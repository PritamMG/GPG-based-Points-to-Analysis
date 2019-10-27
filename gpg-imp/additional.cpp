#include "additional.h"

map< node_id_type, definitions > reuse_ssa; 
definitions visited_nodes, boundary_nodes;
map< unsigned int, GPBList > Function_Worklist; 

unsigned int get_art_node(gimple stmt, basic_block bb, struct cgraph_node *cnode)
{
//	fprintf(dump_file,"\nget_art_node\n");

//	print_gimple_stmt (dump_file, stmt, 0, 0);
//	fprintf(dump_file,"\n\n");

	basic_block bt = stmt->gsbase.bb;
	tree lhs = gimple_call_lhs (stmt);

	csvarinfo_t vi = cs_lookup_vi_for_tree(lhs);

	it ai;
	for(ai= ((block_information *)(bt->aux))->get_list().begin();ai !=((block_information *)(bt->aux))->get_list().end(); ai++ )
	{
		if(!(*ai).get_bool())
		{
			continue;
		}

		constraint_t con = VEC_index(constraint_t, aliases, (*ai).get_int());

		if(con == NULL)
			continue;

		if(con->phi_stmt)
			continue;

		tree lhs_bb = VEC_index(csvarinfo_t,csvarmap,con->lhs.var)->decl;

		if(vi->id == con->lhs.var)
		{
//			fprintf(dump_file,"\nLHS Var %s-%d, RHS Var %s-%d\n", get_var_name(con->lhs.var), con->lhs.var, get_var_name(con->rhs.var), con->rhs.var);

			return con->rhs.var;
		}
	}

	return 0;
}

bool array_ptr_arith(node_id_type node)
{
	Node n = getNode(node);
	IndirectionList ill = n.getList();
	unsigned int vid = n.getVarIndex();

	csvarinfo_t v1, v2, v3, v4;
	tree t1, t2;

	v1 = cs_get_varinfo(vid);
	t1 = SSAVAR(v1->decl);

	set< unsigned int > res = cs_get_all_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, vid), 0);

	if(!res.empty() && ill.stackIndirectionList() && ill.Length() > 2)
		return true; 

	#if 0
	for(definitions:: iterator it = glob_lhs.begin(); it != glob_lhs.end(); it++)
	{
		v2 = cs_get_varinfo(get<0>(*it));

		t2 = SSAVAR(v2->decl);

//		if(get<0>(rhs) == get<0>(*it))
		if(DECL_UID(t1) == DECL_UID(t2))
		{
			if(ill->stackIndirectionList())
				return true;
		}
	}
	#endif

	return false;
}

definitions resolve_ssa(node_id_type node, bool type, basic_block bb, struct cgraph_node *cnode) // type = true => lhs, type = false => rhs
{
//	fprintf(dump_file, "\nTop resolving node\n");
//	print_NodeID(node);

	definitions res, res_temp;

	tree t;
	node_id_type temp;
	unsigned int id;
	set< unsigned int >::iterator cit;	
	set< unsigned int > cons_list;

	// Creating an empty Indirection List
	IndirectionList ilt;
	std::vector< IndirectionList > rem, fin;
	int *field_list;

	IndirectionList e_list(true, 0, 0, field_list);
	IndirectionList f_list(true, 1, 0, field_list);

	Node nt = getNode(node);

	id = nt.getVarIndex();
	ilt = nt.getList();

	t = VEC_index(csvarinfo_t, csvarmap, id)->decl;

	if(id <= 4)
	{
		res.insert(node);
//		fprintf(dump_file, "\nNode\n");
//		print_NodeID(node);
//		fprintf(dump_file, "\nResolved to\n");
//		printDefinitions(res);

		return res;
	}

	gcc_assert(t && TREE_CODE(t) == SSA_NAME);

	visited_nodes.insert(node);

	gimple stmt = SSA_NAME_DEF_STMT(t);

	if(!stmt)
	{
//		fprintf(dump_file, "\nNode\n");
//		print_NodeID(node);
//		fprintf(dump_file, "\nResolved to\n");
//		printDefinitions(res);
		return res;
	}

//	print_gimple_stmt (dump_file, stmt, 0, 0);
//	fprintf(dump_file,"\n\n");

	cons_list = gimple_to_constraints[stmt];

	if(is_gimple_call(stmt))
	{
		if (gimple_call_flags (stmt) & ECF_MALLOC)
		{
			unsigned int rhs_heap = get_art_node(stmt, bb, cnode);

			if(rhs_heap != 0)
			{
				tree lhs = gimple_call_lhs (stmt);

				rem = ilt.remainder(f_list);
	
				fin = e_list.append_list(rem);

				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(rhs_heap, *it);

//					fprintf(dump_file, "\nInserting New Node in res\n");
//					print_NodeID(new_node.getNodeID());
					res.insert(new_node.getNodeID());
				}
			}
		}

		if(type){
		for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
		{
			constraint_t exp = VEC_index(constraint_t,aliases, *cit);

			IndirectionList il1, il2;
			std::tuple< IndirectionList, IndirectionList > il_temp;

			il_temp = createIndirectionList(exp);

			il1 = get<0>(il_temp);
			il2 = get<1>(il_temp);

			rem = ilt.remainder(il1);
			
			fin = il2.append_list(rem);

			tree rhs_op = VEC_index(csvarinfo_t,csvarmap,exp->rhs.var)->decl;

			if(exp->rhs.var > 4 && TREE_CODE(rhs_op) == SSA_NAME)
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

					if(visited_nodes.find(temp) == visited_nodes.end() && (!type && !array_ptr_arith(temp)))			
					{
						if(!reuse_ssa[temp].empty())
						{
							res_temp = reuse_ssa[temp];
						}
						else
						{
							res_temp = resolve_ssa(temp, type, bb, cnode);

							reuse_ssa[temp] = res_temp;
						}

						for(definitions::iterator dit = res_temp.begin(); dit != res_temp.end(); dit++)
						{
//							fprintf(dump_file, "\nInserting New Node in res\n");
//							print_NodeID(*dit);
							res.insert(*dit);
						}	
					}
					#if 1
					else
					{
//						fprintf(dump_file, "\nInserting New Node in res Already in visited list\n");
						//print_NodeID(temp);
						res_temp = reuse_ssa[temp];
						res.insert(res_temp.begin(), res_temp.end());
//						res.insert(temp);
					}
					#endif
				}
			}
			else
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

//					fprintf(dump_file, "\nInserting New Node in res, !SSA\n");
//					print_NodeID(temp);
					res.insert(temp);
				}
			}
		}
		}
	}
	else if(gimple_code(stmt) == GIMPLE_PHI)
	{
//		fprintf(dump_file, "\nPhi Statement\n");
//		print_gimple_stmt (dump_file, stmt, 0, 0);
//		fprintf(dump_file,"\n\n");
//		fprintf(dump_file, "\nResolving Node\n");
//		print_NodeID(node);
		
		for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
		{
			constraint_t exp = VEC_index(constraint_t,aliases, *cit);
			
			IndirectionList il1, il2, f_il, il3;
			std::tuple< IndirectionList, IndirectionList > il_temp;
			
			il_temp = createIndirectionList(exp);

			il1 = get<0>(il_temp);
			il2 = get<1>(il_temp);

			rem = ilt.remainder(il1);

			fin = il2.append_list(rem);

			tree rhs_op = VEC_index(csvarinfo_t,csvarmap,exp->rhs.var)->decl;

			if(exp->rhs.var > 4 && TREE_CODE(rhs_op) == SSA_NAME)
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

					if(visited_nodes.find(temp) == visited_nodes.end() && (!type && !array_ptr_arith(temp)))			
					{
						if(!reuse_ssa[temp].empty())
						{
							res_temp = reuse_ssa[temp];
						}
						else
						{
							res_temp = resolve_ssa(temp, type, bb, cnode);

							reuse_ssa[temp] = res_temp;
						}

						for(definitions::iterator dit = res_temp.begin(); dit != res_temp.end(); dit++)
						{
//							fprintf(dump_file, "\nInserting New Node in res\n");
//							print_NodeID(*dit);
							res.insert(*dit);
						}	
					}
					#if 1
					else
					{
//						fprintf(dump_file, "\nInserting New Node in res, not in visited list\n");
						//print_NodeID(temp);
						res_temp = reuse_ssa[temp];
						res.insert(res_temp.begin(), res_temp.end());
//						res.insert(temp);
					}
					#endif
				}
			}
			else
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

//					fprintf(dump_file, "\nInserting New Node in res, !SSA\n");
//					print_NodeID(temp);
					res.insert(temp);
				}
			}
		}
	}
	else if(gimple_code(stmt) == GIMPLE_NOP)
	{
//		fprintf(dump_file, "\nNOP\n");
//		print_gimple_stmt (dump_file, stmt, 0, 0);
//		fprintf(dump_file,"\n\n");
//		fprintf(dump_file, "\nNode that cannot be resolved\n");
//		print_NodeID(node);
//		fprintf(dump_file, "\nTree Node with SSA\n", alias_get_name(t));
		
		if(is_par_ret(t, cnode, bb) && type)
		{
			tree t1 = SSAVAR(t);

//			fprintf(dump_file, "\nTree Node after SSA\n", alias_get_name(t1));
	
			if(t1)
			{
				csvarinfo_t newnode  = cs_lookup_vi_for_tree(t1);

				if(newnode)
				{
					Node new_node(newnode->id, ilt);
					temp = new_node.getNodeID();

//					fprintf(dump_file, "\nInserting New Node in res\n");
//					print_NodeID(temp);
					res.insert(temp);
				} 	
			}
		}
	}
	#if 0
	else if(gimple_assign_rhs_code(stmt) == POINTER_PLUS_EXPR)
	{
		fprintf(dump_file, "\nHurray\n");
		for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
		{
			constraint_t exp = VEC_index(constraint_t,aliases, *cit);
	
			print_constraint(exp);
		}
		fprintf(dump_file, "\nHurraaaaaaaaaaaay\n");

		Node new_node(undef_id, e_list);
		temp = new_node.getNodeID();

		res.insert(temp);
	}
	#endif
	else if(gimple_code(stmt) == GIMPLE_ASSIGN || gimple_assign_rhs_code(stmt) == POINTER_PLUS_EXPR)
	{
		for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
		{
			constraint_t exp = VEC_index(constraint_t,aliases, *cit);
			
			IndirectionList il1, il2;
			std::tuple< IndirectionList, IndirectionList > il_temp;
			
			il_temp = createIndirectionList(exp);

			il1 = get<0>(il_temp);
			il2 = get<1>(il_temp);

			rem = ilt.remainder(il1);
			fin = il2.append_list(rem);

			tree rhs_op = VEC_index(csvarinfo_t,csvarmap,exp->rhs.var)->decl;

			if(exp->rhs.var > 4 && TREE_CODE(rhs_op) == SSA_NAME)
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

					if(visited_nodes.find(temp) == visited_nodes.end() && (!type && !array_ptr_arith(temp)))
					{
						if(!reuse_ssa[temp].empty())
						{
							res_temp = reuse_ssa[temp];
						}
						else
						{
							res_temp = resolve_ssa(temp, type, bb, cnode);

							reuse_ssa[temp] = res_temp;
						}

						for(definitions::iterator dit = res_temp.begin(); dit != res_temp.end(); dit++)
						{
//							fprintf(dump_file, "\nInserting New Node in res\n");
//							print_NodeID(*dit);
							res.insert(*dit);
						}	
					}
					#if 1
					else
					{
//						fprintf(dump_file, "\nInserting New Node in res, not in visited list\n");
//						print_NodeID(temp);
						res_temp = reuse_ssa[temp];
						res.insert(res_temp.begin(), res_temp.end());
//						res.insert(temp);
					}
					#endif
				}
			}
			else
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

//					fprintf(dump_file, "\nInserting New Node in res, !SSA\n");
//					print_NodeID(temp);
					res.insert(temp);
				}
			}	
		}
	}

	if(res.empty())
	{
		res.insert(node);
	}

//	boundary_nodes.insert(res.begin(), res.end());

//	fprintf(dump_file, "\nNode\n");
//	print_NodeID(node);
//	fprintf(dump_file, "\nResolved to\n");
//	printDefinitions(res);

	return res;
}

GPUSet resolveConstraintSSA(constraint_t cons, basic_block bb, struct cgraph_node *cnode)
{
	fprintf(dump_file,"\nPrinting Constraint\n");
	print_constraint(cons);

	unsigned int id = 0;

	GPUSet res;

	tree lhs, rhs;

//	if(con->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && con->lhs.type == 1 && is_par_ret(lhs, caller, bb))

	lhs = VEC_index(csvarinfo_t,csvarmap,cons->lhs.var)->decl;
	rhs = VEC_index(csvarinfo_t,csvarmap,cons->rhs.var)->decl;

	node_id_type lnode, rnode;
	definitions ldef, rdef;

	IndirectionList l_list, r_list;

//	fprintf(dump_file,"\nJourney Begins\n");
//	fflush(dump_file);

	std::tuple< IndirectionList, IndirectionList > il_temp;
			
	il_temp = createIndirectionList(cons);

	l_list = get<0>(il_temp);
	r_list = get<1>(il_temp);

	fprintf(dump_file,"\nIndirectionLists Created\n");
	fflush(dump_file);

	Node l_node(cons->lhs.var, l_list);
        lnode = l_node.getNodeID();

//	fprintf(dump_file,"\nlnode Created\n");
//	l_node.printNode();
//	fflush(dump_file);

	Node r_node(cons->rhs.var, r_list);
        rnode = r_node.getNodeID();

//	fprintf(dump_file,"\nrnode Created\n");
//	r_node.printNode();
//	fflush(dump_file);

	if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && !is_par_ret(lhs, cnode, bb))
	{
//		fprintf(dump_file,"\nSSA LHS with no DEREF and no para-ret\n");
		return res;
	}
	else if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && is_par_ret(lhs, cnode, bb))
	{
//		fprintf(dump_file,"\nSSA LHS with no DEREF but a para-ret\n");
		visited_nodes.clear();
		ldef = resolve_ssa(lnode, true, bb, cnode); 
	}
	else if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME)
	{
//		fprintf(dump_file,"\nSSA LHS with DEREF\n");
		visited_nodes.clear();
		ldef = resolve_ssa(lnode, true, bb, cnode); 
	}
	else
	{
//		fprintf(dump_file,"\nNON_SSA LHS\n");
		Node new_node(cons->lhs.var, l_list);
//		new_node.printNode();
		ldef.insert(new_node.getNodeID());
	}

	if(cons->rhs.var > 4 && TREE_CODE(rhs) == SSA_NAME)
	{
//		fprintf(dump_file,"\nSSA RHS\n");
		visited_nodes.clear();
		rdef = resolve_ssa(rnode, false, bb, cnode); 
	}
	else
	{
//		fprintf(dump_file,"\nNON_SSA RHS\n");
		Node new_node(cons->rhs.var, r_list);
//		new_node.printNode();
		rdef.insert(new_node.getNodeID());
	}

	for(definitions::iterator lit = ldef.begin(); lit != ldef.end(); lit++)
	{
//		fprintf(dump_file,"\nPrinting ldef\n");
//		print_NodeID(*lit);
		
		for(definitions::iterator rit = rdef.begin(); rit != rdef.end(); rit++)
		{
//			fprintf(dump_file,"\nPrinting rdef\n");
//			print_NodeID(*rit);
		
			GPU gpu(*lit, *rit, id);
			gpu_id_type t = gpu.getGPUID();
//			fprintf(dump_file,"\nHey Der\n");
//			gpu.printGPU();
			res.insert(t);		
		}
	}
	
	return res;
}

GPUSet resolve_constraint_SSA(unsigned int id, basic_block bb, struct cgraph_node *cnode)
{
//	fprintf(dump_file,"\nPrinting Constraint\n");
//	print_constraint(VEC_index(constraint_t, aliases, id));

	GPUSet res;

	tree lhs, rhs;

//	if(con->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && con->lhs.type == 1 && is_par_ret(lhs, caller, bb))

	constraint_t cons = VEC_index(constraint_t, aliases, id);

	lhs = VEC_index(csvarinfo_t,csvarmap,cons->lhs.var)->decl;
	rhs = VEC_index(csvarinfo_t,csvarmap,cons->rhs.var)->decl;

	node_id_type lnode, rnode;
	definitions ldef, rdef;

	IndirectionList l_list, r_list;

//	fprintf(dump_file,"\nJourney Begins\n");
//	fflush(dump_file);

	std::tuple< IndirectionList, IndirectionList > il_temp;
			
	il_temp = createIndirectionList(cons);

	l_list = get<0>(il_temp);
	r_list = get<1>(il_temp);

//	fprintf(dump_file,"\nIndirectionLists Created\n");
//	fflush(dump_file);

	Node l_node(cons->lhs.var, l_list);
        lnode = l_node.getNodeID();

//	fprintf(dump_file,"\nlnode Created\n");
//	l_node.printNode();
//	fflush(dump_file);

	Node r_node(cons->rhs.var, r_list);
        rnode = r_node.getNodeID();

//	fprintf(dump_file,"\nrnode Created\n");
//	r_node.printNode();
//	fflush(dump_file);

	if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && !is_par_ret(lhs, cnode, bb))
	{
//		fprintf(dump_file,"\nSSA LHS with no DEREF and no para-ret\n");
		return res;
	}
	else if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && is_par_ret(lhs, cnode, bb))
	{
//		fprintf(dump_file,"\nSSA LHS with no DEREF but a para-ret\n");
		//visited_nodes.clear();
		//ldef = resolve_ssa(lnode, true, bb, cnode); 
		csvarinfo_t vi = cs_get_varinfo(cons->lhs.var);
		if(vi)
		{
			tree decl = vi->decl;
			decl = SSAVAR(decl);
			vi = cs_lookup_vi_for_tree (decl);
			if(vi)
			{
				Node new_node(vi->id, l_list);
				ldef.insert(new_node.getNodeID());
//				printSetofNodeIDs(ldef);
			}
		}	
	}
	else if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME)
	{
//		fprintf(dump_file,"\nSSA LHS with DEREF\n");
		visited_nodes.clear();
		ldef = resolve_ssa(lnode, true, bb, cnode); 
	}
	else
	{
//		fprintf(dump_file,"\nNON_SSA LHS\n");
//		Node new_node(cons->lhs.var, l_list);
//		new_node.printNode();
//		ldef.insert(new_node.getNodeID());
		ldef.insert(lnode);	
	}

	if(cons->rhs.var > 4 && TREE_CODE(rhs) == SSA_NAME)
	{
//		fprintf(dump_file,"\nSSA RHS\n");
		visited_nodes.clear();
		rdef = resolve_ssa(rnode, false, bb, cnode); 
	}
	else
	{
//		fprintf(dump_file,"\nNON_SSA RHS\n");
//		Node new_node(cons->rhs.var, r_list);
//		new_node.printNode();
//		rdef.insert(new_node.getNodeID());
		rdef.insert(rnode);
	}

	for(definitions::iterator lit = ldef.begin(); lit != ldef.end(); lit++)
	{
//		fprintf(dump_file,"\nPrinting ldef\n");
//		print_NodeID(*lit);
		
		for(definitions::iterator rit = rdef.begin(); rit != rdef.end(); rit++)
		{
//			fprintf(dump_file,"\nPrinting rdef\n");
//			print_NodeID(*rit);
		
			GPU gpu(*lit, *rit, id);
			gpu_id_type t = gpu.getGPUID();
//			fprintf(dump_file,"\nHey Der\n");
//			gpu.printGPU();
			res.insert(t);		
		}
	}
	
	boundary_nodes.insert(ldef.begin(), ldef.end());
	boundary_nodes.insert(rdef.begin(), rdef.end());

	return res;
}

definitions resolve_fp_ssa(unsigned int fp_var, basic_block bb, struct cgraph_node *cnode)
{
	node_id_type node;
	int *field_list;

	IndirectionList list(true, 1, 0, field_list);

	Node new_node(fp_var, list);	
	node = new_node.getNodeID();

	return resolve_ssa(node, true, bb, cnode);
}

GPUSet map_para_args_fp_call(unsigned int callee_rep, unsigned int caller_rep, basic_block bb)
{
	struct cgraph_node *caller, *callee;
	gimple stmt;

	caller = func_numbering[caller_rep];
	callee = func_numbering[callee_rep];
	
	stmt = bb_call_stmt(bb);

	int j, argoffset = 1, i;
	tree arg, par;
	GPUSet res, temp;
	csvarinfo_t fi;

	tree decl = callee->decl;

	if(!decl)
		return res;

	fi = cs_get_vi_for_tree (decl, bb, caller);

	if(fi == NULL)
		return res;

	for (j = 0; j < gimple_call_num_args (stmt); j++)
	{
//		fprintf(dump_file,"\nArg\n");

		arg = gimple_call_arg (stmt, j);

		if (field_must_have_pointers (arg))
		{
			csvarinfo_t cvar = cs_first_vi_for_offset (fi, argoffset);

			if(cvar == NULL)
				continue;

			par = cvar->decl;

			if(par == NULL)
				return res;

			if(field_must_have_pointers(par))
			{
//				fprintf(dump_file,"\nBoth Pointers\n");

				VEC(ce_s, heap) *lhsc = NULL;
				VEC(ce_s, heap) *rhsc = NULL;

//				fprintf(dump_file, "\nParameter %s\n", alias_get_name(par));
//				fprintf(dump_file, "\nArgument %s\n", alias_get_name(arg));

				cs_get_constraint_for(par, &lhsc, bb, caller);
				cs_get_constraint_for(arg, &rhsc, bb, caller);

				struct constraint_expr *c;	
				struct constraint_expr *c2;
				unsigned int k1, k2;

               			FOR_EACH_VEC_ELT (ce_s, lhsc, k1, c)
				//while(VEC_length(ce_s, lhsc) != 0)
				{
					//c = VEC_last(ce_s, lhsc);

               				FOR_EACH_VEC_ELT (ce_s, rhsc, k2, c2)
					//while(VEC_length(ce_s, rhsc) != 0)
					{
						//c2 = VEC_last(ce_s, rhsc);

						constraint_t con = new_constraint (*c, *c2);

//						fprintf(dump_file, "\nHey Constraint\n");
//						print_constraint(con);

						temp = resolveConstraintSSA(con, bb, caller);

						res.insert(temp.begin(), temp.end());
					}
				}

   				VEC_free (ce_s, heap, lhsc);
   				VEC_free (ce_s, heap, rhsc);
			}
		}
	}

	return res;
}

bool isDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	basic_block bb1, bb2;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	int b1, b2;
	GPB gpb1, gpb2;

	gpb1 = gpb_map[caller_rep][gpb_id1];
	gpb2 = gpb_map[caller_rep][gpb_id2];

	b1 = gpb1.getBBIndex();
	b2 = gpb2.getBBIndex();

	if(b1 == b2)
	{
		if(gpb_id1 < gpb_id2)
			return true;

		return false;
	}

	bool flag = false;
	
	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	bb1 = BASIC_BLOCK(b1);
	bb2 = BASIC_BLOCK(b2);

	if((dominated_by_p(CDI_DOMINATORS, bb1, bb2)))
	{
		flag = true;
	}

	pop_cfun();

	return flag;
}

bool isPDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	basic_block bb1, bb2;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	int b1, b2;
	GPB gpb1, gpb2;

	gpb1 = gpb_map[caller_rep][gpb_id1];
	gpb2 = gpb_map[caller_rep][gpb_id2];

	b1 = gpb1.getBBIndex();
	b2 = gpb2.getBBIndex();

	if(b1 == b2)
	{
		if(gpb_id1 < gpb_id2)
			return true;

		return false;
	}

	bool flag = false;
	
	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	bb1 = BASIC_BLOCK(b1);
	bb2 = BASIC_BLOCK(b2);

	if(dominated_by_p(CDI_POST_DOMINATORS, bb2, bb1))
	{
		flag = true;
	}

	pop_cfun();

	return flag;
}

bool isDomPDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	basic_block bb1, bb2;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	int b1, b2;
	GPB gpb1, gpb2;

	gpb1 = gpb_map[caller_rep][gpb_id1];
	gpb2 = gpb_map[caller_rep][gpb_id2];

	b1 = gpb1.getBBIndex();
	b2 = gpb2.getBBIndex();

	if(b1 == b2)
	{
		if(gpb_id1 < gpb_id2)
			return true;

		return false;
	}

	bool flag = false;
	
	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	bb1 = BASIC_BLOCK(b1);
	bb2 = BASIC_BLOCK(b2);

	if((dominated_by_p(CDI_DOMINATORS, bb1, bb2) && dominated_by_p(CDI_POST_DOMINATORS, bb2, bb1)))
//	(dominated_by_p(CDI_DOMINATORS, bb2, bb1) && dominated_by_p(CDI_POST_DOMINATORS, bb1, bb2)))
	{
		flag = true;
//		return true;
	}

	pop_cfun();

	return flag;

//	return false;
}

void get_global_info()
{
	struct varpool_node *node;
	tree t;

	GPUSet initial_decls;

	for (node = varpool_nodes; node; node = node->next)
        {
		t = node->decl;

		csvarinfo_t vi = cs_get_vi_for_tree(t, main_firstbb, main_cnode);

                if(field_must_have_pointers(t))
                {
			if (DECL_INITIAL (t))
			{
				VEC (ce_s, heap) *rhsc = NULL;

				cs_get_constraint_for_rhs (DECL_INITIAL (t), &rhsc, main_firstbb, main_cnode);

				struct constraint_expr lhs, *rhsp, rhs;
				unsigned i;

				lhs.var = vi->id;
				lhs.offset = 0;
				lhs.type = SCALAR;

				int *field_list;
				IndirectionList l_ind(true, 1, 0, field_list);
				IndirectionList r_ind;
				Node l_decl(vi->id, l_ind);

				FOR_EACH_VEC_ELT (ce_s, rhsc, i, rhsp)               // Vini: Why commented out????
				{
					rhs = *rhsp;

					if(rhs.offset == 0 && rhs.type == ADDRESSOF)
					{
						constraint_count++;

						Node r_decl(rhs.var, r_ind);

						GPU gpu(l_decl, r_decl, 0);

						initial_decls.insert(gpu.getGPUID());

						continue;
					}

					cs_process_constraint (new_constraint (lhs, *rhsp), main_firstbb);
				}

				VEC_free (ce_s, heap, rhsc);
			}
		}
	}

	unsigned int main_cnum = ((function_info *)(main_cnode->aux))->func_num;

	RIN[main_cnum][1] = initial_decls;
	BRIN[main_cnum][1] = initial_decls;

//	fflush(dump_file);
//	fprintf(dump_file,"\nNumber of Intialization Constraints %d\n", VEC_length(constraint_t, aliases)); 	
//	fflush(dump_file);

}

GPG createNewGPG(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	basic_block bb = start_bb_of_fn(cnode);
	GPG res;
	GPB entry, gpb, exit;
	GPBSet gpbs, prev2, prev3, next1, next2;
	unsigned int x = ((function_info *)(cnode->aux))->GPB_count;

	GPUSet maygen, mustkill, temp;

	maygen = DownwardsExposedMayDefinitions[cnode_num];
	mustkill = DownwardsExposedMustDefinitions[cnode_num];

	if(maygen.empty())
	{
		((function_info *)(cnode->aux))->GPB_count++;

		entry.setId(x);
		entry.setBBIndex(bb->index);
		entry.setGPUs(mustkill);
		gpb_map[cnode_num][x] = entry;

		gpbs.insert(x);
		res.setEntryGPB(x);
		res.setExitGPB(x);
		res.setGPBs(gpbs);

		return res;
	}
	else
	{
		((function_info *)(cnode->aux))->GPB_count += 3;

		entry.setId(x);
		entry.setBBIndex(bb->index);
		entry.setGPUs(mustkill);
		next1.insert(x+1);
		next1.insert(x+2);
		entry.setNext(next1);
		gpb_map[cnode_num][x] = entry;

		gpb.setId(x+1);
		gpb.setBBIndex(bb->index);
		gpb.setGPUs(maygen);
		prev2.insert(x);
		next2.insert(x+2);
		gpb.setPrev(prev2);
		gpb.setNext(next2);
		gpb_map[cnode_num][x+1] = gpb;

		exit.setId(x+2);
		exit.setBBIndex(bb->index);
		exit.setGPUs(temp);
		prev3.insert(x);
		prev3.insert(x+1);
		exit.setPrev(prev3);
		gpb_map[cnode_num][x+2] = exit;
		
		gpbs.insert(x);
		gpbs.insert(x+1);
		gpbs.insert(x+2);
		res.setEntryGPB(x);
		res.setExitGPB(x+2);
		res.setGPBs(gpbs);

		return res;
	}
}

IndirectionList create_indirection_list(bool type, struct constraint_expr e)
{
	int field_list[IndirectionList::kSize];
	tree t;

//	fprintf(dump_file, "\nInside create_indirection_list %s-%d, %d, %d\n", get_var_name(e.var), e.var, e.type, e.offset);
//	fflush(dump_file);

	csvarinfo_t vi = cs_get_varinfo (e.var);

	if(vi == NULL)
	{
		IndirectionList list;
		return list;
	}

//	fprintf(dump_file, "\nAfter vi serach %d\n", vi->id);
//	fflush(dump_file);

//	if(is_aggregrate_type_varinfo(vi))
	if(type)
	{
//		fprintf(dump_file, "\nAggregrate true\n");
//		fflush(dump_file);

		if(e.type == 1)
		{
//			fprintf(dump_file, "\nScalar\n");
//			fflush(dump_file);

			field_list[0] = SFIELD;
			IndirectionList list(false, 0, 1, field_list);

			return list;	
		}
		else if(e.type == 2)
		{
//			fprintf(dump_file, "\nDeref\n");
//			fflush(dump_file);

			field_list[0] = SFIELD;
			field_list[1] = e.offset;
			IndirectionList list(false, 0, 2, field_list);

			return list;	
		}
		else
		{
//			fprintf(dump_file, "\nAddressof\n");
//			fflush(dump_file);

			IndirectionList list(false, 0, 0, field_list);

			return list;	
		}
	}
	else
	{
//		fprintf(dump_file, "\nAggregrate false\n");
//		fflush(dump_file);

		if(e.type == 1)
		{
//			fprintf(dump_file, "\nScalar\n");
//			fflush(dump_file);

			IndirectionList list(true, 1, 0, field_list);

			return list;	
		}
		else if(e.type == 2)
		{
//			fprintf(dump_file, "\nDeref\n");
//			fflush(dump_file);

			IndirectionList list(true, 2, 0, field_list);

			return list;	
		}
		else
		{
//			fprintf(dump_file, "\nAddressof\n");
//			fflush(dump_file);

			IndirectionList list(true, 0, 0, field_list);

			return list;	
		}
	}
}

std::tuple< IndirectionList, IndirectionList > createIndirectionList(constraint_t con)
{
//	fprintf(dump_file,"\nPrinting Constraint\n");
//	print_constraint(con);

	bool lagg, ragg;
	std::tuple< IndirectionList, IndirectionList > res;
	struct constraint_expr lhs, rhs;
	IndirectionList l, r;

	lhs = con->lhs;
	rhs = con->rhs;

	csvarinfo_t vi_l = cs_get_varinfo (lhs.var);
	csvarinfo_t vi_r = cs_get_varinfo (rhs.var);

	if(vi_l == NULL || vi_r == NULL)
	{
		return res;
	}

//	fprintf(dump_file, "\nAfter vi serach %d\n", vi->id);
//	fflush(dump_file);

//	if(is_aggregrate_type_varinfo(vi))

	if(lhs.var <= 4)
	{
		lagg = false;
	}
	else
	{
		lagg = isAggregrateNode(vi_l);
	}

	if(rhs.var <= 4)
	{
		ragg = false;
	}
	else
	{
		ragg = isAggregrateNode(vi_r);
	}

	if(lagg && ragg) // Both are aggregrate types
	{
		l = create_indirection_list(true, lhs);
		r = create_indirection_list(true, rhs);
	}
	else if(!lagg && !ragg) // Both are scalar types
	{
		l = create_indirection_list(false, lhs);
		r = create_indirection_list(false, rhs);
	}
	else
	{
		l = create_indirection_list(true, lhs);
		r = create_indirection_list(true, rhs);
	}

	#if 0
	fprintf(dump_file, "\nPrinting l: ");
	l.printIndirectionList();
	fprintf(dump_file, "\n");
	fprintf(dump_file, "\nPrinting r: ");
	r.printIndirectionList();
	fprintf(dump_file, "\n");
	#endif

	res = std::make_tuple(l, r);

	return res;
}

bool filter_constraint(unsigned int id, basic_block bb, struct cgraph_node *cnode) // Filter this constraint if this function returns true
{
	constraint_t cons = VEC_index(constraint_t, aliases, id);

	tree lhs = VEC_index(csvarinfo_t,csvarmap,cons->lhs.var)->decl;
	tree rhs = VEC_index(csvarinfo_t,csvarmap,cons->rhs.var)->decl;

	if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && !is_par_ret(lhs, cnode, bb))
	{
		return true;
	}

	return false;
}

bool needsInlining(unsigned int caller, unsigned int callee)
{

	struct cgraph_node *callee_node = func_numbering[callee];

	#if 0
	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (callee_node->decl)), "exit") == 0)
	{
		return false;
	}
	#endif

	if(caller == callee)
	{
		return false;
	}

	if(processed_functions.find(callee) != processed_functions.end())
	{
		return true;
	}

	return false;

	#if 0
	if(callee_node)
	{
		#if !RECURSION
		if(caller == callee)
		{
			return false;
		}
		#endif

		if(((function_info *)(callee_node->aux))->has_fixed_pt())
		{
			fprintf(dump_file,"\nInlining Required Condition 1\n");
			fflush(dump_file);

			return true;
		}
		else
		{
			#if RECURSION
			if(caller == callee)
			{
				fprintf(dump_file,"\nInlining Required Condition 2\n");
				fflush(dump_file);

				return true;
			}
			#endif
		}
	}

	fprintf(dump_file,"\nReturning false\n");
	fflush(dump_file);

	return false;
	#endif
}

bool needsInliningRecursion(unsigned int caller, unsigned int callee)
{
	if(caller == callee)
	{
		return true;
	}

	return false;
}

void collectUpwardExposedVersions(GPUSet gen, struct cgraph_node *cnode)
{	
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	definitions l_temp, r_temp;
	unsigned int lvar, rvar;
	node_id_type lnode, rnode;
	Node nl, nr;

	l_temp = lhsUpwardsExposedDefinitions[caller_rep];
	r_temp = rhsUpwardsExposedDefinitions[caller_rep];

	for(GPUSet::iterator it = gen.begin(); it != gen.end(); it++)
	{

		lnode = get<0>(*it);
		rnode = get<1>(*it);

		nl = getNode(lnode);
		nr = getNode(rnode);

		lvar = get<0>(lnode);
		rvar = get<0>(rnode);

		if(CDV.find(lvar) != CDV.end() || nl.getList().Length() > 1)
		{
			l_temp.insert(lnode);
		}

		if(CDV.find(rvar) != CDV.end() || nr.getList().Length() >= 1)
		{
			r_temp.insert(rnode);
		}
	}
	
	lhsUpwardsExposedDefinitions[caller_rep] = l_temp;
	rhsUpwardsExposedDefinitions[caller_rep] = r_temp;
}

GPBSet get_bb_pred(basic_block bb, struct cgraph_node *cnode)
{
	GPBSet preds;
	GPBSet temp;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;
	
	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	edge e;
        edge_iterator ei;
	basic_block bt;

       	FOR_EACH_EDGE(e,ei,bb->preds)
       	{
		fprintf(dump_file, "\nInside for loop\n");
		fflush(dump_file);

               	bt = e->src;

		if(bt->index == 0)
		{
			continue;
		}

		fprintf(dump_file,"\nCFG-pred %d\n", bt->index);
		fflush(dump_file);

		temp = ((block_information *)(bt->aux))->eblocks;	

		preds.insert(temp.begin(), temp.end());	
	}

	fprintf(dump_file, "\nPreds: ");
	fflush(dump_file);
	print_set_integers(preds);
	fflush(dump_file);

	return preds;


	#if 0
	set< unsigned int > tmp1, tmp2;

	tmp1 = ((block_information *)(bb->aux))->pred_rel;

	tmp2 = ((block_information *)(bb->aux))->pred_with_back_edge_rel;

	tmp1.insert(tmp2.begin(), tmp2.end());

	fprintf(dump_file, "\nInside get_bb_pred BB %d Function %s\n", bb->index, cgraph_node_name(cnode));
	print_set_integers(tmp1);
	fflush(dump_file);

	for(set< unsigned int >::iterator it = tmp1.begin(); it != tmp1.end(); it++)
	{
		fprintf(dump_file, "\nInside for loop\n");
		fflush(dump_file);

		bt = BASIC_BLOCK(*it);

//		temp = ori_red_map[caller_rep][bt->index];

		fprintf(dump_file,"\nCFG-pred %d\n", bt->index);
//		fflush(dump_file);

		temp = ((block_information *)(bt->aux))->eblocks;	

		preds.insert(temp.begin(), temp.end());	

		#if 0
		for(GPBSet::iterator bit = temp.begin(); bit != temp.end(); bit++)
		{
//			gpb = GPB::gpb_map[*bit];

//			if(gpb.e_bb_block)
			{
				preds.insert(*bit);
//				fprintf(dump_file,"\nGPG-pred %d\n", *bit);
//				fflush(dump_file);
//				break;
			}
		}
		#endif
	}

	fprintf(dump_file, "\nPreds: ");
//	fflush(dump_file);
	print_set_integers(preds);
//	fflush(dump_file);

	return preds;
	#endif
}

GPBSet get_bb_succ(basic_block bb, struct cgraph_node *cnode)
{
	GPBSet succs;
	GPBSet temp;
	
//	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	edge e;
        edge_iterator ei;
	basic_block bt;

       	FOR_EACH_EDGE(e,ei,bb->succs)
       	{
		fprintf(dump_file, "\nInside for loop\n");
		fflush(dump_file);

               	bt = e->dest;

		if(bt->index == 0)
		{
			continue;
		}

		fprintf(dump_file,"\nCFG-pred %d\n", bt->index);
//		fflush(dump_file);

		temp = ((block_information *)(bt->aux))->sblocks;	

		succs.insert(temp.begin(), temp.end());	
	}

	fprintf(dump_file, "\nSuccs: ");
//	fflush(dump_file);
	print_set_integers(succs);
//	fflush(dump_file);

	return succs;

	#if 0	
	set< unsigned int > tmp1, tmp2;

	tmp1 = ((block_information *)(bb->aux))->succ_rel;

	tmp2 = ((block_information *)(bb->aux))->succ_with_back_edge_rel;

	tmp1.insert(tmp2.begin(), tmp2.end());
	
	GPB gpb;

	for(set< unsigned int >::iterator it = tmp1.begin(); it != tmp1.end(); it++)
	{
		bt = BASIC_BLOCK(*it);

		temp = ((block_information *)(bt->aux))->sblocks;	

//		temp = ori_red_map[caller_rep][bt->index];

		fprintf(dump_file,"\nCFG-succ %d\n", bt->index);

		succs.insert(temp.begin(), temp.end());

		#if 0
		for(GPBSet::iterator bit = temp.begin(); bit != temp.end(); bit++)
		{
//			gpb = GPB::gpb_map[*bit];

//			if(gpb.e_bb_block)
			{
				succs.insert(*bit);
//				fprintf(dump_file,"\nGPG-pred %d\n", gpb.getId());
//				break;
			}
		}
		#endif
	}

	fprintf(dump_file, "\nSuccs: ");
	print_set_integers(succs);

	return succs;
	#endif
}

std::pair< GPBSet, GPBSet> set_pred_succ(basic_block bb, struct cgraph_node *cnode)
{
	GPBSet preds, succs;

//	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

//	fprintf(dump_file,"\nInside set_red_preds_succs\n");
//	fflush(dump_file);

//	FUNBEGIN();

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

//	map< unsigned int, set< GPB* > > ori_red_map = ((function_info *)(cnode->aux))->ori_red_map;
	GPBSet temp;

	set< unsigned int > tmp1, tmp2;

	tmp1 = ((block_information *)(bb->aux))->pred_rel;

	tmp2 = ((block_information *)(bb->aux))->pred_with_back_edge_rel;

	tmp1.insert(tmp2.begin(), tmp2.end());

	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	basic_block bt, bs;	
	GPB gpb;

	for(set< unsigned int >::iterator it = tmp1.begin(); it != tmp1.end(); it++)
	{
		bt = BASIC_BLOCK(*it);

		if(((block_information *)(bt->aux))->call_block)
		{
			temp = ori_red_map[caller_rep][bt->index];

			for(GPBSet::iterator bit = temp.begin(); bit != temp.end(); bit++)
			{
				gpb = gpb_map[caller_rep][*bit];

				if(gpb.getType() == 3)
				{
					preds.insert(*bit);
					break;
				}		
			}
		}
		else
		{
		        preds.insert(ori_red_map[caller_rep][bt->index].begin(), ori_red_map[caller_rep][bt->index].end());
		}
	}

	tmp1 = ((block_information *)(bb->aux))->succ_rel;

	tmp2 = ((block_information *)(bb->aux))->succ_with_back_edge_rel;

	tmp1.insert(tmp2.begin(), tmp2.end());

	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	for(set< unsigned int >::iterator it = tmp1.begin(); it != tmp1.end(); it++)
	{
		bt = BASIC_BLOCK(*it);

		if(((block_information *)(bt->aux))->call_block)
		{
			temp = ori_red_map[caller_rep][bt->index];

			for(GPBSet::iterator bit = temp.begin(); bit != temp.end(); bit++)
			{
				gpb = gpb_map[caller_rep][*bit];

				if(gpb.getType() == 3)
				{
					succs.insert(*bit);
					break;
				}		
			}
		}
		else
		{
		        succs.insert(ori_red_map[caller_rep][bt->index].begin(), ori_red_map[caller_rep][bt->index].end());
		}
	}

	return make_pair(preds, succs);
}

bool analyze_callee_now(struct cgraph_node *callee)
{
	vector< unsigned int >::iterator it; 

	unsigned int callee_rep = ((function_info *)(callee->aux))->func_num;

	if(processed_functions.find(callee_rep) == processed_functions.end())
	{
		if(!is_present_in_worklist(callee_rep))
		{
			return true;
		}
		else // Identifying Recursive Call
		{
			return false;
		}
	}

	// Already Processed
	return false;
}
