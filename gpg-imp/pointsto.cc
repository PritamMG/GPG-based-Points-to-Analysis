#include <algorithm>
#include "gcc-plugin.h"
#include "config.h"
#include "system.h"
#include "cgraph.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "tree-flow.h"
#include "diagnostic.h"
#include "tree-pass.h"
#include "timevar.h"
#include "alloc-pool.h"
#include "params.h"
#include "ggc.h"
#include "vec.h"
#include "gimple-pretty-print.h"
#include<time.h>
#include "parser.hpp"
#include "interval.hpp"
#include "con.hpp"
#include "basic_block.hpp"
#include "cgraph_node.hpp"
#include "IndirectionList.h"
//#include "dominance.c"
//#include "GPB.h"
#include "GPG.h"
#include<map>
#include<vector>
#include<utility>
#include <sys/time.h>
#define alloc_mem ggc_alloc_cleared_atomic 
#define FP 1 
#define OPTIMIZE 0

using namespace std;

/*-----------------------------------------------------------------------------
 *  Each plugin MUST define this global int to assert compatibility with GPL; 
 *  else the compiler throws a fatal error 
 *-----------------------------------------------------------------------------*/
int plugin_is_GPL_compatible;  
double cpu_time_used;

unsigned int ITER = 0;

void print_constraint_basic_block()
{
	struct cgraph_node *cnode ;
	gimple_stmt_iterator gsi;
	gimple stmt;
	basic_block bb;

//        constraint_expr_type 
	int lhs_type, rhs_type;
        int lhs_var_id, rhs_var_id;
        const char *lhs_op, *rhs_op;
        csvarinfo_t lhs, rhs;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {
       
		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
        		  continue;

		fprintf(dump_file, "\n============================================================================\n");
		fprintf(dump_file, "\n %s\n", cgraph_node_name(cnode));
		fprintf(dump_file, "\n============================================================================\n");
			 	
		FOR_EACH_BB(bb)
		{	
			it ai;
			for(ai= ((block_information *)(bb->aux))->get_list().begin();ai !=((block_information *)(bb->aux))->get_list().end(); ai++ )
			{
				if(!(*ai).get_bool())
				{
//					fprintf(dump_file,"\nConstraint - Use\n");

//					fprintf(dump_file,"\nBasic Block %d Constraint %d\n",bb->index,(*ai).get_int());
//					lhs_op = VEC_index(csvarinfo_t,csvarmap,(*ai).get_int())->name;

//	                		fprintf(dump_file,"\nOp: %s\n",lhs_op);

					continue;
				}
//				((function_info *)(cnode->aux))->cons_num++;

//				fprintf(dump_file, "\nIn loop iteration no %d\n", i++);
				constraint_t con = VEC_index(constraint_t, aliases, (*ai).get_int());

				if(con == NULL)
					continue;

				fprintf(dump_file,"\nBasic Block %d Constraint %d\n",bb->index,(*ai).get_int());
				print_constraint(con);

				#if 0
//				if(is_array_invalid_cons(con))
				{
//					fprintf(dump_file,"\nArray Accessed with indirections\n");
//					array_ind++;
				}

                		lhs_type = con->lhs.type;
//				fprintf(dump_file, "\nIn loop \n");
		                rhs_type = con->rhs.type;
                		lhs_var_id = con->lhs.var;
		                rhs_var_id = con->rhs.var;
                		lhs = VEC_index(csvarinfo_t,csvarmap,lhs_var_id);
		                rhs = VEC_index(csvarinfo_t,csvarmap,rhs_var_id);
				unsigned int lhs_off = con->lhs.offset;
				unsigned int rhs_off = con->rhs.offset;
                		lhs_op = lhs->name;
		                rhs_op = rhs->name;
				fprintf(dump_file,"\nBasic Block %d Constraint %d\n",bb->index,(*ai).get_int());
                		fprintf(dump_file,"\nLHS Op: %s-%d LHS type: %d LHS Offset: %d\n RHS Op: %s-%d RHS type: %d RHS Offset: %d\n",lhs_op, lhs_var_id,lhs_type,lhs_off,rhs_op,rhs_var_id,rhs_type,rhs_off);
//		                fprintf(dump_file,"\nLHS Variable Offset %d Size %d Full Size %d Flag %d\n", lhs->offset, lhs->size, lhs->fullsize,lhs->is_full_var);
//                		fprintf(dump_file,"\nRHS Variable Offset %d Size %d Full Size %d Flag %d\n", rhs->offset, rhs->size, rhs->fullsize, rhs->is_full_var);
				#endif
			}
		}
	}
	
	pop_cfun();
}

void printPredsOfEndBB()
{
	struct cgraph_node * cnode;
	basic_block bb;

	GPBSet preds;
	edge e;
        edge_iterator ei;
	basic_block bt;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		FOR_EACH_BB(bb){
//		bb = end_bb_of_fn(cnode);

		unsigned int preds_c = 0;
		unsigned int succs_c = 0;

		fprintf(dump_file, "\nEnd BB %d of Function %s\n", bb->index, cgraph_node_name(cnode));
		fflush(dump_file);

		FOR_EACH_EDGE(e,ei,bb->preds)
	       	{
	               	bt = e->src;

			if(bt->index == 0)
			{
				continue;
			}

			fprintf(dump_file,"\nCFG-pred %d\n", bt->index);
			fflush(dump_file);
			preds_c++;
		}
		FOR_EACH_EDGE(e,ei,bb->succs)
	       	{
	               	bt = e->dest;

			if(bt->index == 0)
			{
				continue;
			}

			fprintf(dump_file,"\nCFG-succ %d\n", bt->index);
			fflush(dump_file);
			succs_c++;
		}
		if(succs_c == 0)
			fprintf(dump_file, "\nHey Muqambo BB %d of Function %s has no successors\n", bb->index, cgraph_node_name(cnode));
		}
		
		bb = end_bb_of_fn(cnode);

		FOR_EACH_EDGE(e,ei,bb->preds)
	       	{
	               	bt = e->src;

			if(bt->index == 0)
			{
				continue;
			}

			fprintf(dump_file,"\nCFG-pred %d\n", bt->index);
			fflush(dump_file);
		}

		pop_cfun();
	}
}

void data_flow_value_computation()
{
	struct cgraph_node *cnode;
	basic_block bb;

        while(!is_function_worklist_d_empty())
        {
                for(int i = 1; i < func_count_d; i++)
                {
                        if(function_worklist_d[i])
                        {
                                cnode = func_numbering[index_func_array_d[i]];

                                perform_analysis_d(cnode);

                                function_worklist_d[i] = false;

                                ((function_info *)(cnode->aux))->dcount++;

		                i = 0;
			}

		}
	}
}

void gpg_construction()
{
	processed_functions.clear();

	perform_analysis(main_cnode);
}

void testIndirectionLists()
{
	int one[IndirectionList::kSize] = {1, 2, 3, 4};
	int two[IndirectionList::kSize] = {};
	int three[IndirectionList::kSize] = {1, 2};
	int four[IndirectionList::kSize] = {};
	int five[IndirectionList::kSize] = {SFIELD};

	std::vector< IndirectionList > rem, fin;
	std::vector< IndirectionList >::iterator it;

	IndirectionList l1(true, 4, 0, four);
	IndirectionList l2(true, 4, 0, four);

	fprintf(dump_file, "\nPrinting l1\n");	
	l1.printIndirectionList();
	fprintf(dump_file, "\nPrinting l2\n");	
	l2.printIndirectionList();

	IndirectionList l3 = l1.append(l2);

	fprintf(dump_file, "\nPrinting l3\n");	
	l3.printIndirectionList();
}

void testingTreeNodes()
{
	csvarinfo_t vi;
	tree t;
	IndirectionList l, r;
	std::tuple< IndirectionList, IndirectionList > il_temp;
	constraint_t con;

	fprintf(dump_file, "\nInside testingTreeNodes\n");

	for(int i = 0 ; i < VEC_length(constraint_t, aliases); i++)
	{
		con = VEC_index(constraint_t, aliases, i);

		fprintf(dump_file, "\nPrinting Constraint\n");
		print_constraint(con);

		il_temp = createIndirectionList(con);

		l = get<0>(il_temp);
		r = get<1>(il_temp);

		fprintf(dump_file, "\nIndirection List l\n");
		l.printIndirectionList();
		fprintf(dump_file, "\nIndirection List r\n");
		r.printIndirectionList();
	}

	#if 0	
	for(int i = 0; i < VEC_length(csvarinfo_t, csvarmap); i++)
	{
		vi = VEC_index (csvarinfo_t, csvarmap, i);

		if(vi->id <= 4)
		{
			continue;
		}

		fprintf(dump_file, "\nVI Var %s %d\n", get_var_name(vi->id), vi->id);

		t = vi->decl;

		print_node(dump_file, "Tree Node\n", t, 0);

		t = TREE_TYPE(t);

		print_node(dump_file, "Tree Type Node\n", t, 0);

		if(t)
		{
			print_node(dump_file, "\nTREE TYPE Node\n", t, 0);

  			if (must_have_fields(t))
			{
				fprintf(dump_file, "\nRecord Type\n");
			}
			else
			{
				fprintf(dump_file, "\n!Record Type\n");
			}
		}
	}
	#endif
}

void call_graph_statistics()
{
	std::set< unsigned int > visited_fn, callees;

	unsigned int edge_count = 0;

	fprintf(dump_file, "Call Graph\n");

	for(func_map::iterator it = callers.begin(); it != callers.end(); it++)
	{
		visited_fn.insert(it->first);

		callees = it->second;

		for(std::set<unsigned int>::iterator cit = callees.begin(); cit != callees.end(); cit++)
		{
			fprintf(dump_file, "%s->%s\n", cgraph_node_name(func_numbering[it->first]), cgraph_node_name(func_numbering[*cit]));
		}

		edge_count += callees.size();

		visited_fn.insert(callees.begin(), callees.end());
	}

	fprintf(dump_file, "\nCall Graph Statistics\nCall Graph Nodes %d, Call Graph Edges %d\n", visited_fn.size(), edge_count);
}

pair< unsigned int, unsigned int > compute_mod_ref_gpb(unsigned int num, unsigned int gpb_id)
{
	unsigned int mod = 0;
	unsigned int ref = 0;

	pair< unsigned int, unsigned int > result;

	GPG ini_g = Initial_GPG_map[num];
	GPB gpb = ini_g.gpb_map[gpb_id];

	GPUSet gpus = gpb.getOrigGPUs();
	GPUSet pts;
	definitions src, dest;

	stmt_info_type key;
	GPBSet sset, temp_sset;
	unsigned int s_len, d_len;

	#if PRINT_DATA
	struct cgraph_node *cnode = func_numbering[num];
	fprintf(dump_file, "\nMOD Function %s GPB %d\n", cgraph_node_name(cnode), gpb_id);
	#endif


	for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
	{
		key = std::make_tuple(num, gpb_id, *git);

		s_len = getNode(get<0>(*git)).getList().Length();
		d_len = getNode(get<1>(*git)).getList().Length();

		#if PRINT_DATA
		fprintf(dump_file, "\nMOD Function %s GPB %d Src Len %d Dest Len %d\n", cgraph_node_name(cnode), gpb_id, s_len, d_len);
		#endif

		sset = stmt_id_info[key];

		for(GPBSet::iterator sit = sset.begin(); sit != sset.end(); sit++)
		{
			pts = PTS_INFO[*sit];

			#if PRINT_DATA
			fprintf(dump_file, "\nMOD Function %s GPB %d Stmt id %d\n", cgraph_node_name(cnode), gpb_id, *sit);
			#endif

			for(GPUSet::iterator it = pts.begin(); it != pts.end(); it++)
			{
//				if(isPointstoInformation(*it))
				{
					src.insert(get<0>(*it));
					dest.insert(get<1>(*it));
				}
			}		
	
			#if PRINT_DATA
			fprintf(dump_file, "\nMOD Function %s GPB %d Stmt id %d\nSources\n", cgraph_node_name(cnode), gpb_id, *sit);
			printDefinitions(src);
			fprintf(dump_file, "\nMOD Function %s GPB %d Stmt id %d\nDestinations\n", cgraph_node_name(cnode), gpb_id, *sit);
			printDefinitions(dest);
			#endif

			mod += src.size();
			ref += ((s_len-1) * src.size());
			ref += (d_len * dest.size());
			
			#if PRINT_DATA
			fprintf(dump_file, "\nMOD Function %s GPB %d Stmt id %d Mod %d Ref %d\n", cgraph_node_name(cnode), gpb_id, *sit, mod, ref);
			#endif
		}
	}


	result = make_pair(mod, ref);

	return result;
}

void compute_mod_ref_all_gpbs_cnode(unsigned int num)
{
	GPG opt_g;
	struct cgraph_node *cnode;

//	fprintf(dump_file, "\nHey There b1 %s\n", cgraph_node_name(func_numbering[num]));
//	fflush(dump_file);

	opt_g = optimized_GPG_map[num];

	GPBSet gpbs = opt_g.getGPBs();

	GPB gpb;
	GPUSet gpus;

	set< unsigned int > ind_callees;
	unsigned int callee;

	unsigned int mod = 0, temp;
	unsigned int ref = 0;

	pair< unsigned int, unsigned int > res;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = opt_g.gpb_map[*it];

		res = compute_mod_ref_gpb(num, *it);

		mod += res.first;
		ref += res.second;
		
	}

	#if PRINT_DATA
	fprintf(dump_file, "\nTotal MOD Function %s Mod %d Ref %d\n", cgraph_node_name(func_numbering[num]), mod, ref);
	#endif
//	fprintf(dump_file, "\nHey There bl \n");
//	fflush(dump_file);

	SMOD[num] = mod;
	SREF[num] = ref;
}


void compute_mod_ref_cnodes()
{
	GPG ini_g;
	struct cgraph_node *cnode;
	GPBSet gpbs;
	GPB gpb;
	GPUSet gpus;
	set< unsigned int > ind_callees;
	unsigned int callee;

	unsigned int mod = 0, temp;
	unsigned int ref = 0;

	unsigned int cnode_num;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		cnode_num = ((function_info *)(cnode->aux))->func_num;

		set< unsigned int > all_callees;

		ini_g = Initial_GPG_map[cnode_num];

		gpbs = ini_g.getGPBs();

		for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
		{
			gpb = ini_g.gpb_map[*it];

			if(gpb.isCallBlock())
			{
				callee = gpb.getCallee();

				SMOD[cnode_num] += SMOD[callee];

				SREF[cnode_num] += SREF[callee];
			}
			else if(gpb.isIndirectCallBlock())
			{
				Prototype fp, fn;
				fp = gpb.proto;

				for (map <int, Prototype>:: iterator fnit = fn_details.begin(); fnit != fn_details.end(); ++fnit)
        			{
					fn = fnit->second;

					if (fp.compare (fn))
					{
						callee = fnit->first;

						SMOD[cnode_num] += SMOD[callee];

						SREF[cnode_num] += SREF[callee];
					}
				}
			}
			else
			{
				GPUSet gpus = gpb.getOrigGPUs();
				GPUSet pts;
				stmt_info_type key;
				GPBSet sset;
				unsigned int l_len = 0, r_len = 0;
				setOfNodes l_nodes, r_nodes;	

				for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
				{
					l_len = getNode(get<0>(*git)).getList().Length();
					r_len = getNode(get<1>(*git)).getList().Length();

					key = std::make_tuple(cnode_num, *it, *git);

					sset = stmt_id_info[key];

					for(GPBSet::iterator sit = sset.begin(); sit != sset.end(); sit++)
					{
						pts = PTS_INFO[*sit];

						for(GPUSet::iterator pit = pts.begin(); pit != pts.end(); pit++)
						{
							if(isPointstoInformation(*pit))
							{
								l_nodes.insert(get<0>(*pit));
								r_nodes.insert(get<1>(*pit));
							}
						}
						
					}

					//if(l_len >=1)
					{
						SMOD[cnode_num] += l_nodes.size();
					}

					if(r_len >=1)
					{
						SREF[cnode_num] += r_nodes.size();
					}	
				}
			}
		}

		pop_cfun();
	}


	unsigned int mod_count = 0;
	unsigned int ref_count = 0;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		cnode_num = ((function_info *)(cnode->aux))->func_num;

		set< unsigned int > all_callees;

		ini_g = Initial_GPG_map[cnode_num];

		gpbs = ini_g.getGPBs();

		for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
		{
			gpb = ini_g.gpb_map[*it];

			if(gpb.isCallBlock())
			{
				callee = gpb.getCallee();

				temp = SMOD[callee];

				#if 1  //PRINT_DATA
				fprintf(dump_file, "\nFunction: %s #REF: %d #MOD: %d\n", cgraph_node_name(func_numbering[callee]), SREF[callee], SMOD[callee]);
				#endif

				mod_count += temp;

				if(temp > 0)
				{
					SMCALLS++;
				}

				temp = SREF[callee];	

				ref_count += temp;

				if(temp > 0)
				{
					SRCALLS++;
				}
			}
			else if(gpb.isIndirectCallBlock())
			{
				Prototype fp, fn;
				fp = gpb.proto;

				for (map <int, Prototype>:: iterator fnit = fn_details.begin(); fnit != fn_details.end(); ++fnit)
        			{
					fn = fnit->second;

					if (fp.compare (fn))
					{
						callee = fnit->first;

						temp = SMOD[callee];

						mod_count += temp;

						fprintf(dump_file, "\nFunction: %s #REF: %d #MOD: %d\n", cgraph_node_name(func_numbering[callee]), SREF[callee], SMOD[callee]);
						if(temp > 0)
						{
							SMCALLS++;
						}

						temp = SREF[callee];	

						ref_count += temp;

						if(temp > 0)
						{
							SRCALLS++;
						}
					}
				}
			}
		}

	}

	fprintf(dump_file, "\nSMCALLS %d\n", SMCALLS);
	fprintf(dump_file, "\nSRCALLS %d\n", SRCALLS);
	fflush(dump_file);

	fprintf(dump_file, "\nNumber of MODS %d\n\nNumber of REFS %d\n", mod_count, ref_count);
	fflush(dump_file);

//	fprintf(dump_file, "\nHey There bl \n");
//	fflush(dump_file);
}


void side_effect_analysis()
{
	unsigned int num;
	set< unsigned int > scc_cnodes;

	compute_mod_ref_cnodes();

//	fprintf(dump_file, "\nHey There a \n");
//	fflush(dump_file);

	#if 0
	fprintf(dump_file, "\nSMCALLS %d\n", SMCALLS);
	fprintf(dump_file, "\nSRCALLS %d\n", SRCALLS);
	fflush(dump_file);

	unsigned int mod = 0, ref = 0;

	for(map< unsigned int, unsigned int >::iterator it = SMOD.begin(); it != SMOD.end(); it++)
	{
		#if PRINT_DATA
		if(it->second > 0)
		{
			fprintf(dump_file, "\nPositive MOD for Function %s %d\n", cgraph_node_name(func_numbering[it->first]), it->second);
		}
		#endif
		mod += it->second;
	}

	for(map< unsigned int, unsigned int >::iterator it = SREF.begin(); it != SREF.end(); it++)
	{
		#if PRINT_DATA
		if(it->second > 0)
		{
			fprintf(dump_file, "\nPositive REF for Function %s %d\n", cgraph_node_name(func_numbering[it->first]), it->second);
		}
		#endif

		ref += it->second;
	}

	fprintf(dump_file, "\nNumber of MODS %d\n\nNumber of REFS %d\n", mod, ref);
	fflush(dump_file);
	#endif
}

void mod_ref()
{
	struct cgraph_node * cnode;
	GPG g;
	unsigned int cnode_num;
	GPUSet gpus, pts;
	GPBSet gpbs;
	GPB gpb;
	unsigned int mod_count, ref_count;
	stmt_info_type key;
	GPBSet sset, temp_sset;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		cnode_num = ((function_info *)(cnode->aux))->func_num;

		g = optimized_GPG_map[cnode_num];	

		gpbs = g.getGPBs();

		for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
		{
			gpb = g.gpb_map[*it];

			gpus = gpb.getGPUs();

			for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
			{
				key = std::make_tuple(cnode_num, *it, *git);

				sset = stmt_id_info[key];

				for(GPBSet::iterator sit = sset.begin(); sit != sset.end(); sit++)
				{
					pts = PTS_INFO[*sit];

//					count_mod_ref(*git, pts);

				}
			}
		}
	
		pop_cfun();
	}

}

unsigned int execute_ipacs (void)
{
	#if PROFILING
	INIT_PROFILE_STATS();
	FUNBEGIN();
	#endif

	if(!in_lto_p) // Perform analysis only in the LTO mode
	{
		return 0;
	}

	switch_pass = true;

	struct timeval tvalBefore, tvalAfter;

	#if TIME_MEAS
//	clock_t start_t = clock();
	tot_op = 0;
	sr_op = 0;
	dead_op = 0;
	emp_op = 0;
	coal_op = 0;

	gettimeofday (&tvalBefore, NULL);
	#endif

	// Initialization
	init_fn_aux();
	initialization();

// 	Performing Interval Analysis
//	find_interval_first_phase(((function_info *)(main_cnode->aux))->func_num);

	createSCCs();
//	computeLeavesOfSCC();

	// Splitting the Basic Blocks at the Call Sites
	modify_cfg();

	// Preprocessing
	switch_pass = true;

	preprocess_control_flow_graph();

	#if TIME_MEAS
//	clock_t end_t = clock();
	gettimeofday (&tvalAfter, NULL);

//	double elapsed_time = 1000.0 * (end_t-start_t)/CLOCKS_PER_SEC;

//	fprintf(dump_file,"\nPreprocessing Time: %lg\n", elapsed_time);
//	fprintf(dump_file, "\nPreprocessing Time in milliseconds: %0.3f milliseconds\n", (float)(tvalAfter.tv_usec - tvalBefore.tv_usec));
	fprintf(dump_file, "\nPreprocessing Time in microseconds: %ld microseconds\n", ((tvalAfter.tv_sec - tvalBefore.tv_sec)*1000000L+tvalAfter.tv_usec) - tvalBefore.tv_usec); 
	#endif

	#if 0
	fprintf(dump_file, "\nPreprocessing Done\n");	
	fflush(dump_file);
	#endif

	#if 0
	csvarinfo_t vi;

	for(int i = 0; i < VEC_length(csvarinfo_t, csvarmap); i++)
	{
		vi = VEC_index (csvarinfo_t, csvarmap, i);

		if(vi->id <= 4)
		{
			continue;
		}

		fprintf(dump_file, "\nVI Var %s %d\n", get_var_name(vi->id), vi->id);
	}

	print_constraint_basic_block();
	#endif

//	constraint_count += VEC_length(constraint_t, aliases);

	#if PRINT_DATA
//	print_constraint_basic_block();
	#endif

	//print_constraint_basic_block();

	#if FI_ANALYSIS && CI_ANALYSIS

	#if TIME_MEAS
//	start_t = clock();
	gettimeofday (&tvalBefore, NULL);
	#endif

	flowContextInsensitiveAnalysis();

	#if TIME_MEAS
	gettimeofday (&tvalAfter, NULL);

	fprintf(dump_file, "\nAnalysis Time in microseconds: %ld microseconds\n", ((tvalAfter.tv_sec - tvalBefore.tv_sec)*1000000L+tvalAfter.tv_usec) - tvalBefore.tv_usec); 
	#endif
	#else

	#if TIME_MEAS
//	start_t = clock();
	gettimeofday (&tvalBefore, NULL);
	#endif

	collect_fp_type_info();

	constructInitialGPG();

	//printPredsOfEndBB();

	GPGConstruction();

//	constructGPGsForIndirectlyCalledFunctions();

	#if TIME_MEAS
	gettimeofday (&tvalAfter, NULL);

	fprintf(dump_file, "\nAnalysis Time in microseconds: %ld microseconds\n", ((tvalAfter.tv_sec - tvalBefore.tv_sec)*1000000L+tvalAfter.tv_usec) - tvalBefore.tv_usec); 
	fprintf(dump_file, "\nRedundancy Elim Optimization Time: %ld, Strength Reduction: %ld, Dead GPU Elim: %ld, Empty GPB Elim: %ld, Coalescing: %ld\n", tot_op, sr_op, dead_op, emp_op, coal_op);
	#endif
	#endif

	#if DATA_MEAS
	printData();
	#endif

// Client Analysis

	#if DATA_MEAS
	call_graph_statistics();

	side_effect_analysis();
	
	#endif

/////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////

	delete_block_aux();

	end_fn_aux();

	#if PROFILING
	FUNEND();
	PRINT_PROFILE_STATS();
	#endif

	return 0;
}

struct simple_ipa_opt_pass pass_ipacs =
{
  {
    SIMPLE_IPA_PASS,
    "gpg",                                /* name */
    NULL,	                            /* gate */
    execute_ipacs,		            /* execute */
    NULL,                                   /* sub */
    NULL,                                   /* next */
    0,                                      /* static_pass_number */
    TV_INTEGRATION,                         /* tv_id */
    0,                                      /* properties_required */
    0,                                      /* properties_provided */
    0,                                      /* properties_destroyed */
    0,                                      /* todo_flags_start */
    0                                       /* todo_flags_finish */
  }
};
struct register_pass_info pass_info = 
{
	&(pass_ipacs.pass),
	"pta",
	0,
	PASS_POS_INSERT_AFTER
};

int plugin_init(struct plugin_name_args *plugin_info, struct plugin_gcc_version *version)
{
	register_callback(
		plugin_info->base_name,
		PLUGIN_PASS_MANAGER_SETUP,
		NULL,
		&pass_info);
	return 0;
}


//////////////////////////////////////////////////////////////////////////////////////////////////////

