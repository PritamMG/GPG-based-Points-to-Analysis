#include <algorithm>
#include "interval.hpp"
//#include "parser.hpp"

unsigned int interval_count;
unsigned int reduce_graph_count = 0;

map< unsigned int, interval > interval_map;

unsigned int interval::get_id()
{
	return id;
}

void interval::set_id(unsigned int i)
{
	id = i;
}

unsigned int interval::get_header()
{
	return header;	
}

void interval::set_header(unsigned int h)
{
	header = h;
}

list< unsigned int > interval::get_node_list()
{
	return node_list;
}

void interval::set_node_list(list< unsigned int > sc)
{
	node_list = sc;
}

unsigned int interval::get_pred_count()
{
	return pred_count;
}

void interval::set_pred_count(unsigned int c)
{
	pred_count = c;
}

unsigned int interval::get_reach()
{
	return reach;
}

void interval::set_reach(unsigned int r)
{
	reach = r;
}

unsigned int interval::get_inter_order()
{
	return inter_order;
}

void interval::set_inter_order(unsigned int c)
{
	inter_order = c;
}

bool interval::is_marked()
{
	return marked;
}

void interval::set_marked()
{
	marked = true;
}

void interval::reset_marked()
{
	marked = false;
}

bool operator==(const interval & i1, const interval & i2)
{
        if(i1.node_list == i2.node_list)
                return true;

        return false;

}

void interval::print_interval()
{
	fprintf(dump_file,"\nInterval Id: %d\n Nodes in the Interval\n", get_id());

	list< unsigned int >::iterator it;
	list< unsigned int > nodes = get_node_list();

	for(it = nodes.begin(); it != nodes.end(); it++)
	{
		fprintf(dump_file,"%d\t",*it);
	}

	fprintf(dump_file,"\nHeader of the Interval %d\n", get_header());
	fprintf(dump_file,"\nPred Count  %d\n", get_pred_count());
	fprintf(dump_file,"\nSize of Interval %d\n", nodes.size());

	if(is_marked())
		fprintf(dump_file,"\nInterval is Processed\n");
}

list< struct cgraph_node * > interval::get_cnodes()
{
//	fprintf(dump_file,"\nInside get_cnodes %d\n", get_id());
		
	list< unsigned int > nodes = get_node_list();
	list< struct cgraph_node * > result, temp;
	struct cgraph_node *cnode;

	list< unsigned int >::iterator it;
	interval I;

	for(it = nodes.begin(); it != nodes.end(); it++)
	{
		if(*it >= func_num)
		{
			I = interval_map[*it];

			temp = I.get_cnodes();

			result.insert(result.end(), temp.begin(), temp.end());
		}
		else
		{
			cnode = func_numbering[*it];

			result.push_back(cnode);
		}	
	}

	#if 0
	list<struct cgraph_node * >::iterator lit;
	fprintf(dump_file,"\nResult\n");

	for(lit = result.begin(); lit != result.end(); lit++)
	{
		fprintf(dump_file,"%s\t",cgraph_node_name(*lit));
	}

	fprintf(dump_file,"\n");
	#endif

	return result;
}

bool interval::is_equal(interval I)
{
	list< unsigned int > nodes1, nodes2;

	nodes1 = get_node_list();
	nodes2 = I.get_node_list();

	if(nodes1.size() != nodes2.size())
	{
		return false;
	}

	list< struct cgraph_node * > cnodes1, cnodes2;

	cnodes1 = get_cnodes();

	cnodes2 = I.get_cnodes();

	list< struct cgraph_node * >::iterator cit1, cit2;

	if(cnodes1.size() != cnodes2.size())
	{
		return false;
	}

	struct cgraph_node *c1, *c2;

	for(cit1 = cnodes1.begin(), cit2 = cnodes2.begin(); cit1 != cnodes1.end(); cit1++, cit2++)
	{
		c1 = *cit1;
		c2 = *cit2;

//		if(c1->uid != c2->uid)
		if(((function_info *)(c1->aux))->func_num != ((function_info *)(c2->aux))->func_num)
		{
			return false;
		}
	}
		
	return true;
}

unsigned int interval_graph::get_start_node()
{
	return start_node;
}

void interval_graph::set_start_node(unsigned int s)
{
	start_node = s;
}

graph_type interval_graph::get_edge_list()
{
	return edge_list;
}

void interval_graph::set_edge_list(graph_type g)
{
	edge_list = g;
}

set< unsigned int > interval_graph::get_interval_set()
{
	return interval_set;
}

void interval_graph::set_interval_set(set< unsigned int > s)
{
	interval_set = s;
}

unsigned int interval_graph::search_node(unsigned int x)
{
	list<unsigned int> nodes;

	unsigned int result = -1;

	set< unsigned int > intervals = get_interval_set();
	set< unsigned int >::iterator sit;
	interval I;

//	fprintf(dump_file,"\nSearching Node X %d in Interval Graph\n", x);
//	print_interval_graph();

	for(sit = intervals.begin(); sit != intervals.end(); sit++)
	{
		I = interval_map[*sit];

		nodes = I.get_node_list();

		if(find(nodes.begin(), nodes.end(), x) != nodes.end())
		{
			return I.get_id();
		}
	}

	return result;
	
}


set< unsigned int > func_ordered;

void verify_ordering()
{
	fprintf(dump_file,"\nVerifying order\n");

	struct cgraph_node *cnode;

	for(int i = 1; i < func_count; i++)
	{
		cnode = func_numbering[index_func_array[i]];

		fprintf(dump_file,"%s\t", cgraph_node_name(cnode));
	}		

	fprintf(dump_file,"\n\n");
}

void interval_graph::top_sort_ordering()
{
//	fprintf(dump_file,"\nInside top_sort_ordering\n");

	list< unsigned int > visited_d;
	list< unsigned int > visit_d;

	visited_d.push_back(get_start_node());

	while(!visited_d.empty())
	{

		unsigned int s = visited_d.front();
		visited_d.pop_front();

//		fprintf(dump_file,"\nInside top_sort_ordering %d\n", s);

		struct cgraph_node *cnode;

		graph_type edges = get_edge_list();

		graph_type::iterator git;

		interval I = interval_map[s];

		visit_d.push_back(s);

		list< struct cgraph_node * > result;
		result = I.get_cnodes();
	
//		fprintf(dump_file,"\nSize of Result %d\n", result.size());

		list< struct cgraph_node * >::iterator lit;

		for(lit = result.begin(); lit != result.end(); lit++)
		{
			cnode = *lit;

//			if(func_ordered.find(((function_info *)(cnode->aux))->func_num) == func_ordered.end())
			{
//			fprintf(dump_file,"%s\t",cgraph_node_name(cnode));
//			fprintf(dump_file,"\nFunction Ordered in the Worklist D %s at Order %d\n", cgraph_node_name(cnode), func_count_d);

			index_func_array_d[func_count_d] = ((function_info *)(cnode->aux))->func_num;
			func_index_array_d[((function_info *)(cnode->aux))->func_num] = func_count_d;
			function_worklist_d[func_count_d] = true;
			preprocess_worklist[func_count_d] = true;
			func_count_d++;
			func_ordered.insert(((function_info *)(cnode->aux))->func_num);	
			}
		}	

//		fprintf(dump_file,"\nvisit_d\n");
//		for(list< unsigned int >::iterator it = visit_d.begin(); it != visit_d.end(); it++)
		{
//			fprintf(dump_file,"%d\t", *it);
		}
//		fprintf(dump_file,"\n\n");

		for(git = edges.begin(); git != edges.end(); git++)
		{
			if(get<0>(*git) == s)
			{
//				fprintf(dump_file,"\nS = %d\n",get<1>(*git));
				#if 1
				if(find(visit_d.begin(), visit_d.end(), get<1>(*git)) == visit_d.end())
				{
					if(find(visited_d.begin(), visited_d.end(), get<1>(*git)) == visited_d.end())
					{
//					fprintf(dump_file,"\nTesting Interval %d\n", get<1>(*git));
//					interval_map[get<1>(*git)].print_interval();
//					fflush(dump_file);
						visited_d.push_back(get<1>(*git));
					}
				}

				#endif
			}
		}

//		fprintf(dump_file,"\nvisited_d\n");

//		for(list< unsigned int >::iterator it = visited_d.begin(); it != visited_d.end(); it++)
		{
//			fprintf(dump_file,"%d\t", *it);
		}

//		fprintf(dump_file,"\n\n");
	}
}

void interval_graph::depth_ordering(unsigned int s)
{
//	fprintf(dump_file,"\nInside depth_ordering %d\n", s);

	struct cgraph_node *cnode;

	graph_type edges = get_edge_list();

	graph_type::iterator git;

	interval I = interval_map[s];
	interval J;
	I.reset_marked();
	interval_map[I.get_id()] = I;	

	for(git = edges.begin(); git != edges.end(); git++)
	{
		if(get<0>(*git) == s)
		{
			J = interval_map[get<1>(*git)];

			if(J.is_marked())
			{
				depth_ordering(get<1>(*git));
			}
		}
	}

	I = interval_map[s];

	list< struct cgraph_node * > result;
	result = I.get_cnodes();

	list< struct cgraph_node * >::reverse_iterator lit;

	for(lit = result.rbegin(); lit != result.rend(); lit++)
	{
		cnode = *lit;

//		if(func_ordered.find(((function_info *)(cnode->aux))->func_num) == func_ordered.end())
		{
//		fprintf(dump_file,"%s\t",cgraph_node_name(cnode));
//		fprintf(dump_file,"\nFunction Ordered in the Worklist %s %d\n", cgraph_node_name(cnode), func_count);

		index_func_array[func_count] = ((function_info *)(cnode->aux))->func_num;
		func_index_array[((function_info *)(cnode->aux))->func_num] = func_count;
		function_worklist[func_count] = true;
		func_count++;
		func_ordered.insert(((function_info *)(cnode->aux))->func_num);
		}
	}
}

void interval_graph::set_order_of_worklist_d()
{
	set< unsigned int > intervals = get_interval_set();
	graph_type edges = get_edge_list();

	graph_type::iterator git;

	interval I;
	list< struct cgraph_node * > temp, result;

	struct cgraph_node *cnode;
	list< struct cgraph_node * >::iterator rlit;

	set< unsigned int >::iterator sit;

//	fprintf(dump_file,"\nfunc_count_d = %d\n",func_count_d);

	func_ordered.clear();

	if(intervals.size() == 1 && edges.size() == 0)
	{
		sit = intervals.begin();

		I = interval_map[*sit];

		result = I.get_cnodes();

//		fprintf(dump_file,"\nOrder of Functions to be processed - 2\n");

		for(rlit = result.begin(); rlit != result.end(); rlit++)
		{
			cnode = *rlit;

//			if(func_ordered.find(((function_info *)(cnode->aux))->func_num) == func_ordered.end())
			{
//			fprintf(dump_file,"%s\t", cgraph_node_name(cnode));
//			fprintf(dump_file,"\nFunction Ordered in the Worklist %s %d %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num, func_count_d);

			index_func_array_d[func_count_d] = ((function_info *)(cnode->aux))->func_num;
			func_index_array_d[((function_info *)(cnode->aux))->func_num] = func_count_d;
//			fprintf(dump_file,"\nFunction Ordered in the Worklist %s %d %d %d\n", cgraph_node_name(cnode), index_func_array_d[func_count_d], func_index_array_d[((function_info *)(cnode->aux))->func_num], func_count_d);
			function_worklist_d[func_count_d] = true;
			preprocess_worklist[func_count_d] = true;
			func_count_d++;
			func_ordered.insert(((function_info *)(cnode->aux))->func_num);
			}
		}

//		fprintf(dump_file,"\n Func Count in Ordering Worklist %d\n",func_count_d);

//		verify_ordering();

		return;
	}

//	fprintf(dump_file,"\nOrder of Functions to be processed - 3\n");

	top_sort_ordering();

//	verify_ordering();
}

void interval_graph::set_order_of_worklist()
{
//	fprintf(dump_file,"\nFinal Interval Graph\n");
//	print_interval_graph();

	set< unsigned int > intervals = get_interval_set();
	graph_type edges = get_edge_list();

	graph_type::iterator git;

	interval I;
	list< struct cgraph_node * > temp, result;

	struct cgraph_node *cnode;
	list< struct cgraph_node * >::reverse_iterator lit;
	list< struct cgraph_node * >::iterator rlit;

	set< unsigned int >::iterator sit;

	func_ordered.clear();

	if(intervals.size() == 1 && edges.size() == 0)
	{
		sit = intervals.begin();

		I = interval_map[*sit];

		result = I.get_cnodes();

//		fprintf(dump_file,"\nOrder of Functions to be processed\n");

		for(lit = result.rbegin(); lit != result.rend(); lit++)
		{
			cnode = *lit;

//			if(func_ordered.find(((function_info *)(cnode->aux))->func_num) == func_ordered.end())
			{
//			fprintf(dump_file,"%s\t", cgraph_node_name(cnode));
//			fprintf(dump_file,"\nFunction Ordered in the Worklist %s %d\n", cgraph_node_name(cnode), func_count);

			index_func_array[func_count] = ((function_info *)(cnode->aux))->func_num;
			func_index_array[((function_info *)(cnode->aux))->func_num] = func_count;
			function_worklist[func_count] = true;
			func_count++;
			func_ordered.insert(((function_info *)(cnode->aux))->func_num);
			}

		}

//		fprintf(dump_file,"\n Func Count in Ordering Worklist %d\n",func_count);
//		verify_ordering();
		return;
	}

//	fprintf(dump_file,"\nOrder of Functions to be processed - 1\n");

	depth_ordering(get_start_node());
//	verify_ordering();	

//	print_interval_graph();
}

void interval_graph::create_edges_first_phase(interval I)
{
	set< unsigned int >:: iterator cit, rit;
	list< unsigned int >::iterator lit;

	struct cgraph_node *cnodex, *cnodey;

	interval_graph g;
	set< unsigned int > intervals_nodes = get_interval_set();

	unsigned int x, y;
	unsigned int id = I.get_id();
	interval J;
	set< unsigned int > result;
	graph_type edges = get_edge_list();
	tuple< unsigned int, unsigned int > t;
	unsigned int tmp;

	list< unsigned int > nodes = I.get_node_list();

	for(lit = nodes.begin(); lit != nodes.end(); lit++)
	{
		cnodex = func_numbering[*lit];

		set_func caller_list;
		caller_list = callers[*lit];

		for(cit = caller_list.begin(); cit != caller_list.end(); cit++)
		{
			cnodey = func_numbering[*cit];

			if (!gimple_has_body_p (cnodey->decl) || cnodey->clone_of)
				continue;

			y = *cit;

			tmp = search_node(y);

			if(tmp != -1 && tmp != id) // No self loops
			{
				result.insert(tmp);
			}
		}	
	}

	for(rit = result.begin(); rit != result.end(); rit++)
	{
		t = make_tuple(*rit, id);

		edges.insert(t);
	}

	I.set_pred_count(I.get_pred_count() + result.size());
	interval_map[id] = I;

	result.clear();

	for(lit = nodes.begin(); lit != nodes.end(); lit++)
	{
		cnodex = func_numbering[*lit];

		set_func callee_list = callees[*lit];

		for(cit = callee_list.begin(); cit != callee_list.end(); cit++)
		{
			cnodey = func_numbering[*cit];

			if (!gimple_has_body_p (cnodey->decl) || cnodey->clone_of)
				continue;

			y = *cit;

			tmp = search_node(y);

			if(tmp != -1 && tmp != id) // No self loops
			{
				result.insert(tmp);
			}
		}	
	}

	for(rit = result.begin(); rit != result.end(); rit++)
	{
		t = make_tuple(id, *rit);

		edges.insert(t);
	
		J = interval_map[*rit];
		J.set_pred_count(J.get_pred_count() + 1);
		interval_map[*rit] = J;
	}

	intervals_nodes.insert(id);

	set_interval_set(intervals_nodes);
	set_edge_list(edges);
}

interval_graph interval_graph::create_edges(interval_graph g, interval I)
{
//	fprintf(dump_file,"\nInside create_edges()\n");

	list< unsigned int > nodes = I.get_node_list();

	set< unsigned int >:: iterator cit, rit;
	list< unsigned int >::iterator lit;
	graph_type::iterator git;

	unsigned int x, y;
	unsigned int id = I.get_id();
	interval J;

	set< unsigned int > result;

	graph_type edges = get_edge_list();
	graph_type edges_new = g.get_edge_list();
	tuple< unsigned int, unsigned int > t;

	unsigned int tmp;

	set< unsigned int > intervals = g.get_interval_set();

	for(lit = nodes.begin(); lit != nodes.end(); lit++)
	{
		x = *lit;

//		fprintf(dump_file,"\nNode in the Interval %d\n", x);
	
		for(git = edges.begin(); git != edges.end(); git++)
		{
			if(get<1>(*git) == x)
			{
				y = get<0>(*git);

//				fprintf(dump_file,"\nCaller %d\n", y);

				tmp = g.search_node(y);

//				fprintf(dump_file,"\nInterval of Caller %d\n",tmp);

				if(tmp != -1 && tmp != id)
				{
					result.insert(tmp);
				}
			}
		}	
	}

	for(rit = result.begin(); rit != result.end(); rit++)
	{
		t = make_tuple(*rit, id);

		edges_new.insert(t);
	}

	I.set_pred_count(I.get_pred_count() + result.size());
	interval_map[id] = I;

	result.clear();

	for(lit = nodes.begin(); lit != nodes.end(); lit++)
	{
		x = *lit;
	
//		fprintf(dump_file,"\nNode in the Interval %d\n", x);
	
		for(git = edges.begin(); git != edges.end(); git++)
		{
			if(get<0>(*git) == x)
			{
				y = get<1>(*git);

//				fprintf(dump_file,"\nCallee %d\n", y);

				tmp = g.search_node(y);

//				fprintf(dump_file,"\nInterval of Callee %d\n",tmp);

				if(tmp != -1 && tmp != id)
				{
					result.insert(tmp);
				}
			}
		}	
	}

	for(rit = result.begin(); rit != result.end(); rit++)
	{
//		fprintf(dump_file,"%d\t",*lit);
		t = make_tuple(id, *rit);

		edges_new.insert(t);

		J = interval_map[*rit];
		J.set_pred_count(J.get_pred_count()+1);
		interval_map[*rit] = J;
	}

	intervals.insert(id);

	g.set_interval_set(intervals);
	g.set_edge_list(edges_new);

//	fprintf(dump_file,"\nKay Chalu\n");
//	g.print_interval_graph();
	
	return g;	
}

void interval_graph::reduce_interval_graph()
{
//	fprintf(dump_file,"\nInside reduce_interval_graph\n");

	unsigned int s = get_start_node();

//	fprintf(dump_file,"\nStart Node %d\n",s);
	set< unsigned int > intervals = get_interval_set();
	graph_type edges = get_edge_list();

	list< unsigned int > H;

	interval_graph g;
	unsigned int i = 1;

//	fprintf(dump_file,"\nhiiiiiii\n");

	H.push_back(s);
	unsigned int x, y, h, z;
	unsigned int order;
	interval ix, iy;
	graph_type::iterator git;

	list< unsigned int >::iterator it;

	while(!H.empty())
	{
		h = H.front();
		H.pop_front();

		order = 0;

		interval I;
		I.set_id(interval_count++);
		I.set_header(h);
		I.set_pred_count(0);
		I.set_inter_order(0);
		I.set_inter_order(0);

//		fprintf(dump_file,"\nCreating Interval %d\n", I.get_id());

		list< unsigned int > Ih;

		Ih.push_back(h);
		ix = interval_map[h];

		if(ix.is_marked())
			continue;

//		ix.print_interval();

		ix.set_inter_order(order++);

//		fprintf(dump_file,"\nHellooo\n");
//		fprintf(dump_file,"\nHeader %d\n",h);
		bool no_edges = false;

		for(it = Ih.begin(); it != Ih.end(); it++)
		{
			x = *it;

			ix = interval_map[x];

//			fprintf(dump_file,"\nCalleer %d\n", x);

			if(ix.is_marked())
			{
//				fprintf(dump_file,"\nHeeee\n");
				no_edges = true;
				continue;
			}

//			fprintf(dump_file,"\nHiiii\n");
	
			ix.set_marked();
			interval_map[x] = ix;

			for(git = edges.begin(); git != edges.end(); git++)
			{
				z = get<0>(*git);

				if(z != x)
				{
					continue;
				}
				
				y = get<1>(*git);

				iy = interval_map[y];

//				fprintf(dump_file,"\nCallee %d\n", y);

				if(iy.get_pred_count() > 0)
					iy.set_pred_count(iy.get_pred_count() - 1);

				if(iy.get_reach() == 0)
				{
//					fprintf(dump_file,"\nReach == 0\n");
					
					iy.set_reach(h);
					interval_map[y] = iy;
//					fprintf(dump_file,"\nSetting Header %d\n",h, iy.get_reach());

					if(iy.get_pred_count() == 0)
					{
//						fprintf(dump_file,"\nPred Count == 0\n");
					
						Ih.push_back(y);
	
						iy.set_inter_order(order++);
					}
					else
					{
//						fprintf(dump_file,"\nPred Count != 0\n");
					
						if(find(H.begin(), H.end(), y) == H.end())
						{
							H.push_back(y);
						}
					}
				}
				else if(iy.get_reach() == h && iy.get_pred_count() == 0)
				{
//					fprintf(dump_file,"\nReach == h and Pred Count == 0\n");
					
					Ih.push_back(y);

					H.remove(y);
				}
			}

//			fprintf(dump_file,"\nNext Element of Ih\n");
		}

//		if(!no_edges)
		{
			
		I.set_node_list(Ih);
		I.set_reach(0);

		set< unsigned int > nodes = g.get_interval_set();
		graph_type edges1 = g.get_edge_list();
		unsigned int id = I.get_id();
		tuple< unsigned int, unsigned int > t;
	
		interval_map[id] = I;

		if(i == 1)
		{
			i++;
			g.set_start_node(id);

			nodes.insert(id);

			g.set_interval_set(nodes);
		}
		else
		{
//			fprintf(dump_file,"\nCreating Edges in Interval Graph\n");
			g = create_edges(g, I);
//			g.print_interval_graph();
		}

//		fprintf(dump_file,"\nNewly Created Interval in Reduced Graph\n");
		I = interval_map[id];
//		I.print_interval();
//		fprintf(dump_file,"\nIthe\n");
		}
	}


	#if 1
	if(get_interval_set().size() == g.get_interval_set().size() || (g.get_interval_set().size() == 1 && g.get_edge_list().size() == 0))
//	if(is_equal(g) || (g.get_interval_set().size() == 1 && g.get_edge_list().size() == 0))
	{
		reduce_graph_count++;
//		fprintf(dump_file,"\nReduced Interval Graph No %d Original Node Count %d Node Count %d\n", reduce_graph_count, get_interval_set().size(), g.get_interval_set().size());

		set< unsigned int >::iterator interval_it;

		#if 0
		for(interval_it = g.get_interval_set().begin(); interval_it != g.get_interval_set().end(); interval_it++)
		{
			fprintf(dump_file,"\nInterval %d Number of Nodes %d\n",*interval_it, interval_map[*interval_it].get_node_list().size());
		}
		#endif

//		fprintf(dump_file,"\nBase Condition for Graph Reducibility\n");

//		g.print_interval_graph();

		set_order_of_worklist_d();
		set_order_of_worklist();

		#if STATS
//		fprintf(dump_file,"\nGraph Reduction Process Terminates\n");
//		fprintf(dump_file,"\nFinal Interval Graph\n");
//		print_interval_graph();
//		fprintf(dump_file,"\nNumber of Steps Required for Interval Analysis = %d\n", reduce_graph_count);
		#endif
	}
	else
	{
//		fprintf(dump_file,"\nRecursive Call\n");
		reduce_graph_count++;
//		fprintf(dump_file,"\nReduced Interval Graph No %d Original Node Count %d Node Count %d\n", reduce_graph_count, get_interval_set().size(), g.get_interval_set().size());

		set< unsigned int >::iterator interval_it;

		#if 0
		for(interval_it = g.get_interval_set().begin(); interval_it != g.get_interval_set().end(); interval_it++)
		{
			fprintf(dump_file,"\nInterval %d Number of Nodes %d\n",*interval_it, interval_map[*interval_it].get_node_list().size());
		}
		#endif

//		g.print_interval_graph();
//		fprintf(dump_file,"\nReducing Graph\n");

//		g.print_interval_graph();

		g.reduce_interval_graph();	
//		g.set_order_of_worklist();
	}
	#endif
}

bool interval_graph::is_equal(interval_graph g)
{
	set< unsigned int > nodes1, nodes2;
		
//	fprintf(dump_file,"\nInside is_equal\n");

	graph_type edges1, edges2;

	nodes1 = get_interval_set();
	nodes2 = g.get_interval_set();

	edges1 = get_edge_list();
	edges2 = g.get_edge_list();

	set< unsigned int >::iterator sit1, sit2;
	graph_type::iterator git1, git2;

	if(nodes1.size() != nodes2.size())
	{
		return false;
	}	
	else if(edges1.size() != edges2.size())
	{
		return false;
	}

	interval I, J, K, L;
	int i = 0;

	for(sit1 = nodes1.begin(); sit1 != nodes1.end(); sit1++)
	{
		I = interval_map[*sit1];
//		I.print_interval();

		for(sit2 = nodes2.begin(); sit2 != nodes2.end(); sit2++)
		{
			J = interval_map[*sit2];

//			J.print_interval();

			if(I.is_equal(J))
			{
//				fprintf(dump_file,"\nIntervals Equal\n");
				i++;
				break;
			}
		}
	}
//	fprintf(dump_file,"\nI %d\n",i);
//	fprintf(dump_file,"\nNode Size %d\n",nodes1.size());

	if( i != nodes1.size())
	{
		return false;
	}

	i = 0;

	for(git1 = edges1.begin(); git1 != edges1.end(); git1++)
	{
		I = interval_map[get<0>(*git1)];
		J = interval_map[get<1>(*git1)];

		for(git2 = edges2.begin(); git2 != edges2.end(); git2++)
		{
			K = interval_map[get<0>(*git2)];
			L = interval_map[get<1>(*git2)];

			if(I.is_equal(K) && J.is_equal(L))
			{
				i++;
				break;
			}
		}
	}

	if( i != edges1.size())
	{
		return false;
	}

	return true;

}

/*
bool operator<(const il & i1, const il & i2)
{
        if(i1.deref_list < i2.deref_list)
                return true;

        return false;
}
*/

bool operator==(const interval_graph & g1, const interval_graph & g2)
{
	graph_type::iterator it1, it2;
	interval il1, il2, ir1, ir2;
	bool match;
	graph_type edges1, edges2;

	edges1 = g1.edge_list;
	edges2 = g2.edge_list;

        if(g1.interval_set == g2.interval_set)
	{
		if(edges1.size() == edges2.size())
		{
			for(it1 = edges1.begin(); it1 != edges1.end(); it1++)
			{
				il1 = interval_map[get<0>(*it1)];
				ir1 = interval_map[get<1>(*it1)];

				match = false;

				for(it2 = edges2.begin(); it2 != edges2.end(); it2++)
				{
					il2 = interval_map[get<0>(*it2)];
					ir2 = interval_map[get<1>(*it2)];

					if(il1 == il2 && ir1 == ir2)
					{
						match = true;
						break;
					}
				}

				if(!match)
				{
					return false;
				}
			}
			return true;
		}
	}

        return false;

}

void interval_graph::print_interval_graph()
{
	fprintf(dump_file,"\nPrinting Interval Graph\n");

	set< unsigned int > intervals = get_interval_set();
	graph_type edges = get_edge_list();

	list< unsigned int > nodes;

	list< unsigned int >:: iterator lit;
	graph_type::iterator it;
	set< unsigned int >::iterator sit;
	interval i;

	fprintf(dump_file,"\nNumber of Intervals in the Graph %d\n", intervals.size());
	fprintf(dump_file,"\nIntervals in the Graph\n");
	
	for(sit = intervals.begin(); sit != intervals.end(); sit++)
	{
		i = interval_map[*sit];
		i.print_interval();
	}

	fprintf(dump_file,"\nEdges between the Intervals in the Graph\n");

	for(it = edges.begin(); it != edges.end(); it++)
	{
		fprintf(dump_file,"\n%d -> %d\n", get<0>(*it), get<1>(*it));
	}

	fprintf(dump_file,"\nAfter Printing Interval Graph\n");
}

void find_interval_first_phase(unsigned int s)
{
//	fprintf(dump_file,"\nInside find_interval_first_phase\n");

//	create_call_graph();

//	fprintf(dump_file,"\nCall Graph Created\n");


	interval_count = func_num; 
	list< unsigned int > H;

	interval_graph g;
	set< unsigned int > intervals_nodes;

	H.push_back(s);

	struct cgraph_node *cnodex, *cnodey;

	unsigned int x, y, h;

	unsigned int order;
	struct cgraph_edge *edge;
	list< unsigned int >::iterator it;

	set_func::iterator sfit;
	set_func set_temp;

	unsigned int i = 1;
//	fprintf(dump_file,"\nInterval Count %d\n", interval_count);

	while(!H.empty())
	{
		h = H.front();
		H.pop_front();

		cnodex = func_numbering[h];

		if(((function_info *)(cnodex->aux))->is_marked())
			continue;
		
		interval I;
		I.set_id(interval_count);
		interval_count++;
		I.set_pred_count(0);
		I.set_inter_order(0);
		I.set_reach(0);
		I.reset_marked();

		list< unsigned int > Ih;

		Ih.push_back(h);
		I.set_header(h);
		order = 0;
		
		((function_info *)(cnodex->aux))->set_inter_order(order++);

//		fprintf(dump_file,"\nHeader %s %d\n", cgraph_node_name(cnodex), h);

		for(it = Ih.begin(); it != Ih.end(); it++)
		{
			x = *it;

			cnodex = func_numbering[x];

//			fprintf(dump_file,"\nCaller %s %d\n", cgraph_node_name(cnodex), x);

			if(((function_info *)(cnodex->aux))->is_marked())
			{
				continue;
			}
			
			((function_info *)(cnodex->aux))->set_marked();

			set_temp = callees[x];
//			set_temp = callees[((function_info *)(cnodex->aux))->func_num];

//			for(edge = cnodex->callees; edge; edge = edge->next_callee)
			for(sfit = set_temp.begin(); sfit != set_temp.end(); sfit++)
			{
				cnodey = func_numbering[*sfit];
//				cnodey = edge->callee;

				if (!gimple_has_body_p (cnodey->decl) || cnodey->clone_of)
					continue;

				y = *sfit;
//				y = ((function_info *)(cnodey->aux))->func_num;

//				fprintf(dump_file,"\nCallee %s %d Count %d\n", cgraph_node_name(cnodey), y, ((function_info *)(cnodey->aux))->get_pred_count());

				if(((function_info *)(cnodey->aux))->get_pred_count() > 0)
					((function_info *)(cnodey->aux))->set_pred_count(((function_info *)(cnodey->aux))->get_pred_count() - 1);

//				fprintf(dump_file,"\nHiiiii\n");
//				fprintf(dump_file,"\nReach %d ID %d\n",((function_info *)(cnodey->aux))->get_reach(), I.get_id());

				if(((function_info *)(cnodey->aux))->get_reach() == 0)
				{

//					fprintf(dump_file,"\nReach == 0\n");

					((function_info *)(cnodey->aux))->set_reach(h);

					if(((function_info *)(cnodey->aux))->get_pred_count() == 0)
					{
//						fprintf(dump_file,"\nPred Count == 0\n");

						Ih.push_back(y);

						((function_info *)(cnodey->aux))->set_inter_order(order++);
					}
					else
					{
//						fprintf(dump_file,"\nPred Count != 0\n");

						if(find(H.begin(), H.end(), y) == H.end())
						{
							H.push_back(y);
						}
					}
				}
				else if(((function_info *)(cnodey->aux))->get_reach() == h && ((function_info *)(cnodey->aux))->get_pred_count() == 0)
				{
//					fprintf(dump_file,"\nReach == h and Pred Count == 0\n");

					Ih.push_back(y);
					((function_info *)(cnodey->aux))->set_inter_order(order++);
				
					H.remove(y);
				}	
				
			}

//			fprintf(dump_file,"\nNext Element of Ih\n");
		}

		I.set_node_list(Ih);
		unsigned int id = I.get_id();

		if(i == 1)
		{
			i++;

			I.set_pred_count(0);

			g.set_start_node(id);

			intervals_nodes.insert(id);
//			fprintf(dump_file,"\nTesting Interval ID %d\n",id);

			interval_map[id] = I;
			g.set_interval_set(intervals_nodes);
		}
		else
		{
			interval_map[id] = I;
			g.create_edges_first_phase(I);
		}

//		fprintf(dump_file,"\nNewly Created Interval\n");
//		I = interval_map[id];
//		I.print_interval();	
//		interval_map[I.get_id()] = I;
	}

	// First phase Interval Graph Ready

	set< unsigned int > intervals = g.get_interval_set();
	graph_type edges_of_graph = g.get_edge_list();

//	g.print_interval_graph();

	if(intervals.size() == 1 && edges_of_graph.size() == 0)
	{
//		fprintf(dump_file,"\nReducible Graph\n");
//		g.print_interval_graph();

		// To Be Uncommented

		g.set_order_of_worklist_d();
		g.set_order_of_worklist();

		#if STATS
//		fprintf(dump_file,"\nFinal Interval Graph\n");
//		g.print_interval_graph();
//		fprintf(dump_file,"\nNumber of Steps Required for Interval Analysis = 1\n");
		#endif
	}
	else
	{	
//		fprintf(dump_file,"\nFirst Phase Intervals Created\n");	
//		g.print_interval_graph();
		reduce_graph_count++;
//		fprintf(dump_file,"\nReduced Interval Graph No %d Original Node Count %d Node Count %d\n", reduce_graph_count, func_num + 1, intervals.size());
		set< unsigned int >::iterator interval_it;

//		for(interval_it = intervals.begin(); interval_it != intervals.end(); interval_it++)
		{
//			fprintf(dump_file,"\nInterval %d Number of Nodes %d\n",*interval_it, interval_map[*interval_it].get_node_list().size());
		}

//		fprintf(dump_file,"\nReducing Graph\n");

//		g.print_interval_graph();

		g.reduce_interval_graph();
//		g.set_order_of_worklist();
	}
}

void print_edges(graph_type edges)
{
	graph_type::iterator it;

	fprintf(dump_file,"\nEdges of a Graph\n");
	
	for(it = edges.begin(); it != edges.end(); it++)
	{
		fprintf(dump_file,"\n%d -> %d\n", get<0>(*it), get<1>(*it));
	}

}

void print_nodes(set< unsigned int > intervals)
{
	set< unsigned int >::iterator sit;
	interval i;

	fprintf(dump_file,"\nNodes in a Graph\n");
	
	for(sit = intervals.begin(); sit != intervals.end(); sit++)
	{
		i = interval_map[*sit];
		i.print_interval();
	}
}
