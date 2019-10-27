#include "cgraph_node.hpp"

using namespace std;

map< unsigned int, vector< unsigned int > > function_info::get_indirect_callees()
{
	return indirect_callees;
}

void function_info::set_indirect_callees(map< unsigned int, vector< unsigned int > > m)
{
	indirect_callees = m;
}

bool function_info::has_fixed_pt()
{
	return fixed_pt;
}

void function_info::set_fixed_pt()
{
	fixed_pt = true;
}

void function_info::reset_fixed_pt()
{
	fixed_pt = false;
}

list< unsigned int > function_info::get_wrklist_points_red()
{
	return wrklist_points_red;
}

list< unsigned int > function_info::get_wrklist_dfv_red()
{
	return wrklist_dfv_red;
}

void function_info::set_wrklist_points_red(list< unsigned int > w)
{
	wrklist_points_red = w;
}

void function_info::set_wrklist_dfv_red(list < unsigned int > w)
{
	wrklist_dfv_red = w;
}

bool function_info::is_visited()
{
	return visited;
}

void function_info::set_visited(bool b)
{
	visited = b;
}

bool function_info::is_dvisited()
{
	return dvisited;
}

void function_info::set_dvisited(bool b)
{
	dvisited = b;
}

unsigned int function_info::get_num_bb()
{
	return num_bb;
}

void function_info::set_num_bb(unsigned int n)
{
	num_bb = n;
}

unsigned int function_info::get_end_block_index()
{
	return num_bb;
}

void function_info::set_end_block_index(unsigned int n)
{
	num_bb = n;
}

bool function_info::has_ret_type()
{
	return has_ret;
}

void function_info::set_ret_type()
{
	has_ret = true;
}

void function_info::reset_ret_type()
{
	has_ret = false;
}

bool function_info::is_empty_worklist(int x)
{
	int i;

//	fprintf(dump_file,"\nis_empty_worklist for function %s\n", cgraph_node_name(this));
	
	if(x == 1) // Check Liveness Worklist
	{
		for(i=0; i < num_bb; i++)
		{
			if(live_worklist[i])
			{
				return false;
			}
		}

		return true;
	}
	else if(x == 2) // Check Points-to Worklist
	{
//		fprintf(dump_file,"\nPoints-to Worklist with %d BB\n", num_bb);

		for(i=0; i < num_bb; i++)
		{
			if(points_worklist[i])
			{
//				fprintf(dump_file,"\nWorklist Not Empty\n");
				return false;
			}
		}

//		fprintf(dump_file,"\nWorklist Empty\n");

		return true;

	}			
}

set<unsigned int> function_info::get_params()
{
	return params;
}

void function_info::set_params(set<unsigned int> pr)
{
	params = pr;
}

void function_info::add_param(unsigned int x)
{
	set<unsigned int> temp;
	temp = get_params();
	temp.insert(x);
	set_params(temp);
}

#ifndef MRB
unsigned int function_info::get_ret_id()
{
	return ret_id;
}

void function_info::set_ret_id(unsigned int rt)
{
	ret_id = rt;
}
#endif	

#ifdef MRB
set< unsigned int > function_info::get_ret_id()
{
	return ret_id;
}

void function_info::set_ret_id(set< unsigned int > rt)
{
	ret_id = rt;
}
#endif

unsigned int function_info::get_pred_count()
{
	return pred_count;
}

void function_info::set_pred_count(unsigned int c)
{
	pred_count = c;
}

unsigned int function_info::get_multi_return()
{
	return multi_return;
}

void function_info::set_multi_return(unsigned int c)
{
	multi_return = c;
}


unsigned int function_info::get_reach()
{
	return reach;
}

void function_info::set_reach(unsigned int r)
{
	reach = r;
}

unsigned int function_info::get_inter_order()
{
	return inter_order;
}

void function_info::set_inter_order(unsigned int c)
{
	inter_order = c;
}

bool function_info::is_marked()
{
	return marked;
}

void function_info::set_marked()
{
	marked = true;
}

void function_info::reset_marked()
{
	marked = false;
}

unsigned int function_info::get_order()
{
	return order;
}

void function_info::set_order(unsigned int o)
{
	order = o;
}

void function_info::incre_order()
{
	unsigned int t = get_order();
	t++;
	set_order(t);
}


//////////////////////////////////////////////////////////////////


