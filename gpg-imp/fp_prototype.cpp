#include "fp_prototype.hpp"

map <int, Prototype> fn_details; // Function Prototypes
map <int, Prototype> fp_details; // Function Pointer Prototypes

Prototype::Prototype ()//(unsigned int args)
{
	//no_args = args;
}

Prototype::Prototype (unsigned int args, list <tree> param, tree ret)
{
	no_args = args;
	param_list = param;
	ret_value = ret;
}

/*void Prototype::set_no_args (unsigned int args)
{
	no_args = args;	
}*/

void Prototype::print ()
{
	fprintf (dump_file, " No of Args : %d", no_args);
	fprintf (dump_file, "\nArgs\n");
	
	for(list<tree>::iterator it = param_list.begin(); it != param_list.end(); it++)
	{
		print_generic_expr (dump_file, *it, 0);
	}	

	fprintf (dump_file, "\nReturn value\n");
	print_generic_expr (dump_file, ret_value, 0);
	fflush(dump_file);
}


bool compare_record_tree (tree t1, tree t2)
{

//	fprintf (dump_file, "\nIn compare_record_tree");
        tree tf1 = TYPE_FIELDS (t1);
        tree tf2 = TYPE_FIELDS (t2);
//my_print_node (dump_file, "\t\tfields", TYPE_FIELDS (*it), 0);

  //              fprintf (dump_file, "\n");
//            print_generic_expr (dump_file, tf1, 0);
  //          print_generic_expr (dump_file, tf2, 0);
expanded_location xloc1;
xloc1 = expand_location (DECL_SOURCE_LOCATION (tf1));

expanded_location xloc2;
xloc2 = expand_location (DECL_SOURCE_LOCATION (tf2));

//fprintf (dump_file, "\n\n\t -- my print -- file %s line %d \n", xloc1.file, xloc1.line);
//fprintf (dump_file, "\n\n\t -- my print -- file %s line %d \n", xloc2.file, xloc2.line);

	if (xloc1.line == xloc2.line && strcmp (xloc1.file, xloc2.file) == 0)
		return true;
//	fprintf (dump_file, "\nReturning false from compare_record_tree");
	return false; 
}

bool compare_tree (tree t1, tree t2, bool status)
{
//	fprintf (dump_file, "\nIn compare_tree");
//	print_node (dump_file, "\n\t t1", t1, 0);
//	print_node (dump_file, "\n\t t2", t2, 0);
	if (RECORD_OR_UNION_TYPE_P (t1) &&
		RECORD_OR_UNION_TYPE_P (t2))
	{
//		fprintf (dump_file, "\nIn RECORD TYPE");
//		if (compare_record_tree (t1, t2))
			return true;
//		return false;
	}

	else if (t1 == t2)
	{
//		fprintf (dump_file, "\nIn else if 1");
		return true;
	}
	else if (TREE_CODE (t1) == TREE_CODE (t2) && TREE_TYPE (t1) && TREE_TYPE (t2))
	{
//		fprintf (dump_file, "\nIn else if 2");
		return compare_tree (TREE_TYPE (t1), TREE_TYPE (t2), true);
	}
	else if ((TREE_CODE (t1) == VOID_TYPE || TREE_CODE (t2) == VOID_TYPE) && status)
	{
//		fprintf (dump_file, "\nIn else if 3");
		return true;
	}

	
//	fprintf (dump_file, "\nOut of compare_tree");
	return false;
}

bool Prototype::compare (Prototype p2)
{
	if (no_args == p2.no_args && compare_tree (ret_value, p2.ret_value, false))
	{
		list <tree>::iterator it1, it2;
		for (it1 = param_list.begin (), it2 = p2.param_list.begin (); it1 != param_list.end () ; ++it1, ++it2)
		{
			if (!compare_tree (*it1, *it2, false))
				return false;
		}
	
		return true;
	}
	return false;
}

void print_fn_details ()
{
	for (map <int, Prototype>::iterator it = fn_details.begin (); it != fn_details.end (); ++it)
	{
		fprintf (dump_file, "\nFn Uid : %d", it->first);
		it->second.print ();
	}
}

void print_fp_details ()
{
	for (map <int, Prototype>::iterator it = fp_details.begin (); it != fp_details.end (); ++it)
	{
		fprintf (dump_file, "\nFP Uid : %d", it->first);
		it->second.print ();
	}
}


