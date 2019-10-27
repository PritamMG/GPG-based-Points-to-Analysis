#include "parser.hpp"
#include "basic_block.hpp"
//#include "preprocess.hpp"
#include "cgraph_node.hpp"
#include "interval.hpp"
#include <string> 
//#include <sstream>

unsigned int data_phase;
struct cgraph_node *special_node;

list<struct cgraph_node * > order_func;
basic_block main_firstbb = NULL;
bool multi_rhs = false;
bool compute_only_pinfo = false;
bool compute_alias_and_pinfo = false;
//bool all_contexts_together = true;
bool check_deref = false;
bool deref_stmt = false;
alloc_pool constraint_pool;
alloc_pool csvarinfo_pool;
VEC(csvarinfo_t, heap) *csvarmap;
VEC(constraint_t, heap) *aliases;
VEC(constraint_t,heap) *constraints;
struct pointer_map_t *vi_for_tree;
struct cgraph_node * main_cnode, *global_cnode = NULL;
set<unsigned int> CDV;
set<unsigned int> globals;
unsigned int FCount = 0;

//list<basic_block> worklist;

unsigned int num_procs;

set< unsigned int > visited_list, bb_reachable_from_start, bb_reachable_from_exit;
set< unsigned int > all_succ_list;

set< unsigned int > to_be_processed_functions_for_fp; 

set< unsigned int > pred_succ_visited; 

map <unsigned int, tree> uid_to_tree;

map < gimple, set< unsigned int > > gimple_to_constraints;

set< unsigned int > processed_functions;

set< unsigned int > address_taken;

list< unsigned int > func_worklist, func_worklist_again, partial_func_worklist;
set< unsigned int > sym_gpgs;

set< struct cgraph_node * > indirect_cnodes;

list<struct cgraph_node * >::reverse_iterator cnode_it;

map< unsigned int, struct cgraph_node * > func_numbering;

unsigned long constraint_count = 0;
unsigned int call_site_count = 0;

bool switch_pass;

unsigned int num_bb_count = 0;

double preprocessing_time = 0;
double interval_analysis_time = 0;

func_map callers, callees, scc_callers, scc_callees;

double temptime = 0;

FILE *f;

#if 0
unsigned int index_func_array[FUNC_COUNT];
unsigned int func_index_array[FUNC_COUNT];

unsigned int index_func_array_d[FUNC_COUNT];
unsigned int func_index_array_d[FUNC_COUNT];

bool function_worklist[FUNC_COUNT];
bool preprocess_worklist[FUNC_COUNT];
bool function_worklist_d[FUNC_COUNT];
#endif

#if 1
unsigned int *index_func_array;
unsigned int *func_index_array;

unsigned int *index_func_array_d;
unsigned int *func_index_array_d;

bool *function_worklist;
bool *preprocess_worklist;
bool *function_worklist_d;

#endif


unsigned int func_count = 1;
unsigned int func_count_d = 1;
unsigned int test_func_count = 0;

unsigned int func_num = 1;

set< struct cgraph_node * > set_cnodes_call_graph;
bool print = false;

tree get_called_fn_decl (gimple stmt)
{
	gcc_assert(is_gimple_call(stmt));
	
	/* If we can resolve it here, its a simple function call. */
	
//	fprintf(dump_file,"\nCall\n");

	tree decl = gimple_call_fndecl (stmt);

	/* The call is through function pointer. */
	if (!decl)
		decl = gimple_call_fn (stmt);

	return decl;
}

bool associate_varinfo_to_alias (struct cgraph_node *node, void *data)
{      
  if (node->alias || node->thunk.thunk_p)
    cs_insert_vi_for_tree (node->decl, (csvarinfo_t)data);
  return false;
}  

/* Return the node to which the basic block belongs. */
#if 0
struct cgraph_node * cnode_of_bb (basic_block bb)
{
   return (struct cgraph_node *) (((block_information)(bb->aux)).get_cfun());
}
#endif

gimple bb_call_stmt (basic_block bb)
{
   gimple_stmt_iterator gsi;
   gimple stmt;
   for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi)) {
      stmt = gsi_stmt (gsi);
      if (is_gimple_call (stmt))
	{
         return stmt;
	}
   }

   return NULL;
}

basic_block start_bb_of_fn (struct cgraph_node *node)
{
	basic_block bb = ENTRY_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl));
	basic_block nn;
         edge e;
        edge_iterator ei;

//        if(((block_information *)(bb->aux))->end_block)
//              return nn;

        #if 1
        FOR_EACH_EDGE(e,ei,bb->succs)
        {
                if(e->dest == NULL)
                        continue;

                basic_block bt = e->dest;

//                fprintf(dump_file,"\nSucc of Entry Block %d -> %d %s\n", bb->index, bt->index, cgraph_node_name(node));

//		return bt;
        }
	#endif
	
   return ENTRY_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl))->next_bb;
}

basic_block end_bb_of_fn (struct cgraph_node *node)
{
	if(switch_pass)
		return EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl));

	#if 1
	unsigned int x = ((function_info *)(node->aux))->end_block_id;

	basic_block bb;

	struct function *fn;
	
	fn = DECL_STRUCT_FUNCTION(node->decl);

	if(x == 0)
	{
		bb = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl))->prev_bb;
	}
	else
	{
		bb = BASIC_BLOCK_FOR_FUNCTION(fn, x);
	}

	return bb;
	#endif

}

/* Return the position, in bits, of FIELD_DECL from the beginning of its
   structure.  */

HOST_WIDE_INT bitpos_of_field (const tree fdecl)
{
  if (!host_integerp (DECL_FIELD_OFFSET (fdecl), 0)
      || !host_integerp (DECL_FIELD_BIT_OFFSET (fdecl), 0))
    return -1;

  return (TREE_INT_CST_LOW (DECL_FIELD_OFFSET (fdecl)) * BITS_PER_UNIT
          + TREE_INT_CST_LOW (DECL_FIELD_BIT_OFFSET (fdecl)));
}

/* Create a new constraint consisting of LHS and RHS expressions.  */

constraint_t new_constraint (const struct constraint_expr lhs,
                const struct constraint_expr rhs)
{
  constraint_t ret = (constraint_t) pool_alloc (constraint_pool);
  ret->lhs = lhs;
  ret->rhs = rhs;
  return ret;
}

/* Return true if two constraint expressions A and B are equal.  */

bool constraint_expr_equal (struct constraint_expr a, struct constraint_expr b)
{
  return a.type == b.type && a.var == b.var && a.offset == b.offset;
}

/* Return true if two constraints A and B are equal.  */

bool constraint_equal (struct constraint a, struct constraint b)
{
  return constraint_expr_equal (a.lhs, b.lhs)
    && constraint_expr_equal (a.rhs, b.rhs);
}

/* Return a printable name for DECL  */

const char * alias_get_name (tree decl)
{
  const char *res;
  char *temp;
  int num_printed = 0;

  if (DECL_ASSEMBLER_NAME_SET_P (decl))
    res = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl));
  else
    res= get_name (decl);
  if (res != NULL)
    return res;

  res = "NULL";
  if (!dump_file)
    return res;

  if (TREE_CODE (decl) == SSA_NAME)
    {
      num_printed = asprintf (&temp, "%s_%u",
                              alias_get_name (SSA_NAME_VAR (decl)),
                              SSA_NAME_VERSION (decl));
    }
  else if (DECL_P (decl))
    {
      num_printed = asprintf (&temp, "D.%u", DECL_UID (decl));
    }
  if (num_printed > 0)
    {
      res = ggc_strdup (temp);
      free (temp);
    }
  return res;
}

/* Return true if V is a tree that we can have subvars for.
   Normally, this is any aggregate type.  Also complex
   types which are not gimple registers can have subvars.  */

bool var_can_have_subvars (const_tree v)
{
  /* Volatile variables should never have subvars.  */
  if (TREE_THIS_VOLATILE (v))
  {
    return false;
  }

  /* Non decls or memory tags can never have subvars.  */
  if (!DECL_P (v))
  {
    return false;
  }

  /* Aggregates without overlapping fields can have subvars.  */
  if (TREE_CODE (TREE_TYPE (v)) == RECORD_TYPE)
  {
    return true;
  }

  return false;
}

/* Return true if T is a type that does contain pointers.  */

bool type_must_have_pointers (tree t)
{
  if (POINTER_TYPE_P (t))
  {
    return true;
  }

  if (TREE_CODE (t) == ARRAY_TYPE)
  {
    return type_must_have_pointers (TREE_TYPE (t));
  }

  /* A function or method can have pointers as arguments, so track
     those separately.  */
  if (TREE_CODE (t) == FUNCTION_TYPE
      || TREE_CODE (t) == METHOD_TYPE)
  {
    return true;
  }

  if (RECORD_OR_UNION_TYPE_P (t))
  {
    return true;
  }

  return false;
}

void print_set_tree_nodes(set_tree_nodes res)
{
	for(set_tree_nodes::iterator it = res.begin(); it != res.end(); it++)
	{
		print_node(dump_file, "\n----------Tree Node --------\n", *it, 0);
	}	

	fprintf(dump_file, "\n\n");
}

bool must_have_fields(tree t)
{
//	print_node(dump_file, "\nTree Node in must_have_fields_new\n", t, 0);

//	if(AGGREGATE_TYPE_P (TREE_TYPE (t)) || RECORD_OR_UNION_TYPE_P (t) || var_can_have_subvars(t))
	if(RECORD_OR_UNION_TYPE_P (t) || var_can_have_subvars(t))
	{
//		fprintf(dump_file, "\nRecord Type\n");

		return true;
	}

	if (POINTER_TYPE_P (t))
	{
//		fprintf(dump_file, "\nPointer Type\n");

		if(TREE_TYPE(t))
		{
			t = TREE_TYPE(t);

			if(t)
			{
//				fprintf(dump_file, "\nTREE_TYPE Pointer Type\n");
				return must_have_fields(t);
			}
		}
	}

//	fprintf(dump_file, "\nReturning false in must_have_fields\n");

	return false;
}

bool isAggregrateNode(csvarinfo_t vi)
{
	tree t;

	if(vi)
	{
		if(vi->is_heap_var || vi->is_art_var)
		{
			return true;
		}	

		t = vi->decl;

		if(TREE_TYPE(t))
		{
			t = TREE_TYPE(t);

			if(t)
			{
				if(RECORD_OR_UNION_TYPE_P (t) || var_can_have_subvars(t))
				{
					return false;
				}

				return must_have_fields(t);
			}
		}
	}
}

bool isAggregrateNodeTree(tree t)
{
	csvarinfo_t vi;

	vi = cs_lookup_vi_for_tree(t);

	if(vi)
	{
		if(vi->is_heap_var || vi->is_art_var)
		{
			return true;
		}	

		if(TREE_TYPE(t))
		{
			t = TREE_TYPE(t);

			if(t)
			{
				if(RECORD_OR_UNION_TYPE_P (t) || var_can_have_subvars(t))
				{
					return false;
				}
	
				return must_have_fields(t);
			}
		}
	}

	return false;
}

bool field_must_have_pointers (tree t)
{
  return type_must_have_pointers (TREE_TYPE (t));
}


/* Given a TYPE, and a vector of field offsets FIELDSTACK, push all
   the fields of TYPE onto fieldstack, recording their offsets along
   the way.

   OFFSET is used to keep track of the offset in this entire
   structure, rather than just the immediately containing structure.
   Returns false if the caller is supposed to handle the field we
   recursed for.  */

/*
void check (VEC(fieldoff_s,heap) *fieldstack )
{
       if (VEC_length (fieldoff_s, fieldstack) <= 1
          || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {
       }
       else
}
*/

bool push_fields_onto_fieldstack (tree type, VEC(fieldoff_s,heap) **fieldstack, HOST_WIDE_INT offset)
{

  tree field;
  bool empty_p = true;

  if (TREE_CODE (type) != RECORD_TYPE)
    return false;


  /* If the vector of fields is growing too big, bail out early.
     Callers check for VEC_length <= MAX_FIELDS_FOR_FIELD_SENSITIVE, make
     sure this fails.  */
  if (VEC_length (fieldoff_s, *fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
    return false;


  for (field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    if (TREE_CODE (field) == FIELD_DECL)
      {
        bool push = false;
        HOST_WIDE_INT foff = bitpos_of_field (field);

        if (!var_can_have_subvars (field)
            || TREE_CODE (TREE_TYPE (field)) == QUAL_UNION_TYPE
            || TREE_CODE (TREE_TYPE (field)) == UNION_TYPE)
          push = true;
        else if (!push_fields_onto_fieldstack
                    (TREE_TYPE (field), fieldstack, offset + foff)
                 && (DECL_SIZE (field)
                     && !integer_zerop (DECL_SIZE (field))))
	{
          /* Empty structures may have actual size, like in C++.  So
             see if we didn't push any subfields and the size is
             nonzero, push the field onto the stack.  */
//	  check (*fieldstack);
          push = true;
	}

        if (push)
          {
            fieldoff_s *pair = NULL;
            bool has_unknown_size = false;
            bool must_have_pointers_p;

            if (!VEC_empty (fieldoff_s, *fieldstack))
	    {
//	      check (*fieldstack);
              pair = VEC_last (fieldoff_s, *fieldstack);
            }

            /* If there isn't anything at offset zero, create sth.  */
            if (!pair
                && offset + foff != 0)
              {
                pair = VEC_safe_push (fieldoff_s, heap, *fieldstack, NULL);
                pair->offset = 0;
                pair->size = offset + foff;
                pair->has_unknown_size = false;
                pair->must_have_pointers = false;
                pair->may_have_pointers = false;
                pair->only_restrict_pointers = false;
              }

            if (!DECL_SIZE (field)
                || !host_integerp (DECL_SIZE (field), 1))
              has_unknown_size = true;

//	    check (*fieldstack);

            /* If adjacent fields do not contain pointers merge them.  */
            must_have_pointers_p = field_must_have_pointers (field);
            if (pair
                && !has_unknown_size
                && !must_have_pointers_p
                && !pair->must_have_pointers
                && !pair->has_unknown_size
                && pair->offset + (HOST_WIDE_INT)pair->size == offset + foff)
              {
                pair->size += TREE_INT_CST_LOW (DECL_SIZE (field));
              }
            else
              {
//	        check (*fieldstack);
                pair = VEC_safe_push (fieldoff_s, heap, *fieldstack, NULL);	// PROBLEM: fieldstack not working
//	        check (*fieldstack);
                pair->offset = offset + foff;
                pair->has_unknown_size = has_unknown_size;
                if (!has_unknown_size)
                  pair->size = TREE_INT_CST_LOW (DECL_SIZE (field));
                else
                  pair->size = -1;
                pair->must_have_pointers = must_have_pointers_p;
                pair->may_have_pointers = true;
                pair->only_restrict_pointers
                  = (!has_unknown_size
                     && POINTER_TYPE_P (TREE_TYPE (field))
                     && TYPE_RESTRICT (TREE_TYPE (field)));
              }
//	      check (*fieldstack);
          }

//	check (*fieldstack);
        empty_p = false;
      }

  return !empty_p;
}

/* Count the number of arguments DECL has, and set IS_VARARGS to true
   if it is a varargs function.  */

unsigned int count_num_arguments (tree decl, bool *is_varargs)
{
  unsigned int num = 0;
  tree t;

  /* Capture named arguments for K&R functions.  They do not
     have a prototype and thus no TYPE_ARG_TYPES.  */
  for (t = DECL_ARGUMENTS (decl); t; t = DECL_CHAIN (t))
    ++num;

  /* Check if the function has variadic arguments.  */
  for (t = TYPE_ARG_TYPES (TREE_TYPE (decl)); t; t = TREE_CHAIN (t))
    if (TREE_VALUE (t) == void_type_node)
      break;
  if (!t)
    *is_varargs = true;

  return num;
}

/* Return true if FIELDSTACK contains fields that overlap.
   FIELDSTACK is assumed to be sorted by offset.  */

bool check_for_overlaps (VEC (fieldoff_s,heap) *fieldstack)
{
  fieldoff_s *fo = NULL;
  unsigned int i;
  HOST_WIDE_INT lastoffset = -1;

  FOR_EACH_VEC_ELT (fieldoff_s, fieldstack, i, fo)
    {
      if (fo->offset == lastoffset)
        return true;
      lastoffset = fo->offset;
    }
  return false;
}

/* qsort comparison function for two fieldoff's PA and PB */
// This function cannot be made a member function of this class

int fieldoff_compare (const void *pa, const void *pb)
{
  const fieldoff_s *foa = (const fieldoff_s *)pa;
  const fieldoff_s *fob = (const fieldoff_s *)pb;
  unsigned HOST_WIDE_INT foasize, fobsize;

  if (foa->offset < fob->offset)
    return -1;
  else if (foa->offset > fob->offset)
    return 1;

  foasize = foa->size;
  fobsize = fob->size;
  if (foasize < fobsize)
    return -1;
  else if (foasize > fobsize)
    return 1;
  return 0;
}

/* Sort a fieldstack according to the field offset and sizes.  */

void sort_fieldstack (VEC(fieldoff_s,heap) *fieldstack)
{
  VEC_qsort (fieldoff_s, fieldstack, fieldoff_compare);
}

/*----------------------------------------------------------------------
  The base implementation. The method implements points-to analysis
  using callstrings method. All the functions that have _cs_ 
  prepended to their names have been lifted from tree-ssa-structalias.c
  ---------------------------------------------------------------------*/

/* Return the varmap element N */

csvarinfo_t cs_get_varinfo (unsigned int n)
{
   return VEC_index (csvarinfo_t, csvarmap, n);
}

/* Insert ID as the variable id for tree T in the vi_for_tree map.  */

void cs_insert_vi_for_tree (tree t, csvarinfo_t vi)
{
   void **slot = pointer_map_insert (vi_for_tree, t);
   gcc_assert (vi);
   gcc_assert (*slot == NULL);
   *slot = vi;
}

bool is_proper_var (unsigned int varid)
{
   return (varid > 2);
}

bool parm_decl (unsigned int varid)
{
   return (TREE_CODE (SSAVAR (cs_get_varinfo (varid)->decl))
          == PARM_DECL);
}

struct cgraph_node * scoping_fn (unsigned int varid)
{
   return cs_get_varinfo (varid)->scoping_function;
}

bool var_defined_in_cfun (unsigned int varid, struct cgraph_node * cnode)
{
   return (cnode == scoping_fn (varid));
}

bool global_var (unsigned int varid)
{
   return (cs_get_varinfo (varid)->is_global_var);
}

bool art_var (unsigned int varid)
{
  csvarinfo_t vi = cs_get_varinfo (varid);	
   return (vi->is_art_var || vi->is_heap_var);
}

bool unexpandable_var (unsigned int var, HOST_WIDE_INT offset)
{
   return (offset == 0 ||
           !is_proper_var (var) ||
           offset == UNKNOWN_OFFSET ||
           cs_get_varinfo (var)->is_heap_var);
}

/* Given a gimple tree T, return the constraint expression vector for it
   to be used as the rhs of a constraint.  */

void cs_get_constraint_for_rhs (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   gcc_assert (VEC_length (ce_s, *results) == 0);
   cs_get_constraint_for_1 (t, results, false, false, bb, cnode);
}

void create_cdv(csvarinfo_t var)
{
//   	unsigned index = VEC_length (csvarinfo_t, csvarmap);

	csvarinfo_t ret_cdv = (csvarinfo_t) pool_alloc (csvarinfo_pool);
	ret_cdv->id = var->id + 1;
//	ret_cdv->name = var->name; // cdv_name;
//	string str = std::string(var->name);
//	ret_cdv->name = str.c_str(); // cdv_name;
	char *temp = (char *)xmalloc(strlen(var->name)+1);
	strcpy(temp,var->name);
//	ret_cdv->name = strdup(var->name); // cdv_name;
	ret_cdv->name = (const char *)temp;
	ret_cdv->decl = var->decl;
	ret_cdv->is_unknown_size_var = var->is_unknown_size_var;
	ret_cdv->is_full_var = var->is_full_var;
	ret_cdv->is_heap_var = var->is_heap_var;
	ret_cdv->may_have_pointers = var->may_have_pointers;
	ret_cdv->is_global_var = var->is_global_var;
	ret_cdv->scoping_function = var->scoping_function;
	ret_cdv->next = NULL;
	VEC_safe_push (csvarinfo_t, heap, csvarmap, ret_cdv);

	CDV.insert(ret_cdv->id);
}

/* Return a new variable info structure consisting for a variable
   named NAME, and using constraint graph node NODE.  Append it
   to the vector of variable info structures.  */
csvarinfo_t cs_new_var_info (tree t, const char *name, struct cgraph_node * cnode)
{
   unsigned index = VEC_length (csvarinfo_t, csvarmap);
   csvarinfo_t ret = (csvarinfo_t) pool_alloc (csvarinfo_pool);
	
   ret->id = index;
   ret->name = name;

   ret->decl = t;
   ret->is_unknown_size_var = false;
   ret->is_full_var = (t == NULL_TREE);
   ret->is_heap_var = false;
   ret->is_art_var = false; // Added by Pritam
   ret->may_have_pointers = true;
   ret->is_global_var = (t == NULL_TREE);
   /* Vars without decl are artificial and do not have sub-variables.  */
   if (t && DECL_P (t))
     ret->is_global_var = (is_global_var (t)
                          /* We have to treat even local register variables
                             as escape points.  */
                          || (TREE_CODE (t) == VAR_DECL
                              && DECL_HARD_REGISTER (t)));
   //ret->constraints_with_vi_as_lhs = NULL;
//   ret->scoping_function = (ret->is_global_var) ? NULL : cnode;
   ret->scoping_function = cnode;
   ret->next = NULL;


   VEC_safe_push (csvarinfo_t, heap, csvarmap, ret); 

   if(ret->is_global_var)
   {	
	globals.insert(index);	
   }

  	if(ret->id > 4 && !(is_ssa_var(ret->id)) && TREE_CODE (t) != FUNCTION_DECL)
	{
	        create_cdv(ret);
	}

   return ret;
}

/* Create a varinfo structure for NAME and DECL, and add it to VARMAP.
   This will also create any varinfo structures necessary for fields
   of DECL.  */

csvarinfo_t cs_create_variable_info_for_1 (tree decl, const char *name, struct cgraph_node * cnode)
{

   csvarinfo_t vi, newvi;
   tree decl_type = TREE_TYPE (decl);
   tree declsize = DECL_P (decl) ? DECL_SIZE (decl) : TYPE_SIZE (decl_type);
   VEC (fieldoff_s,heap) *fieldstack = NULL;
   fieldoff_s *fo;
   unsigned int i;

   if (!declsize || !host_integerp (declsize, 1)) {
      vi = cs_new_var_info (decl, name, cnode);
      vi->offset = 0;
      vi->size = ~0;
      vi->fullsize = ~0;
      vi->is_unknown_size_var = true;
      vi->is_full_var = true;
      vi->may_have_pointers = true;
      return vi;
   }
   /* Collect field information.  */
   if (var_can_have_subvars (decl)
      /* ???  Force us to not use subfields for global initializers
	 in IPA mode.  Else we'd have to parse arbitrary initializers.  */
      && !(is_global_var (decl) && DECL_INITIAL (decl))) {
//	fprintf(dump_file,"\nInside create variable %s\n",name);

       fieldoff_s *fo = NULL;
       bool notokay = false;
       unsigned int i;

       push_fields_onto_fieldstack (decl_type, &fieldstack, 0);
/*
       if (VEC_length (fieldoff_s, fieldstack) <= 1
          || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {
       }
       else

       if (VEC_length (fieldoff_s, fieldstack) <= 1)
       if (VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
       else
*/

       for (i = 0; !notokay && VEC_iterate (fieldoff_s, fieldstack, i, fo); i++)
	   if (fo->has_unknown_size || fo->offset < 0) {
	       notokay = true;
	       break;
	   }

          /* We can't sort them if we have a field with a variable sized type,
 	  which will make notokay = true.  In that case, we are going to return
	  without creating varinfos for the fields anyway, so sorting them is a
	  waste to boot.  */
       if (!notokay) {

	   sort_fieldstack (fieldstack);
	   /* Due to some C++ FE issues, like PR 22488, we might end up
	      what appear to be overlapping fields even though they,
	      in reality, do not overlap.  Until the C++ FE is fixed,
	      we will simply disable field-sensitivity for these cases.  */
	   notokay = check_for_overlaps (fieldstack);
       }

       if (notokay)
	   VEC_free (fieldoff_s, heap, fieldstack);
   }

/*
   if (VEC_length (fieldoff_s, fieldstack) <= 1)
   if (VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
   else
*/

   /* If we didn't end up collecting sub-variables create a full
      variable for the decl.  */
   if (VEC_length (fieldoff_s, fieldstack) <= 1
      || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {

       vi = cs_new_var_info (decl, name, cnode);
       vi->offset = 0;
       vi->may_have_pointers = true;
       vi->fullsize = TREE_INT_CST_LOW (declsize);
       vi->size = vi->fullsize;
       vi->is_full_var = true;
       VEC_free (fieldoff_s, heap, fieldstack);
       return vi;
   }


   vi = cs_new_var_info (decl, name, cnode);
   vi->fullsize = TREE_INT_CST_LOW (declsize);
   for (i = 0, newvi = vi;
       VEC_iterate (fieldoff_s, fieldstack, i, fo);
       ++i, newvi = newvi->next) {


       const char *newname = "NULL";
       char *tempname;

       if (dump_file) {
	   asprintf (&tempname, "%s." HOST_WIDE_INT_PRINT_DEC
		    "+" HOST_WIDE_INT_PRINT_DEC, name, fo->offset,fo->size);
	   newname = ggc_strdup (tempname);
	   free (tempname);

       }
       newvi->name = newname;
       newvi->offset = fo->offset;
       newvi->size = fo->size;
       newvi->fullsize = vi->fullsize;
       newvi->may_have_pointers = fo->may_have_pointers;
       // newvi->only_restrict_pointers = fo->only_restrict_pointers;
       if (i + 1 < VEC_length (fieldoff_s, fieldstack))
	   newvi->next = cs_new_var_info (decl, name, cnode);
   }

   VEC_free (fieldoff_s, heap, fieldstack);
   if (vi)
 	  return vi;
}

unsigned int cs_create_variable_info_for (tree decl, const char *name, basic_block bb, struct cgraph_node * cnode)
{
   csvarinfo_t vi = cs_create_variable_info_for_1 (decl, name, cnode);
   unsigned int id = vi->id;

   cs_insert_vi_for_tree (decl, vi);

#if 0
   /* Create initial constraints for globals.  */
   for (; vi; vi = vi->next) {
       if (!vi->may_have_pointers || !vi->is_global_var)
           continue;

       /* If this is a global variable with an initializer,
          generate constraints for it. */
       if (DECL_INITIAL (decl)) {
           VEC (ce_s, heap) *rhsc = NULL;
           struct constraint_expr lhs, *rhsp;
           unsigned i;
           cs_get_constraint_for_rhs (DECL_INITIAL (decl), &rhsc, main_firstbb, main_cnode);
           lhs.var = vi->id;
           lhs.offset = 0;
           lhs.type = SCALAR;
           FOR_EACH_VEC_ELT (ce_s, rhsc, i, rhsp)               // Vini: Why commented out????
               cs_process_constraint (new_constraint (lhs, *rhsp), main_firstbb);
           VEC_free (ce_s, heap, rhsc);                 // Vini: Why commented out????
       }
    }
#endif
   return id;
}


/* Find the variable id for tree T in the map. If T doesn't 
  exist in the map, create an entry for it and return it. */

csvarinfo_t cs_get_vi_for_tree (tree stmt, basic_block bb, struct cgraph_node * cnode)
{
	tree t;

	if(switch_pass)
	{
		t = stmt;
	}
	else
	{
		t = SSAVAR (stmt);
	}

   void **slot = pointer_map_contains (vi_for_tree, t);

   if (slot == NULL)
   {
//	fprintf(dump_file,"\nNew var\n");
//	print_generic_expr(dump_file, t, 0);
//	fprintf(dump_file,"\n\n");

       csvarinfo_t vi = cs_get_varinfo (cs_create_variable_info_for (t, alias_get_name (t), bb, cnode));
//	fprintf(dump_file,"\nNew Var Name %s-%d\n", alias_get_name(t), vi->id);
       if (vi)
       return vi;
       //return cs_get_varinfo (cs_create_variable_info_for (t, alias_get_name (t), bb, cnode));
   }

//	fprintf(dump_file,"\nAlready exists var\n");
//	print_generic_expr(dump_file, t, 0);
//	fprintf(dump_file,"\n\n");

   csvarinfo_t vi = (csvarinfo_t) *slot;

//	fprintf(dump_file,"\nIts vi\n");
//	print_generic_expr(dump_file, vi->decl, 0);
//	fprintf(dump_file,"\n\nvi ID: %d\n", vi->id);
   if (vi)
   	return (csvarinfo_t) *slot;

}

/* Find the variable info for tree T in VI_FOR_TREE. If T does not
   exist in the map, return NULL, otherwise, return the varinfo 
   we found.  */

csvarinfo_t cs_lookup_vi_for_tree (tree t)
{
   void **slot = pointer_map_contains (vi_for_tree, t);
   if (slot == NULL)
       return NULL;

   return (csvarinfo_t) *slot;
}

/* Get a scalar constraint expression for a new temporary variable.  */

struct constraint_expr cs_new_scalar_tmp_constraint_exp (const char *name, struct cgraph_node * cnode)
{
   struct constraint_expr tmp;
   csvarinfo_t vi;

   vi = cs_new_var_info (NULL_TREE, name, cnode);
   vi->offset = 0;
   vi->size = -1;
   vi->fullsize = -1;
   vi->is_full_var = 1;

   tmp.var = vi->id;
   tmp.type = SCALAR;
   tmp.offset = 0;

   return tmp;
}

/* CHANGE DUE TO GCC-4.7.2
   function make_heapvar_for of gcc-4.6.* is modified to make_heapvar in gcc-4.7.2.
   This cs_make_heapvar_for is also modified */

/* Temporary storage for fake var decls.  */
struct obstack fake_var_decl_obstack;

/* Build a fake VAR_DECL acting as referrer to a DECL_UID.  */

tree build_fake_var_decl (tree type)
{
  tree decl = (tree) XOBNEW (&fake_var_decl_obstack, struct tree_var_decl);
  memset (decl, 0, sizeof (struct tree_var_decl));
  TREE_SET_CODE (decl, VAR_DECL);
  TREE_TYPE (decl) = type;
  DECL_UID (decl) = allocate_decl_uid ();
  SET_DECL_PT_UID (decl, -1);
  layout_decl (decl, 0);
  return decl;
}

/* Create a new artificial heap variable with NAME.
   Return the created variable.  */

csvarinfo_t cs_make_heapvar_for (csvarinfo_t lhs, const char *name, struct cgraph_node * cnode)
{
  csvarinfo_t vi;
  tree heapvar;
  const char *newname = "NULL";
  char *tempname;

//  heapvar = build_fake_var_decl (ptr_type_node);


//  else	

  /* Append 'heap' with the its index in csvarinfo. */
  asprintf (&tempname, "%s.%d", name, VEC_length (csvarinfo_t, csvarmap));
  newname = ggc_strdup (tempname);

  heapvar = build_fake_var_decl (ptr_type_node);
  DECL_EXTERNAL (heapvar) = 1;
  vi = cs_new_var_info (heapvar, newname, cnode);

//  fprintf(dump_file,"\nNewName %s\n", newname);	

  //vi->is_artificial_var = true;
  vi->is_heap_var = true;
  vi->is_art_var = true;   // Added by Pritam
  vi->is_unknown_size_var = true;
  vi->offset = 0;
  vi->fullsize = ~0;
  vi->size = ~0;
  vi->is_full_var = true;
  cs_insert_vi_for_tree (heapvar, vi);

  return vi;
}

bool is_aggregrate_type_tree(tree t)
{
	csvarinfo_t vi;

	vi = cs_lookup_vi_for_tree(t);

	#if 0
	if (TREE_CODE (TREE_TYPE (t)) == POINTER_TYPE)
//	if (POINTER_TYPE_P (t))
	{
		fprintf(dump_file, "\nPointer Type\n");
		fprintf(dump_file, "\nVi Var %s %d\n", get_var_name(vi->id), vi->id);

		if(TREE_TYPE(t))
		{
			is_aggregrate_type_tree(TREE_TYPE(t));	
		}
	}
	#endif

	if(!vi)
	{
		if(vi->is_heap_var || vi->is_art_var || AGGREGATE_TYPE_P (TREE_TYPE (t)) || RECORD_OR_UNION_TYPE_P (t) || var_can_have_subvars(t))
		{
			return true;
		}	
	}

	return false;
}

bool is_aggregrate_type_varinfo(csvarinfo_t vi)
{
	tree t;

	t = vi->decl;

	if(t != NULL)
	{
//		print_node(dump_file, "tree node", t, 0);

		return is_aggregrate_type_tree(t);
	}

	return false;
}


/* Create a constraint ID = &FROM. */
void cs_make_constraint_from (csvarinfo_t vi, int from, basic_block bb)
{
   struct constraint_expr lhs, rhs;

   lhs.var = vi->id;
   lhs.offset = 0;
   lhs.type = SCALAR;

   rhs.var = from;
   rhs.offset = 0;
   rhs.type = ADDRESSOF;
   cs_process_constraint (new_constraint (lhs, rhs), bb);
}

/* Create a new artificial heap variable with NAME and make a
   constraint from it to LHS.  Return the created variable.  */

csvarinfo_t cs_make_constraint_from_heapvar (csvarinfo_t lhs, const char *name, basic_block bb, struct cgraph_node * cnode)
{
   csvarinfo_t vi = cs_make_heapvar_for (lhs, name, cnode);
//   cs_do_structure_copy (lhs->decl, vi->decl, bb, cnode);	
   cs_make_constraint_from (lhs, vi->id, bb);
//   fprintf(dump_file,"\nHeap Object Created\n");	
   	
   return vi;
}

/* Find the first varinfo in the same variable as START that overlaps with
   OFFSET.  If there is no such varinfo the varinfo directly preceding
   OFFSET is returned.  */

csvarinfo_t cs_first_or_preceding_vi_for_offset (csvarinfo_t start, unsigned HOST_WIDE_INT offset)
{
   /* If we cannot reach offset from start, lookup the first field
      and start from there.  */
   if (start->offset > offset)
       start = cs_lookup_vi_for_tree (start->decl);

   /* We may not find a variable in the field list with the actual
      offset when when we have glommed a structure to a variable.
      In that case, however, offset should still be within the size
      of the variable.
      If we got beyond the offset we look for return the field
      directly preceding offset which may be the last field.  */
   while (start->next && offset >= start->offset
         && !((offset - start->offset) < start->size))
       start = start->next;

   return start;
}

/* Dereference the constraint expression CONS, and return the result.
   DEREF (ADDRESSOF) = SCALAR
   DEREF (SCALAR) = DEREF
   DEREF (DEREF) = (temp = DEREF1; result = DEREF(temp))
   This is needed so that we can handle dereferencing DEREF constraints.  */

void cs_do_deref (VEC (ce_s, heap) **constraints, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr *c;
   unsigned int i = 0;

   FOR_EACH_VEC_ELT (ce_s, *constraints, i, c) {
//       c->ptr_arith = false; 	
       if (c->type == SCALAR)
           c->type = DEREF;
       else if (c->type == ADDRESSOF)
           c->type = SCALAR;
       else if (c->type == DEREF) {
           struct constraint_expr tmplhs;
           tmplhs = cs_new_scalar_tmp_constraint_exp ("dereftmp", cnode);
           cs_process_constraint (new_constraint (tmplhs, *c), bb);
           c->var = tmplhs.var;
       }
       else
           gcc_unreachable ();
   }
}

/* Get constraint expressions for offsetting PTR by OFFSET.  Stores the
   resulting constraint expressions in *RESULTS.  */

void cs_get_constraint_for_ptr_offset (tree ptr, tree offset,
			       VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr c;
   unsigned int j, n;
   HOST_WIDE_INT rhsunitoffset, rhsoffset;

   if (offset == NULL_TREE || !host_integerp (offset, 0))
       rhsoffset = UNKNOWN_OFFSET;
   else {
       /* Make sure the bit-offset also fits.  */
       rhsunitoffset = TREE_INT_CST_LOW (offset);
       rhsoffset = rhsunitoffset * BITS_PER_UNIT;
       if (rhsunitoffset != rhsoffset / BITS_PER_UNIT)
	   rhsoffset = UNKNOWN_OFFSET;
   }

   cs_get_constraint_for_rhs (ptr, results, bb, cnode);
   if (rhsoffset == 0)
       return;

   /* As we are eventually appending to the solution do not use
      VEC_iterate here. */
   n = VEC_length (ce_s, *results);
   for (j = 0; j < n; j++) {
       csvarinfo_t curr;
       c = *VEC_index (ce_s, *results, j);
	
       curr = cs_get_varinfo (c.var);

       /* If this varinfo represents a full variable just use it. */
       if (c.type == ADDRESSOF && curr->is_full_var)
	{
	   c.offset = 0;
//	   c.ptr_arith = false; //For Pointer Arithmetic	
// 	   fprintf(dump_file,"\nPTR Arith2\n");
	}
       /* If we do not know the offset add all subfields. */
       else if (c.type == ADDRESSOF && rhsoffset == UNKNOWN_OFFSET) {
	   csvarinfo_t temp = cs_lookup_vi_for_tree (curr->decl);
	   do {
	       struct constraint_expr c2;
	       c2.var = temp->id;
	       c2.type = ADDRESSOF;
	       c2.offset = 0;
	       if (c2.var != c.var)
		{
//	   	   c2.ptr_arith = false; //For Pointer Arithmetic	
 //	   	   fprintf(dump_file,"\nPTR Arith3\n");
		   VEC_safe_push (ce_s, heap, *results, &c2);
		}
	       temp = temp->next;
	   } while (temp);
       }
       else if (c.type == ADDRESSOF) {
	   csvarinfo_t temp;
	   unsigned HOST_WIDE_INT offset = curr->offset + rhsoffset;

	   /* Search the sub-field which overlaps with the
	      pointed-to offset.  If the result is outside of the variable
	      we have to provide a conservative result, as the variable is
	      still reachable from the resulting pointer (even though it
	      technically cannot point to anything).  The last and first
	      sub-fields are such conservative results.
	      ???  If we always had a sub-field for &object + 1 then
	      we could represent this in a more precise way.  */
	   if (rhsoffset < 0 && curr->offset < offset)
	       offset = 0;
	   temp = cs_first_or_preceding_vi_for_offset (curr, offset);

	   /* If the found variable is not exactly at the pointed to
	     result, we have to include the next variable in the
	     solution as well.  Otherwise two increments by offset / 2
	     do not result in the same or a conservative superset
	     solution.  */
	   if (temp->offset != offset && temp->next != NULL) {
	       struct constraint_expr c2;
	       c2.var = temp->next->id;
	       c2.type = ADDRESSOF;
	       c2.offset = 0;
//      	       c2.ptr_arith = false; //For Pointer Arithmetic	
//	       fprintf(dump_file,"\nPTR Arith4\n");
	       VEC_safe_push (ce_s, heap, *results, &c2);
	   }
	   c.var = temp->id;
	   c.offset = 0;
//  	   c.ptr_arith = false; //For Pointer Arithmetic	
//           fprintf(dump_file,"\nPTR Arith5\n");
       }
       else
	{
	   c.offset = rhsoffset;
	   c.ptr_arith = true;
//           fprintf(dump_file,"\nPTR Arith6\n");
	}

       VEC_replace (ce_s, *results, j, &c);
   }
}

/* Given a COMPONENT_REF T, return the constraint_expr vector for it.
   If address_p is true the result will be taken its address of.
   If lhs_p is true then the constraint expression is assumed to be used
   as the lhs.  */

void cs_get_constraint_for_component_ref (tree t, VEC(ce_s, heap) **results,
				  bool address_p, bool lhs_p, basic_block bb, struct cgraph_node * cnode)
{
//	fprintf(dump_file,"\n In parser.cpp component ref\n");

   tree orig_t = t;
   HOST_WIDE_INT bitsize = -1;
   HOST_WIDE_INT bitmaxsize = -1;
   HOST_WIDE_INT bitpos;
   tree forzero;
   struct constraint_expr *result;

   /* Some people like to do cute things like take the address of
     &0->a.b */
   forzero = t;
   while (handled_component_p (forzero)
	 || INDIRECT_REF_P (forzero)
	 || TREE_CODE (forzero) == MEM_REF)
       forzero = TREE_OPERAND (forzero, 0);

   if (CONSTANT_CLASS_P (forzero) && integer_zerop (forzero)) {
       struct constraint_expr temp;
       temp.offset = 0;
       temp.var = readonly_id;
       temp.type = SCALAR;
//       temp.ptr_arith = false;	
       VEC_safe_push (ce_s, heap, *results, &temp);
       return;
   }

   /* Handle type-punning through unions. If we are extracting a pointer
      from a union via a possibly type-punning access that pointer
      points to anything, similar to a conversion of an integer to
      a pointer.  */
   if (!lhs_p) {
      tree u;
      for (u = t;
	   TREE_CODE (u) == COMPONENT_REF || TREE_CODE (u) == ARRAY_REF;
	   u = TREE_OPERAND (u, 0))
	if (TREE_CODE (u) == COMPONENT_REF
	    && TREE_CODE (TREE_TYPE (TREE_OPERAND (u, 0))) == UNION_TYPE) 
 	{
	/*
            struct constraint_expr temp;

            temp.offset = 0;
            temp.var = anything_id;
            temp.type = ADDRESSOF;
            VEC_safe_push (ce_s, heap, *results, &temp);
	*/
            return;
        }
   }

   t = get_ref_base_and_extent (t, &bitpos, &bitsize, &bitmaxsize);

   /* Pretend to take the address of the base, we'll take care of
      adding the required subset of sub-fields below.  */
   cs_get_constraint_for_1 (t, results, true, lhs_p, bb, cnode);
   if (VEC_length (ce_s, *results) == 0)
       return;
   else
       gcc_assert (VEC_length (ce_s, *results) == 1);
   
   result = VEC_last (ce_s, *results);
//   result->ptr_arith = false;

   if (result->type == SCALAR
       && cs_get_varinfo (result->var)->is_full_var)
       /* For single-field vars do not bother about the offset.  */
       result->offset = 0;
   else if (result->type == SCALAR) {
      /* In languages like C, you can access one past the end of an
	 array.  You aren't allowed to dereference it, so we can
	 ignore this constraint. When we handle pointer subtraction,
	 we may have to do something cute here.  */

      if ((unsigned HOST_WIDE_INT)bitpos < cs_get_varinfo (result->var)->fullsize
	  && bitmaxsize != 0) {
	  /* It's also not true that the constraint will actually start at the
	     right offset, it may start in some padding.  We only care about
	     setting the constraint to the first actual field it touches, so
	     walk to find it.  */
	  struct constraint_expr cexpr = *result;
	  csvarinfo_t curr;
	  VEC_pop (ce_s, *results);
	  cexpr.offset = 0;
	  for (curr = cs_get_varinfo (cexpr.var); curr; curr = curr->next) {
	      if (ranges_overlap_p (curr->offset, curr->size,
				    bitpos, bitmaxsize)) {
		  cexpr.var = curr->id;
//		  cexpr.ptr_arith = false;
		  VEC_safe_push (ce_s, heap, *results, &cexpr);
		  if (address_p)
		     break;
	       }
	   }
	   /* If we are going to take the address of this field then
	      to be able to compute reachability correctly add at least
	      the last field of the variable.  */
	   if (address_p && VEC_length (ce_s, *results) == 0) {
	       curr = cs_get_varinfo (cexpr.var);
	       while (curr->next)
		   curr = curr->next;
	       cexpr.var = curr->id;
//	       cexpr.ptr_arith = false;
	       VEC_safe_push (ce_s, heap, *results, &cexpr);
	   }
	   /*
	   else if (VEC_length (ce_s, *results) == 0)
            // Assert that we found *some* field there. The user couldn't be
            // accessing *only* padding.
            // Still the user could access one past the end of an array
            // embedded in a struct resulting in accessing *only* padding.
            // Or accessing only padding via type-punning to a type
            // that has a filed just in padding space.
            {
              cexpr.type = SCALAR;
              cexpr.var = anything_id;
              cexpr.offset = 0;
              VEC_safe_push (ce_s, heap, *results, &cexpr);
            }
	    */
       }
       else if (bitmaxsize == 0) {
	  if (dump_file && (dump_flags & TDF_DETAILS));
       }
       else
	  if (dump_file && (dump_flags & TDF_DETAILS));
   }
   else if (result->type == DEREF) {
      /* If we do not know exactly where the access goes say so.  Note
	 that only for non-structure accesses we know that we access
	 at most one subfiled of any variable.  */
       if (bitpos == -1 || bitsize != bitmaxsize
	  || AGGREGATE_TYPE_P (TREE_TYPE (orig_t))	/* Look into : Structure variables */
	  || result->offset == UNKNOWN_OFFSET)
	   result->offset = UNKNOWN_OFFSET;
       else
	   result->offset += bitpos;
   }
   else
       gcc_unreachable ();
}

/* Get a constraint expression vector from an SSA_VAR_P node.
   If address_p is true, the result will be taken its address of.  */

void cs_get_constraint_for_ssa_var (tree t, VEC(ce_s, heap) **results, bool address_p, basic_block bb, struct cgraph_node * cnode)
{

   struct constraint_expr cexpr;
   csvarinfo_t vi;

   /* We allow FUNCTION_DECLs here even though it doesn't make much sense. */
   gcc_assert (SSA_VAR_P (t) || DECL_P (t));


   /* For parameters, get at the points-to set for the actual parm decl. */
   if (TREE_CODE (t) == SSA_NAME
       && (TREE_CODE (SSA_NAME_VAR (t)) == PARM_DECL
 	  || TREE_CODE (SSA_NAME_VAR (t)) == RESULT_DECL)
       && SSA_NAME_IS_DEFAULT_DEF (t)) {
//       cs_get_constraint_for_ssa_var (t, results, address_p, bb, cnode); // Change made by Pritam
       cs_get_constraint_for_ssa_var (SSA_NAME_VAR (t), results, address_p, bb, cnode);

       return;
   }

   vi = cs_get_vi_for_tree (t, bb, cnode);
   cexpr.var = vi->id;

   cexpr.type = SCALAR;
//   cexpr.ptr_arith = false;	
   cexpr.offset = 0;

   /* If we are not taking the address of the constraint expr, add all
      sub-fiels of the variable as well.  */
/*
   if (!address_p)
   if (!vi->is_full_var)
   else
*/

   if (!address_p && !vi->is_full_var) {
      for (; vi; vi = vi->next) {
	   cexpr.var = vi->id;
	  

	   VEC_safe_push (ce_s, heap, *results, &cexpr);
      }
      return;
   }

   VEC_safe_push (ce_s, heap, *results, &cexpr);
}

/* Given a tree T, return the constraint expression for it.  */

void cs_get_constraint_for_1 (tree t, VEC (ce_s, heap) **results, bool address_p,
		      bool lhs_p, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr temp;

   /* x = integer is all glommed to a single variable, which doesn't
     point to anything by itself.  That is, of course, unless it is an
     integer constant being treated as a pointer, in which case, we
     will return that this is really the addressof anything.  This
     happens below, since it will fall into the default case. The only
     case we know something about an integer treated like a pointer is
     when it is the NULL pointer, and then we just say it points to
     NULL.

     Do not do that if -fno-delete-null-pointer-checks though, because
     in that case *NULL does not fail, so it _should_ alias *anything.
     It is not worth adding a new option or renaming the existing one,
     since this case is relatively obscure.  */
   if ((TREE_CODE (t) == INTEGER_CST && integer_zerop (t))
      /* The only valid CONSTRUCTORs in gimple with pointer typed
	 elements are zero-initializer.  But in IPA mode we also
	 process global initializers, so verify at least.  */
      || (TREE_CODE (t) == CONSTRUCTOR
	  && CONSTRUCTOR_NELTS (t) == 0)) {
       if (flag_delete_null_pointer_checks) {
	   temp.var = nothing_id;
           temp.type = ADDRESSOF;
           temp.offset = 0;
//	   temp.ptr_arith = false;	

           VEC_safe_push (ce_s, heap, *results, &temp);
       }
       return;
   }

  /* String constants are read-only. Don't consider them. 
   if (TREE_CODE (t) == STRING_CST)
       return;*/

   /* String constants are read-only. */
   if (TREE_CODE (t) == STRING_CST) {
      temp.var = readonly_id;
      temp.type = SCALAR;
      temp.offset = 0;
//      temp.ptr_arith = false;
      VEC_safe_push (ce_s, heap, *results, &temp);
      return;
   }

   switch (TREE_CODE_CLASS (TREE_CODE (t))) {
       case tcc_expression:
       {
           switch (TREE_CODE (t)) {
	       case ADDR_EXPR:

	           cs_get_constraint_for_address_of (TREE_OPERAND (t, 0), results, bb, cnode);
           return;
	        default:;
	   }
 	   break;
       }
       case tcc_reference:
       {
	   switch (TREE_CODE (t)) {
	       case MEM_REF:
	       {
	           struct constraint_expr cs;
	      	   csvarinfo_t vi, curr;
	           tree off = double_int_to_tree (sizetype, mem_ref_offset (t));
	      	   cs_get_constraint_for_ptr_offset (TREE_OPERAND (t, 0), off, results, bb, cnode);
                   if (VEC_length (ce_s, *results) == 0)
                       return;
	      	   cs_do_deref (results, bb, cnode);

	           /* If we are not taking the address then make sure to process
		      all subvariables we might access.  */
	      	   cs = *VEC_last (ce_s, *results);
//                   cs.ptr_arith = false;
	      	   if (address_p || cs.type != SCALAR)
		       return;

	      	   vi = cs_get_varinfo (cs.var);
	      	   curr = vi->next;
	      	   if (!vi->is_full_var && curr) {
		       unsigned HOST_WIDE_INT size;
		       if (host_integerp (TYPE_SIZE (TREE_TYPE (t)), 1))
		           size = TREE_INT_CST_LOW (TYPE_SIZE (TREE_TYPE (t)));
		       else
		           size = -1;
		       for (; curr; curr = curr->next) {
		      	   if (curr->offset - vi->offset < size) {
			       cs.var = curr->id;
			       VEC_safe_push (ce_s, heap, *results, &cs);
			   }
		           else
			       break;
		       }
		   }
	           return;
	       }
	       case ARRAY_REF:
	       case ARRAY_RANGE_REF:
	       case COMPONENT_REF:
	           cs_get_constraint_for_component_ref (t, results, address_p, lhs_p, bb, cnode);
	           return;
	       case VIEW_CONVERT_EXPR:
	           cs_get_constraint_for_1 (TREE_OPERAND (t, 0), results, address_p, lhs_p, bb, cnode);
	    	   return;
	       /* We are missing handling for TARGET_MEM_REF here.  */
	       default:;
	   }
	   break;
       }
       case tcc_exceptional:
       {
	   switch (TREE_CODE (t)) {
	       case SSA_NAME:
	       {
		   cs_get_constraint_for_ssa_var (t, results, address_p, bb, cnode);
	           return;
	       }
	       case CONSTRUCTOR:
	       {
	           unsigned int i;
	      	   tree val;
	      	   VEC (ce_s, heap) *tmp = NULL;
	      	   FOR_EACH_CONSTRUCTOR_VALUE (CONSTRUCTOR_ELTS (t), i, val) {
		       struct constraint_expr *rhsp;
		       unsigned j;
		       cs_get_constraint_for_1 (val, &tmp, address_p, lhs_p, bb, cnode);
		       FOR_EACH_VEC_ELT (ce_s, tmp, j, rhsp)
		           VEC_safe_push (ce_s, heap, *results, rhsp);
		       VEC_truncate (ce_s, tmp, 0);
		   }
	           VEC_free (ce_s, heap, tmp);
	           /* We do not know whether the constructor was complete,
	              so technically we have to add &NOTHinG or &ANYTHinG
		      like we do for an empty constructor as well.  */
	           return;
	       }
	       default:;
	   }
	   break;
       }
       case tcc_declaration:
       {
	   cs_get_constraint_for_ssa_var (t, results, address_p, bb, cnode);
	   return;
       }
       case tcc_constant:
	   return;
       default:;
   }
}


/* Efficiently generates constraints from all entries in *RHSC to all
   entries in *LHSC.  */

void cs_process_all_all_constraints (VEC (ce_s, heap) *lhsc, VEC (ce_s, heap) *rhsc, basic_block bb)
{
   struct constraint_expr *lhsp, *rhsp;
   unsigned i, j;

//   print_variable_data ();

   FOR_EACH_VEC_ELT (ce_s, lhsc, i, lhsp) {
       FOR_EACH_VEC_ELT (ce_s, rhsc, j, rhsp) {
//	   print_variable_data (lhsp->var);
//	   print_variable_data (rhsp->var);
           cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
           multi_rhs = true;
       }
       multi_rhs = false;
   }
}


/* Given a tree T, return the constraint expression for taking the
   address of it. */

void cs_get_constraint_for_address_of (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr *c;
   unsigned int i;

   cs_get_constraint_for_1 (t, results, true, true, bb, cnode);
   FOR_EACH_VEC_ELT (ce_s, *results, i, c) {
       if (c->type == DEREF)
           c->type = SCALAR;
       else
           c->type = ADDRESSOF;
//       c->ptr_arith = false;
   }
}

/* Given a gimple tree T, return the constraint expression vector for it.  */

void cs_get_constraint_for (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
  gcc_assert (VEC_length (ce_s, *results) == 0);
  cs_get_constraint_for_1 (t, results, false, true, bb, cnode);
}


/* Creation function node for DECL, using NAME, and return the index
   of the variable we've created for the function.  */

csvarinfo_t cs_create_func_info_for (tree decl, const char *name, struct cgraph_node * cnode)
{
   csvarinfo_t vi, prev_vi;
   tree arg;
   unsigned int i;
   bool is_varargs = false;
   unsigned int num_args = count_num_arguments (decl, &is_varargs);
   /* Create the variable info.  */
   vi = cs_new_var_info (decl, name, cnode);
   vi->offset = 0;
   vi->size = 1;
   vi->fullsize = num_args + 1;
   vi->may_have_pointers = false;
   if (is_varargs)
       vi->fullsize = ~0;
   cs_insert_vi_for_tree (vi->decl, vi);

   prev_vi = vi;

   /* Set up variables for each argument.  */
   arg = DECL_ARGUMENTS (decl);
   for (i = 1; i < num_args + 1; i++) {
       csvarinfo_t argvi;
       tree argdecl = decl;

       if (arg)
           argdecl = arg;

       argvi = cs_new_var_info (argdecl, alias_get_name (argdecl), cnode);
       unsigned int t = argvi->id;
//	fprintf(dump_file,"\nSetting parameter %s %d\n",alias_get_name(argdecl), t);	
       ((function_info *)(cnode->aux))->add_param(t);
       argvi->offset = i;
       argvi->size = 1;
       argvi->is_full_var = true;
       argvi->fullsize = vi->fullsize;
       if (arg)
       gcc_assert (prev_vi->offset < argvi->offset);
       prev_vi->next = argvi;
       prev_vi = argvi;
       if (arg) {
           cs_insert_vi_for_tree (arg, argvi);
           arg = DECL_CHAIN (arg);
       }
   }

   /* Add one representative for all further args.  */
   if (is_varargs) {
       csvarinfo_t argvi;
       const char *newname;
       char *tempname;
       tree decl;

       asprintf (&tempname, "%s.varargs", name);
       newname = ggc_strdup (tempname);
       free (tempname);

       /* CHANGE DUE TO GCC-4.7.2 */
       /* We need sth that can be pointed to for va_start.  */
       decl = build_fake_var_decl (ptr_type_node);

       /* According to gcc-4.6.*
       decl = create_tmp_var_raw (ptr_type_node, name);
       get_var_ann (decl); */

       argvi = cs_new_var_info (decl, newname, cnode);
       argvi->offset = 1 + num_args;
       argvi->size = ~0;
       argvi->is_full_var = true;
       argvi->is_heap_var = true;
       argvi->fullsize = vi->fullsize;
       gcc_assert (prev_vi->offset < argvi->offset);
       prev_vi->next = argvi;
       prev_vi = argvi;
   }

   return vi;
}

/* Find the first varinfo in the same variable as START that overlaps with
   OFFSET.  Return NULL if we can't find one.  */

csvarinfo_t cs_first_vi_for_offset (csvarinfo_t start, unsigned HOST_WIDE_INT offset)       /* Look into */
{
//	fprintf(dump_file,"\n123 --- %d - %s\n", start->id, get_var_name(start->id));

   offset += start->offset;

   /* If the offset is outside of the variable, bail out.  */
   if (offset >= start->fullsize)
	{
//		fprintf(dump_file,"\n NULL\n");
       return NULL;
	}

//	fprintf(dump_file,"\n456\n");

   /* If we cannot reach offset from start, lookup the first field
      and start from there.  */
   if (start->offset > offset)
       start = cs_lookup_vi_for_tree (start->decl);

//	fprintf(dump_file,"\n789\n");

   while (start) {
      /* We may not find a variable in the field list with the actual
         offset when when we have glommed a structure to a variable.
         In that case, however, offset should still be within the size
         of the variable. */
       if (offset >= start->offset
           && (offset - start->offset) < start->size)
           return start;

       start= start->next;
   }

//	fprintf(dump_file,"\nABC\n");

   return NULL;
}

set< unsigned int > cs_get_all_vi_for_offset (csvarinfo_t start, unsigned HOST_WIDE_INT offset)       /* Look into */
{
//	fprintf(dump_file,"\n123 --- %d - %s\n", start->id, get_var_name(start->id));

	set< unsigned int > res;

   offset += start->offset;

   /* If the offset is outside of the variable, bail out.  */
   if (offset >= start->fullsize)
	{
//		fprintf(dump_file,"\n NULL\n");
       return res;
	}

//	fprintf(dump_file,"\n456\n");

   /* If we cannot reach offset from start, lookup the first field
      and start from there.  */
   if (start->offset > offset)
   {	
       start = cs_lookup_vi_for_tree (start->decl);
       if(field_must_have_pointers (start->decl))
		res.insert(start->id);
   }

//	fprintf(dump_file,"\n789\n");

   while (start) {
      /* We may not find a variable in the field list with the actual
         offset when when we have glommed a structure to a variable.
         In that case, however, offset should still be within the size
         of the variable. */
//       if (offset >= start->offset
//           && (offset - start->offset) < start->size)
//           return start;
//   if (offset >= start->fullsize)
       {
		if(field_must_have_pointers (start->decl))
			res.insert(start->id);
       }

       start= start->next;
//	offset += start->offset;
   }

//	fprintf(dump_file,"\nABC\n");

   return res;
}


/* Handle aggregate copies by expanding into copies of the respective
   fields of the structures.  */

void cs_do_structure_copy (tree lhsop, tree rhsop, basic_block bb, struct cgraph_node * cnode)  /* Look into : Structure variables */
{
   struct constraint_expr *lhsp, *rhsp;
   VEC (ce_s, heap) *lhsc = NULL, *rhsc = NULL;
   unsigned j;

   cs_get_constraint_for (lhsop, &lhsc, bb, cnode);
   cs_get_constraint_for_rhs (rhsop, &rhsc, bb, cnode);

   lhsp = VEC_index (ce_s, lhsc, 0);
   rhsp = VEC_index (ce_s, rhsc, 0);


   // Commented by Vini, used by Prashant
//    if (lhsp->type == DEREF)
//       return;
//    if (rhsp->type == DEREF) {
//        gcc_assert (VEC_length (ce_s, rhsc) == 1);
//        rhsp->var = undef_id;
//        rhsp->offset = 0;
//        rhsp->type = ADDRESSOF;
//        cs_process_all_all_constraints (lhsc, rhsc, bb);
//    }

   // Added by Vini
   if (lhsp->type == DEREF || rhsp->type == DEREF)
   {
     if (lhsp->type == DEREF)
       {
         gcc_assert (VEC_length (ce_s, lhsc) == 1);
         lhsp->offset = UNKNOWN_OFFSET;
       }
     if (rhsp->type == DEREF)
       {
         gcc_assert (VEC_length (ce_s, rhsc) == 1);
         rhsp->offset = UNKNOWN_OFFSET;
       }
     cs_process_all_all_constraints (lhsc, rhsc, bb);
   }

   else if (lhsp->type == SCALAR &&
            (rhsp->type == SCALAR || rhsp->type == ADDRESSOF)) {
       HOST_WIDE_INT lhssize, lhsmaxsize, lhsoffset;
       HOST_WIDE_INT rhssize, rhsmaxsize, rhsoffset;
       unsigned k = 0;
       get_ref_base_and_extent (lhsop, &lhsoffset, &lhssize, &lhsmaxsize);
       get_ref_base_and_extent (rhsop, &rhsoffset, &rhssize, &rhsmaxsize);
       for (j = 0; VEC_iterate (ce_s, lhsc, j, lhsp);) {
           csvarinfo_t lhsv, rhsv;
           rhsp = VEC_index (ce_s, rhsc, k);
           lhsv = cs_get_varinfo (lhsp->var);
           rhsv = cs_get_varinfo (rhsp->var);
          if (lhsv->may_have_pointers
               && (lhsv->is_full_var
                  || rhsv->is_full_var
                  || ranges_overlap_p (lhsv->offset + rhsoffset, lhsv->size,
                                       rhsv->offset + lhsoffset, rhsv->size)))
	   {
               cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
	   }
           if (!rhsv->is_full_var && (lhsv->is_full_var
                  || (lhsv->offset + rhsoffset + lhsv->size
                      > rhsv->offset + lhsoffset + rhsv->size))) {
               ++k;
               if (k >= VEC_length (ce_s, rhsc))
                   break;
           }
           else
	   {
               ++j;
           }
       }
   }
   else
   {
       gcc_unreachable ();
   }


   VEC_free (ce_s, heap, lhsc);
   VEC_free (ce_s, heap, rhsc);
}

void cs_init_base_vars (struct cgraph_node * cnode)
{
  // csvarinfo_t var_nothing, var_integer, var_undef;
 csvarinfo_t var_nothing, var_readonly, var_escaped, var_undef, var_summ_node;

   /* Create an UNKNOWN variable, for unknown pointer values. */
   var_undef = cs_new_var_info (NULL_TREE, "undef", cnode);
   gcc_assert (var_undef->id == undef_id);
//   gcc_assert (var_undef->name == "undef");
   var_undef->offset = 0;
   var_undef->size = ~0;
   var_undef->fullsize = ~0;
   var_undef->next = NULL;

   /* Create the NULL variable, used to represent that a variable points
      to NULL.  */
   var_nothing = cs_new_var_info (NULL_TREE, "null", cnode);
   gcc_assert (var_nothing->id == nothing_id);
//   gcc_assert (var_nothing->name == "null");
   var_nothing->offset = 0;
   var_nothing->size = ~0;
   var_nothing->fullsize = ~0;

   /* Create the INTEGER variable, used to represent that a variable points
     to what an INTEGER "points to".  
   var_integer = cs_new_var_info (NULL_TREE, "integer", cnode);
   gcc_assert (var_integer->id == integer_id);
   var_integer->size = ~0;
   var_integer->fullsize = ~0;
   var_integer->offset = 0;
   var_integer->next = NULL;*/

   /* Create an ESCAPED variable, for escaped pointer values. */
   var_escaped = cs_new_var_info (NULL_TREE, "escaped", cnode);
   gcc_assert (var_escaped->id == escaped_id);
//   gcc_assert (var_escaped->name == "escaped");
   var_escaped->offset = 0;
   var_escaped->size = ~0;
   var_escaped->fullsize = ~0;
   var_escaped->next = NULL;

   /* Create the READONLY variable, used to represent string constants
      and integer pointers. */
   var_readonly = cs_new_var_info (NULL_TREE, "readonly", cnode);
   gcc_assert (var_readonly->id == readonly_id);
//   gcc_assert (var_readonly->name == "readonly");
   var_readonly->size = ~0;
   var_readonly->fullsize = ~0;
   var_readonly->offset = 0;
   var_readonly->next = NULL;

  /* Represents Summary Node */
   var_summ_node = cs_new_var_info (NULL_TREE, "summ_node", cnode);
   gcc_assert (var_summ_node->id == summ_node_id);
//   gcc_assert (var_readonly->name == "readonly");
   var_summ_node->size = ~0;
   var_summ_node->fullsize = ~0;
   var_summ_node->offset = 0;
   var_summ_node->next = NULL;

}

void cs_init_alias_vars (struct cgraph_node * cnode)
{
   csvarmap = VEC_alloc (csvarinfo_t, heap, 200);
   aliases = VEC_alloc (constraint_t, heap, 200);
   constraint_pool = create_alloc_pool ("Constraint pool", sizeof (struct constraint), 200);
   csvarinfo_pool = create_alloc_pool ("Variable pool", sizeof (struct csvariable_info), 200);
   vi_for_tree = pointer_map_create ();
   cs_init_base_vars (cnode);
   gcc_obstack_init (&fake_var_decl_obstack);
}

tree cs_get_var (tree t)
{
   if (TREE_CODE (t) == MEM_REF) {
       t = TREE_OPERAND (t, 0);
       return cs_get_var (t);
   }
   return t;
}

tree cs_get_var1 (tree t)
{
   if (TREE_CODE (t) == MEM_REF) {
       t = TREE_OPERAND (t, 1);
       return cs_get_var (t);
   }
   return t;
}

/*-------------------------------------------------------------------------------------
  Function which processes the constraint t, retrieves the lhs and rhs of the pointsto
  constraint, and updates the alias pool. 
  ------------------------------------------------------------------------------------*/

void cs_process_constraint (constraint_t t, basic_block bb)
{
   struct constraint_expr rhs = t->rhs;
   struct constraint_expr lhs = t->lhs;

   gcc_assert (rhs.var < VEC_length (csvarinfo_t, csvarmap));
   gcc_assert (lhs.var < VEC_length (csvarinfo_t, csvarmap));

   if (!is_proper_var (lhs.var))
   {
       return;
   }

//	fprintf(dump_file,"\ncs_process_constraint BB %d lhs %s-%d rhs %s-%d\n", bb->index, get_var_name(lhs.var), lhs.var, get_var_name(rhs.var), rhs.var);

   // ADDRESSOF on the lhs is invalid.  
   gcc_assert (lhs.type != ADDRESSOF);

   if (check_deref) 
       deref_stmt = (rhs.type == DEREF || lhs.type == DEREF);

   // if (!compute_only_pinfo)
       insert_alias_in_pool (t, cs_get_varinfo (lhs.var), bb);

 /*  if (compute_alias_and_pinfo)
	{
       //compute_stmt_out_1 (cpinfo, t);
	}
   
   if (compute_only_pinfo)
	{
       //compute_stmt_out_2 (cpinfo, t);
	}*/
}

bool
possibly_lhs_deref (gimple stmt)            
{                                               
   tree lhsop = gimple_assign_lhs (stmt);      
   tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

   return ((TREE_CODE (lhsop) == MEM_REF) ||    
   		(TREE_CODE (lhsop) == COMPONENT_REF));
} 

bool is_deref_stmt(gimple stmt)
{
	set< unsigned int > cons_list;
	set< unsigned int >::iterator cit;

	cons_list = gimple_to_constraints[stmt];

	for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
	{
		constraint_t exp = VEC_index(constraint_t,aliases, *cit);

		if(exp->lhs.type > 1 || exp->rhs.type > 1)
			return true;
	}

	return false;
}

bool possibly_deref (gimple stmt)
{
   tree lhsop = gimple_assign_lhs (stmt);
   tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

   //return ((TREE_CODE (lhsop) == MEM_REF) ||
   //		(rhsop && TREE_CODE (rhsop) == MEM_REF));

   return ((TREE_CODE (lhsop) == MEM_REF) ||
   		(rhsop && TREE_CODE (rhsop) == MEM_REF) ||
   		(TREE_CODE (lhsop) == COMPONENT_REF) ||
   		(rhsop && TREE_CODE (rhsop) == COMPONENT_REF));

}


/* --------------------------------------------------------------------
   Perform necessary initializations for the callstrings pointsto pass.
   -------------------------------------------------------------------*/

/*--------------------------------------------------------------------
  Returns the called function's decl tree. If it is a direct function 
  call, the TREE_CODE of the returned decl will be FUNCTION_DECL. If 
  it is a call via function pointer, it will be VAR_DECL. 
  -------------------------------------------------------------------*/

void map_arguments_at_call (gimple stmt, tree decl, bool generate_liveness, basic_block bb, struct cgraph_node * cnode)
{

   VEC(ce_s, heap) *rhsc = NULL;
   size_t j;
   int argoffset = 1;
   csvarinfo_t fi;

   /* Generate liveness for call via function pointers and library routines. */
   if (generate_liveness) {

       struct constraint_expr *exp;
       unsigned i;

       for (j = 0; j < gimple_call_num_args (stmt); j++) {

           tree arg = gimple_call_arg (stmt, j);
		if(AGGREGATE_TYPE_P (TREE_TYPE (arg)))
//		       fprintf(dump_file,"\nArgument in library call\n");
           if (field_must_have_pointers (arg) && TREE_CODE (arg) != ADDR_EXPR) {
//	       fprintf(dump_file,"\nArgument is a pointer\n");
               VEC (ce_s, heap) *results = NULL;
               cs_get_constraint_for (arg, &results, bb, cnode);
               FOR_EACH_VEC_ELT (ce_s, results, i, exp)
	       {
//                   ((block_information *)(bb->aux))->add_to_parsed_data_indices (exp->var, false, bb);	// generate_liveness_constraints // Vini: Why commented out???
		     generate_liveness_constraint(cnode, bb,exp->var);  // To Be Checked
	       }
               VEC_free (ce_s, heap, results);
           }
       }
       return;
   }

   /* Map call arguments. */
   fi = cs_get_vi_for_tree (decl, bb, cnode);

   for (j = 0; j < gimple_call_num_args (stmt); j++) {

//       ((function_info *)(cnode->aux))->cons_num++;

       struct constraint_expr lhs ;
       struct constraint_expr *rhsp;
       tree arg = gimple_call_arg (stmt, j);
       if (field_must_have_pointers (arg)) {
           cs_get_constraint_for (arg, &rhsc, bb, cnode);
           lhs.type = SCALAR;
           lhs.var = cs_first_vi_for_offset (fi, argoffset)->id;
           lhs.offset = 0;
           while (VEC_length (ce_s, rhsc) != 0) {
               rhsp = VEC_last (ce_s, rhsc);
              cs_process_constraint (new_constraint (lhs, *rhsp), bb);
               VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
          multi_rhs = false;
       }
       argoffset++;
   }
   VEC_free (ce_s, heap, rhsc);

}

bool identifyExitFunction(gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
	tree decl = get_called_fn_decl (stmt);
	struct cgraph_node *callee = cgraph_get_node(decl);

//	fprintf(dump_file, "\nCallee %s\n", cgraph_node_name(callee));

	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (callee->decl)), "exit") == 0)
	{
//		fprintf(dump_file, "\nHulla Re\n");
		return true;
	}

	return false;
}

void process_library_call (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
   /* Generate liveness. */
   unsigned int before_aliases = VEC_length(constraint_t, aliases);
   map_arguments_at_call (stmt, NULL, true, bb, cnode); 
   unsigned int after_aliases = VEC_length(constraint_t, aliases);
   set< unsigned int > cons_list;
   for(unsigned int i = before_aliases; i < after_aliases; i++)
   	cons_list.insert(i);
   gimple_to_constraints[stmt] = cons_list;

   /* Handle malloc by introducing a points to to heap. */
   if (gimple_call_flags (stmt) & ECF_MALLOC) {
       tree lhs = gimple_call_lhs (stmt);
   	before_aliases = VEC_length(constraint_t, aliases);
       if (lhs && field_must_have_pointers (lhs))
	{	
           cs_make_constraint_from_heapvar (cs_get_vi_for_tree (lhs, bb, cnode), "heap", bb, cnode);
	    constraint_t con = VEC_pop(constraint_t,aliases);
	    con->heap_alloc = true;
            VEC_safe_push (constraint_t, heap, aliases, con);	
	}
	after_aliases = VEC_length(constraint_t, aliases);
   	for(unsigned int i = before_aliases; i < after_aliases; i++)
   		cons_list.insert(i);
	gimple_to_constraints[stmt] = cons_list;

   }
}

void generate_liveness_constraint(struct cgraph_node *cnode, basic_block bb, unsigned int id)
{
((block_information *)(bb->aux))->get_list().push(id,false);


//((function_info *)(cnode->aux))->push_front(bb,1);

}


void process_gimple_assign_stmt (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{

 tree lhsop = gimple_assign_lhs (stmt);
 tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

   if (rhsop && TREE_CLOBBER_P (rhsop))
	return;


   if (field_must_have_pointers (lhsop)) 
   {
       VEC(ce_s, heap) *lhsc = NULL;
       VEC(ce_s, heap) *rhsc = NULL;
       if (rhsop && AGGREGATE_TYPE_P (TREE_TYPE (lhsop)))  /* Look into : Structure variables */
       {
		cs_do_structure_copy (lhsop, rhsop, bb, cnode); 
       }
       else 
       {
           cs_get_constraint_for (lhsop, &lhsc, bb, cnode);
           if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
	   {
//		fprintf(dump_file,"\nPTR Arith1\n");
                cs_get_constraint_for_ptr_offset (gimple_assign_rhs1 (stmt),
                                           gimple_assign_rhs2 (stmt), &rhsc, bb, cnode);
	   }
           //else if (code == BIT_AND_EXPR
           //        && TREE_CODE (gimple_assign_rhs2 (t)) == INTEGER_CST)
           //{
              // Aligning a pointer via a BIT_AND_EXPR is offsetting
              //   the pointer.  Handle it by offsetting it by UNKNOWN.
           //   get_constraint_for_ptr_offset (gimple_assign_rhs1 (t), NULL_TREE, &rhsc);
           //}
           else if ((CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt))
                     && !(POINTER_TYPE_P (gimple_expr_type (stmt))
                     && !POINTER_TYPE_P (TREE_TYPE (rhsop))))
                     || gimple_assign_single_p (stmt))
	   {

                // cs_get_constraint_for (rhsop, &rhsc, bb, cnode);	// by Prashant
                cs_get_constraint_for_rhs (rhsop, &rhsc, bb, cnode);   // To Be Checked
//                cs_get_constraint_for (rhsop, &rhsc, bb, cnode);
	   }
	  // cs_process_all_all_constraints calls
	  // cs_process_constraint calls
	  // insert_alias_in_pool. This function stores constraints in a global
	  // variable: aliases (of type constraint_t).

          cs_process_all_all_constraints (lhsc, rhsc, bb);
       }

       // Commented by Prashant
       // If there is a store to a global variable the rhs escapes.
       // ...

       VEC_free (ce_s, heap, rhsc);
       VEC_free (ce_s, heap, lhsc);

//	print_assignment_data ();
   }

//   else
//   {
       // Generate liveness of lhs
       if (lhsop && TREE_CODE (lhsop) == MEM_REF && (!(is_pointer (rhsop))))
       {
            // generate_liveness_constraint
		generate_liveness_constraint (cnode, bb, (cs_get_vi_for_tree (cs_get_var (lhsop), bb, cnode))->id);
       }

	#if 0       
       // Generate liveness of rhs
       if (rhsop && TREE_CODE (rhsop) == MEM_REF)
       {
            // generate_liveness_constraint
		generate_liveness_constraint (bb, (cs_get_vi_for_tree (cs_get_var (rhsop), bb, cnode))->id);
       }
	#endif
//   }
}

set< constraint_t, cons_cmp > my_cs_do_structure_copy (tree lhsop, tree rhsop, basic_block bb, struct cgraph_node * cnode)  /* Look into : Structure variables */
{
	set< constraint_t, cons_cmp > result;

   struct constraint_expr *lhsp, *rhsp;
   VEC (ce_s, heap) *lhsc = NULL, *rhsc = NULL;
   unsigned j;

   cs_get_constraint_for (lhsop, &lhsc, bb, cnode);
   cs_get_constraint_for_rhs (rhsop, &rhsc, bb, cnode);

   lhsp = VEC_index (ce_s, lhsc, 0);
   rhsp = VEC_index (ce_s, rhsc, 0);


   // Commented by Vini, used by Prashant
//    if (lhsp->type == DEREF)
//       return;
//    if (rhsp->type == DEREF) {
//        gcc_assert (VEC_length (ce_s, rhsc) == 1);
//        rhsp->var = undef_id;
//        rhsp->offset = 0;
//        rhsp->type = ADDRESSOF;
//        cs_process_all_all_constraints (lhsc, rhsc, bb);
//    }

   // Added by Vini
   if (lhsp->type == DEREF || rhsp->type == DEREF)
   {
     if (lhsp->type == DEREF)
       {
         gcc_assert (VEC_length (ce_s, lhsc) == 1);
         lhsp->offset = UNKNOWN_OFFSET;
       }
     if (rhsp->type == DEREF)
       {
         gcc_assert (VEC_length (ce_s, rhsc) == 1);
         rhsp->offset = UNKNOWN_OFFSET;
       }

	struct constraint_expr *rhsp, *lhsp;
	int i,j;

	FOR_EACH_VEC_ELT (ce_s, lhsc, i, lhsp)
		FOR_EACH_VEC_ELT (ce_s, rhsc, j, rhsp)
		{
			result.insert(new_constraint (*lhsp, *rhsp));
		}	

//     cs_process_all_all_constraints (lhsc, rhsc, bb);
   }

   else if (lhsp->type == SCALAR &&
            (rhsp->type == SCALAR || rhsp->type == ADDRESSOF)) {
       HOST_WIDE_INT lhssize, lhsmaxsize, lhsoffset;
       HOST_WIDE_INT rhssize, rhsmaxsize, rhsoffset;
       unsigned k = 0;
       get_ref_base_and_extent (lhsop, &lhsoffset, &lhssize, &lhsmaxsize);
       get_ref_base_and_extent (rhsop, &rhsoffset, &rhssize, &rhsmaxsize);
       for (j = 0; VEC_iterate (ce_s, lhsc, j, lhsp);) {
           csvarinfo_t lhsv, rhsv;
           rhsp = VEC_index (ce_s, rhsc, k);
           lhsv = cs_get_varinfo (lhsp->var);
           rhsv = cs_get_varinfo (rhsp->var);
          if (lhsv->may_have_pointers
               && (lhsv->is_full_var
                  || rhsv->is_full_var
                  || ranges_overlap_p (lhsv->offset + rhsoffset, lhsv->size,
                                       rhsv->offset + lhsoffset, rhsv->size)))
	   {
		result.insert(new_constraint (*lhsp, *rhsp));
//               cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
	   }
           if (!rhsv->is_full_var && (lhsv->is_full_var
                  || (lhsv->offset + rhsoffset + lhsv->size
                      > rhsv->offset + lhsoffset + rhsv->size))) {
               ++k;
               if (k >= VEC_length (ce_s, rhsc))
                   break;
           }
           else
	   {
               ++j;
           }
       }
   }
   else
   {
       gcc_unreachable ();
   }


   VEC_free (ce_s, heap, lhsc);
   VEC_free (ce_s, heap, rhsc);

	return result;
}


set< constraint_t, cons_cmp > get_constraint_expr (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
	set< constraint_t, cons_cmp > result;
	int j, i;

	tree lhsop = gimple_assign_lhs (stmt);
	tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

	if (rhsop && TREE_CLOBBER_P (rhsop))
		return result;


   if (field_must_have_pointers (lhsop)) 
   {
       VEC(ce_s, heap) *lhsc = NULL;
       VEC(ce_s, heap) *rhsc = NULL;
       if (rhsop && AGGREGATE_TYPE_P (TREE_TYPE (lhsop)))  /* Look into : Structure variables */
       {
		return my_cs_do_structure_copy (lhsop, rhsop, bb, cnode); 
       }
       else 
       {
           cs_get_constraint_for (lhsop, &lhsc, bb, cnode);
           if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
	   {
//		fprintf(dump_file,"\nPTR Arith1\n");
                cs_get_constraint_for_ptr_offset (gimple_assign_rhs1 (stmt),
                                           gimple_assign_rhs2 (stmt), &rhsc, bb, cnode);
	   }
           //else if (code == BIT_AND_EXPR
           //        && TREE_CODE (gimple_assign_rhs2 (t)) == INTEGER_CST)
           //{
              // Aligning a pointer via a BIT_AND_EXPR is offsetting
              //   the pointer.  Handle it by offsetting it by UNKNOWN.
           //   get_constraint_for_ptr_offset (gimple_assign_rhs1 (t), NULL_TREE, &rhsc);
           //}
           else if ((CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt))
                     && !(POINTER_TYPE_P (gimple_expr_type (stmt))
                     && !POINTER_TYPE_P (TREE_TYPE (rhsop))))
                     || gimple_assign_single_p (stmt))
	   {

                // cs_get_constraint_for (rhsop, &rhsc, bb, cnode);	// by Prashant
                cs_get_constraint_for_rhs (rhsop, &rhsc, bb, cnode);   // To Be Checked
//                cs_get_constraint_for (rhsop, &rhsc, bb, cnode);
	   }
	  // cs_process_all_all_constraints calls
	  // cs_process_constraint calls
	  // insert_alias_in_pool. This function stores constraints in a global
	  // variable: aliases (of type constraint_t).

	struct constraint_expr *rhsp, *lhsp;

	FOR_EACH_VEC_ELT (ce_s, lhsc, i, lhsp)
		FOR_EACH_VEC_ELT (ce_s, rhsc, j, rhsp)
		{
			result.insert(new_constraint (*lhsp, *rhsp));
		}	
		
//          cs_process_all_all_constraints (lhsc, rhsc, bb);
       }

       VEC_free (ce_s, heap, rhsc);
       VEC_free (ce_s, heap, lhsc);
   }

	return result;
}

void append_to_bb_constraints (unsigned int id,bool b, basic_block bb)
{
((block_information *)(bb->aux))->get_list().push(id,b);
}

/*-------------------------------------------------------------------------
  Insert the constraint t in the alias pool. Update the alias list for the
  current basic block. Also, update the bb_alias_list of variable vi (forming 
  the LHS of the constraint) to reflect the fact that variable vi is the
  lhs of some constraint t.
  ------------------------------------------------------------------------*/
void insert_alias_in_pool (constraint_t t, csvarinfo_t vi, basic_block bb)
{

    // df_list new_alias;					// Vini: Why commented out? Liveness set
     unsigned int loc;
     bool alias_found = false;// check_alias_inclusion (t, vi, &loc);	// Vini: Why commented out?
     if (!alias_found) {
         loc = VEC_length (constraint_t, aliases);
         VEC_safe_push (constraint_t, heap, aliases, t);
         //append_constraint_to_varinfo (vi, loc);		// Vini: Why commented out? Adds to liveness set
     }
     //new_alias = create_df_constraint (loc);			// Vini: Why commented out? Adds to liveness set
     // if (!compute_alias_and_pinfo)
     {
//        ((block_information *)(bb->aux))->add_to_parsed_data_indices (loc, true, bb);	// Add to constraints (or parsed data) of the block
//	  generate_liveness_constraint(bb, loc);
	if(switch_pass)
	{
		  struct cgraph_node *node = ((block_information *)(bb->aux))->get_cfun();
//		fprintf(dump_file,"\nProblem Here1\n");
		 if(global_cnode != NULL && global_cnode->uid == node->uid)
		{
			append_to_bb_constraints (loc, true, main_firstbb);
		}
		else
		{	
		  append_to_bb_constraints (loc, true, bb);
		}
	}
     }
     //else							// Vini: Why commented out?
//     {
         //append_to_fptr_constraints (new_alias);		// Vini: Why commented out?
//     }
}

/*
void init_bb_aux(basic_block bb)
{
	
struct cgraph_node *cnode;

for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {

        if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
          continue;
        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

        FOR_EACH_BB(bb)
                {
                bb->aux = new block_information(cnode);
                }
        pop_cfun();
        }

}

void end_bb_aux(basic_block bb)
{

struct cgraph_node *cnode;

for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {

if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
        continue;
        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

        FOR_EACH_BB (bb) {
                if (bb->aux)
                        {
                        delete (block_information *)bb->aux;
                        bb->aux = NULL;
                        }
                }

        pop_cfun();
        }
}
*/

void process_gimple_condition(gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
 struct constraint_expr *exp;
   unsigned i;

   tree op0 = gimple_cond_lhs (stmt);
   tree op1 = gimple_cond_rhs (stmt);

   if (field_must_have_pointers (op0) && TREE_CODE (op0) != ADDR_EXPR) {
       VEC (ce_s, heap) *results = NULL;
       cs_get_constraint_for (op0, &results, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, results, i, exp)
		generate_liveness_constraint (cnode, bb, exp->var);
       VEC_free (ce_s, heap, results);
   }
   if (field_must_have_pointers (op1) && TREE_CODE (op1) != ADDR_EXPR) {
       VEC (ce_s, heap) *results = NULL;
       cs_get_constraint_for (op1, &results, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, results, i, exp)
		generate_liveness_constraint (cnode, bb, exp->var);
       VEC_free (ce_s, heap, results);
   }

}

void
process_gimple_phi_stmt (gimple stmt, basic_block bb, struct cgraph_node *cnode)
{
   VEC(ce_s, heap) *lhsc = NULL;
   VEC(ce_s, heap) *rhsc = NULL;
   struct constraint_expr *c;
   constraint_t con;	
   size_t i;
   unsigned int j;

   unsigned int before_aliases = VEC_length(constraint_t, aliases);

   /* For a phi node, assign all the arguments to the result. */
   cs_get_constraint_for (gimple_phi_result (stmt), &lhsc, bb, cnode);
   for (i = 0; i < gimple_phi_num_args (stmt); i++) {
       tree strippedrhs = PHI_ARG_DEF (stmt, i);
       STRIP_NOPS (strippedrhs);
       cs_get_constraint_for (strippedrhs, &rhsc, bb, cnode);
       for (j = 0; VEC_iterate (ce_s, lhsc, j, c); j++) {
           struct constraint_expr *c2;
           while (VEC_length (ce_s, rhsc) > 0) {
               c2 = VEC_last (ce_s, rhsc);
	       con = new_constraint (*c, *c2);
	       con->phi_stmt = true;		
               cs_process_constraint (con, bb);
		VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
       }
   }
   multi_rhs = false;
   VEC_free (ce_s, heap, rhsc);
   VEC_free (ce_s, heap, lhsc);

	
   unsigned int after_aliases = VEC_length(constraint_t, aliases);
   set< unsigned int > cons_list;
   for(unsigned int i = before_aliases; i < after_aliases; i++)
   	cons_list.insert(i);
   gimple_to_constraints[stmt] = cons_list;

}


void process_gimple_phi_stmt1 (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
   VEC(ce_s, heap) *lhsc = NULL;
   VEC(ce_s, heap) *rhsc = NULL;
   struct constraint_expr *c, *c1;
   size_t i;
   unsigned int j;
//        print_gimple_stmt(dump_file,stmt,0,0);

   /* For a phi node, assign all the arguments to the result. */
//	fprintf(dump_file,"\nProblem is here\n");
//	print_generic_expr(dump_file,gimple_phi_result (stmt),0);
   cs_get_constraint_for (gimple_phi_result (stmt), &lhsc, bb, cnode);
   for (i = 0; i < gimple_phi_num_args (stmt); i++) {
       tree strippedrhs = PHI_ARG_DEF (stmt, i);
       STRIP_NOPS (strippedrhs);
       cs_get_constraint_for (strippedrhs, &rhsc, bb, cnode);
	bool is_reqd = false;

	for (j = 0; VEC_iterate (ce_s, lhsc, j, c); j++)
	{
		struct constraint_expr *c2;

		while (VEC_length (ce_s, rhsc) > 0)
		{
			c2 = VEC_last (ce_s, rhsc);
	
			constraint_t con = new_constraint (*c, *c2);

			tree lhs = VEC_index(csvarinfo_t, csvarmap, con->lhs.var)->decl;
			tree rhs = VEC_index(csvarinfo_t, csvarmap, con->rhs.var)->decl;

//			fprintf(dump_file,"\nHEre\n");
//			fprintf(dump_file,"\nCnode %s\n",cgraph_node_name(cnode));

			VEC_pop (ce_s, rhsc);
		}
	}

//	fprintf(dump_file,"\nBahar\n");
//	print_set_ssa_rep(lhs_resol);
//	print_set_ssa_rep(rhs_resol);

	}

//   multi_rhs = false;
   VEC_free (ce_s, heap, rhsc);
   VEC_free (ce_s, heap, lhsc);
}

bool is_gimple_endblock (gimple t)
{
   return (gimple_code (t) == GIMPLE_RETURN);
}


/* Iterate over all the PHI nodes of the basic block and 
   calculate alias info for them. */

bool process_phi_pointers (basic_block bb, struct cgraph_node * cnode)
{
   gimple_stmt_iterator gsi;

   bool has_phi = false;
   for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi)) {
//       print_gimple_stmt (dump_file, gsi_stmt(gsi), 0,0);
       gimple phi = gsi_stmt (gsi);
       tree phi_result = gimple_phi_result (phi);
       if (is_gimple_reg (phi_result)) {
           if (field_must_have_pointers (phi_result)) {
               has_phi = true;
               process_gimple_phi_stmt (phi, bb, cnode);
           }
       }
   }

   return has_phi;
}

void generate_retval_liveness (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
   tree retval = gimple_return_retval (stmt);
//	retval = SSAVAR(retval);

   if (retval!=NULL_TREE && field_must_have_pointers (retval)) {
       VEC(ce_s, heap) *rhsc = NULL;
       struct constraint_expr *rhs;
       unsigned int i;

       cs_get_constraint_for (retval, &rhsc, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, rhsc, i, rhs)
	{
//		generate_liveness_constraint (bb, rhs->var);


//		((function_info *)(cnode->aux))->add_ele_param_ret(rhs->var); 	
//		fprintf(dump_file,"\nReturn Type\n");
//		set< unsigned int > temp = ((function_info *)(cnode->aux))->get_ret_id();
//		temp.insert(rhs->var);
//		((function_info *)(cnode->aux))->set_ret_id(temp);
//		((function_info *)(cnode->aux))->set_ret_type();
	}
   }
}

gimple_stmt_iterator split_bb_at_stmt (basic_block & bb, gimple stmt, struct cgraph_node *cnode)
{
//	if (!gsi_end_p (gsi_start_bb (bb)))
//		print_gimple_stmt (dump_file, gsi_stmt (gsi_start_bb (bb)), 0, 0);
	#if 0
	edge e = split_block (bb, stmt);
	bb = e->dest;
	if (!gsi_end_p (gsi_start_bb (bb)))
//		print_gimple_stmt (dump_file, gsi_stmt (gsi_start_bb (bb)), 0, 0);
		initialize_block_aux (bb, cnode);
	#endif
	return gsi_start_bb (bb);
}

void initialize_block_aux (basic_block block, struct cgraph_node *cnode)
{
	// block->aux = (block_information *) ggc_alloc_cleared_atomic (sizeof (block_information));
	block->aux = new block_information(cnode);
//	block->aux = NULL;
}

void delete_block_aux()
{
        struct cgraph_node * cnode;
	basic_block endbb;

        for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
        {
                if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
	                continue;
                push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));


		#if 1
		endbb = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (cnode->decl));

		if (endbb->aux)
		{
			delete (block_information *)endbb->aux;
			endbb->aux = NULL;
		}
		#endif

                basic_block bb;
                FOR_EACH_BB (bb) {
                        if (bb->aux)
                        {
//#if GC
//				fprintf (dump_file, "\nGC block %d %s %d", bb->index, cgraph_node_name(cnode), cnode->uid);
                                delete (block_information *)bb->aux;
                                bb->aux = NULL;
                        }
                }
                pop_cfun();
        }
}

bool is_function_worklist_empty()
{
	for(int i = 1; i < func_count; i++)
	{
		if(function_worklist[i])
		{
			return false;
		}
	}

	return true;
}

bool is_function_worklist_d_empty()
{
	struct cgraph_node *cnode;

	for(int i = 1; i < func_count_d; i++)
	{
		if(function_worklist_d[i])
		{
                        cnode = func_numbering[index_func_array_d[i]];

			return false;
		}
	}

	return true;
}

void depth_ordering(struct cgraph_node *cnode)
{
	struct cgraph_edge *edge;

	struct cgraph_node *node;

//	fprintf(dump_file,"\nFunction calling depth_ordering %s\n",cgraph_node_name(cnode));

	#if 0
	if(((function_info *)(cnode->aux))->ordered)
	{
		return;

	}
	#endif	

	((function_info *)(cnode->aux))->ordered = true;

	for(edge = cnode->callees; edge; edge = edge->next_callee)
	{
		node = edge->callee;

//		fprintf(dump_file,"\nhiiiiiiii\n");
//		fprintf(dump_file,"\nCallee %s\n",cgraph_node_name(node));

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;
	
		if(!((function_info *)(node->aux))->ordered)
		{
			depth_ordering(node);
		}	
	}

//	fprintf(dump_file,"\nDepth Order %d set for Function %s\n",func_count, cgraph_node_name(cnode));

//	index_func_array[func_count] = cnode;
//	func_index_array[cnode->uid] = func_count;
//	function_worklist[func_count++] = true;

}

void create_depth_ordering()
{
	struct cgraph_node *cnode;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
       
        	if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
	          continue;
	
//		fprintf(dump_file, "\nFunction %s Order %d\n", cgraph_node_name(cnode), cnode->order);

	        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

		depth_ordering(cnode);

	}

}

set< unsigned int > nodes_visited_callees;
unsigned int call_depth, call_temp;

void get_trans_callees(struct cgraph_node *cnode)
{
	struct cgraph_node *node;
	struct cgraph_edge *edge;

	nodes_visited_callees.insert(((function_info *)(cnode->aux))->func_num);

	for(edge = cnode->callees; edge; edge = edge->next_callee)
	{
		node = edge->callee;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

		((function_info *)(cnode->aux))->trans_callees.insert(((function_info *)(node->aux))->func_num);

		if(nodes_visited_callees.find(((function_info *)(node->aux))->func_num) == nodes_visited_callees.end())
		{
			call_temp++;
			get_trans_callees(node);
		}
//		else
		{
//			call_temp = INFINITY;
		}

		((function_info *)(cnode->aux))->trans_callees.insert(((function_info *)(node->aux))->trans_callees.begin(), ((function_info *)(node->aux))->trans_callees.end());

		if(call_depth < call_temp)
		{
			call_depth = call_temp;
		}

		call_temp = 0;
	}
	
}

void get_callees()
{
	int i = 1;

	struct cgraph_node *cnode;

	for(i; i < func_count; i++)
	{
		call_depth = 0;
		call_temp = 0;

		cnode = func_numbering[index_func_array[i]];
		nodes_visited_callees.clear();

		get_trans_callees(cnode);

		((function_info *)(cnode->aux))->max_depth = call_depth;
	}
}

// Update Call Graph with function pointer information

void update_call_graph(struct cgraph_node *caller, struct cgraph_node *callee, basic_block bb)
{
	process_call_pt_indirect(caller, bb, callee);

	set< unsigned int > temp;

	unsigned int caller_num, callee_num;

	caller_num = ((function_info *)(caller->aux))->func_num;
	callee_num = ((function_info *)(callee->aux))->func_num;

	temp = callers[callee_num];

	temp.insert(caller_num);

	callers[callee_num] = temp;	

	temp = callees[caller_num];

	temp.insert(callee_num);

	callees[caller_num] = temp;
}

void print_call_graph()
{
	func_map::iterator it;
	struct cgraph_node *cnode1, *cnode2;
	set_func callee_set, caller_set;
	set_func::iterator sit;

	fprintf(dump_file,"\nPrinting New Call Graph\n");

	fprintf(dump_file,"\nPrinting Callees\n");

	for(it = callees.begin(); it != callees.end(); it++)
	{
		cnode1 = func_numbering[it->first];
		callee_set = it->second;

		fprintf(dump_file,"\nNew:Function %s (%d) Callees", cgraph_node_name(cnode1), it->first);

		for(sit = callee_set.begin(); sit != callee_set.end(); sit++)
		{
			cnode2 = func_numbering[*sit];

			if (!gimple_has_body_p (cnode2->decl) || cnode2->clone_of)
				continue; 

			fprintf(dump_file,"\t%s (%d)", cgraph_node_name(cnode2), *sit);
		}
		fprintf(dump_file,"\n\n");
	}	

	fprintf(dump_file,"\nPrinting Callers\n");

	for(it = callers.begin(); it != callers.end(); it++)
	{
		cnode1 = func_numbering[it->first];
		caller_set = it->second;

		fprintf(dump_file,"\nNew:Function %s (%d) Callers", cgraph_node_name(cnode1), it->first);

		for(sit = caller_set.begin(); sit != caller_set.end(); sit++)
		{
			cnode2 = func_numbering[*sit];

			if (!gimple_has_body_p (cnode2->decl) || cnode2->clone_of)
				continue; 

			fprintf(dump_file,"\t%s (%d)", cgraph_node_name(cnode2), *sit);
		}
		fprintf(dump_file,"\n\n");
	}	
}

void print_scc_call_graph()
{
	func_map::iterator it;
	struct cgraph_node *cnode1, *cnode2;
	set_func callee_set, caller_set;
	set_func::iterator sit;

	fprintf(dump_file,"\nPrinting SCC Call Graph\n");

	fprintf(dump_file,"\nPrinting Callees\n");

	for(it = scc_callees.begin(); it != scc_callees.end(); it++)
	{
		fprintf(dump_file, "\nFCount %d, entry %d\n", FCount, it->first);

		if(it->first <= FCount)
		{
			cnode1 = func_numbering[it->first];

			fprintf(dump_file,"\nNew:Function %s (%d) Callees", cgraph_node_name(cnode1), it->first);
		}
		else 
		{
			fprintf(dump_file,"\nNew:SCC (%d) Callees", it->first);
		}

		callee_set = it->second;

		for(sit = callee_set.begin(); sit != callee_set.end(); sit++)
		{
			if(*sit <= FCount)
			{
				cnode2 = func_numbering[*sit];

				if (!gimple_has_body_p (cnode2->decl) || cnode2->clone_of)
					continue; 

				fprintf(dump_file,"\t%s (%d)", cgraph_node_name(cnode2), *sit);
			}
			else
			{
				fprintf(dump_file,"\t (%d)", *sit);
			}
		}
		fprintf(dump_file,"\n\n");
	}	

	fprintf(dump_file,"\nPrinting Callers\n");

	for(it = scc_callers.begin(); it != scc_callers.end(); it++)
	{
		if(it->first <= FCount)
		{
			cnode1 = func_numbering[it->first];

			fprintf(dump_file,"\nNew:Function %s (%d) Callers", cgraph_node_name(cnode1), it->first);
		}
		else
		{
			fprintf(dump_file,"\nNew:SCC (%d) Callers", it->first);
		}

		caller_set = it->second;

		for(sit = caller_set.begin(); sit != caller_set.end(); sit++)
		{
			if(*sit <= FCount)
			{
				cnode2 = func_numbering[*sit];

				if (!gimple_has_body_p (cnode2->decl) || cnode2->clone_of)
					continue; 

				fprintf(dump_file,"\t%s (%d)", cgraph_node_name(cnode2), *sit);
			}
			else
			{
				fprintf(dump_file,"\t (%d)", *sit);
			}
		}

		fprintf(dump_file,"\n\n");
	}	
}

void print_original_call_graph()
{
	func_map::iterator it;
	struct cgraph_node *cnode1, *cnode2;
	struct cgraph_edge *edge;

	fprintf(dump_file,"\nPrinting Original Call Graph\n");

	for(it = callees.begin(); it != callees.end(); it++)
	{
		cnode1 = func_numbering[it->first];
//		callee_set = it->second;

		fprintf(dump_file,"\nOriginal:Function %s Callees", cgraph_node_name(cnode1));

		for(edge = cnode1->callees; edge; edge = edge->next_callee)
		{
			cnode2 = edge->callee;

			if (!gimple_has_body_p (cnode2->decl) || cnode2->clone_of)
				continue; 

			fprintf(dump_file,"\t%s", cgraph_node_name(cnode2));
		}

		fprintf(dump_file,"\n\n");
	}
}

void create_call_graph()
{
	struct cgraph_node *cnode, *callee, *caller;
	struct cgraph_edge *edge;

	for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{
		set_func temp1, temp2;

		/* Nodes without a body, and clone nodes are not interesting. */ 
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of) 
			continue; 

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

//		fprintf(dump_file,"\nCnode in question %s\n", cgraph_node_name(cnode));

		for(edge = cnode->callees; edge; edge = edge->next_callee)
		{
			callee = edge->callee;

			if (!gimple_has_body_p (callee->decl) || callee->clone_of)
				continue; 

			temp1.insert(((function_info *)(callee->aux))->func_num);

		}

		callees[((function_info *)(cnode->aux))->func_num] = temp1;

		for(edge = cnode->callers; edge; edge = edge->next_caller)
		{
			caller = edge->caller;

			if (!gimple_has_body_p (caller->decl) || caller->clone_of)
				continue; 

			temp2.insert(((function_info *)(caller->aux))->func_num);
		}

		callers[((function_info *)(cnode->aux))->func_num] = temp2;

		((function_info *)(cnode->aux))->set_pred_count(temp2.size());

//		((function_info *)(cnode->aux))->set_num_bb(total_bbs);

		((function_info *)(cnode->aux))->set_num_bb(total_bbs+1);
//		((function_info *)(cnode->aux))->num_trans_bbs = total_bbs+1;

//		initialize_worklist(cnode, total_bbs);

		pop_cfun();

	}

//	fprintf(dump_file,"\nHyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy\n");
//	print_call_graph();
//	print_original_call_graph();
}

void init_worklist()
{
	struct cgraph_node *cnode, *callee, *caller;
	struct cgraph_edge *edge;

	for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{
		set_func temp1, temp2;

		/* Nodes without a body, and clone nodes are not interesting. */ 
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of) 
			continue; 

//		fprintf(dump_file,"\nCnode in question %s\n", cgraph_node_name(cnode));

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

//		((function_info *)(cnode->aux))->set_num_bb(total_bbs);
		((function_info *)(cnode->aux))->set_num_bb(total_bbs+1);
		((function_info *)(cnode->aux))->num_trans_bbs = total_bbs+1;

//		unsigned int x = total_bbs;
		unsigned int x = total_bbs+1;

//		fprintf(dump_file,"\nKay Challu AheABC\n");

		initialize_worklist(cnode, x);

		pop_cfun();

	}
}
	
bool identifyExitFunctionCnode(struct cgraph_node *cnode)
{
	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "exit") == 0)
	{
//		fprintf(dump_file, "\nHulla Re\n");
		return true;
	}

	return false;
}

void initialization (void) 
{ 
	struct cgraph_node * cnode = NULL; 

	bool is_first_cnode = true;

	unsigned int function_found = 0;

	// init_alias_heapvars (); 
	cs_init_alias_vars (cnode); 
	int start_node = 1;

	for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{ 
		struct cgraph_node *alias; 
		csvarinfo_t vi; 
 
		/* Nodes without a body, and clone nodes are not interesting. */ 
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of) 
			continue; 

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

//		fprintf(dump_file,"\nFunction %s\n", cgraph_node_name(cnode));

		/* locating main function. */ 
//		if (strcmp (cgraph_node_name (cnode), "int main()") == 0)
		if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "main") == 0)
		{
			main_cnode = cnode; 
			main_firstbb = start_bb_of_fn (cnode);
		}
		else if (is_first_cnode && !main_cnode)
		{
			global_cnode = cnode;
		}

		is_first_cnode = false;
 
		// Creates csvarinfo_t for this function and its parameters and local variables 
		vi = cs_create_func_info_for (cnode->decl, cgraph_node_name (cnode), cnode); 
 
		/* CHANGE due gcc-4.7.2 */ 
		cgraph_for_node_and_aliases (cnode, associate_varinfo_to_alias, vi, true); 

		((function_info *)(cnode->aux))->func_num = func_num;

//		fprintf(dump_file,"\nInitialize %s %d\n", cgraph_node_name(cnode), func_num);

		func_numbering[func_num] = cnode;
		func_num++;
		FCount++;

		pop_cfun();
	}

	create_call_graph();

//	fprintf(dump_file, "\nPrinting Call Graph...\n");
//	print_call_graph();

 	index_func_array = XNEWVEC (unsigned int, func_num);
 	index_func_array_d = XNEWVEC (unsigned int, func_num);

 	func_index_array = XNEWVEC (unsigned int, func_num);
 	func_index_array_d = XNEWVEC (unsigned int, func_num);

 	function_worklist = XNEWVEC (bool, func_num);
 	function_worklist_d = XNEWVEC (bool, func_num);
 	preprocess_worklist = XNEWVEC (bool, func_num);
}

gimple_stmt_iterator split_block_at_stmt (gimple statement, basic_block block, struct cgraph_node *cnode)
{
	edge e = split_block (block, statement);
	block = e->dest;

	// Initialize the newly created basic block
	initialize_block_aux (block, cnode);

	return gsi_start_bb (block);
}

void print_variable_data ()
{
	for (int index = 0; index < VEC_length (csvarinfo_t, csvarmap); index++)
	{
	        csvarinfo_t variable = VEC_index (csvarinfo_t, csvarmap, index);
	}
}

void print_assignment_data ()
{
	for (int index = 0; index < VEC_length (constraint_t, aliases); index++)
	{
	        constraint_t assignment = VEC_index (constraint_t, aliases, index);
        	constraint_expr lhs = assignment->lhs;
	        constraint_expr rhs = assignment->rhs;
        	csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, csvarmap, lhs.var);
	        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, csvarmap, rhs.var);
	}
}

void print_variable_data (int index)
{
        csvarinfo_t variable = VEC_index (csvarinfo_t, csvarmap, index);

	csvarinfo_t vi;
//	for (vi = variable; vi; vi = vi->next)
}

void print_assignment_data (int index)
{
        constraint_t assignment = VEC_index (constraint_t, aliases, index);
        constraint_expr lhs = assignment->lhs;
        constraint_expr rhs = assignment->rhs;
        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, csvarmap, lhs.var);
        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, csvarmap, rhs.var);
}

void print_parsed_data (basic_block current_block)
{


}

void print_parsed_data ()
{

   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
//			print_parsed_data (current_block);
		}

		pop_cfun();
	}
}


void init_fn_aux()
{
	struct cgraph_node *cnode;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next)
	{
		basic_block current_block;

		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

		cnode->aux = new function_info();

		pop_cfun();
	}
}

void refresh_fn_aux(struct cgraph_node *cnode)
{
	#if 0
	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	set< unsigned int > pars = ((function_info *)(cnode->aux))->get_params();
	
	#ifndef MRB
	unsigned int ret_id;
	#endif
	#ifdef MRB
	set< unsigned int > ret_id;
	#endif		

	ret_id = ((function_info *)(cnode->aux))->get_ret_id();
	unsigned int multi_return = ((function_info *)(cnode->aux))->get_multi_return();
	bool has_ret = ((function_info *)(cnode->aux))->has_ret_type();

	unsigned int pred_count = ((function_info *)(cnode->aux))->get_pred_count();
	unsigned int num_bb = ((function_info *)(cnode->aux))->get_num_bb();

	unsigned int end_block_index = ((function_info *)(cnode->aux))->get_end_block_index();

	int reach = ((function_info *)(cnode->aux))->get_reach();

	unsigned int inter_order = ((function_info *)(cnode->aux))->get_inter_order();

	bool marked = ((function_info *)(cnode->aux))->is_marked();

	unsigned int order = ((function_info *)(cnode->aux))->get_order();

	set< unsigned int > trans_callees = ((function_info *)(cnode->aux))->trans_calles;

	set_call_pts call_pts = ((function_info *)(cnode->aux))->call_pts;

	unsigned int max_depth = ((function_info *)(cnode->aux))->max_depth;

	unsigned int ret_bb = ((function_info *)(cnode->aux))->ret_bb;

	unsigned int end_block_id = 

        if(cnode->aux)
	{
              	delete (function_info *)cnode->aux;
	
		cnode->aux = NULL;

		cnode->aux = new function_info();
	}
	#endif

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	if(cnode->aux)
	{
		processed_functions.erase(((function_info *)(cnode->aux))->func_num);	

		((function_info *)(cnode->aux))->count = 0;

	}

	pop_cfun();
}

void end_fn_aux()
{
	struct cgraph_node *cnode;
	
//	fprintf(dump_file,"\nInside end_fn_aux\n");

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next)
	{

		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
		        continue;

//		fprintf(dump_file,"\nInside end_fn_aux %s\n", cgraph_node_name(cnode));
//		fflush(dump_file);

	        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));


        	if(cnode->aux)
                {
//			fprintf(dump_file,"\nDeleting fn_aux %s\n", cgraph_node_name(cnode));
//			fflush(dump_file);

                	delete (function_info *)cnode->aux;

//			fprintf(dump_file,"\nDeleted fn_aux %s\n", cgraph_node_name(cnode));
//			fflush(dump_file);
	                cnode->aux = NULL;
                }

        	pop_cfun();
        }

	#if 0
	free(index_func_array);
	free(index_func_array_d);

	free(func_index_array);
	free(func_index_array_d);

	free(function_worklist);
	free(function_worklist_d);
	free(preprocess_worklist);
	#endif
}


void print_original_cfg ()
{
//	FUNCTION_NAME ();

   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		int n = 1;
		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			gimple_stmt_iterator gsi;
			for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi))
			{
				print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);
			}
		}

		pop_cfun();
	}
}

/* ----------------------------------------------------------------
   Restoring the cfg by clearing the aux field of each basic block
   and removing unnecessary (split) blocks.
   ---------------------------------------------------------------*/
void restore_control_flow_graph ()
{
//	FUNCTION_NAME ();

   struct cgraph_node * cnode;
   for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
   {
       if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
           continue;

       push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));
       // current_function_decl = cnode->decl;
       // set_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

       /* Free cgraph node's aux field. */
       if (cnode->aux) {
           ggc_free (cnode->aux);
           cnode->aux = NULL;
       }
       /* Free each bb's aux field. */
       basic_block cbb;
       FOR_EACH_BB (cbb) {
           if (cbb->aux) {
               ggc_free (cbb->aux);
               cbb->aux = NULL;
           }
       }
       /* Merge bb's if necessary. */
       cleanup_tree_cfg ();
       /* Free the dominator info. */
       free_dominance_info (CDI_DOMINATORS);
       free_dominance_info (CDI_POST_DOMINATORS);
   
       pop_cfun ();
   }
}

bool check_if_var_temp(unsigned int var)
{
	if(var <= 3)
	{
		return false;
	}

	tree decl = VEC_index(csvarinfo_t, csvarmap, var)->decl;

	if(!decl)
	{
		return false;
	}

	if(DECL_ARTIFICIAL(decl))
	{
		return true;
	}
	else
	{
		return false;
	}
}

void initialize_points_worklist(struct cgraph_node *new_node)
{
	int i;
	int num_bb = ((function_info *)(new_node->aux))->get_num_bb();

	for(i = 0; i < num_bb-1; i++)
	{
//		fprintf(dump_file,"\nHerew IN\n");
		((function_info *)(new_node->aux))->points_worklist[i] = true;
//		fprintf(dump_file,"\nHerew OUT\n");
	}

	((function_info *)(new_node->aux))->points_worklist[i] = true;
//	fprintf(dump_file,"\nHerew\n");
}

void initialize_worklist(struct cgraph_node *cnode, int num_bb)
{
	int i;
//	int num_bb = total_bbs;
	basic_block bt;

	int *rp, *pp;

	// Dynamic Allocation

	rp = XNEWVEC (int, num_bb);
//	rp = XNEWVEC (int, total_bbs+1);
//	fprintf(dump_file,"\nTotal Number of BBs n Function %s is %d\n", cgraph_node_name(cnode), num_bb);

	pre_and_rev_post_order_compute (NULL, rp, false);
	pp = XNEWVEC (int, num_bb);
//	pp = XNEWVEC (int, total_bbs+1);
	post_order_compute (pp, false, true);

	#if 0
	((function_info *)(cnode->aux))->rev_post_order = XNEWVEC (int, total_bbs+2);
	((function_info *)(cnode->aux))->post_order = XNEWVEC (int, total_bbs+2);
	((function_info *)(cnode->aux))->bb_rp_order = XNEWVEC (int, total_bbs+2);
	((function_info *)(cnode->aux))->bb_p_order = XNEWVEC (int, total_bbs+2);
	((function_info *)(cnode->aux))->live_worklist = XNEWVEC (bool, total_bbs+2);
	((function_info *)(cnode->aux))->points_worklist = XNEWVEC (bool, total_bbs+2);
	#endif

//	for(i = 0; i < num_bb; i++)
	for(i = 0; i < num_bb-1; i++)
	{
//		fprintf(dump_file,"\nHeyyy\n");
		((function_info *)(cnode->aux))->rev_post_order[i] = rp[i];

		bt = BASIC_BLOCK(((function_info *)(cnode->aux))->rev_post_order[i]);
//		fprintf(dump_file,"\nbt->index %d Order %d\n",bt->index, i);

		((function_info *)(cnode->aux))->bb_rp_order[bt->index] = i;

//		((function_info *)(cnode->aux))->live_worklist[i] = false;
		((function_info *)(cnode->aux))->points_worklist[i] = true;
	}

	// For LAST BB with Index 1

//	fprintf(dump_file,"\nAssigning BB 1 with Order %d\n", i);
	#if 1
	((function_info *)(cnode->aux))->rev_post_order[i] = 1; // rp[i];
	((function_info *)(cnode->aux))->bb_rp_order[1] = i;
	((function_info *)(cnode->aux))->points_worklist[i] = true;
	#endif

//	fprintf(dump_file,"\nPost Order\n");

	#if 0
//	for(i = 0; i < num_bb; i++)
	for(i = 0; i < num_bb-1; i++)
	{
		((function_info *)(cnode->aux))->post_order[i] = pp[i];

		bt = BASIC_BLOCK(((function_info *)(cnode->aux))->post_order[i]);

//		fprintf(dump_file,"\nbt->index %d\n",bt->index);

		((function_info *)(cnode->aux))->bb_p_order[bt->index] = i;

		((function_info *)(cnode->aux))->live_worklist[i] = true;
//		((function_info *)(cnode->aux))->points_worklist[i] = false;
	}	

	// For LAST BB with Index 1

	#if 1
	((function_info *)(cnode->aux))->post_order[i] = 1; // pp[i];
	((function_info *)(cnode->aux))->bb_p_order[1] = i;
	((function_info *)(cnode->aux))->live_worklist[i] = true;
	#endif

	((function_info *)(cnode->aux))->live_worklist[0] = true;
	((function_info *)(cnode->aux))->points_worklist[0] = true;
	#endif

	free (rp);	
	free (pp);	

//	fprintf(dump_file,"\nEnd of initialize_worklist\n");
}

void get_pred_count(struct cgraph_node *cnode)
{
	struct cgraph_edge *edge;
	unsigned int x = 0;

	for(edge = cnode->callers; edge; edge = edge->next_caller)
	{
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		++x;
	}

	((function_info *)(cnode->aux))->set_pred_count(x);
}

void get_total_cnodes(struct cgraph_node *cnode)
{
	struct cgraph_edge *edge;
	struct cgraph_node *node;

//	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "encode_one_frame") == 0)
//		print = true;	

	for(edge = cnode->callees; edge; edge = edge->next_callee)
	{
		node = edge->callee;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

//		if(print)
//		fprintf(f, "\"%s\" -> \"%s\";\n", cgraph_node_name(cnode), cgraph_node_name(node));

//		((function_info *)(cnode->aux))->callee_count++; // = ((function_info *)(node->aux))->callee_count;

		if(set_cnodes_call_graph.find(node) == set_cnodes_call_graph.end())
		{
			set_cnodes_call_graph.insert(node);

			get_total_cnodes(node);
		}


//		((function_info *)(cnode->aux))->callee_count += ((function_info *)(node->aux))->callee_count;
	}

}

bool call_indirectly(struct cgraph_node *cnode) // Returns true if this function is called indirectly
{
	struct cgraph_edge *edge;

	struct cgraph_node *node;

	int x = 0, y = 0;

	for(edge= cnode->callers; edge; edge = edge->next_caller)
	{
		node = edge->caller;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

		x++;
	}

	for(edge= cnode->callees; edge; edge = edge->next_callee)
	{
		node = edge->callee;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

		y++;
	}

	if(x > 0 || y > 0)
	{
		return false;
	}
	else
	{
		return true;
	}
	
}

void process_call_pt_indirect(struct cgraph_node *caller, basic_block bb, struct cgraph_node *callee)
{
	callpt_type temp;
        set< callpt_type > callpts;

	temp = std::tr1::make_tuple(((function_info *)(caller->aux))->func_num, bb->index);

	callpts = ((function_info *)(callee->aux))->call_pts;
        callpts.insert(temp);
        ((function_info *)(callee->aux))->call_pts = callpts;
}

void process_call_pt(struct cgraph_node *cnode, basic_block bb, gimple stmt)
{
	struct cgraph_node *node;
	callpt_type temp;
	set< callpt_type > callpts;

	tree decl = get_called_fn_decl (stmt);

	temp = make_tuple(((function_info *)(cnode->aux))->func_num, bb->index);

	if (TREE_CODE (decl) == FUNCTION_DECL)
	{
		node = cgraph_get_node(decl);

		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
                          return;

		callpts = ((function_info *)(node->aux))->call_pts;
		callpts.insert(temp);
		((function_info *)(node->aux))->call_pts = callpts;
	}
	else //Indirect Call Should Add for function Pointers
	{
		#if 0 //def FP
		tree decl2 = SSA_NAME_VAR(decl);
		fp_call_type fp_temp = make_tuple(((function_info *)(cnode->aux))->func_num, bb->index, DECL_UID(decl2));
		set< unsigned int > callee_list = fp_call_details[fp_temp];

		for(set< unsigned int >::iterator it = callee_list.begin(); it != callee_list.end(); it++)
		{
			node = func_numbering[*it];

			callpts = ((function_info *)(node->aux))->call_pts;
			callpts.insert(temp);
			((function_info *)(node->aux))->call_pts = callpts;
		}	
		#endif
	
		return;
	}	
}

void preprocess_cnode(struct cgraph_node *cnode)
{
	unsigned int start_cons = VEC_length(constraint_t, aliases);

	basic_block current_block;

	basic_block endblock = NULL;

	bool is_start_block = true;

//	fprintf(dump_file,"\nPreprocess Cnode %s\n", cgraph_node_name(cnode));

//	((function_info *)(cnode->aux))->set_num_bb(total_bbs);
	((function_info *)(cnode->aux))->set_num_bb(total_bbs+1);
	((function_info *)(cnode->aux))->num_trans_bbs = total_bbs+1;

	#if 1
	if(switch_pass)
//		initialize_worklist(cnode, total_bbs);
		initialize_worklist(cnode, total_bbs+1);
	#endif

	basic_block bs, bt;

	edge e;
	edge_iterator ei;
	basic_block bq;

	FOR_EACH_BB (current_block) 
	{
		num_bb_count++;

		unsigned int stmt_count = 0;

		gimple_stmt_iterator gsi, origgsi;
		bool has_phi = false;

		has_phi = process_phi_pointers(current_block, cnode);

		FOR_EACH_EDGE(e,ei,current_block->succs)
       		{
               		bq = e->dest;

			if(bq->index == 0)
			{
				continue;
			}

			((function_info *)(cnode->aux))->cf_edges++;
			((function_info *)(cnode->aux))->trans_cf_edges++;
		}

		compute_pred_rel(current_block, cnode);
		compute_succ_rel(current_block, cnode);

		set< unsigned int > t_b_set = ((block_information *)(current_block->aux))->pred_with_back_edge_rel;

		for(set< unsigned int >::iterator sit = t_b_set.begin(); sit != t_b_set.end(); sit++)
		{
			bs = BASIC_BLOCK(*sit);

//			((function_info *)(cnode->aux))->back_edges.insert(make_tuple(bs->index, current_block->index));

//			fprintf(dump_file,"\nBack Edge from %d to %d\n", bs->index, current_block->index);
		}

//		fprintf(dump_file,"\nPreprocess BB Index %d\n", current_block->index);

		// Iterate over the statements of current_block.
		for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi)) 
		{
			gimple stmt = gsi_stmt (gsi);
//			print_gimple_stmt (dump_file, stmt, 0, 0);

			if (is_gimple_call (stmt) || is_gimple_endblock (stmt)) 
			{
				tree decl = NULL;

				// Need not break in case of library routines.
				if (is_gimple_call (stmt)) 
				{
					decl = get_called_fn_decl (stmt);

					#if 0
					tree lhs_ret = gimple_call_lhs (stmt);
					if(lhs_ret)
	       					cs_create_variable_info_for (lhs_ret, alias_get_name (lhs_ret), current_block, cnode);
					#endif

					if (TREE_CODE (decl) == FUNCTION_DECL) 
					{
						if (!DECL_STRUCT_FUNCTION (decl))// && !identifyExitFunction(stmt, current_block, cnode)) 
						{
							process_library_call (stmt, current_block, cnode);

							#if 0
							if(identifyExitFunction(stmt, current_block, cnode))
								generate_liveness_constraint(current_block, -1);
							#endif
							// A library call is not marked as a call_block
							continue;
						}
					}
				}
				if (is_gimple_call (stmt)) 
				{
					call_site_count++;

					bool fptr_call = (TREE_CODE (decl) != FUNCTION_DECL);

					if(switch_pass)
						process_call_pt(cnode, current_block, stmt);

					// Mark the calling function pointer as live.
					if (fptr_call && switch_pass) 
					{
	 					unsigned int var = cs_get_vi_for_tree (decl, current_block, cnode)->id;
//						generate_liveness_constraint(current_block, var);
					}

					// Mapping of Parameter-Argument for Direct Calls
					if (!fptr_call && switch_pass) 
					{
						// Discover the static call argument mapping.
						unsigned int before_aliases = VEC_length(constraint_t, aliases);
						map_arguments_at_call (stmt, decl, fptr_call, current_block, cnode); 
						unsigned int after_aliases = VEC_length(constraint_t, aliases);
						set< unsigned int > cons_list;
						for(unsigned int i = before_aliases; i < after_aliases; i++)
							cons_list.insert(i);
						gimple_to_constraints[stmt] = cons_list;

						#if 0 // For adding return block after call block
						decl = get_called_fn_decl (stmt);

						if(TREE_CODE(decl) == FUNCTION_DECL)
						{
							struct cgraph_node *callee = cgraph_get_node(decl);

							origgsi = gsi;
							gsi = split_bb_at_stmt (current_block, gsi_stmt (gsi), cnode);
	
//							((block_information *)(current_block->aux))->return_block = true;		
//							map_return_value (cnode, current_block, end_bb_of_fn(callee)->prev_bb, callee);
						}
						#endif
					}

					// Mark call current_block with its properties.
//					((block_information *)(current_block->aux))->call_block = true; 
				}
				if(is_gimple_endblock (stmt))
				{
					tree retval = NULL;
					retval = gimple_return_retval (stmt);
					generate_retval_liveness(stmt, current_block, cnode);

					#if 0
					if(retval)
					{
					print_gimple_stmt (dump_file, stmt, 0, 0);
					fprintf(dump_file, "\nRetval %d, %s, %s\n", current_block->index, cgraph_node_name(cnode), alias_get_name(retval));
					}
					#endif

					unsigned int temp_g = ((function_info*)(cnode->aux))->get_multi_return();

					((function_info*)(cnode->aux))->set_multi_return(++temp_g);

					if (retval && field_must_have_pointers (retval) && TREE_CODE (retval) == INTEGER_CST)
					{
//						fprintf(dump_file, "\nHiyyyyya\n");
//						fprintf(dump_file, "\n%d\n", nothing_id);

						#ifdef MRB
						set< unsigned int > ret_temp = ((function_info *)(cnode->aux))->get_ret_id();
						ret_temp.insert(nothing_id);	
						((function_info *)(cnode->aux))->set_ret_id(ret_temp);
						#endif

						#ifndef MRB
						((function_info *)(cnode->aux))->set_ret_id(nothing_id);
						#endif

						((function_info *)(cnode->aux))->set_ret_type();
					}	
					else if (retval != NULL && field_must_have_pointers (retval)) 
					{
//						fprintf(dump_file, "\n!Hiyyyyya\n");

						retval = SSAVAR(retval);
						csvarinfo_t ret_vi = cs_get_vi_for_tree(retval, current_block, cnode);

//						fprintf(dump_file,"\nSetting Return Var %s-%d\n", get_var_name(ret_vi->id), ret_vi->id);

						if(ret_vi != NULL)
						{
//							fprintf(dump_file, "\nFound ret_vi %d %s\n", ret_vi->id, alias_get_name(ret_vi->decl));
						
							#ifdef MRB
							set< unsigned int > ret_temp = ((function_info *)(cnode->aux))->get_ret_id();
							ret_temp.insert(ret_vi->id);	
							((function_info *)(cnode->aux))->set_ret_id(ret_temp);
							#endif

							#ifndef MRB
							((function_info *)(cnode->aux))->set_ret_id(ret_vi->id);
							#endif

							((function_info *)(cnode->aux))->set_ret_type();				
						}
						#if 0	
						else
						{
							fprintf(dump_file, "\n!Found ret_vi\n");
						
						}
						#endif	
					}
				}
			}

			// Inspect other statements for possible pointers.
			else if (is_gimple_assign (stmt)) 
			{
				check_deref = true; 

				stmt_count++;

//				fprintf(dump_file,"\nprocess_gimple_assign\n");
				unsigned int before_aliases = VEC_length(constraint_t, aliases);
				process_gimple_assign_stmt (stmt, current_block, cnode);
				unsigned int after_aliases = VEC_length(constraint_t, aliases);
				set< unsigned int > cons_list;
				for(unsigned int i = before_aliases; i < after_aliases; i++)
					cons_list.insert(i);
				gimple_to_constraints[stmt] = cons_list;
				check_deref = false;

				if(possibly_lhs_deref (stmt))          
				{
					tree lhsop = gimple_assign_lhs (stmt);
		
					csvarinfo_t vi_lhs = cs_lookup_vi_for_tree(lhsop);

					if(vi_lhs)
					{
//						((function_info *)(cnode->aux))->lhs_deref_set.insert(vi_lhs->id);
					}
				}
			}
			else if (gimple_code (stmt) == GIMPLE_COND) 
			{
//				process_gimple_condition (stmt, current_block, cnode); 
			}

		}

		#if 0
		fprintf(dump_file,"\nPred Rel of BB %d: ", current_block->index);
		print_set_integers(((block_information *)(current_block->aux))->pred_rel);

		fprintf(dump_file,"\n\nPred with Back Edge Rel of BB %d: ", current_block->index);
		print_set_integers(((block_information *)(current_block->aux))->pred_with_back_edge_rel);

		fprintf(dump_file,"\nSucc Rel of BB %d: ", current_block->index);
		print_set_integers(((block_information *)(current_block->aux))->succ_rel);

		fprintf(dump_file,"\n\nSucc with Back Edge Rel of BB %d: ", current_block->index);
		print_set_integers(((block_information *)(current_block->aux))->succ_with_back_edge_rel);
		#endif

		((function_info *)(cnode->aux))->cf_edges+=(stmt_count-1);
		((function_info *)(cnode->aux))->trans_cf_edges+=(stmt_count-1);
	}

	current_block = end_bb_of_fn(cnode);

	compute_pred_rel(current_block, cnode);
	compute_succ_rel(current_block, cnode);

	compute_reachability_from_exit_node(cnode);

	set< unsigned int > t_b_set = ((block_information *)(current_block->aux))->pred_with_back_edge_rel;

	for(set< unsigned int >::iterator sit = t_b_set.begin(); sit != t_b_set.end(); sit++)
	{
		bs = BASIC_BLOCK(*sit);

		((function_info *)(cnode->aux))->back_edges.insert(make_tuple(bs->index, current_block->index));
	}

	#if 1
	perform_reachability_analysis(cnode);
	compute_in_loop(cnode);
	compute_pred_in_loop(cnode);
	#endif

	((function_info *)(cnode->aux))->num_bbs = total_bbs+1;
	((function_info *)(cnode->aux))->num_trans_bbs = total_bbs+1;

	unsigned int end_cons = VEC_length(constraint_t, aliases);

	((function_info *)(cnode->aux))->num_constraints = end_cons - start_cons;

	#if 0 //DATA_MEASURE
	fprintf(dump_file,"\nCnode Constraints %s %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->num_constraints);
	#endif
}

void preprocess_cnode_x(struct cgraph_node *cnode)
{
	unsigned int start_cons = VEC_length(constraint_t, aliases);

	basic_block current_block;

	basic_block endblock = NULL;

	bool is_start_block = true;

//	fprintf(dump_file,"\nPreprocess Cnode %s\n", cgraph_node_name(cnode));

//	((function_info *)(cnode->aux))->set_num_bb(total_bbs);
	((function_info *)(cnode->aux))->set_num_bb(total_bbs+1);
	((function_info *)(cnode->aux))->num_trans_bbs = total_bbs+1;

	if(switch_pass)
//		initialize_worklist(cnode, total_bbs);
		initialize_worklist(cnode, total_bbs+1);

	basic_block bs, bt;

	FOR_EACH_BB (current_block) 
	{
		num_bb_count++;

		gimple_stmt_iterator gsi, origgsi;
		bool has_phi = false;

//		has_phi = process_phi_pointers(current_block, cnode);

		compute_pred_rel(current_block, cnode);
		compute_succ_rel(current_block, cnode);

		set< unsigned int > t_b_set = ((block_information *)(current_block->aux))->pred_with_back_edge_rel;

		for(set< unsigned int >::iterator sit = t_b_set.begin(); sit != t_b_set.end(); sit++)
		{
			bs = BASIC_BLOCK(*sit);

			((function_info *)(cnode->aux))->back_edges.insert(make_tuple(bs->index, current_block->index));

//			fprintf(dump_file,"\nBack Edge from %d to %d\n", bs->index, current_block->index);
		}

//		fprintf(dump_file,"\nPreprocess BB Index %d\n", current_block->index);

		// Iterate over the statements of current_block.
		for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi)) 
		{
			gimple stmt = gsi_stmt (gsi);
//			print_gimple_stmt (dump_file, stmt, 0, 0);

			if (is_gimple_call (stmt) || is_gimple_endblock (stmt)) 
			{
				tree decl = NULL;

				// Need not break in case of library routines.
				if (is_gimple_call (stmt)) 
				{
					decl = get_called_fn_decl (stmt);
					if (TREE_CODE (decl) == FUNCTION_DECL) 
					{
						if (!DECL_STRUCT_FUNCTION (decl)) 
						{
							process_library_call (stmt, current_block, cnode);
							// A library call is not marked as a call_block
							continue;
						}
					}
				}
				if (is_gimple_call (stmt)) 
				{
					call_site_count++;

					bool fptr_call = (TREE_CODE (decl) != FUNCTION_DECL);

					if(switch_pass)
						process_call_pt(cnode, current_block, stmt);

					#if 0	
					// Mark the calling function pointer as live.
					if (fptr_call && switch_pass) 
					{
	 					unsigned int var = cs_get_vi_for_tree (decl, current_block, cnode)->id;
						generate_liveness_constraint(current_block, var);
					}
					#endif

					// Mapping of Parameter-Argument for Direct Calls
					if (!fptr_call && switch_pass) 
					{
						// Discover the static call argument mapping.
						unsigned int before_aliases = VEC_length(constraint_t, aliases);
						map_arguments_at_call (stmt, decl, fptr_call, current_block, cnode); 
						unsigned int after_aliases = VEC_length(constraint_t, aliases);
						set< unsigned int > cons_list;
						for(unsigned int i = before_aliases; i < after_aliases; i++)
						cons_list.insert(i);
						gimple_to_constraints[stmt] = cons_list;

						#if 0
						decl = get_called_fn_decl (stmt);

						if(TREE_CODE(decl) == FUNCTION_DECL)
						{
							struct cgraph_node *callee = cgraph_get_node(decl);

							origgsi = gsi;
//							gsi = split_bb_at_stmt (current_block, gsi_stmt (gsi), cnode);
	
//							((block_information *)(current_block->aux))->return_block = true;		
//							map_return_value (cnode, current_block, end_bb_of_fn(callee)->prev_bb, callee);
						}
						#endif
					}

					// Mark call current_block with its properties.
					((block_information *)(current_block->aux))->call_block = true; 
				}
				if(is_gimple_endblock (stmt))
				{
					tree retval = gimple_return_retval (stmt);

					unsigned int temp_g = ((function_info*)(cnode->aux))->get_multi_return();

					((function_info*)(cnode->aux))->set_multi_return(++temp_g);

					if (retval != NULL_TREE && field_must_have_pointers (retval)) 
					{
						retval = SSAVAR(retval);
						csvarinfo_t ret_vi = cs_get_vi_for_tree(retval, current_block, cnode);

//						fprintf(dump_file,"\nSetting Return Var %s-%d\n", get_var_name(ret_vi->id), ret_vi->id);

						if(ret_vi != NULL)
						{
							#ifdef MRB
							set< unsigned int > ret_temp = ((function_info *)(cnode->aux))->get_ret_id();
							ret_temp.insert(ret_vi->id);	
							((function_info *)(cnode->aux))->set_ret_id(ret_temp);
							#endif

							#ifndef MRB
							((function_info *)(cnode->aux))->set_ret_id(ret_vi->id);
							#endif

							((function_info *)(cnode->aux))->set_ret_type();				
						}
					}
				}
			}

			// Inspect other statements for possible pointers.
			else if (is_gimple_assign (stmt)) 
			{
				check_deref = true; 

//				fprintf(dump_file,"\nprocess_gimple_assign\n");
				unsigned int before_aliases = VEC_length(constraint_t, aliases);
				process_gimple_assign_stmt (stmt, current_block, cnode);
				unsigned int after_aliases = VEC_length(constraint_t, aliases);
				set< unsigned int > cons_list;
				for(unsigned int i = before_aliases; i < after_aliases; i++)
					cons_list.insert(i);
				gimple_to_constraints[stmt] = cons_list;
				check_deref = false;

				if(possibly_lhs_deref (stmt))          
				{
					tree lhsop = gimple_assign_lhs (stmt);
		
					csvarinfo_t vi_lhs = cs_lookup_vi_for_tree(lhsop);

					if(vi_lhs)
					{
//						((function_info *)(cnode->aux))->lhs_deref_set.insert(vi_lhs->id);
					}
				}
			}
			else if (gimple_code (stmt) == GIMPLE_COND) 
			{
//				process_gimple_condition (stmt, current_block, cnode); 
			}

		}


		#if 0
		fprintf(dump_file,"\nPred Rel of BB %d: ", current_block->index);
		print_set_integers(((block_information *)(current_block->aux))->pred_rel);

		fprintf(dump_file,"\n\nPred with Back Edge Rel of BB %d: ", current_block->index);
		print_set_integers(((block_information *)(current_block->aux))->pred_with_back_edge_rel);

		fprintf(dump_file,"\nSucc Rel of BB %d: ", current_block->index);
		print_set_integers(((block_information *)(current_block->aux))->succ_rel);

		fprintf(dump_file,"\n\nSucc with Back Edge Rel of BB %d: ", current_block->index);
		print_set_integers(((block_information *)(current_block->aux))->succ_with_back_edge_rel);
		#endif
	}

	current_block = end_bb_of_fn(cnode);

	compute_pred_rel(current_block, cnode);
	compute_succ_rel(current_block, cnode);

	compute_reachability_from_exit_node(cnode);

	set< unsigned int > t_b_set = ((block_information *)(current_block->aux))->pred_with_back_edge_rel;

	for(set< unsigned int >::iterator sit = t_b_set.begin(); sit != t_b_set.end(); sit++)
	{
		bs = BASIC_BLOCK(*sit);

		((function_info *)(cnode->aux))->back_edges.insert(make_tuple(bs->index, current_block->index));
	}

	#if 1
	perform_reachability_analysis(cnode);
	compute_in_loop(cnode);
	compute_pred_in_loop(cnode);
	#endif

	unsigned int end_cons = VEC_length(constraint_t, aliases);

	((function_info *)(cnode->aux))->num_constraints = end_cons - start_cons;

	#if 0 //DATA_MEASURE
	fprintf(dump_file,"\nCnode Constraints %s %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->num_constraints);
	#endif
}

void preprocess_control_flow_graph()
{
	bool is_start_block;
	struct cgraph_node * cnode;
	basic_block endbb;

	num_procs = 0;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		num_procs++;

		preprocess_cnode(cnode);

		calculate_dominance_info(CDI_DOMINATORS);
		calculate_dominance_info(CDI_POST_DOMINATORS);

		pop_cfun();
	}

//	compute_pred_succ_rel();

//	fprintf(dump_file,"\nOut of Loop\n");

//	if(switch_pass)
		// Creating Node for undef
//		create_undef_node();

	create_scc_call_graph();

	DFS_COUNT = scc_callees.size();
	DFS(((function_info *)(main_cnode->aux))->func_num);
}

bool is_cdv(unsigned int id)
{
	if(CDV.find(id) != CDV.end())
		return true;
	else
		return false;
}

unsigned int context_dep(unsigned int id) // Given x, return x'
{
	if(CDV.find(id) != CDV.end())
		return id;
	else
		return (id+1);
}

unsigned int context_dep_rev(unsigned int id) // Given x', return x
{
	if(CDV.find(id) != CDV.end())
		return (id-1);
	else
		return id;
}

const char * copy_string(const char * var)
{
        char *temp = (char *)xmalloc(strlen(var)+1);
        strcpy(temp,var);
        const char * temp1 = (const char *)temp;

        return temp1;
}

const char * get_var_name(unsigned int vid)
{
	const char *nn = "i";
        const char *name,*fname;

	fname = copy_string(VEC_index(csvarinfo_t, csvarmap, vid)->name);

	if(CDV.find(vid) != CDV.end())
	{
        	name = copy_string(VEC_index(csvarinfo_t, csvarmap, vid)->name);
                string str = string(name) + string(nn);
                fname = copy_string(str.c_str());
	}

	return fname;
}

bool is_ssa_var(unsigned int var)
{
	if(var <= 4)
		return false;

	tree t = VEC_index(csvarinfo_t, csvarmap, var)->decl;

        if(TREE_CODE(t) == SSA_NAME)
                return true;

        return false;
}

bool is_ssa(tree t)
{
        if(TREE_CODE(t) == SSA_NAME)
                return true;

        return false;
}

void modify_cfg()
{
	tree retval, decl;
	gimple_stmt_iterator gsi, origgsi;
	gimple stmt;
	unsigned int index;	

	basic_block endblock = NULL, bb = NULL, exit_bb = NULL;

	bool is_start_block;
	struct cgraph_node *cnode;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		is_start_block = true;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		FOR_EACH_BB (bb) 
		{
			// Initialize auxillary info.
			if (!bb->aux)
			{
				initialize_block_aux (bb,cnode);
			}

			// Identification of start block, Sp 
			if (is_start_block) 
			{
//				fprintf(dump_file,"\nStartee %s %d\n", cgraph_node_name(cnode), bb->index);
				((block_information *)(bb->aux))->start_block = true;
				is_start_block = false;
			}

			// Iterate over the statements of current_block.
			for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi)) 
			{
				stmt = gsi_stmt (gsi);

//				print_gimple_stmt (dump_file, stmt, 0, 0);

				if (is_gimple_call (stmt)) // || is_gimple_endblock (stmt)) 
				{
					origgsi = gsi;
					decl = NULL;

					// Need not break in case of library routines.
					if (is_gimple_call (stmt)) 
					{
						decl = get_called_fn_decl (stmt);
						if (TREE_CODE (decl) == FUNCTION_DECL) 
						{
							
							if (!DECL_STRUCT_FUNCTION (decl))// && !identifyExitFunction(stmt, bb, cnode)) 
							{
								// A library call is not marked as a call_block
//								fprintf(dump_file,"\nProcess Library Call\n");
//								process_library_call (stmt, bb, cnode);
								continue;
							}
						}
					}

					origgsi = gsi;
        	                        gsi_prev (&gsi);
                	                if (!gsi_end_p (gsi))
                        	        {
 	                        	        edge e = split_block (bb,gsi_stmt (gsi));
                                        	bb = e->dest;

	                                        if(!bb->aux)
							initialize_block_aux (bb,cnode);	

                	                        gsi=gsi_start_bb(bb);
                        	         }
                                	 else
                                        	gsi = origgsi;

	                                 origgsi=gsi;
        	                         gsi_next(&gsi);
                	                 if(!gsi_end_p(gsi))
                        	         {
                	        	          gsi=origgsi;
                                        	  split_block (bb,gsi_stmt (gsi));
	                                          if(!bb->aux)
//      	                	                  bb->aux = new block_information(cnode);
							  initialize_block_aux (bb,cnode);
                        	         }
                                	 else
                                        	  gsi=origgsi;

					((block_information *)(bb->aux))->call_block = true; 

				}
				else if (is_gimple_endblock (stmt)) 
				{
					((block_information *)(bb->aux))->end_block = true;
					((function_info *)(cnode->aux))->end_block_id = bb->index;
					((function_info *)(cnode->aux))->set_end_block_index(bb->index);
					endblock = bb;
				}

			}
		}

		exit_bb = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (cnode->decl));
//		fprintf(dump_file,"\nCnode Exit Block %s %d\n", cgraph_node_name(cnode), exit_bb->index);

		if (!exit_bb->aux)
		{
			initialize_block_aux (exit_bb,cnode);
		}

		pop_cfun();
	}
}

void gather_global_variable_information (basic_block bb, struct cgraph_node *cnode)
{
        struct varpool_node *node;
//	fprintf(dump_file,"\nInside gather_global_var_information for function %s\n", cgraph_node_name(cnode));
//	 fflush(dump_file);

	tree decl_init = NULL, t;
	csvarinfo_t lvar, rvar;

//        fprintf(dump_file,"\nGlobal Variables\n");

        for (node = varpool_nodes; node; node = node->next)
        {
//		fflush(dump_file);
//		fprintf(dump_file,"\nGLOBAl\n");
                t = node->decl;

                if(field_must_have_pointers(t))
                {
//			
        	}
	}

//	fprintf(dump_file,"\nBasic Block %d of Function %s Local HRG\n", bb->index, cgraph_node_name(cnode));
//	g.print_dvg_local(bb);
	
}

unsigned int fp_count = 1;

bool is_function_pointer (tree t)
{
        /* Check if the variable is a function pointer */
	if (TREE_TYPE (t))
	{
		if (TREE_CODE (TREE_TYPE (t)) == POINTER_TYPE)
		{
			if (TREE_TYPE (TREE_TYPE (t)))
			{
				if (TREE_CODE (TREE_TYPE (TREE_TYPE (t))) == FUNCTION_TYPE || TREE_CODE (TREE_TYPE (TREE_TYPE (t))) == METHOD_TYPE)
				{
					Prototype obj = compute_Prototype (TREE_TYPE (t));

//					fprintf(dump_file, "\nFP for prototyping %s\n", alias_get_name(t));

					fp_details [DECL_UID (t)] = obj;

					return true;
				}
			}
		}
	}

        return false;
}

bool is_function_pointer_var (unsigned int var)
{
	tree t;

	csvarinfo_t vi = cs_lookup_vi_for_tree(t);

	if(vi)
	{
		t = vi->decl;

	        /* Check if the variable is a function pointer */
		if (TREE_TYPE (t))
		{
			if (TREE_CODE (TREE_TYPE (t)) == POINTER_TYPE)
			{
				if (TREE_TYPE (TREE_TYPE (t)))
				{
					if (TREE_CODE (TREE_TYPE (TREE_TYPE (t))) == FUNCTION_TYPE || TREE_CODE (TREE_TYPE (TREE_TYPE (t))) == METHOD_TYPE)
					{
//						Prototype obj = compute_Prototype (TREE_TYPE (t));

//						fp_details [DECL_UID (t)] = obj;

						return true;
					}
				}
			}
		}
	}

        return false;
}

bool is_pointer (tree t)
{
        /* Check if the variable is a function pointer */
	if (TREE_TYPE (t))
	{
		if (TREE_CODE (TREE_TYPE (t)) == POINTER_TYPE)
		{
			return true;
		}
	}

        return false;
}

bool is_pointer_to_aggregrate (tree t)
{
	if (TREE_TYPE (t))
	{
		if (TREE_CODE (TREE_TYPE (t)) == POINTER_TYPE)
		{
			if (TREE_TYPE (TREE_TYPE (t)))
			{
				if(AGGREGATE_TYPE_P (TREE_TYPE (TREE_TYPE(t))))
				{
					return true;
				}	
			}
		}
	}

	return false;
}

void gather_global_var_information ()
{
        struct varpool_node *node;

        for (node = varpool_nodes; node; node = node->next)
	{
		is_function_pointer (node->decl);
	}
}

void gather_local_var_information ()
{
	tree var;
	unsigned u;

	FOR_EACH_LOCAL_DECL (cfun, u, var)
	{
		is_function_pointer (var);
	}
}

void analyze_parm_decl_arguments ()
{
	tree args = DECL_ARGUMENTS (cfun->decl);

	while (args)
	{
		if (TREE_CODE (args) == PARM_DECL && !is_global_var (args))
		{
			is_function_pointer (args);
		}

		args = TREE_CHAIN (args);
	}
}

bool is_ret_id(tree t, struct cgraph_node *cnode, basic_block bb)
{
	bool has_ret = ((function_info *)(cnode->aux))->has_ret_type();
	#ifndef MRB
	unsigned int ret_id;
	#endif
	#ifdef MRB
	set< unsigned int > ret_id;
	#endif

	if(has_ret)
	{
		ret_id = ((function_info *)(cnode->aux))->get_ret_id();

		tree t1 = SSAVAR(t);

		if(t1)
		{
			csvarinfo_t y = cs_get_vi_for_tree(t1, bb, cnode);

			#ifndef MRB
			if(y->id == ret_id)
			#endif
			#ifdef MRB		
			if(ret_id.find(y->id) != ret_id.end())
			#endif
			{
				return true;
			}
		}

		return false;
	}
}

bool is_par_ret(tree t, struct cgraph_node *cnode, basic_block bb)
{
	set< unsigned int > params  = ((function_info *)(cnode->aux))->get_params();
	bool has_ret = ((function_info *)(cnode->aux))->has_ret_type();
	#ifndef MRB
	unsigned int ret_id;
	#endif
	#ifdef MRB
	set< unsigned int > ret_id;
	#endif

//	fprintf(dump_file,"\nFunction %s has Pointer Return Variable %d\n", cgraph_node_name(cnode), ret_id);
	if(has_ret)
	{
		ret_id = ((function_info *)(cnode->aux))->get_ret_id();
//		fprintf(dump_file,"\nFunction %s has Pointer Return Variable %s-%d\n", cgraph_node_name(cnode), get_var_name(ret_id), ret_id);
	}

	#if 0 
	fprintf(dump_file,"\nPrinting Parameters of Function %s\n", cgraph_node_name(cnode));

	for(set< unsigned int >::iterator sit = params.begin(); sit != params.end(); sit++)
	{
		fprintf(dump_file,"%s-%d\t", get_var_name(*sit), *sit);
	}

	fprintf(dump_file,"\n\n");
	#endif

//	tree t = VEC_index(csvarinfo_t,csvarmap,x)->decl;

	tree t1 = SSAVAR(t);

	if(t1)
	{
		csvarinfo_t y = cs_get_vi_for_tree(t1, bb, cnode);
		csvarinfo_t z = cs_get_vi_for_tree(t, bb, cnode);

//		fprintf(dump_file,"\nY->ID %s-%d Z->ID %s-%d\n", get_var_name(y->id), y->id, get_var_name(z->id), z->id);

		#ifndef MRB
		if(y->id == ret_id)
		#endif
		#ifdef MRB
		if(ret_id.find(y->id) != ret_id.end())
		#endif
		{
//			fprintf(dump_file,"\nReturn Var\n");
			return true;
		}
		else if(params.find(y->id) != params.end())
		{
			return true;
		}
	}

//	fprintf(dump_file,"\nHelllooyy\n");

	return false;
}

// Vini, June'15
void map_return_value (struct cgraph_node * src_function, 
	basic_block call_block,
	basic_block callee_end_block, 
	struct cgraph_node * called_function)
{
   bool found_rhs = true;
   /* Is there a receiving pointer value in the call statement? */
   gimple call_stmt = bb_call_stmt (call_block);
   if (is_gimple_call (call_stmt)) 
   {
      tree lhsop = gimple_call_lhs (call_stmt);
      if (lhsop && field_must_have_pointers (lhsop)) 
      {
         found_rhs = false;
         gimple_stmt_iterator ret_gsi;
         for (ret_gsi = gsi_start_bb (callee_end_block); !gsi_end_p (ret_gsi); gsi_next (&ret_gsi)) 
         {
            gimple ret_stmt = gsi_stmt (ret_gsi);
            if (gimple_code (ret_stmt) == GIMPLE_RETURN)
            {
               tree rhsop = gimple_return_retval (ret_stmt);
	       if (rhsop != NULL_TREE)
               {
                  /* Map it to the return value of return statement. */
                  VEC(ce_s, heap) *lhsc = NULL, *rhsc = NULL;
                  cs_get_constraint_for (lhsop, &lhsc, call_block, src_function);
                  cs_get_constraint_for (rhsop, &rhsc, callee_end_block, called_function);
                  cs_process_all_all_constraints (lhsc, rhsc, call_block);
                  VEC_free (ce_s, heap, lhsc);
                  VEC_free (ce_s, heap, rhsc);

		  found_rhs = true;
                  break;
               }
	    }
         }
      }
   }

//   if (!found_rhs)
//   {
//	print_gimple_stmt (dump_file, call_stmt, 0, 0);
	// This need not be an error since a function pointer might be wrongly pointing to a function
//	fprintf (dump_file, "\ncall-statement expects return, but return-block of function %s not found",
//		cgraph_node_name (called_function));
//   }
}

// Vini, June'15
void map_function_arguments (struct cgraph_node * src_function, 
	basic_block call_block, 
	gimple call_stmt, 
	struct cgraph_node * called_function)
{
   //fprintf (dump_file, "\nmap_function_arguments()");
   //fprintf (dump_file, "\nsrc_function=%s", cgraph_node_name (src_function));
   //fprintf (dump_file, "\ncalled_function=%s", cgraph_node_name (called_function));
   //fprintf (dump_file, "\n");
   //print_gimple_stmt (dump_file, call_stmt, 0, 0);

   VEC(ce_s, heap) *rhsc = NULL;
   size_t j;
   int argoffset = 1;
   csvarinfo_t fi;

   unsigned int num = 0;
   for (tree t = DECL_ARGUMENTS (called_function->decl); t; t = DECL_CHAIN (t))
        ++num;
   if (num != gimple_call_num_args (call_stmt))
   {
        VEC_free (ce_s, heap, rhsc);
	return;
   }

   fi = cs_get_vi_for_tree (called_function->decl, call_block, src_function);

   for (j = 0; j < gimple_call_num_args (call_stmt); j++) {
       //fprintf (dump_file, "\narg=%d", j);
       struct constraint_expr lhs ;
       struct constraint_expr *rhsp;
       tree arg = gimple_call_arg (call_stmt, j);
       if (field_must_have_pointers (arg)) {
           //fprintf (dump_file, "\narg has pointers");
           cs_get_constraint_for (arg, &rhsc, call_block, src_function);
	   //fprintf (dump_file, "\nFetched arg in rhsc");
           lhs.type = SCALAR;
           csvarinfo_t param = cs_first_vi_for_offset (fi, argoffset);
	   if (!param)
           {
                VEC_free (ce_s, heap, rhsc);
		return;
           }
           lhs.var = param->id;
           lhs.offset = 0;
	   //fprintf (dump_file, "\nmapped arguments:");
   	   //fprintf (dump_file, "\nlhs var %d, type %d", lhs.var, lhs.type);
           while (VEC_length (ce_s, rhsc) != 0) {
               rhsp = VEC_last (ce_s, rhsc);
	       //fprintf (dump_file, "\nrhs var %d, type %d", rhsp->var, rhsp->type);
               cs_process_constraint (new_constraint (lhs, *rhsp), call_block);
               //fprintf (dump_file, "\nlhs rhs constraint created");
               VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
          multi_rhs = false;
       }
       argoffset++;
   }
   VEC_free (ce_s, heap, rhsc);

   //fprintf (dump_file, "\nDone map_function_arguments");
}

void print_points_to_info (tree ptr, set<tree> *gcc_pta_data)
{

	int i;
	int num_valid_vars = 0;
//	for (i = 0; i < num_ssa_names; i++)
//	{
//		tree ptr = ssa_name (i);

//		print_generic_expr (dump_file, ptr, 0);

		if (ptr == NULL_TREE
				|| SSA_NAME_IN_FREE_LIST (ptr))
		{
			
//			continue;
			return;
		}

		struct ptr_info_def *pi = SSA_NAME_PTR_INFO (ptr);
		/* What follows is essentially a reimplementation of GGC's 
		 * dump_points_to_info_for () (from gcc/tree-ssa-alias.c), 
		 * modified to print names of global variables properly, 
		 * using information saved by LFCPA while worklist creation.
		 */
		if (pi)
		{
//			fprintf (dump_file, "\n\tin if 1");
			num_valid_vars++;
//					fprintf (dump_file, "\nFound call through fn ptr statement : ");
			struct pt_solution * pt = &(pi->pt);
//					fprintf (dump_file, "\nFound call through fn ptr statement : ");
			bitmap pointee = pt->vars;
//					fprintf (dump_file, "\nFound call through fn ptr statement : ");
			bitmap_iterator bi;
//					fprintf (dump_file, "\nFound call through fn ptr statement : ");
			unsigned int rhsbit;
//					fprintf (dump_file, "\nFound call through fn ptr statement : ");
			int j = 1;
//					fprintf (dump_file, "\nFound call through fn ptr statement : ");
			tree var = (SSA_NAME_VAR (ptr));
//					print_generic_expr(dump_file, var, 0);
//					fprintf (dump_file, "\nFound call through fn ptr statement : ");

			
			#ifdef pta_test
			if (pt->anything)
				fprintf (dump_file, ", points-to anything");

			if (pt->nonlocal)
				fprintf (dump_file, ", points-to non-local");

			if (pt->escaped)
				fprintf (dump_file, ", points-to escaped");

			if (pt->ipa_escaped)
				fprintf (dump_file, ", points-to unit escaped");

			if (pt->null)
				fprintf (dump_file, ", points-to NULL");
			#endif

			if (pt->vars /*&& !bitmap_empty_p (pt->vars)*/)
			{
//				fprintf (dump_file, "\n\tin if 2");
//				fprintf (dump_file, "\nBitmap lets proceed\n");
				
				int cnt = bitmap_count_bits (pointee);
//					fprintf (dump_file, "\nFound call through fn ptr statement : ");

				tree decl_name = DECL_NAME (var);
				if (decl_name)
				{
//						print_generic_expr(dump_file, decl_name, 0);
			
					#ifdef pta_test
					fprintf (dump_file, "%s", IDENTIFIER_POINTER (DECL_NAME (var)));
					#endif
				}
//				else
//					fprintf (dump_file, "\nno decl_name \n");

//					fprintf (dump_file, "\nFound call through fn ptr statement : ");


			if (pt->vars)
			{
//				fprintf (dump_file, "\n\tin if 3");
				#ifdef pta_test
				fprintf (dump_file, ", points-to vars: ");

				/* dump_decl_set (dump_file, pt->vars); */
				fprintf(dump_file,"{");
				/*Loop over all bits set in pointee, starting with 0 and setting
                                 *rhsbit to the bit number
                                 */
				#endif
				EXECUTE_IF_SET_IN_BITMAP (pointee, 0, rhsbit, bi)
				{
//					fprintf (dump_file, "\n\tin EXECUTE_IF_SET_IN_BITMAP");
					if (uid_to_tree[rhsbit])/* true in case of global variables */
					{
//						fprintf (dump_file, "\t for fn : %d", rhsbit);
						#ifdef pta_test
 						fprintf (dump_file, "\n:%s: ", IDENTIFIER_POINTER (DECL_NAME (uid_to_tree [rhsbit])));
						#endif
						gcc_pta_data->insert (uid_to_tree[rhsbit]);
//					else 
//						fprintf (dump_file, " D.%d", rhsbit);
						#ifdef pta_test
						if(j++ < cnt)
							fprintf (dump_file, ",");
						#endif
					}
				}

				#ifdef pta_test
				fprintf(dump_file," }");

				if (pt->vars_contains_global)
					fprintf (dump_file, " (includes global vars)");
				fprintf (dump_file, "\n");
				#endif
			}
			}
		} /* End reimplementation of dump_points_to_info_for () */
//	}
//	if (!num_valid_vars)
//		fprintf (dump_file, "No valid SSA_NAMEs found.\n");

	return;
}


set <int> cnode_gcc_pta, cnode_address_taken;

void compute_fns_gcc_pta (struct cgraph_node *caller, tree decl, basic_block bb)
{
	tree decl1 = SSA_NAME_VAR (decl);

//        fprintf (dump_file, "\nIn compute_indirect_edges_cg : ");
//      print_generic_expr (dump_file, decl1, 0);

        set <tree> callee_decl, new_callee_decl;

//        print_points_to_info (decl, &callee_decl);

        for (set <tree>:: iterator it = callee_decl.begin(); it != callee_decl.end(); ++it)
        {
                struct cgraph_node *callee;
                callee = cgraph_get_node (*it);

//		if (callee->address_taken == 1)
		{
			new_callee_decl.insert(*it);
		}
	}

//	fprintf(dump_file,"\nCaller %s Basic Block %d Callee Set Size %d\nCallees: ", cgraph_node_name(caller), bb->index, callee_decl.size());

        for (set <tree>:: iterator it = new_callee_decl.begin(); it != new_callee_decl.end(); ++it)
        {
                struct cgraph_node *callee;
                callee = cgraph_get_node (*it);

//		fprintf (dump_file, "\nFunction : %s/%d", cgraph_node_name (callee), callee->uid );
//		fprintf (dump_file, "%s\t", cgraph_node_name (callee));
		cnode_gcc_pta.insert (callee->uid);
        }
}

void compute_in_loop(struct cgraph_node *cnode)
{
	basic_block bb;

	set< unsigned int > in, out, temp1, temp2;

	FOR_EACH_BB (bb) 
	{
		in = ((block_information *)(bb->aux))->reach_in;
		out = ((block_information *)(bb->aux))->reach_out;

//		temp1 = ((block_information *)(bb->aux))->pred_with_back_edge_rel;

		if(in == out)
		{
			((block_information *)(bb->aux))->in_loop = true;

//			((block_information *)(bb->aux))->back_edge_sources.insert(temp1.begin(), temp1.end());
		}
	}
}

void compute_pred_in_loop(struct cgraph_node *cnode)
{
	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);
	basic_block bb, bt, bs;

	set< unsigned int > temp, temp1, in;

	FOR_EACH_BB (bb) 
	{
		if(!((block_information *)(bb->aux))->in_loop)
		{
//			fprintf(dump_file,"\nBB Not in Loop %d\n", bb->index);
			temp = ((block_information *)(bb->aux))->pred_rel;
//			temp1 = ((block_information *)(bb->aux))->pred_with_back_edge_rel;
//			temp.insert(temp1.begin(), temp1.end());
			
			for(set< unsigned int >::iterator it = temp.begin(); it != temp.end(); it++)
			{
				bt = BASIC_BLOCK_FOR_FUNCTION(fn, *it);	
			
				if(((block_information *)(bt->aux))->in_loop)
				{
//					fprintf(dump_file,"\nPred of BB in Loop %d\n", bt->index);

					((block_information *)(bb->aux))->pred_in_loop = true;

					for(set< unsigned int >::iterator sit = ((block_information *)(bt->aux))->back_edge_sources.begin(); sit != ((block_information *)(bt->aux))->back_edge_sources.end(); sit++)
					{	
						bs = BASIC_BLOCK_FOR_FUNCTION(fn, *sit);	

						in = ((block_information *)(bs->aux))->reach_in;

						if(in.find(bs->index) != in.end())
						{
//							fprintf(dump_file,"\nSrc of Back Edge in Loop %d\n", bs->index);

							((block_information *)(bs->aux))->frontiers.insert(bb->index);	
						}
					}
				}
			}
		}
	}
}

void compute_frontiers(struct cgraph_node *cnode)
{
	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);
	basic_block bb, bt;

	set< unsigned int > temp, temp1;

	FOR_EACH_BB (bb) 
	{
		temp = ((block_information *)(bb->aux))->succ_with_back_edge_rel;
			
		for(set< unsigned int >::iterator it = temp.begin(); it != temp.end(); it++)
		{
			bt = BASIC_BLOCK_FOR_FUNCTION(fn, *it);	
			
			if(((block_information *)(bt->aux))->in_loop)
			{
				((block_information *)(bb->aux))->pred_in_loop = true;
			}
		}
	}
}

void perform_reachability_analysis(struct cgraph_node *cnode)
{
	basic_block bb;
	basic_block start_bb = start_bb_of_fn(cnode);

	list< unsigned int > worklist;

	set< unsigned int > temp1, temp, temp2, temp3;

	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	worklist.push_back(start_bb->index);

	basic_block bt;

	while(!worklist.empty())
	{
		set< unsigned int > in, out_p, bes;

		bb = BASIC_BLOCK_FOR_FUNCTION(fn, worklist.front());

		worklist.pop_front();

//		fprintf(dump_file,"\nProcessing BB for Reachability Analysis is %d\n", bb->index);

		out_p = ((block_information *)(bb->aux))->reach_out;

//		fprintf(dump_file,"\nPrev Reach OUT\n");
//		print_set_integers(out_p);

		temp = ((block_information *)(bb->aux))->pred_rel;
		temp3 = ((block_information *)(bb->aux))->pred_with_back_edge_rel;
		temp.insert(temp3.begin(), temp3.end());

		for(set< unsigned int >::iterator it = temp.begin(); it != temp.end(); it++)
		{
			bt = BASIC_BLOCK_FOR_FUNCTION(fn, *it);

			temp1 = ((block_information *)(bt->aux))->reach_out;
			temp2 = ((block_information *)(bt->aux))->back_edge_sources;

			in.insert(temp1.begin(), temp1.end());

			bes.insert(temp2.begin(), temp2.end());	
		}

//		fprintf(dump_file,"\nBES UNION\n");
//		print_set_integers(bes);

		for(set< unsigned int >::iterator it = temp3.begin(); it != temp3.end(); it++)
		{
			bt = BASIC_BLOCK_FOR_FUNCTION(fn, *it);

//			fprintf(dump_file,"\nAdding %d to BES\n", bt->index);

			bes.insert(bt->index);
		}

//		fprintf(dump_file,"\nNEW BES\n");
//		print_set_integers(bes);

		((block_information *)(bb->aux))->reach_in = in;
		((block_information *)(bb->aux))->back_edge_sources = bes;

//		fprintf(dump_file,"\nReach IN\n");
//		print_set_integers(in);

		in.insert(bb->index);

//		out_n.insert(in.begin(), in.end());

//		fprintf(dump_file,"\nNew Reach OUT\n");
//		print_set_integers(in);

		if(!(out_p == in))
		{
			((block_information *)(bb->aux))->reach_out = in;

//			fprintf(dump_file,"\nReach Changed\n");

			temp = ((block_information *)(bb->aux))->succ_rel;
			temp1 = ((block_information *)(bb->aux))->succ_with_back_edge_rel;

			temp.insert(temp1.begin(), temp1.end());

			for(set< unsigned int >::iterator it = temp.begin(); it != temp.end(); it++)
			{
//				fprintf(dump_file,"\nPushing %d on worklist\n", *it);
				worklist.push_back(*it);
			}
		}
	}
}

bool is_indirect_call(struct cgraph_node *node, basic_block bb)
{
	tree decl;
	gimple stmt;

	if(((block_information *)(bb->aux))->call_block)
	{
		stmt = bb_call_stmt(bb);

		decl = get_called_fn_decl (stmt);

		if(is_function_pointer(decl))
		{
			return true;
		}
	}

	return false;
}

void compute_pred_rel(basic_block bb, struct cgraph_node *cnode)
{
       	edge e;
        edge_iterator ei;
	basic_block bt;

	set< unsigned int > temp_pred1, temp_pred2, temp1, temp2;

//	fprintf(dump_file,"\nInside compute_pred_rel Function %s BB = %d\n", cgraph_node_name(cnode), bb->index);

       	FOR_EACH_EDGE(e,ei,bb->preds)
       	{
               	bt = e->src;

//		fprintf(dump_file,"\nInside compute_pred_rel BT = %d\n", bt->index);

		if(bt->index == 0)
		{
			continue;
		}

		#if 0//!FP
		if(is_indirect_call(cnode, bt))
		{
			temp1 = ((block_information *)(bt->aux))->pred_rel;
			temp2 = ((block_information *)(bt->aux))->pred_with_back_edge_rel;

			temp_pred2.insert(temp2.begin(), temp2.end());
			temp_pred1.insert(temp1.begin(), temp1.end());
			
			continue;
		}
		#endif

		if(is_in_back_edge(bb, bt, cnode))
		{
//			fprintf(dump_file,"\nBB - BT in back edge\n");

			temp_pred2.insert(bt->index);
		}
		else
		{
//			fprintf(dump_file,"\nBB - BT no back edge\n");

			temp_pred1.insert(bt->index);
		}
       	}

//	fprintf(dump_file,"\nPred Rel\n");
//	print_set_integers(temp_pred1);
//	fprintf(dump_file,"\nPred Rel Completed\n");

	((block_information *)(bb->aux))->pred_rel.insert(temp_pred1.begin(), temp_pred1.end());	
	((block_information *)(bb->aux))->pred_with_back_edge_rel.insert(temp_pred2.begin(), temp_pred2.end());	
}

set< unsigned int > compute_pred_trans_rel(basic_block bb, struct cgraph_node *cnode)
{
       	edge e;
        edge_iterator ei;
	basic_block bt;

//	fprintf(dump_file, "\nInside compute_pred_trans_rel %d\n", bb->index);

	set< unsigned int > temp_pred1, temp_pred2;

	pred_succ_visited.insert(bb->index);

	temp_pred1.insert(bb->index);

       	FOR_EACH_EDGE(e,ei,bb->preds)
       	{
               	bt = e->src;

//		fprintf(dump_file,"\nPred Hey %d\n", bt->index);

		if(bt->index == 0)
		{
			continue;
		}

		#if 0
		if(is_in_back_edge(bb, bt, cnode))
		{
			temp_pred1.insert(bt->index);
			continue;
		}
		#endif

//		if(temp_pred1.find(bt->index) == temp_pred1.end())
		if(pred_succ_visited.find(bt->index) == pred_succ_visited.end())
		{
			temp_pred1.insert(bt->index);

			pred_succ_visited.insert(bt->index);

			temp_pred2 = compute_pred_trans_rel(bt, cnode);

			temp_pred1.insert(temp_pred2.begin(), temp_pred2.end());
		}
       	}

	return temp_pred1;

//	((block_information *)(bb->aux))->pred_trans_rel.insert(temp_pred1.begin(), temp_pred1.end());	
}


void compute_succ_rel(basic_block bb, struct cgraph_node *cnode)
{
       	edge e;
        edge_iterator ei;
	basic_block bt;

	set< unsigned int > temp_succ1, temp_succ2;

       	FOR_EACH_EDGE(e,ei,bb->succs)
       	{
               	bt = e->dest;

		if(bt->index == 0)
		{
			continue;
		}
	
		if(is_out_back_edge(bb, bt, cnode))
		{
			temp_succ2.insert(bt->index);
		}
		else
		{
			temp_succ1.insert(bt->index);
		}
       	}

//	fprintf(dump_file,"\nSucc Rel\n");
//	print_set_integers(temp_succ1);
//	fprintf(dump_file,"\nSucc Rel Completed\n");

	((block_information *)(bb->aux))->succ_rel.insert(temp_succ1.begin(), temp_succ1.end());	
	((block_information *)(bb->aux))->succ_with_back_edge_rel.insert(temp_succ2.begin(), temp_succ2.end());	
}

set< unsigned int > compute_succ_trans_rel(basic_block bb, struct cgraph_node *cnode)
{
       	edge e;
        edge_iterator ei;
	basic_block bt;

	pred_succ_visited.insert(bb->index);

	set< unsigned int > temp_succ1, temp_succ2;

	temp_succ1.insert(bb->index);

       	FOR_EACH_EDGE(e,ei,bb->succs)
       	{
               	bt = e->dest;

		if(bt->index == 0)
		{
			continue;
		}

		#if 0
		if(is_out_back_edge(bb, bt, cnode))
		{
			continue;
		}
		#endif

//		if(temp_succ1.find(bt->index) == temp_succ1.end())
		if(pred_succ_visited.find(bt->index) == pred_succ_visited.end())
		{
			temp_succ1.insert(bt->index);

			pred_succ_visited.insert(bt->index);

			temp_succ2 = compute_succ_trans_rel(bt, cnode);

			temp_succ1.insert(temp_succ2.begin(), temp_succ2.end());
		}
       	}

	return temp_succ1;

//	((block_information *)(bb->aux))->succ_trans_rel.insert(temp_succ1.begin(), temp_succ1.end());	
}

void print_set_integers(set< unsigned int > s)
{
	for(set< unsigned int >::iterator it = s.begin(); it != s.end(); it++)
	{
		fprintf(dump_file,"%u\t", *it);
	}
	fprintf(dump_file, "\n");
}

void print_list_integers(list< unsigned int > s)
{
	for(list< unsigned int >::iterator it = s.begin(); it != s.end(); it++)
	{
		fprintf(dump_file,"%d\t", *it);
	}
	fprintf(dump_file, "\n");
}

void compute_pred_succ_rel()
{
	struct cgraph_node * cnode;
	basic_block bb, bs;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		set< unsigned int > temp_set;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		struct function *fn;
	
		fn = DECL_STRUCT_FUNCTION(cnode->decl);

		FOR_EACH_BB (bb) 
		{
			pred_succ_visited.clear();

			compute_pred_rel(bb, cnode);
//			temp_set = compute_pred_trans_rel(bb, cnode);

//			((block_information *)(bb->aux))->pred_trans_rel.insert(temp_set.begin(), temp_set.end());	

			pred_succ_visited.clear();

			compute_succ_rel(bb, cnode);
//			temp_set = compute_succ_trans_rel(bb, cnode);

//			((block_information *)(bb->aux))->succ_trans_rel.insert(temp_set.begin(), temp_set.end());	

			set< unsigned int > t_b_set = ((block_information *)(bb->aux))->pred_with_back_edge_rel;

			for(set< unsigned int >::iterator sit = t_b_set.begin(); sit != t_b_set.end(); sit++)
			{
				bs = BASIC_BLOCK_FOR_FUNCTION(fn, *sit);

				((function_info *)(cnode->aux))->back_edges.insert(make_tuple(bs->index, bb->index));
			}

			#if 1
			perform_reachability_analysis(cnode);
			compute_in_loop(cnode);
			compute_pred_in_loop(cnode);
			#endif


			#if 0
			fprintf(dump_file,"\nPred Rel of BB %d: ", bb->index);
			print_set_integers(((block_information *)(bb->aux))->pred_rel);

			fprintf(dump_file,"\n\nPred with Back Edge Rel of BB %d: ", bb->index);
			print_set_integers(((block_information *)(bb->aux))->pred_with_back_edge_rel);

			fprintf(dump_file,"\n\nPred Trans Rel of BB %d: ", bb->index);
			print_set_integers(((block_information *)(bb->aux))->pred_trans_rel);

			fprintf(dump_file,"\n\nSucc Rel of BB %d: ", bb->index);
			print_set_integers(((block_information *)(bb->aux))->succ_rel);

			fprintf(dump_file,"\n\nSucc with Back Edge Rel of BB %d: ", bb->index);
			print_set_integers(((block_information *)(bb->aux))->succ_with_back_edge_rel);

			fprintf(dump_file,"\n\nSucc Trans Rel of BB %d: ", bb->index);
			print_set_integers(((block_information *)(bb->aux))->succ_trans_rel);
			#endif
		}

		bb = end_bb_of_fn(cnode);

		pred_succ_visited.clear();

		compute_pred_rel(bb, cnode);
//		temp_set = compute_pred_trans_rel(bb, cnode);

//		((block_information *)(bb->aux))->pred_trans_rel.insert(temp_set.begin(), temp_set.end());	

		pred_succ_visited.clear();

		compute_succ_rel(bb, cnode);
//		temp_set = compute_succ_trans_rel(bb, cnode);

//		((block_information *)(bb->aux))->succ_trans_rel.insert(temp_set.begin(), temp_set.end());

		set< unsigned int > t_b_set = ((block_information *)(bb->aux))->pred_with_back_edge_rel;

		for(set< unsigned int >::iterator sit = t_b_set.begin(); sit != t_b_set.end(); sit++)
		{
			bs = BASIC_BLOCK_FOR_FUNCTION(fn, *sit);

			((function_info *)(cnode->aux))->back_edges.insert(make_tuple(bs->index, bb->index));
		}	

		pop_cfun();
	}
}

bool is_out_back_edge(basic_block bb, basic_block bt, struct cgraph_node *cnode)
{
	if(bb->index == bt->index)
	{
		return true;
	}

	int i;
	unsigned int nb;
	basic_block temp = NULL;

	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	nb = ((function_info *)(cnode->aux))->get_num_bb()+1;

	int x = 0, y = 0;

	for(i = 0; i < nb-1; i++)
	{
		temp = BASIC_BLOCK(((function_info *)(cnode->aux))->rev_post_order[i]);

		if(temp == NULL)
		{
			continue;
		}

		if(temp->index == bb->index)
		{
			x = i;
			break;
		}
	}

	temp = NULL;
	
	for(i = 0; i < nb-1; i++)
	{
		temp = BASIC_BLOCK(((function_info *)(cnode->aux))->rev_post_order[i]);

		if(temp == NULL)
		{
			continue;
		}

		if(temp->index == bt->index)
		{
			y = i;
			break;
		}
	}

	pop_cfun();

	if(x > y)
	{
		return true;
	}

	return false;
}

bool is_in_back_edge(basic_block bb, basic_block bt, struct cgraph_node *cnode)
{
	if(bb->index == bt->index)
	{
		return true;
	}

	int i;
	unsigned int nb;
	basic_block temp = NULL;

	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	nb = ((function_info *)(cnode->aux))->get_num_bb()+1;

	int x = 0, y = 0;

	for(i = 0; i < nb-1; i++)
	{
		temp = BASIC_BLOCK(((function_info *)(cnode->aux))->rev_post_order[i]);

		if(temp == NULL)
		{
			continue;
		}

		if(temp->index == bb->index)
		{
			x = i;
			break;
		}
	}

	temp = NULL;
	
	for(i = 0; i < nb-1; i++)
	{
		temp = BASIC_BLOCK(((function_info *)(cnode->aux))->rev_post_order[i]);

		if(temp == NULL)
		{
			continue;
		}

		if(temp->index == bt->index)
		{
			y = i;
			break;
		}
	}

	pop_cfun();
	
//	fprintf(dump_file,"\nX = %d, Y = %d\n", x, y);

	if(x < y)
	{
		return true;
	}

	return false;
}

void reachability_exit_node(unsigned int node, struct cgraph_node *cnode)
{
	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);
	basic_block bb, bs;	

	bb = BASIC_BLOCK_FOR_FUNCTION(fn, node);

	set< unsigned int > preds, temp;

	preds = ((block_information *)(bb->aux))->pred_rel;
	temp = ((block_information *)(bb->aux))->pred_with_back_edge_rel;

	preds.insert(temp.begin(), temp.end());

	for(set< unsigned int >::iterator it = preds.begin(); it != preds.end(); it++)
	{
		if(visited_list.find(*it) == visited_list.end())
		{
			visited_list.insert(*it);

			bb_reachable_from_exit.erase(*it);

			reachability_exit_node(*it, cnode);
		}	
	}
}

bool is_exit_block_reachable_from_current_block(struct cgraph_node *cnode, basic_block bb)
{
	basic_block exit_block, bt;

	exit_block = end_bb_of_fn(cnode);

	visited_list.clear();

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	FOR_EACH_BB(bt)
	{
		bb_reachable_from_exit.insert(bt->index);
	}

	bb_reachable_from_exit.erase(exit_block->index);

	pop_cfun();

	reachability_exit_node(exit_block->index, cnode);
	
	if(bb_reachable_from_exit.find(bb->index) != bb_reachable_from_exit.end())
	{
		return false;
	}

	return true;
}

void compute_reachability_from_exit_node(struct cgraph_node *cnode)
{
	basic_block bb;

	set< unsigned int > unreachable_bb;

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	FOR_EACH_BB(bb)
	{
		if(!is_exit_block_reachable_from_current_block(cnode, bb))
		{
			unreachable_bb.insert(bb->index);
		}
	}

	bb = end_bb_of_fn(cnode);

	if(!is_exit_block_reachable_from_current_block(cnode, bb))
	{
		unreachable_bb.insert(bb->index);
	}

	((function_info *)(cnode->aux))->unreachable_bb = unreachable_bb;

//	fprintf(dump_file,"\nUnreachable Blocks in Function %s\n", cgraph_node_name(cnode));
//	print_set_integers(unreachable_bb);	

	pop_cfun();
}

void init_bb_aux()
{
basic_block bb, exit_bb;
struct cgraph_node *cnode;

for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {

        if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
          continue;
        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

        FOR_EACH_BB(bb)
                {
                bb->aux = new block_information(cnode);
                }

		exit_bb = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (cnode->decl));

		if (!exit_bb->aux)
		{
			exit_bb->aux = new block_information(cnode);
		}

        pop_cfun();
        }

}


void end_bb_aux()
{

struct cgraph_node *cnode;
basic_block bb;

for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {

if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
        continue;
        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

        FOR_EACH_BB (bb) {
                if (bb->aux)
                        {
                        delete (block_information *)bb->aux;
                        bb->aux = NULL;
                        }
                }



        pop_cfun();
        }
}

unsigned int gindex = 0;
list< unsigned int > S;
map< unsigned int, unsigned int > Index, Lowlink;
map< unsigned int, map< unsigned int, unsigned int > > ORDER, REV_ORDER;
bool onStack[3000];
set< set< unsigned int > > scc_in_call_graph;
map< unsigned int, set< unsigned int > > leaves_sccs;
map< unsigned int, set< unsigned int > > leavesSCCs;
map< unsigned int, set< unsigned int > > SCC_MAP;
unsigned int SCC_Count;
set< unsigned int > SCCs;
map< unsigned int, unsigned int > func_scc_map;
map< unsigned int, unsigned int > DFS_ORDER; // DFS_ORDER[func_num] = dfs_order
map< unsigned int, unsigned int > REV_DFS_ORDER; // REV_DFS_ORDER[dfs_order] = func_num
map< unsigned int, bool > LABEL;
unsigned int DFS_COUNT = 0;
unsigned int BFS_COUNT = 0;

void createSCCs()
{
	int i = 1;
	S.clear();
	gindex = 0;
	SCC_Count = FCount;

	for(; i <= FCount; i++)
	{
		Index[i] = -1;
		Lowlink[i] = 0;
		onStack[i] = false;
	}	

//	fprintf(dump_file, "\nDone with Initializations %d\n", FCount);

	for(i = 1; i <= FCount; i++)
	{
		if(Index[i] == -1)
		{
			strongConnect(i);
		}	
	}

	#if 0	
	printAllSCCs();
	printIntervalIndex();
	printLeavesOfAllSCCs();
	#endif
}

void printIntervalIndex()
{
	unsigned int i = 1;

	for(; i <= FCount; i++)
	{
		fprintf(dump_file, "\nBottom-up index of %s (%d) is %d\n", cgraph_node_name(func_numbering[i]), i, func_index_array[i]);
		fprintf(dump_file, "\nTop-down index of %s (%d) is %d\n", cgraph_node_name(func_numbering[i]), i, func_index_array_d[i]);
	}
}

void printLeavesOfAllSCCs()
{
	set< unsigned int > scc;

	unsigned int i = 0;

	for(map< unsigned int, set< unsigned int > >::iterator it = leaves_sccs.begin(); it != leaves_sccs.end(); it++)
	{
		fprintf(dump_file, "\nLeaf is a Function %s (%d)\n", cgraph_node_name(func_numbering[it->first]), it->first);

		scc = it->second;

		for(set< unsigned int >::iterator sit = scc.begin(); sit != scc.end(); sit++)
		{
			fprintf(dump_file, "\nFunction %s (%d)\n", cgraph_node_name(func_numbering[*sit]), *sit);
		}

		fprintf(dump_file, "\n\n");
	}
}

void printAllSCCs()
{
	set< unsigned int > scc;

	fprintf(dump_file, "\nAll SCCs in a Call Graph with their Indexes and Lowlinks\n");
	unsigned int i = 0;

	for(set< set < unsigned int > >::iterator it = scc_in_call_graph.begin(); it != scc_in_call_graph.end(); it++)
	{
		scc = *it;

		fprintf(dump_file, "\nSCC %d\n", ++i);
		
		for(set< unsigned int >::iterator sit = scc.begin(); sit != scc.end(); sit++)
		{
			fprintf(dump_file, "\nFunction %s (%d), Index = %d, Lowlink = %d\n", cgraph_node_name(func_numbering[*sit]), *sit, Index[*sit], Lowlink[*sit]);
		}

		fprintf(dump_file, "\n\n");
	}
}

void strongConnect(unsigned int v)
{
//	fprintf(dump_file, "\nstrongConnect %d\n", v);
//	fprintf(dump_file, "\nstrongConnect %s - %d\n", cgraph_node_name(func_numbering[v]), v);

	Index[v] = gindex;

	Lowlink[v] = gindex;

	gindex++;

	S.push_back(v);

	onStack[v] = true;

	set< unsigned int > callee_set = callees[v];
	unsigned int w;

	for(set< unsigned int >::iterator it = callee_set.begin(); it != callee_set.end(); it++)
	{
		w = *it;
	
//		fprintf(dump_file, "\nSuccessor of v %s - %d is w %s - %d\n", cgraph_node_name(func_numbering[v]), v, cgraph_node_name(func_numbering[w]), w);

//		fprintf(dump_file, "\nDetails of w %d, Lowlink = %d, Index = %d, onStack %d\n", w, Lowlink[w], Index[w], onStack[w]);
			
		if(Index[w] == -1)
		{
//			fprintf(dump_file, "\nInside if 1\n");
			
			strongConnect(w);

			if(Lowlink[w] < Lowlink[v])
			{
//				fprintf(dump_file, "\nInside if 2 %d, %d\n", Lowlink[v], Lowlink[w]);
			
				Lowlink[v] = Lowlink[w];
			}
		}
		else if(onStack[w])
		{
//			fprintf(dump_file, "\nInside else 1\n");
			
			if(Index[w] < Lowlink[v])
			{
//				fprintf(dump_file, "\nInside else 2 %d, %d\n", Lowlink[v], Index[w]);
			
				Lowlink[v] = Index[w];

				set< unsigned int > temp = leaves_sccs[v];
				temp.insert(w);

				leaves_sccs[v] = temp;
			}
		}

//		fprintf(dump_file, "\nInside the for loop\n");
	}

//	fprintf(dump_file, "\nOutside the for loop\n");

	set< unsigned int > scc;

	if(Lowlink[v] == Index[v])
	{
//		fprintf(dump_file, "\nNew SCC\n");

		do
		{
			w = S.back();

			S.pop_back();

			onStack[w] = false;

			scc.insert(w);

		}while(w != v);
	}

	if(scc.size() > 1)
	{
		scc_in_call_graph.insert(scc);

		SCC_MAP[++SCC_Count] = scc;
		unsigned int order;

		for(set< unsigned int >::iterator scit = scc.begin(); scit != scc.end(); scit++)
		{
			SCCs.insert(*scit);

			order = Index[*scit];
			ORDER[SCC_Count][*scit] = order;
			REV_ORDER[SCC_Count][order] = *scit;

			if(leaves_sccs.find(*scit) != leaves_sccs.end())
			{
				set< unsigned int > tempi;

				tempi = leavesSCCs[SCC_Count];
				tempi.insert(*scit);
				leavesSCCs[SCC_Count] = tempi;
			}

			func_scc_map[*scit] = SCC_Count;
		}

		#if 0
		fprintf(dump_file, "\nStrongly Connected Component with Function %s (%d), Index = %d", cgraph_node_name(func_numbering[v]), v, Index[v]);
		print_set_integers(scc);
		fprintf(dump_file, "\n\n");
		#endif
	}
}

void create_scc_call_graph()
{
//	fprintf(dump_file, "\nInside create_scc_call_graph: SCC_Count %d, FCount %d\n", SCC_Count, FCount);

	struct cgraph_node * cnode;
	unsigned int cnode_num, scc_num;
	set< unsigned int > preds, succs;

	#if 0
	fprintf(dump_file, "\nPrinting Call Graph\n");
	print_call_graph();
	#endif

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		cnode_num = ((function_info *)(cnode->aux))->func_num;

//		fprintf(dump_file, "\nConsidering Function %s (%d)\n", cgraph_node_name(cnode), cnode_num);

		LABEL[cnode_num] = false;

		if(SCCs.find(cnode_num)	!= SCCs.end()) // Present in SCC
		{
//			fprintf(dump_file, "\nIn a SCC\n");
			
			scc_num = func_scc_map[cnode_num];

			preds = callers[cnode_num];
			succs = callees[cnode_num];

			#if 0
			fprintf(dump_file, "\nPreds in original call graph\n");
			print_set_integers(preds);
			fprintf(dump_file, "\nSuccs in original call graph\n");
			print_set_integers(succs);
			#endif

			set< unsigned int > temp_s;

			temp_s = scc_callees[scc_num];

			#if 0
			fprintf(dump_file, "\ntemp_s\n");
			print_set_integers(temp_s);
			#endif

			for(set< unsigned int >::iterator sit = succs.begin(); sit != succs.end(); sit++)
			{
//				fprintf(dump_file, "\nSucc %d\n", *sit);

				if(SCCs.find(*sit) == SCCs.end())
				{
//					fprintf(dump_file, "\nNot in an SCC\n");

					temp_s.insert(*sit);
				}
			}

			scc_callees[scc_num] = temp_s;

			set< unsigned int > temp_p;

			temp_p = scc_callers[scc_num];

			for(set< unsigned int >::iterator pit = preds.begin(); pit != preds.end(); pit++)
			{
				if(SCCs.find(*pit) == SCCs.end())
				{
					temp_p.insert(*pit);
				}
			}

			scc_callers[scc_num] = temp_p;

			#if 0
			fprintf(dump_file, "\nPreds in new call graph\n");
			print_set_integers(scc_callers[scc_num]);
			fprintf(dump_file, "\nSuccs in new call graph\n");
			print_set_integers(scc_callees[scc_num]);
			#endif
		}
		else
		{
//			fprintf(dump_file, "\nNot in a SCC\n");
			
			preds = callers[cnode_num];
			succs = callees[cnode_num];

			#if 0
			fprintf(dump_file, "\nPreds in original call graph\n");
			print_set_integers(preds);
			fprintf(dump_file, "\nSuccs in original call graph\n");
			print_set_integers(succs);
			#endif

			set< unsigned int > temp_s;

			temp_s = scc_callees[cnode_num];

			for(set< unsigned int >::iterator sit = succs.begin(); sit != succs.end(); sit++)
			{
				if(SCCs.find(*sit) != SCCs.end())
				{
					scc_num = func_scc_map[*sit];

					temp_s.insert(scc_num);
				}
				else
				{
					temp_s.insert(*sit);
				}
			}

			scc_callees[cnode_num] = temp_s;

			set< unsigned int > temp_p;

			temp_p = scc_callers[cnode_num];

			for(set< unsigned int >::iterator pit = preds.begin(); pit != preds.end(); pit++)
			{
				if(SCCs.find(*pit) != SCCs.end())
				{
					scc_num = func_scc_map[*pit];

					temp_s.insert(scc_num);
				}
				else
				{
					temp_p.insert(*pit);
				}
			}

			scc_callers[cnode_num] = temp_p;

			#if 0			
			fprintf(dump_file, "\nPreds in new call graph\n");
			print_set_integers(scc_callers[cnode_num]);
			fprintf(dump_file, "\nSuccs in new call graph\n");
			print_set_integers(scc_callees[cnode_num]);
			#endif
		}
	}

//	print_scc_call_graph();
}

void DFS(unsigned int v)
{
	LABEL[v] = true;

//	fprintf(dump_file, "\nInside DFS %d order %d\n", v, DFS_COUNT);

	set< unsigned int > succs;
	unsigned int w;

	succs = scc_callees[v];

	for(set< unsigned int >::iterator it = succs.begin(); it != succs.end(); it++)
	{
		w = *it;

		if(!LABEL[w])
		{
			DFS(w);
		}
	}

	unsigned int order = DFS_COUNT;

	DFS_ORDER[v] = DFS_COUNT;
	REV_DFS_ORDER[DFS_COUNT] = v;

	DFS_COUNT--;
}

Prototype compute_Prototype (tree decl)
{
//	fprintf (dump_file, "\nin compute_Prototype");
//		tree t1 = TREE_TYPE (decl);
	tree t2 = TREE_TYPE (decl);

//						print_node (dump_file, "\nT2", t2, 0);

	unsigned int no_args = 0;
	list <tree> param;
	tree return_val = NULL;
	if (t2 && TREE_TYPE (t2))
	{

		return_val = TREE_TYPE (t2);
//						print_node (dump_file, "\nRETURN_VAL", return_val, 0);
//                fprintf (dump_file, "\nFunction Pointer return type: ");
//                print_generic_expr (dump_file, return_val, 0);
//		print_node (dump_file, "\n\t dumping args : ", t3, 0);

//my_print_node (dump_file, "parameters", TYPE_ARG_TYPES (t2), 0);

		if (TYPE_ARG_TYPES (t2))
		{	
			no_args = 1;
			tree t4 = TYPE_ARG_TYPES (t2);	
			param.push_back (TREE_VALUE (t4));
//			fprintf (dump_file, "\nArgument : %d :", TYPE_UID (TREE_VALUE (t4)));
  //            	  print_generic_expr (dump_file, TREE_VALUE (t4), 0);

			while (t4 && TREE_CHAIN (t4))
			{
//			          my_print_node (file, "chain", TREE_CHAIN (node), indent + 4);
				no_args++;
				t4 = TREE_CHAIN (t4);
				param.push_back (TREE_VALUE (t4));
//				fprintf (dump_file, "\nArgument : %d :", TYPE_UID (TREE_VALUE (t4)));
//              	  	print_generic_expr (dump_file, TREE_VALUE (t4), 0);
			}
		}

	}
	Prototype obj (no_args, param, return_val);
//	obj.set_no_args (no_args);

	return obj;
}


void collect_fp_type_info()
{
	gather_global_var_information ();

	struct cgraph_node *node;

	set< unsigned int > temp;

        for (node = cgraph_nodes; node; node = node->next)
        {
		/* Nodes without a body, and clone nodes are not interesting. */
                if (!gimple_has_body_p (node->decl) || node->clone_of)
                        continue;

                push_cfun (DECL_STRUCT_FUNCTION (node->decl));

		tree decl = node->decl;

		if (node->address_taken == 1)
		{
			Prototype obj = compute_Prototype (decl);
			fn_details [((function_info *)(node->aux))->func_num] = obj;
		}

                gather_local_var_information ();
		analyze_parm_decl_arguments ();

                /* restoring the context by popping cfun. */
                pop_cfun ();
        }

	#if 0
	fprintf(dump_file, "\nFN and FP Details\n");
	fflush(dump_file);

	print_fn_details ();	
	print_fp_details ();	

	fprintf(dump_file, "\nFN and FP Details\n");
	fflush(dump_file);
	#endif

}

//#endif
