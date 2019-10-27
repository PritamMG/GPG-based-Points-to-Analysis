#ifndef ADDITIONAL_H_
#define ADDITIONAL_H_

#include "GPG.h"
//#include "parser.hpp"
//#include "cgraph_node.hpp"
#include <vector>
#include <tuple>
#include <set>
#include <map>

extern map< node_id_type, definitions > reuse_ssa; 
extern definitions visited_nodes, boundary_nodes;
extern map< unsigned int, GPBList > Function_Worklist; 

//====================================================================================================================================

unsigned int get_art_node(gimple stmt, basic_block bb, struct cgraph_node *cnode);
bool array_ptr_arith(node_id_type node);
definitions resolve_ssa(node_id_type node, bool type, basic_block bb, struct cgraph_node *cnode); // type = true => lhs, type = false => rhs
GPUSet resolveConstraintSSA(constraint_t cons, basic_block bb, struct cgraph_node *cnode);
GPUSet resolve_constraint_SSA(unsigned int id, basic_block bb, struct cgraph_node *cnode);
definitions resolve_fp_ssa(unsigned int fp_var, basic_block bb, struct cgraph_node *cnode);
GPUSet map_para_args_fp_call(unsigned int callee_rep, unsigned int caller_rep, basic_block bb);
bool isDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
bool isPDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
bool isDomPDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
void get_global_info();
GPG createNewGPG(struct cgraph_node *cnode);
IndirectionList create_indirection_list(bool type, struct constraint_expr e);
std::tuple< IndirectionList, IndirectionList > createIndirectionList(constraint_t con);
bool filter_constraint(unsigned int id, basic_block bb, struct cgraph_node *cnode); // Filter this constraint if this function returns true
bool needsInlining(unsigned int caller, unsigned int callee);
bool needsInliningRecursion(unsigned int caller, unsigned int callee);
void collectUpwardExposedVersions(GPUSet gen, struct cgraph_node *cnode);
GPBSet get_bb_pred(basic_block bb, struct cgraph_node *cnode);
GPBSet get_bb_succ(basic_block bb, struct cgraph_node *cnode);
std::pair< GPBSet, GPBSet> set_pred_succ(basic_block bb, struct cgraph_node *cnode);
bool analyze_callee_now(struct cgraph_node *callee);

#endif  // AD ADDITIONAL_H_
