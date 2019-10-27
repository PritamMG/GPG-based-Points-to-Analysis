#ifndef CGRAPH_NODE_H
#define CGRAPH_NODE_H

#include "parser.hpp"
#include<stack>
#include<list>
#include<vector>
#define BLOCK_COUNT 5000
	
using namespace std;		

typedef list<basic_block>::iterator cgraphit;

class function_info {

	private:

		list< unsigned int > wrklist_points_red;
		list< unsigned int > wrklist_dfv_red;

		bool visited;
		bool dvisited;

		map< unsigned int, vector< unsigned int > > indirect_callees;

		unsigned int multi_return;	

		set<unsigned int> params;
		#ifndef MRB	
		unsigned int ret_id;	
		#endif	
		#ifdef MRB	
		set< unsigned int > ret_id;	
		#endif	

		unsigned int num_bb;	
		unsigned int end_block_index;

		bool has_ret;

		unsigned int pred_count;	
		int reach;
		unsigned int inter_order;	
		bool marked;
		unsigned int order;

	public:
		bool fixed_pt;

//		unsigned int GPB_count;

		unsigned int func_num;			
                function_info() {dvisited = false; visited = false; has_ret = false; count = 0; ordered  = false; pred_count = 0; reach = 0; inter_order = 0; marked = false; callee_count = 0; call_num = 0; cons_num = 0; dcount = 0; use_count = 0; end_block_id = 0; max_depth = 0; order = 0; multi_return = 0; num_stmts = 0; fixed_pt = false; num_trans_bbs = 0; num_nonptr_stmts = 0; cf_edges = 0; trans_cf_edges = 0; num_bbs = 0; num_trans_nonptr_stmts = 0; num_trans_stmts = 0;}

//		map< unsigned int, set< GPB* > > ori_red_map;

		unsigned int num_nonptr_stmts;
		unsigned int num_stmts;
		unsigned int cf_edges;
		unsigned int num_bbs;

		unsigned int num_trans_nonptr_stmts;
		unsigned int num_trans_stmts;
		unsigned int trans_cf_edges;
		unsigned int num_trans_bbs;

		set< unsigned int > inline_count;
		set< unsigned int > unreachable_bb;

		set< std::tr1::tuple< unsigned int, unsigned int > > back_edges;

		map< unsigned int, vector< unsigned int > > get_indirect_callees();	
		void set_indirect_callees(map< unsigned int, vector< unsigned int > > m);

		bool has_fixed_pt();
		void set_fixed_pt();
		void reset_fixed_pt();

		list< unsigned int > get_wrklist_points_red();
	        list< unsigned int > get_wrklist_dfv_red();

	        void set_wrklist_points_red(list< unsigned int >);
	        void set_wrklist_dfv_red(list< unsigned int >);

		unsigned int num_constraints;
	
		set< unsigned int > trans_callees;

		set_call_pts call_pts;
		unsigned int max_depth;

		set< unsigned int > pending_callees;

		unsigned int ret_bb;	
		unsigned int end_block_id;

		unsigned int callee_count;
		unsigned int cons_num;	
		unsigned int call_num;

		#if 1
		int rev_post_order[BLOCK_COUNT];	
		int post_order[BLOCK_COUNT];	
		int bb_rp_order[BLOCK_COUNT];	
		int bb_p_order[BLOCK_COUNT];	

		bool live_worklist[BLOCK_COUNT];	
		bool points_worklist[BLOCK_COUNT];	
		#endif

		#if 0
		int *rev_post_order;	
		int *post_order;	
		int *bb_rp_order;	
		int *bb_p_order;	

		bool *live_worklist;	
		bool *points_worklist;	
		#endif

		bool ordered;

		set< unsigned int > call_block_list;
		unsigned int count;
		unsigned int use_count;		
		unsigned int dcount;

		set<unsigned int> get_params();
		void set_params(set<unsigned int> p);

		void add_param(unsigned int);
		
		#ifndef MRB	
		unsigned int get_ret_id();
		void set_ret_id(unsigned int);	
		#endif
		#ifdef MRB	
		set< unsigned int > get_ret_id();
		void set_ret_id(set< unsigned int >);	
		#endif

		unsigned int get_multi_return();
		void set_multi_return(unsigned int);

		unsigned int get_pred_count();
		void set_pred_count(unsigned int);

		unsigned int get_order();
		void set_order(unsigned int);
		void incre_order();

		unsigned int get_reach();
		void set_reach(unsigned int);

		unsigned int get_inter_order();
		void set_inter_order(unsigned int);

		bool is_marked();
		void set_marked();	
		void reset_marked();	

		bool is_visited();
		void set_visited(bool b);

		bool is_dvisited();
		void set_dvisited(bool b);

		unsigned int get_num_bb();
		void set_num_bb(unsigned int);

		unsigned int get_end_block_index();
		void set_end_block_index(unsigned int);

		bool has_ret_type();
		void set_ret_type();
		void reset_ret_type();

		bool is_empty_worklist(int);
};
		
	     
#endif



