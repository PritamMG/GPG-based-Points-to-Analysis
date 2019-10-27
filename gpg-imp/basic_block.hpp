#ifndef BASIC_BLOCK_H
#define BASIC_BLOCK_H

#include "con.hpp"
#include "parser.hpp"
#include <vector>
#include<list>
#include<map>
#include<set>

using namespace std;

class block_information{

	private:

		unsigned int order;
		bool visited;
		set< unsigned int > para_block;
		set< unsigned int > exit_block;
		
	public:	
		struct cgraph_node * node;
		constraint_list cons;
		
		bool call_block;
		bool return_block;
		bool start_block;
		bool end_block;
	
		std::set< unsigned int > sblocks, eblocks;

		block_information() {call_block = false; return_block=false;start_block = false;end_block=false;pinitialized = 1; dinitialized = 1; order = 1; visited = false; in_loop = false; pred_in_loop = false;}

		block_information(struct cgraph_node *);
		constraint_list & get_list();
		struct cgraph_node * get_cfun();

		void erase_list();

		set< unsigned int > pred_rel;
		set< unsigned int > pred_trans_rel;
		set< unsigned int > pred_with_back_edge_rel;
	
		set< unsigned int > succ_rel;
		set< unsigned int > succ_trans_rel;
		set< unsigned int > succ_with_back_edge_rel;

		set< unsigned int > reach_in;
		set< unsigned int > reach_out;

		bool in_loop, pred_in_loop;

		set< unsigned int > frontiers;
		set< unsigned int > back_edge_sources;
		
		clock_t start_t, end_t;

		set< unsigned int > get_para_block();
		void set_para_block(set< unsigned int > x);	

		set< unsigned int > get_exit_block();
		void set_exit_block(set< unsigned int > x);	

		int pinitialized;
		int dinitialized;

		bool is_visited();
		void set_visited();
		void reset_visited();

		unsigned int get_order();
		void set_order(unsigned int);
		void incre_order();		
};

#endif


