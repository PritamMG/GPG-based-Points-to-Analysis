#ifndef INTERVAL_H
#define INTERVAL_H

#include "cgraph_node.hpp"
//#include "parser.hpp"
#include<stack>
#include<list>
#include<map>
#include<tr1/tuple>
#include<set>

using namespace std;

//typedef set< struct cgraph_node * > set_cnodes;
extern unsigned int interval_count;

class interval{

	unsigned int id;

	unsigned int header;

	list< unsigned int > node_list;

	unsigned int pred_count;
	unsigned int reach;
	unsigned int inter_order;
	bool marked;

	public:
		interval() {pred_count = 0; reach = 0; inter_order = 0; marked = false;}

		unsigned int get_id();
		void set_id(unsigned int);

		unsigned int get_header();
		void set_header(unsigned int);

		list< unsigned int > get_node_list();
		void set_node_list(list< unsigned int >);

		unsigned int get_pred_count();
		void set_pred_count(unsigned int);

		unsigned int get_reach();
		void set_reach(unsigned int);

		unsigned int get_inter_order();
		void set_inter_order(unsigned int);

		bool is_marked();
		void set_marked();
		void reset_marked();

//		friend bool operator<(const interval & i1, const interval & i2);
                friend bool operator==(const interval & i1, const interval & i2);

		void print_interval();

		list< struct cgraph_node * > get_cnodes();
		bool is_equal(interval);
};

typedef std::tr1::tuple< unsigned int, unsigned int > interval_edge;

typedef set< interval_edge > graph_type;

extern map< unsigned int, interval > interval_map;

class interval_graph{

	
	graph_type edge_list;
	
	unsigned int start_node;

	set< unsigned int > interval_set;	

	public:
		interval_graph(){};

		unsigned int get_start_node();
		void set_start_node(unsigned int);

		graph_type get_edge_list();
		void set_edge_list(graph_type);		

		set< unsigned int > get_interval_set();
		void set_interval_set(set< unsigned int >);

		unsigned int search_node(unsigned int);

		void reduce_interval_graph();
		void set_order_of_worklist();

//		friend bool operator<(const interval_graph & g1, const interval_graph & g2);
                friend bool operator==(const interval_graph & g1, const interval_graph & g2);

		void print_interval_graph();
		void create_edges_first_phase(interval);
		interval_graph create_edges(interval_graph, interval);

		bool is_equal(interval_graph);
		void depth_ordering(unsigned int);

		void set_order_of_worklist_d();
		void top_sort_ordering();
};

void find_interval_first_phase(unsigned int);
void print_edges(graph_type);
void print_nodes(set< unsigned int >);

#endif
