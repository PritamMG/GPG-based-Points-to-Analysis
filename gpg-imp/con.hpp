#ifndef CON_H
#define CON_H


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
#include "parser.hpp"
#include <list>

using namespace std;

	class auxiliary{
	
		int index;
		bool is_alias;
	
		public:
	
			auxiliary(int,bool);
			int get_int();
			bool get_bool();

	};

	

	typedef list< auxiliary >::iterator it;
	typedef list< auxiliary >::reverse_iterator rit;

	class constraint_list{
	
		list< auxiliary > conlist;
	
		public:
			constraint_list() {}
			void push(int,bool);
			it begin();
			int length();
			it end();
			rit rbegin();
			rit rend();
			bool empty();
			auxiliary & front();
			auxiliary & back();
	};


#endif 
