#include "gcc-plugin.h"

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
//#include "tm_p.h"
#include "diagnostic.h"
#include "tree-flow.h"
#include "tree-pass.h"
#include "toplev.h"
#include "tree.h"

#include "cgraph.h"          
#include "timevar.h"
#include "alloc-pool.h"
#include "params.h"
#include "ggc.h"
#include "vec.h"  
#include "cfgloop.h" 
//#include "tree-scalar-evolution.h" 
//#include "tree-vectorizer.h" 
#include "tree-dump.h" 

#include "tree-pretty-print.h"
#include "gimple-pretty-print.h"
#include <utility>
#include <list>
#include <vector>
#include <map>
#include <set>

using namespace std;
//typedef pair <bool, int> param_details;

class Prototype
{
	unsigned int no_args;
	list <tree> param_list;
	tree ret_value;

	public:
	Prototype ();//(unsigned int);
	Prototype (unsigned int, list <tree>, tree);
//	void set_no_args (unsigned int);
	void print ();
	bool compare (Prototype p2);
};

void print_fn_details ();
void print_fp_details ();

extern map <int, Prototype> fn_details; // Function Prototypes
extern map <int, Prototype> fp_details; // Function Pointer Prototypes

