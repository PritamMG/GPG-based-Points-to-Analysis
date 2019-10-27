#ifndef GPB_H_
#define GPB_H_

#include "GPU.h"
#include<set>
#include<list>
#include<map>

//extern long GPB_count;

typedef std::set< unsigned int > GPBSet;
typedef std::list< unsigned int > GPBList;

class GPB
{
	private:

		// BB Set of GPUs in this GPB
		GPUSet gpus;

		// BB Set of Original GPUs in this GPB
		GPUSet orig_gpus;

		// BB Set of May GPUs in this GPB
		GPUSet may_gpus;

		// BB Set of Must GPUs in this GPB
		GPUSet must_gpus;

		// Unique identifier of GPB, computed using GPB_count
		unsigned int id;

		// Type of GPB. 0 => Start GPB, 1 => End GPB, 2 => Parameter GPB, 3 => Return GPB
		unsigned int type;

		// BB index in  original CFG	
		unsigned int bb_index;

		bool call_block;
		bool exit_call_block;
		bool indirect_call_block;
		bool interval;
		bool interval_direct;
		bool sym_gpb;
		bool resolved;

		unsigned int callee;
		definitions indirect_callees;
		GPBSet interval_set;

		GPBSet set_callees;

		bool dirty;

	public:

		GPB() {id = 0; type = 4; exit_call_block = false; call_block = false; indirect_call_block = false; callee = 0; s_bb_block = true; e_bb_block = false; bb_index = 0; interval = false; interval_direct = false; dirty = false; sym_gpb = false; resolved = false;};

		Prototype proto;

		GPBSet getSetOfCallees();
		void setSetOfCallees(GPBSet s);

		bool isSymGPB();
		void setSymGPB();
		void resetSymGPB();

		bool isResolved();
		void setResolved();
		void resetResolved();

		bool isDirty();
		void setDirty();
		void resetDirty();

		// BB Add element to the Set of GPUs in this GPB
		void insertGPU(gpu_id_type);

		void insertGPUOrig(gpu_id_type);

		// BB Add pointer to PrevGpg
		void addPrev(unsigned int);

		// BB Remove pointer to PrevGpg
		void remPrev(unsigned int);

		// BB Add pointer to NextGpg
		void addNext(unsigned int);

		// BB Remove pointer to NextGpg
		void remNext(unsigned int);

		// BB to check whether this GPB is empty or not
		bool isEmpty();

		bool isInitialEmpty();

		// BB To find the match in in_ set and return all pairs of (dest_,
		// dest_ind_) whose nodeid == id and Indlist =</(prefix) list
		//std::unordered_set<Ref<Gpu>> MatchDestination(
		//   NodeIndex, IndirectionList);

		// BB get gpus in the GPB
		GPUSet getGPUs();
		void setGPUs(GPUSet g);

		GPUSet getOrigGPUs();
		void setOrigGPUs(GPUSet o);

		// BB get may gpus in the GPB
		GPUSet getMayGPUs();
		void setMayGPUs(GPUSet g);

		// BB get must gpus in the GPB
		GPUSet getMustGPUs();
		void setMustGPUs(GPUSet g);

		unsigned int getId();
		void setId(unsigned int i);

		unsigned int getBBIndex();
		void setBBIndex(unsigned int b);
	
		unsigned int getType();
		void setType(unsigned int t);

		bool isStartGPB();
		bool isEndGPB();
		bool isParaGPB();
		bool isReturnGPB();

		bool isCallBlock();
		bool isExitCallBlock();
		bool isIndirectCallBlock();
		bool isInterval();
		bool isIntervalDirect();

		void setCallBlock();
		void resetCallBlock();
		void setExitCallBlock();
		void resetExitCallBlock();
		void setIndirectCallBlock();
		void resetIndirectCallBlock();
		void setInterval();
		void resetInterval();
		void setIntervalDirect();
		void resetIntervalDirect();

		unsigned int getCallee();
		void setCallee(unsigned int c);

		definitions getIndirectCallees();
		void addIndirectCallee(node_id_type n);
		void setIndirectCallees(definitions callees);

		GPBSet getIntervalSet();
		void setIntervalSet(GPBSet s);

		GPB deep_copy();

		bool s_bb_block;
		bool e_bb_block;	

		void printGPB(struct cgraph_node *cnode);
		void printInitialGPB(struct cgraph_node *cnode);
};

extern std::map< unsigned int, std::map< unsigned int, GPBSet > > ori_red_map;

#if 0
extern std::map< unsigned int, std::map< unsigned int, GPUSet > > RIN;
extern std::map< unsigned int, std::map< unsigned int, GPUSet > > ROUT;
extern std::map< unsigned int, std::map< unsigned int, GPUSet > > BRIN;
extern std::map< unsigned int, std::map< unsigned int, GPUSet > > BROUT;

extern std::map< unsigned int, std::map< unsigned int, GPUSet > > PTSIN;
extern std::map< unsigned int, std::map< unsigned int, GPUSet > > PTSOUT;
#endif

extern std::map< unsigned int, std::map< unsigned int, GPBSet > > BB_START;
extern std::map< unsigned int, std::map< unsigned int, GPBSet > > BB_END;
extern std::map< unsigned int, std::map< unsigned int, GPBSet > > call_site_map; 

//extern std::map< unsigned int, std::map< unsigned int, GPB > > gpb_map; 

extern std::map< unsigned int, std::map< unsigned int, bool > > visited_map; 

extern std::map< unsigned int, std::map< unsigned int, unsigned int > > visited_count;
void printGPBList(GPBList list);
#endif  // AD GPB_H_
