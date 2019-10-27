#ifndef GPU_H_
#define GPU_H_

#include "IndirectionList.h"
#include "parser.hpp"

#include <limits>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <set>
#include <list>
#include <utility>
#define PRINT_DATA 1 
#define DATA_MEAS 0 
#define PROFILING 0
#define TIME_MEAS 0
#define FI_ANALYSIS 0 
#define CI_ANALYSIS 0
#define PAR_FI 0
#define BLOCKING 1
#define HEURISTICS 1

extern std::set< unsigned int > escaped;

typedef std::tuple< unsigned int, unsigned int, unsigned int > node_id_type;

typedef std::set< node_id_type > definitions;
typedef std::list< definitions > definitions_list;
typedef std::set< node_id_type > setOfNodes;
typedef std::list< node_id_type > listOfNodes;

extern std::map< node_id_type, set_tree_nodes > NodeType;

extern definitions visitedNodes;

class Node
{
	private:
		unsigned int var_index;	
		IndirectionList list;
		node_id_type node_id;

	public:
		Node() {}

		Node(unsigned int v, IndirectionList il)
		{
			var_index = v;
			list = il;

			insertNodeInMap();
		}
		
		unsigned int getVarIndex();
		void setVarIndex(unsigned int i);

		IndirectionList getList();
		void setList(IndirectionList l);

		node_id_type getNodeID() const;
		void setNodeID(node_id_type n);			

		void insertNodeInMap();

		void printNode();
		void printNodeID();

		bool operator==(const Node &n) const;
		Node conDep();
};

typedef std::pair< unsigned int, unsigned int > key_for_il;
extern std::map< key_for_il, std::vector< Node > > NodeMap;

Node getNode(node_id_type n);

void printSetofNodeIDs(setOfNodes s);
void printListofNodeIDs(listOfNodes l);
void printSetofNodes(setOfNodes s);
void printListofNodes(listOfNodes l);

typedef std::tuple< node_id_type, node_id_type > gpu_id_type;
//typedef std::tuple< node_id_type, node_id_type, unsigned int > gpu_id_type;

typedef std::tuple< unsigned int, unsigned int, gpu_id_type > stmt_info_type;

extern std::map< stmt_info_type, set< unsigned int > > stmt_id_info;


extern std::map< gpu_id_type, set_tree_nodes > DefTypes;
extern std::map< gpu_id_type, set_tree_nodes > RefTypes;

class GPU
{
	private:
		node_id_type src, tgt;
		unsigned int stmt_num;
		gpu_id_type gpu_id;

	public:

		GPU() {};
 
		GPU(node_id_type s, node_id_type t);
		GPU(Node s, Node t);

		// == operator overloading
		bool operator==(const GPU &g) const;

		gpu_id_type getGPUID() const;
		void setGPUID(gpu_id_type g);

		// get source and target
		node_id_type getSource();
		void setSource(node_id_type s);

		unsigned int getSourceVar();
		IndirectionList getSourceList();

		node_id_type getTarget();
		void setTarget(node_id_type t);

		unsigned int getTargetVar();
		IndirectionList getTargetList();

		// get stmtnum
		unsigned int getStmtNum();
		void setStmtNum(unsigned int s);

		void printGPU();

		// global map of GPUs
		static std::map< gpu_id_type, GPU > gpu_map;
};

typedef std::set< gpu_id_type > GPUSet;

extern std::map< unsigned int, std::map< unsigned int, GPUSet > > GPG_GPUs_map;

typedef std::tuple< unsigned int, unsigned int > gpu_key_type;

extern std::map< gpu_key_type, unsigned int > gpu_key;

extern GPUSet exportedDef, importedUse;

extern std::map< unsigned int, GPUSet > FI_DATA_FI_ANALYSIS;

extern std::map< gpu_id_type, GPUSet > typeCompatibleGPUs;

extern std::map< gpu_id_type, bool > ptr_arith_map;
//extern std::map< unsigned int, bool > ptr_arith_map;
extern std::map< unsigned int , GPUSet > PTS_INFO;

extern std::map< unsigned int, GPUSet > Queued;

extern bool ptr_arith;

extern std::map< unsigned int, GPUSet > flowInsensitiveInformation;
extern std::map< unsigned int, std::map< unsigned int, GPUSet > > FIP;
extern std::map< unsigned int, std::map< unsigned int, GPUSet > > FINP;

extern GPUSet queued_temp;

bool isPivotPresent(node_id_type n_id, gpu_id_type p_id);
bool isValidSSComposition(node_id_type n_id, gpu_id_type p_id);
bool isValidTSComposition(node_id_type n_id, gpu_id_type p_id);
bool isDesirableComposition(node_id_type n_id, gpu_id_type p_id);
bool undesComposition(bool type, node_id_type n_id, gpu_id_type p_id);

definitions TSComposition(node_id_type n_id, gpu_id_type p_id);
definitions SSComposition(node_id_type n_id, gpu_id_type p_id);

bool isDataDependent(gpu_id_type c_id, gpu_id_type p_id);
bool areDataDependent(GPUSet gpus1, GPUSet gpus2);

bool isBoundaryGPU(gpu_id_type bg);
bool isIndirectGPU(gpu_id_type indg);
GPUSet ret_ind_gpus(GPUSet r);

definitions getAllNodes(unsigned int n, IndirectionList list);

definitions NodeReduction(bool type, node_id_type n_id, GPUSet rin, GPUSet used, struct cgraph_node *cnode); // Source = 1, Target = 0
definitions NodeReductionWB(bool type, node_id_type n_id, GPUSet rin, GPUSet brin, GPUSet used, struct cgraph_node *cnode);

GPUSet GPUReduction(gpu_id_type c_id, GPUSet rin, GPUSet used, struct cgraph_node *cnode); // Source = 1, Target = 0
std::tuple< GPUSet, GPUSet > GPUReductionWB(gpu_id_type c_id, GPUSet rin, GPUSet brin, GPUSet used, struct cgraph_node *cnode); // Source = 1, Target = 0

GPUSet meet(GPUSet in1, GPUSet in2);

definitions Def(GPUSet red, gpu_id_type w);
GPUSet Match(gpu_id_type w, GPUSet rin);
GPUSet killBoundaryDefinition(gpu_id_type c_id);
GPUSet Kill(GPUSet red, GPUSet rin, struct cgraph_node *cnode, unsigned int id, definitions dfp);
bool toBeKilled(struct cgraph_node *cnode, GPUSet gen, unsigned int gpb_id, gpu_id_type w);

GPUSet RGen(GPUSet rin, GPUSet delta, struct cgraph_node *cnode, unsigned int gpb_id);
GPUSet ROut(GPUSet rin, GPUSet rgen, GPUSet rkill);
std::tuple< GPUSet, GPUSet > ReachingGPUsAnalysis(GPUSet rin, GPUSet delta, struct cgraph_node *cnode, unsigned int id, definitions dfp);

std::tuple< GPUSet, GPUSet > BRGen(GPUSet rin, GPUSet brin, GPUSet delta, struct cgraph_node *cnode, unsigned int gpb_id);
GPUSet Blocked(GPUSet rin, GPUSet rgen);
GPUSet RegenerateGPUs(GPUSet blocked, GPUSet brin, GPUSet brgen_temp);
GPUSet MatchSourceVar(GPUSet I, GPUSet G);
GPUSet BROut(GPUSet brin, GPUSet brgen, GPUSet brkill, GPUSet blocked);
std::tuple< GPUSet, GPUSet, GPUSet > ReachingGPUsAnalysisWB(GPUSet rin, GPUSet brin, GPUSet delta, struct cgraph_node *cnode, unsigned int id, definitions dfp);

void print_GPU(gpu_id_type gpu);
void printSetOfGPUs(GPUSet gpus);
bool isPointstoEdge(gpu_id_type gpu);
bool isKLimited(gpu_id_type gpu);
bool isPointstoInformation(gpu_id_type gpu);
bool isUseGPU(gpu_id_type gpu);

void print_NodeID(node_id_type n);

// Obsolete Functions

GPUSet ss_composition(gpu_id_type c_id, gpu_id_type p_id);    
GPUSet ts_composition(gpu_id_type c_id, gpu_id_type p_id);    

bool is_pivot_present_ss_composition(gpu_id_type c_id, gpu_id_type p_id);	
bool is_pivot_present_ts_composition(gpu_id_type c_id, gpu_id_type p_id);	

bool is_valid_ss_composition(gpu_id_type c_id, gpu_id_type p_id);
bool is_valid_ts_composition(gpu_id_type c_id, gpu_id_type p_id);

bool is_desirable_ss_composition(gpu_id_type c_id, gpu_id_type p_id);
bool is_desirable_ts_composition(gpu_id_type c_id, gpu_id_type p_id);

bool undes_ss_composition(gpu_id_type c_id, gpu_id_type p_id);
bool undes_ts_composition(gpu_id_type c_id, gpu_id_type p_id);

GPUSet filterLocal(GPUSet gen, struct cgraph_node *cnode);

void printSetOfGPUIDs(GPUSet gpus);
void printDefinitions(definitions defs);
void printDefinitionsList(definitions_list defs);

bool isInScope(unsigned int var, struct cgraph_node *cnode);

bool sanityCheck(GPUSet gen);

bool isArray(unsigned int var);
bool isArrayTree(tree t);
bool areStructHeapData(GPUSet gpus);

gpu_id_type getCopyGPU(node_id_type nid);
GPUSet filterFlowInsensitiveData(GPUSet gen, struct cgraph_node *cnode, unsigned int gpb_id);
bool isStackGPU(gpu_id_type id);
bool areAdvancingGPUs(GPUSet gpus);
bool areSameSourceGPUs(GPUSet gpus);
bool isAdvancingGPU(gpu_id_type id);
bool isKLimitedGPU(gpu_id_type id);
GPUSet convertAdvancingToKLimitedGPU(gpu_id_type id);

definitions FINodeReduction(bool type, node_id_type n_id, struct cgraph_node *cnode);
definitions FIGPUComposition(bool type, node_id_type n_id, GPUSet fi, struct cgraph_node *cnode);
GPUSet FIComposition(GPUSet delta, struct cgraph_node *cnode);
GPUSet FIComp(GPUSet delta, struct cgraph_node *cnode);
gpu_id_type stripUpwardsExposed(gpu_id_type id);

bool checkGPUSetForCoalescing(GPUSet gpus, struct cgraph_node *cnode);
bool isDerefGPU(gpu_id_type indg);

set_tree_nodes extractTypeOfExpression(node_id_type n);
void collectTypeInfoForGPUSet(struct cgraph_node *cnode, GPUSet gpus, bool orig);

set_tree_nodes fieldsType(set_tree_nodes res, unsigned int field);
set_tree_nodes findFieldType(tree t, unsigned int field);


std::pair< set_tree_nodes, set_tree_nodes >  computeTypeOfNode(node_id_type n, bool lhs);
bool isDataDependencePresent(gpu_id_type p, gpu_id_type c);
void recordDataDependenceForGPUSet(GPUSet gpus);
void recordDataDependence(GPUSet p_gpus, GPUSet c_gpus);
GPUSet computeBlockedGPUs(GPUSet in, GPUSet bar);

void computeDefRefForGPUSet(struct cgraph_node *cnode, GPUSet gpus, bool orig);

bool skipFunction(unsigned int id);

#endif  // AD GPU_H_
