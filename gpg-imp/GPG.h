#ifndef GPG_H_
#define GPG_H_

#include "GPB.h"
#include "cgraph_node.hpp"
#include "basic_block.hpp"
#include <vector>
#include <map>
#include <string>
#define NEW_APP 1
#define INTDIR 0
#define OPTIMIZE 0

typedef std::pair< unsigned int, unsigned int > edge_type;
typedef std::set< edge_type > edge_set;
typedef std::set< edge_type > call_site_info;

extern GPBSet visited_list1, bb_reachable_from_start1, bb_reachable_from_exit1, all_succ_list1;

extern unsigned long sr_op, dead_op, emp_op, coal_op, tot_op;
extern struct timeval TValBefore, TValAfter, DTValBefore, DTValAfter, ETValBefore, ETValAfter, CTValBefore, CTValAfter, STValBefore, STValAfter;

extern std::map< unsigned int, unsigned int > enhanceCount;
extern std::map< unsigned int , GPUSet > UpwardsGPUs;
extern std::map< unsigned int , GPBSet > OriginalGPUs;

extern std::map< unsigned int, std::map< unsigned int, bool > > LABEL_GPB;
extern std::map< unsigned int, std::map< unsigned int, unsigned int > > DFS_GPB;
extern std::map< unsigned int, std::map< unsigned int, unsigned int > > REV_DFS_GPB;
extern std::map< unsigned int, std::map< unsigned int, unsigned int > > BFS_GPB;
extern std::map< unsigned int, std::map< unsigned int, unsigned int > > REV_BFS_GPB;

extern std::map< unsigned int, unsigned int > PROCESSING_COUNT;

extern std::map< unsigned int, GPUSet > BDEFS;

extern std::map< unsigned int, std::map< unsigned int, GPUSet > > BI;

extern GPUSet U_FI_GPUs, U_FIP_GPUs, U_GPUs, UFICS;

extern std::map< unsigned int, bool > INC, OUTC;

extern GPBSet already_coalesced, coalesceG;

extern definitions DFP_TEMP;

extern unsigned int unreachableGPUs;

typedef int * d_worklist_type;
extern std::map< unsigned int, d_worklist_type > GPB_worklist;

class GPG
{
	private:
		bool top;

		edge_set back_edges;

		// AD Start and Exit GPB
		unsigned int entry;
		unsigned int end;

		// BB vector of GPBs which are contained in a GPG
		GPBSet gpbs;
		std::map< unsigned int, GPG > intervals;

		std::map< unsigned int, GPBSet > preds;
		std::map< unsigned int, GPBSet > succs;

		GPBSet call_sites;


	public:

		// BB constructor
		GPG() {entry = 0, end = 0; top = false; GPB_count = 1;}

		GPG(unsigned int, unsigned int, GPBSet, edge_set, GPBSet);

		std::map< unsigned int, GPB > gpb_map;

		std::map< unsigned int, GPUSet > RIN;
		std::map< unsigned int, GPUSet > ROUT;

		std::map< unsigned int, GPUSet > BRIN;
		std::map< unsigned int, GPUSet > BROUT;

		std::map< unsigned int, definitions > DFP;

		std::map< unsigned int, GPUSet > PTSIN;
		std::map< unsigned int, GPUSet > PTSOUT;

		unsigned int GPB_count;

		GPBSet getCallSites();
		void setCallSites(GPBSet s);

		std::map< unsigned int, GPBSet > getPreds() const;
		void setPreds(std::map< unsigned int, GPBSet > p);

		std::map< unsigned int, GPBSet > getSuccs() const;
		void getSuccs(std::map< unsigned int, GPBSet > s);

		GPBSet getPrev(unsigned int n);
		GPBSet getNext(unsigned int n);

		void setPrev(unsigned int n, GPBSet s);
		void setNext(unsigned int n, GPBSet s);

		void addPrev(unsigned int n, unsigned int a);
		void remPrev(unsigned int n, unsigned int a);

		void addNext(unsigned int n, unsigned int a);
		void remNext(unsigned int n, unsigned int a);

		// BB get entry & exit GPB
		unsigned int getEntryGPB() const;
		unsigned int getExitGPB() const;
  

		void setEntryGPB(unsigned int gpb)
		{
			entry = gpb;
		}

		void setExitGPB(unsigned int gpb)
		{
			end = gpb;
		}

		bool isTop();
		void setTop();
		void resetTop();

		// BB get gpb set in the GPGs
		GPBSet getGPBs() const;
		void setGPBs(GPBSet g);

		// BB get gpb set in the GPGs
		std::map< unsigned int, GPG > getIntervals() const;
		void setIntervals(std::map< unsigned int, GPG > g);

		void addGPB(unsigned int gpb_id, GPBSet prev, GPBSet next, struct cgraph_node *cnode);

		void deadGPUElimination(GPUSet queued, struct cgraph_node *cnode);
		void commonGPUElimination(struct cgraph_node *cnode);
		void eliminateGPB(unsigned int gpb, struct cgraph_node *cnode);
		void eliminateEmptyGPB(unsigned int gpb, struct cgraph_node *cnode);

		GPUSet getPrevGPUs(struct cgraph_node *cnode, unsigned int gpb_id);

		void coalesceGPBs(unsigned int gpb1, unsigned int gpb2, struct cgraph_node *cnode);
		bool checkDataDependence(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
		void CoalescingGPBs(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);

		edge_set getBackEdges();
		void setBackEdges(edge_set e);

		GPBSet loop(edge_type e, struct cgraph_node *cnode);
		void forwardReachable(unsigned int gpb1, unsigned int gpb2, unsigned int exit, struct cgraph_node *cnode);
		GPBSet frontiers(edge_type e, struct cgraph_node *cnode);
		void regularizedLoop(edge_type e, struct cgraph_node *cnode);	
		void regularizedAllLoops(struct cgraph_node *cnode);	

		void printGPG(struct cgraph_node *cnode);
		void printInitialGPG(struct cgraph_node *cnode);

		bool operator==(const GPG &g) const;
		
		bool containsCycle(struct cgraph_node *cnode);

		void reachability_start_node_recursive(unsigned int node, struct cgraph_node *cnode);
		void reachability_exit_node_recursive(unsigned int node, struct cgraph_node *cnode);
		void reachability(struct cgraph_node *cnode);

		void succ_trans(unsigned int node, struct cgraph_node *cnode);

		bool maxNodeCount();
		bool isIdentity();
		bool isFreeOfCallGPBs(struct cgraph_node *cnode);
		std::set< unsigned int > getCallBlocksForGPG(struct cgraph_node *cnode);

		bool isReachableFromStartNode(unsigned int node, struct cgraph_node *cnode);
		bool isReachableFromExitNode(unsigned int node, struct cgraph_node *cnode);

		bool checkGPGStructure(struct cgraph_node *cnode, bool orig);
		
		GPBSet getCallBlocks(struct cgraph_node *cnode);
		GPBSet getSymGPBs(struct cgraph_node *cnode);
		GPBSet getCallBlocksForCallee(struct cgraph_node *cnode, unsigned int the_callee);
		GPBSet getIndirectCallBlocks(struct cgraph_node *cnode);
		GPBSet getIntervalBlocks(struct cgraph_node *cnode);

		GPG meet(GPG g);
		unsigned int returnNumberOfEmptyGPBsFromGPG(unsigned int caller, bool orig);
		GPBSet returnEmptyGPBs(unsigned int caller, bool orig);
	
		unsigned int returnNumberOfDirectCallBlocks(struct cgraph_node *cnode);
		unsigned int returnNumberOfIndirectCallBlocks(struct cgraph_node *cnode);
		unsigned int returnNumberOfIntervals(struct cgraph_node *cnode);
		unsigned int returnNumberOfControlFlowEdges(struct cgraph_node *cnode);

		bool emptyGPG(struct cgraph_node *cnode);
	
		unsigned int coalescingGroupOfGPBs(GPBSet coalesce_group, struct cgraph_node *cnode);	
		
		unsigned int returnNumberOfOrigGPUs(struct cgraph_node *cnode);
		unsigned int returnNumberOfReducedGPUs(struct cgraph_node *cnode);
		bool areCallBlocksPresentForRecursion(struct cgraph_node *cnode);

		void removeEmptyGPB(unsigned int id, struct cgraph_node *cnode);
		void removeGPB(unsigned int id, struct cgraph_node *cnode);
		void replaceSibGPBs(unsigned int id, unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
		void replaceGPBs(unsigned int id, unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
		void replaceGPB(unsigned int id, unsigned int id_r, struct cgraph_node *cnode);
		bool areRelated(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
		void replaceAdjGPBs(unsigned int id, unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
		void coalesceAdjGPBs(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);

		void eliminateAllEmptyGPBs(struct cgraph_node *cnode, bool empty);

		bool canCoalesce(unsigned int gpb_id, GPBSet succs, struct cgraph_node *cnode);

		void insertParaGPBForDirectCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee, GPUSet res);
		void insertRetGPB(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, unsigned int x, GPG g_callee, GPUSet res);
		GPBSet inlineCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee);
		void inlineCallAlt(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee);
		GPUSet getParaArgGPUs(basic_block bb, struct cgraph_node *cnode);
		GPUSet getRetGPUs(basic_block bb, struct cgraph_node *caller, struct cgraph_node *callee, GPG g_callee);
		
		void replaceIndirectCallGPB(unsigned int gpb_id, unsigned int cnode_num, basic_block bb);
		void replaceDirectCallGPB(unsigned int gpb_id, unsigned int cnode_num, basic_block bb);
		void eraseDirectCallGPB(unsigned int gpb_id, unsigned int cnode_num);
		void eraseIndirectCallGPB(unsigned int gpb_id, unsigned int cnode_num);

		void insertParaGPBForIndirectCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee, GPUSet res);
		void insertRetGPBForIndirectCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, unsigned int x, GPG g_callee, GPUSet res);
		GPBSet inlineIndirectCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee);
		void inlineIndirectCallAlt(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee);
		GPBSet inlineIndirectCallAltLatest(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee);

		void recordBackEdges(struct cgraph_node *cnode);

		void checkForCoalescing(struct cgraph_node *cnode);
		void sanitize(struct cgraph_node *cnode, bool orig); // orig = true => Original GPUs, orig = false => Reduced GPUs
		void localOptimizations(struct cgraph_node *cnode, bool orig);
		void generateDotFileForGPG(struct cgraph_node *cnode, bool orig, string name);
		void performCoalescing(struct cgraph_node *cnode);
		void optimizeGPG(struct cgraph_node *cnode, bool orig);
		void computeDownwardsExposedDefinitions(struct cgraph_node *cnode);

		void handlingCalls(struct cgraph_node *cnode);
		void handlingCallsAlt(struct cgraph_node *cnode);
		void handlingRecursiveCalls(struct cgraph_node *cnode);
		void handlingSymGPBs(struct cgraph_node *cnode);
		GPUSet insertBoundaryDefinitions(struct cgraph_node *cnode);
		void initialize_GPB_worklist(struct cgraph_node *cnode);
		void analyzeCallees(struct cgraph_node *caller);
		void handlingSelectiveCalls(struct cgraph_node *cnode, unsigned int the_callee);

		void analyzeGPG(struct cgraph_node *cnode, bool again);
		bool analyzeGPB(unsigned int gpb_id, struct cgraph_node *cnode);
		GPUSet get_rin(unsigned int gpb_id, struct cgraph_node *cnode);
		GPUSet get_brin(unsigned int gpb_id, struct cgraph_node *cnode);
		void get_succ_gpbs(unsigned int current_node_id, struct cgraph_node *cnode);
		void get_pred_gpbs(unsigned int current_node_id, struct cgraph_node *cnode);
		void convertIndirectCallToDirectCall(unsigned int call, unsigned int callee_rep, unsigned int caller_rep, basic_block bb);
		void processIndirectCall(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet rin, GPUSet brin);
		void processIndirectCallAlt(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet rin, GPUSet brin);
		bool processingRecursion(struct cgraph_node *cnode);
		void after_recursion(struct cgraph_node *cnode);

		void createIntervals(struct cgraph_node *cnode);
		void addToInterval(unsigned int gpb_id, struct cgraph_node *cnode);
		void makeInterval(GPBSet interval_set, struct cgraph_node *cnode, bool direct);
		void createIntervalsForDirectCalls(struct cgraph_node *cnode);
		void addToIntervalForDirectCalls(unsigned int gpb_id, struct cgraph_node *cnode);

		GPUSet get_ptsin(unsigned int gpb_id, struct cgraph_node *cnode);
		void computePointstoGPG(struct cgraph_node *cnode);
		void computePointstoGPB(unsigned int gpb_id, struct cgraph_node *cnode);
		void resolveInterval(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet ptsin);
		void inlineInterval(unsigned int gpb_id, struct cgraph_node *cnode);
		void resolveIntervalDirect(unsigned int gpb_id, struct cgraph_node *cnode);

		GPUSet computeBI(unsigned int gpb_id, struct cgraph_node *cnode);
		GPUSet getCallIn(unsigned int bb_index, struct cgraph_node *cnode);
		GPUSet filterBI(GPUSet temp, struct cgraph_node *cnode);
		GPUSet filterGPUs(node_id_type node, GPUSet gpus, bool type);

		void oneMoreOptimization(struct cgraph_node *cnode);
		void performOneMoreOptimization(GPBSet interval_set, struct cgraph_node *cnode);
		void checkOneMoreOptimization(unsigned int gpb_id, struct cgraph_node *cnode);

		void eliminateSelfLoops(struct cgraph_node *cnode);
		void eliminateSelectiveSelfLoops(struct cgraph_node *cnode, bool orig);

		bool isIdentityGPG(struct cgraph_node *cnode, bool orig);

		#if INTDIR
		GPBSet getIntervalDirectBlocks(struct cgraph_node *cnode);
		#endif

		GPBSet computeIN(unsigned int gpb_id, struct cgraph_node *cnode);
		void eliminateEmptyGPBsDFA(struct cgraph_node *cnode, bool orig);

		void partial_analysis(struct cgraph_node *cnode, unsigned int callee);

		unsigned int returnNumberOfHeapGPUs(struct cgraph_node *cnode, bool orig);
		unsigned int returnNumberOfScalarGPUs(struct cgraph_node *cnode, bool orig);
		unsigned int returnNumberOfFIGPUs(struct cgraph_node *cnode);

		GPUSet returnNonScalarGPUs(struct cgraph_node *cnode, bool orig);
		GPUSet returnScalarGPUs(struct cgraph_node *cnode, bool orig);
		GPUSet returnAllGPUs(struct cgraph_node *cnode, bool orig);
		GPUSet returnFIGPUs(struct cgraph_node *cnode);
		GPUSet returnGPUsWithUpwardsExposedVariables(struct cgraph_node *cnode, bool orig);

		void kLimitGPUsInGPG(struct cgraph_node *cnode, bool orig);
		GPBSet returnCallBlocksPresentForRecursion(struct cgraph_node *cnode);

//		void collectPTSInfo(struct cgraph_node *cnode);

		void DFS(unsigned int v, struct cgraph_node *cnode);
		void BFS(struct cgraph_node *cnode);

		void coalescingDFA(struct cgraph_node *cnode);
		void coalescingDFAAlt(struct cgraph_node *cnode);
		void collectGroup(unsigned int current_node_id, struct cgraph_node *cnode);
		bool checkRegularPart();
		bool makeRegularPart();

		GPUSet returnGPUs(struct cgraph_node *cnode, bool orig);
		void collectTypeInfo(struct cgraph_node *cnode, bool orig);

		std::pair< GPBSet, GPBSet> set_pred_succ(basic_block bb, struct cgraph_node *cnode);

		void renumberGPBs(struct cgraph_node *cnode);
		void coalesceStartGPB(struct cgraph_node *cnode);
		void coalesceEndGPB(struct cgraph_node *cnode);
		void coalesceStartEndGPBs(struct cgraph_node *cnode);

		void recordDataDependence(struct cgraph_node *cnode, bool orig);
		void computeDefRef(struct cgraph_node *cnode, bool orig);

		std::tuple< unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int > returnAllTypesOfGPUs(struct cgraph_node *cnode);

		void computeBackEdges(struct cgraph_node *cnode);

		void post_processing(struct cgraph_node *cnode);
		void analyzeGPGWithBI(struct cgraph_node *cnode, bool again, GPUSet bi);
		bool analyzeGPBWithBI(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet bi);

		unsigned int returnNumberOfSymGPBs(struct cgraph_node *cnode);

		void shouldRepresentSymGPG(struct cgraph_node *cnode);

		unsigned int returnNumberOfGPBsFromGPG(unsigned int caller);

		void copyFIData(unsigned int callee_rep, unsigned int caller_rep);

		void computeDFP(unsigned int gpb_id);
};

extern std::map< unsigned int, GPUSet > prospectiveProducerGPUs;
extern std::map< unsigned int, GPG > GPG_map;
extern std::map< unsigned int, GPG > Initial_GPG_map;
extern std::map< unsigned int, GPG > Call_GPG_map;
extern std::map< unsigned int, GPG > deltaGPG_map; // For Recursion
extern std::map< unsigned int, GPG > optimized_GPG_map;
extern std::map< unsigned int, GPG > partial_optimized_GPG_map;
extern std::map< unsigned int, unsigned int > SMOD;
extern std::map< unsigned int, unsigned int > SREF;
extern unsigned int SMCALLS;
extern unsigned int SRCALLS;
extern std::map< unsigned int, definitions > lhsUpwardsExposedDefinitions;
extern std::map< unsigned int, definitions > rhsUpwardsExposedDefinitions;
extern std::map< unsigned int, GPUSet > DownwardsExposedMayDefinitions;
extern std::map< unsigned int, GPUSet > DownwardsExposedMustDefinitions;
extern std::map< unsigned int, definitions > incompleteCallees;

extern std::map< unsigned int, call_site_info > CallerCallSite;

//===============================================================================================================================

extern map< node_id_type, definitions > reuse_ssa; 
extern definitions visited_nodes, boundary_nodes;
extern map< unsigned int, GPBList > Function_Worklist; 

//====================================================================================================================================

unsigned int get_art_node(gimple stmt, basic_block bb, struct cgraph_node *cnode);
bool array_ptr_arith(node_id_type node);
definitions resolve_ssa(node_id_type node, bool type, basic_block bb, struct cgraph_node *cnode); // type = true => lhs, type = false => rhs
GPUSet resolveConstraintSSA(constraint_t cons, basic_block bb, struct cgraph_node *cnode);
GPUSet resolve_constraint_SSA(unsigned int id, basic_block bb, struct cgraph_node *cnode, bool use);
definitions resolve_fp_ssa(unsigned int fp_var, basic_block bb, struct cgraph_node *cnode);
GPUSet map_para_args_fp_call(unsigned int callee_rep, unsigned int caller_rep, basic_block bb);
//bool isDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
//bool isPDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
//bool isDomPDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode);
GPUSet get_global_info();
GPG createNewGPG(struct cgraph_node *cnode);
IndirectionList create_indirection_list(bool type, struct constraint_expr e);
std::tuple< IndirectionList, IndirectionList > createIndirectionList(constraint_t con);
bool filter_constraint(unsigned int id, basic_block bb, struct cgraph_node *cnode); // Filter this constraint if this function returns true
bool needsInlining(unsigned int caller, unsigned int callee);
bool needsInliningRecursion(unsigned int caller, unsigned int callee);
void collectUpwardExposedVersions(GPUSet gen, struct cgraph_node *cnode);
GPBSet get_bb_pred(basic_block bb, struct cgraph_node *cnode);
GPBSet get_bb_succ(basic_block bb, struct cgraph_node *cnode);
//std::pair< GPBSet, GPBSet> set_pred_succ(basic_block bb, struct cgraph_node *cnode);
bool analyze_callee_now(struct cgraph_node *callee);

//==========================================================================================================================================

GPG compute_gpus(basic_block bb, struct cgraph_node *cnode, GPG gpg);
bool is_present_in_worklist(unsigned int x);
void print_worklist();
bool single_entry_loop(edge_type e, struct cgraph_node *cnode);
GPG normalize_cfg(struct cgraph_node *cnode);
void perform_analysis(struct cgraph_node *cnode);
void print_constraint(constraint_t con);
void perform_analysis_d(struct cgraph_node *cnode);
GPUSet map_args_para_call(struct cgraph_node *callee, basic_block bb, struct cgraph_node * cnode);
void getCallSitesInfo();
GPG performCoalescingAlt(struct cgraph_node *cnode, GPG g);
void constructInitialGPG();
void constructGPGsForIndirectlyCalledFunctions();
void GPGConstruction();
void processSCC(unsigned int num);
void perform_analysis_again(struct cgraph_node *cnode);
void performAnalysis(struct cgraph_node *cnode);

bool checkTypeCompatibility(GPUSet p_gpus, GPUSet s_gpus);
bool isDerefPresent(GPUSet res);
bool isSubset(GPUSet p, GPUSet n);
bool typeCompatibility(set_tree_nodes nodes, GPUSet res);
bool typeCompatibilityOfGPUs(GPUSet gpus_p, GPUSet gpus_n);
set_tree_nodes sourceTypes(GPUSet res);

bool checkDataDependenceForCoalescing(GPUSet in, GPUSet gen);

void flowContextInsensitiveAnalysis();
void flowInsensitiveContextSensitiveAnalysis(struct cgraph_node *cnode);

void printStatistics(struct cgraph_node *cnode);
void printPointsToInformationStatistics(struct cgraph_node *cnode);
void printFIPointsToInformationStatistics(struct cgraph_node *cnode);
void printData();

void enhanceGPG(struct cgraph_node *cnode, GPUSet rin, GPUSet brin);

#endif  // AD GPG_H_

