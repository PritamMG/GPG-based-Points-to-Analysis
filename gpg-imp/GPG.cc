#include "GPG.h"
#include <stdlib.h>
#include <string.h>
#include "CoalescingAbstraction.h"
#include <vector>

using namespace std;

std::map< unsigned int, GPUSet > prospectiveProducerGPUs;
std::map< unsigned int, GPG > GPG_map;
std::map< unsigned int, GPG > Initial_GPG_map;
std::map< unsigned int, GPG > Call_GPG_map;
std::map< unsigned int, GPG > deltaGPG_map; // For Recursion
std::map< unsigned int, GPG > optimized_GPG_map;
std::map< unsigned int, GPG > partial_optimized_GPG_map;
std::map< unsigned int, unsigned int > SMOD;
std::map< unsigned int, unsigned int > SREF;
unsigned int SMCALLS = 0;
unsigned int SRCALLS = 0;
std::map< unsigned int, definitions > lhsUpwardsExposedDefinitions;
std::map< unsigned int, definitions > rhsUpwardsExposedDefinitions;
std::map< unsigned int, GPUSet > DownwardsExposedMayDefinitions;
std::map< unsigned int, GPUSet > DownwardsExposedMustDefinitions;
std::map< unsigned int, definitions > incompleteCallees;

std::map< unsigned int, call_site_info > CallerCallSite;

unsigned long sr_op, dead_op, emp_op, coal_op, tot_op;
struct timeval TValBefore, TValAfter, DTValBefore, DTValAfter, ETValBefore, ETValAfter, CTValBefore, CTValAfter, STValBefore, STValAfter;


std::map< unsigned int, std::map< unsigned int, bool > > LABEL_GPB;
std::map< unsigned int, std::map< unsigned int, unsigned int > > DFS_GPB;
std::map< unsigned int, std::map< unsigned int, unsigned int > > REV_DFS_GPB;
std::map< unsigned int, std::map< unsigned int, unsigned int > > BFS_GPB;
std::map< unsigned int, std::map< unsigned int, unsigned int > > REV_BFS_GPB;

std::map< unsigned int, unsigned int > enhanceCount;
std::map< unsigned int , GPUSet > UpwardsGPUs;
std::map< unsigned int , GPBSet > OriginalGPUs;

std::map< unsigned int, unsigned int > PROCESSING_COUNT;

std::map< unsigned int, bool > INC, OUTC;

std::map< unsigned int, GPUSet > BDEFS;

std::map< unsigned int, std::map< unsigned int, GPUSet > > BI;

GPBSet already_coalesced, coalesceG;

definitions DFP_TEMP;

GPUSet U_FI_GPUs, U_FIP_GPUs, U_GPUs, UFICS;

std::map< unsigned int, GPBSet > GPG::getPreds() const
{
	return preds;
}

void GPG::setPreds(std::map< unsigned int, GPBSet > p)
{
	preds = p;
}

std::map< unsigned int, GPBSet > GPG::getSuccs() const
{
	return succs;
}

void GPG::getSuccs(std::map< unsigned int, GPBSet > s)
{
	succs = s;
}

GPBSet GPG::getPrev(unsigned int n)
{
	return preds[n];
}

GPBSet GPG::getNext(unsigned int n)
{
	return succs[n];
}

void GPG::setPrev(unsigned int n, GPBSet s)
{
	preds[n] = s;
}

void GPG::setNext(unsigned int n, GPBSet s)
{
	succs[n] = s;
}

void GPG::addPrev(unsigned int n, unsigned int a)
{
	GPBSet temp = preds[n];
	temp.insert(a);
	preds[n] = temp;
}

void GPG::remPrev(unsigned int n, unsigned int a)
{
	GPBSet temp = preds[n];
	temp.erase(a);
	preds[n] = temp;
}

void GPG::addNext(unsigned int n, unsigned int a)
{
	GPBSet temp = succs[n];
	temp.insert(a);
	succs[n] = temp;
}

void GPG::remNext(unsigned int n, unsigned int a)
{
	GPBSet temp = succs[n];
	temp.erase(a);
	succs[n] = temp;
}

bool GPG::isTop()
{
	return top;
}

void GPG::setTop()
{
	top = true;
}

void GPG::resetTop()
{
	top = false;
}

edge_set GPG::getBackEdges()
{
	return back_edges;
}

void GPG::setBackEdges(edge_set e)
{
	back_edges = e;
}

GPG::GPG(unsigned int s, unsigned int e, GPBSet g, edge_set es, GPBSet c)
{
	entry = s;
	end = e;
	gpbs = g;
	back_edges = es;	
	call_sites = c;

	top = false;
}

GPBSet GPG::getCallSites()
{
	return call_sites;
}

void GPG::setCallSites(GPBSet c)
{
	call_sites = c;
}

// BB getter function
unsigned int GPG::getEntryGPB() const
{
	return entry;
}

unsigned int GPG::getExitGPB() const
{
	return end;
}

GPBSet GPG::getGPBs() const
{
	return gpbs;
}

void GPG::setGPBs(GPBSet g)
{
	gpbs = g;
}

std::map< unsigned int, GPG > GPG::getIntervals() const
{
	return intervals;
}

void GPG::setIntervals(std::map< unsigned int, GPG > g)
{
	intervals = g;
}

void GPG::addGPB(unsigned int gpb_id, GPBSet prev, GPBSet next, struct cgraph_node *cnode)
{
//	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();

	GPB gpb = gpb_map[gpb_id];
	
	GPB temp;
	
	gpbs.insert(gpb_id);

	#if 0
	fprintf(dump_file,"\nGPB %d BB %d\nPrev: ", gpb_id, gpb.getBBIndex());
	print_set_integers(prev);

	fprintf(dump_file,"\nNext: ");
	print_set_integers(next);
	#endif

	for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
	{
		addNext(*it, gpb_id);
	}

	for(GPBSet::iterator it = next.begin(); it != next.end(); it++)
	{
		addPrev(*it, gpb_id);
	}

	setPrev(gpb_id, prev);
	setNext(gpb_id, next);

	setGPBs(gpbs);

	#if 0
	fprintf(dump_file, "\nEnd addGPB\n");
	printGPG(cnode);
	#endif
}

bool GPG::checkDataDependence(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	if(gpb_id1 == gpb_id2)
	{
		return false;
	}

	GPB gpb1, gpb2;

	gpb1 = gpb_map[gpb_id1];
	gpb2 = gpb_map[gpb_id2];

	GPUSet gpus1, gpus2, gpus;

	gpus1 = gpb1.getGPUs(); 
	gpus2 = gpb2.getGPUs(); 

	if(areDataDependent(gpus1, gpus2))
	{
		#if 0
		fprintf(dump_file, "\nData Dependency between GPUs of %d and %d\n", gpb_id1, gpb_id2);
		fflush(dump_file);
		#endif

		return true;
	}

	return false;
}

#if 0
void GPG::CoalescingGPBs(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	fprintf(dump_file, "\nCoalesce %d and %d\n", gpb_id1, gpb_id2);
	fflush(dump_file);

	fprintf(dump_file, "\nGPG before Coalescing\n");
	printGPG(cnode);

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	if(gpb_id1 == gpb_id2)
	{
		return;
	}

	fprintf(dump_file, "\nCoalesce %d and %d\n", gpb_id1, gpb_id2);
	fflush(dump_file);

	GPB gpb1, gpb2;

	gpb1 = gpb_map[caller_rep][gpb_id1];
	gpb2 = gpb_map[caller_rep][gpb_id2];

	fprintf(dump_file, "\nGot %d and %d\n", gpb_id1, gpb_id2);
	fflush(dump_file);

	GPUSet gpus1, gpus2, gpus, may_gpus1, may_gpus2, may_gpus, rout1, rout2;

	gpus1 = gpb1.getGPUs(); 
	gpus2 = gpb2.getGPUs(); 

	fprintf(dump_file, "\nGot GPUs of %d and %d\n", gpb_id1, gpb_id2);
	fflush(dump_file);

	rout1 = ROUT[caller_rep][gpb_id1];
	rout2 = ROUT[caller_rep][gpb_id2];

	fprintf(dump_file, "\nGot ROUT of %d and %d\n", gpb_id1, gpb_id2);
	fflush(dump_file);

	may_gpus1 = gpb1.getMayGPUs(); 
	may_gpus2 = gpb2.getMayGPUs(); 

	fprintf(dump_file, "\nGot May GPUs of %d and %d\n", gpb_id1, gpb_id2);
	fflush(dump_file);

	fprintf(dump_file, "\nUnion of May GPUs\n");
	fflush(dump_file);

	may_gpus = may_gpus1;
	may_gpus.insert(may_gpus2.begin(), may_gpus2.end());

	fprintf(dump_file, "\nHey There\n");
	fflush(dump_file);

	GPB gpb;

	unsigned int entry, exit;
	entry = getEntryGPB();
	exit = getExitGPB();

	fprintf(dump_file, "\nEntry %d, Exit %d\n", entry, exit);
	fflush(dump_file);

	gpus = gpus1;
	gpus.insert(gpus2.begin(), gpus2.end());

	gpu_id_type cgpu;

	for(GPUSet::iterator it = gpus1.begin(); it != gpus1.end(); it++)
	{
		cgpu = getCopyGPU(get<0>(*it));

		if(rout2.find(cgpu) != rout2.end())
		{
			may_gpus.insert(*it);
		}
	}
	
	for(GPUSet::iterator it = gpus2.begin(); it != gpus2.end(); it++)
	{
		cgpu = getCopyGPU(get<0>(*it));

		if(rout1.find(cgpu) != rout1.end())
		{
			may_gpus.insert(*it);
		}
	}

	GPUSet og1, og2;

	og1 = gpb1.getOrigGPUs();
	og2 = gpb2.getOrigGPUs();

	og1.insert(og2.begin(), og2.end());

	gpb.setId(((function_info *)(cnode->aux))->GPB_count++);
	unsigned int z = ((function_info *)(cnode->aux))->GPB_count-1;

	gpb.replaceGPBs(gpb_id1, gpb_id2, cnode);

	gpb.setBBIndex(gpb1.getBBIndex());

	gpb.setGPUs(gpus);
//	gpb.setOrigGPUs(og1);
	gpb.setMayGPUs(may_gpus);

	gpb_map[caller_rep][z] = gpb;

	GPBSet gpbs = getGPBs();

	gpbs.erase(gpb_id1);
	gpbs.erase(gpb_id2);

	gpbs.insert(z);

	fprintf(dump_file, "\nOld Entry %d and Exit %d\n", entry, exit);
	fprintf(dump_file, "\ngpb_id1 %d, gpb_id2 %d\n", gpb_id1, gpb_id2);

	if(gpb_id1 == entry)
	{
		fprintf(dump_file, "\nSetting new Entry %d\n", z);
		setEntryGPB(z);
	}

	if(gpb_id2 == exit)
	{
		fprintf(dump_file, "\nSetting new Exit %d\n", z);
		setExitGPB(z);
	}

	setGPBs(gpbs);

	fprintf(dump_file, "\nGPG after Coalescing\n");
	printGPG(cnode);
}
#endif	

void GPG::coalesceGPBs(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	if(gpb_id1 == gpb_id2)
	{
		return;
	}

//	fprintf(dump_file, "\nInside coalesceGPBs()\n");

	GPB gpb1, gpb2;

	gpb1 = gpb_map[gpb_id1];
	gpb2 = gpb_map[gpb_id2];

	bool ordered_call_block;

	GPUSet gpus1, gpus2, gpus;

	gpus1 = gpb1.getGPUs(); 
	gpus2 = gpb2.getGPUs(); 

	if(gpb1.isSymGPB() || gpb2.isSymGPB())
	{
		return;
	}

	if((isDerefPresent(gpus1) || isDerefPresent(gpus2)) && checkDataDependenceForCoalescing(gpus1, gpus2))
//	if(areDataDependent(gpus1, gpus2))
	{
//		fprintf(dump_file, "\nData Dependency between GPUs of %d and %d\n", gpb_id1, gpb_id2);
//		fflush(dump_file);

		return;
	}

	#if 0
	fprintf(dump_file, "\nCoalesce %d and %d\n", gpb_id1, gpb_id2);
	fflush(dump_file);
	printGPG(cnode);
	fprintf(dump_file, "\nGPG Before Coalescing GPBs\n");
	#endif

	GPB gpb;

	unsigned int entry, exit;
	entry = getEntryGPB();
	exit = getExitGPB();

	gpus = gpus1;
	gpus.insert(gpus2.begin(), gpus2.end());

	gpb.setId(GPB_count++);
	unsigned int z = GPB_count-1;

	stmt_info_type key_t, key;
	GPBSet sset, temp_sset;

	for(GPUSet::iterator rit = gpus1.begin(); rit != gpus1.end(); rit++)
	{
		key_t = std::make_tuple(caller_rep, gpb_id1, *rit); 

		temp_sset = stmt_id_info[key_t];

//		stmt_id_info.erase(key_t);

		key = std::make_tuple(caller_rep, z, *rit);

		sset = stmt_id_info[key];

		sset.insert(temp_sset.begin(), temp_sset.end());

		stmt_id_info[key] = sset;
	}

	for(GPUSet::iterator rit = gpus2.begin(); rit != gpus2.end(); rit++)
	{
		key_t = std::make_tuple(caller_rep, gpb_id2, *rit); 

		temp_sset = stmt_id_info[key_t];

//		stmt_id_info.erase(key_t);

		key = std::make_tuple(caller_rep, z, *rit);

		sset = stmt_id_info[key];

		sset.insert(temp_sset.begin(), temp_sset.end());

		stmt_id_info[key] = sset;
	}

	replaceGPBs(z, gpb_id1, gpb_id2, cnode);

	gpb.setBBIndex(gpb1.getBBIndex());

	gpb.setGPUs(gpus);

	gpb_map[z] = gpb;

	GPBSet gpbs = getGPBs();

	gpbs.erase(gpb_id1);
	gpbs.erase(gpb_id2);

	gpbs.insert(z);

	RIN[z] = RIN[gpb_id1];
	BRIN[z] = BRIN[gpb_id1];

	ROUT[z] = ROUT[gpb_id2];
	BROUT[z] = BROUT[gpb_id2];

	#if 0
	fprintf(dump_file, "\nOld Entry %d and Exit %d\n", entry, exit);
	fprintf(dump_file, "\ngpb_id1 %d, gpb_id2 %d\n", gpb_id1, gpb_id2);
	#endif

	if(gpb_id1 == entry)
	{
//		fprintf(dump_file, "\nSetting new Entry %d\n", z);

		setEntryGPB(z);
	}

	if(gpb_id2 == exit)
	{
//		fprintf(dump_file, "\nSetting new Exit %d\n", z);

		setExitGPB(z);
	}

	setGPBs(gpbs);

	#if 0
	fprintf(dump_file, "\nGPG after Coalescing in coalesceGPBs\n");
	printGPG(cnode);
	#endif
}

void GPG::coalesceAdjGPBs(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	if(gpb_id1 == gpb_id2)
	{
		return;
	}

	GPB gpb1, gpb2;

	gpb1 = gpb_map[gpb_id1];
	gpb2 = gpb_map[gpb_id2];

	bool ordered_call_block;

	GPUSet gpus1, gpus2, gpus;

	gpus1 = gpb1.getGPUs(); 
	gpus2 = gpb2.getGPUs(); 

//	fprintf(dump_file, "\nCoalesce Adj GPBs %d and %d\n", gpb_id1, gpb_id2);
//	fflush(dump_file);
//	printGPG(cnode);
//	fprintf(dump_file, "\nGPG Before Coalescing GPBs\n");

	GPB gpb;

	unsigned int entry, exit;
	entry = getEntryGPB();
	exit = getExitGPB();

	gpus = gpus1;
	gpus.insert(gpus2.begin(), gpus2.end());

	GPUSet og1, og2;

	gpb.setId(GPB_count++);
	unsigned int z = GPB_count-1;

	replaceAdjGPBs(z, gpb_id1, gpb_id2, cnode);

	gpb.setBBIndex(gpb1.getBBIndex());

	gpb.setGPUs(gpus);

	gpb_map[z] = gpb;

	GPBSet gpbs = getGPBs();

	gpbs.erase(gpb_id1);
	gpbs.erase(gpb_id2);

	gpbs.insert(z);

//	fprintf(dump_file, "\nOld Entry %d and Exit %d\n", entry, exit);
//	fprintf(dump_file, "\ngpb_id1 %d, gpb_id2 %d\n", gpb_id1, gpb_id2);

	if(gpb_id1 == entry || gpb_id2 == entry)
	{
//		fprintf(dump_file, "\nSetting new Entry %d\n", z);
		setEntryGPB(z);
	}

	if(gpb_id2 == exit || gpb_id2 == exit)
	{
//		fprintf(dump_file, "\nSetting new Exit %d\n", z);
		setExitGPB(z);
	}

	setGPBs(gpbs);

//	fprintf(dump_file, "\nGPG after Coalescing in coalesceGPBs\n");
//	printGPG(cnode);
}

GPUSet GPG::getPrevGPUs(struct cgraph_node *cnode, unsigned int gpb_id)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet preds = getPrev(gpb_id);

	GPUSet res, temp;
	GPB gpb;
	bool start = true;

	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		GPUSet temp_s;

		gpb = gpb_map[*it];

		temp = gpb.getGPUs();

		if(start)
		{
			start = false;
			res = temp;
		}
		else
		{
			set_intersection(res.begin(), res.end(), temp.begin(), temp.end(), inserter(temp_s, temp_s.end()));

			res = temp_s;
		}
	}

	return res;
}

void GPG::commonGPUElimination(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();
	GPB gpb;

	GPUSet in_gpus, gpus, fin_gpus;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		GPUSet int_set, diff_set;

		gpb = gpb_map[*it];

		gpus = gpb.getGPUs();

		in_gpus = getPrevGPUs(cnode, *it);

		set_intersection(gpus.begin(), gpus.end(), in_gpus.begin(), in_gpus.end(), inserter(int_set, int_set.end()));
		
		set_difference(gpus.begin(), gpus.end(), int_set.begin(), int_set.end(), inserter(diff_set, diff_set.end()));

		gpb.setGPUs(diff_set);

		gpb_map[*it] = gpb;
	}
}

void GPG::deadGPUElimination(GPUSet queued, struct cgraph_node *cnode)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	if(isIdentity())
	{
		return;
	}

	GPBSet gpbs = getGPBs();

	if(gpbs.size() == 1)
	{
		#if PROFILING
		RETURN_VOID();
		#else
		return;
		#endif
	}

	unsigned int exit = getExitGPB();
	GPB exit_gpb = gpb_map[exit]; 

	GPUSet gpus, gpusb;

	gpus = ROUT[exit];
	gpusb = BROUT[exit];

	gpus.insert(queued.begin(), queued.end());
	gpus.insert(gpusb.begin(), gpusb.end());

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nROUT for dead GPU Elimination\n");
	printSetOfGPUs(gpus);
	#endif

	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		GPUSet i_gpus, rem_gpus, fin_gpus;

		gpb = gpb_map[*it];

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nConsidering GPB %d for dead code elimination\n", *it);
//		gpb.printGPB(cnode);
		#endif

		if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock())
		{
			continue;
		}

		i_gpus = gpb.getGPUs();

		for(GPUSet::iterator git = i_gpus.begin(); git != i_gpus.end(); git++)
		{
//			fprintf(dump_file, "\nConsidering GPU for dead code elimination\n");
//			print_GPU(*git);

			if(gpus.find(*git) == gpus.end())
			{
				rem_gpus.insert(*git);
			}
			#if 0 //PRINT_DATA
			else
			{
				fprintf(dump_file, "\nCannot be eliminated\n");
				print_GPU(*git);
			}
			#endif
		}	

		set_difference(i_gpus.begin(), i_gpus.end(), rem_gpus.begin(), rem_gpus.end(), inserter(fin_gpus, fin_gpus.end()));

		gpb.setGPUs(fin_gpus);

		gpb_map[*it] = gpb;
	}

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

void GPG::eliminateGPB(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;
	unsigned int entry;
	entry = getEntryGPB();

	if(entry == gpb_id)
	{
		GPBSet gpbs;
		setGPBs(gpbs);
		setTop();

		return;
	}

	GPBSet gpbs = getGPBs();
		
	removeGPB(gpb_id, cnode);

	gpbs.erase(gpb_id);

	setGPBs(gpbs);
}

void GPG::eliminateEmptyGPB(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	#if 0
	fprintf(dump_file,"\nBefore Elimination of Empty GPB %d\n", gpb_id);
	fflush(dump_file);
	printGPG(cnode);
	fflush(dump_file);

	fprintf(dump_file, "\nEliminating GPB %d with entry = %d, exit = %d\n", gpb_id, getEntryGPB(), getExitGPB());
	fflush(dump_file);
	#endif

	removeEmptyGPB(gpb_id, cnode);

	GPBSet gpbs = getGPBs();
	
	gpbs.erase(gpb_id);

	setGPBs(gpbs);
}

GPBSet loop_set;

void GPG::forwardReachable(unsigned int gpb_id1, unsigned int gpb_id2, unsigned int exit_id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPB gpb1, gpb2, exit;
	edge_set backedges = getBackEdges();

	edge_type e = make_pair(gpb_id1, gpb_id2);

	if(backedges.find(e) == backedges.end())
	{
		if(exit_id == gpb_id2)
		{
			loop_set.insert(gpb_id2);

			return;
		}
		else
		{
			GPBSet succs = getNext(gpb_id2);

			for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
			{
				loop_set.insert(gpb_id2);

				forwardReachable(gpb_id2, *it, exit_id, cnode);
			}
		}
	}
}

GPBSet GPG::loop(edge_type e, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();
	edge_set backedges = getBackEdges();

	loop_set.clear();

	GPBSet res, succs;

	GPB src, dest;
	unsigned int src_id, dest_id;
	src_id = get<0>(e);
	dest_id = get<1>(e);

	succs = getNext(src_id);

	loop_set.insert(src_id);

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		forwardReachable(src_id, *it, dest_id, cnode);
	}

	for(GPBSet::iterator it = loop_set.begin(); it != loop_set.end(); it++)
	{
		res.insert(*it);
	}	

	return res;
}

GPBSet GPG::frontiers(edge_type e, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet res, gpbs_in_loop;

	gpbs_in_loop = loop(e, cnode);

	GPBSet succs;
	GPB gpb;

	for(GPBSet::iterator it = gpbs_in_loop.begin(); it != gpbs_in_loop.end(); it++)
	{
		succs = getNext(*it);

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			if(gpbs_in_loop.find(*sit) == gpbs_in_loop.end())
			{
				res.insert(*sit);
			}
		}
	}

	return res;
}

void GPG::regularizedLoop(edge_type e, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet front_gpbs = frontiers(e, cnode);
	GPB src, f;
	
	unsigned int src_id = get<0>(e);

	for(GPBSet::iterator it = front_gpbs.begin(); it != front_gpbs.end(); it++)
	{
		addNext(src_id, *it);
		addPrev(*it, src_id);
	}
}

void GPG::regularizedAllLoops(struct cgraph_node *cnode)
{
	edge_set backedges = getBackEdges();

	for(edge_set::iterator it  = backedges.begin(); it != backedges.end(); it++)
	{
		regularizedLoop(*it, cnode);
	}
}

bool GPG::operator==(const GPG &g) const
{
	if(getEntryGPB() == g.getEntryGPB())
	{
		if(getExitGPB() == g.getExitGPB())
		{
			if(getGPBs() == g.getGPBs())
			{
				if(getPreds() == g.getPreds())
				{
					if(getSuccs() == g.getSuccs())
					{
						return true;
					}
				}
			}
		}
	}

	return false;
}

unsigned int GPG::returnNumberOfReducedGPUs(struct cgraph_node *cnode)
{
	if(isTop())
	{
		return 0;
	}

	GPBSet gpbs = getGPBs();
	GPB gpb;
	GPUSet gpus;
	unsigned int res = 0;
	GPUSet fin;

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		gpus = gpb.getGPUs();

		fin.insert(gpus.begin(), gpus.end());
		
//		res += gpus.size();
	}

	return fin.size();

//	return res;
}

unsigned int GPG::returnNumberOfFIGPUs(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	
	unsigned int res = 0;
	GPUSet temp;

	std::map< unsigned int, GPUSet > fip = FIP[cnode_num];
	std::map< unsigned int, GPUSet > finp = FINP[cnode_num];

	for(std::map< unsigned int, GPUSet >::iterator it = fip.begin(); it != fip.end(); it++)
	{
		temp = it->second;

		res = res + (temp.size());
	}

	for(std::map< unsigned int, GPUSet >::iterator it = finp.begin(); it != finp.end(); it++)
	{
		temp = it->second;

		res = res + (temp.size());
	}

	return res;
}

GPUSet GPG::returnFIGPUs(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	
	GPUSet res;
	GPUSet temp;

	std::map< unsigned int, GPUSet > fip = FIP[cnode_num];
	std::map< unsigned int, GPUSet > finp = FINP[cnode_num];

	for(std::map< unsigned int, GPUSet >::iterator it = fip.begin(); it != fip.end(); it++)
	{
		temp = it->second;

		res.insert(temp.begin(), temp.end());
	}

	for(std::map< unsigned int, GPUSet >::iterator it = finp.begin(); it != finp.end(); it++)
	{
		temp = it->second;

		res.insert(temp.begin(), temp.end());
	}

	return res;
}

unsigned int GPG::returnNumberOfScalarGPUs(struct cgraph_node *cnode, bool orig)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	
	GPBSet gpbs = getGPBs();

	GPB gpb;
	GPUSet res, gpus;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];		

		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

		for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
		{
			if(isStackGPU(*git))
			{
				res.insert(*git);
			}
		}
	}

	return res.size();
}

unsigned int GPG::returnNumberOfHeapGPUs(struct cgraph_node *cnode, bool orig)
{
	unsigned int tot;
	unsigned stot;

	if(orig)
	{
		tot = returnNumberOfOrigGPUs(cnode);
	}
	else
	{
		tot = returnNumberOfReducedGPUs(cnode);
	}

	stot = returnNumberOfScalarGPUs(cnode, orig);

	return (tot-stot);
}

GPUSet GPG::returnGPUs(struct cgraph_node *cnode, bool orig)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs;
	GPB gpb;
	GPUSet res, gpus;

	gpbs = getGPBs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];
	
		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

		res.insert(gpus.begin(), gpus.end());
	}

	return res;
}

GPUSet GPG::returnNonScalarGPUs(struct cgraph_node *cnode, bool orig)
{
	GPUSet res, gpus;

	if(isTop() || isIdentityGPG(cnode, orig))
	{
		return res;
	}

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs;
	GPB gpb;

	gpbs = getGPBs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];
	
		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

		for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
		{
			if(!isStackGPU(*git))
			{
				res.insert(*git);	
			}	
		}
	}
	
	return res;
}

GPUSet GPG::returnAllGPUs(struct cgraph_node *cnode, bool orig)
{
	GPUSet res, gpus;

	if(isTop() || isIdentityGPG(cnode, orig))
	{
		return res;
	}

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs;
	GPB gpb;

	gpbs = getGPBs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];
	
		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

		res.insert(gpus.begin(), gpus.end());
	}
	
	return res;
}

GPUSet GPG::returnScalarGPUs(struct cgraph_node *cnode, bool orig)
{
	GPUSet res, gpus;

	if(isTop() || isIdentityGPG(cnode, orig))
	{
		return res;
	}

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs;
	GPB gpb;

	gpbs = getGPBs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];
	
		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

		for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
		{
			if(isStackGPU(*git))
			{
				res.insert(*git);	
			}	
		}
	}
	
	return res;
}

GPUSet GPG::returnGPUsWithUpwardsExposedVariables(struct cgraph_node *cnode, bool orig)
{
	GPUSet res, gpus;
	IndirectionList list1, list2;

	if(isTop() || isIdentityGPG(cnode, orig))
	{
		return res;
	}

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs;
	GPB gpb;

	gpbs = getGPBs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];
	
		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

		for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
		{
			list1 = getNode(get<0>(*git)).getList();
			list2 = getNode(get<1>(*git)).getList();

			if(list1.Length() > 1 || list2.Length() > 0)
			{
				res.insert(*git);
			}
		}
	}
	
	return res;
}

unsigned int GPG::returnNumberOfOrigGPUs(struct cgraph_node *cnode)
{
	GPBSet gpbs = getGPBs();
	GPB gpb;
	GPUSet gpus;
	unsigned int res = 0;
	GPUSet fin;

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		gpus = gpb.getOrigGPUs();
		
		fin.insert(gpus.begin(), gpus.end());
		
//		res += gpus.size();
	}

	return fin.size();

//	return res;
}

void GPG::printGPG(struct cgraph_node *cnode)
{
	if(isTop())
	{
		fprintf(dump_file, "\nTop GPG for Function %s\n", cgraph_node_name(cnode));
		return;
	}
	
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();
	GPB temp;

	unsigned int gpb_count;
	unsigned int edge_count;
	double ratio1, ratio2;

	gpb_count = gpbs.size();
	edge_count = returnNumberOfControlFlowEdges(cnode);
	
	if(edge_count == 0)
	{
		ratio1 = -1.0;
		ratio2 = -1.0;
	}
	else if(gpb_count == 0)
	{
		ratio1 = 0.0;
		ratio2 = 0.0;
	}
	else
	{
		ratio1 = (edge_count * 1.0)/gpb_count;
		ratio2 = (edge_count * 1.0)/(gpb_count * gpb_count);
	}

	unsigned int start, exit;
	start = getEntryGPB();
	exit = getExitGPB();

	fprintf(dump_file, "\nGPG for Function %s\n", cgraph_node_name(cnode));
	fprintf(dump_file, "\nEntry GPB %u\n", start);
	fprintf(dump_file, "\nExit GPB %u\n", exit);
//	fprintf(dump_file, "\nTotal Number of GPBs: %d, Number of Empty GPBs (Orig): %d, Number of Empty GPBs (Reduced): %d, Number of Call Blocks: %d, Number of Indirect Call Blocks: %d, Number of Reduced GPUs: %d, Number of Orig GPUs: %d, Number of Scalar GPUs: %d, Number of Structure GPUs: %d, Number of Flow Insensitive GPUs: %d,  Number of Control Flow Edges: %d, Ratio1: %f, Ratio2: %f\n", gpb_count, returnNumberOfEmptyGPBsFromGPG(caller_rep, false), returnNumberOfEmptyGPBsFromGPG(caller_rep, false), returnNumberOfDirectCallBlocks(cnode), returnNumberOfIndirectCallBlocks(cnode), returnNumberOfReducedGPUs(cnode), returnNumberOfOrigGPUs(cnode), returnNumberOfScalarGPUs(cnode, false), returnNumberOfHeapGPUs(cnode, false), returnNumberOfFIGPUs(cnode), edge_count, ratio1, ratio2);

	fprintf(dump_file, "\nTotal Number of GPBs: %d, Number of Empty GPBs: %d, Number of Call Blocks: %d, Number of Indirect Call Blocks: %d, Number of GPUs: %d, Number of Scalar GPUs: %d, Number of Non-Scalar GPUs: %d, Number of Flow Insensitive GPUs: %d,  Number of Control Flow Edges: %d, Ratio1: %f, Ratio2: %f\n", gpb_count, returnNumberOfEmptyGPBsFromGPG(caller_rep, false), returnNumberOfDirectCallBlocks(cnode), returnNumberOfIndirectCallBlocks(cnode), returnNumberOfReducedGPUs(cnode), returnNumberOfScalarGPUs(cnode, false), returnNumberOfHeapGPUs(cnode, false), returnNumberOfFIGPUs(cnode), edge_count, ratio1, ratio2);

	GPBSet prev, next;
		
	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		temp = gpb_map[*it];
		prev = getPrev(*it);
		next = getNext(*it);

		fprintf(dump_file, "\nGPB %u for BB %d in CFG\n", *it, temp.getBBIndex());
		fprintf(dump_file, "\nPreds (%d): ", prev.size());
		print_set_integers(prev);
		fprintf(dump_file, "\nSuccs (%d): ", next.size());
		print_set_integers(next);
		temp.printGPB(cnode);
	}

	#if 1
	fflush(dump_file);
	fprintf(dump_file, "\nFI GPUs\n");
	printSetOfGPUs(returnFIGPUs(cnode));
	fprintf(dump_file, "\nFI GPUs Over\n");
	fflush(dump_file);
	fprintf(dump_file, "\n\n");
	#endif
}

void GPG::printInitialGPG(struct cgraph_node *cnode)
{
	if(isTop())
	{
		fprintf(dump_file, "\nTop GPG\n");
	}
	
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();
	GPB temp;

	unsigned int gpb_count;
	unsigned int edge_count;
	double ratio1, ratio2;

	gpb_count = gpbs.size();
	edge_count = returnNumberOfControlFlowEdges(cnode);
	
	if(edge_count == 0)
	{
		ratio1 = -1.0;
		ratio2 = -1.0;
	}
	else if(gpb_count == 0)
	{
		ratio1 = 0.0;
		ratio2 = 0.0;
	}
	else
	{
		ratio1 = (edge_count * 1.0)/gpb_count;
		ratio2 = (edge_count * 1.0)/(gpb_count * gpb_count);
	}

	unsigned int start, exit;
	start = getEntryGPB();
	exit = getExitGPB();

	fprintf(dump_file, "\nGPG for Function %s\n", cgraph_node_name(cnode));
	fprintf(dump_file, "\nEntry GPB %d\n", start);
	fprintf(dump_file, "\nExit GPB %d\n", exit);
	fprintf(dump_file, "\nTotal Number of GPBs: %d, Number of Empty GPBs (Orig): %d, Number of Empty GPBs (Reduced): %d, Number of Call Blocks: %d, Number of Indirect Call Blocks: %d, Number of Reduced GPUs: %d, Number of Orig GPUs: %d, Number of Scalar GPUs: %d, Number of Structure GPUs: %d, Number of Flow Insensitive GPUs: %d, Number of Control Flow Edges: %d, Ratio1: %f, Ratio2: %f\n", gpb_count, returnNumberOfEmptyGPBsFromGPG(caller_rep, true), returnNumberOfEmptyGPBsFromGPG(caller_rep, true), returnNumberOfDirectCallBlocks(cnode), returnNumberOfIndirectCallBlocks(cnode), returnNumberOfReducedGPUs(cnode), returnNumberOfOrigGPUs(cnode), returnNumberOfScalarGPUs(cnode, true), returnNumberOfHeapGPUs(cnode, true), returnNumberOfFIGPUs(cnode), edge_count, ratio1, ratio2);
	
	GPBSet prev, next;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		prev = getPrev(*it);
		next = getNext(*it);

		temp = gpb_map[*it];
		fprintf(dump_file, "\nGPB %d with BB %d\n", *it, temp.getBBIndex());

		fprintf(dump_file, "\nPreds (%d): ", prev.size());
		print_set_integers(prev);
		fprintf(dump_file, "\nSuccs (%d): ", next.size());
		print_set_integers(next);
		temp.printInitialGPB(cnode);
	}

	fprintf(dump_file, "\nFI GPUs\n");
	printSetOfGPUs(returnFIGPUs(cnode));
	fprintf(dump_file, "\n\n");
}

bool GPG::containsCycle(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();

	GPBSet preds, succs, temp;

	std::map< unsigned int, std::tuple< GPBSet, GPBSet > > in_out_map; // bb_block = 0, in = 1, out = 2

	GPB bb, bt;

	list< unsigned int > worklist;

	unsigned int start_node;
	start_node = getEntryGPB();

	worklist.push_back(start_node);

	unsigned int node;

	while(!worklist.empty())
	{
		GPBSet in, out_p, out_n;

		node = worklist.front();

		bb = gpb_map[node];

		worklist.pop_front();

		out_p = get<1>(in_out_map[node]);

		preds = getPrev(node);

		for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
		{
			temp = get<1>(in_out_map[*it]);

			in.insert(temp.begin(), temp.end());
		}

		in_out_map[node] = std::make_tuple(in, out_p);

		if(in.find(node) != in.end())
		{
			return true;
		}

		out_n.insert(in.begin(), in.end());

		out_n.insert(node);

		if(!(out_p == out_n))
		{
			in_out_map[node] = std::make_tuple(in, out_n);

			succs = getNext(node);

			for(set< unsigned int >::iterator sit = succs.begin(); sit != succs.end(); sit++)
			{
				worklist.push_back(*sit);
			}	
		}
	}
	
	return false;
}

GPBSet visited_list1, bb_reachable_from_start1, bb_reachable_from_exit1, all_succ_list1;

void GPG::reachability_start_node_recursive(unsigned int node, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet succs;

	succs = getNext(node);

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		if(visited_list1.find(*it) == visited_list1.end())
		{
			visited_list1.insert(*it);

			bb_reachable_from_start1.erase(*it);

			reachability_start_node_recursive(*it, cnode);
		}	
	}
}

void GPG::reachability_exit_node_recursive(unsigned int node, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet preds;

	preds = getPrev(node);

	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		if(visited_list1.find(*it) == visited_list1.end())
		{
			visited_list1.insert(*it);

			bb_reachable_from_exit1.erase(*it);

			reachability_exit_node_recursive(*it, cnode);
		}	
	}
}

unsigned int unreachableGPUs = 0;

void GPG::reachability(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPB block;
	GPUSet gpus;

	unsigned int exit_node = getExitGPB();
	unsigned int start_node = getEntryGPB();

	visited_list1.clear();

	bb_reachable_from_start1 = getGPBs();

	if(bb_reachable_from_start1.size() == 1)
	{
		return;
	}

	bb_reachable_from_start1.erase(start_node);
	reachability_start_node_recursive(start_node, cnode);

	if(bb_reachable_from_start1.size() != 0)
	{
		#if 1
//		fprintf(dump_file,"\nGPBs not reachable from start node are:\n");
//		print_set_integers(bb_reachable_from_start1);

		for(GPBSet::iterator it = bb_reachable_from_start1.begin(); it != bb_reachable_from_start1.end(); it++)
		{
			block = gpb_map[*it];

//			fprintf(dump_file,"\nCaller GPG Block Number %d - Callee CFG Block Number %d\t", *it, block.getBBIndex());

			bool to_be_eliminated = true;

			if(block.isCallBlock() || block.isSymGPB())
			{
				unsigned int callee_n = block.getCallee();

				GPG g = optimized_GPG_map[callee_n];
				gpus = g.returnGPUs(func_numbering[callee_n], false);
				
			}
			else if(block.isIndirectCallBlock())
			{
			}
			else
			{
				gpus = block.getGPUs();
			}

			for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
			{
				if(!isPointstoEdge(*it))
				{
					unreachableGPUs++;

					to_be_eliminated = false;

					break;
				}
			}
	
			if(to_be_eliminated)
			{
				eliminateGPB(*it, cnode);
			}
		}
		#endif
	}

	if(exit_node == 0)
	{
		return;
	}

	visited_list1.clear();

	bb_reachable_from_exit1 = getGPBs();

	bb_reachable_from_exit1.erase(exit_node);
	reachability_exit_node_recursive(exit_node, cnode);

	if(bb_reachable_from_exit1.size() != 0)
	{
		#if 1
//		fprintf(dump_file,"\nGPBs from which exit node is not reachable are:\n");

		for(set< unsigned int >::iterator it = bb_reachable_from_exit1.begin(); it != bb_reachable_from_exit1.end(); it++)
		{
			block = gpb_map[*it];

//			fprintf(dump_file,"\nCaller GPG Block Number %d - Callee CFG Block Number %d\t", *it, block.getBBIndex());

			bool to_be_eliminated = true;

			if(block.isCallBlock() || block.isSymGPB())
			{
				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nCall Block\n");
				fflush(dump_file);
				#endif

			
				unsigned int callee_n = block.getCallee();

				GPG g = optimized_GPG_map[callee_n];
				gpus = g.returnGPUs(func_numbering[callee_n], false);
				
			}
			else if(block.isIndirectCallBlock())
			{
			}
			else
			{
				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nNon-Call Block\n");
				fflush(dump_file);
				#endif

				gpus = block.getGPUs();
			}

			for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
			{
				if(!isPointstoEdge(*it))
				{
					unreachableGPUs++;

					to_be_eliminated = false;

					break;
				}
			}

			if(to_be_eliminated)
			{
				eliminateGPB(*it, cnode);
			}
		}
		#endif
	}

	GPBSet gpbs = getGPBs();

	if(gpbs.empty())
	{
		setTop();
		setEntryGPB(0);
		setExitGPB(0);
	}

	start_node = getEntryGPB();
	exit_node = getExitGPB();

	if(gpbs.find(exit_node) == gpbs.end())
	{
		setExitGPB(start_node);
	}
}

void GPG::succ_trans(unsigned int node, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet succs;

	succs = getNext(node);

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		if(visited_list1.find(*it) == visited_list1.end())
		{
			visited_list1.insert(*it);

			all_succ_list1.insert(*it);

			succ_trans(*it, cnode);
		}
	}
}

bool GPG::maxNodeCount()
{
	GPBSet gpbs = getGPBs();

	if(gpbs.size() > 2000)
	{
		return false;
	}

	return true;
}

bool GPG::isIdentityGPG(struct cgraph_node *cnode, bool orig)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();
	GPUSet gpus;
	GPB gpb;
	GPB gpb_s, gpb_e;

	if(gpbs.size() == 1)
	{
		gpb = gpb_map[*(gpbs.begin())];

		if(orig)
		{
			if(gpb.isInitialEmpty())
			{
				return true;
			}
		}
		else
		{		
			if(gpb.isEmpty())
			{
				return true;
			}
		}
	}	
	if(gpbs.size() == 2)
	{
		for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
		{
			gpb = gpb_map[*it];

			if(orig)
			{
				if(!gpb.isInitialEmpty())
				{
					return false;
				}
			}
			else
			{		
				if(!gpb.isEmpty())
				{
					return false;
				}
			}
		}

		return true;
	}

	return false;
}

bool GPG::isIdentity()
{
	GPBSet gpbs = getGPBs();

	if(gpbs.empty()) // || gpbs.size() == 1)
	{
		return true;
	}

	return false;
}

bool GPG::isFreeOfCallGPBs(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();

	GPB bb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		bb = gpb_map[*it];

		#if INTDIR
		if(bb.isCallBlock() || bb.isSymGPB() || bb.isIndirectCallBlock() || bb.isInterval() || bb.isIntervalDirect())
		#else
		if(bb.isCallBlock() || bb.isSymGPB() || bb.isIndirectCallBlock() || bb.isInterval())
		#endif
		{
			return true;
		}
	}

	return false;
}

set< unsigned int > GPG::getCallBlocksForGPG(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	set< unsigned int > res;

	if(isIdentity())
	{
		return res;
	}

	GPBSet bb_set;

	bb_set = getGPBs();
	GPB bb;

	for(GPBSet::iterator sit = bb_set.begin(); sit != bb_set.end(); sit++)
	{
		bb = gpb_map[*sit];

		if(bb.isCallBlock())
		{
			res.insert(*sit);
		}
	}

	return res;
}

bool GPG::isReachableFromStartNode(unsigned int node, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	#if 0
	fprintf(dump_file,"\nChecking Reachability from start node %d\n", node);
	fflush(dump_file);
	#endif
	
	unsigned int start_node = getEntryGPB();

	if(node == start_node)
	{
		return true;
	}

	GPBSet succs = getNext(start_node);

	#if 0
	fprintf(dump_file,"\nSuccessors\n");
	fflush(dump_file);
	#endif

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		#if 0
		fprintf(dump_file, "\nSucc %d\n", *it);
		fflush(dump_file);
		#endif

		if(node == *it)
		{
			#if 0
			fprintf(dump_file, "\nNode %d Found\n", *it);
			fflush(dump_file);
			#endif

			return true;
		}

		if(visited_list1.find(*it) == visited_list1.end())
		{
			#if 0
			fprintf(dump_file, "\nCheck suucs of %d\n", *it);
			fflush(dump_file);
			#endif

			if(!isReachableFromStartNode(*it, cnode))
			{
				#if 0
				fprintf(dump_file, "\nNode %d not reachable\n", *it);
				fflush(dump_file);
				#endif

				return false;	
			}
		}
	}

	#if 0
	fprintf(dump_file,"\nNo Successors\n");
	fflush(dump_file);
	#endif

	return true;
}

bool GPG::isReachableFromExitNode(unsigned int node, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	#if 0
	fprintf(dump_file,"\nChecking Reachability from exit node %d\n", node);
	fflush(dump_file);
	#endif
	
	unsigned int exit_node = getExitGPB();

	if(node == exit_node)
	{
		return true;
	}

	GPBSet succs = getNext(node);

	#if 0
	fprintf(dump_file,"\nSuccessors\n");
	fflush(dump_file);
	#endif

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		#if 0
		fprintf(dump_file, "\nSucc %d\n", *it);
		fflush(dump_file);
		#endif

		if(exit_node == *it)
		{
			#if 0
			fprintf(dump_file, "\nNode %d Found\n", *it);
			fflush(dump_file);
			#endif

			return true;
		}

		if(visited_list1.find(*it) == visited_list1.end())
		{
			#if 0
			fprintf(dump_file, "\nCheck suucs of %d\n", *it);
			fflush(dump_file);
			#endif

			if(!isReachableFromExitNode(*it, cnode))
			{
				#if 0
				fprintf(dump_file, "\nNode %d not reachable\n", *it);
				fflush(dump_file);
				#endif

				return false;	
			}	
		}
	}

	#if 0
	fprintf(dump_file,"\nNo Successors\n");
	fflush(dump_file);
	#endif

	return true;
}

bool GPG::checkGPGStructure(struct cgraph_node *cnode, bool orig)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet bb_set = getGPBs();
	unsigned int entry, end;

	entry = getEntryGPB();
	end = getExitGPB();

	if(isTop())
	{
		return false;
	}

	#if 0
	if(entry == end)
	{
		if(bb_set.size() != 1)
		{
			fprintf(dump_file, "\nAlert\nSpurious Nodes\n");
			fprintf(dump_file, "\nExtra Nodes when GPG consists of single entry-exit\n");
			return true;
		}
	}
	#endif

	if(bb_set.find(entry) == bb_set.end())
	{
		fprintf(dump_file, "\nAlert\nEntry not found\n");

		return true;
	}

	if(bb_set.find(end) == bb_set.end())
	{
		fprintf(dump_file, "\nAlert\nExit not found\n");

		return true;
	}

	if(!(getPrev(entry).empty()))
	{
		fprintf(dump_file, "\nAlert\nEntry has predecessors\n");

		return true;
	}

	if(!(getNext(end).empty()))
	{
		fprintf(dump_file, "\nAlert\nExit has successors\n");

		return true;
	}	

	GPB bb1, bb2;

	GPBSet end_prev, end_next;
	bool end_disconnect = false;

	end_prev = getPrev(end);
	end_next = getNext(end);

	if(end_prev.empty() && end_next.empty())
	{
		end_disconnect = true;
	}

	for(GPBSet::iterator it = bb_set.begin(); it != bb_set.end(); it++)
	{
		GPBSet succs, preds, temp_set1, preds_temp, succs_temp;

		if(*it < 0)
		{
			fprintf(dump_file, "\nSpoiler Alert\n");
			fprintf(stderr, "\nSpoiler Alert\n");
			return true;
		}

		bb1 = gpb_map[*it];

		succs = getNext(*it);
		preds_temp = getPrev(*it);

		if((end == *it) && end_disconnect)
		{
			continue;
		}

		#if 0
		if(end_disconnect && bb_set.size() > 2 && succs.empty() && preds_temp.empty())
		{
//			fprintf(dump_file, "\nAlert No predecessors and successors\n");
//			printGPG(cnode);
//			return true;
//			exit(1);
		}
		else if((!(end_disconnect)) && bb_set.size() > 1 && succs.empty() && preds_temp.empty())
		{
			fprintf(dump_file, "\nAlert No predecessors and successors\n");
			printGPG(cnode);
			return true;
//			exit(1);	
		}
		#endif

		#if 0
		if(succs.size() > 20 || preds_temp.size() > 20)
		{
			fprintf(dump_file, "\nToo many preds-succs for GPB %d\n", *it);
			fprintf(stderr, "\nToo many preds-succs for GPB %d\n", *it);

			return true;
		}
		#endif	

		set_intersection(bb_set.begin(), bb_set.end(), succs.begin(), succs.end(), inserter(temp_set1, temp_set1.end()));

		if(temp_set1 != succs)
		{
			fprintf(dump_file, "\nAlert\nSpurious Nodes for GPB %d\n", *it);
			fprintf(dump_file, "\nSuccs Not in GPBs Set\n");
			#if 1
			fprintf(dump_file, "\nGPBs\n");
			print_set_integers(bb_set);
			fprintf(dump_file, "\ntemp_set1\n");
			print_set_integers(temp_set1);
			fprintf(dump_file, "\nsuccs\n");
			print_set_integers(succs);
			#endif	
			return true;
		}	

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			GPBSet temp_set2;

			bb2 = gpb_map[*sit];

			preds = getPrev(*sit);
			succs_temp = getNext(*sit);

			if(succs.size() == 0 and preds.size() == 0)
			{
				fprintf(dump_file, "\nNo succs and preds\n");
				return true;	
			}

			#if 0			
			if(preds.size() > 20 || succs_temp.size() > 20)
			{
				fprintf(dump_file, "\nToo many preds-succs for GPB %d\n", *sit);
				fprintf(stderr, "\nToo many preds-succs for GPB %d\n", *sit);
	
				return true;
			}
			#endif

			set_intersection(bb_set.begin(), bb_set.end(), preds.begin(), preds.end(), inserter(temp_set2, temp_set2.end()));

			if(temp_set2 != preds)
			{
				fprintf(dump_file, "\nAlert\nSpurious Nodes\n");
				fprintf(dump_file, "\nPreds Not in GPBs Set %d and %d\n", *it, *sit);
				fprintf(dump_file, "\ntemp_set2: ");
				print_set_integers(temp_set2);
				fprintf(dump_file, "\npreds: ");
				print_set_integers(preds);
				fprintf(dump_file, "\nbb_set: ");
				print_set_integers(bb_set);
				fprintf(dump_file, "\n\n");
	
				return true;
			}

			if(preds.find(*it) == preds.end())
			{
				fprintf(dump_file, "\nALert\nGPB1\n");
				bb1.printGPB(cnode);
				fprintf(dump_file, "\nGPB2\n");
				bb2.printGPB(cnode);
				return true;

				#if 0
				fprintf(stderr,"\nSucc - Pred Problem\n");
				fflush(dump_file);
				exit(0);
				#endif
			}
		}
	}

	return false;
}

bool GPG::areCallBlocksPresentForRecursion(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs, res;;

	if(isIdentity())
	{
		return false;
	}

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock())
		{
			if(gpb.getCallee() == caller_rep)
			{
				return true;
			}
		}
	}

	return false;
}

GPBSet GPG::returnCallBlocksPresentForRecursion(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs, res;

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock())
		{
			if(gpb.getCallee() == caller_rep)
			{
				res.insert(*it);
			}
		}
	}

	return res;
}

unsigned int GPG::returnNumberOfSymGPBs(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs;
	unsigned int res = 0;

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isSymGPB())
		{
			res++;
		}
	}

	return res;
}

GPBSet GPG::getCallBlocks(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs, res;

	if(isIdentity())
	{
		return res;
	}

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock())
		{
			res.insert(*it);
		}
	}

	return res;
}

GPBSet GPG::getSymGPBs(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs, res;

	if(isIdentity())
	{
		return res;
	}

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isSymGPB())
		{
			res.insert(*it);
		}
	}

	return res;
}

GPBSet GPG::getCallBlocksForCallee(struct cgraph_node *cnode, unsigned int the_callee)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;
	unsigned int callee;

	GPBSet gpbs, res;

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock())
		{
			callee = gpb.getCallee();

			if(the_callee == callee)
			{
				res.insert(*it);
			}
		}
	}

	return res;
}

GPBSet GPG::getIntervalBlocks(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs, res;

	if(isIdentity())
	{
		return res;
	}

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isInterval())
		{
			res.insert(*it);
		}
	}

	return res;
}

#if INTDIR
GPBSet GPG::getIntervalDirectBlocks(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs, res;

	if(isIdentity())
	{
		return res;
	}

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isInterval() || gpb.isIntervalDirect())
		{
			res.insert(*it);
		}
	}

	return res;
}
#endif

GPBSet GPG::getIndirectCallBlocks(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs, res;

	if(isIdentity())
	{
		return res;
	}

	gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isIndirectCallBlock())
		{
			res.insert(*it);
		}
	}

	return res;
}

GPG GPG::meet(GPG g)
{
	if(isIdentity())
	{
		return g;
	}
	
	if(g.isIdentity())
	{
		return *(this);
	}

	unsigned int start_node1 = getEntryGPB();
	unsigned int start_node2 = g.getEntryGPB();

	unsigned int end_gpb1 = getExitGPB();
	unsigned int end_gpb2 = g.getExitGPB();

	GPG res;

	if(start_node1 != start_node2)
	{
		return res;
	}

	res.setEntryGPB(start_node1);

	GPBSet gpbs = getGPBs();
	GPBSet gpbs1 = g.getGPBs();

	std::map< unsigned int, GPB > new_gpb_map;
	std::map< unsigned int, GPUSet > rin, brin, rout, brout, ptsin, ptsout;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		new_gpb_map[*it] = gpb_map[*it];

		rin[*it] = RIN[*it];
		brin[*it] = BRIN[*it];

		rout[*it] = ROUT[*it];
		brout[*it] = BROUT[*it];

		ptsin[*it] = PTSIN[*it];
		ptsout[*it] = PTSOUT[*it];
	}

	for(GPBSet::iterator it = gpbs1.begin(); it != gpbs1.end(); it++)
	{
		new_gpb_map[*it] = g.gpb_map[*it];

		rin[*it] = g.RIN[*it];
		brin[*it] = g.BRIN[*it];

		rout[*it] = g.ROUT[*it];
		brout[*it] = g.BROUT[*it];

		ptsin[*it] = g.PTSIN[*it];
		ptsout[*it] = g.PTSOUT[*it];

		gpbs.insert(*it);
	}

//	gpbs.insert(gpbs1.begin(), gpbs1.end());	

	edge_set backedges = getBackEdges();
	edge_set backedges1 = g.getBackEdges();

	backedges.insert(backedges1.begin(), backedges1.end());

	if(end_gpb1 >= end_gpb2)
	{
		res.setExitGPB(end_gpb1);
	}
	else
	{
		res.setExitGPB(end_gpb2);
	}

	if(GPB_count >= g.GPB_count)
	{
		res.GPB_count = GPB_count;
	}
	else
	{
		res.GPB_count = g.GPB_count;
	}

	res.setGPBs(gpbs);
	res.setBackEdges(backedges);
	res.gpb_map = new_gpb_map;

	res.RIN = rin;
	res.BRIN = brin;

	res.ROUT = rout;
	res.BROUT = brout;

	res.PTSIN = ptsin;
	res.PTSOUT = ptsout;

	return res;
}

GPBSet GPG::returnEmptyGPBs(unsigned int caller, bool orig)
{
	GPBSet gpbs, res;
	GPUSet gpus;
	GPB gpb;

	gpbs= getGPBs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(orig)
		{
			if(gpb.isInitialEmpty())
			{
				res.insert(*it);
			}		
		}
		else
		{
			if(gpb.isEmpty())
			{
				res.insert(*it);
			}		
		}
	}

	return res;
}

unsigned int GPG::returnNumberOfEmptyGPBsFromGPG(unsigned int caller, bool orig)
{
	if(isTop())
	{
		return 0;
	}

	GPBSet gpbs = getGPBs();
	GPB gpb;
	unsigned int res = 0;
	GPUSet gpus;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(orig)
		{
			if(gpb.isInitialEmpty())
			{
				res++;
			}		
		}
		else
		{
			if(gpb.isEmpty())
			{
				res++;
			}		
		}
	}

	return res;
}

unsigned int GPG::returnNumberOfGPBsFromGPG(unsigned int caller)
{
	if(isTop())
	{
		return 0;
	}

	GPBSet gpbs = getGPBs();

	return gpbs.size();
}

unsigned int GPG::returnNumberOfDirectCallBlocks(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	unsigned int calls = 0;

	GPBSet gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock())
			calls++;
	}

	return calls;
}

unsigned int GPG::returnNumberOfIndirectCallBlocks(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	unsigned int calls = 0;

	GPBSet gpbs = getGPBs();
//	GPBSet intervals = getIntervals();
//	gpbs.insert(intervals.begin(), intervals.end());
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isIndirectCallBlock())
			calls++;
	}

	return calls;
}

unsigned int GPG::returnNumberOfIntervals(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	unsigned int calls = 0;

	GPBSet gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		#if INTDIR
		if(gpb.isInterval() || gpb.isIntervalDirect())
		#else
		if(gpb.isInterval())
		#endif
			calls++;
	}

	return calls;
}

bool GPG::emptyGPG(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();
	GPB gpb;	

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(!gpb.isEmpty())
		{
			return false;
		}
	}

	return true;
}

unsigned int GPG::coalescingGroupOfGPBs(GPBSet coalesce_group, struct cgraph_node *cnode)	
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	unsigned int start, end;

	start = getEntryGPB();
	end = getExitGPB();

	#if 0
	fprintf(dump_file, "\nInside coalescingGroupOfGPBs\n");
	fflush(dump_file);	
	print_set_integers(coalesce_group);
	#endif

	GPUSet must_gpus, gpus, rin, brin, rout, brout, temp_gpuset;
	GPBSet prev, next, temp_gpbset;
	GPB gpb;
	unsigned int bb_index;
	bool self_loop = false;

	GPBSet tempi;
	basic_block bb;
	unsigned int b;
	bool ffound = false;
	GPBSet call_sites = getCallSites();
	GPBSet found_set;

	stmt_info_type key_t, key;
	GPBSet sset, temp_sset;

	unsigned int x = GPB_count++;

	for(GPBSet::iterator it = coalesce_group.begin(); it != coalesce_group.end(); it++)
	{
		gpb = gpb_map[*it];

		if(call_sites.find(*it) != call_sites.end())
		{
			found_set.insert(*it);
		}

		b = gpb.getBBIndex();

		#if 0
		fprintf(dump_file, "\nGPB %d\n", *it);
		fflush(dump_file);	
		#endif

		#if 0
		fprintf(dump_file, "\nGetting GPUs for GPB %d\n", *it);
		fflush(dump_file);	
		#endif

		// Reduced GPUs
		temp_gpuset = gpb.getGPUs();

		for(GPUSet::iterator rit = temp_gpuset.begin(); rit != temp_gpuset.end(); rit++)
		{
			key_t = std::make_tuple(cnode_num, *it, *rit); 

			temp_sset = stmt_id_info[key_t];

//			stmt_id_info.erase(key_t);

			key = std::make_tuple(cnode_num, x, *rit);

			sset = stmt_id_info[key];

			sset.insert(temp_sset.begin(), temp_sset.end());

			stmt_id_info[key] = sset;

			gpus.insert(*rit);
		}

//		gpus.insert(temp_gpuset.begin(), temp_gpuset.end());

		#if 0
		fprintf(dump_file, "\nGetting RIN for GPB %d\n", *it);
		fflush(dump_file);	
		#endif

		// RIN
		temp_gpuset = RIN[*it];
		rin.insert(temp_gpuset.begin(), temp_gpuset.end());

		#if 0
		fprintf(dump_file, "\nGetting BRIN for GPB %d\n", *it);
		fflush(dump_file);	
		#endif

		// BRIN
		temp_gpuset = BRIN[*it];
		brin.insert(temp_gpuset.begin(), temp_gpuset.end());

		#if 0
		fprintf(dump_file, "\nGetting ROUT for GPB %d\n", *it);
		fflush(dump_file);	
		#endif

		// ROUT
		temp_gpuset = ROUT[*it];
		rout.insert(temp_gpuset.begin(), temp_gpuset.end());

		#if 0
		fprintf(dump_file, "\nGetting BROUT for GPB %d\n", *it);
		fflush(dump_file);	
		#endif

		// BROUT
		temp_gpuset = BROUT[*it];
		brout.insert(temp_gpuset.begin(), temp_gpuset.end());

		#if 0
		fprintf(dump_file, "\nGetting Prev for GPB %d\n", *it);
		fflush(dump_file);	
		#endif

		// Prev
		temp_gpbset = getPrev(*it);
		prev.insert(temp_gpbset.begin(), temp_gpbset.end());

		#if 0
		fprintf(dump_file, "\nPrev for GPB %d\n", *it);
		fflush(dump_file);	
		print_set_integers(temp_gpbset);	
		fflush(dump_file);
		fprintf(dump_file, "\nAccumalted Prev so far\n");
		fflush(dump_file);	
		print_set_integers(prev);	
		fflush(dump_file);
		#endif

		if(temp_gpbset.find(*it) != temp_gpbset.end())
			self_loop = true;			

		#if 0
		fprintf(dump_file, "\nGetting Next for GPB %d\n", *it);
		fflush(dump_file);	
		#endif

		// Next
		temp_gpbset = getNext(*it);
		next.insert(temp_gpbset.begin(), temp_gpbset.end());

		#if 0
		fprintf(dump_file, "\nNext for GPB %d\n", *it);
		fflush(dump_file);	
		print_set_integers(temp_gpbset);	
		fflush(dump_file);
		fprintf(dump_file, "\nAccumalted Next so far\n");
		fflush(dump_file);	
		print_set_integers(next);	
		fflush(dump_file);
		#endif

//		bb_index = gpb.getBBIndex();
	}

	#if 0
	if(!found_set.empty())
	{
		call_sites.insert(x);
		GPBSet ttset, ttset_t;

		for(GPBSet::iterator it = found_set.begin(); it != found_set.end(); it++)
		{
			call_sites.erase(*it);

			ttset = call_site_map[cnode_num][x];
			ttset_t = call_site_map[cnode_num][*it];
			ttset.insert(ttset_t.begin(), ttset_t.end());
			call_site_map[cnode_num][x] = ttset;

			call_site_map[cnode_num].erase(*it);
		}

		setCallSites(call_sites);
	}
	#endif

	#if 0
	fprintf(dump_file, "\nNew GPB %d\n", x);
	fflush(dump_file);	

	fprintf(dump_file, "\nPrev before for New GPB %d\n", x);
	fflush(dump_file);
	print_set_integers(prev);	
	fflush(dump_file);

	fprintf(dump_file, "\nNext before for New GPB %d\n", x);
	fflush(dump_file);
	print_set_integers(next);	
	fflush(dump_file);
	#endif

	for(GPBSet::iterator sit = coalesce_group.begin(); sit != coalesce_group.end(); sit++)
	{
		#if 0
		fprintf(dump_file, "\nErasing From Prev %d\n", *sit);
		fflush(dump_file);
		#endif

		prev.erase(*sit);
	}
	
	for(GPBSet::iterator sit = coalesce_group.begin(); sit != coalesce_group.end(); sit++)
	{
		#if 0
		fprintf(dump_file, "\nErasing from Next %d\n", *sit);
		fflush(dump_file);
		#endif

		next.erase(*sit);
	}

	if(self_loop)
	{
		prev.insert(x);
		next.insert(x);
	}

	#if 0
	fprintf(dump_file, "\nPrev for New GPB %d\n", x);
	fflush(dump_file);
	print_set_integers(prev);	
	fflush(dump_file);

	fprintf(dump_file, "\nNext for New GPB %d\n", x);
	fflush(dump_file);
	print_set_integers(next);	
	fflush(dump_file);
	#endif

	for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
	{
		if(*it == x)
			continue;

		temp_gpbset = getNext(*it);

		for(GPBSet::iterator sit = coalesce_group.begin(); sit != coalesce_group.end(); sit++)
		{
			temp_gpbset.erase(*sit);
		}

		temp_gpbset.insert(x);
		setNext(*it, temp_gpbset);
	}

	for(GPBSet::iterator it = next.begin(); it != next.end(); it++)
	{
		if(*it == x)
			continue;

		temp_gpbset = getPrev(*it);

		for(GPBSet::iterator sit = coalesce_group.begin(); sit != coalesce_group.end(); sit++)
		{
			temp_gpbset.erase(*sit);
		}

		temp_gpbset.insert(x);
		setPrev(*it, temp_gpbset);
	}

	#if 0
	fprintf(dump_file, "\nAdjust Successors of Prev and Predecessors for Next\n");	
	fflush(dump_file);

	gpu_id_type cgpu;

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		fprintf(dump_file, "\nChecking if its Must GPU\n");
		fflush(dump_file);
		print_GPU(*it);
		fflush(dump_file);

		cgpu = getCopyGPU(get<0>(*it));

		fprintf(dump_file, "\nCorresponding Boundary GPU\n");
		fflush(dump_file);
		print_GPU(cgpu);
		fflush(dump_file);

		if(rout.find(cgpu) == rout.end())
		{
			fprintf(dump_file, "\nBoundary GPU not present in ROUT\n");
			fflush(dump_file);

			must_gpus.insert(*it);
		}
	}

	fprintf(dump_file, "\nSetting Up for new GPB\n");
	fflush(dump_file);
	#endif

	GPB new_gpb;

	new_gpb.setId(x);
	new_gpb.setBBIndex(b);
	setPrev(x, prev);
	setNext(x, next);
	new_gpb.setGPUs(gpus);

//	new_gpb.setMustGPUs(must_gpus);
//	new_gpb.setDirty();

	gpb_map[x] = new_gpb;

	#if 1
	RIN[x] = rin;
	ROUT[x] = rout;
	BRIN[x] = brin;
	BROUT[x] = brout;
	#endif

	temp_gpbset = getGPBs();

	for(GPBSet::iterator sit = coalesce_group.begin(); sit != coalesce_group.end(); sit++)
	{
		temp_gpbset.erase(*sit);
	}

	temp_gpbset.insert(x);
	setGPBs(temp_gpbset);	

	DFP[x] = DFP_TEMP;

	unsigned int entry, exit;
	entry = getEntryGPB();
	exit = getExitGPB();

	if(coalesce_group.find(entry) != coalesce_group.end())
	{
		setEntryGPB(x);
	}

	if(coalesce_group.find(exit) != coalesce_group.end())
	{
		setExitGPB(x);
	}
	
	#if 0
	if(coalesce_group.find(start) != coalesce_group.end())
	{
		setEntryGPB(x);
	}

	if(coalesce_group.find(end) != coalesce_group.end())
	{
		setExitGPB(x);
	}
	#endif	

	#if 0
	fprintf(dump_file, "\nEnd of coalescingGroupOfGPBs\n");
	printGPG(cnode);
	#endif

	return x;
}

void GPG::removeEmptyGPB(unsigned int id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPB gpb;
	GPBSet prev, next;
	prev = getPrev(id);
	next = getNext(id);
	GPUSet gpus;

//	fprintf(dump_file, "\nInside removeEmptyGPB for %d\n", id);

	#if 0	
	fprintf(dump_file, "\nPredecessors\n");
	print_set_integers(prev);		
	fprintf(dump_file, "\nSuccessors\n");
	print_set_integers(next);		
	#endif

	if(prev.empty() && next.empty())
	{
		// Record it
		return;
	}

	for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
	{
		if(*it == id)
		{
			continue;
		}

		GPBSet temp = getNext(*it);
		temp.insert(next.begin(), next.end());
		temp.erase(id);
		setNext(*it, temp);
	}

	for(GPBSet::iterator it = next.begin(); it != next.end(); it++)
	{
		if(*it == id)
		{
			continue;
		}

		GPBSet temp = getPrev(*it);
		temp.insert(prev.begin(), prev.end());
		temp.erase(id);
		setPrev(*it, temp);
	}

	GPBSet bb_temp, temp_set;
	gpb = gpb_map[id];
//	unsigned int b = gpb.getBBIndex();
	temp_set = getPrev(id);
	temp_set.erase(id);
	
//	fprintf(dump_file, "\nHey Der1\n");
//	fflush(dump_file);

//	basic_block bb = BASIC_BLOCK(b);

//	fprintf(dump_file, "\nHey Der2 %d, %d\n", b);
//	fflush(dump_file);

	GPBSet call_sites = getCallSites();

	if(call_sites.find(id) != call_sites.end())
	{
		call_sites.erase(id);
		prev.erase(id);

		GPBSet callee = call_site_map[caller_rep][id];
		GPBSet ttset;

		call_sites.insert(prev.begin(), prev.end());

		for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
		{
			ttset = call_site_map[caller_rep][*it];
			ttset.insert(callee.begin(), callee.end());
			call_site_map[caller_rep][*it] = ttset;
		}

		call_site_map[caller_rep].erase(id);
	
		setCallSites(call_sites);
	}

	#if 0
	bb_temp = BB_START[caller_rep][b];	

	if(bb_temp.find(id) != bb_temp.end())
	{
		bb_temp.erase(id);
		bb_temp.insert(temp_set.begin(), temp_set.end());
		BB_START[caller_rep][b] = bb_temp;
	}

	temp_set = getNext(id);
	temp_set.erase(id);

	bb_temp = BB_END[caller_rep][b];	

	if(bb_temp.find(id) != bb_temp.end())
	{
		bb_temp.erase(id);
		bb_temp.insert(temp_set.begin(), temp_set.end());
		BB_END[caller_rep][b] = bb_temp;
	}

//	bb_temp = ((block_information *)(bb->aux))->sblocks;

//	fprintf(dump_file, "\nHey Der3\n");
//	fflush(dump_file);

//	((block_information *)(bb->aux))->sblocks = bb_temp;
	#endif
}

void GPG::removeGPB(unsigned int id, struct cgraph_node *cnode) // Remove GPB without connecting its predecessors to its successors, to remove call GPBs after fixed-point computation for recursion
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPB gpb1, gpb2;
	GPBSet prev, next;
	prev = getPrev(id);
	next = getNext(id);

	for (auto it1 = prev.begin(); it1 != prev.end(); it1++)
	{
		if(*it1 == id)
			continue;
	
		remNext(*it1, id);
	}

	for (auto it2 = next.begin(); it2 != next.end(); it2++)
	{
		if(*it2 == id)
			continue;
	
		remPrev(*it2, id);
	}

	GPBSet call_sites = getCallSites();

	if(call_sites.find(id) != call_sites.end())
	{
		call_sites.erase(id);
		prev.erase(id);

		GPBSet callee = call_site_map[caller_rep][id];
		GPBSet ttset;

		call_sites.insert(prev.begin(), prev.end());

		for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
		{
			ttset = call_site_map[caller_rep][*it];
			ttset.insert(callee.begin(), callee.end());
			call_site_map[caller_rep][*it] = ttset;
		}

		call_site_map[caller_rep].erase(id);
	
		setCallSites(call_sites);
	}

	#if 0
	GPB gpb = gpb_map[caller_rep][id];

	unsigned int b  = gpb.getBBIndex();
//	basic_block bb = BASIC_BLOCK(b);

	GPBSet temp;
	temp = BB_START[caller_rep][b];
	temp.erase(id);
	BB_START[caller_rep][b] = temp;

	temp = BB_END[caller_rep][b];
	temp.erase(id);
	BB_END[caller_rep][b] = temp;

//	temp = ((block_information *)(bb->aux))->sblocks;
//	((block_information *)(bb->aux))->sblocks = temp;
	#endif
}

void GPG::replaceSibGPBs(unsigned int id, unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet prev1, prev2, next2, next1, prev, next;

	prev1 = getPrev(gpb_id1);
	next1 = getNext(gpb_id1);

	prev2 = getPrev(gpb_id2);
	next2 = getNext(gpb_id2);

	prev = prev1;
	prev.insert(prev2.begin(), prev2.end());

	next = next1;
	next.insert(next2.begin(), next2.end());

	if(prev.find(gpb_id1) != prev.end())
	{
		prev.erase(gpb_id1);
		prev.insert(id);
	}
	if(prev.find(gpb_id2) != prev.end())
	{
		prev.erase(gpb_id2);
		prev.insert(id);
	}

	if(next.find(gpb_id1) != next.end())
	{
		next.erase(gpb_id1);
		next.insert(id);
	}
	if(next.find(gpb_id2) != next.end())
	{
		next.erase(gpb_id2);
		next.insert(id);
	}

	for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
	{
		if(*it == gpb_id1 || *it == gpb_id2)
			continue;

		addNext(*it, id);
		remNext(*it, gpb_id1);
		remNext(*it, gpb_id2);
	}

	for(GPBSet::iterator it = next.begin(); it != next.end(); it++)
	{
		if(*it == gpb_id1 || *it == gpb_id2)
			continue;

		addPrev(*it, id);
		remPrev(*it, gpb_id1);
		remPrev(*it, gpb_id2);
	}

	setPrev(id, prev);
	setNext(id, next);

	RIN[id] = RIN[gpb_id1];
	BRIN[id] = BRIN[gpb_id1];

	ROUT[id] = ROUT[gpb_id2];
	BROUT[id] = BROUT[gpb_id2];
}

void GPG::replaceGPBs(unsigned int id, unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet prev, next;

	prev = getPrev(gpb_id1);
	next = getNext(gpb_id2);

	for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
	{
		if(*it == gpb_id1 || *it == gpb_id2)
			continue;

		addNext(*it, id);
		remNext(*it, gpb_id1);
	}

	for(GPBSet::iterator it = next.begin(); it != next.end(); it++)
	{
		if(*it == gpb_id1 || *it == gpb_id2)
			continue;

		addPrev(*it, id);
		remPrev(*it, gpb_id2);
	}

	setPrev(id, prev);
	setNext(id, next);

	RIN[id] = RIN[gpb_id1];
	BRIN[id] = BRIN[gpb_id1];

	ROUT[id] = ROUT[gpb_id2];
	BROUT[id] = BROUT[gpb_id2];
}

void GPG::replaceAdjGPBs(unsigned int id, unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet prev, prev2, next, next2;

	prev = getPrev(gpb_id1);
	prev2 = getPrev(gpb_id2);

	next = getNext(gpb_id1);
	next2 = getNext(gpb_id2);

	next.insert(next2.begin(), next2.end());
	prev.insert(prev2.begin(), prev2.end());

	next.erase(gpb_id1);
	next.erase(gpb_id2);

	prev.erase(gpb_id1);
	prev.erase(gpb_id2);

	#if 0
	fprintf(dump_file, "\nNew prev\n");
	print_set_integers(prev);
	fprintf(dump_file, "\nNew next\n");
	print_set_integers(next);
	#endif

	for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
	{
		addNext(*it, id);
		remNext(*it, gpb_id1);
		remNext(*it, gpb_id2);
	}

	for(GPBSet::iterator it = next.begin(); it != next.end(); it++)
	{
		addPrev(*it, id);
		remPrev(*it, gpb_id1);
		remPrev(*it, gpb_id2);
	}

	setPrev(id, prev);
	setNext(id, next);

	GPUSet temp1, temp2;

	temp1 = RIN[gpb_id1];
	temp2 = RIN[gpb_id2];
	temp1.insert(temp2.begin(), temp2.end());

	RIN[id] = temp1;

	temp1 = BRIN[gpb_id1];
	temp2 = BRIN[gpb_id2];
	temp1.insert(temp2.begin(), temp2.end());

	BRIN[id] = temp1;

	temp1 = ROUT[gpb_id1];
	temp2 = ROUT[gpb_id2];
	temp1.insert(temp2.begin(), temp2.end());

	ROUT[id] = temp1;

	temp1 = BROUT[gpb_id1];
	temp2 = BROUT[gpb_id2];
	temp1.insert(temp2.begin(), temp2.end());

	BROUT[id] = temp1;

	#if 0
	GPBSet call_sites = getCallSites();
	
	if(call_sites.find(gpb_id1) != call_sites.end())
	{
		call_sites.erase(gpb_id1);
		call_sites.insert(id);

		GPBSet callee = call_site_map[caller_rep][gpb_id1];
		GPBSet ttset;
		
		ttset = call_site_map[caller_rep][id];
		ttset.insert(callee.begin(), callee.end());
		call_site_map[caller_rep][id] = ttset;

		call_site_map[caller_rep].erase(gpb_id1);	

		setCallSites(call_sites);
	}

	call_sites = getCallSites();
	
	if(call_sites.find(gpb_id2) != call_sites.end())
	{
		call_sites.erase(gpb_id2);
		call_sites.insert(id);

		GPBSet callee = call_site_map[caller_rep][gpb_id2];
		GPBSet ttset;
		
		ttset = call_site_map[caller_rep][id];
		ttset.insert(callee.begin(), callee.end());
		call_site_map[caller_rep][id] = ttset;

		call_site_map[caller_rep].erase(gpb_id2);	

		setCallSites(call_sites);
	}
	#endif
}

void GPG::replaceGPB(unsigned int id, unsigned int id_r, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet prev, next;
	prev = getPrev(id);
	next = getNext(id);
	next.erase(id);
	prev.erase(id);

	for (auto it1 = prev.begin(); it1 != prev.end(); it1++)
	{
		if(*it1 == id)
			continue;

		addNext(*it1, id_r);	
		remNext(*it1, id);	
	}
		
	for (auto it2 = next.begin(); it2 != next.end(); it2++)
	{
		if(*it2 == id)
			continue;

		addPrev(*it2, id_r);	
		remPrev(*it2, id);	
	}

	GPBSet call_sites = getCallSites();
	
	if(call_sites.find(id) != call_sites.end())
	{
		call_sites.erase(id);
		call_sites.insert(id_r);

		GPBSet callee = call_site_map[caller_rep][id];
		GPBSet ttset;
		
		ttset = call_site_map[caller_rep][id_r];
		ttset.insert(callee.begin(), callee.end());
		call_site_map[caller_rep][id_r] = ttset;

		call_site_map[caller_rep].erase(id);	

		setCallSites(call_sites);
	}

	#if 0
	unsigned int b;
	GPB gpb = gpb_map[caller_rep][id];

	b = gpb.getBBIndex();

//	basic_block bb = BASIC_BLOCK(b);

	GPBSet temp;
	temp = BB_START[caller_rep][b];

	if(temp.find(id) != temp.end())
	{
		temp.erase(id);
		temp.insert(id_r);

		BB_START[caller_rep][b] = temp;
	}

	temp = BB_END[caller_rep][b];

	if(temp.find(id) != temp.end())
	{
		temp.erase(id);
		temp.insert(id_r);

		BB_END[caller_rep][b] = temp;
	}

//	temp = ((block_information *)(bb->aux))->sblocks; 
//	((block_information *)(bb->aux))->sblocks = temp; 

	gpb = gpb_map[caller_rep][id_r];
	gpb.setBBIndex(b);
	gpb_map[caller_rep][id_r] = gpb;
	#endif
}

bool GPG::areRelated(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet preds, succs;

	preds = getPrev(gpb_id1);

	if(preds.find(gpb_id2) != preds.end())
	{
		return true;
	}
	else
	{
		succs = getNext(gpb_id1);

		if(succs.find(gpb_id2) != succs.end())
		{
			return true;
		}
	}

	return false;
}

void GPG::eliminateAllEmptyGPBs(struct cgraph_node *cnode, bool orig) // orig = true => Orig GPUs, orig = false => reduced GPUs
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int cnum = ((function_info *)(cnode->aux))->func_num;

	GPBList consideredGPBs;
	GPBSet alreadyVisited;
	unsigned int gpb_id, temp_ps;
	unsigned int entry, end;

	entry = getEntryGPB();
	end = getExitGPB();
	consideredGPBs.push_back(entry);

	GPB gpb;
	GPUSet gpus;
	GPBSet succs, temp;

	while(!consideredGPBs.empty())
	{
		gpb_id = consideredGPBs.front();
		consideredGPBs.pop_front();
		alreadyVisited.insert(gpb_id);

		gpb = gpb_map[gpb_id];

//		fprintf(dump_file, "\nConsidering GPB %d to be eliminated with entry = %d, exit = %d\n", gpb_id, entry, end);
//		fflush(dump_file);

		succs = getNext(gpb_id);

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			if(alreadyVisited.find(*sit) == alreadyVisited.end())
			if(find(consideredGPBs.begin(), consideredGPBs.end(), *sit) == consideredGPBs.end())
			{
				consideredGPBs.push_back(*sit);
			}
		}

		if(gpb_id == entry || gpb_id == end)
		{
			continue;	
		}

		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

//		fprintf(dump_file, "\nInside eliminateEmptyGPB\n");
//		printSetOfGPUs(gpus);

		if(orig)
		{	
			if(gpb.isInitialEmpty())
			{
				eliminateEmptyGPB(gpb_id, cnode);
			}
		}
		else
		{	
			if(gpb.isEmpty())
			{
				eliminateEmptyGPB(gpb_id, cnode);
			}
		}

		#if 0
		if(checkGPGStructure(cnode, orig))
		{
			fprintf(dump_file,"\nHigh Alert after Elimination of Empty GPB %d\n", gpb_id);
			fflush(dump_file);
			printGPG(cnode);
			fflush(dump_file);
			exit(1);
		}
		#endif
	}

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

bool GPG::canCoalesce(unsigned int gpb_id, GPBSet succs, struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet preds = getPrev(gpb_id);
	preds.erase(gpb_id);
	GPBSet temp;

	set_intersection(succs.begin(), succs.end(), preds.begin(), preds.end(), inserter(temp, temp.end()));

	for(GPBSet::iterator it = temp.begin(); it != temp.end(); it++)
	{
		if(checkDataDependence(gpb_id, *it, cnode))
		{
			return false;
		}
	}

	return true;
}

GPUSet GPG::getParaArgGPUs(basic_block bb, struct cgraph_node *cnode)
{
	it ai;
	GPUSet res, temp_set;

	unsigned int stmt_id;

	#if 0
	fprintf(dump_file, "\nInside getParaArgGPUs for basic block %d and function %s\n", bb->index, cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	for(ai= ((block_information *)(bb->aux))->get_list().begin();ai !=((block_information *)(bb->aux))->get_list().end(); ai++ )
	{
		if(!(*ai).get_bool())
		{
			continue;
		}

		stmt_id = (*ai).get_int();

		#if 0
		fprintf(dump_file, "\nConstraint Number %d\n", stmt_id);
		fflush(dump_file);
		#endif

		constraint_t con = VEC_index(constraint_t, aliases, stmt_id);

		if(con == NULL)
			continue;

		if(con->phi_stmt)
			continue;

		#if 0
		print_constraint(con);
		fflush(dump_file);

		fprintf(dump_file, "\nBefore resolving the constraint\n");
		fflush(dump_file);
		#endif

		temp_set = resolve_constraint_SSA(stmt_id, bb, cnode, true);

		#if 0
		fprintf(dump_file, "\nAfter resolving the constraint\n");
		fflush(dump_file);
		printSetOfGPUs(temp_set);
		fflush(dump_file);
		#endif

		res.insert(temp_set.begin(), temp_set.end());
	}	

	#if 0
	fprintf(dump_file, "\nEnd of getParaArgGPUs\n");
	fflush(dump_file);
	#endif

	return res;
}

void GPG::insertParaGPBForDirectCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee, GPUSet res)
{
//	fprintf(dump_file, "\nCall GPB %d\n", call_gpb);

	GPB call = gpb_map[call_gpb];

	struct cgraph_node *cnode = func_numbering[caller_rep];

//	g.printGPG(cnode);

	GPBSet preds, temp, succs;
	GPUSet temp_set;

	preds = getPrev(call_gpb);
	preds.erase(call_gpb);

	GPB para_gpb, temp_gpb;

	unsigned int  x = GPB_count++;

//	fprintf(dump_file, "\nx = %d\n", x);
//	GPB_count++;

	unsigned int start = g_callee.getEntryGPB();

//	fprintf(dump_file, "\nstart = %d, caller_rep = %d, callee_rep = %d, caller = %s\n", start, caller_rep, callee_rep, cgraph_node_name(cnode));
//	g_c.printInitialGPG(func_numbering[callee_rep]);

	if(getEntryGPB() == call_gpb)
	{
		setEntryGPB(x);
	}

	para_gpb.setId(x);

	setPrev(x, preds);

	succs.insert(start+x);

	setNext(x, succs);

	para_gpb.setBBIndex(bb->index);

	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		remNext(*it, call_gpb);
		addNext(*it, x);
	}	

	#if 0
	temp = BB_START[caller_rep][bb->index];
	temp.erase(call_gpb);
	temp.insert(x);
	BB_START[caller_rep][bb->index] = temp;

//	temp = ((block_information *)(bb->aux))->sblocks;
//	((block_information *)(bb->aux))->sblocks = temp;
	#endif

	#if 0
	temp = ori_red_map[caller_rep][bb->index];
	temp.erase(call_gpb);
	temp.insert(x);
	ori_red_map[caller_rep][bb->index] = temp;
	#endif

	GPBSet gpbs = getGPBs();

//	fprintf(dump_file, "\nHey Inserting Para Block\n");
//	print_set_integers(gpbs);

	gpbs.erase(call_gpb);
	gpbs.insert(x);

//	fprintf(dump_file, "\nHey Inserting Para Block, after deleting %d and inserting %d\n", call_gpb, x);
//	print_set_integers(gpbs);

	setGPBs(gpbs);

	#if 0
	fprintf(dump_file, "\nPara GPUs\n");
	printSetOfGPUs(res);
	#endif

	para_gpb.setOrigGPUs(res);
//	para_gpb.setGPUs(res);

	gpb_map[x] = para_gpb;	

//	fprintf(dump_file, "\nAfter Inserting Para GPB\n");
//	g.printGPG(cnode);
}

GPUSet GPG::getRetGPUs(basic_block bb, struct cgraph_node *caller, struct cgraph_node *callee, GPG g_callee)
{
	GPUSet res;

	if(((function_info *)(callee->aux))->has_ret_type())
	{
		#if 0
		fprintf(dump_file, "\nReturn Value\n");
		fflush(dump_file);
		fprintf(dump_file, "\nCaller %s\n", cgraph_node_name(caller));
		fflush(dump_file);
		fprintf(dump_file, "\nCallee %s\n", cgraph_node_name(callee));
		fflush(dump_file);
		#endif

		#ifndef MRB
		unsigned int ret_id;
		#endif
		#ifdef MRB
		set< unsigned int > ret_id;
		#endif

		ret_id = ((function_info *)(callee->aux))->get_ret_id();

//		fprintf(dump_file, "\nBefore Stmt\n");

		gimple stmt = bb_call_stmt (bb);

//		fprintf(dump_file, "\nAfter Stmt\n");

//		print_gimple_stmt (dump_file, stmt, 0, 0);
//		fprintf(dump_file,"\n\n");

		tree lhsop = gimple_call_lhs (stmt);
		csvarinfo_t vi = NULL;

		if(lhsop)
		{
			VEC(ce_s, heap) *lhsc = NULL;	
			cs_get_constraint_for (lhsop, &lhsc, bb, caller);
		
//			fprintf(dump_file, "\nHey LHS\n");
//			fprintf(dump_file, "\nLHS Name %s\n", alias_get_name(lhsop));
			//vi = cs_get_vi_for_tree(lhsop, bb, caller);
			//lhsop = SSAVAR(lhsop);

			vi = cs_lookup_vi_for_tree (lhsop);

			#ifndef MRB
			if(ret_id <= 4)
			{
				int f[IndirectionList::kSize];
				IndirectionList elist(true, 0, 0, f);
				Node rhs(ret_id, elist);

				IndirectionList l(true, 1, 0, f);

				Node lhs(vi->id, l);
				GPU gpu(lhs, rhs);

//				gpu.printGPU();
//				fflush(dump_file);

				res.insert(gpu.getGPUID());
			}
			#endif

		unsigned int end = g_callee.getExitGPB();
		unsigned int callee_rep = ((function_info *)(callee->aux))->func_num;
		GPUSet brout = BROUT[end];

		for(GPUSet::iterator it = brout.begin(); it != brout.end(); it++)
		{
//			print_GPU(*it);

			#ifndef MRB
			if(get<0>(get<0>(*it)) == ret_id)
			#endif
			#ifdef MRB
			if(ret_id.find(get<0>(get<0>(*it))) != ret_id.end())
			#endif
			{
				#if 0
				fprintf(dump_file, "\nFound Yes\n");
				fflush(dump_file);
				fprintf(dump_file, "\nFound %d\n", vi->id);
				fflush(dump_file);
				#endif

				Node rhs = getNode(get<1>(*it));

				#if 0
				fprintf(dump_file, "\nRHS\n");
				fflush(dump_file);
				rhs.printNode();
				fflush(dump_file);
				#endif

				IndirectionList r = rhs.getList();

				if(r.get_st_hp())
				{
					#if 0
					fprintf(dump_file, "\nStack Indlist\n");
					fflush(dump_file);
					#endif

					int field_list[IndirectionList::kSize];
					IndirectionList l(true, 1, 0, field_list);

					Node lhs(vi->id, l);
					GPU gpu(lhs, rhs);

//					gpu.printGPU();
//					fflush(dump_file);

					res.insert(gpu.getGPUID());
				}	
				else
				{
//					fprintf(dump_file, "\n!Stack Indlist\n");
//					fflush(dump_file);

					int field_list[IndirectionList::kSize];
					field_list[0] = SFIELD;
					IndirectionList l(false, 0, 1, field_list);

					Node lhs(vi->id, l);
					GPU gpu(lhs, rhs);

//					gpu.printGPU();
//					fflush(dump_file);

					res.insert(gpu.getGPUID());
				}
			}
		}}
	}

	#if 0
	fprintf(dump_file, "\nNo Return Value\n");
	fflush(dump_file);
	#endif

	return res;
}

void GPG::insertRetGPB(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, unsigned int x, GPG g_callee, GPUSet res)
{
	struct cgraph_node *callee = func_numbering[callee_rep];
	struct cgraph_node *caller = func_numbering[caller_rep];

	GPB call = gpb_map[call_gpb];

	GPBSet temp, succs, preds;

	unsigned int end = g_callee.getExitGPB();
	GPUSet temp_set;

	GPB ret_gpb, temp_gpb;

	ret_gpb.setId(++GPB_count);
	ret_gpb.setBBIndex(bb->index);
	GPB_count++;

//	fprintf(dump_file, "\nRet Id %d\n", GPB_count-1);

	unsigned int y = GPB_count - 1;

	if(getExitGPB() == call_gpb)
	{
		setExitGPB(y);
	}

	preds.insert(end+x);

	unsigned int w = end+x;

	setPrev(y, preds);

	succs = getNext(call_gpb);
	succs.erase(call_gpb);

	setNext(y, succs);

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		remPrev(*it, call_gpb);
		addPrev(*it, y);
	}

	remNext(w, call_gpb);
	addNext(w, y);

	GPB end_gpb = gpb_map[end+x];
//	end_gpb.setBBIndex(bb->index);
	gpb_map[end+x] = end_gpb;

	#if 0
	temp = BB_END[caller_rep][bb->index];
	temp.erase(call_gpb);
	temp.insert(y);
	BB_END[caller_rep][bb->index] = temp;
	#endif

//	temp = ((block_information *)(bb->aux))->eblocks;
//	((block_information *)(bb->aux))->eblocks = temp;

	#if 0
	temp = ori_red_map[caller_rep][bb->index];
	temp.insert(y);
	ori_red_map[caller_rep][bb->index] = temp;
	#endif

	GPBSet gpbs = getGPBs();
	gpbs.insert(y);
	setGPBs(gpbs);

	#if 0
	fprintf(dump_file, "\nRet GPUs\n");
	printSetOfGPUs(res);
	#endif

	ret_gpb.setOrigGPUs(res);
//	ret_gpb.setGPUs(res);

	gpb_map[y] = ret_gpb;

//	fprintf(dump_file, "\nAfter Inserting Ret GPB\n");
//	printGPG(caller);
}

void GPG::inlineCallAlt(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee)
{
	GPUSet array_data_caller, array_data_callee;

	array_data_callee = flowInsensitiveInformation[callee_rep];
	array_data_caller = flowInsensitiveInformation[caller_rep];

	for(GPUSet::iterator it = array_data_callee.begin(); it != array_data_callee.end(); it++)
	{
		array_data_caller.insert(stripUpwardsExposed(*it));
	}

	flowInsensitiveInformation[caller_rep] = array_data_caller; 

	struct cgraph_node *callee = func_numbering[callee_rep];
	struct cgraph_node *caller = func_numbering[caller_rep];

//	fprintf(dump_file, "\ng_callee\n");
//	g_callee.printInitialGPG(callee);

	if(g_callee.isTop())
	{
		eliminateGPB(call_gpb, caller);

		return;
	}

	GPB call = gpb_map[call_gpb];
	GPB temp_gpb, temp_gpb1;

//	fprintf(dump_file, "\ng_caller entry %d\n", getEntryGPB());

	GPUSet hgpus;
	insertParaGPBForDirectCall(call_gpb, callee_rep, caller_rep, bb, g_callee, hgpus);

	#if 0
	fprintf(dump_file, "\nAfter Inserting Para GPB\n");
	printInitialGPG(caller);
	#endif

	unsigned int  x = GPB_count - 1;

	unsigned int  b = bb->index;

	GPBSet gpbs_caller = getGPBs();
	GPBSet gpbs_callee = g_callee.getGPBs();

//	if(gpbs_caller.find(g_caller.getEntryGPB()) != gpbs_caller.end())
//		fprintf(dump_file, "\ng_caller entry %d\n", g_caller.getEntryGPB());

	GPBSet preds, temp;

	unsigned int start, end, para, ret;

	start = g_callee.getEntryGPB();
	unsigned int t;

//	fprintf(dump_file, "\nInlining Callee %s with Offset %d\n", cgraph_node_name(callee), x);
//	g_callee.printGPG(callee);
	unsigned int w;

	for(GPBSet::iterator it = gpbs_callee.begin(); it != gpbs_callee.end(); it++)
	{
		GPB new_gpb;

		temp_gpb = gpb_map[*it];

		t = *it;
		w = t+x;

		new_gpb.setId(w);

		GPB_count = t+x;	

		temp = g_callee.getPrev(*it);

//		fprintf(dump_file, "\nPredecessors of GPB in Callee = %d, and that in caller = %d\n", t, t+x);
//		print_set_integers(temp);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addPrev(w, *pit+x);
		}

		if(start == *it)
		{
			addPrev(w, x); // Adding Para GPB as a predecessor
		}

		temp = g_callee.getNext(*it);

//		fprintf(dump_file, "\nSuccessors of GPB in Callee = %d, and that in caller = %d\n", t, t+x);
//		print_set_integers(temp);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addNext(w, *pit+x);
		}

		if(temp_gpb.isCallBlock())
		{
			new_gpb.setCallBlock();
			new_gpb.setCallee(temp_gpb.getCallee());
		}
		else if(temp_gpb.isInterval())
		{
			new_gpb.setInterval();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#if INTDIR
		else if(temp_gpb.isIntervalDirect())
		{
			new_gpb.setIntervalDirect();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#endif
		else if(temp_gpb.isIndirectCallBlock())
		{
			new_gpb.setIndirectCallBlock();

			definitions def = temp_gpb.getIndirectCallees();

			definitions def_res;
			Node n1;	
			unsigned int var1;
			IndirectionList list1;
			node_id_type nid;

			for(definitions::iterator iit = def.begin(); iit != def.end(); iit++)
			{
				n1 = getNode(*iit);

				var1 = n1.getVarIndex();
				list1 = n1.getList();

				if(CDV.find(var1) != CDV.end())
				{
					--var1;
					Node n2(var1, list1);
					nid = n2.getNodeID();
				}
				else
				{
					nid = *iit;
				}

				def_res.insert(nid);
			}

			new_gpb.setIndirectCallees(def_res);
		}

		GPUSet gpu_set = temp_gpb.getGPUs();
		GPUSet res_gpus;

		for(GPUSet::iterator git = gpu_set.begin(); git != gpu_set.end(); git++)
		{
			res_gpus.insert(stripUpwardsExposed(*git));
		}
		
//		new_gpb.setGPUs(res_gpus);
		new_gpb.setOrigGPUs(res_gpus);

		new_gpb.setBBIndex(b);

		gpbs_caller.insert(t+x);

		#if 0
		temp = ori_red_map[caller_rep][bb->index];
		temp.insert(t+x);
		ori_red_map[caller_rep][bb->index] = temp;
		#endif

		gpb_map[t+x] = new_gpb;
	}

	std::map< unsigned int, GPG > intervals_caller, intervals_callee;
	intervals_caller = getIntervals();
	intervals_callee = g_callee.getIntervals();

	for(std::map< unsigned int, GPG >::iterator it = intervals_callee.begin(); it != intervals_callee.end(); it++)
	{	
		intervals_caller[(it->first+x)] = it->second;
	}

	setGPBs(gpbs_caller);
	setIntervals(intervals_caller);
	
//	fprintf(dump_file, "\nBefore inserting Ret Block\n");
//	printGPG(caller);

	GPUSet rgpus;

	insertRetGPB(call_gpb, callee_rep, caller_rep, bb, x, g_callee, rgpus);

//	fprintf(dump_file, "\nGPG After Inlining Call GPB %d\n", call_gpb);
//	printGPG(caller);

	#if 0
	if(checkGPGStructure(caller, true))
	{
		fprintf(dump_file,"\nHigh Inlining Alert\n");
		fflush(dump_file);
		printGPG(caller);
		fflush(dump_file);
		exit(1);
	}
	#endif

	return;
}

void GPG::copyFIData(unsigned int callee_rep, unsigned int caller_rep)
{
	GPUSet t1, t2;
	std::map< unsigned int, GPUSet > fip_data_callee, fip_data_caller, finp_data_callee, finp_data_caller;
	fip_data_caller = FIP[caller_rep];
	finp_data_caller = FINP[caller_rep];

	fip_data_callee = FIP[callee_rep];

	for(std::map< unsigned int, GPUSet >::iterator fit = fip_data_callee.begin(); fit != fip_data_callee.end(); fit++)
	{
		if(is_ssa_var(fit->first))
		{
			continue;
		}

		t1 = fit->second;

		t2 = fip_data_caller[fit->first];

		t2.insert(t1.begin(), t1.end());

		fip_data_caller[fit->first] = t2;
	}

	finp_data_callee = FINP[callee_rep];

	for(std::map< unsigned int, GPUSet >::iterator fit = finp_data_callee.begin(); fit != finp_data_callee.end(); fit++)
	{
		t1 = fit->second;

		t2 = finp_data_caller[fit->first];

		for(GPUSet::iterator mit = t1.begin(); mit != t1.end(); mit++)
		{
			gpu_id_type id_temp = stripUpwardsExposed(*mit);

			t2.insert(id_temp);
		}

//		t2.insert(t1.begin(), t1.end());

		finp_data_caller[fit->first] = t2;
	}

	FIP[caller_rep] = fip_data_caller;
	FINP[caller_rep] = finp_data_caller;
}

GPBSet GPG::inlineCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	struct cgraph_node *callee = func_numbering[callee_rep];
	struct cgraph_node *caller = func_numbering[caller_rep];

	copyFIData(callee_rep, caller_rep);

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nBefore Inlining the call at GPB %d in GPG of Function %s of the Callee %s\n", call_gpb, cgraph_node_name(caller), cgraph_node_name(callee));
	fflush(dump_file);
	printInitialGPG(caller);
	fflush(dump_file);
	fprintf(dump_file, "\nOld GPBs\n");
	print_set_integers(getGPBs());
	fflush(dump_file);
	#endif

	GPBSet to_be_analyzed;
	GPBSet old_gpbs, new_gpbs;
	old_gpbs = getGPBs();

	GPB call = gpb_map[call_gpb];
	GPB temp_gpb, temp_gpb1;

	GPUSet para_gpus, ret_gpus;
	
	#if 0
	fprintf(dump_file, "\nComputing para_gpus\n");
	fflush(dump_file);
	#endif

	para_gpus = getParaArgGPUs(bb, caller);

	#if 0
	fprintf(dump_file, "\nComputed para_gpus\n");
	fflush(dump_file);
	#endif

	ret_gpus = getRetGPUs(bb, caller, callee, g_callee);

	#if 0
	fprintf(dump_file, "\nComputed ret_gpus\n");
	fflush(dump_file);
	
	fprintf(dump_file, "\nEmpty para_gpus %d\nEmpty ret_gpus %d\n", para_gpus.empty(), ret_gpus.empty());
	fflush(dump_file);
	#endif

	unsigned int  x;

	GPBSet gpbs_caller = getGPBs();
	GPBSet gpbs_callee = g_callee.getGPBs();

	GPBSet call_sites, ttset;

	unsigned int start, end, para, ret;

	start = g_callee.getEntryGPB();

	if(!para_gpus.empty())
	{
		insertParaGPBForDirectCall(call_gpb, callee_rep, caller_rep, bb, g_callee, para_gpus);

//		fprintf(dump_file, "\nGPB Count = %d\n", GPB_count);
//		fflush(dump_file);

		x = GPB_count - 1;

		gpbs_caller = getGPBs();

//		to_be_analyzed.insert(x);
	}
	else
	{
		x = GPB_count - 1;

		gpbs_caller.erase(call_gpb);

//		to_be_analyzed.insert(start+x);
	}

	#if 0
	fprintf(dump_file, "\nAfter Inserting Para GPB\n");
	printInitialGPG(caller);
	#endif

	unsigned int  b = bb->index;

//	if(gpbs_caller.find(g_caller.getEntryGPB()) != gpbs_caller.end())
//		fprintf(dump_file, "\ng_caller entry %d\n", g_caller.getEntryGPB());

	GPBSet preds, temp;

	unsigned int t;

//	fprintf(dump_file, "\nInlining Callee %s with Offset %d\n", cgraph_node_name(callee), x);
//	g_callee.printGPG(callee);

	unsigned int w;

	GPBSet call_prev;

	for(GPBSet::iterator it = gpbs_callee.begin(); it != gpbs_callee.end(); it++)
	{
		GPB new_gpb;

		temp_gpb = g_callee.gpb_map[*it];

		t = *it;
		w = t+x;

		#if 0
		if(w > 2147483640)
		{
			fprintf(dump_file, "\nOverFlow of GPB Count: w = %u, t = %u, x = %u\n", w, t, x);
	
			exit(1);
		}
		#endif

		DFP[w] = g_callee.DFP[t];

		new_gpb.setId(w);
//		to_be_analyzed.insert(w);

		GPB_count = t+x;	

		temp = g_callee.getPrev(*it);

		#if 0
		fprintf(dump_file, "\nPredecessors of GPB in Callee = %d, and that in caller = %d\n", t, t+x);
		print_set_integers(temp);
		#endif

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addPrev(w, *pit+x);
		}

		if(start == *it)
		{
			if(!para_gpus.empty())
			{
				addPrev(w, x); // Adding Para GPB as a predecessor
			}
			else
			{
//				fprintf(dump_file, "\nStart GPB of callee is first GPB\n");

				if(getEntryGPB() == call_gpb)
				{
//					fprintf(dump_file, "\nSetting new Entry %d\n", w);
					setEntryGPB(w);
				}
		
				call_prev = getPrev(call_gpb);

				for(GPBSet::iterator it = call_prev.begin(); it != call_prev.end(); it++)
				{
					if(*it == call_gpb)
					{
						addPrev(w, w);
						addNext(w, w);

						continue;
					}

					remNext(*it, call_gpb);
					addPrev(w, *it);
					addNext(*it, w);
				}
			}
		}

		temp = g_callee.getNext(*it);

		#if 0
		fprintf(dump_file, "\nSuccessors of GPB in Callee = %d, and that in caller = %d\n", t, t+x);
		print_set_integers(temp);
		#endif

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addNext(w, *pit+x);
		}

		#if 0
		if(temp_gpb.isDirty())
		{
			new_gpb.setDirty();
		}
		#endif

		if(temp_gpb.isSymGPB())
		{
			new_gpb.setSymGPB();

			GPBSet temp_c = temp_gpb.getSetOfCallees();
			temp_c.insert(callee_rep);
			new_gpb.setSetOfCallees(temp_c);

			new_gpb.setCallee(callee_rep);
			new_gpb.setGPUs(temp_gpb.getGPUs());

			if(temp_gpb.isResolved())
			{
				new_gpb.setResolved();	
			}
			else
			{
				new_gpb.resetResolved();	
			}
		}
		else if(temp_gpb.isCallBlock())
		{
			new_gpb.setCallBlock();
			new_gpb.setCallee(temp_gpb.getCallee());
		}
		#if 0
		else if(temp_gpb.isInterval())
		{
			new_gpb.setInterval();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#endif
		#if INTDIR
		else if(temp_gpb.isIntervalDirect())
		{
			new_gpb.setIntervalDirect();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#endif
		else if(temp_gpb.isIndirectCallBlock())
		{
			new_gpb.setIndirectCallBlock();

			definitions def = temp_gpb.getIndirectCallees();

			definitions def_res;
			Node n1;	
			unsigned int var1;
			IndirectionList list1;
			node_id_type nid;

			for(definitions::iterator iit = def.begin(); iit != def.end(); iit++)
			{
				n1 = getNode(*iit);

				var1 = n1.getVarIndex();
				list1 = n1.getList();

				if(CDV.find(var1) != CDV.end())
				{
					--var1;
					Node n2(var1, list1);
					nid = n2.getNodeID();
				}
				else
				{
					nid = *iit;
				}

				def_res.insert(nid);
			}

			new_gpb.setIndirectCallees(def_res);
		}

		GPUSet gpu_set = temp_gpb.getGPUs();
		GPUSet res_gpus;
		gpu_id_type nid;
		GPBSet sid;
		stmt_info_type key_t, key_callee;

		for(GPUSet::iterator git = gpu_set.begin(); git != gpu_set.end(); git++)
		{
			nid = stripUpwardsExposed(*git);

			#if DATA_MEAS
			gpu_key_type gkey = std::make_tuple(w, caller_rep);
			gpu_key[gkey] = callee_rep;	
			#endif

			res_gpus.insert(nid);

			GPBSet sset;

			key_t = std::make_tuple(caller_rep, w, nid);

			key_callee = std::make_tuple(callee_rep, t, *git);

			sid = stmt_id_info[key_callee];

			sset = stmt_id_info[key_t];

			sset.insert(sid.begin(), sid.end());			

			stmt_id_info[key_t] = sset;

			#if 0
			fprintf(dump_file, "\nGPU after removing upwards exposed in inlineCall\n");
			print_GPU(nid);
			tree t = NodeType[get<0>(nid)];

			if(t != NULL)
			{
				print_node(dump_file, "\nTREE IN FI Filtering\n", t, 0);
			}
			#endif
		}
		
//		new_gpb.setGPUs(res_gpus);
		new_gpb.setOrigGPUs(res_gpus);
		new_gpb.setGPUs(res_gpus);

		new_gpb.setBBIndex(b);

		gpbs_caller.insert(t+x);

		#if 0
		temp = ori_red_map[caller_rep][bb->index];
		temp.insert(t+x);
		ori_red_map[caller_rep][bb->index] = temp;
		#endif

		gpb_map[t+x] = new_gpb;
	}

	#if 0
	std::map< unsigned int, GPG > intervals_caller, intervals_callee;
	intervals_caller = getIntervals();
	intervals_callee = g_callee.getIntervals();

	for(std::map< unsigned int, GPG >::iterator it = intervals_callee.begin(); it != intervals_callee.end(); it++)
	{	
		intervals_caller[(it->first+x)] = it->second;
	}

	setIntervals(intervals_caller);
	#endif

	setGPBs(gpbs_caller);

	#if 0
	fprintf(dump_file, "\nBefore inserting Ret Block\n");
	printGPG(caller);
	#endif	
		
	if(!ret_gpus.empty())
	{
		insertRetGPB(call_gpb, callee_rep, caller_rep, bb, x, g_callee, ret_gpus);

//		to_be_analyzed.insert(GPB_count - 1);
	}
	else
	{
		unsigned int end_c = g_callee.getExitGPB();
		unsigned int fend_c = end_c+x;
		call_prev = getNext(call_gpb);

		if(getExitGPB() == call_gpb)
		{
			setExitGPB(fend_c);
		}

		for(GPBSet::iterator it = call_prev.begin(); it != call_prev.end(); it++)
		{
			if(*it == call_gpb)
			{
				addPrev(w, w);
				addNext(w, w);

				continue;
			}

			remPrev(*it, call_gpb);
			addNext(fend_c, *it);
			addPrev(*it, fend_c);
		}

		GPB_count++;
	}

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nGPG After Inlining Call GPB %d\n", call_gpb);
	printGPG(caller);

	if(checkGPGStructure(caller, true))
	{
		fprintf(dump_file,"\nHigh Inlining Alert\n");
		fflush(dump_file);
		printGPG(caller);
		fflush(dump_file);
		generateDotFileForGPG(caller, true, "call");
		g_callee.generateDotFileForGPG(callee, true, "call");
		exit(1);
	}
	#endif

	new_gpbs = getGPBs();

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nOLD GPBS\n");
	print_set_integers(old_gpbs);
	fflush(dump_file);
	fprintf(dump_file, "\nNEW GPBS\n");
	print_set_integers(new_gpbs);
	fflush(dump_file);
	#endif

	set_difference(new_gpbs.begin(), new_gpbs.end(), old_gpbs.begin(), old_gpbs.end(), inserter(to_be_analyzed, to_be_analyzed.end()));

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nAfter Inlining the call at GPB %d in GPG of Function %s of the Callee %s\n", call_gpb, cgraph_node_name(caller), cgraph_node_name(callee));
	fflush(dump_file);
	printInitialGPG(caller);
	fflush(dump_file);
	fprintf(dump_file, "\nNew GPBs\n");
	print_set_integers(getGPBs());
	fflush(dump_file);
	#endif

	#if PROFILING
	RETURN(to_be_analyzed);
	#else
	return(to_be_analyzed);
	#endif
}

void GPG::replaceIndirectCallGPB(unsigned int gpb_id, unsigned int cnode_num, basic_block bb)
{
	unsigned int exit = getExitGPB();
	gpu_id_type cgpu;

	GPB gpb = gpb_map[gpb_id];
	definitions callees;

	gpb.resetIndirectCallBlock();
	gpb.setIndirectCallees(callees);

	GPUSet gpus, maydef, mustdef, rout;

	gpus = DownwardsExposedMayDefinitions[cnode_num]; 
	rout = ROUT[exit];	

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		cgpu = getCopyGPU(get<0>(*it));

		if(rout.find(cgpu) != rout.end())
		{
			maydef.insert(*it);
		} 
		else
		{
			mustdef.insert(*it);
		}
	}

	if(maydef.empty())
	{
		gpb.setOrigGPUs(mustdef);
//		gpb.setGPUs(gpus);
	}
	else
	{
		GPB temp_gpb;

		gpb.setOrigGPUs(maydef);

		struct cgraph_node *cnode = func_numbering[cnode_num];
		unsigned int x = GPB_count++;

		GPBSet call_sites = getCallSites();
	
		if(call_sites.find(gpb_id) != call_sites.end())
		{
			call_sites.erase(gpb_id);
			call_sites.insert(x);

			GPBSet callee = call_site_map[cnode_num][gpb_id];
			GPBSet ttset;
		
			ttset = call_site_map[cnode_num][x];
			ttset.insert(callee.begin(), callee.end());
			call_site_map[cnode_num][x] = ttset;

			call_site_map[cnode_num].erase(gpb_id);	

			setCallSites(call_sites);
		}		

		GPBSet preds, succs, t_preds, t_succs, temp;
		preds = getPrev(gpb_id);
		succs = getNext(gpb_id);
		t_succs = succs;
		t_succs.insert(gpb_id);
		t_preds.insert(x);

		if(succs.find(gpb_id) != succs.end())
		{
			succs.erase(gpb_id);
			succs.insert(x);
		}

		setPrev(gpb_id, t_preds);
		setNext(gpb_id, succs);

		GPB new_gpb;
		new_gpb.setId(x);
		setPrev(x, preds);
		setNext(x, t_succs);

		new_gpb.setBBIndex(bb->index);

		new_gpb.setOrigGPUs(mustdef);

		for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
		{
			if(*it == gpb_id || *it == x)
				continue;

			remNext(*it, gpb_id);
			addNext(*it, x);
		}	

		for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
		{
			if(*it == gpb_id || *it == x)
				continue;

			addPrev(*it, x);
		}

		#if 0
		temp = BB_START[cnode_num][bb->index];
		temp.erase(gpb_id);
		temp.insert(x);
		BB_START[cnode_num][bb->index] = temp;

		temp = BB_END[cnode_num][bb->index];
		temp.erase(gpb_id);
		temp.insert(x);
		BB_END[cnode_num][bb->index] = temp;

//		temp = ((block_information *)(bb->aux))->sblocks;
//		((block_information *)(bb->aux))->sblocks = temp;
		#endif

		#if 0
		temp = ori_red_map[cnode_num][bb->index];
		temp.insert(x);
		ori_red_map[cnode_num][bb->index] = temp;
		#endif

		gpb_map[x] = new_gpb;

		GPBSet gpbs = getGPBs();
		gpbs.insert(x);
		setGPBs(gpbs);

		if(gpb_id == getEntryGPB())
		{
			setEntryGPB(x);
		}

		if(gpb_id == getExitGPB())
		{
			setExitGPB(x);
		}
	}

	gpb_map[gpb_id] = gpb;
}

void GPG::replaceDirectCallGPB(unsigned int gpb_id, unsigned int cnode_num, basic_block bb)
{
	unsigned int exit = getExitGPB();
	gpu_id_type cgpu;

	GPB gpb = gpb_map[gpb_id];
	definitions callees;

	gpb.resetCallBlock();
	gpb.setCallee(0);

	GPUSet gpus, maydef, mustdef, rout;

	gpus = DownwardsExposedMayDefinitions[cnode_num]; 
	rout = ROUT[exit];	

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		cgpu = getCopyGPU(get<0>(*it));

		if(rout.find(cgpu) != rout.end())
		{
			maydef.insert(*it);
		} 
		else
		{
			mustdef.insert(*it);
		}
	}

	if(maydef.empty())
	{
		gpb.setOrigGPUs(mustdef);
//		gpb.setGPUs(gpus);
	}
	else
	{
		GPB temp_gpb;

		gpb.setOrigGPUs(maydef);

		struct cgraph_node *cnode = func_numbering[cnode_num];
		unsigned int x = GPB_count++;

		GPBSet call_sites = getCallSites();
	
		if(call_sites.find(gpb_id) != call_sites.end())
		{
			call_sites.erase(gpb_id);
			call_sites.insert(x);

			GPBSet callee = call_site_map[cnode_num][gpb_id];
			GPBSet ttset;
		
			ttset = call_site_map[cnode_num][x];
			ttset.insert(callee.begin(), callee.end());
			call_site_map[cnode_num][x] = ttset;

			call_site_map[cnode_num].erase(gpb_id);	

			setCallSites(call_sites);
		}

		GPBSet preds, succs, t_preds, t_succs, temp;
		preds = getPrev(gpb_id);
		succs = getNext(gpb_id);
		t_succs = succs;
		t_succs.insert(gpb_id);
		t_preds.insert(x);

		if(succs.find(gpb_id) != succs.end())
		{
			succs.erase(gpb_id);
			succs.insert(x);
		}

		setPrev(gpb_id, t_preds);
		setNext(gpb_id, succs);

		GPB new_gpb;
		new_gpb.setId(x);
		setPrev(x, preds);
		setNext(x, t_succs);

		new_gpb.setBBIndex(bb->index);

		new_gpb.setOrigGPUs(mustdef);

		for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
		{
			if(*it == gpb_id || *it == x)
				continue;

			remNext(*it, gpb_id);
			addNext(*it, x);
		}	

		for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
		{
			if(*it == gpb_id || *it == x)
				continue;

			addPrev(*it, x);
		}

		#if 0
		temp = BB_START[cnode_num][bb->index];
		temp.erase(gpb_id);
		temp.insert(x);
		BB_START[cnode_num][bb->index] = temp;

		temp = BB_END[cnode_num][bb->index];
		temp.erase(gpb_id);
		temp.insert(x);
		BB_END[cnode_num][bb->index] = temp;

//		temp = ((block_information *)(bb->aux))->sblocks;
//		((block_information *)(bb->aux))->sblocks = temp;
		#endif

		#if 0
		temp = ori_red_map[cnode_num][bb->index];
		temp.insert(x);
		ori_red_map[cnode_num][bb->index] = temp;
		#endif

		gpb_map[x] = new_gpb;

		GPBSet gpbs = getGPBs();
		gpbs.insert(x);
		setGPBs(gpbs);

		if(gpb_id == getEntryGPB())
		{
			setEntryGPB(x);
		}

		if(gpb_id == getExitGPB())
		{
			setExitGPB(x);
		}
	}

	gpb_map[gpb_id] = gpb;
}

void GPG::eraseDirectCallGPB(unsigned int gpb_id, unsigned int cnode_num)
{
	GPB gpb = gpb_map[gpb_id];

	gpb.resetCallBlock();
	gpb.setCallee(0);

	GPUSet gpus;
	gpb.setOrigGPUs(gpus);
//	gpb.setGPUs(gpus);

	gpb_map[gpb_id] = gpb;
}

void GPG::eraseIndirectCallGPB(unsigned int gpb_id, unsigned int cnode_num)
{
	GPB gpb = gpb_map[gpb_id];
	definitions callees;

	gpb.resetIndirectCallBlock();
	gpb.setIndirectCallees(callees);

	GPUSet gpus;
	gpb.setOrigGPUs(gpus);
//	gpb.setGPUs(gpus);

	gpb_map[gpb_id] = gpb;
}

void GPG::computeDownwardsExposedDefinitions(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPUSet queued = Queued[cnode_num];

	unsigned int exit = getExitGPB();
	GPUSet gpus, rout, maygen, mustkill;
	gpu_id_type cgpu;
	Node node;
	node_id_type nid;
	unsigned int var;
	IndirectionList list;

	rout = ROUT[exit];

	rout.insert(queued.begin(), queued.end());	

	for(GPUSet::iterator it = rout.begin(); it != rout.end(); it++)
	{
		if(isBoundaryGPU(*it))
		{
			continue;
		}

		nid = get<0>(*it);
		node = getNode(nid);
		var = node.getVarIndex();

		if(!isInScope(var, cnode))
		{
			continue;
		}

		#if 0
		fprintf(dump_file, "\nChecking BD for GPU\n");
		print_GPU(*it);
		#endif

		cgpu = getCopyGPU(nid);

		#if 0
		fprintf(dump_file, "\nCorresponding BD\n");
		print_GPU(cgpu);
		#endif

		if(rout.find(cgpu) != rout.end())
		{
			maygen.insert(*it);
		} 
		else
		{
			mustkill.insert(*it);
		}

		#if 0
		list = node.getList();

		if(CDV.find(var) == CDV.end())
		{
//			if(list.Length() == 1)
			{
				cgpu = getCopyGPU(nid);

				fprintf(dump_file, "\nCorresponding BD\n");
				print_GPU(cgpu);

				if(rout.find(cgpu) != rout.end())
				{
					maygen.insert(*it);
				} 
				else
				{
					mustkill.insert(*it);
				}
			}
		}
		#endif
	}

	DownwardsExposedMayDefinitions[cnode_num] = maygen; 
	DownwardsExposedMustDefinitions[cnode_num] = mustkill; 

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nmaygen\n");
	printSetOfGPUs(maygen);
	fprintf(dump_file, "\nmustkill\n");
	printSetOfGPUs(mustkill);
	#endif
}

void GPG::insertParaGPBForIndirectCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee, GPUSet res)
{
	struct cgraph_node *cnode = func_numbering[caller_rep];

	GPB call = gpb_map[call_gpb];

	GPBSet preds, temp, succs;
	GPUSet temp_set;

	preds = getPrev(call_gpb);
	preds.insert(call_gpb);

	GPB para_gpb, temp_gpb;

	unsigned int  x = GPB_count++;
	unsigned int start = g_callee.getEntryGPB();

	if(getEntryGPB() == call_gpb)
	{
		setEntryGPB(x);
	}

	para_gpb.setId(x);

	setPrev(x, preds);

	succs.insert(start+x);

	setNext(x, succs);

	para_gpb.setBBIndex(bb->index);

	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		remNext(*it, call_gpb);
		addNext(*it, x);
	}	

	#if 0
	temp = BB_START[caller_rep][bb->index];
	temp.erase(call_gpb);
	temp.insert(x);
	BB_START[caller_rep][bb->index] = temp;

//	temp = ((block_information *)(bb->aux))->sblocks;
//	((block_information *)(bb->aux))->sblocks = temp;
	#endif

	#if 0
	temp = ori_red_map[caller_rep][bb->index];
	temp.erase(call_gpb);
	temp.insert(x);
	ori_red_map[caller_rep][bb->index] = temp;
	#endif

	GPBSet gpbs = getGPBs();
	gpbs.erase(call_gpb);
	gpbs.insert(x);
	setGPBs(gpbs);

	para_gpb.setOrigGPUs(res);
//	para_gpb.setGPUs(res);

	gpb_map[x] = para_gpb;	
}

void GPG::insertRetGPBForIndirectCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, unsigned int x, GPG g_callee, GPUSet res)
{
	struct cgraph_node *caller = func_numbering[caller_rep];
	struct cgraph_node *callee = func_numbering[callee_rep];

	GPB call = gpb_map[call_gpb];

	GPBSet temp, succs, preds;

	unsigned int end = g_callee.getExitGPB();
	GPUSet temp_set;

	GPB ret_gpb, temp_gpb;

	ret_gpb.setId(++GPB_count);
	ret_gpb.setBBIndex(bb->index);
	GPB_count++;

	unsigned int y = GPB_count - 1;

	if(getExitGPB() == call_gpb)
	{
		setExitGPB(y);
	}

	preds.insert(end+x);

	setPrev(y, preds);

	succs = getNext(call_gpb);
	succs.erase(call_gpb);

	setNext(y, succs);

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		remPrev(*it, call_gpb);
		addPrev(*it, y);
	}

	remNext((end+x), call_gpb);
	addNext((end+x), y);

	GPB end_gpb = gpb_map[end+x];
//	end_gpb.setBBIndex(bb->index);
	gpb_map[end+x] = end_gpb;

	#if 0
	temp = BB_END[caller_rep][bb->index];
	temp.erase(call_gpb);
	temp.insert(y);
	BB_END[caller_rep][bb->index] = temp;

//	temp = ((block_information *)(bb->aux))->eblocks;
//	((block_information *)(bb->aux))->eblocks = temp;
	#endif

	#if 0
	temp = ori_red_map[caller_rep][bb->index];
	temp.insert(y);
	ori_red_map[caller_rep][bb->index] = temp;
	#endif

	GPBSet gpbs = getGPBs();
	gpbs.insert(y);
	setGPBs(gpbs);

	ret_gpb.setOrigGPUs(res);
//	ret_gpb.setGPUs(res);

	gpb_map[y] = ret_gpb;
}

GPBSet GPG::inlineIndirectCall(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee)
{
	struct cgraph_node *callee = func_numbering[callee_rep];
	struct cgraph_node *caller = func_numbering[caller_rep];

	#if 0
	fprintf(dump_file, "\nInline Call for GPB %d in GPG of Function %s for Callee %s\nSuccs: ", call_gpb, cgraph_node_name(caller), cgraph_node_name(callee));
	fflush(dump_file);
	print_set_integers(getPrev(call_gpb));
	fflush(dump_file);
	fprintf(dump_file, "\nPreds: ");
	fflush(dump_file);
	print_set_integers(getNext(call_gpb));
	fflush(dump_file);
	fprintf(dump_file, "\n\n");
	fflush(dump_file);
	#endif

	GPBSet to_be_analyzed;

	#if 0
	fprintf(dump_file, "\nGPB Count = %d\n", GPB_count);
	fflush(dump_file);

	fprintf(dump_file, "\ng_callee of Callee Function %s\n", cgraph_node_name(callee));
	fflush(dump_file);
	g_callee.printGPG(callee);
	fflush(dump_file);

	fprintf(dump_file, "\ng_caller of Caller Function %s\n", cgraph_node_name(caller));
	fflush(dump_file);
	printInitialGPG(caller);
	fflush(dump_file);
	#endif

	#if 0
	fprintf(dump_file, "\ng_caller of Caller Function %s\n", cgraph_node_name(caller));
	fflush(dump_file);
	printInitialGPG(caller);
	fflush(dump_file);
	#endif

	GPB call = gpb_map[call_gpb];
	GPB temp_gpb, temp_gpb1;

	#if 0
	fprintf(dump_file, "\ng_caller entry %d\n", getEntryGPB());
	fflush(dump_file);
	#endif

	GPUSet para_gpus, ret_gpus;
	
	para_gpus = map_para_args_fp_call(callee_rep, caller_rep, bb);

	#if 0
	fprintf(dump_file, "\nComputed para_gpus\n");
	fflush(dump_file);
	#endif

	ret_gpus = getRetGPUs(bb, caller, callee, g_callee);

	#if 0
	fprintf(dump_file, "\nComputed ret_gpus\n");
	fflush(dump_file);
	
	fprintf(dump_file, "\nEmpty para_gpus %d\nEmpty ret_gpus %d\n", para_gpus.empty(), ret_gpus.empty());
	fflush(dump_file);
	#endif

	unsigned int  x;

	GPBSet gpbs_caller = getGPBs();
	GPBSet gpbs_callee = g_callee.getGPBs();

	GPBSet call_sites, ttset;

	unsigned int start, end, para, ret;

	start = g_callee.getEntryGPB();

	if(!para_gpus.empty())
	{
		insertParaGPBForDirectCall(call_gpb, callee_rep, caller_rep, bb, g_callee, para_gpus);

//		fprintf(dump_file, "\nGPB Count = %d\n", GPB_count);
//		fflush(dump_file);

		x = GPB_count - 1;

		gpbs_caller = getGPBs();

		to_be_analyzed.insert(x);
	}
	else
	{
		x = GPB_count - 1;

		gpbs_caller.erase(call_gpb);

		to_be_analyzed.insert(start+x);
	}

	#if 0
	fprintf(dump_file, "\nAfter Inserting Para GPB\n");
	printInitialGPG(caller);
	#endif

	unsigned int  b = bb->index;

//	if(gpbs_caller.find(g_caller.getEntryGPB()) != gpbs_caller.end())
//		fprintf(dump_file, "\ng_caller entry %d\n", g_caller.getEntryGPB());

	GPBSet preds, temp;

	unsigned int t;

//	fprintf(dump_file, "\nInlining Callee %s with Offset %d\n", cgraph_node_name(callee), x);
//	g_callee.printGPG(callee);

	unsigned int w;

	GPBSet call_prev;

	for(GPBSet::iterator it = gpbs_callee.begin(); it != gpbs_callee.end(); it++)
	{
		GPB new_gpb;

		temp_gpb = g_callee.gpb_map[*it];

		t = *it;
		w = t+x;

		DFP[w] = g_callee.DFP[t];

		#if 0
		if(w > 2147483640)
		{
			fprintf(dump_file, "\nOverFlow of GPB Count: w = %u, t = %u, x = %u\n", w, t, x);
	
			exit(1);
		}
		#endif

		new_gpb.setId(w);
		to_be_analyzed.insert(w);

		GPB_count = t+x;	

		temp = g_callee.getPrev(*it);

		#if 0
		fprintf(dump_file, "\nPredecessors of GPB in Callee = %d, and that in caller = %d\n", t, t+x);
		print_set_integers(temp);
		#endif

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addPrev(w, *pit+x);
		}

		if(start == *it)
		{
			if(!para_gpus.empty())
			{
				addPrev(w, x); // Adding Para GPB as a predecessor
			}
			else
			{
//				fprintf(dump_file, "\nStart GPB of callee is first GPB\n");

				if(getEntryGPB() == call_gpb)
				{
//					fprintf(dump_file, "\nSetting new Entry %d\n", w);
					setEntryGPB(w);
				}
		
				call_prev = getPrev(call_gpb);

				for(GPBSet::iterator it = call_prev.begin(); it != call_prev.end(); it++)
				{
					if(*it == call_gpb)
					{
						addPrev(w, w);
						addNext(w, w);

						continue;
					}

					remNext(*it, call_gpb);
					addPrev(w, *it);
					addNext(*it, w);
				}
			}
		}

		temp = g_callee.getNext(*it);

		#if 0
		fprintf(dump_file, "\nSuccessors of GPB in Callee = %d, and that in caller = %d\n", t, t+x);
		print_set_integers(temp);
		#endif

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addNext(w, *pit+x);
		}

		#if 0
		if(temp_gpb.isDirty())
		{
			new_gpb.setDirty();
		}
		#endif
		
		if(temp_gpb.isSymGPB())
		{
			new_gpb.setSymGPB();
			new_gpb.setCallee(callee_rep);
			new_gpb.setGPUs(temp_gpb.getGPUs());

			GPBSet temp_c = temp_gpb.getSetOfCallees();
			temp_c.insert(callee_rep);
			new_gpb.setSetOfCallees(temp_c);

			if(temp_gpb.isResolved())
			{
				new_gpb.setResolved();	
			}
			else
			{
				new_gpb.resetResolved();	
			}
		}
		else if(temp_gpb.isCallBlock())
		{
			new_gpb.setCallBlock();
			new_gpb.setCallee(temp_gpb.getCallee());
		}
		#if 0
		else if(temp_gpb.isInterval())
		{
			new_gpb.setInterval();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#endif
		#if INTDIR
		else if(temp_gpb.isIntervalDirect())
		{
			new_gpb.setIntervalDirect();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#endif
		else if(temp_gpb.isIndirectCallBlock())
		{
			new_gpb.setIndirectCallBlock();

			definitions def = temp_gpb.getIndirectCallees();

			definitions def_res;
			Node n1;	
			unsigned int var1;
			IndirectionList list1;
			node_id_type nid;

			for(definitions::iterator iit = def.begin(); iit != def.end(); iit++)
			{
				n1 = getNode(*iit);

				var1 = n1.getVarIndex();
				list1 = n1.getList();

				if(CDV.find(var1) != CDV.end())
				{
					--var1;
					Node n2(var1, list1);
					nid = n2.getNodeID();
				}
				else
				{
					nid = *iit;
				}

				def_res.insert(nid);
			}

			new_gpb.setIndirectCallees(def_res);
		}

		GPUSet gpu_set = temp_gpb.getGPUs();
		GPUSet res_gpus;
		gpu_id_type nid;
		GPBSet sid;
		stmt_info_type key_t, key_callee;

		for(GPUSet::iterator git = gpu_set.begin(); git != gpu_set.end(); git++)
		{
			nid = stripUpwardsExposed(*git);

			res_gpus.insert(nid);

			GPBSet sset;

			key_t = std::make_tuple(caller_rep, w, nid);

			key_callee = std::make_tuple(callee_rep, t, *git);

			sid = stmt_id_info[key_callee];

			sset = stmt_id_info[key_t];

			sset.insert(sid.begin(), sid.end());			

			stmt_id_info[key_t] = sset;

			#if 0
			fprintf(dump_file, "\nGPU after removing upwards exposed in inlineCall\n");
			print_GPU(nid);
			tree t = NodeType[get<0>(nid)];

			if(t != NULL)
			{
				print_node(dump_file, "\nTREE IN FI Filtering\n", t, 0);
			}
			#endif
		}
		
//		new_gpb.setGPUs(res_gpus);
		new_gpb.setOrigGPUs(res_gpus);

		new_gpb.setBBIndex(b);

		gpbs_caller.insert(t+x);

		#if 0
		temp = ori_red_map[caller_rep][bb->index];
		temp.insert(t+x);
		ori_red_map[caller_rep][bb->index] = temp;
		#endif

		gpb_map[t+x] = new_gpb;
	}

	#if 0
	std::map< unsigned int, GPG > intervals_caller, intervals_callee;
	intervals_caller = getIntervals();
	intervals_callee = g_callee.getIntervals();

	for(std::map< unsigned int, GPG >::iterator it = intervals_callee.begin(); it != intervals_callee.end(); it++)
	{	
		intervals_caller[(it->first+x)] = it->second;
	}

	setIntervals(intervals_caller);
	#endif

	setGPBs(gpbs_caller);

	#if 0
	fprintf(dump_file, "\nBefore inserting Ret Block\n");
	printGPG(caller);
	#endif	
		
	if(!ret_gpus.empty())
	{
		insertRetGPB(call_gpb, callee_rep, caller_rep, bb, x, g_callee, ret_gpus);

		to_be_analyzed.insert(GPB_count - 1);
	}
	else
	{
		unsigned int end_c = g_callee.getExitGPB();
		unsigned int fend_c = end_c+x;
		call_prev = getNext(call_gpb);

		if(getExitGPB() == call_gpb)
		{
			setExitGPB(fend_c);
		}

		for(GPBSet::iterator it = call_prev.begin(); it != call_prev.end(); it++)
		{
			if(*it == call_gpb)
			{
				addPrev(w, w);
				addNext(w, w);

				continue;
			}

			remPrev(*it, call_gpb);
			addNext(fend_c, *it);
			addPrev(*it, fend_c);
		}

		GPB_count++;
	}

//	fprintf(dump_file, "\nGPG After Inlining Call GPB %d\n", call_gpb);
//	printGPG(caller);

	#if 0	
	if(checkGPGStructure(caller, true))
	{
		fprintf(dump_file,"\nHigh Inlining Alert\n");
		fprintf(dump_file,"\nHigh Inlining Alert123 %s\n", cgraph_node_name(callee));
		fflush(dump_file);
		printGPG(caller);
		fflush(dump_file);
		generateDotFileForGPG(caller, true, "call");
		g_callee.generateDotFileForGPG(callee, true, "call");
		exit(1);
	}
	#endif

	return(to_be_analyzed);
}

GPBSet GPG::inlineIndirectCallAltLatest(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee)
{
	GPBSet to_be_analyzed;

	GPUSet array_data_caller, array_data_callee;

	array_data_callee = flowInsensitiveInformation[callee_rep];
	array_data_caller = flowInsensitiveInformation[caller_rep];

	for(GPUSet::iterator it = array_data_callee.begin(); it != array_data_callee.end(); it++)
	{
		array_data_caller.insert(stripUpwardsExposed(*it));
	}

	flowInsensitiveInformation[caller_rep] = array_data_caller; 

	struct cgraph_node *callee = func_numbering[callee_rep];
	struct cgraph_node *caller = func_numbering[caller_rep];

//	fprintf(dump_file, "\nInside inlineIndirectCall\n");
//	g_caller.printGPG(caller);

	GPB call = gpb_map[call_gpb];
	GPB temp_gpb, temp_gpb1;

	GPUSet para_gpus, ret_gpus;
	
	para_gpus = map_para_args_fp_call(callee_rep, caller_rep, bb);

	ret_gpus = getRetGPUs(bb, caller, callee, g_callee);

	if(para_gpus.empty() && ret_gpus.empty() && g_callee.isIdentityGPG(callee, false))
	{
		eliminateEmptyGPB(call_gpb, caller);
	}

	unsigned int x;

	GPBSet gpbs_caller = getGPBs();
	GPBSet gpbs_callee = g_callee.getGPBs();

	GPBSet call_sites, ttset;

	unsigned int start, end, para, ret;

	start = g_callee.getEntryGPB();

	if(!para_gpus.empty())
	{
		insertParaGPBForIndirectCall(call_gpb, callee_rep, caller_rep, bb, g_callee, para_gpus);

		x = GPB_count - 1;
		
		gpbs_caller = getGPBs();
		
		call_sites = getCallSites();
		call_sites.insert(x);
		setCallSites(call_sites);

		ttset = call_site_map[caller_rep][x];	
		ttset.insert(callee_rep);	
		call_site_map[caller_rep][x] = ttset;	

		to_be_analyzed.insert(x);
	}
	else
	{
		x = GPB_count;
		
		gpbs_caller.erase(call_gpb);

		call_sites = getCallSites();
		call_sites.insert(start+x);
		setCallSites(call_sites);

		ttset = call_site_map[caller_rep][start+x];	
		ttset.insert(callee_rep);	
		call_site_map[caller_rep][start+x] = ttset;	

		to_be_analyzed.insert(start+x);
	}

	unsigned int  b = bb->index;

	GPBSet preds, temp;

	unsigned int t, w;

	GPBSet call_prev;

	for(GPBSet::iterator it = gpbs_callee.begin(); it != gpbs_callee.end(); it++)
	{
		GPB new_gpb;

		temp_gpb = g_callee.gpb_map[*it];

		t = temp_gpb.getId();
		w = t+x;

		new_gpb.setId(w);

		to_be_analyzed.insert(w);

		GPB_count = w;	

		temp = g_callee.getPrev(*it);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addPrev(w, *pit+x);
		}

		if(start == *it)
		{
			if(!para_gpus.empty())
			{
				addPrev(w, x); // Adding Para GPB as a predecessor
			}
			else
			{
				if(getEntryGPB() == call_gpb)
				{
					setEntryGPB(w);
				}

				call_prev = getPrev(call_gpb);

				for(GPBSet::iterator it = call_prev.begin(); it != call_prev.end(); it++)
				{
					if(*it == call_gpb)
					{
						addPrev(w, w);
						addNext(w, w);

						continue;
					}

					remNext(*it, call_gpb);
					addPrev(w, *it);
					addNext(*it, w);
				}
			}
		}

		temp = g_callee.getNext(*it);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addNext(w, *pit+x);
		}

		if(temp_gpb.isDirty())
		{
			new_gpb.setDirty();
		}

		if(temp_gpb.isCallBlock())
		{
			new_gpb.setCallBlock();
			new_gpb.setCallee(temp_gpb.getCallee());
		}
		#if 0
		else if(temp_gpb.isInterval())
		{
			new_gpb.setInterval();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#endif
		#if INTDIR
		else if(temp_gpb.isIntervalDirect())
		{
			new_gpb.setIntervalDirect();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#endif
		else if(temp_gpb.isIndirectCallBlock())
		{
			new_gpb.setIndirectCallBlock();

			definitions def = temp_gpb.getIndirectCallees();

			definitions d_res;
			Node n1;	
			unsigned int var1;
			IndirectionList list1;
			node_id_type nid;

			for(definitions::iterator lit = def.begin(); lit != def.end(); lit++)
			{
				n1 = getNode(*lit);

				var1 = n1.getVarIndex();
				list1 = n1.getList();

				if(CDV.find(var1) != CDV.end())
				{
					--var1;
					Node n2(var1, list1);
					nid = n2.getNodeID();
				}
				else
				{
					nid = *lit;
				}
				
				d_res.insert(nid);
			}

			new_gpb.setIndirectCallees(d_res);
		}

		GPUSet gpu_set = temp_gpb.getGPUs();
		GPUSet res_gpus;

		for(GPUSet::iterator git = gpu_set.begin(); git != gpu_set.end(); git++)
		{
			res_gpus.insert(stripUpwardsExposed(*git));
		}
		
//		new_gpb.setGPUs(res_gpus);
		new_gpb.setOrigGPUs(res_gpus);

		new_gpb.setBBIndex(b);

		gpbs_caller.insert(w);

		#if 0
		temp = ori_red_map[caller_rep][bb->index];
		temp.insert(w);
		ori_red_map[caller_rep][bb->index] = temp;
		#endif

		gpb_map[w] = new_gpb;
	}

	#if 0
	std::map< unsigned int, GPG > intervals_caller, intervals_callee;
	intervals_caller = getIntervals();
	intervals_callee = g_callee.getIntervals();

	for(std::map< unsigned int, GPG >::iterator it = intervals_callee.begin(); it != intervals_callee.end(); it++)
	{	
		intervals_caller[(it->first+x)] = it->second;
	}

	setIntervals(intervals_caller);
	#endif

	setGPBs(gpbs_caller);

	if(!ret_gpus.empty())
	{
		insertRetGPBForIndirectCall(call_gpb, callee_rep, caller_rep, bb, x, g_callee, ret_gpus);
		
		to_be_analyzed.insert(GPB_count - 1);
	}
	else
	{
		unsigned int end_c = g_callee.getExitGPB();
		unsigned int fend_c = end_c+x;
		call_prev = getNext(call_gpb);

		if(getExitGPB() == call_gpb)
		{
			setExitGPB(fend_c);
		}

		for(GPBSet::iterator it = call_prev.begin(); it != call_prev.end(); it++)
		{
			if(*it == call_gpb)
			{
				addPrev(w, w);
				addNext(w, w);

				continue;
			}

			remPrev(*it, call_gpb);
			addNext(fend_c, *it);
			addPrev(*it, fend_c);
		}

		GPB_count++;
	}

	return(to_be_analyzed);
}

void GPG::inlineIndirectCallAlt(unsigned int call_gpb, unsigned int callee_rep, unsigned int caller_rep, basic_block bb, GPG g_callee)
{
	GPUSet array_data_caller, array_data_callee;

	array_data_callee = flowInsensitiveInformation[callee_rep];
	array_data_caller = flowInsensitiveInformation[caller_rep];

	for(GPUSet::iterator it = array_data_callee.begin(); it != array_data_callee.end(); it++)
	{
		array_data_caller.insert(stripUpwardsExposed(*it));
	}

	flowInsensitiveInformation[caller_rep] = array_data_caller; 

	struct cgraph_node *callee = func_numbering[callee_rep];
	struct cgraph_node *caller = func_numbering[caller_rep];

	if(g_callee.isTop())
	{
		eliminateGPB(call_gpb, caller);

		return;

//		return;
	}

//	fprintf(dump_file, "\nInside inlineIndirectCall\n");
//	g_caller.printGPG(caller);

	GPB call = gpb_map[call_gpb];
	GPB temp_gpb, temp_gpb1;
	GPUSet para_gpus, ret_gpus;

	insertParaGPBForIndirectCall(call_gpb, callee_rep, caller_rep, bb, g_callee, para_gpus);

	unsigned int  x = GPB_count - 1;

	#if 0
	GPBSet call_sites = getCallSites();
	call_sites.insert(x);
	setCallSites(call_sites);

	GPBSet ttset = call_site_map[caller_rep][x];
	ttset.insert(callee_rep);
	call_site_map[caller_rep][x] = ttset;
	#endif

	unsigned int  b = bb->index;

	GPBSet gpbs_caller = getGPBs();
	GPBSet gpbs_callee = g_callee.getGPBs();

	GPBSet preds, temp;

	unsigned int start, end, para, ret;

	start = g_callee.getEntryGPB();
	unsigned int t, w;

	for(GPBSet::iterator it = gpbs_callee.begin(); it != gpbs_callee.end(); it++)
	{
		GPB new_gpb;

		temp_gpb = gpb_map[*it];

		t = temp_gpb.getId();
		w = t+x;

		new_gpb.setId(w);

		GPB_count = w;	

		temp = g_callee.getPrev(*it);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addPrev(w, *pit+x);
		}

		if(start == *it)
		{
			addPrev(w, x); // Adding Para GPB as a predecessor
		}

		temp = g_callee.getNext(*it);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addNext(w, *pit+x);
		}

		if(temp_gpb.isCallBlock())
		{
			new_gpb.setCallBlock();
			new_gpb.setCallee(temp_gpb.getCallee());
		}
		else if(temp_gpb.isInterval())
		{
			new_gpb.setInterval();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#if INTDIR
		else if(temp_gpb.isIntervalDirect())
		{
			new_gpb.setIntervalDirect();

			GPBSet interval_set, tempi;
			tempi = temp_gpb.getIntervalSet();

			#if 0
			for(GPBSet::iterator wit = tempi.begin(); wit != tempi.end(); wit++)
			{
				interval_set.insert((*wit+x));
			}
			#endif

			new_gpb.setIntervalSet(tempi);
		}
		#endif
		else if(temp_gpb.isIndirectCallBlock())
		{
			new_gpb.setIndirectCallBlock();

			definitions def = temp_gpb.getIndirectCallees();

			definitions d_res;
			Node n1;	
			unsigned int var1;
			IndirectionList list1;
			node_id_type nid;

			for(definitions::iterator lit = def.begin(); lit != def.end(); lit++)
			{
				n1 = getNode(*lit);

				var1 = n1.getVarIndex();
				list1 = n1.getList();

				if(CDV.find(var1) != CDV.end())
				{
					--var1;
					Node n2(var1, list1);
					nid = n2.getNodeID();
				}
				else
				{
					nid = *lit;
				}
				
				d_res.insert(nid);
			}

			new_gpb.setIndirectCallees(d_res);
		}

		GPUSet gpu_set = temp_gpb.getGPUs();
		GPUSet res_gpus;

		for(GPUSet::iterator git = gpu_set.begin(); git != gpu_set.end(); git++)
		{
			res_gpus.insert(stripUpwardsExposed(*git));
		}
		
//		new_gpb.setGPUs(res_gpus);
		new_gpb.setOrigGPUs(res_gpus);

		new_gpb.setBBIndex(b);

		gpbs_caller.insert(w);

		#if 0
		temp = ori_red_map[caller_rep][bb->index];
		temp.insert(w);
		ori_red_map[caller_rep][bb->index] = temp;
		#endif

		gpb_map[w] = new_gpb;
	}

	std::map< unsigned int, GPG > intervals_caller, intervals_callee;
	intervals_caller = getIntervals();
	intervals_callee = g_callee.getIntervals();

	for(std::map< unsigned int, GPG >::iterator it = intervals_callee.begin(); it != intervals_callee.end(); it++)
	{	
		intervals_caller[(it->first+x)] = it->second;
	}

	setGPBs(gpbs_caller);
	setIntervals(intervals_caller);

	insertRetGPBForIndirectCall(call_gpb, callee_rep, caller_rep, bb, x, g_callee, ret_gpus);

	return;
}

void GPG::checkForCoalescing(struct cgraph_node *cnode)
{
	#if 0
	fprintf(dump_file,"\nInside checkForCoalescing for Function %s\nGPG g before coalescing\n", cgraph_node_name(cnode));
	fflush(dump_file);
	printGPG(cnode);
	fflush(dump_file);
	#endif

	GPBSet gpbs = getGPBs();
	unsigned int start, end;
	start = getEntryGPB();
	end = getExitGPB();
	std::pair< unsigned int, unsigned int > ptemp;
	GPBSet succs, preds;
	unsigned int next, prev;
	GPB gpb1, gpb2;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb1 = gpb_map[*it];

		#if 1
		if(*it == start || *it == end)
		{
			continue;
		}
		#endif

	
		#if 0	
		fprintf(dump_file, "\nChecking GPB %d\n", *it);
		fflush(dump_file);
		#endif

		#if 0
		#if INTDIR
		if(gpb1.isCallBlock() || gpb1.isIndirectCallBlock() || gpb1.isInterval() || gpb1.isIntervalDirect())
		#else
		if(gpb1.isCallBlock() || gpb1.isIndirectCallBlock() || gpb1.isInterval())
		#endif
		#endif
		if(gpb1.isCallBlock() || gpb1.isSymGPB() || gpb1.isIndirectCallBlock())
		{
			continue;
		}

		succs = getNext(*it);	

		#if 0	
		fprintf(dump_file, "\nChecking Succs of GPB %d\n", *it);
		fflush(dump_file);
		print_set_integers(succs);
		fflush(dump_file);
		#endif

		if(succs.size() == 1)
		{
			#if 0
			fprintf(dump_file, "\nSingle Successor of GPB %d\n", *it);
			fflush(dump_file);
			#endif

			next = *(succs.begin());

			#if 1
			if(next == start || next == end)
			{
				continue;
			}
			#endif

			gpb2 = gpb_map[next];

			#if 0
			#if INTDIR 
			if(gpb2.isCallBlock() || gpb2.isIndirectCallBlock() || gpb2.isInterval() || gpb2.isIntervalDirect())
			#else
			if(gpb2.isCallBlock() || gpb2.isIndirectCallBlock() || gpb2.isInterval())
			#endif
			#endif
			if(gpb2.isCallBlock() || gpb2.isSymGPB() || gpb2.isIndirectCallBlock())
			{
				continue;
			}

			preds = getPrev(next);

			if(preds.size() == 1)
			{
				prev = *(preds.begin());

				if(next == prev)
				{
					continue;
				}

				if(prev == *it)
				{
					coalesceGPBs(*it, next, cnode);

					return;
				}
			}
			#if 0
			if(isDomPDom(*it, next, cnode))
			{
				#if 0
				fprintf(dump_file, "\nChecking Dom-Pdom of %d with its Successor %d\n", *it, next);
				fflush(dump_file);
				#endif

				g.coalesceGPBs(*it, next, cnode);

				return g;
			}
			#endif
		}
		#if 1
		else
		{
			GPUSet ggpus1, ggpus2;

			ggpus1 = gpb1.getGPUs();

			for(GPBSet::iterator ssit = succs.begin(); ssit != succs.end(); ssit++)
			{
				if(*ssit == start || *ssit == end)
				{	
					continue;
				}

				gpb2 = gpb_map[*ssit];

				#if 0
				#if INTDIR
				if(gpb2.isCallBlock() || gpb2.isIndirectCallBlock() || gpb2.isInterval() || gpb2.isIntervalDirect())
				#else
				if(gpb2.isCallBlock() || gpb2.isIndirectCallBlock() || gpb2.isInterval())
				#endif
				#endif	
				if(gpb2.isCallBlock() || gpb2.isSymGPB() || gpb2.isIndirectCallBlock())
				{
					continue;
				}

				ggpus2 = gpb2.getGPUs();

				GPBSet prevt = getPrev(*ssit);

				if(prevt.size() < 2)
				{
					continue;
				}

				if(ggpus1 == ggpus2)
				{
					coalesceAdjGPBs(*it, *ssit, cnode);

					return;
				}				
				else // Perform Aggressive Optimizations when the # GPBs exceeds GPB_THRESH
				{
					if(gpbs.size() <= GPB_THRESH)
					{
						continue;
					}

					ggpus1.insert(ggpus2.begin(), ggpus2.end());

					if(areAdvancingGPUs(ggpus1))
					{
						coalesceAdjGPBs(*it, *ssit, cnode);

						return;
					}
					else if(areSameSourceGPUs(ggpus1))
					{
						coalesceAdjGPBs(*it, *ssit, cnode);

						return;
					}

					#if 0
					if(areStructHeapData(ggpus1) && areStructHeapData(ggpus2))
					{
						coalesceAdjGPBs(*it, *ssit, cnode);

						return;
					}
					#endif
				}
			}
		}
		#endif
	}
}

void GPG::sanitize(struct cgraph_node *cnode, bool orig) // orig = true => Original GPUs, orig = false => Reduced GPUs
{
	unsigned int cnum = ((function_info *)(cnode->aux))->func_num;

	if(isTop())
		return;

	GPBSet gpbs = getGPBs();

	#if 0
	if(gpbs.size() > 400)
	{
		fprintf(stderr, "\nToo many GPBs in sanitizeInitialGPG for Function %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		fprintf(dump_file, "\nToo many GPBs  in sanitizeInitialGPG for Function %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		printInitialGPG(cnode);
		generateDotFileForInitialGPG(cnode);
		fflush(dump_file);
		exit(1);
	}
	#endif

	GPBSet e_gpbs = returnEmptyGPBs(cnum, orig);

	unsigned int start, end;
	start = getEntryGPB();
	end = getExitGPB();
	GPBSet eg;
	eg.insert(start);
	eg.insert(end);

	
	if(e_gpbs.size() <= 2)
	{
	}
	else if(e_gpbs.size() > 2)
	{
		fprintf(stderr, "\nExcessive Empty GPBs in sanitize  for Function %s\n", cgraph_node_name(cnode));
		fprintf(dump_file, "\nExcessive Empty GPBs  in sanitize for Function %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		printInitialGPG(cnode);
		generateDotFileForGPG(cnode, orig, "san");
		fflush(dump_file);
		exit(1);
	}
	else
	{
		if(!(e_gpbs == eg))
		{
			fprintf(stderr, "\nEmpty GPBs Other than Entry and Exit  in sanitizeGPG for Function %s\n", cgraph_node_name(cnode));
			fprintf(dump_file, "\nEmpty GPBs Other than Entry and Exit in sanitizeGPG  for Function %s\n", cgraph_node_name(cnode));
			fflush(dump_file);
			printInitialGPG(cnode);
			generateDotFileForGPG(cnode, orig, "san");
			fflush(dump_file);
			exit(1);
		}
	}

	#if 0
	if(containsCycle(cnode))
	{
		fprintf(stderr,"\nCycle in GPG Alert\n");
		fflush(dump_file);
		printGPG();
		fflush(dump_file);
		exit(1);
	}
	#endif

	#if 0
	if(!reachability(cnode))
	{
		fprintf(stderr,"\nReachability Issue\n");
		fflush(stderr);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}
	#endif
	
	if(checkGPGStructure(cnode, orig))
	{
		fprintf(stderr,"\nSucc - Pred Problem in sanitizeGPG for Function %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		printInitialGPG(cnode);
		generateDotFileForGPG(cnode, orig, "san");
		fflush(dump_file);
		exit(1);
	}

	#if 0
	if(maxNodeCount())
	{
		fprintf(stderr,"\nMax Node Set Alert\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);

	}
	#endif

	#if 0
	fprintf(dump_file,"\nAt the end of sanitize function for function\n");
	fflush(dump_file);
	#endif
}

void GPG::generateDotFileForGPG(struct cgraph_node *cnode, bool orig, string name)
{
	unsigned int cnum = ((function_info *)(cnode->aux))->func_num;

	GPBSet succs, gpbs;
	gpbs = getGPBs();
	GPB gpb;
	GPUSet gpus;

	FILE *fptr;
	char buf[0x100];
	snprintf(buf, sizeof(buf), "%s_%s.dot", cgraph_node_name(cnode), name.c_str());
	fptr = fopen(buf, "w");
	fprintf(fptr, "strict digraph{ \n{\n");

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isSymGPB())
		{
			fprintf(fptr, "%d [color=pink]\n", gpb.getCallee());
		}
		else if(gpb.isCallBlock())
		{
			fprintf(fptr, "%d [color=green]\n", gpb.getCallee());
		}
		else if(gpb.isInterval())
		{
			fprintf(fptr, "%d [color=yellow]\n", *it);
		}
		#if INTDIR
		else if(gpb.isIntervalDirect())
		{
			fprintf(fptr, "%d [color=gray]\n", *it);
		}
		#endif
		else if(gpb.isIndirectCallBlock())
		{
			fprintf(fptr, "%d [color=red]\n", *it);
		}
		else if(orig)
		{
			gpus = gpb.getOrigGPUs();

			if(gpus.empty())
				fprintf(fptr, "%d [color=blue]\n", *it);
		}
		else if(!orig)
		{
			gpus = gpb.getGPUs();

			if(gpus.empty())
				fprintf(fptr, "%d [color=blue]\n", *it);
		}

	}

	fprintf(fptr, "}\n");

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		succs = getNext(*it);

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			fprintf(fptr, "%d -> %d\n", *it, *sit);
		}
	}	

	fprintf(fptr, "}\n");
	fclose(fptr);
}

void GPG::localOptimizations(struct cgraph_node *cnode, bool orig)
{
//	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	if(!isTop())
	{
//		eliminateAllEmptyGPBs(cnode, orig); // Eliminate Empty GPBs
		eliminateEmptyGPBsDFA(cnode, orig);
	}
}

void GPG::coalesceStartGPB(struct cgraph_node *cnode)
{
	unsigned int start;

	start = getEntryGPB();

	GPBSet succs, preds;

	succs = getNext(start);

	unsigned int s;

	GPB gpb;

	if(succs.size() == 1)
	{
		s = *(succs.begin());

		gpb = gpb_map[s];

		if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock())
		{
			return;
		}

		preds = getPrev(s);

		if(preds.size() == 1)
		{
			if(start == *(preds.begin()))
			{
				coalesceGPBs(start, s, cnode);
			}
		}
	}
}

void GPG::coalesceEndGPB(struct cgraph_node *cnode)
{
	unsigned int end;

	end = getExitGPB();

	GPBSet preds, succs;

	preds = getPrev(end);

	GPB gpb;

	unsigned int p;

	if(preds.size() == 1)
	{
		p = *(preds.begin());

		gpb = gpb_map[p];

		if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock())
		{
			return;
		}

		succs = getNext(p);

		if(succs.size() == 1)
		{
			if(end == *(succs.begin()))
			{
				coalesceGPBs(p, end, cnode);
			}
		}
	}
}

void GPG::coalesceStartEndGPBs(struct cgraph_node *cnode)
{
	coalesceStartGPB(cnode);

	coalesceEndGPB(cnode);

	#if 0
	GPG prev;

	while(!(prev == *this))
	{
		prev = *this;

		coalesceStartGPB(cnode);

		if(checkGPGStructure(cnode, false))
		{
			fprintf(dump_file,"\nHigh Alert after Coalescing GPBs\n");
			fflush(dump_file);
			printGPG(cnode);
			fflush(dump_file);
			exit(1);
		}

		if(getGPBs().size() == 1)
		{
			RETURN_VOID();

//			return;
		}
	}

	GPG prev1;

	while(!(prev1 == *this))
	{
		prev1 = *this;

		coalesceEndGPB(cnode);

		if(checkGPGStructure(cnode, false))
		{
			fprintf(dump_file,"\nHigh Alert after Coalescing GPBs\n");
			fflush(dump_file);
			printGPG(cnode);
			fflush(dump_file);
			exit(1);
		}

		if(getGPBs().size() == 1)
		{
			RETURN_VOID();

//			return;
		}
	}
	#endif

	return;
}

void GPG::performCoalescing(struct cgraph_node *cnode)
{
	GPG prev;

	#if 0
	fprintf(dump_file, "\nInside performCoalescing\n");
	fflush(dump_file);
	#endif

	while(!(prev == *this))
	{
		#if 0
		fprintf(dump_file,"\nprev != g\n");
		fflush(dump_file);
		#endif

		prev = *this;

		checkForCoalescing(cnode);

		#if 0
		if(checkGPGStructure(cnode, false))
		{
			fprintf(dump_file,"\nHigh Alert after Coalescing GPBs\n");
			fflush(dump_file);
			printGPG(cnode);
			fflush(dump_file);
			exit(1);
		}
		#endif

//		fprintf(dump_file, "\nNew g after Coalescing\n");
//		g.printGPG(cnode);

		if(getGPBs().size() == 1)
		{
			return;

//			return;
		}
	}

	#if 0
	fprintf(dump_file,"\nprev == g\n");
	fflush(dump_file);
	#endif

	return;
}

GPG performCoalescingAlt(struct cgraph_node *cnode, GPG g)
{
	GPG prev;

	#if 0
	fprintf(dump_file, "\nInside performCoalescing\n");
	fflush(dump_file);
	#endif

	while(!(prev == g))
	{
		#if 0
		fprintf(dump_file,"\nprev != g\n");
		fflush(dump_file);
		#endif

		prev = g;

		g.checkForCoalescing(cnode);

		#if 0
		if(g.checkGPGStructure(cnode, false))
		{
			fprintf(dump_file,"\nHigh Alert after Coalescing GPBs\n");
			fflush(dump_file);
			g.printGPG(cnode);
			fflush(dump_file);
			exit(1);
		}
		#endif

//		fprintf(dump_file, "\nNew g after Coalescing\n");
//		g.printGPG(cnode);

		if(g.getGPBs().size() == 1)
		{
			return(g);

//			return(g);
		}
	}

	#if 0
	fprintf(dump_file,"\nprev == g\n");
	fflush(dump_file);
	#endif

	return(g);

//	return(g);
}

void GPG::optimizeGPG(struct cgraph_node *cnode, bool orig)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned long temp_time;

	#if TIME_MEAS
	clock_t start_t = clock();
	gettimeofday (&TValBefore, NULL);
	#endif

	unsigned int cnum = ((function_info *)(cnode->aux))->func_num;

	unsigned int gpus_before, gpus_after, gpbs_before, gpbs_after, egpbs_before, egpbs_after;
	unsigned int back_edges_before, back_edges_after;

	#if 0 // PRINT_DATA
	fprintf(dump_file,"\nGPG before reachability of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	reachability(cnode);

	#if 0 //PRINT_DATA
	fprintf(dump_file,"\nGPG after reachability of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	localOptimizations(cnode, false);

	#if 0 //PRINT_DATA
	fprintf(dump_file,"\nGPG after local optimizations of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	if(isTop())
	{
		#if DATA_MEAS
		gpus_before = returnNumberOfReducedGPUs(cnode);
		egpbs_before = returnNumberOfGPBsFromGPG(cnum);

		computeBackEdges(cnode);
		back_edges_before = getBackEdges().size();

		gpbs_before = getGPBs().size();

		gpus_after = 0;
		egpbs_after = 0;

		back_edges_after = 0;
		gpbs_after = 0;

		fprintf(dump_file, "\nEffect of Dead GPU Elimination for Function %s, GPUs Before: %u, GPUs After: %u, GPBs Before: %u, GPBs After: %u, Node Uid: %d\n", cgraph_node_name(cnode), gpus_before, gpus_after, egpbs_before, egpbs_after, cnode->uid);

		fprintf(dump_file, "\nEffect of Coalescing for Function %s, GPBs Before: %u, GPBs After: %u, Back Edges Before: %u, Back Edges After: %u, Node Uid: %d\n", cgraph_node_name(cnode), gpbs_before, gpbs_after, back_edges_before, back_edges_after, cnode->uid);
		#endif	

		#if PROFILING	
		RETURN_VOID();
		#else
		return;
		#endif
	}

	#if PAR_FI
	unsigned int end_gpb = getExitGPB();

	GPUSet res = returnGPUs(cnode, false);
//	GPUSet res = ROUT[end_gpb];
	unsigned int x = 1;

	#if DATA_MEAS
	gpus_before = returnNumberOfReducedGPUs(cnode);
	egpbs_before = returnNumberOfGPBsFromGPG(cnum);

	computeBackEdges(cnode);
	back_edges_before = getBackEdges().size();

	gpbs_before = getGPBs().size();

	gpus_after = res.size();
	egpbs_after = 0;

	back_edges_after = 0;
	gpbs_after = 1;

	fprintf(dump_file, "\nEffect of Dead GPU Elimination for Function %s, GPUs Before: %u, GPUs After: %u, GPBs Before: %u, GPBs After: %u, Node Uid: %d\n", cgraph_node_name(cnode), gpus_before, gpus_after, egpbs_before, egpbs_after, cnode->uid);

	fprintf(dump_file, "\nEffect of Coalescing for Function %s, GPBs Before: %u, GPBs After: %u, Back Edges Before: %u, Back Edges After: %u, Node Uid: %d\n", cgraph_node_name(cnode), gpbs_before, gpbs_after, back_edges_before, back_edges_after, cnode->uid);
	#endif

	GPG g;
	GPB entry;

	g.GPB_count++;

	entry.setId(x);
	entry.setBBIndex(2);
	entry.setGPUs(res);
	g.gpb_map[x] = entry;

	gpbs.insert(x);
	g.setEntryGPB(x);
	g.setExitGPB(x);
	g.setGPBs(gpbs);

//	*this = g;

	this->gpbs = g.gpbs;
	this->entry = g.entry;
	this->end = g.end;
	this->gpb_map = g.gpb_map;
	this->GPB_count = g.GPB_count;

	this->RIN = g.RIN;
	this->BRIN = g.BRIN;
	this->ROUT = g.ROUT;
	this->BROUT = g.BROUT;

	this->preds = g.preds;
	this->succs = g.succs;

	this->top = g.top;
	this->back_edges = g.back_edges;

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
	#endif

	definitions lup = lhsUpwardsExposedDefinitions[cnum];

	GPBSet dcalls, icalls, icalls_temp, intervals_t;
	dcalls = getCallBlocks(cnode);
	icalls = getIndirectCallBlocks(cnode);
	intervals_t = getIntervalBlocks(cnode);
	unsigned int syms = returnNumberOfSymGPBs(cnode);

	if(lup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && syms == 0)
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nInstant Optimizations for Function %s\n", cgraph_node_name(cnode));
		#endif

		computeDownwardsExposedDefinitions(cnode);

		GPG g = createNewGPG(cnode);

		optimized_GPG_map[cnum] = g;

		#if DATA_MEAS
		gpus_before = returnNumberOfReducedGPUs(cnode);
		egpbs_before = returnNumberOfGPBsFromGPG(cnum);

		computeBackEdges(cnode);
		back_edges_before = getBackEdges().size();

		gpbs_before = getGPBs().size();

		gpus_after  = g.returnNumberOfReducedGPUs(cnode);
		egpbs_after = g.returnNumberOfGPBsFromGPG(cnum);

		back_edges_after = 0;
		gpbs_after = getGPBs().size();

		fprintf(dump_file, "\nEffect of Dead GPU Elimination for Function %s, GPUs Before: %u, GPUs After: %u, GPBs Before: %u, GPBs After: %u, Node Uid: %d\n", cgraph_node_name(cnode), gpus_before, gpus_after, egpbs_before, egpbs_after, cnode->uid);

		fprintf(dump_file, "\nEffect of Coalescing for Function %s, GPBs Before: %u, GPBs After: %u, Back Edges Before: %u, Back Edges After: %u, Node Uid: %d\n", cgraph_node_name(cnode), gpbs_before, gpbs_after, back_edges_before, back_edges_after, cnode->uid);
		#endif

//		*this = g;

		this->gpbs = g.gpbs;
		this->entry = g.entry;
		this->end = g.end;
		this->gpb_map = g.gpb_map;
		this->GPB_count = g.GPB_count;

		this->RIN = g.RIN;
		this->BRIN = g.BRIN;
		this->ROUT = g.ROUT;
		this->BROUT = g.BROUT;

		this->preds = g.preds;
		this->succs = g.succs;
	
		this->top = g.top;
		this->back_edges = g.back_edges;

		#if PROFILING
		RETURN_VOID();
		#else
		return;
		#endif
	}

	GPUSet queued = Queued[cnum];

//	oneMoreOptimization(cnode);

	#if 0
	if(checkGPGStructure(cnode, false))
	{
		fprintf(dump_file,"\nHigh Alert after one more optimization\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}

	fprintf(dump_file,"\nGPG after one more optimization of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	#if 0
	commonGPUElimination(cnode);

	fprintf(dump_file,"\nGPG after common GPU elimination of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	#if DATA_MEAS
	gpus_before = returnNumberOfReducedGPUs(cnode);
	
	gpbs_before = returnNumberOfGPBsFromGPG(cnum);
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file,"\nGPG before dead GPU elimination of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	#if HEURISTICS
	if(getSymGPBs(cnode).size() == 0)
	{
		#if TIME_MEAS
		gettimeofday (&DTValBefore, NULL);
		#endif

		deadGPUElimination(queued, cnode); // Dead GPU Elimination

		#if TIME_MEAS
		gettimeofday (&DTValAfter, NULL);

		temp_time = ((DTValAfter.tv_sec - DTValBefore.tv_sec)*1000000L+DTValAfter.tv_usec) - DTValBefore.tv_usec;
		dead_op += temp_time;
		#endif	
	}
	#else
	#if TIME_MEAS
	gettimeofday (&DTValBefore, NULL);
	#endif

	deadGPUElimination(queued, cnode); // Dead GPU Elimination

	#if TIME_MEAS
	gettimeofday (&DTValAfter, NULL);

	temp_time = ((DTValAfter.tv_sec - DTValBefore.tv_sec)*1000000L+DTValAfter.tv_usec) - DTValBefore.tv_usec;
	dead_op += temp_time;
	#endif

	#endif
//	#endif

	#if DATA_MEAS
	gpus_after = returnNumberOfReducedGPUs(cnode);
	
	gpbs_after = returnNumberOfGPBsFromGPG(cnum);

	fprintf(dump_file, "\nEffect of Dead GPU Elimination for Function %s, GPUs Before: %u, GPUs After: %u, GPBs Before: %u, GPBs After: %u, Node Uid: %d\n", cgraph_node_name(cnode), gpus_before, gpus_after, gpbs_before, gpbs_after, cnode->uid);
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file,"\nGPG after dead GPU elimination of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif
	
//	eliminateAllEmptyGPBs(cnode, orig); // Eliminate Empty GPBs

	#if TIME_MEAS
	gettimeofday (&ETValBefore, NULL);
	#endif

	eliminateEmptyGPBsDFA(cnode, orig);

	#if TIME_MEAS
	gettimeofday (&ETValAfter, NULL);

	temp_time = ((ETValAfter.tv_sec - ETValBefore.tv_sec)*1000000L+ETValAfter.tv_usec) - ETValBefore.tv_usec;
	emp_op += temp_time;
	#endif

	#if 0
	if(checkGPGStructure(cnode, false))
	{
		fprintf(dump_file,"\nHigh Alert after Dead GPU Elimination\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}

	fprintf(dump_file,"\nGPG after elimination of empty GPBs of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	generateDotFileForGPG(cnode, false, "elim");
	#endif

	eliminateSelfLoops(cnode);

	#if 0
	if(checkGPGStructure(cnode, false))
	{
		fprintf(dump_file,"\nHigh Alert after Self Loop Elimination\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}

	fprintf(dump_file,"\nGPG after eliminating self loops of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	generateDotFileForGPG(cnode, false, "asl");
	#endif

//	GPG g = *this;

//	g = performCoalescingAlt(cnode, g); // Coalescing GPBs

//	performCoalescing(cnode); // Coalescing GPBs

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nGPG before coalescing1\n");
	fflush(dump_file);
	printGPG(cnode);
	fflush(dump_file);
	#endif


	#if DATA_MEAS
	computeBackEdges(cnode);

	gpbs_before = getGPBs().size();
	
	back_edges_before = getBackEdges().size();
	#endif

	#if TIME_MEAS
	gettimeofday (&CTValBefore, NULL);
	#endif

	coalescingDFA(cnode);

	#if 0
	if(checkGPGStructure(cnode, false))
	{
		fprintf(dump_file,"\nHigh Alert after Coalescing\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nGPG after coalescing1\n");
	fflush(dump_file);
	printGPG(cnode);
	fflush(dump_file);
	#endif

	eliminateSelfLoops(cnode);

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nGPG after eliminating self loops\n");
	fflush(dump_file);
	printGPG(cnode);
	fflush(dump_file);
	#endif

	#if DATA_MEAS
	computeBackEdges(cnode);

	gpbs_after = getGPBs().size();
	
	back_edges_after = getBackEdges().size();

	fprintf(dump_file, "\nEffect of Coalescing for Function %s, GPBs Before: %u, GPBs After: %u, Back Edges Before: %u, Back Edges After: %u, Node Uid: %d\n", cgraph_node_name(cnode), gpbs_before, gpbs_after, back_edges_before, back_edges_after, cnode->uid);
	#endif

	#if 0
	if(checkGPGStructure(cnode, false))
	{
		fprintf(dump_file,"\nHigh Alert Self Loop Elimination 2\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}

	fprintf(dump_file,"\nGPG after eliminating self loops2 of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	coalesceStartEndGPBs(cnode);

	#if TIME_MEAS
	gettimeofday (&CTValAfter, NULL);

	temp_time = ((CTValAfter.tv_sec - CTValBefore.tv_sec)*1000000L+CTValAfter.tv_usec) - CTValBefore.tv_usec;
	coal_op += temp_time;
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nGPG after coalescing Start and End GPBs\n");
	fflush(dump_file);
	printGPG(cnode);
	fflush(dump_file);
	#endif

	#if 0
	if(checkGPGStructure(cnode, false))
	{
		fprintf(dump_file,"\nHigh Alert after Coalescing of Start and End GPBs\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}

	fprintf(dump_file, "\nGPG after coalescing and before renumbering with GPB_count = %d\n", GPB_count);
	fflush(dump_file);
	printGPG(cnode);
	fflush(dump_file);
	#endif

	renumberGPBs(cnode);

	#if 0
	fprintf(dump_file, "\nGPG after renumbering with GPB_count = %d\n", GPB_count);
	fflush(dump_file);
	printGPG(cnode);
	fflush(dump_file);

	fprintf(dump_file,"\nOptimized GPG of Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	#if TIME_MEAS
	gettimeofday (&TValAfter, NULL);

	temp_time = ((TValAfter.tv_sec - TValBefore.tv_sec)*1000000L+TValAfter.tv_usec) - TValBefore.tv_usec;
//	fprintf(dump_file, "\nTemp Time: %ld microsec\n", temp_time);
	tot_op += temp_time;
	#endif

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

void GPG::recordBackEdges(struct cgraph_node *cnode)
{
	basic_block bb;
	std::set< unsigned int > succs;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs_d, gpbs_s;
	GPB gpb1, gpb2;
	bool f1 = false, f2 = false;
	
	edge_set backedges;
	edge_type e;

//	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	FOR_EACH_BB(bb) 
	{
		succs = ((block_information *)(bb->aux))->succ_with_back_edge_rel;

//		gpbs_s = ori_red_map[caller_rep][bb->index];

		for(GPBSet::iterator git = gpbs_s.begin(); git != gpbs_s.end(); git++)
		{
			gpb1 = gpb_map[*git];

			if(gpb1.e_bb_block)
			{
				f1 = true;
				break;
			}
		}

		for(set< unsigned int >::iterator it = succs.begin(); it != succs.end(); it++)
		{
//			gpbs_d = ori_red_map[caller_rep][*it];	

			for(GPBSet::iterator git = gpbs_d.begin(); git != gpbs_d.end(); git++)
			{
				gpb2 = gpb_map[*git];

				if(gpb2.s_bb_block)
				{
					f2 = true;
					break;
				}
			}
		}

		if(f1 && f2)
		{
			e = make_pair(gpb1.getId(), gpb2.getId());

			backedges.insert(e);
		}
	}

	setBackEdges(backedges);
//	pop_cfun();
}

void GPG::handlingCallsAlt(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	#if 0
	fprintf(dump_file, "\nInside handlingCalls\n");
	fflush(dump_file);
	printInitialGPG(cnode);
	fflush(dump_file);
	#endif

	GPBSet call_gpbs = getCallBlocks(cnode);
	GPBSet gpbs = getGPBs();
	GPB gpb;
	unsigned int callee;
	basic_block bb;
	GPUSet itmp;

	#if 0
	fprintf(dump_file, "\nIterating through all GPBs to identify call GPBs\n");
	fflush(dump_file);
	#endif

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(!gpb.isCallBlock())
		{
			continue;
		}

		#if 0
		fprintf(dump_file, "\nCall Block %d to be Inlined in GPG of function %s with Callee %d\n", *it, cgraph_node_name(cnode), callee);
		fflush(dump_file);
		#endif

		callee = gpb.getCallee();
		struct cgraph_node *callee_node = func_numbering[callee];

		#if 0
		fprintf(dump_file, "\nFound Callee %s for Caller %s\n", cgraph_node_name(callee_node), cgraph_node_name(cnode));
		fflush(dump_file);
		#endif

		if(needsInlining(cnode_num, callee))
		{
			bb = BASIC_BLOCK(gpb.getBBIndex());

			#if 0 //FP	
			definitions itmp = incompleteCallees[callee];

			if(itmp.empty())
			#endif
			{
				GPG g = optimized_GPG_map[callee];
				callee_node = func_numbering[callee];

				#if 0
				fprintf(dump_file, "\nGPG of the Callee %s to be inlined\n", cgraph_node_name(callee_node));
				fflush(dump_file);
				g.printGPG(callee_node);
				fflush(dump_file);
				#endif

				if(g.isTop())
				{
					eliminateGPB(*it, cnode);

					if(*it == getEntryGPB())
					{
						setTop();
					}

					return;
				}
				else //if(!g.isTop())
				{
					if(g.isIdentityGPG(callee_node, false))
					{
						#if 0
						fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee_node));
						fflush(dump_file);
						#endif

						if(*it == getEntryGPB())
						{
							eraseDirectCallGPB(*it, cnode_num);
						}
						else
						{
							eliminateEmptyGPB(*it, cnode);
						}

						#if 0
						fprintf(dump_file, "\nCall Eliminated\n");
						fflush(dump_file);

						fprintf(dump_file, "\ng_caller of Caller Function %s after elimination\n", cgraph_node_name(cnode));
						fflush(dump_file);
						printInitialGPG(cnode);
						fflush(dump_file);
						#endif
					}
					else
					{
						GPUSet maygen, mustkill;
						definitions lup, rup;

						lup = lhsUpwardsExposedDefinitions[callee];
						rup = rhsUpwardsExposedDefinitions[callee];
						maygen = DownwardsExposedMayDefinitions[callee];
						mustkill = DownwardsExposedMustDefinitions[callee];

						GPBSet dcalls, icalls, intervals_t;
						dcalls = g.getCallBlocks(callee_node);
						icalls = g.getIndirectCallBlocks(callee_node);
						intervals_t = g.getIntervalBlocks(callee_node);

						if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
						{
//							fprintf(dump_file, "\nNo Upwards Exposed\n");
		
							if(*it == getEntryGPB())
							{
								eraseDirectCallGPB(*it, cnode_num);
							}
							else
							{
								eliminateEmptyGPB(*it, cnode);
							}
						}
						else
						{
//							fprintf(dump_file, "\nInline GPG of callee for non-Identity and non-Top %s\n", cgraph_node_name(callee_node));

							inlineCall(*it, callee, cnode_num, bb, g);
						}
					}
				}
			}
		}
	}

//	fprintf(dump_file,"\nGPG of Function %s after handling calls\n", cgraph_node_name(cnode));
//	printInitialGPG(cnode);

	return;
}

void GPG::shouldRepresentSymGPG(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPUSet total_gpus, scalar_gpus, upwards_gpus, temp_c, total_struct_gpus;

	GPBSet gpbs = getGPBs();
	GPB gpb_c;

	IndirectionList list1, list2;

	for(GPBSet::iterator gc = gpbs.begin(); gc != gpbs.end(); gc++)
	{
		gpb_c = gpb_map[*gc];

		temp_c = gpb_c.getGPUs();

		for(GPUSet::iterator cit = temp_c.begin(); cit != temp_c.end(); cit++)
		{
			total_gpus.insert(*cit);

			if(isStackGPU(*cit))	
			{
				scalar_gpus.insert(*cit);
			}
			else
			{
				list1 = getNode(get<0>(*cit)).getList();
				list2 = getNode(get<1>(*cit)).getList();

				if(list1.Length() > 1 || list2.Length() > 0)
				{
					upwards_gpus.insert(*cit);
				}
			}
		}
	}

	double percentage = (upwards_gpus.size() * 1.0)/(total_gpus.size() - scalar_gpus.size());
	percentage *= 100;
	GPUSet fin_gpus_set;

	if(percentage >= 80.0 && upwards_gpus.size() > 10)
	{
		sym_gpgs.insert(cnode_num);
				
		for(GPUSet::iterator gc = upwards_gpus.begin(); gc != upwards_gpus.end(); gc++)
		{
			fin_gpus_set.insert(stripUpwardsExposed(*gc));
		}

		UpwardsGPUs[cnode_num] = fin_gpus_set;
	}
}

void GPG::handlingSymGPBs(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();

	GPB gpb;
	unsigned int callee;
	basic_block bb;
	GPUSet itmp;

	struct cgraph_node *callee_node;
	GPBSet callee_set;

	GPBSet temp_gpbs, to_be_added;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(!gpb.isSymGPB())
		{
			continue;
		}

		callee = gpb.getCallee();

		callee_set.insert(callee);

		callee_node = func_numbering[callee];
		
		bb = BASIC_BLOCK(gpb.getBBIndex());
	
		GPG g = optimized_GPG_map[callee];

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nOptimized GPG of the callee %s for SymGPB %d\n", cgraph_node_name(callee_node), *it);
		g.printGPG(callee_node);
		#endif

		if(g.isTop())
		{
			eliminateGPB(*it, cnode);

			if(*it == getEntryGPB())
			{
				setTop();
			}
		}
		else
		{
			if(g.isIdentityGPG(callee_node, false))
			{
				if(*it == getEntryGPB())
				{
					eraseDirectCallGPB(*it, cnode_num);
				}
				else
				{
					eliminateEmptyGPB(*it, cnode);
				}
			}
			else
			{
				GPUSet maygen, mustkill;
				definitions lup, rup;

				lup = lhsUpwardsExposedDefinitions[callee];
				rup = rhsUpwardsExposedDefinitions[callee];
				maygen = DownwardsExposedMayDefinitions[callee];
				mustkill = DownwardsExposedMustDefinitions[callee];

				GPBSet dcalls, icalls, intervals_t;
				dcalls = g.getCallBlocks(callee_node);
				icalls = g.getIndirectCallBlocks(callee_node);
				intervals_t = g.getIntervalBlocks(callee_node);

				if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
				{
//					fprintf(dump_file, "\nNo Upwards Exposed\n");
		
					if(*it == getEntryGPB())
					{
						eraseDirectCallGPB(*it, cnode_num);
					}
					else
					{
						eliminateEmptyGPB(*it, cnode);
					}
				}
				else
				{
					#if 0 //HEURISTICS
					GPUSet fin_gpus_set;

					if(sym_gpgs.find(callee) != sym_gpgs.end())
					{
						gpb.setSymGPB();

						fin_gpus_set = UpwardsGPUs[callee];
	
						gpb.setOrigGPUs(fin_gpus_set);

						GPBSet set_callees = gpb.getSetOfCallees();
						set_callees.insert(callee);
						gpb.setSetOfCallees(set_callees);

						gpb_map[*it] = gpb;
					}
					else
					{
						temp_gpbs = inlineCall(*it, callee, cnode_num, bb, g);
					}
					#else
					temp_gpbs = inlineCall(*it, callee, cnode_num, bb, g);
					#endif	

					to_be_added.insert(temp_gpbs.begin(), temp_gpbs.end());
				}
			}
		}

		localOptimizations(cnode, true);
	}
	
	#if 0
	unsigned int start = getEntryGPB();

	gpbs = getGPBs();

	unsigned int size = gpbs.size();

	std::map< unsigned int, bool > worklist;

	DFS_COUNT = size;

	std::map< unsigned int, bool > label;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		label[*it] = false;
	}

	LABEL_GPB[cnode_num] = label;

	DFS(start, cnode);

	int * wk = new int[size+1];

	unsigned int i;

	for(i = 1; i <= gpbs.size(); i++)
	{
		wk[i] = false;
	}

	unsigned int order;

	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[cnode_num];
	
	for(GPBSet::iterator it = to_be_added.begin(); it != to_be_added.end(); it++)
	{
		order = dfs_gpb[*it];
		wk[order] = true;
	}

	GPB_worklist[cnode_num] = wk;
	#endif
}

void GPG::handlingRecursiveCalls(struct cgraph_node *cnode)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nInside handlingRecursiveCalls\n");
	fflush(dump_file);
	printInitialGPG(cnode);
	fflush(dump_file);
	#endif

	GPBSet gpbs = getGPBs();

	GPB gpb;
	unsigned int callee;
	basic_block bb;
	GPUSet itmp;

	struct cgraph_node *callee_node;
	GPBSet temp_gpbs, to_be_added;
	GPBSet callee_set;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isSymGPB())
		{
			continue;
		}

		if(!gpb.isCallBlock())
		{
			continue;
		}

		callee = gpb.getCallee();

		callee_set.insert(callee);

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nCall Block %d to be Inlined in GPG of function %s with Callee %d\n", *it, cgraph_node_name(cnode), callee);
		fflush(dump_file);
		#endif

		callee_node = func_numbering[callee];
		
		((function_info *)(cnode->aux))->num_trans_nonptr_stmts += ((function_info *)(callee_node->aux))->num_trans_nonptr_stmts;
		((function_info *)(cnode->aux))->num_trans_stmts += ((function_info *)(callee_node->aux))->num_trans_stmts;
		((function_info *)(cnode->aux))->num_trans_bbs += ((function_info *)(callee_node->aux))->num_trans_bbs;
		((function_info *)(cnode->aux))->trans_cf_edges += ((function_info *)(callee_node->aux))->trans_cf_edges;

		#if 0
		fprintf(dump_file, "\nFound Callee %s for Caller %s\n", cgraph_node_name(callee_node), cgraph_node_name(cnode));
		fflush(dump_file);
		#endif

		bb = BASIC_BLOCK(gpb.getBBIndex());
	
		#if 0
		fprintf(dump_file, "\nAgain: BB index 1 %d\n", gpb.getBBIndex());
		fflush(dump_file);
		fprintf(dump_file, "\nBB index 2 %d\n", bb->index);
		fflush(dump_file);
		#endif

		GPG g = optimized_GPG_map[callee];

		#if 0 
		fprintf(dump_file, "\nGPG of the Callee %s to be inlined\n", cgraph_node_name(callee_node));
		fflush(dump_file);
		g.printGPG(callee_node);
		fflush(dump_file);
		#endif

		if(g.isTop())
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nGPG of the callee is Top\n");
			fflush(dump_file);
			#endif

			eliminateGPB(*it, cnode);

			if(*it == getEntryGPB())
			{
				setTop();
			}

			#if 0
			#if PROFILING
			RETURN_VOID();
			#else
			return;
			#endif
			#endif
		}
		else //if(!g.isTop())
		{
			if(g.isIdentityGPG(callee_node, false))
			{
				#if 0 //PRINT_DATA 
				fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee_node));
				fflush(dump_file);
				#endif

				if(*it == getEntryGPB())
				{
					eraseDirectCallGPB(*it, cnode_num);
				}
				else
				{
					eliminateEmptyGPB(*it, cnode);
				}

				#if 0
				fprintf(dump_file, "\nCall Eliminated\n");
				fflush(dump_file);

				fprintf(dump_file, "\ng_caller of Caller Function %s after elimination\n", cgraph_node_name(cnode));
				fflush(dump_file);
				printInitialGPG(cnode);
				fflush(dump_file);
				#endif
			}
			else
			{
				GPUSet maygen, mustkill;
				definitions lup, rup;

				lup = lhsUpwardsExposedDefinitions[callee];
				rup = rhsUpwardsExposedDefinitions[callee];
				maygen = DownwardsExposedMayDefinitions[callee];
				mustkill = DownwardsExposedMustDefinitions[callee];

				GPBSet dcalls, icalls, intervals_t;
				dcalls = g.getCallBlocks(callee_node);
				icalls = g.getIndirectCallBlocks(callee_node);
				intervals_t = g.getIntervalBlocks(callee_node);

				if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
				{
//					fprintf(dump_file, "\nNo Upwards Exposed\n");
		
					if(*it == getEntryGPB())
					{
						eraseDirectCallGPB(*it, cnode_num);
					}
					else
					{
						eliminateEmptyGPB(*it, cnode);
					}
				}
				else
				{
//					fprintf(dump_file, "\nInline GPG of callee for non-Identity and non-Top %s\n", cgraph_node_name(callee_node));

					#if HEURISTICS
					GPUSet fin_gpus_set;

					if(sym_gpgs.find(callee) != sym_gpgs.end())
					{
						#if 0 //PRINT_DATA
						fprintf(dump_file, "\nIntroducing Sym GPG\n");
						g.printGPG(callee_node);	
						fflush(dump_file);	
						#endif

						gpb.setSymGPB();

						fin_gpus_set = UpwardsGPUs[callee];
	
						gpb.setOrigGPUs(fin_gpus_set);

						GPBSet set_callees = gpb.getSetOfCallees();
						set_callees.insert(callee);
						gpb.setSetOfCallees(set_callees);

						gpb_map[*it] = gpb;
					}
					else
					{
						temp_gpbs = inlineCall(*it, callee, cnode_num, bb, g);

						#if 0 //PRINT_DATA
						fprintf(dump_file, "\nInlining Call\n");
						printGPG(callee_node);	
						fflush(dump_file);	
						#endif
					}
					#else
					temp_gpbs = inlineCall(*it, callee, cnode_num, bb, g);
					#endif	

					to_be_added.insert(temp_gpbs.begin(), temp_gpbs.end());
				}
			}
		}

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nInside handlingRecursiveCalls before localOptimizations\n");
		fflush(dump_file);
		#endif

		localOptimizations(cnode, true);

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nInside handlingRecursiveCalls after localOptimizations\n");
		fflush(dump_file);
		#endif

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPG after inlining the call at GPB %d in Function %s\n", *it, cgraph_node_name(cnode));
		printInitialGPG(cnode);
		fflush(dump_file);
		fprintf(dump_file, "\nGPBs in the GPG of Function %s\n", cgraph_node_name(cnode));
		print_set_integers(getGPBs());
		fflush(dump_file);
		#endif
	}

	unsigned int start = getEntryGPB();

	#if 0
	BFS_COUNT = 0;

	BFS(cnode);
	#endif

	gpbs = getGPBs();

	unsigned int size = gpbs.size();

	std::map< unsigned int, bool > worklist;

	#if 1
	DFS_COUNT = size;

	std::map< unsigned int, bool > label;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		label[*it] = false;
	}

	LABEL_GPB[cnode_num] = label;

	DFS(start, cnode);
	#endif

	int * wk = new int[size+1];

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nAllocation done for Function %s of the size %d\n", cgraph_node_name(cnode), size);
	fflush(dump_file);
	#endif

	unsigned int i;

	for(i = 1; i <= gpbs.size(); i++)
	{
		wk[i] = false;
	}

	unsigned int order;

	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[cnode_num];

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nAfter DFS\n");
	printInitialGPG(cnode);
	#endif
	
	for(GPBSet::iterator it = to_be_added.begin(); it != to_be_added.end(); it++)
	{
		if(gpbs.find(*it) == gpbs.end())
		{
			continue;
		}

		order = dfs_gpb[*it];

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPB %d has Order %d\n", *it, order);
		fflush(dump_file);

		if(order > size)
		{
			fprintf(dump_file, "\nOrder > Size\n");
			fflush(dump_file);
			exit(1);
		}
		#endif	
		
		wk[order] = true;
	}

	GPB_worklist[cnode_num] = wk;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nWorklist initialized for Function %s of the size %d\n", cgraph_node_name(cnode), size);
	fflush(dump_file);
	#endif

	GPUSet t1, t2;
	std::map< unsigned int, GPUSet > fip_data_callee, fip_data_caller, finp_data_callee, finp_data_caller;
	fip_data_caller = FIP[cnode_num];
	finp_data_caller = FINP[cnode_num];

	for(GPBSet::iterator cit = callee_set.begin(); cit != callee_set.end(); cit++)
	{
		fip_data_callee = FIP[*cit];

		for(std::map< unsigned int, GPUSet >::iterator fit = fip_data_callee.begin(); fit != fip_data_callee.end(); fit++)
		{
			if(is_ssa_var(fit->first))
			{
				continue;
			}

			t1 = fit->second;

			t2 = fip_data_caller[fit->first];

			t2.insert(t1.begin(), t1.end());

			fip_data_caller[fit->first] = t2;
		}

		finp_data_callee = FINP[*cit];

		for(std::map< unsigned int, GPUSet >::iterator fit = finp_data_callee.begin(); fit != finp_data_callee.end(); fit++)
		{
			t1 = fit->second;

			t2 = finp_data_caller[fit->first];

			for(GPUSet::iterator mit = t1.begin(); mit != t1.end(); mit++)
			{
				gpu_id_type id_temp = stripUpwardsExposed(*mit);

				t2.insert(id_temp);
			}

//			t2.insert(t1.begin(), t1.end());

			finp_data_caller[fit->first] = t2;
		}
	}

	FIP[cnode_num] = fip_data_caller;
	FINP[cnode_num] = finp_data_caller;

	unsigned int entry = getEntryGPB();

	GPUSet bi = BDEFS[cnode_num];
	RIN[entry] = bi;
	BRIN[entry] = bi;

	#if 0
	GPUSet array_data_caller, array_data_callee;

	array_data_caller = flowInsensitiveInformation[cnode_num];

	for(GPBSet::iterator cit = callee_set.begin(); cit != callee_set.end(); cit++)
	{
		array_data_callee = flowInsensitiveInformation[*cit];

		for(GPUSet::iterator it = array_data_callee.begin(); it != array_data_callee.end(); it++)
		{
			GPU temp_gpu = GPU::gpu_map[*it];
			array_data_caller.insert(temp_gpu.stripUpwardsExposed());
		}
	}

	flowInsensitiveInformation[cnode_num] = array_data_caller;
	#endif

//	fprintf(dump_file,"\nGPG of Function %s after handling calls\n", cgraph_node_name(cnode));
//	printInitialGPG(cnode);

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

void GPG::handlingCalls(struct cgraph_node *cnode)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nInside handlingCalls\n");
	fflush(dump_file);
	printInitialGPG(cnode);
	fflush(dump_file);
	#endif

	GPBSet gpbs = getGPBs();
	GPBSet recursive_calls, open_ckt_calls, scc_funcs, scc_leaves, leaves;

	unsigned int scc_num;

	if(SCCs.find(cnode_num) != SCCs.end()) // Function cnode is in SCC
	{
		scc_num = func_scc_map[cnode_num]; 	
		scc_funcs = SCC_MAP[scc_num];
		scc_leaves = leavesSCCs[scc_num];
		leaves = leaves_sccs[cnode_num];

		#if 0	
		fprintf(dump_file, "\nLeaves of SCC %d\n", scc_num);
		print_set_integers(scc_leaves); 
		fprintf(dump_file, "\nLeaves of Function %d\n", cnode_num);
		print_set_integers(leaves); 
		#endif
	}	

	GPB gpb;
	unsigned int callee;
	basic_block bb;
	GPUSet itmp;

//	fprintf(dump_file, "\nIterating through all GPBs to identify call GPBs\n");
//	fflush(dump_file);

	struct cgraph_node *callee_node;
	GPBSet callee_set;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isSymGPB())
		{
			continue;
		}	

		if(!gpb.isCallBlock())
		{
			continue;
		}

		callee = gpb.getCallee();

		#if 0
		fprintf(dump_file, "\nCall Block %d to be Inlined in GPG of function %s with Callee %d\n", *it, cgraph_node_name(cnode), callee);
		fflush(dump_file);
		#endif

		if(leaves.find(callee) != leaves.end())
		{
//			fprintf(dump_file, "\nCall %d to be open-cktd\n", *it);

			open_ckt_calls.insert(*it);

			continue;
		}
		else if(scc_funcs.find(callee) != scc_funcs.end())
		{
//			fprintf(dump_file, "\nRecursive Call %d to be inlined\n", *it);

			recursive_calls.insert(*it);
	
			continue;
		}
		#if 0
		else 
		{
			recursive_calls.insert(*it);
	
			continue;
		}
		#endif		

		callee_node = func_numbering[callee];

		((function_info *)(cnode->aux))->num_trans_nonptr_stmts += ((function_info *)(callee_node->aux))->num_trans_nonptr_stmts;
		((function_info *)(cnode->aux))->num_trans_stmts += ((function_info *)(callee_node->aux))->num_trans_stmts;
		((function_info *)(cnode->aux))->num_trans_bbs += ((function_info *)(callee_node->aux))->num_trans_bbs;
		((function_info *)(cnode->aux))->trans_cf_edges += ((function_info *)(callee_node->aux))->trans_cf_edges;

		callee_set.insert(callee);

//		fprintf(dump_file, "\nFound Callee %s for Caller %s\n", cgraph_node_name(callee_node), cgraph_node_name(cnode));
//		fflush(dump_file);

		bb = BASIC_BLOCK(gpb.getBBIndex());

		#if 0
		fprintf(dump_file, "\nBB index 1 %d\n", gpb.getBBIndex());
		fflush(dump_file);
		fprintf(dump_file, "\nBB index 2 %d\n", bb->index);
		fflush(dump_file);
		#endif

		GPG g = optimized_GPG_map[callee];

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPG of the Callee %s to be inlined\n", cgraph_node_name(callee_node));
		fflush(dump_file);
		g.printGPG(callee_node);
		fflush(dump_file);

		fprintf(dump_file, "\nGPB Count in handlingCalls = %d\n", GPB_count);
		fflush(dump_file);
		#endif

		if(g.isTop())
		{
			eliminateGPB(*it, cnode);

			if(*it == getEntryGPB())
			{
				setTop();
			}

			#if 0
			#if PROFILING
			RETURN_VOID();
			#else
			return;
			#endif
			#endif
		}
		else //if(!g.isTop())
		{
			if(g.isIdentityGPG(callee_node, false))
			{
				#if 0
				fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee_node));
				fflush(dump_file);
				#endif

				if(*it == getEntryGPB())
				{
					eraseDirectCallGPB(*it, cnode_num);
				}
				else
				{
					eliminateEmptyGPB(*it, cnode);
				}

				#if 0
				fprintf(dump_file, "\nCall Eliminated\n");
				fflush(dump_file);

				fprintf(dump_file, "\ng_caller of Caller Function %s after elimination\n", cgraph_node_name(cnode));
				fflush(dump_file);
				printInitialGPG(cnode);
				fflush(dump_file);
				#endif
			}
			else
			{
				GPUSet maygen, mustkill;
				definitions lup, rup;

				lup = lhsUpwardsExposedDefinitions[callee];
				rup = rhsUpwardsExposedDefinitions[callee];
				maygen = DownwardsExposedMayDefinitions[callee];
				mustkill = DownwardsExposedMustDefinitions[callee];

				GPBSet dcalls, icalls, intervals_t;
				dcalls = g.getCallBlocks(callee_node);
				icalls = g.getIndirectCallBlocks(callee_node);
				intervals_t = g.getIntervalBlocks(callee_node);

				if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
				{
//					fprintf(dump_file, "\nNo Upwards Exposed\n");
		
					if(*it == getEntryGPB())
					{
						eraseDirectCallGPB(*it, cnode_num);
					}
					else
					{
						eliminateEmptyGPB(*it, cnode);
					}
				}
				else
				{
//					fprintf(dump_file, "\nInline GPG of callee for non-Identity and non-Top %s\n", cgraph_node_name(callee_node));
					GPBSet temp_gpbs;

					#if HEURISTICS
					GPUSet fin_gpus_set;

					if(sym_gpgs.find(callee) != sym_gpgs.end())
					{
						#if 0 //PRINT_DATA
						fprintf(dump_file, "\nIntroducing Sym GPG\n");
						g.printGPG(callee_node);	
						fflush(dump_file);	
						#endif

						gpb.setSymGPB();

						fin_gpus_set = UpwardsGPUs[callee];
	
						gpb.setOrigGPUs(fin_gpus_set);

						GPBSet set_callees = gpb.getSetOfCallees();
						set_callees.insert(callee);
						gpb.setSetOfCallees(set_callees);

						gpb_map[*it] = gpb;
					}
					else
					{
						temp_gpbs = inlineCall(*it, callee, cnode_num, bb, g);

						#if 0 //PRINT_DATA
						fprintf(dump_file, "\nInlining Call\n");
						printGPG(callee_node);	
						fflush(dump_file);	
						#endif
					}
					#else
					temp_gpbs = inlineCall(*it, callee, cnode_num, bb, g);
					#endif	
				}
			}
		}
	}

	deltaGPG_map[cnode_num] = *this;	

	for(GPBSet::iterator it = open_ckt_calls.begin(); it != open_ckt_calls.end(); it++)
	{
		eliminateGPB(*it, cnode);
	}

	reachability(cnode);

	GPBSet new_gpbs = getGPBs();
	GPBSet new_recursive_calls;

	set_intersection(recursive_calls.begin(), recursive_calls.end(), new_gpbs.begin(), new_gpbs.end(), inserter(new_recursive_calls, new_recursive_calls.end()));

	for(GPBSet::iterator it = new_recursive_calls.begin(); it != new_recursive_calls.end(); it++)
	{
		gpb = gpb_map[*it];

		if(!gpb.isCallBlock())
		{
			continue;
		}

		callee = gpb.getCallee();

		callee_set.insert(callee);

		bb = BASIC_BLOCK(gpb.getBBIndex());

		GPG g = optimized_GPG_map[callee];
		callee_node = func_numbering[callee];

		((function_info *)(cnode->aux))->num_trans_nonptr_stmts += ((function_info *)(callee_node->aux))->num_trans_nonptr_stmts;
		((function_info *)(cnode->aux))->num_trans_stmts += ((function_info *)(callee_node->aux))->num_trans_stmts;
		((function_info *)(cnode->aux))->num_trans_bbs += ((function_info *)(callee_node->aux))->num_trans_bbs;
		((function_info *)(cnode->aux))->trans_cf_edges += ((function_info *)(callee_node->aux))->trans_cf_edges;

		#if 0 //PRINT_DATA	
		fprintf(dump_file, "\nGPG of the Callee %s to be inlined\n", cgraph_node_name(callee_node));
		fflush(dump_file);
		g.printGPG(callee_node);
		fflush(dump_file);
		#endif

		if(g.isTop())
		{
			eliminateGPB(*it, cnode);

			if(*it == getEntryGPB())
			{
				setTop();
			}

			#if 0
			#if PROFILING
			RETURN_VOID();
			#else
			return;
			#endif
			#endif
		}
		else //if(!g.isTop())
		{
			if(g.isIdentityGPG(callee_node, false))
			{
				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee_node));
				fflush(dump_file);
				#endif

				if(*it == getEntryGPB())
				{
					eraseDirectCallGPB(*it, cnode_num);
				}
				else
				{
					eliminateEmptyGPB(*it, cnode);
				}

				#if 0
				fprintf(dump_file, "\nCall Eliminated\n");
				fflush(dump_file);

				fprintf(dump_file, "\ng_caller of Caller Function %s after elimination\n", cgraph_node_name(cnode));
				fflush(dump_file);
				printInitialGPG(cnode);
				fflush(dump_file);
				#endif
			}
			else
			{
				GPUSet maygen, mustkill;
				definitions lup, rup;

				lup = lhsUpwardsExposedDefinitions[callee];
				rup = rhsUpwardsExposedDefinitions[callee];
				maygen = DownwardsExposedMayDefinitions[callee];
				mustkill = DownwardsExposedMustDefinitions[callee];

				GPBSet dcalls, icalls, intervals_t;
				dcalls = g.getCallBlocks(callee_node);
				icalls = g.getIndirectCallBlocks(callee_node);
				intervals_t = g.getIntervalBlocks(callee_node);

				if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
				{
//					fprintf(dump_file, "\nNo Upwards Exposed\n");
		
					if(*it == getEntryGPB())
					{
						eraseDirectCallGPB(*it, cnode_num);
					}
					else
					{
						eliminateEmptyGPB(*it, cnode);
					}
				}
				else
				{
//					fprintf(dump_file, "\nInline GPG of callee for non-Identity and non-Top %s\n", cgraph_node_name(callee_node));
					GPBSet temp_gpbs;

					#if HEURISTICS
					GPUSet fin_gpus_set;

					if(sym_gpgs.find(callee) != sym_gpgs.end())
					{
						gpb.setSymGPB();

						fin_gpus_set = UpwardsGPUs[callee];
	
						gpb.setOrigGPUs(fin_gpus_set);

						GPBSet set_callees = gpb.getSetOfCallees();
						set_callees.insert(callee);
						gpb.setSetOfCallees(set_callees);

						gpb_map[*it] = gpb;
					}
					else
					{
						temp_gpbs = inlineCall(*it, callee, cnode_num, bb, g);
					}
					#else
					temp_gpbs = inlineCall(*it, callee, cnode_num, bb, g);
					#endif	
				}
			}
		}
	}

	GPUSet t1, t2;
	std::map< unsigned int, GPUSet > fip_data_callee, fip_data_caller, finp_data_callee, finp_data_caller;
	fip_data_caller = FIP[cnode_num];
	finp_data_caller = FINP[cnode_num];
	GPUSet bi, bi_temp;

	bi = BDEFS[cnode_num];

	GPUSet xinfo, temp_info;

	stmt_info_type key;
	GPBSet sset, temp_sset;

	for(GPBSet::iterator cit = callee_set.begin(); cit != callee_set.end(); cit++)
	{
		#if 0
		bi_temp = BDEFS[*cit];

		bi.insert(bi_temp.begin(), bi_temp.end());
		#endif

		fip_data_callee = FIP[*cit];

		for(std::map< unsigned int, GPUSet >::iterator fit = fip_data_callee.begin(); fit != fip_data_callee.end(); fit++)
		{
			if(is_ssa_var(fit->first))
			{
				continue;
			}

			t1 = fit->second;

			t2 = fip_data_caller[fit->first];

			for(GPUSet::iterator mit = t1.begin(); mit != t1.end(); mit++)
			{
				key = std::make_tuple(*cit, 0, *mit);

				sset = stmt_id_info[key];

				key = std::make_tuple(cnode_num, 0, *mit);

				temp_sset = stmt_id_info[key];

				temp_sset.insert(sset.begin(), sset.end());

				stmt_id_info[key] = temp_sset;

				t2.insert(*mit);
			}

//			t2.insert(t1.begin(), t1.end());

			fip_data_caller[fit->first] = t2;
		}

		finp_data_callee = FINP[*cit];

		for(std::map< unsigned int, GPUSet >::iterator fit = finp_data_callee.begin(); fit != finp_data_callee.end(); fit++)
		{
			t1 = fit->second;

			t2 = finp_data_caller[fit->first];

			for(GPUSet::iterator mit = t1.begin(); mit != t1.end(); mit++)
			{
				key = std::make_tuple(*cit, 0, *mit);

				sset = stmt_id_info[key];

				gpu_id_type id_temp = stripUpwardsExposed(*mit);

				key = std::make_tuple(cnode_num, 0, id_temp);

				temp_sset = stmt_id_info[key];

				temp_sset.insert(sset.begin(), sset.end());

				stmt_id_info[key] = temp_sset;

				t2.insert(id_temp);
			}

//			t2.insert(t1.begin(), t1.end());

			finp_data_caller[fit->first] = t2;
		}
	}

	FIP[cnode_num] = fip_data_caller;
	FINP[cnode_num] = finp_data_caller;

	unsigned int entry = getEntryGPB();

//	BDEFS[cnode_num] = bi;
	RIN[entry] = bi;
	BRIN[entry] = bi;

	#if 0
	GPUSet array_data_caller, array_data_callee;

	array_data_caller = flowInsensitiveInformation[cnode_num];

	for(GPBSet::iterator cit = callee_set.begin(); cit != callee_set.end(); cit++)
	{
		array_data_callee = flowInsensitiveInformation[*cit];

		for(GPUSet::iterator it = array_data_callee.begin(); it != array_data_callee.end(); it++)
		{
			GPU temp_gpu = GPU::gpu_map[*it];
			array_data_caller.insert(temp_gpu.stripUpwardsExposed());
		}
	}

	flowInsensitiveInformation[cnode_num] = array_data_caller;
	#endif

//	fprintf(dump_file,"\nGPG of Function %s after handling calls\n", cgraph_node_name(cnode));
//	printInitialGPG(cnode);

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

void GPG::handlingSelectiveCalls(struct cgraph_node *cnode, unsigned int the_callee)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	struct cgraph_node *the_callee_node = func_numbering[the_callee];

	#if 0
	fprintf(dump_file, "\nInside handlingSelectiveCalls selective for %s\n", cgraph_node_name(the_callee_node));
	fflush(dump_file);
	printInitialGPG(cnode);
	fflush(dump_file);
	#endif

	GPBSet call_gpbs = getCallBlocks(cnode);
	GPBSet gpbs = getGPBs();
	GPB gpb;
	unsigned int callee;
	basic_block bb;
	GPUSet itmp;

	#if 0
	fprintf(dump_file, "\nIterating through all GPBs to identify call GPBs\n");
	fflush(dump_file);
	#endif

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(!gpb.isCallBlock())
		{
			continue;
		}

		#if 0
		fprintf(dump_file, "\nCall GPB %d in GPG of function %s\n", *it, cgraph_node_name(cnode));
		fflush(dump_file);
		#endif

		callee = gpb.getCallee();

		if(the_callee != callee)
		{
			continue;
		}

		#if 0
		fprintf(dump_file, "\nCall GPB %d found for selective callee\n");
		fflush(dump_file);
		#endif

		struct cgraph_node *callee_node;

		callee_node = func_numbering[callee];

		#if 0
		fprintf(dump_file, "\nFound Callee %s for Caller %s\n", cgraph_node_name(callee_node), cgraph_node_name(cnode));
		fflush(dump_file);
		#endif

		GPG g = optimized_GPG_map[callee];

		#if 0
		fprintf(dump_file, "\nGPG of the Callee %s to be inlined\n", cgraph_node_name(callee_node));
		fflush(dump_file);
		g.printGPG(callee_node);
		fflush(dump_file);
		#endif

		if(g.isTop())
		{
			eliminateGPB(*it, cnode);

			if(*it == getEntryGPB())
			{
				setTop();

				return;
			}
		}
		else
		{
			if(g.isIdentityGPG(callee_node, false))
			{
				#if 0
				fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee_node));
				fflush(dump_file);
				#endif

				if(*it == getEntryGPB())
				{
					eraseDirectCallGPB(*it, cnode_num);
				}
				else
				{
					eliminateEmptyGPB(*it, cnode);
				}

				#if 0
				fprintf(dump_file, "\nCall Eliminated\n");
				fflush(dump_file);

				fprintf(dump_file, "\ng_caller of Caller Function %s after elimination\n", cgraph_node_name(cnode));
				fflush(dump_file);
				printInitialGPG(cnode);
				fflush(dump_file);
				#endif
			}
			else
			{
				GPUSet maygen, mustkill;
				definitions lup, rup;

				lup = lhsUpwardsExposedDefinitions[callee];
				rup = rhsUpwardsExposedDefinitions[callee];
				maygen = DownwardsExposedMayDefinitions[callee];
				mustkill = DownwardsExposedMustDefinitions[callee];

				GPBSet dcalls, icalls, intervals_t;
				dcalls = g.getCallBlocks(callee_node);
				icalls = g.getIndirectCallBlocks(callee_node);
				intervals_t = g.getIntervalBlocks(callee_node);

				if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
				{
//					fprintf(dump_file, "\nNo Upwards Exposed\n");
		
					if(*it == getEntryGPB())
					{
						eraseDirectCallGPB(*it, cnode_num);
					}
					else
					{
						eliminateEmptyGPB(*it, cnode);
					}
				}
				else
				{	
					bb = BASIC_BLOCK(gpb.getBBIndex());

//					fprintf(dump_file, "\nInline GPG of callee for non-Identity and non-Top %s\n", cgraph_node_name(callee_node));

					inlineCall(*it, callee, cnode_num, bb, g);
				}
			}				

		}
	}

	#if 0
	fprintf(dump_file,"\nGPG of Function %s after handling selective calls\n", cgraph_node_name(cnode));
	printInitialGPG(cnode);
	#endif

	return;
}

GPUSet GPG::insertBoundaryDefinitions(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

//	FUNBEGIN();

	#if 0
	fprintf(dump_file,"\nInside BI %d for Function %s\n", boundary_nodes.size(), cgraph_node_name(cnode));
	fflush(dump_file);

	fprintf(dump_file,"\nPrinting boundary_nodes\n");
	printSetofNodes(boundary_nodes);
	fprintf(dump_file,"\nEnd of Printing boundary_nodes\n");
	#endif

	csvarinfo_t vi;
	Node n;
	int length;
	GPUSet bi;
	unsigned int var;

	for(definitions::iterator it = boundary_nodes.begin(); it != boundary_nodes.end(); it++)
	{
		n = getNode(*it);

		var = n.getVarIndex();

		vi = cs_get_varinfo(var);

		if(vi == NULL)
			continue;

//		fprintf(dump_file, "\nVar found %s-%d, Global %d, Para-Ret %d\n", get_var_name(vi->id), vi->id, global_var(vi->id), is_par_ret(vi->decl, cnode, NULL));
//		fflush(dump_file);

		if(vi->id < 4)
		{
			continue;
		}
		
		if(!(global_var(var) || is_par_ret(vi->decl, cnode, NULL)))
		{
			continue;
		}

		if(n.getList().Length() == 0)
		{
			continue;
		}

//		if(is_aggregrate_type_varinfo(vi))
		if(isAggregrateNode(vi))
		{
//			fprintf(dump_file, "\nAggregate Type\n");
//			fflush(dump_file);

			int field_list[IndirectionList::kSize];

			length = n.getList().Length();

			for(int i = 0; i < length; i++)
//			for(int i = 0; i < k_thresh; i++)
			{
				field_list[i] = SFIELD;				
				
				IndirectionList l(false, 0, i+1, field_list);

				Node lhs(var, l);
				Node rhs(var+1, l);
				GPU gpu(lhs, rhs);

//				fprintf(dump_file, "\nPrinting GPU\n");
//				gpu.printGPU();

				bi.insert(gpu.getGPUID());
			}
		}
		else
		{
//			fprintf(dump_file, "\nScalar Type\n");
//			fflush(dump_file);

			length = n.getList().getStarCount();
			int *field_list;

//			fprintf(dump_file, "\nStar Count %d\n", length);
//			fflush(dump_file);

			for(int i = 0; i < length; i++)
			{
				IndirectionList l(true, i+1, 0, field_list);

				Node lhs(var, l);
				Node rhs(var+1, l);
				GPU gpu(lhs, rhs);

//				fprintf(dump_file, "\nPrinting GPU\n");
//				gpu.printGPU();

				bi.insert(gpu.getGPUID());
			}
	
		}
	}

	#if 0 // PRINT_DATA
	fprintf(dump_file,"\nPrinting BI\n");
	fflush(dump_file);
	printSetOfGPUs(bi);
	fflush(dump_file);

//	fprintf(dump_file, "\nEnd of BI\n");
//	fflush(dump_file);
	#endif

	return bi;

//	RETURN(bi);
}

void GPG::initialize_GPB_worklist(struct cgraph_node *cnode)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	unsigned int start = getEntryGPB();

	#if 0
	BFS_COUNT = 0;

	BFS(cnode);
	#endif

	GPBSet gpbs = getGPBs();

	unsigned int size = gpbs.size();

	std::map< unsigned int, bool > worklist;

	#if 1
	DFS_COUNT = size;

	std::map< unsigned int, bool > label;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		label[*it] = false;
	}

	LABEL_GPB[caller_rep] = label;

	DFS(start, cnode);
	#endif

	int * wk = new int[size+1];

	unsigned int i;

	for(i = 1; i <= gpbs.size(); i++)
	{
		wk[i] = true;
	}

	GPB_worklist[caller_rep] = wk;

	#if DATA_MEAS

	GPBSet succs;
	edge_set res;
	edge_type edge;

	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[caller_rep];

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		succs = getNext(*it);

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			if(dfs_gpb[*it] >= dfs_gpb[*sit])
			{
				edge = std::make_pair(*it, *sit);

				res.insert(edge);
			}
		}
	}
	
	setBackEdges(res);
	#endif

	#if 0
	fprintf(dump_file, "\nInitializing Worklist of GPG for Function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	printInitialGPG(cnode);
	fflush(dump_file);

	GPBList wrklist;
	GPBList pending_list, finished_list;

	pending_list.push_back(start);

	unsigned int current_node_id;

	GPB current_node;
	GPBSet succs;

	while(!pending_list.empty())
	{
		current_node_id = pending_list.front(); 
		current_node = gpb_map[caller_rep][current_node_id];
		pending_list.pop_front();

		if(find(wrklist.begin(), wrklist.end(), current_node_id) == wrklist.end())
		{
			fprintf(dump_file, "\nAdding GPB %d to the worklist\n", current_node_id);
			fflush(dump_file);
			wrklist.push_back(current_node_id);
			finished_list.push_back(current_node_id);
		}

		succs = getNext(current_node_id);

		for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
		{
			if(find(finished_list.begin(), finished_list.end(), *it) == finished_list.end())
			if(find(pending_list.begin(), pending_list.end(), *it) == pending_list.end())
			{
				pending_list.push_back(*it);
			}
		}		
	}

	Function_Worklist[caller_rep] = wrklist;
	#endif

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

#if 0
void GPG::collectPTSInfo(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs;
	GPUSet gpus, temp;
	GPB gpb;
	unsigned int stmt_id;

	gpbs = getGPBs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		GPUSet res;

		gpb = gpb_map[cnode_num][*it];

		gpus = gpb.getGPUs();

		for(GPUSet::iterator sit = gpus.begin(); sit != gpus.end(); sit++)
		{
			stmt_id = get<2>(*sit);

			temp = PTS_INFO[stmt_id];
			temp.insert(*sit);
			PTS_INFO[stmt_id] = temp;
		} 
	}
}
#endif

void GPG::analyzeGPG(struct cgraph_node *cnode, bool again)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	#if TIME_MEAS
	gettimeofday (&STValBefore, NULL);
	#endif

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	if(isTop())
	{
		#if PROFILING
		RETURN_VOID();
		#else
		return;
		#endif
	}

	unsigned int current_node_id;
	GPB current_node;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nAnalyzing GPG for Procedure %s\n", cgraph_node_name(cnode));
	printInitialGPG(cnode);	
	fflush(dump_file);
	#endif

	//bool isPointstoEdge(gpu_id_type gpu)

	GPBSet gpbs = getGPBs();
	unsigned int size = gpbs.size();

	int * worklist = GPB_worklist[caller_rep];
	int i;
	bool change;
	std::map< unsigned int, unsigned int > rev_dfs_gpb = REV_DFS_GPB[caller_rep];

	for(i = 1; i <= size; i++)
	{
		current_node_id = rev_dfs_gpb[i]; 

		visited_count[caller_rep][current_node_id] = 0;
	}

	for(i = 1; i <= size; i++)
	{
		change  =  false;

		if(worklist[i])
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file," \nDereferencing the worklist\n");
			fflush(dump_file);
			#endif
			current_node_id = rev_dfs_gpb[i]; 

			worklist[i] = false;

			change = analyzeGPB(current_node_id, cnode);
		}

		if(change)
		{
			i = 0;
		}
	}

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nFirst elemnent of the worklist %s %d\n", cgraph_node_name(cnode), GPB_worklist[caller_rep][1]);
	fprintf(dump_file, "\nControl reached here before error....1 %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	delete(GPB_worklist[caller_rep]);

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nControl reached here before error....2 %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nAfter Analyzing FS part of GPG for Procedure %s\n", cgraph_node_name(cnode));
	printGPG(cnode);	
	fflush(dump_file);
	#endif

	#if 0
	while(!(Function_Worklist[caller_rep].empty()))
	{
		GPBList list_temp = Function_Worklist[caller_rep];

		current_node_id = list_temp.front();
		current_node = gpb_map[caller_rep][current_node_id];
		list_temp.pop_front();

		Function_Worklist[caller_rep] = list_temp;

		analyzeGPB(current_node_id, cnode);
	}
	#endif

	#if 0
	fprintf(dump_file, "\nGPG of function %s after analyses\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	#if !again
	GPUSet brout, temp_arr, res_arr, new_arr, t_p;
	unsigned int exit;

	exit = getExitGPB();

	#if BLOCKING
	brout = BROUT[exit];
	#else
	brout = ROUT[exit];
	#endif

	std::map< unsigned int, GPUSet > array_data = FINP[caller_rep];

	for(std::map< unsigned int, GPUSet >::iterator fit = array_data.begin(); fit != array_data.end(); fit++)
	{
		temp_arr = fit->second;

		#if 0
		for(GPUSet::iterator git = temp_arr.begin(); git != temp_arr.end(); git++)
		{
			res_arr.insert(stripUpwardsExposed(*git));
		}
		#endif

		res_arr.insert(temp_arr.begin(), temp_arr.end());
	}

	GPUSet resolved_arr = res_arr;
//	GPUSet resolved_arr = FIComposition(res_arr, cnode);
	
	#if 0
	GPUSet resolved_arr = FIComp(res_arr, cnode);
	#endif

	#if 0
	fprintf(dump_file, "\nrout in function %s\n", cgraph_node_name(cnode));
	printSetOfGPUs(brout);

	fprintf(dump_file, "\nres_arr in function %s\n", cgraph_node_name(cnode));
	printSetOfGPUs(res_arr);

	fprintf(dump_file, "\nresolved_arr in function %s\n", cgraph_node_name(cnode));
	printSetOfGPUs(resolved_arr);
	#endif

	std::tuple< GPUSet, GPUSet > new_arr_res;

	#if 0	
	#if BLOCKING
	new_arr_res = BRGen(brout, brout, resolved_arr, cnode, 0);

	new_arr = get<0>(new_arr_res);
	#else
	new_arr = RGen(brout, resolved_arr, cnode, 0);
	#endif
	#endif

	new_arr = RGen(brout, resolved_arr, cnode, 0);

	unsigned int var;
	GPUSet t_np;

	array_data.clear();
	stmt_info_type key;

	for(GPUSet::iterator nit = new_arr.begin(); nit != new_arr.end(); nit++)
	{
		var = get<0>(get<0>(*nit));

		if(!isPointstoEdge(*nit))
		{
			t_np = array_data[var];

			t_np.insert(*nit);

			array_data[var] = t_np;
		}
		else
		{
			t_p = FIP[caller_rep][var];

			t_p.insert(*nit);

			FIP[caller_rep][var] = t_p;
		}
	}

	FINP[caller_rep] = array_data;
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nAfter Analyzing FI part of GPG for Procedure %s\n", cgraph_node_name(cnode));
	printGPG(cnode);	
	fflush(dump_file);
	#endif

//	collectPTSInfo(cnode);

	#if TIME_MEAS
	gettimeofday (&STValAfter, NULL);

	unsigned long temp_time = ((STValAfter.tv_sec - STValBefore.tv_sec)*1000000L+STValAfter.tv_usec) - STValBefore.tv_usec;
	sr_op += temp_time;
	#endif

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

void GPG::get_succ_gpbs(unsigned int current_node_id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet succs = getNext(current_node_id); 

	int *wk = GPB_worklist[caller_rep];

	unsigned int order;

	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[caller_rep];

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nSuccessos of %d\n", current_node_id);
	print_set_integers(succs);
	fflush(dump_file);
	#endif
	
	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nPushing Successor %d\n", *it);
		fflush(dump_file);
		#endif

		order = dfs_gpb[*it];
		wk[order] = true;
	}

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nEnd of For Loop\n");
	fflush(dump_file);
	#endif

	GPB_worklist[caller_rep] = wk;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nUpdating the worklist\n");
	fflush(dump_file);
	#endif

	#if 0
	GPB current_node = gpb_map[caller_rep][current_node_id];

	GPBList wrklist = Function_Worklist[((function_info *)(cnode->aux))->func_num];

	for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
	{
		if(find(wrklist.begin(), wrklist.end(), *sit) == wrklist.end())
		{
			wrklist.push_back(*sit);
		}
	}

	Function_Worklist[((function_info *)(cnode->aux))->func_num] = wrklist;
	#endif
}

void GPG::get_pred_gpbs(unsigned int current_node_id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet preds = getPrev(current_node_id); 

	int * wk = GPB_worklist[caller_rep];

	unsigned int order;

	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[caller_rep];
	
	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		#if 0
		fprintf(dump_file, "\nPushing Predecessor %d\n", *it);
		fflush(dump_file);
		#endif

		order = dfs_gpb[*it];
		wk[order] = true;
	}

	GPB_worklist[caller_rep] = wk;

	#if 0
	GPB current_node = gpb_map[caller_rep][current_node_id];

	GPBList wrklist = Function_Worklist[((function_info *)(cnode->aux))->func_num];

	for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
	{
		if(find(wrklist.begin(), wrklist.end(), *sit) == wrklist.end())
		{
			wrklist.push_back(*sit);
		}
	}

	Function_Worklist[((function_info *)(cnode->aux))->func_num] = wrklist;
	#endif
}

void GPG::resolveInterval(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet ptsin)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	std::map< unsigned int, GPG > interval_map;
	interval_map = getIntervals();

	GPG res = interval_map[gpb_id];

	GPBSet gpbs = res.getGPBs();
	GPUSet in;
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isIndirectCallBlock())
		{
			res.processIndirectCall(*it, cnode, ptsin, in);
		}
		
		if(gpb.isInterval())
		{
			resolveInterval(*it, cnode, ptsin);
		
			inlineInterval(*it, cnode);
		}
	}

	res.initialize_GPB_worklist(cnode);

	res.analyzeGPG(cnode, false);

	res.optimizeGPG(cnode, false);

	interval_map[gpb_id] = res;
}

void GPG::resolveIntervalDirect(unsigned int gpb_id, struct cgraph_node *cnode)
{
	std::map< unsigned int, GPG > interval_map;
	interval_map = getIntervals();

	GPG res = interval_map[gpb_id];

	GPBSet gpbs = res.getGPBs();

	res.handlingCalls(cnode);

	res.initialize_GPB_worklist(cnode);

	res.analyzeGPG(cnode, false);

	res.optimizeGPG(cnode, false);

	interval_map[gpb_id] = res;
}

void GPG::inlineInterval(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPB temp_gpb;

	unsigned int  x = GPB_count++;

	std::map< unsigned int, GPG > interval_map = getIntervals();
	GPG res = interval_map[gpb_id];

	GPBSet preds, succs, temp, gpbs, gpbs_int;

	gpbs_int = res.getGPBs();
	gpbs = getGPBs();
	preds = getPrev(gpb_id);
	succs = getNext(gpb_id);

	unsigned int t, w, b, start, end;
	basic_block bb;

	start = res.getEntryGPB();
	end = res.getExitGPB();

	#if 0
	fprintf(dump_file, "\nGPG before inlining\n");
	printGPG(cnode);
	fprintf(dump_file, "\nInlining Interval %d with Offset %d\n", gpb_id, x);
	fprintf(dump_file, "\nGPG to be inlined\n");
	res.printGPG(cnode);
	#endif

	for(GPBSet::iterator it = gpbs_int.begin(); it != gpbs_int.end(); it++)
	{
		GPB new_gpb;

		temp_gpb = gpb_map[*it];
		b = temp_gpb.getBBIndex();

		t = *it;
		w = t+x;

		new_gpb.setId(w);

		GPB_count = w;	

		temp = res.getPrev(*it);

		#if 0
		fprintf(dump_file, "\nPredecessors of GPB in Interval = %d, and that in GPG = %d\n", t, t+x);
		print_set_integers(temp);
		#endif

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addPrev(w, *pit+x);
		}

		#if 0
		fprintf(dump_file, "\nPredecessors of Start GPB in Interval = %d, and that in GPG = %d\n", t, t+x);
		print_set_integers(preds);
		#endif

		if(start == *it)
		{
			for(GPBSet::iterator pit = preds.begin(); pit != preds.end(); pit++)
			{
				addPrev(w, *pit);
			}
		}

		#if 0
		fprintf(dump_file, "\nSuccessors of End GPB in Interval = %d, and that in GPG = %d\n", t, t+x);
		print_set_integers(succs);
		#endif

		if(end == *it)
		{
			for(GPBSet::iterator pit = succs.begin(); pit != succs.end(); pit++)
			{
				addNext(w, *pit);
			}
		}

		temp = res.getNext(*it);

		#if 0
		fprintf(dump_file, "\nSuccessors of GPB in Interval = %d, and that in GPG = %d\n", t, t+x);
		print_set_integers(temp);
		#endif

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			addNext(w, *pit+x);
		}

		GPUSet gpu_set = temp_gpb.getGPUs();
		GPUSet res_gpus;

		for(GPUSet::iterator git = gpu_set.begin(); git != gpu_set.end(); git++)
		{
			res_gpus.insert(stripUpwardsExposed(*git));
		}
		
//		new_gpb.setGPUs(res_gpus);
		new_gpb.setGPUs(res_gpus);

		new_gpb.setBBIndex(b);

		gpb_map[w] = new_gpb;

		gpbs.insert(w);

		#if 0
		temp = ori_red_map[cnode_num][b];
		temp.insert(w);
		temp.erase(t);	
		ori_red_map[cnode_num][b] = temp;
		#endif

//		bb = BASIC_BLOCK(b);

		#if 0
//		temp = ((block_information *)(bb->aux))->sblocks;
		temp = BB_START[cnode_num][b];

		for(GPBSet::iterator wit = temp.begin(); wit != temp.end(); wit++)
		{
			temp.erase(*wit);
			temp.insert(*wit+x);
		}

		BB_START[cnode_num][b] = temp;
//		((block_information *)(bb->aux))->sblocks = temp;

		temp = BB_END[cnode_num][b];
//		temp = ((block_information *)(bb->aux))->eblocks;

		for(GPBSet::iterator wit = temp.begin(); wit != temp.end(); wit++)
		{
			temp.erase(*wit);
			temp.insert(*wit+x);
		}

		BB_END[cnode_num][b] = temp;
//		((block_information *)(bb->aux))->eblocks = temp;
		#endif

		gpb_map[w] = new_gpb;
	}

	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		addNext(*it, start+x);
	}

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		addPrev(*it, end+x);
	}

	setGPBs(gpbs);
	eliminateGPB(gpb_id, cnode);

	GPBList list_temp = Function_Worklist[cnode_num];
	list_temp.push_front(start+x);
	Function_Worklist[cnode_num] = list_temp;

	#if 0
	if(checkGPGStructure(cnode, true))
	{
		fprintf(dump_file,"\nHigh Inlining Alert\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}
	#endif
}

GPUSet GPG::getCallIn(unsigned int bb_index, struct cgraph_node *cnode)
{
	#if 0
	fprintf(dump_file, "\nInside getCallIn\n");
	fflush(dump_file);
	#endif

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	basic_block bb;

	#if 0
	fflush(dump_file);
	fprintf(dump_file, "\nInside getCallIn for caller %s and call site %d\n", cgraph_node_name(cnode), bb_index);
	fflush(dump_file);

	fprintf(dump_file, "\nInside getCallIn with BB %d\n", bb_index);
	fflush(dump_file);
	#endif

//	bb = BASIC_BLOCK(bb_index);

	#if 0
	fprintf(dump_file, "\nBB Found %d\n", bb->index);
	fflush(dump_file);
	#endif

	GPBSet st_gpbs;
//	st_gpbs = ((block_information *)(bb->aux))->sblocks;
//	st_gpbs = BB_START[cnode_num][bb_index];
	GPBSet gpbs = getGPBs();
	GPBSet preds;
	GPUSet temp, res;
	unsigned int gpb_id;

	#if 0
	fprintf(dump_file, "\nGPG->CFG\n");
	fflush(dump_file);
	print_set_integers(st_gpbs);	
	fflush(dump_file);
	#endif

	for(GPBSet::iterator it = st_gpbs.begin(); it != st_gpbs.end(); it++)
	{
		gpb_id = *it;

		#if 0
		fprintf(dump_file, "\nGPB %d\n", gpb_id);
		fflush(dump_file);
		#endif

		if(gpbs.find(gpb_id) != gpbs.end())
		{
			#if 0
			fprintf(dump_file, "\nPresent in GPG\n");
			fflush(dump_file);
			#endif

			temp = PTSIN[gpb_id];

			res.insert(temp.begin(), temp.end());	
		}
		#if 0
		else
		{
			fprintf(dump_file, "\n!Present in GPG\n");
			fflush(dump_file);

			edge e;
		        edge_iterator ei;
			basic_block bt;

		       	FOR_EACH_EDGE(e,ei,bb->preds)
       			{
               			bt = e->src;

				if(bt->index == 0)
				{
					continue;
				}

				fprintf(dump_file, "\nPred of BB %d is BT %d\n", bb->index, bt->index);
				fflush(dump_file);

				temp = getCallIn(bt->index, cnode);

				res.insert(temp.begin(), temp.end());	
			}
		}
		#endif
	}

	return res;
}

GPUSet GPG::filterGPUs(node_id_type node, GPUSet gpus, bool type)
{
	GPUSet res;
	
	visited_nodes.insert(node);
	
	Node n = getNode(node);

	unsigned int var = n.getVarIndex();
	unsigned int lhs_var, rhs_var;
	unsigned int lhs_varp, rhs_varp, varp;

	if(CDV.find(var) != CDV.end())
		var--;
	
	int f[IndirectionList::kSize];
	IndirectionList list(false, 0, 0, f);

	Node lhs, rhs;
	Node lhsp, rhsp, np;
	IndirectionList lhs_il, rhs_il, n_il;

	n_il = n.getList();

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		if(isBoundaryGPU(*it))
		{
			continue;
		}

		lhs = getNode(get<0>(*it));		

		rhs = getNode(get<1>(*it));		

		lhs_var = lhs.getVarIndex();
		rhs_var = rhs.getVarIndex();

		lhs_il = lhs.getList();

		lhsp = lhs.conDep();
		np = n.conDep();

		lhs_varp = lhsp.getVarIndex();
		varp = np.getVarIndex();

		if(lhs_varp == varp)
		{
			if(lhs_il.isPrefix(n_il))
			{
				res.insert(*it);

				if(rhs_var > 4)
				{
					std::vector< IndirectionList > rem, fin;

					rem = n_il.remainder(lhs_il);

					for(std::vector< IndirectionList >::iterator iit = rem.begin(); iit != rem.end(); iit++)
					{
						if(iit->Length() == 0 && !type)
						{
							continue;
						}
						else if(iit->Length() == 1 && type)
						{
							continue;
						}

						definitions new_nodes;
						GPUSet temp1;
						new_nodes = getAllNodes(rhs_var, *iit);

						for(definitions::iterator dit = new_nodes.begin(); dit != new_nodes.end(); dit++)
						{
							if(visited_nodes.find(*dit) != visited_nodes.end())
							{
								continue;
							}

							temp1 = filterGPUs(*dit, gpus, type);

							res.insert(temp1.begin(), temp1.end());
						}
					}
				}	
			}
		}

	}

	return res;
}

GPUSet GPG::filterBI(GPUSet temp, struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	definitions ldef, rdef;
	GPUSet temp_set, res;

	ldef = lhsUpwardsExposedDefinitions[cnode_num];
	rdef = rhsUpwardsExposedDefinitions[cnode_num];

	for(definitions::iterator it = ldef.begin(); it != ldef.end(); it++)
	{
		visited_nodes.clear();

		temp_set = filterGPUs(*it, temp, true);

		res.insert(temp_set.begin(), temp_set.end());
	}

	for(definitions::iterator it = rdef.begin(); it != rdef.end(); it++)
	{
		visited_nodes.clear();

		temp_set = filterGPUs(*it, temp, false);

		res.insert(temp_set.begin(), temp_set.end());
	}

	return res;
}

GPUSet GPG::computeBI(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	basic_block bb;
	call_site_info info;

	#if 0
	fprintf(dump_file, "\nInside computeBI for function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	unsigned int call;
	struct cgraph_node *node;
	GPUSet BI, temp;
	GPUSet parGPUs, pGPUs;
	definitions temp_def;

	set_call_pts::iterator sit;

        sit = ((function_info *)(cnode->aux))->call_pts.begin();

	for(sit; sit != ((function_info *)(cnode->aux))->call_pts.end(); sit++)
        {
                node = func_numbering[get<0>(*sit)];

		call = get<1>(*sit);

		push_cfun (DECL_STRUCT_FUNCTION (node->decl));

		bb = BASIC_BLOCK(call);

		pGPUs = map_args_para_call(cnode, bb, node);

		pop_cfun();

		definitions x_nodes;

		for(GPUSet::iterator pit = pGPUs.begin(); pit != pGPUs.end(); pit++)
		{
			x_nodes.insert(get<1>(*pit));
		}

		temp_def = lhsUpwardsExposedDefinitions[cnode_num];
		temp_def.insert(x_nodes.begin(), x_nodes.end());
		lhsUpwardsExposedDefinitions[cnode_num] = temp_def;

		temp_def = rhsUpwardsExposedDefinitions[cnode_num];
		temp_def.insert(x_nodes.begin(), x_nodes.end());
		rhsUpwardsExposedDefinitions[cnode_num] = temp_def;

		parGPUs.insert(pGPUs.begin(), pGPUs.end());
	}

	info = CallerCallSite[cnode_num];

	for(call_site_info::iterator it = info.begin(); it != info.end(); it++)
	{
		node = func_numbering[get<0>(*it)];

		call = get<1>(*it);

		temp = PTSIN[call];

		temp = filterBI(temp, cnode);

		BI.insert(temp.begin(), temp.end());
	}

	BI = filterBI(BI, cnode);

	unsigned int start = getEntryGPB();
	GPUSet temp_set = PTSOUT[start];
	temp_set.insert(parGPUs.begin(), parGPUs.end());
	PTSOUT[start] = temp_set;

	return BI;

//	temp_set = PTSIN[start];
//	temp_set.insert(BI.begin(), BI.end());
//	PTSIN[start] = temp_set;
}

void GPG::computePointstoGPB(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	unsigned int count = visited_count[cnode_num][gpb_id];

	#if 0
	if(count > 10)
	{
		fprintf(dump_file, "\nToo Many Iterations: Processed GPB %d of Function %s too many times\n", gpb_id, cgraph_node_name(cnode));

		
//		exit(1);
	}
	else
	{
		visited_count[cnode_num][gpb_id] = ++count;
	}
	#endif

	GPB gpb = gpb_map[gpb_id];
	
	std::tuple< GPUSet, GPUSet, GPUSet > result;
	
	#if 0
	fprintf(dump_file,"\nComputing PTSTO for GPB %d\n", gpb_id); 
	fflush(dump_file);
	#endif

	std::pair< GPUSet, GPUSet > res;
	GPUSet gpus;

	#if 0
	fprintf(dump_file, "\nHiyaa Before %d\n", gpb.getBBIndex());
	fflush(dump_file);
	#endif

	basic_block bb = BASIC_BLOCK(gpb.getBBIndex());

	GPUSet ptsin, prev_ptsin, ptsout, prev_ptsout;

	unsigned int start_node_id = getEntryGPB(); 

	if(start_node_id == gpb_id)
	{
		ptsin = computeBI(gpb_id, cnode);

		#if 0
		fprintf(dump_file, "\nStart Node %d\n", gpb_id);
		fflush(dump_file);

		fprintf(dump_file, "\nHiyaa After123\n");
		fflush(dump_file);
		#endif
	}
	else
	{
		ptsin = get_ptsin(gpb_id, cnode);

		#if 0
		fprintf(dump_file, "\n!Start Node %d\n", gpb_id);
		fflush(dump_file);

		fprintf(dump_file, "\nHiyaa After456\n");
		fflush(dump_file);
		#endif
	}

	if(gpb.isCallBlock())
	{
		#if 0
		fprintf(dump_file, "\nDirect Call\n");
		fflush(dump_file);
		#endif

		GPBSet to_be_analyzed, atemp;

		unsigned int callee_rep = gpb.getCallee();
		struct cgraph_node *callee_node = func_numbering[callee_rep];

		GPG gpg_callee = optimized_GPG_map[callee_rep];

		if(gpg_callee.isTop())
		{
			eliminateGPB(gpb_id, cnode);

			if(gpb_id == getEntryGPB())
			{
				setTop();
			}
		}
		else
		{
			if(gpg_callee.isIdentityGPG(callee_node, false))
			{
				#if 0
				fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee_node));
				fflush(dump_file);
				#endif

				if(gpb_id == getEntryGPB())
				{
					to_be_analyzed.insert(gpb_id);

					eraseDirectCallGPB(gpb_id, cnode_num);
				}
				else
				{
					eliminateEmptyGPB(gpb_id, cnode);
				}
			}
			else
			{
				GPUSet maygen, mustkill;
				definitions lup, rup;

				lup = lhsUpwardsExposedDefinitions[callee_rep];
				rup = rhsUpwardsExposedDefinitions[callee_rep];
				maygen = DownwardsExposedMayDefinitions[callee_rep];
				mustkill = DownwardsExposedMustDefinitions[callee_rep];
		
				GPBSet dcalls, icalls, intervals_t;
				dcalls = gpg_callee.getCallBlocks(callee_node);
				icalls = gpg_callee.getIndirectCallBlocks(callee_node);
				intervals_t = gpg_callee.getIntervalBlocks(callee_node);

				if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
				{
					if(gpb_id == getEntryGPB())
					{
						to_be_analyzed.insert(gpb_id);

						eraseDirectCallGPB(gpb_id, cnode_num);
					}
					else
					{
						eliminateEmptyGPB(gpb_id, cnode);
					}
				}
				else
				{
//					fprintf(dump_file, "\nActually Inlining\n");

					atemp = inlineCall(gpb_id, callee_rep, cnode_num, bb, gpg_callee);

					to_be_analyzed.insert(atemp.begin(), atemp.end());
				}
			}
		}

		if(!gpg_callee.isTop())
		{
			GPBList list_temp = Function_Worklist[cnode_num];

			for(GPBSet::iterator lit = to_be_analyzed.begin(); lit != to_be_analyzed.end(); lit++)
			{
				list_temp.push_front(*lit);
			}

			Function_Worklist[cnode_num] = list_temp;
		}

		return;
	}
	else if(gpb.isInterval())
	{
		#if 0
		fprintf(dump_file, "\nInterval\n");
		fflush(dump_file);
		#endif

		resolveInterval(gpb_id, cnode, ptsin);

		inlineInterval(gpb_id, cnode);

		return;
	}
	#if INTDIR
	else if(gpb.isIntervalDirect())
	{
		#if 0
		fprintf(dump_file, "\nInterval Direct\n");
		fflush(dump_file);
		#endif

		resolveIntervalDirect(gpb_id, cnode);

		inlineInterval(gpb_id, cnode);

		return;
	}	
	#endif
	else if(gpb.isIndirectCallBlock())
	{
		#if 0
		fprintf(dump_file, "\nIndirect Call\n");
		fflush(dump_file);
		#endif

		GPUSet brin;

		processIndirectCall(gpb_id, cnode, ptsin, brin);

		return;
	}

	gpus = gpb.getGPUs();

	#if 0
	fprintf(dump_file, "\nPTSIN: %d", ptsin.size());
	fflush(dump_file);
	printSetOfGPUs(ptsin);
	fflush(dump_file);
	fprintf(dump_file, "\nDelta: ");
	fflush(dump_file);
	printSetOfGPUs(gpus);
	fflush(dump_file);
	#endif

	GPUSet ptsgen, array_data_temp, array_data;
	std::tuple< GPUSet, GPUSet > temp_res1;

	definitions dfp_t;

	temp_res1 = ReachingGPUsAnalysis(ptsin, gpus, cnode, gpb_id, dfp_t);
	ptsout = get<0>(temp_res1);
	ptsgen = get<1>(temp_res1);

	prev_ptsout = PTSOUT[gpb_id];

	#if 1
	ptsin.insert(prev_ptsin.begin(), prev_ptsin.end());

	ptsout.insert(prev_ptsout.begin(), prev_ptsout.end());
	#endif

	PTSIN[gpb_id] = ptsin;

	PTSOUT[gpb_id] = ptsout;

	//if(!(prev_rout == rout))
	if(!(prev_ptsout == ptsout))
        {
		#if 0
		fprintf(dump_file, "\nRecording PTS with change PTSOUT GPB %d of Function %s ", gpb_id, cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUIDs(ptsout);
		fprintf(dump_file, "\n\n");
		fflush(dump_file);
		#endif

		get_succ_gpbs(gpb_id, cnode);
	}
	#if 0
	else
	{
		fprintf(dump_file, "\nRecording PTS without change PTSOUT GPB %d of Function %s ", gpb_id, cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUIDs(ptsout);
		fprintf(dump_file, "\n\n");
		fflush(dump_file);
	}
	#endif
}

bool GPG::analyzeGPB(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	unsigned int count = visited_count[caller_rep][gpb_id];

	visited_count[caller_rep][gpb_id] = ++count;

	GPB gpb = gpb_map[gpb_id];
	
	std::tuple< GPUSet, GPUSet, GPUSet > result;
	
	#if 0 //PRINT_DATA
	fprintf(dump_file,"\nProcessing GPB %d\n", gpb_id); 
	fflush(dump_file);
	#endif

	std::pair< GPUSet, GPUSet > res;
	GPUSet gpus;

	GPUSet rin, brin, prev_rin, prev_brin, prev_rout, prev_brout;

	unsigned int start_node_id = getEntryGPB(); 

	if(start_node_id == gpb_id)
	{
//		rin = RIN[start_node_id];
//		brin = BRIN[start_node_id];

		#if BLOCKING
		rin = BDEFS[caller_rep];
		brin = BDEFS[caller_rep];
		#else
		rin = BDEFS[caller_rep];
		#endif

		#if 0 // PRINT_DATA
		fprintf(dump_file, "\nBI\n");
		fflush(dump_file);
		printSetOfGPUs(rin);
		fflush(dump_file);
		#endif
	}
	else
	{
		#if BLOCKING
		rin = get_rin(gpb_id, cnode);
		brin = get_brin(gpb_id, cnode);
		#else
		rin = get_rin(gpb_id, cnode);
		#endif
	}

	prev_rin = RIN[gpb_id];
	prev_brin = BRIN[gpb_id];

	#if BLOCKING
	if((prev_rin == rin) && (prev_brin == brin) && visited_count[caller_rep][gpb_id] != 1)
	#else
	if((prev_rin == rin) && visited_count[caller_rep][gpb_id] != 1)
	#endif
	{
		return false;
	}

	if(gpb.isIndirectCallBlock())
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nIndirect Call GPB\n");
		#endif

		unsigned int main_num = ((function_info *)(main_cnode->aux))->func_num;

		GPUSet static_init = BDEFS[main_num];

		GPUSet top, prev_rout, prev_brout, rout, brout;

		prev_rout = ROUT[gpb_id];
		prev_brout = BROUT[gpb_id];

		prev_rin = RIN[gpb_id];
		prev_brin = BRIN[gpb_id];

		rin.insert(prev_rin.begin(), prev_rin.end());
		brin.insert(prev_brin.begin(), prev_brin.end());

		rin.insert(static_init.begin(), static_init.end());
		brin.insert(static_init.begin(), static_init.end());

		RIN[gpb_id] = rin;

		BRIN[gpb_id] = brin;
//		BROUT[gpb_id] = top;
//		ROUT[gpb_id] = top;

		processIndirectCall(gpb_id, cnode, rin, brin);	

		#if 0
		if(!(prev_rout == top) || !(prev_brout == top))
        	{
			get_succ_gpbs(gpb_id, cnode);

		}
		#endif

		return(true);
	}


	gpus = gpb.getOrigGPUs();

	GPUSet delta;
	delta = FIComp(gpus, cnode); 
	

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nRIN for GPB %d and Function %s\n", gpb_id, cgraph_node_name(cnode));
	fflush(dump_file);
	printSetOfGPUs(rin);
	fflush(dump_file);
	fprintf(dump_file, "\nBRIN: ");
	fflush(dump_file);
	printSetOfGPUs(brin);
	fflush(dump_file);
	fprintf(dump_file, "\nDelta: ");
	fflush(dump_file);
	printSetOfGPUs(delta);
	fflush(dump_file);
	#endif

	GPUSet queued, rout, brout, brgen, ind_gpus, rgen, array_data_temp, array_data;
	std::tuple< GPUSet, GPUSet > temp_res1;

	#if BLOCKING
	rin.insert(prev_rin.begin(), prev_rin.end());

	brin.insert(prev_brin.begin(), prev_brin.end());
	#else
	rin.insert(prev_rin.begin(), prev_rin.end());
	#endif

	definitions dfp = DFP[gpb_id];
	
	temp_res1 = ReachingGPUsAnalysis(rin, delta, cnode, gpb_id, dfp);
	rout = get<0>(temp_res1);
	rgen = get<1>(temp_res1);

	rgen = FIComp(rgen, cnode); // Newly Added

	#if BLOCKING
	std::tuple< GPUSet, GPUSet, GPUSet > temp_res;

	temp_res =  ReachingGPUsAnalysisWB(rin, brin, delta, cnode, gpb_id, dfp);
	brout = get<0>(temp_res);
	queued = get<1>(temp_res);
	brgen = get<2>(temp_res);

	brgen = FIComp(brgen, cnode); // Newly Added
	#endif

	GPUSet up;
	#if BLOCKING
	up = brgen;
	#else
	up = rgen;
	#endif
	
	std::map< unsigned int, GPUSet > fi_data = FINP[caller_rep];
	GPUSet t_up;

	for(std::map< unsigned int, GPUSet >::iterator fit = fi_data.begin(); fit != fi_data.end(); fit++)
	{
		t_up = fit->second;

		up.insert(t_up.begin(), t_up.end());
	}

	collectUpwardExposedVersions(up, cnode);

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nBRGen for GPB %d and Function %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(brgen);
	fprintf(dump_file, "\nBROut\n");
	printSetOfGPUs(brout);
	fprintf(dump_file, "\nqueued\n");
	printSetOfGPUs(queued);
	#endif

	#if BLOCKING
	for(GPUSet::iterator git = brgen.begin(); git != brgen.end(); git++)
	{
		if(isIndirectGPU(*git))
		{
			ind_gpus.insert(*git);
		}
	}

	GPUSet temp_queued = Queued[caller_rep];

	temp_queued.insert(queued.begin(), queued.end());

	Queued[caller_rep] = temp_queued;

	GPUSet temp_pros = prospectiveProducerGPUs[caller_rep];
	temp_pros.insert(ind_gpus.begin(), ind_gpus.end());

	prospectiveProducerGPUs[caller_rep] = temp_pros;
	#endif

	#if BLOCKING
	gpb.setGPUs(brgen);
	#else
	gpb.setGPUs(rgen);
	#endif

	gpb_map[gpb_id] = gpb;

	prev_rout = ROUT[gpb_id];
	prev_brout = BROUT[gpb_id];

	#if BLOCKING
	rout.insert(prev_rout.begin(), prev_rout.end());

	brout.insert(prev_brout.begin(), prev_brout.end());
	#else
	rout.insert(prev_rout.begin(), prev_rout.end());
	#endif

	#if HEURISTICS
	GPUSet top;
	bool resolved = true;

	if(gpb.isSymGPB())
	{	
		#if Blocking
		for(GPUSet::iterator gc = brgen.begin(); gc != brgen.end(); gc++)
		#else
		for(GPUSet::iterator gc = rgen.begin(); gc != rgen.end(); gc++)
		#endif
		{
			if(!isPointstoInformation(*gc))
			{
				resolved = false;
				break;
			}
		}

		if(resolved)
		{
			gpb.setResolved();
			gpb_map[gpb_id] = gpb;
		}	

		#if BLOCKING
		GPUSet temp_out1, temp_out2;

		temp_out1 = rin;
		temp_out1.insert(rout.begin(), rout.end());

		temp_out2 = brin;
		temp_out2.insert(brout.begin(), brout.end());

		BROUT[gpb_id] = temp_out2;
		ROUT[gpb_id] = temp_out1;

		RIN[gpb_id] = rin;
		BRIN[gpb_id] = brin;

		#else
		GPUSet temp_out1;

		temp_out1 = rin;
		temp_out1.insert(rout.begin(), rout.end());

		RIN[gpb_id] = rin;

		ROUT[gpb_id] = temp_out1;
		#endif
	}
	else
	{
		#if BLOCKING
		RIN[gpb_id] = rin;
		ROUT[gpb_id] = rout;

		BRIN[gpb_id] = brin;
		BROUT[gpb_id] = brout;
		#else
		RIN[gpb_id] = rin;
		ROUT[gpb_id] = rout;
		#endif
	}
	#else
	#if BLOCKING
	RIN[gpb_id] = rin;
	ROUT[gpb_id] = rout;

	BRIN[gpb_id] = brin;
	BROUT[gpb_id] = brout;
	#else
	RIN[gpb_id] = rin;
	ROUT[gpb_id] = rout;
	#endif
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nStatistics\n");
	fprintf(dump_file, "\nDelta: ");
	fflush(dump_file);
	printSetOfGPUs(delta);
	fflush(dump_file);
	printSetOfGPUs(BROUT[gpb_id]);
	fprintf(dump_file, "\nBRGEN");
	printSetOfGPUs(brgen);
	fprintf(dump_file, "\nQueued");
	printSetOfGPUs(Queued[caller_rep]);
	fprintf(dump_file, "\n\n");
	fflush(dump_file);
	fprintf(dump_file, "\nROUT");
	printSetOfGPUs(ROUT[gpb_id]);
	fflush(dump_file);
	fprintf(dump_file, "\nBROUT");
	printSetOfGPUs(BROUT[gpb_id]);
	fflush(dump_file);
	#endif

	computeDFP(gpb_id);	

/*
	GPUSet dfp_temp;

	dfp_temp = BROUT[gpb_id];

	definitions dfp_out;

	for(GPUSet::iterator it = dfp_temp.begin(); it != dfp_temp.end(); it++)
	{
		if(isBoundaryGPU(*it))
		{
			dfp_out.insert(get<0>(*it));	
		}	
	}	

	DFP[gpb_id] = dfp_out;
*/

	#if BLOCKING
	if(!(prev_rout == rout) || !(prev_brout == brout))
	#else
	if(!(prev_rout == rout))
	#endif
        {
		get_succ_gpbs(gpb_id, cnode);

		return(true);		
	}
	else
	{
		return(false);		
	}	
}

void GPG::computeDFP(unsigned int gpb_id)
{
	GPUSet in, out, delta, diff, diff1;
	definitions dfp, defined, preserved;

	GPB gpb = gpb_map[gpb_id];

	in = BRIN[gpb_id];
	out = BROUT[gpb_id];

	delta = gpb.getGPUs();

	set_intersection(out.begin(), out.end(), in.begin(), in.end(), inserter(diff, diff.end()));
	set_difference(diff.begin(), diff.end(), delta.begin(), delta.end(), inserter(diff1, diff1.end()));

	for(GPUSet::iterator it = diff1.begin(); it != diff1.end(); it++)
	{
		preserved.insert(get<0>(*it));
	}
	
	for(GPUSet::iterator it = delta.begin(); it != delta.end(); it++)
	{
		defined.insert(get<0>(*it));
	}

	set_intersection(defined.begin(), defined.end(), preserved.begin(), preserved.end(), inserter(dfp, dfp.end()));

	DFP[gpb_id] = dfp;
}

#if 0
bool GPG::analyzeGPB(unsigned int gpb_id, struct cgraph_node *cnode)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	unsigned int count = visited_count[caller_rep][gpb_id];

	visited_count[caller_rep][gpb_id] = ++count;

	#if 0
	if(count > 50)
	{
		fprintf(dump_file, "\nToo Many Iterations: Processed GPB %d of Function %s too many times\n", gpb_id, cgraph_node_name(cnode));

		fprintf(stderr, "\nToo Many Iterations: Processed GPB %d of Function %s too many times\n", gpb_id, cgraph_node_name(cnode));
		
//		exit(1);
	}
	else
	{
		visited_count[caller_rep][gpb_id] = ++count;
	}
	#endif

	GPB gpb = gpb_map[gpb_id];
	
	std::tuple< GPUSet, GPUSet, GPUSet > result;
	
	#if PRINT_DATA
	fprintf(dump_file,"\nProcessing GPB %d\n", gpb_id); 
	fflush(dump_file);
	#endif

	std::pair< GPUSet, GPUSet > res;
	GPUSet gpus;

	GPUSet rin, brin, prev_rin, prev_brin, prev_rout, prev_brout;

	unsigned int start_node_id = getEntryGPB(); 

	if(start_node_id == gpb_id)
	{
//		rin = RIN[start_node_id];
//		brin = BRIN[start_node_id];

		#if BLOCKING
		rin = BDEFS[caller_rep];
		brin = BDEFS[caller_rep];
		#else
		rin = BDEFS[caller_rep];
		#endif

		#if 0 // PRINT_DATA
		fprintf(dump_file, "\nBI\n");
		fflush(dump_file);
		printSetOfGPUs(rin);
		fflush(dump_file);
		#endif
	}
	else
	{
		#if BLOCKING
		rin = get_rin(gpb_id, cnode);
		brin = get_brin(gpb_id, cnode);
		#else
		rin = get_rin(gpb_id, cnode);
		#endif
	}

	prev_rin = RIN[gpb_id];
	prev_brin = BRIN[gpb_id];

	#if PRINT_DATA
	fprintf(dump_file, "\nRequired Intervention\n");
	fflush(dump_file);

	if(prev_rin == rin)
	{
		fprintf(dump_file, "\nprev_rin == rin\n");
		fflush(dump_file);
	}
	else
	{
		fprintf(dump_file, "\nprev_rin != rin\n");
		fflush(dump_file);
	}
	if(prev_brin == brin)
	{
		fprintf(dump_file, "\nprev_brin == brin\n");
		fflush(dump_file);
	}
	else
	{
		fprintf(dump_file, "\nprev_brin != brin\n");
		fflush(dump_file);
	}
	#endif

	#if BLOCKING
	if((prev_rin == rin) && (prev_brin == brin) && visited_count[caller_rep][gpb_id] != 1)
	#else
	if((prev_rin == rin) && visited_count[caller_rep][gpb_id] != 1)
	#endif
	{
		#if PRINT_DATA
		fprintf(dump_file, "\nReturn without processing\n");
		fflush(dump_file);
		#endif

		#if PROFILING
		RETURN(false);
		#else
		return false;
		#endif
	}

	#if PRINT_DATA
	fprintf(dump_file, "\nRIN for GPB %d function %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(rin);	
	fprintf(dump_file, "\nGPB %d of Function %s is visited %d times\n", gpb_id, cgraph_node_name(cnode), visited_count[caller_rep][gpb_id]);
	fflush(dump_file);

	if(visited_count[caller_rep][gpb_id] > 1 && rin.size() == 0)	
	{
		fprintf(dump_file, "\nSpecial Alert: RIN Wiped Out\n");
	}
	#endif

	#if 0
	if(gpb.isCallBlock())// || gpb.isExitCallBlock())
	{
//		fprintf(dump_file, "\nHey\n");

		GPUSet top, prev_rout, prev_brout;

		prev_rout = ROUT[gpb_id];
		prev_brout = BROUT[gpb_id];
		
		#if 1
		prev_rin = RIN[gpb_id];
		prev_brin = BRIN[gpb_id];

		rin.insert(prev_rin.begin(), prev_rin.end());
		brin.insert(prev_brin.begin(), prev_brin.end());

//		rout.insert(prev_rout.begin(), prev_rout.end());
//		brout.insert(prev_brout.begin(), prev_brout.end());
		#endif

		RIN[gpb_id] = rin;
		ROUT[gpb_id] = top;

		BRIN[gpb_id] = brin;
		BROUT[gpb_id] = top;

		if(!(prev_rout == top) || !(prev_brout == top))
        	{
			get_succ_gpbs(gpb_id, cnode);

			#if PROFILING
			RETURN(true);
			#else
			return(true);
			#endif
		}

		#if PROFILING
		RETURN(false);
		#else
		return(false);
		#endif

//		RETURN_VOID();

//		return;
	}
	else if(gpb.isInterval())
	{
		fprintf(dump_file, "\nInterval GPB\n");

		#if 1 //!FP
		GPUSet top, prev_rout, prev_brout;

		prev_rout = ROUT[caller_rep][gpb_id];
		prev_brout = BROUT[caller_rep][gpb_id];

		#if 1
		prev_rin = RIN[caller_rep][gpb_id];
		prev_brin = BRIN[caller_rep][gpb_id];

		rin.insert(prev_rin.begin(), prev_rin.end());
		brin.insert(prev_brin.begin(), prev_brin.end());

//		rout.insert(prev_rout.begin(), prev_rout.end());
//		brout.insert(prev_brout.begin(), prev_brout.end());
		#endif

		RIN[caller_rep][gpb_id] = rin;
		ROUT[caller_rep][gpb_id] = top;

		BRIN[caller_rep][gpb_id] = brin;
		BROUT[caller_rep][gpb_id] = top;

		if(!(prev_rout == top) || !(prev_brout == top))
        	{
			get_succ_gpbs(gpb_id, cnode);
		}
		#endif

		RETURN_VOID();

//		return;
	}
	else if(gpb.isIntervalDirect())
	{
//		fprintf(dump_file, "\nInterval GPB\n");

		#if 1 //!FP
		GPUSet top, prev_rout, prev_brout;

		prev_rout = ROUT[caller_rep][gpb_id];
		prev_brout = BROUT[caller_rep][gpb_id];

		#if 1
		prev_rin = RIN[caller_rep][gpb_id];
		prev_brin = BRIN[caller_rep][gpb_id];

		rin.insert(prev_rin.begin(), prev_rin.end());
		brin.insert(prev_brin.begin(), prev_brin.end());

//		rout.insert(prev_rout.begin(), prev_rout.end());
//		brout.insert(prev_brout.begin(), prev_brout.end());
		#endif

		RIN[caller_rep][gpb_id] = rin;
		ROUT[caller_rep][gpb_id] = top;

		BRIN[caller_rep][gpb_id] = brin;
		BROUT[caller_rep][gpb_id] = top;

		if(!(prev_rout == top) || !(prev_brout == top))
        	{
			get_succ_gpbs(gpb_id, cnode);

			#if PROFILING
			RETURN(true);
			#else
			return(true);
			#endif
		}
		#endif

		#if PROFILING
		RETURN(false);
		#else
		return(false);
		#endif

//		RETURN_VOID();

//		return;
	}
	else if(gpb.isIndirectCallBlock())
	{
//		fprintf(dump_file, "\nIndirect Call GPB\n");

		#if 1 //!FP
		GPUSet top, prev_rout, prev_brout;

		prev_rout = ROUT[gpb_id];
		prev_brout = BROUT[gpb_id];

		#if 1
		prev_rin = RIN[gpb_id];
		prev_brin = BRIN[gpb_id];

		rin.insert(prev_rin.begin(), prev_rin.end());
		brin.insert(prev_brin.begin(), prev_brin.end());

//		rout.insert(prev_rout.begin(), prev_rout.end());
//		brout.insert(prev_brout.begin(), prev_brout.end());
		#endif

		RIN[gpb_id] = rin;
		ROUT[gpb_id] = top;

		BRIN[gpb_id] = brin;
		BROUT[gpb_id] = top;

		if(!(prev_rout == top) || !(prev_brout == top))
        	{
			get_succ_gpbs(gpb_id, cnode);

			#if PROFILING
			RETURN(true);
			#else
			return(true);
			#endif
		}
		#endif

		#if 0
		processIndirectCall(gpb_id, cnode, rin, brin);	
		#endif

		#if PROFILING
		RETURN(false);
		#else
		return(false);
		#endif

//		RETURN_VOID();

//		return;
	}
	#endif

//	fprintf(dump_file, "\nHey U1223\n");

	gpus = gpb.getOrigGPUs();

//	GPUSet delta = FIComposition(gpus, cnode);
	GPUSet delta;
	delta = FIComp(gpus, cnode); // Uncomment
	

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nRIN: ");
	fflush(dump_file);
	printSetOfGPUs(rin);
	fflush(dump_file);
	fprintf(dump_file, "\nBRIN: ");
	fflush(dump_file);
	printSetOfGPUs(brin);
	fflush(dump_file);
	fprintf(dump_file, "\nDelta: ");
	fflush(dump_file);
	printSetOfGPUs(delta);
	fflush(dump_file);
	#endif

	GPUSet queued, rout, brout, brgen, ind_gpus, rgen, array_data_temp, array_data;
	std::tuple< GPUSet, GPUSet > temp_res1;

	#if BLOCKING
	rin.insert(prev_rin.begin(), prev_rin.end());

	brin.insert(prev_brin.begin(), prev_brin.end());
	#else
	rin.insert(prev_rin.begin(), prev_rin.end());
	#endif
	
//	fprintf(dump_file, "\nBefore Reaching GPUs Analysis without Blocking\n");
//	fflush(dump_file);

	temp_res1 = ReachingGPUsAnalysis(rin, delta, cnode, gpb_id);
	rout = get<0>(temp_res1);
	rgen = get<1>(temp_res1);

	rgen = FIComp(rgen, cnode); // Newly Added

//	fprintf(dump_file, "\nAfter Reaching GPUs Analysis without Blocking\n");
//	fflush(dump_file);

	#if BLOCKING
	std::tuple< GPUSet, GPUSet, GPUSet > temp_res;

//	fprintf(dump_file, "\nBefore Reaching GPUs Analysis with Blocking %s, %d\n", cgraph_node_name(cnode), gpb_id);
//	fflush(dump_file);

	temp_res =  ReachingGPUsAnalysisWB(rin, brin, delta, cnode, gpb_id);
	brout = get<0>(temp_res);
	queued = get<1>(temp_res);
	brgen = get<2>(temp_res);

	brgen = FIComp(brgen, cnode); // Newly Added
	#endif

//	fprintf(dump_file, "\nAfter Reaching GPUs Analysis with Blocking\n");
//	fflush(dump_file);

	GPUSet up;
	#if BLOCKING
	up = brgen;
	#else
	up = rgen;
	#endif
	
	std::map< unsigned int, GPUSet > fi_data = FINP[caller_rep];
	GPUSet t_up;

	for(std::map< unsigned int, GPUSet >::iterator fit = fi_data.begin(); fit != fi_data.end(); fit++)
	{
		t_up = fit->second;

		up.insert(t_up.begin(), t_up.end());
	}

//	fprintf(dump_file, "\nBefore Collecting upwards exposed\n");
//	fflush(dump_file);

	collectUpwardExposedVersions(up, cnode);

//	fprintf(dump_file, "\nAfter Collecting upwards exposed\n");
//	fflush(dump_file);

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nBRGen for GPB %d and Function %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(brgen);
	fprintf(dump_file, "\nBROut\n");
	printSetOfGPUs(brout);
	fprintf(dump_file, "\nqueued\n");
	printSetOfGPUs(queued);
	#endif

	#if BLOCKING
	for(GPUSet::iterator git = brgen.begin(); git != brgen.end(); git++)
	{
		if(isIndirectGPU(*git))
		{
			ind_gpus.insert(*git);
		}
	}

	GPUSet temp_queued = Queued[caller_rep];

	temp_queued.insert(queued.begin(), queued.end());

	Queued[caller_rep] = temp_queued;

	GPUSet temp_pros = prospectiveProducerGPUs[caller_rep];
	temp_pros.insert(ind_gpus.begin(), ind_gpus.end());

	prospectiveProducerGPUs[caller_rep] = temp_pros;
	#endif

//	fprintf(dump_file, "\nFinal BRGEN\n");
//	printSetOfGPUs(brgen);

//	gpb.setGPUs(rgen);

	#if BLOCKING
	gpb.setGPUs(brgen);
	#else
	gpb.setGPUs(rgen);
	#endif

	gpb_map[gpb_id] = gpb;

	prev_rout = ROUT[gpb_id];
	prev_brout = BROUT[gpb_id];

	#if BLOCKING
	rout.insert(prev_rout.begin(), prev_rout.end());

	brout.insert(prev_brout.begin(), prev_brout.end());
	#else
	rout.insert(prev_rout.begin(), prev_rout.end());
	#endif

	#if HEURISTICS
	GPUSet top;
	bool resolved = true;

	if(gpb.isSymGPB())
	{	
		#if Blocking
		for(GPUSet::iterator gc = brgen.begin(); gc != brgen.end(); gc++)
		#else
		for(GPUSet::iterator gc = rgen.begin(); gc != rgen.end(); gc++)
		#endif
		{
			if(!isPointstoInformation(*gc))
			{
				resolved = false;
				break;
			}
		}

		if(resolved)
		{
			gpb.setResolved();
			gpb_map[gpb_id] = gpb;
		}	

		#if BLOCKING

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nHeuristics with Blocking for %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		fprintf(dump_file, "\nBROUT - Heuristics with Blocking for %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUs(brout);
		fflush(dump_file);
		fprintf(dump_file, "\nROUT - Heuristics with Blocking for %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUs(rout);
		fflush(dump_file);
		#endif

		GPUSet temp_out1, temp_out2;

		temp_out1 = rin;
		temp_out1.insert(rout.begin(), rout.end());

		temp_out2 = brin;
		temp_out2.insert(brout.begin(), brout.end());

		BROUT[gpb_id] = temp_out2;
		ROUT[gpb_id] = temp_out1;

		RIN[gpb_id] = rin;
		BRIN[gpb_id] = brin;

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nHeuristics with Blocking (after setting the values) for %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		fprintf(dump_file, "\nBROUT - Heuristics with Blocking for %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUs(BROUT[gpb_id]);
		fflush(dump_file);
		fprintf(dump_file, "\nROUT - Heuristics with Blocking for %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUs(ROUT[gpb_id]);
		fflush(dump_file);
		#endif
		#else
		GPUSet temp_out1;

		temp_out1 = rin;
		temp_out1.insert(rout.begin(), rout.end());

		RIN[gpb_id] = rin;

		ROUT[gpb_id] = temp_out1;
		#endif
	}
	else
	{
		#if BLOCKING
		RIN[gpb_id] = rin;
		ROUT[gpb_id] = rout;

		BRIN[gpb_id] = brin;
		BROUT[gpb_id] = brout;
		#else
		RIN[gpb_id] = rin;
		ROUT[gpb_id] = rout;
		#endif
	}
	#else
	#if BLOCKING
	RIN[gpb_id] = rin;
	ROUT[gpb_id] = rout;

	BRIN[gpb_id] = brin;
	BROUT[gpb_id] = brout;
	#else
	RIN[gpb_id] = rin;
	ROUT[gpb_id] = rout;
	#endif
	#endif

	#if 0 //PRINT_DATA
	#if BLOCKING
	#if 0
	fprintf(dump_file, "\nGPB %d for Function %s\n", gpb_id, cgraph_node_name(cnode));
	fprintf(dump_file, "\nBRIN");
	printSetOfGPUs(BRIN[gpb_id]);
	fflush(dump_file);
	fprintf(dump_file, "\nDelta: ");
	fflush(dump_file);
	printSetOfGPUs(delta);
	fflush(dump_file);
	fprintf(dump_file, "\nBROUT");
	printSetOfGPUs(BROUT[gpb_id]);
	fprintf(dump_file, "\nBRGEN");
	printSetOfGPUs(brgen);
	fprintf(dump_file, "\nQueued");
	printSetOfGPUs(Queued[caller_rep]);
	fprintf(dump_file, "\n\n");
	fflush(dump_file);
	#endif
	fprintf(dump_file, "\nStatistics\n");
	fprintf(dump_file, "\nDelta: ");
	fflush(dump_file);
	printSetOfGPUs(delta);
	fflush(dump_file);
	printSetOfGPUs(BROUT[gpb_id]);
	fprintf(dump_file, "\nBRGEN");
	printSetOfGPUs(brgen);
	fprintf(dump_file, "\nQueued");
	printSetOfGPUs(Queued[caller_rep]);
	fprintf(dump_file, "\n\n");
	fflush(dump_file);
	fprintf(dump_file, "\nROUT");
	printSetOfGPUs(ROUT[gpb_id]);
	fflush(dump_file);
	fprintf(dump_file, "\nBROUT");
	printSetOfGPUs(BROUT[gpb_id]);
	fflush(dump_file);
	#else
	#if 0
	fprintf(dump_file, "\nGPB %d for Function %s\n", gpb_id, cgraph_node_name(cnode));
	fprintf(dump_file, "\nRIN");
	printSetOfGPUs(RIN[gpb_id]);
	fflush(dump_file);
	fprintf(dump_file, "\nDelta: ");
	fflush(dump_file);
	printSetOfGPUs(delta);
	fflush(dump_file);
	fprintf(dump_file, "\nROUT");
	printSetOfGPUs(ROUT[gpb_id]);
	fprintf(dump_file, "\nRGEN");
	printSetOfGPUs(rgen);
	fprintf(dump_file, "\n\n");
	fflush(dump_file);
	#endif
	fprintf(dump_file, "\nDelta: ");
	fflush(dump_file);
	printSetOfGPUs(delta);
	fflush(dump_file);
	fprintf(dump_file, "\nRGEN");
	printSetOfGPUs(rgen);
	fprintf(dump_file, "\n\n");
	fflush(dump_file);
	#endif
	#endif

	#if 0 //PRINT_DATA
	GPUSet diff_rout1, diff_rout2, diff_rin, diff_brin;
	#if BLOCKING
	set_difference(rout.begin(), rout.end(), prev_rout.begin(), prev_rout.end(), inserter(diff_rout1, diff_rout1.end()));
	set_difference(prev_rout.begin(), prev_rout.end(), rout.begin(), rout.end(), inserter(diff_rout2, diff_rout2.end()));

	set_difference(rin.begin(), rin.end(), prev_rin.begin(), prev_rin.end(), inserter(diff_rin, diff_rin.end()));
	set_difference(brin.begin(), brin.end(), prev_brin.begin(), prev_brin.end(), inserter(diff_brin, diff_brin.end()));
	#else
	set_difference(brout.begin(), brout.end(), prev_brout.begin(), prev_brout.end(), inserter(diff_rout1, diff_rout1.end()));
	set_difference(prev_brout.begin(), prev_brout.end(), brout.begin(), brout.end(), inserter(diff_rout2, diff_rout2.end()));

	set_difference(rin.begin(), rin.end(), prev_rin.begin(), prev_rin.end(), inserter(diff_rin, diff_rin.end()));
	#endif

	fprintf(dump_file, "\nDiff1 for GPB %d CNODE %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(diff_rout1);
	fflush(dump_file);
	fprintf(dump_file, "\nDiff2 for GPB %d CNODE %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(diff_rout2);
	fflush(dump_file);
	fprintf(dump_file, "\nDiff for RIN GPB %d CNODE %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(diff_rin);
	fflush(dump_file);
	fprintf(dump_file, "\nDiff for BRIN GPB %d CNODE %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(diff_brin);
	fflush(dump_file);
	fprintf(dump_file, "\nSizes for GPB %d: Prev RIN %d RIN %d Prev ROUT %d ROUT %d RGen %d\n", gpb_id, prev_rin.size(), rin.size(), prev_rout.size(), rout.size(), rgen.size());
	fflush(dump_file);
	#endif

	
	//if(!(prev_rout == rout))
	#if BLOCKING
	if(!(prev_rout == rout) || !(prev_brout == brout))
	#else
	if(!(prev_rout == rout))
	#endif
        {
		#if 0 // PRINT_DATA
		fprintf(dump_file, "\nRecording with change BROUT GPB %d of Function %s ", gpb_id, cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUIDs(brout);
		fprintf(dump_file, "\n\n");
		fflush(dump_file);
		fprintf(dump_file, "\nRecording with change ROUT GPB %d of Function %s ", gpb_id, cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUIDs(rout);
		fprintf(dump_file, "\n\n");
		fflush(dump_file);
		#endif

		get_succ_gpbs(gpb_id, cnode);

		#if PROFILING
		RETURN(true);
		#else		
		return(true);		
		#endif
	}
	else
	{
		#if PROFILING
		RETURN(false);		
		#else		
		return(false);		
		#endif
	}	
	#if 0
	else
	{
		fprintf(dump_file, "\nRecording without change BROUT GPB %d of Function %s ", gpb_id, cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUIDs(brout);
		fprintf(dump_file, "\n\n");
		fflush(dump_file);
		fprintf(dump_file, "\nRecording without change ROUT GPB %d of Function %s ", gpb_id, cgraph_node_name(cnode));
		fflush(dump_file);
		printSetOfGPUIDs(rout);
		fprintf(dump_file, "\n\n");
		fflush(dump_file);

		RETURN(false);
	}
	#endif

	
//	RETURN_VOID();
}
#endif

void GPG::analyzeGPGWithBI(struct cgraph_node *cnode, bool again, GPUSet bi)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	if(isTop())
	{
		#if PROFILING
		RETURN_VOID();
		#else
		return;
		#endif
	}

	RIN.clear();
	ROUT.clear();

	#if BLOCKING
	BRIN.clear();
	BROUT.clear();
	#endif

	unsigned int current_node_id;
	GPB current_node;

	GPBSet gpbs = getGPBs();
	unsigned int size = gpbs.size();

	int * worklist = GPB_worklist[caller_rep];
	int i;
	bool change;
	std::map< unsigned int, unsigned int > rev_dfs_gpb = REV_DFS_GPB[caller_rep];

	for(i = 1; i <= size; i++)
	{
		current_node_id = rev_dfs_gpb[i]; 

		visited_count[caller_rep][current_node_id] = 0;
	}

	for(i = 1; i <= size; i++)
	{
		change  =  false;

		if(worklist[i])
		{
			current_node_id = rev_dfs_gpb[i]; 

			worklist[i] = false;

			change = analyzeGPBWithBI(current_node_id, cnode, bi);
		}

		if(change)
		{
			i = 0;
		}
	}

	free(GPB_worklist[caller_rep]);

	GPUSet brout, rout, temp_arr, res_arr, new_arr, t_p;
	unsigned int exit;

	exit = getExitGPB();

	#if BLOCKING
	brout = BROUT[exit];
	#else
	rout = ROUT[exit];
	#endif

	std::map< unsigned int, GPUSet > array_data = FINP[caller_rep];

	for(std::map< unsigned int, GPUSet >::iterator fit = array_data.begin(); fit != array_data.end(); fit++)
	{
		temp_arr = fit->second;

		#if 0
		for(GPUSet::iterator git = temp_arr.begin(); git != temp_arr.end(); git++)
		{
			res_arr.insert(stripUpwardsExposed(*git));
		}
		#endif

		res_arr.insert(temp_arr.begin(), temp_arr.end());
	}

	GPUSet resolved_arr = res_arr;
//	GPUSet resolved_arr = FIComposition(res_arr, cnode);
	
	std::tuple< GPUSet, GPUSet > new_arr_res;

	#if BLOCKING
	new_arr = RGen(brout, resolved_arr, cnode, 0);
	#else
	new_arr = RGen(rout, resolved_arr, cnode, 0);
	#endif

	unsigned int var;
	GPUSet t_np;

	array_data.clear();
	stmt_info_type key;

	for(GPUSet::iterator nit = new_arr.begin(); nit != new_arr.end(); nit++)
	{
		var = get<0>(get<0>(*nit));

		if(!isPointstoEdge(*nit))
		{
			t_np = array_data[var];

			t_np.insert(*nit);

			array_data[var] = t_np;
		}
		else
		{
			t_p = FIP[caller_rep][var];

			t_p.insert(*nit);

			FIP[caller_rep][var] = t_p;
		}
	}

	FINP[caller_rep] = array_data;

	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

bool GPG::analyzeGPBWithBI(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet bi)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPB gpb = gpb_map[gpb_id];

	unsigned int count = visited_count[caller_rep][gpb_id];

	visited_count[caller_rep][gpb_id] = ++count;

	std::tuple< GPUSet, GPUSet, GPUSet > result;
	
	std::pair< GPUSet, GPUSet > res;
	GPUSet gpus;

	GPUSet rin, brin, prev_rin, prev_brin, prev_rout, prev_brout;

	unsigned int start_node_id = getEntryGPB(); 

	if(start_node_id == gpb_id)
	{
		rin = bi;
	}
	else
	{
		rin = get_rin(gpb_id, cnode);
	}

	prev_rin = RIN[gpb_id];
	prev_brin = BRIN[gpb_id];

	if((prev_rin == rin) && visited_count[caller_rep][gpb_id] != 1)
	{
		#if PROFILING
		RETURN(false);
		#else
		return false;
		#endif
	}

	gpus = gpb.getGPUs();

	GPUSet gpus_new;

	for(GPUSet::iterator giit = gpus.begin(); giit != gpus.end(); giit++)
	{
		gpus_new.insert(stripUpwardsExposed(*giit));
	}

	GPUSet delta;
	delta = FIComp(gpus_new, cnode);
	
	GPUSet queued, rout, brout, brgen, ind_gpus, rgen, array_data_temp, array_data;
	std::tuple< GPUSet, GPUSet > temp_res1;

	rin.insert(prev_rin.begin(), prev_rin.end());

	definitions dfp_t;
	
	temp_res1 = ReachingGPUsAnalysis(rin, delta, cnode, gpb_id, dfp_t);
	rout = get<0>(temp_res1);
	rgen = get<1>(temp_res1);

	rgen = FIComp(rgen, cnode);
	
	gpb.setGPUs(rgen);

	gpb_map[gpb_id] = gpb;

	prev_rout = ROUT[gpb_id];
	prev_brout = BROUT[gpb_id];

	rout.insert(prev_rout.begin(), prev_rout.end());

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nProcessing GPB %d with BI\n", gpb_id);
	#endif

	#if HEURISTICS
	GPUSet top;
	bool resolved = true;

	for(GPUSet::iterator gc = rgen.begin(); gc != rgen.end(); gc++)
	{
		if(!isPointstoInformation(*gc))
		{
			resolved = false;
			break;
		}
	}

	if(resolved)
	{
		gpb.setResolved();
		gpb_map[gpb_id] = gpb;
	}	

	if(gpb.isSymGPB())
	{
		GPUSet temp_out1, temp_out2;

		temp_out1 = rin;
		temp_out1.insert(rout.begin(), rout.end());

		ROUT[gpb_id] = temp_out1;
		RIN[gpb_id] = rin;

		#if BLOCKING
		temp_out2 = brin;
		temp_out2.insert(brout.begin(), brout.end());

		BROUT[gpb_id] = temp_out2;
		BRIN[gpb_id] = rin;
		#endif
	}
	else
	{
		ROUT[gpb_id] = rout;
		RIN[gpb_id] = rin;

		#if BLOCKING
		BROUT[gpb_id] = rout;
		BRIN[gpb_id] = rin;
		#endif
	}
	#else
	RIN[gpb_id] = rin;
	ROUT[gpb_id] = rout;

	#if BLOCKING
	BROUT[gpb_id] = rout;
	BRIN[gpb_id] = rin;
	#endif
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nDelta[%d]\n", gpb_id);
	printSetOfGPUs(delta);
	fprintf(dump_file, "\nRIN[%d]\n", gpb_id);
	printSetOfGPUs(RIN[gpb_id]);
	fprintf(dump_file, "\nRGen[%d]\n", gpb_id);
	printSetOfGPUs(rgen);
	fprintf(dump_file, "\nROUT[%d]\n", gpb_id);
	printSetOfGPUs(ROUT[gpb_id]);
	#endif

	if(!(prev_rout == rout))
        {
		get_succ_gpbs(gpb_id, cnode);
		
		#if PROFILING
		RETURN(true);
		#else		
		return(true);		
		#endif
	}
	else
	{
		#if PROFILING
		RETURN(false);		
		#else		
		return(false);		
		#endif
	}	
}

GPUSet GPG::get_ptsin(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPB gpb = gpb_map[gpb_id];

	GPBSet preds = getPrev(gpb_id);
	GPUSet res, temp_res;
	
	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		temp_res = PTSOUT[*it];

		res.insert(temp_res.begin(), temp_res.end());
	}

	return res;
}


GPUSet GPG::get_rin(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPB gpb = gpb_map[gpb_id];

	GPBSet preds = getPrev(gpb_id);
	GPUSet res, temp_res;
	
	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nPred %d\n", *it);
		fprintf(dump_file, "\nROUT of Pred %d\n", *it);
		printSetOfGPUs(ROUT[*it]);
		fprintf(dump_file, "\nBOUT of Pred %d\n", *it);
		printSetOfGPUs(BROUT[*it]);
		#endif

		temp_res = ROUT[*it];

		res.insert(temp_res.begin(), temp_res.end());
	}

	return res;
}

GPUSet GPG::get_brin(unsigned int gpb_id, struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPB gpb = gpb_map[gpb_id];

	GPBSet preds = getPrev(gpb_id);
	GPUSet res, temp_res;
	
	for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
	{
		temp_res = BROUT[*it];

		res.insert(temp_res.begin(), temp_res.end());
	}

	return res;
}

void GPG::convertIndirectCallToDirectCall(unsigned int call, unsigned int callee_rep, unsigned int caller_rep, basic_block bb)
{
	struct cgraph_node *cnode = func_numbering[caller_rep];
	GPB call_gpb = gpb_map[call];

	GPB gpb;
	GPBSet temp_gpbs;

	gpb.setId(GPB_count++);
	gpb.setCallBlock();
	gpb.setCallee(callee_rep);

	unsigned int  x = GPB_count - 1;
	unsigned int b = bb->index;

	replaceGPB(call, x, cnode); 

	GPBSet prev, next;
	prev = getPrev(call);
	next = getNext(call);

	if(prev.find(call) != prev.end())
	{
		prev.erase(call);
		prev.insert(x);
	}

	if(next.find(call) != next.end())
	{
		next.erase(call);
		next.insert(x);
	}

	setPrev(x, prev);
	setNext(x, next);

	#if 0
	temp_gpbs = ori_red_map[caller_rep][b];
	temp_gpbs.erase(call);
	temp_gpbs.insert(x);
	ori_red_map[caller_rep][b] = temp_gpbs;
	#endif

	#if 0
//	temp_gpbs = ((block_information *)(bb->aux))->sblocks;
	temp_gpbs = BB_START[caller_rep][b];
	temp_gpbs.erase(call);
	temp_gpbs.insert(x);
	BB_START[caller_rep][b] = temp_gpbs;
//	((block_information *)(bb->aux))->sblocks = temp_gpbs ;

//	temp_gpbs = ((block_information *)(bb->aux))->eblocks;
	temp_gpbs = BB_END[caller_rep][b];
	temp_gpbs.erase(call);
	temp_gpbs.insert(x);
	BB_END[caller_rep][b] = temp_gpbs;
//	((block_information *)(bb->aux))->eblocks = temp_gpbs;
	#endif

	GPBSet gpbs = getGPBs();
	gpbs.erase(call);
	gpbs.insert(x);
	setGPBs(gpbs);

	gpb_map[x] = gpb; 

	unsigned int start, end;
	start = getEntryGPB();
	end = getExitGPB();

	if(call == start)
	{
		setEntryGPB(x);
	}

	if(call == end)
	{
		setExitGPB(x);
	}
}

void GPG::processIndirectCall(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet rin, GPUSet brin)
{
//	fprintf(dump_file, "\nIn processIndirectCall, Call Block %d in Function %s\n", gpb_id, cgraph_node_name(cnode));

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPB call = gpb_map[gpb_id];

	unsigned int b = call.getBBIndex();

	basic_block bb = BASIC_BLOCK(b);

	definitions callees = call.getIndirectCallees();
	definitions unresolved_calls, temp;
	set< unsigned int > resolved_calls, identity_calls;
	Node callee_node;
	IndirectionList list;
	unsigned int var;
	node_id_type nd_id;

	std::map< unsigned int, GPUSet > fip = FIP[cnode_num];
	std::map< unsigned int, GPUSet > finp = FINP[cnode_num];
	GPUSet tempset;

	for(std::map< unsigned int, GPUSet >::iterator it = fip.begin(); it != fip.end(); it++)
	{
		tempset = it->second;

		rin.insert(tempset.begin(), tempset.end());
	}

	for(std::map< unsigned int, GPUSet >::iterator it = finp.begin(); it != finp.end(); it++)
	{
		tempset = it->second;

		rin.insert(tempset.begin(), tempset.end());
	}

	#if 0
	fprintf(dump_file, "\nNumber of Indirect Callees %d\n", callees.size());
	printDefinitions(callees);
	#endif

	for(definitions::iterator it = callees.begin(); it != callees.end(); it++)
	{
		callee_node = getNode(*it);

		#if 0 
		callee_node.printNode();
		printSetOfGPUs(brin);
		#endif

		var = callee_node.getVarIndex();

		list = callee_node.getList();
	
		visitedNodes.clear();
		GPUSet used;

		temp = NodeReduction(false, *it, rin, used, cnode); // Source = 1, Target = 0

		#if 0 
		fprintf(dump_file, "\ntemp size = %d\n", temp.size());
		printDefinitions(temp);
		#endif

		for(definitions::iterator dit = temp.begin(); dit != temp.end(); dit++)
		{
			callee_node = getNode(*dit);

//			callee_node.printNode();

			list = callee_node.getList();
			
			var = callee_node.getVarIndex();

			if(list.Length() == 0)
			{
				csvarinfo_t vi = cs_get_varinfo (get<0>(*dit));
				tree decl;

				if(vi)
				{
					decl = vi->decl;

					if (TREE_CODE (decl) == FUNCTION_DECL) 
					{
						struct cgraph_node *callee = cgraph_get_node(decl);

						resolved_calls.insert(((function_info *)(callee->aux))->func_num);
					}
					else
					{
						continue;
					}	
				}
			}
		}
	}	

	GPG g = *this;
	
	GPG gpg_callee, temp_gpg, fin;
	unsigned int entry, z;
	GPBSet gpbs_to_be_analyzed, atemp;

	unsigned int resolution = 0;

	#if 1
	if(resolved_calls.size() == 0) // Unresolved calls are resolved by type matching
	{
		Prototype fp = call.proto;
		struct cgraph_node *callee_type;

//		fprintf(dump_file, "\nFunction Type Matching Used for caller %s\n", cgraph_node_name(cnode));
			
		unsigned int fn_count = 0;

		for (map <int, Prototype>:: iterator fnit = fn_details.begin(); fnit != fn_details.end(); ++fnit)
        	{
			Prototype fn = fnit->second;

			if (fp.compare (fn))
			{
				#if 1
				struct cgraph_node *callee = func_numbering[fnit->first];

//				fprintf(dump_file, "\nFunction Type Matching %s\n", cgraph_node_name(callee));
			
				fn_count++;

				update_call_graph(cnode, callee, bb);

				if(analyze_callee_now(callee))
				{
					perform_analysis(callee);
				}

				gpg_callee = optimized_GPG_map[fnit->first];

				if(gpg_callee.isIdentityGPG(callee, false))
				{
//					fprintf(dump_file, "\nGPG is idenitity\n");
			
					identity_calls.insert(fnit->first);
				}
				else
				{
					resolved_calls.insert(fnit->first);
				}
				#endif

//				resolved_calls.insert(fnit->first);
			}
        	}

		#if 0 
		if(resolved_calls.size() != fn_count)
		{
			fprintf(dump_file, "\nNot all GPGs are idenitity\n");
			
			resolved_calls.clear();
		}
		#endif
	}
	#endif

	#if DATA_MEAS
	fprintf(dump_file, "\nFunction Pointer Call in Function %d %s GPB %d has %d number of callees\n", cnode->uid, cgraph_node_name(cnode), gpb_id, (resolved_calls.size()+identity_calls.size()));
	#endif	

	if(resolved_calls.empty())
	{
		if(gpb_id == getEntryGPB())
		{
			gpbs_to_be_analyzed.insert(gpb_id);

			eraseDirectCallGPB(gpb_id, cnode_num);
		}
		else
		{
			eliminateEmptyGPB(gpb_id, cnode);
		}
	}
	
	for(set< unsigned int >::iterator cit = resolved_calls.begin(); cit != resolved_calls.end(); cit++)
	{
		resolution = 1;

		struct cgraph_node *callee = func_numbering[*cit];

		update_call_graph(cnode, callee, bb);

		gpg_callee = optimized_GPG_map[*cit];

		entry = gpg_callee.getEntryGPB();	
		z = GPB_count - 1;

		if(gpg_callee.isTop())
		{
			eliminateGPB(gpb_id, cnode);

			if(gpb_id == getEntryGPB())
			{
				setTop();
			}
		}
		else
		{
			if(gpg_callee.isIdentityGPG(callee, false))
			{
				#if 0
				fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee));
				fflush(dump_file);
				#endif

				if(gpb_id == getEntryGPB())
				{
					gpbs_to_be_analyzed.insert(gpb_id);

					eraseDirectCallGPB(gpb_id, cnode_num);
				}
				else
				{
					eliminateEmptyGPB(gpb_id, cnode);
				}
			}
			else
			{
				GPUSet maygen, mustkill;
				definitions lup, rup;

				lup = lhsUpwardsExposedDefinitions[*cit];
				rup = rhsUpwardsExposedDefinitions[*cit];
				maygen = DownwardsExposedMayDefinitions[*cit];
				mustkill = DownwardsExposedMustDefinitions[*cit];

				GPBSet dcalls, icalls, intervals_t;
				dcalls = gpg_callee.getCallBlocks(callee);
				icalls = gpg_callee.getIndirectCallBlocks(callee);
				intervals_t = gpg_callee.getIntervalBlocks(callee);

				if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
				{
//					fprintf(dump_file, "\nNo Upwards Exposed\n");

					if(gpb_id == getEntryGPB())
					{
						gpbs_to_be_analyzed.insert(gpb_id);

						eraseDirectCallGPB(gpb_id, cnode_num);
					}
					else
					{
						eliminateEmptyGPB(gpb_id, cnode);
					}
				}
				else
				{
					#if 0 //PRINT_DATA
					fprintf(dump_file, "\nInline GPG of callee for non-Identity and non-Top %s\n", cgraph_node_name(callee));
					fflush(dump_file);
					#endif

					atemp = inlineIndirectCall(gpb_id, *cit, cnode_num, bb, gpg_callee);

					#if 0 //PRINT_DATA
					printGPG(cnode);
					#endif

					gpbs_to_be_analyzed.insert(atemp.begin(), atemp.end());
				}
			}	

//			gpbs_to_be_analyzed.insert(entry+z);
		}
		
		#if 0
		fin = fin.meet(cnode, *this);
		fprintf(dump_file, "\nMeet %s\n", cgraph_node_name(callee));
		printGPG(cnode);
		fflush(dump_file);
		#endif
	}

	/*
	localOptimizations(cnode, true);

	GPBSet new_gpb_set = getGPBs();

	GPBSet gpbs_temp1;

	set_intersection(new_gpb_set.begin(), new_gpb_set.end(), gpbs_to_be_analyzed.begin(), gpbs_to_be_analyzed.end(), inserter(gpbs_temp1, gpbs_temp1.end())); 
	*/	

	#if 0 // Setting the Top value for unresolved calls
	GPUSet top;	

	if(resolution == 0 && gpbs_to_be_analyzed.size() == 0)
	{
		fprintf(dump_file, "\nTOP Vale as OUT\n");
		BROUT[gpb_id] = top;
		ROUT[gpb_id] = top;

		return;
	}
	#endif

	for(GPBSet::iterator ait = gpbs_to_be_analyzed.begin(); ait != gpbs_to_be_analyzed.end(); ait++)
	{
		analyzeGPB(*ait, cnode);
	}
}

#if 0
void GPG::processIndirectCall(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet rin, GPUSet brin)
{
//	fprintf(dump_file, "\nIn processIndirectCall, Call Block %d in Function %s\n", gpb_id, cgraph_node_name(cnode));

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPB call = gpb_map[gpb_id];

	unsigned int b = call.getBBIndex();

	basic_block bb = BASIC_BLOCK(b);

	definitions callees = call.getIndirectCallees();
	definitions unresolved_calls, temp;
	set< unsigned int > resolved_calls;
	Node callee_node;
	IndirectionList list;
	unsigned int var;
	node_id_type nd_id;

	#if 0
	fprintf(dump_file, "\nNumber of Indirect Callees %d\n", callees.size());
	printDefinitions(callees);
	#endif

	for(definitions::iterator it = callees.begin(); it != callees.end(); it++)
	{
		callee_node = getNode(*it);

		#if 0
		callee_node.printNode();
		printSetOfGPUs(brin);
		#endif

		var = callee_node.getVarIndex();

		list = callee_node.getList();
	
		visitedNodes.clear();
		GPUSet used;
		
		temp = NodeReduction(false, *it, rin, used, cnode); // Source = 1, Target = 0

		#if 0
		fprintf(dump_file, "\ntemp size = %d\n", temp.size());
		printDefinitions(temp);
		#endif

		for(definitions::iterator dit = temp.begin(); dit != temp.end(); dit++)
		{
			callee_node = getNode(*dit);

//			callee_node.printNode();

			list = callee_node.getList();
			
			var = callee_node.getVarIndex();

			if(list.Length() == 0)
			{
				csvarinfo_t vi = cs_get_varinfo (get<0>(*dit));
				tree decl;

				if(vi)
				{
					decl = vi->decl;

					if (TREE_CODE (decl) == FUNCTION_DECL) 
					{
						struct cgraph_node *callee = cgraph_get_node(decl);

						resolved_calls.insert(((function_info *)(callee->aux))->func_num);
					}
					else
					{
						continue;
					}	
				}
			}
		}
	}	

	GPG g = *this;
	
	GPG gpg_callee, temp_gpg, fin;
	unsigned int entry, z;
	GPBSet gpbs_to_be_analyzed, atemp;

	for(set< unsigned int >::iterator cit = resolved_calls.begin(); cit != resolved_calls.end(); cit++)
	{
		struct cgraph_node *callee = func_numbering[*cit];

		#if 0
		fprintf(dump_file, "\nICallee %s\n", cgraph_node_name(callee));
		fflush(dump_file);
		#endif

		update_call_graph(cnode, callee, bb);

		if(analyze_callee_now(callee))
		{
			perform_analysis(callee);
		}

		gpg_callee = optimized_GPG_map[*cit];

		#if 0
		fprintf(dump_file, "\nOptimized GPG of Callee %s for indirect call\n", cgraph_node_name(callee));
		gpg_callee.printGPG(callee);
		#endif

		entry = gpg_callee.getEntryGPB();	
		z = GPB_count - 1;

		if(gpg_callee.isTop())
		{
			eliminateGPB(gpb_id, cnode);

			if(gpb_id == getEntryGPB())
			{
				setTop();
			}
		}
		else
		{
			if(gpg_callee.isIdentityGPG(callee, false))
			{
				#if 0
				fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee));
				fflush(dump_file);
				#endif

				if(gpb_id == getEntryGPB())
				{
					gpbs_to_be_analyzed.insert(gpb_id);

					eraseDirectCallGPB(gpb_id, cnode_num);
				}
				else
				{
					eliminateEmptyGPB(gpb_id, cnode);
				}
			}
			else
			{
				GPUSet maygen, mustkill;
				definitions lup, rup;

				lup = lhsUpwardsExposedDefinitions[*cit];
				rup = rhsUpwardsExposedDefinitions[*cit];
				maygen = DownwardsExposedMayDefinitions[*cit];
				mustkill = DownwardsExposedMustDefinitions[*cit];

				GPBSet dcalls, icalls, intervals_t;
				dcalls = gpg_callee.getCallBlocks(callee);
				icalls = gpg_callee.getIndirectCallBlocks(callee);
				intervals_t = gpg_callee.getIntervalBlocks(callee);

				if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
				{
//					fprintf(dump_file, "\nNo Upwards Exposed\n");

					if(gpb_id == getEntryGPB())
					{
						gpbs_to_be_analyzed.insert(gpb_id);

						eraseDirectCallGPB(gpb_id, cnode_num);
					}
					else
					{
						eliminateEmptyGPB(gpb_id, cnode);
					}
				}
				else
				{
//					fprintf(dump_file, "\nInline GPG of callee for non-Identity and non-Top %s\n", cgraph_node_name(callee));

					atemp = inlineIndirectCall(gpb_id, *cit, cnode_num, bb, gpg_callee);

					gpbs_to_be_analyzed.insert(atemp.begin(), atemp.end());
				}
			}	

//			gpbs_to_be_analyzed.insert(entry+z);
		}
		
		fin = fin.meet(g);
	}

	if(!gpg_callee.isTop())
	{
		GPBList list_temp = Function_Worklist[cnode_num];

		for(set< unsigned int >::iterator ait = gpbs_to_be_analyzed.begin(); ait != gpbs_to_be_analyzed.end(); ait++)
		{
			list_temp.push_front(*ait);
		} 

		Function_Worklist[cnode_num] = list_temp;
	}

	#if 0
	fprintf(dump_file, "\nFinal fin\n");
	fflush(dump_file);
	fin.printGPG(cnode);
	fflush(dump_file);
	#endif

	*this = fin;
	
//	fin.localOptimizations(cnode);
//	localOptimizations(cnode);
}
#endif

void GPG::processIndirectCallAlt(unsigned int gpb_id, struct cgraph_node *cnode, GPUSet rin, GPUSet brin)
{
//	fprintf(dump_file, "\nIn processIndirectCall, Call Block %d in Function %s\n", gpb_id, cgraph_node_name(cnode));

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPB call = gpb_map[gpb_id];

	unsigned int b = call.getBBIndex();

//	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	basic_block bb = BASIC_BLOCK(b);

	definitions callees = call.getIndirectCallees();
	definitions unresolved_calls, temp;
	set< unsigned int > resolved_calls;
	Node callee_node;
	IndirectionList list;
	unsigned int var;
	node_id_type nd_id;

	#if 0
	fprintf(dump_file, "\nNumber of Indirect Callees %d\n", callees.size());
	printDefinitions(callees);
	#endif

	for(definitions::iterator it = callees.begin(); it != callees.end(); it++)
	{
		callee_node = getNode(*it);

		#if 0
		callee_node.printNode();
		printSetOfGPUs(brin);
		#endif

		var = callee_node.getVarIndex();

		list = callee_node.getList();
	
		#if 0		
		if(CDV.find(var) != CDV.end())
		{
			--var;
			Node nn(var, list);
			nd_id = nn.getNodeID();
		}
		else
		{
			nd_id = *it;
		}
		#endif

		visitedNodes.clear();
		GPUSet used;
		
		temp = NodeReduction(false, *it, brin, used, cnode); // Source = 1, Target = 0

		#if 0
		fprintf(dump_file, "\ntemp size = %d\n", temp.size());
		printDefinitions(temp);
		#endif

		for(definitions::iterator dit = temp.begin(); dit != temp.end(); dit++)
		{
			callee_node = getNode(*dit);

//			callee_node.printNode();

			list = callee_node.getList();
			
			var = callee_node.getVarIndex();

			if(list.Length() == 0)
			{
				csvarinfo_t vi = cs_get_varinfo (get<0>(*dit));
				tree decl;

				if(vi)
				{
					decl = vi->decl;

					if (TREE_CODE (decl) == FUNCTION_DECL) 
					{
						struct cgraph_node *callee = cgraph_get_node(decl);

						resolved_calls.insert(((function_info *)(callee->aux))->func_num);
					}
					else
					{
						unresolved_calls.insert(*dit);
					}	
				}
				else
				{
					unresolved_calls.insert(*dit);
				}	
			}
			else
			{
				unresolved_calls.insert(*dit);
			}	
		}
	}	

	#if 0
	fprintf(dump_file, "\nunresolved_calls = %d, resolved_calls = %d\n", unresolved_calls.size(), resolved_calls.size());
	fprintf(dump_file, "\nUnresolved Calls\n");
	printDefinitions(unresolved_calls);
	fprintf(dump_file, "\nResolved Calls\n");
	#endif

	for(set< unsigned int >::iterator temp_it = resolved_calls.begin(); temp_it != resolved_calls.end(); temp_it++)
	{
		struct cgraph_node *temp_c = func_numbering[*temp_it];

//		fprintf(dump_file, "%s\t", cgraph_node_name(temp_c));
	}

//	fprintf(dump_file, "\n\n");

	GPG g = *this;

	if(unresolved_calls == callees && resolved_calls.empty()) // Nothing Resolved 
	{
//		fprintf(dump_file, "\nNo Callees Resolved\n");
//		g.printGPG(cnode);

		return;
	}	

	set< unsigned int > gpbs_to_be_analyzed;
	
	if(unresolved_calls.empty()) // Completely resolved
	{
		// Don't do anything
	}
	else // Partially resolved
	{
		GPB gpb;

		gpb.setId(GPB_count++);

		unsigned int x = GPB_count - 1;
//		fprintf(dump_file, "\nx = %d, gpb_id = %d\n", x, gpb_id);

		definitions r_temp;
		r_temp = rhsUpwardsExposedDefinitions[caller_rep];
		r_temp.insert(unresolved_calls.begin(), unresolved_calls.end());	
		rhsUpwardsExposedDefinitions[caller_rep] = r_temp;

		#if FP
		definitions callees_updated;
		r_temp = incompleteCallees[caller_rep];
		set_difference(r_temp.begin(), r_temp.end(), callees.begin(), callees.end(), inserter(callees_updated, callees_updated.end()));
		callees_updated.insert(unresolved_calls.begin(), unresolved_calls.end());	
		incompleteCallees[caller_rep] = callees_updated;
		#endif

		gpb.setBBIndex(b);
		gpb.setIndirectCallBlock();
		gpb.setIndirectCallees(unresolved_calls);		
		g.setPrev(x, getPrev(gpb_id));
		g.setNext(x, getNext(gpb_id));
		g.remPrev(x, gpb_id);
		g.remNext(x, gpb_id);
		g.replaceGPB(gpb_id, x, cnode);

		gpb_map[x] = gpb;

		GPBSet temp_gpbs;

		#if 0
		temp_gpbs = ori_red_map[caller_rep][b];
		temp_gpbs.erase(gpb_id);
		temp_gpbs.insert(x);
		ori_red_map[caller_rep][b] = temp_gpbs;
		#endif

		#if 0
//		temp_gpbs = ((block_information *)(bb->aux))->sblocks;
		temp_gpbs = BB_START[caller_rep][b];
		temp_gpbs.erase(gpb_id);
		temp_gpbs.insert(x);
		BB_START[caller_rep][b] = temp_gpbs;
//		((block_information *)(bb->aux))->sblocks = temp_gpbs ;

//		temp_gpbs = ((block_information *)(bb->aux))->eblocks;
		temp_gpbs = BB_END[caller_rep][b];
		temp_gpbs.erase(gpb_id);
		temp_gpbs.insert(x);
		BB_END[caller_rep][b] = temp_gpbs;
//		((block_information *)(bb->aux))->eblocks = temp_gpbs;
		#endif

		GPBSet gpbs = g.getGPBs();

		gpbs.erase(gpb_id);
		gpbs.insert(x);

		if(gpb_id == g.getEntryGPB())
		{
			g.setEntryGPB(x);
		}

		if(gpb_id == g.getExitGPB())
		{
			g.setExitGPB(x);
		}

		g.setGPBs(gpbs);

//		g = g_initial;
		//g = g.meet(g_initial);
//		fprintf(dump_file, "\nHola\n");
//		g.printGPG(cnode);

		gpbs_to_be_analyzed.insert(x);
	}
	
	GPG fin;

	if(!unresolved_calls.empty()) 
	{
		fin = g;
	}

	GPG gpg_callee, temp_gpg;
	unsigned int entry, z;

	for(set< unsigned int >::iterator cit = resolved_calls.begin(); cit != resolved_calls.end(); cit++)
	{
		struct cgraph_node *callee = func_numbering[*cit];

//		fprintf(dump_file, "\nICallee %s\n", cgraph_node_name(callee));
//		fflush(dump_file);

		update_call_graph(cnode, callee, bb);

		if(analyze_callee_now(callee))
		{
			perform_analysis(callee);
		}

		gpg_callee = optimized_GPG_map[*cit];

//		fprintf(dump_file, "\nOptimized GPG of Callee %s for indirect call\n", cgraph_node_name(callee));
//		gpg_callee.printGPG(callee);

		entry = gpg_callee.getEntryGPB();	
		z = GPB_count - 1;

		definitions itmp = incompleteCallees[*cit];

		if(itmp.empty())
		{
//			fprintf(dump_file, "\nGPG of callee is free of indirect calls\n");
//			fflush(dump_file);

			#if 0
			GPUSet def_gpus;
			definitions lup, rup;

			lup = lhsUpwardsExposedDefinitions[caller_rep];
			rup = rhsUpwardsExposedDefinitions[caller_rep];
			def_gpus = DownwardsExposedDefinitions[caller_rep];

			if(lup.empty() && rup.empty() && def_gpus.empty())
			{
				eraseIndirectCallGPB(gpb_id, caller_rep, bb);
				continue;
			}
			else if(lup.empty())
			{
				replaceIndirectCallGPB(gpb_id, caller_rep, bb);
				continue;
			}
			#endif

			g.inlineIndirectCall(gpb_id, *cit, caller_rep, bb, gpg_callee);
		}
		else
		{
			g.convertIndirectCallToDirectCall(gpb_id, *cit, caller_rep, bb);
		}
	
//		fprintf(dump_file, "\nDone with Inlining for Callee %s\n", cgraph_node_name(callee));
//		fflush(dump_file);

		#if 0
		fprintf(dump_file, "\nGPG of the callee %s\n", cgraph_node_name(callee));
		fflush(dump_file);
		gpg_callee.printGPG(callee);
		fflush(dump_file);
		fprintf(dump_file, "\nAfter Inlining Indirect Call with Callee's GPG %s\n", cgraph_node_name(callee));
		fflush(dump_file);
		temp_gpg.printGPG(cnode);
		fflush(dump_file);
		#endif

		fin = fin.meet(g);

		#if 0
		fprintf(dump_file, "\nfin\n");
		fflush(dump_file);
		fin.printGPG(cnode);
		fflush(dump_file);
		#endif

		gpbs_to_be_analyzed.insert(entry+z);
	}

	GPBList list_temp = Function_Worklist[caller_rep];

	for(set< unsigned int >::iterator ait = gpbs_to_be_analyzed.begin(); ait != gpbs_to_be_analyzed.end(); ait++)
	{
		list_temp.push_front(*ait);
	} 

	Function_Worklist[caller_rep] = list_temp;

	#if 0
	fprintf(dump_file, "\nFinal fin\n");
	fflush(dump_file);
	fin.printGPG(cnode);
	fflush(dump_file);
	#endif

	*this = fin;
	
//	fin.localOptimizations(cnode);
//	localOptimizations(cnode);
}

bool GPG::processingRecursion(struct cgraph_node *cnode)
{
//	fprintf(dump_file, "\nInside processingRecursion\n");

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	GPUSet s_gpus, ns_gpus;
	GPBSet calls, self_calls;
	GPB gpb;

	ns_gpus = returnNonScalarGPUs(cnode, false);
	s_gpus = returnScalarGPUs(cnode, false);

	self_calls = returnCallBlocksPresentForRecursion(cnode);
	calls = getCallBlocksForGPG(cnode);

	#if 0	
	if(!(self_calls == calls))
	{
		fprintf(dump_file, "\nChecking Alert\n");
		printGPG(cnode);

		exit(1);
	}
	#endif

	if(ns_gpus.empty()) // Only Scalar GPUs
	{
		GPBSet gpbs = getGPBs();

		for(GPBSet::iterator cit = self_calls.begin(); cit != self_calls.end(); cit++)
		{
			gpb = gpb_map[*cit];

			removeGPB(*cit, cnode);

			gpbs.erase(*cit);
		}

		setGPBs(gpbs);
	
		#if 0
		fprintf(dump_file, "\nGPG after elimination of call blocks\n");
		printGPG(cnode);
		#endif

		localOptimizations(cnode, false);

		return(true);
	}
	else //if(areAdvancingGPUs(ns_gpus))
	{
		kLimitGPUsInGPG(cnode, false);

		GPBSet gpbs = getGPBs();

		for(GPBSet::iterator cit = self_calls.begin(); cit != self_calls.end(); cit++)
		{
			gpb = gpb_map[*cit];

			removeGPB(*cit, cnode);

			gpbs.erase(*cit);
		}

		setGPBs(gpbs);
	
		#if 0
		fprintf(dump_file, "\nGPG after elimination of call blocks\n");
		printGPG(cnode);
		#endif

		localOptimizations(cnode, false);

		return(true);
	}

	unsigned int callee_rep;
	struct cgraph_node *callee;
	unsigned int b, z, exit, entry;
	GPG gpg_callee;	
	basic_block bb;

	GPUSet prev_rout, prev_brout, rout, brout;

	GPG g_caller;
	bool recur = false;

	#if INTDIR
	GPBSet int_set = getIntervalDirectBlocks(cnode);

	for(GPBSet::iterator it = int_set.begin(); it != int_set.end(); it++)
	{
		resolveIntervalDirect(*it, cnode);

		inlineInterval(*it, cnode);
	}
	#endif
//	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	do
	{
//		fprintf(dump_file, "\nFixed Point Iteration\n");
		
		calls = getCallBlocksForGPG(cnode);

		set< unsigned int > to_be_analyzed, atemp;

		for(GPBSet::iterator cit = calls.begin(); cit != calls.end(); cit++)
		{
			gpb = gpb_map[*cit];

			b = gpb.getBBIndex();
			bb = BASIC_BLOCK(b);

			callee_rep = gpb.getCallee();

			if(!needsInliningRecursion(caller_rep, callee_rep))
			{
				continue;
			}

			callee = func_numbering[callee_rep];

//			fprintf(dump_file, "\nRecursive Call: Callee %s\n", cgraph_node_name(callee));

			if(((function_info *)(cnode->aux))->count == 1)
			{
				deltaGPG_map[caller_rep] = optimized_GPG_map[caller_rep];
			}

			recur = true;

			gpg_callee = deltaGPG_map[callee_rep];

			z = GPB_count + 1;
			entry = gpg_callee.getEntryGPB();	

//			fprintf(dump_file, "\nGPG of the callee\n");
//			gpg_callee.printGPG(callee);

			#if 0 //FP
			definitions itmp = incompleteCallees[callee_rep];

			if(itmp.empty())
			#endif
			{
				if(gpg_callee.isTop())
				{
					eliminateGPB(*cit, cnode);

					if(*cit == getEntryGPB())
					{
						setTop();
					}
				}
				else
				{
					if(gpg_callee.isIdentityGPG(callee, false))
					{
//						fprintf(dump_file, "\nIdentity GPG Callee %s\n", cgraph_node_name(callee));
//						fflush(dump_file);

						if(*cit == getEntryGPB())
						{
							to_be_analyzed.insert(*cit);

							eraseDirectCallGPB(*cit, caller_rep);
						}
						else
						{
							eliminateEmptyGPB(*cit, cnode);
						}
					}
					else
					{
						GPUSet maygen, mustkill;
						definitions lup, rup;

						lup = lhsUpwardsExposedDefinitions[callee_rep];
						rup = rhsUpwardsExposedDefinitions[callee_rep];
						maygen = DownwardsExposedMayDefinitions[callee_rep];
						mustkill = DownwardsExposedMustDefinitions[callee_rep];

						GPBSet dcalls, icalls, intervals_t;
						dcalls = gpg_callee.getCallBlocks(callee);
						icalls = gpg_callee.getIndirectCallBlocks(callee);
						intervals_t = gpg_callee.getIntervalBlocks(callee);

//						fprintf(dump_file, "\nHey Der\n");

						if(lup.empty() && rup.empty() && dcalls.empty() && icalls.empty() && intervals_t.empty() && maygen.empty() && mustkill.empty())
						{
//							fprintf(dump_file, "\nHey Der123\n");

							if(*cit == getEntryGPB())
							{
								to_be_analyzed.insert(*cit);

								eraseDirectCallGPB(*cit, caller_rep);
							}
							else
							{
								eliminateEmptyGPB(*cit, cnode);
							}
						}
						else
						{
//							fprintf(dump_file, "\nActually Inlining\n");

							atemp = inlineCall(*cit, callee_rep, caller_rep, bb, gpg_callee);

							to_be_analyzed.insert(atemp.begin(), atemp.end());
						}
					}
				}
			}

//			fprintf(dump_file, "\nAfter Inlining of a call\n");
//			printGPG(cnode);

			localOptimizations(cnode, true);
		}	

		#if 0
		fprintf(dump_file, "\nEnd of Pass\n");
		fprintf(dump_file, "\nAfter Inlining of a call\n");
		printGPG(cnode);

		//localOptimizationsOnInitialGPG(cnode);
		//localOptimizations(cnode);
		fprintf(dump_file, "\nRecursive Local Optimizations\n");
		printGPG(cnode);
		#endif

		GPBList list_temp = Function_Worklist[caller_rep];

		for(set< unsigned int >::iterator ait = to_be_analyzed.begin(); ait != to_be_analyzed.end(); ait++)
		{
			list_temp.push_front(*ait);
		}	 

		Function_Worklist[caller_rep] = list_temp;

		analyzeGPG(cnode, true);

//		fprintf(dump_file, "\nRecursive Analyzing GPG\n");

		exit = getExitGPB();

		prev_rout = rout;
		prev_brout = brout;

		rout = ROUT[exit];
		brout = BROUT[exit];

		#if 0
		fprintf(dump_file, "\nPrev ROUT\n");
		printSetOfGPUs(prev_rout);
		fprintf(dump_file, "\nROUT\n");
		printSetOfGPUs(rout);

		fprintf(dump_file, "\nPrev BROUT\n");
		printSetOfGPUs(prev_brout);
		fprintf(dump_file, "\nBROUT\n");
		printSetOfGPUs(brout);
		#endif

	}while((!(prev_rout == rout)) || (!(prev_brout == brout)));

	#if 0
	fprintf(dump_file, "\nGPG after fixed point\n");
	printGPG(cnode);
	#endif

	calls = getCallBlocksForGPG(cnode);

	GPBSet gpbs = getGPBs();

	for(GPBSet::iterator cit = calls.begin(); cit != calls.end(); cit++)
	{
		gpb = gpb_map[*cit];

		removeGPB(*cit, cnode);

		gpbs.erase(*cit);
	}

	setGPBs(gpbs);

	#if 0
	fprintf(dump_file, "\nGPG after elimination of call blocks\n");
	printGPG(cnode);
	#endif

//	localOptimizationsOnInitialGPG(cnode);
	localOptimizations(cnode, false);

	return(recur);
}

void GPG::after_recursion(struct cgraph_node *cnode)
{
//	set_call_pts pts = ((function_info *)(cnode->aux))->call_pts;

	struct cgraph_node *caller;
	unsigned int caller_rep;
	basic_block bb;
	GPBSet temp;
	GPBList wrklist;
	GPG g_caller;

	#if 0
	fprintf(dump_file,"\nInside after_recursion for function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	unsigned int callee_rep = ((function_info *)(cnode->aux))->func_num;

	GPBSet caller_set = callers[callee_rep];

//	for(set_call_pts::iterator pit = pts.begin(); pit != pts.end(); pit++)
	for(GPBSet::iterator it = caller_set.begin(); it != caller_set.end(); it++)
	{
//		caller_rep = get<0>(*pit);

		caller_rep = *it;

		caller = func_numbering[caller_rep];

		#if 0
		fprintf(dump_file,"\nConsidering Caller %s\n", cgraph_node_name(caller));
		fflush(dump_file);
		#endif

		g_caller = optimized_GPG_map[caller_rep];

		if(g_caller.getCallBlocksForCallee(caller, callee_rep).empty())
		{
//			fprintf(dump_file,"\nCaller %s does not have call blocks for callee %s\n", cgraph_node_name(caller), cgraph_node_name(cnode));
//			fflush(dump_file);

			continue;
		}
		
		if(processed_functions.find(caller_rep) != processed_functions.end())
		{
//			fprintf(dump_file, "\nProcessing the Caller again %s after it's Callee GPG %s is modified\nGPg of Caller before processing", cgraph_node_name(caller), cgraph_node_name(cnode));
//			g_caller.printGPG(caller);


			g_caller.partial_analysis(caller, callee_rep);
		}
	}
}

//============================================================================================================================================

map< node_id_type, definitions > reuse_ssa; 
definitions visited_nodes, boundary_nodes;
map< unsigned int, GPBList > Function_Worklist; 

std::map< unsigned int, d_worklist_type > GPB_worklist;

unsigned int get_art_node(gimple stmt, basic_block bb, struct cgraph_node *cnode)
{
//	fprintf(dump_file,"\nget_art_node\n");

//	print_gimple_stmt (dump_file, stmt, 0, 0);
//	fprintf(dump_file,"\n\n");

	basic_block bt = stmt->gsbase.bb;
	tree lhs = gimple_call_lhs (stmt);

	csvarinfo_t vi = cs_lookup_vi_for_tree(lhs);

	it ai;
	for(ai= ((block_information *)(bt->aux))->get_list().begin();ai !=((block_information *)(bt->aux))->get_list().end(); ai++ )
	{
		if(!(*ai).get_bool())
		{
			continue;
		}

		constraint_t con = VEC_index(constraint_t, aliases, (*ai).get_int());

		if(con == NULL)
			continue;

		if(con->phi_stmt)
			continue;

		tree lhs_bb = VEC_index(csvarinfo_t,csvarmap,con->lhs.var)->decl;

		if(vi->id == con->lhs.var)
		{
//			fprintf(dump_file,"\nLHS Var %s-%d, RHS Var %s-%d\n", get_var_name(con->lhs.var), con->lhs.var, get_var_name(con->rhs.var), con->rhs.var);

			return con->rhs.var;
		}
	}

	return 0;
}

bool array_ptr_arith(node_id_type node)
{
	Node n = getNode(node);
	IndirectionList ill = n.getList();
	unsigned int vid = n.getVarIndex();

	csvarinfo_t v1, v2, v3, v4;
	tree t1, t2;

	v1 = cs_get_varinfo(vid);
	t1 = SSAVAR(v1->decl);

	set< unsigned int > res = cs_get_all_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, vid), 0);

	if(!res.empty() && ill.stackIndirectionList() && ill.Length() > 2)
		return true; 

	#if 0
	for(definitions:: iterator it = glob_lhs.begin(); it != glob_lhs.end(); it++)
	{
		v2 = cs_get_varinfo(get<0>(*it));

		t2 = SSAVAR(v2->decl);

//		if(get<0>(rhs) == get<0>(*it))
		if(DECL_UID(t1) == DECL_UID(t2))
		{
			if(ill->stackIndirectionList())
				return true;
		}
	}
	#endif

	return false;
}

definitions resolve_ssa(node_id_type node, bool type, basic_block bb, struct cgraph_node *cnode) // type = true => lhs, type = false => rhs
{
	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nTop resolving node\n");
	print_NodeID(node);
	#endif

	definitions res, res_temp;

	tree t;
	node_id_type temp;
	unsigned int id;
	set< unsigned int >::iterator cit;	
	set< unsigned int > cons_list;

	// Creating an empty Indirection List
	IndirectionList ilt;
	std::vector< IndirectionList > rem, fin;
	int *field_list;

	IndirectionList e_list(true, 0, 0, field_list);
	IndirectionList f_list(true, 1, 0, field_list);

	Node nt = getNode(node);

	id = nt.getVarIndex();
	ilt = nt.getList();

	t = VEC_index(csvarinfo_t, csvarmap, id)->decl;

	if(id <= 4)
	{
		res.insert(node);
//		fprintf(dump_file, "\nNode\n");
//		print_NodeID(node);
//		fprintf(dump_file, "\nResolved to\n");
//		printDefinitions(res);

		return res;
	}

	gcc_assert(t && TREE_CODE(t) == SSA_NAME);

	visited_nodes.insert(node);

	gimple stmt = SSA_NAME_DEF_STMT(t);

	if(!stmt)
	{
//		fprintf(dump_file, "\nNode\n");
//		print_NodeID(node);
//		fprintf(dump_file, "\nResolved to\n");
//		printDefinitions(res);
		return res;
	}

//	print_gimple_stmt (dump_file, stmt, 0, 0);
//	fprintf(dump_file,"\n\n");

	cons_list = gimple_to_constraints[stmt];

	if(is_gimple_call(stmt))
	{
		if (gimple_call_flags (stmt) & ECF_MALLOC)
		{
//			fprintf(dump_file, "\nMalloc\n");

			unsigned int rhs_heap = get_art_node(stmt, bb, cnode);

			if(rhs_heap != 0)
			{
				tree lhs = gimple_call_lhs (stmt);

				rem = ilt.remainder(f_list);
	
				fin = e_list.append_list(rem);

				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(rhs_heap, *it);

//					fprintf(dump_file, "\nInserting New Node in res\n");
//					print_NodeID(new_node.getNodeID());

					res.insert(new_node.getNodeID());
				}
			}
		}

		if(type){
		for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
		{
			constraint_t exp = VEC_index(constraint_t,aliases, *cit);

			IndirectionList il1, il2;
			std::tuple< IndirectionList, IndirectionList > il_temp;

			il_temp = createIndirectionList(exp);

			il1 = get<0>(il_temp);
			il2 = get<1>(il_temp);

			rem = ilt.remainder(il1);
			
			fin = il2.append_list(rem);

			tree rhs_op = VEC_index(csvarinfo_t,csvarmap,exp->rhs.var)->decl;

			if(exp->rhs.var > 4 && TREE_CODE(rhs_op) == SSA_NAME)
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

					if(visited_nodes.find(temp) == visited_nodes.end()) // && (!type && !array_ptr_arith(temp)))			
					{
						if(!reuse_ssa[temp].empty())
						{
							res_temp = reuse_ssa[temp];
						}
						else
						{
							res_temp = resolve_ssa(temp, type, bb, cnode);

							reuse_ssa[temp] = res_temp;
						}

						for(definitions::iterator dit = res_temp.begin(); dit != res_temp.end(); dit++)
						{
//							fprintf(dump_file, "\nInserting New Node in res\n");
//							print_NodeID(*dit);
							res.insert(*dit);
						}	
					}
					#if 1
					else
					{
//						fprintf(dump_file, "\nInserting New Node in res Already in visited list\n");
						//print_NodeID(temp);
						res_temp = reuse_ssa[temp];
						res.insert(res_temp.begin(), res_temp.end());
//						res.insert(temp);
					}
					#endif
				}
			}
			else
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

//					fprintf(dump_file, "\nInserting New Node in res, !SSA\n");
//					print_NodeID(temp);
					res.insert(temp);
				}
			}
		}
		}
	}
	else if(gimple_code(stmt) == GIMPLE_PHI)
	{
//		fprintf(dump_file, "\nPhi Statement\n");
//		print_gimple_stmt (dump_file, stmt, 0, 0);
//		fprintf(dump_file,"\n\n");
//		fprintf(dump_file, "\nResolving Node\n");
//		print_NodeID(node);
		
		for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
		{
			constraint_t exp = VEC_index(constraint_t,aliases, *cit);
			
			IndirectionList il1, il2, f_il, il3;
			std::tuple< IndirectionList, IndirectionList > il_temp;
			
			il_temp = createIndirectionList(exp);

			il1 = get<0>(il_temp);
			il2 = get<1>(il_temp);

			rem = ilt.remainder(il1);

			fin = il2.append_list(rem);

			tree rhs_op = VEC_index(csvarinfo_t,csvarmap,exp->rhs.var)->decl;

			if(exp->rhs.var > 4 && TREE_CODE(rhs_op) == SSA_NAME)
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

					if(visited_nodes.find(temp) == visited_nodes.end()) // && (!type && !array_ptr_arith(temp)))			
					{
						if(!reuse_ssa[temp].empty())
						{
							res_temp = reuse_ssa[temp];
						}
						else
						{
							res_temp = resolve_ssa(temp, type, bb, cnode);

							reuse_ssa[temp] = res_temp;
						}

						for(definitions::iterator dit = res_temp.begin(); dit != res_temp.end(); dit++)
						{
//							fprintf(dump_file, "\nInserting New Node in res\n");
//							print_NodeID(*dit);
							res.insert(*dit);
						}	
					}
					#if 1
					else
					{
//						fprintf(dump_file, "\nInserting New Node in res, not in visited list\n");
						//print_NodeID(temp);
						res_temp = reuse_ssa[temp];
						res.insert(res_temp.begin(), res_temp.end());
//						res.insert(temp);
					}
					#endif
				}
			}
			else
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

//					fprintf(dump_file, "\nInserting New Node in res, !SSA\n");
//					print_NodeID(temp);
					res.insert(temp);
				}
			}
		}
	}
	else if(gimple_code(stmt) == GIMPLE_NOP)
	{
//		fprintf(dump_file, "\nNOP\n");
//		print_gimple_stmt (dump_file, stmt, 0, 0);
//		fprintf(dump_file,"\n\n");
//		fprintf(dump_file, "\nNode that cannot be resolved\n");
//		print_NodeID(node);
//		fprintf(dump_file, "\nTree Node with SSA\n", alias_get_name(t));
		
		if(is_par_ret(t, cnode, bb) && type)
		{
			tree t1 = SSAVAR(t);

//			fprintf(dump_file, "\nTree Node after SSA\n", alias_get_name(t1));
	
			if(t1)
			{
				csvarinfo_t newnode  = cs_lookup_vi_for_tree(t1);

				if(newnode)
				{
					Node new_node(newnode->id, ilt);
					temp = new_node.getNodeID();

//					fprintf(dump_file, "\nInserting New Node in res\n");
//					print_NodeID(temp);
					res.insert(temp);
				} 	
			}
		}
		else
		{
			res.insert(node);
		}
	}
	#if 0
	else if(gimple_assign_rhs_code(stmt) == POINTER_PLUS_EXPR)
	{
		fprintf(dump_file, "\nHurray\n");
		for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
		{
			constraint_t exp = VEC_index(constraint_t,aliases, *cit);
	
			print_constraint(exp);
		}
		fprintf(dump_file, "\nHurraaaaaaaaaaaay\n");

		Node new_node(undef_id, e_list);
		temp = new_node.getNodeID();

		res.insert(temp);
	}
	#endif
	else if(gimple_code(stmt) == GIMPLE_ASSIGN || gimple_assign_rhs_code(stmt) == POINTER_PLUS_EXPR)
	{
//		fprintf(dump_file, "\nAssignment\n");

		if(gimple_assign_rhs_code(stmt) == POINTER_PLUS_EXPR)
		{
			ptr_arith = true;
		}

		for(cit = cons_list.begin(); cit != cons_list.end(); cit++)
		{
			constraint_t exp = VEC_index(constraint_t,aliases, *cit);

//			print_constraint(exp);
			
			IndirectionList il1, il2;
			std::tuple< IndirectionList, IndirectionList > il_temp;
			
			il_temp = createIndirectionList(exp);

			il1 = get<0>(il_temp);
			il2 = get<1>(il_temp);

			rem = ilt.remainder(il1);
			fin = il2.append_list(rem);

			tree rhs_op = VEC_index(csvarinfo_t,csvarmap,exp->rhs.var)->decl;

			if(exp->rhs.var > 4 && TREE_CODE(rhs_op) == SSA_NAME)
			{
//				fprintf(dump_file, "\nRHS is also SSA\n");

				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

					if(visited_nodes.find(temp) == visited_nodes.end()) // && (!type && !array_ptr_arith(temp)))
					{
//						fprintf(dump_file, "\nVisited Already\n");

						if(!reuse_ssa[temp].empty())
						{
//							fprintf(dump_file, "\nAlready Resolved\n");

							res_temp = reuse_ssa[temp];
						}
						else
						{
//							fprintf(dump_file, "\nTo be Resolved\n");

							res_temp = resolve_ssa(temp, type, bb, cnode);

							reuse_ssa[temp] = res_temp;
						}

						for(definitions::iterator dit = res_temp.begin(); dit != res_temp.end(); dit++)
						{
//							fprintf(dump_file, "\nInserting New Node in res\n");
//							print_NodeID(*dit);
							res.insert(*dit);
						}	
					}
					#if 1
					else
					{
//						fprintf(dump_file, "\n!Visited Already\n");

//						fprintf(dump_file, "\nInserting New Node in res, not in visited list\n");
//						print_NodeID(temp);
						res_temp = reuse_ssa[temp];
						res.insert(res_temp.begin(), res_temp.end());
//						res.insert(temp);
					}
					#endif
				}
			}
			else
			{
				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					Node new_node(exp->rhs.var, *it);
					temp = new_node.getNodeID();

//					fprintf(dump_file, "\nInserting New Node in res, !SSA\n");
//					print_NodeID(temp);
					res.insert(temp);
				}
			}	
		}
	}

	if(res.empty())
	{
		res.insert(node);
	}

//	boundary_nodes.insert(res.begin(), res.end());

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nNode\n");
	print_NodeID(node);
	fprintf(dump_file, "\nResolved to\n");
	printDefinitions(res);
	#endif

	return res;
}

GPUSet resolveConstraintSSA(constraint_t cons, basic_block bb, struct cgraph_node *cnode)
{
	#if 0
	fprintf(dump_file,"\nPrinting Constraint\n");
	print_constraint(cons);
	#endif

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	unsigned int id = 0;

	GPUSet res;

	tree lhs, rhs;

//	if(con->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && con->lhs.type == 1 && is_par_ret(lhs, caller, bb))

	lhs = VEC_index(csvarinfo_t,csvarmap,cons->lhs.var)->decl;
	rhs = VEC_index(csvarinfo_t,csvarmap,cons->rhs.var)->decl;

	node_id_type lnode, rnode;
	definitions ldef, rdef;

	IndirectionList l_list, r_list;

//	fprintf(dump_file,"\nJourney Begins\n");
//	fflush(dump_file);

	std::tuple< IndirectionList, IndirectionList > il_temp;
			
	il_temp = createIndirectionList(cons);

	l_list = get<0>(il_temp);
	r_list = get<1>(il_temp);

	#if 0
	fprintf(dump_file,"\nIndirectionLists Created\n");
	fflush(dump_file);
	#endif

	Node l_node(cons->lhs.var, l_list);
        lnode = l_node.getNodeID();

//	fprintf(dump_file,"\nlnode Created\n");
//	l_node.printNode();
//	fflush(dump_file);

	Node r_node(cons->rhs.var, r_list);
        rnode = r_node.getNodeID();

//	fprintf(dump_file,"\nrnode Created\n");
//	r_node.printNode();
//	fflush(dump_file);
	bool ptr_arith_l = false, ptr_arith_r = false;

	if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && !is_par_ret(lhs, cnode, bb))
	{
//		fprintf(dump_file,"\nSSA LHS with no DEREF and no para-ret\n");
		return res;
	}
	else if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && is_par_ret(lhs, cnode, bb))
	{
//		fprintf(dump_file,"\nSSA LHS with no DEREF but a para-ret\n");
		visited_nodes.clear();

		ptr_arith = false;

		ldef = resolve_ssa(lnode, true, bb, cnode); 

		ptr_arith_l = ptr_arith;
	}
	else if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME)
	{
//		fprintf(dump_file,"\nSSA LHS with DEREF\n");
		visited_nodes.clear();

		ptr_arith = false;

		ldef = resolve_ssa(lnode, true, bb, cnode); 

		ptr_arith_l = ptr_arith;
	}
	else
	{
//		fprintf(dump_file,"\nNON_SSA LHS\n");
		Node new_node(cons->lhs.var, l_list);
//		new_node.printNode();
		ldef.insert(new_node.getNodeID());
	}

	if(cons->rhs.var > 4 && TREE_CODE(rhs) == SSA_NAME)
	{
//		fprintf(dump_file,"\nSSA RHS\n");
		visited_nodes.clear();

		ptr_arith = false;

		rdef = resolve_ssa(rnode, false, bb, cnode); 

		ptr_arith_r = ptr_arith;
	}
	else
	{
//		fprintf(dump_file,"\nNON_SSA RHS\n");
		Node new_node(cons->rhs.var, r_list);
//		new_node.printNode();
		rdef.insert(new_node.getNodeID());
	}

	for(definitions::iterator lit = ldef.begin(); lit != ldef.end(); lit++)
	{
//		fprintf(dump_file,"\nPrinting ldef\n");
//		print_NodeID(*lit);
		
		for(definitions::iterator rit = rdef.begin(); rit != rdef.end(); rit++)
		{
//			fprintf(dump_file,"\nPrinting rdef\n");
//			print_NodeID(*rit);
		
			GPU gpu(*lit, *rit);

			gpu_id_type t = gpu.getGPUID();

			if(ptr_arith_l || ptr_arith_r)
			{
				ptr_arith_map[t] = true;	
			}

//			fprintf(dump_file,"\nHey Der\n");
//			gpu.printGPU();
			res.insert(t);		
		}
	}
	
	return res;
}

GPUSet resolve_constraint_SSA(unsigned int id, basic_block bb, struct cgraph_node *cnode, bool use)
{
//	fprintf(dump_file,"\nPrinting Constraint\n");
//	print_constraint(VEC_index(constraint_t, aliases, id));

	
//	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPUSet res;

	if(!use)
	{
//		fprintf(dump_file, "\nUse\n");
//		fflush(dump_file);

		tree rhs = VEC_index(csvarinfo_t,csvarmap, id)->decl;
		definitions ldef, rdef;
		csvarinfo_t vi = cs_get_varinfo (id);	
		bool ptr_arith, ptr_arith_r;

		if(vi == NULL)
		{
			return res;
		}
	
		bool tp;

		if(id < 4)
		{
			tp = false;
		}
		else
		{
			tp = isAggregrateNode(vi);
		}

		struct constraint_expr exp;
		exp.var = id;
		exp.offset = 0;
		exp.type = SCALAR;
		IndirectionList list_l = create_indirection_list(tp, exp);

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nlist_l %d in basic_block %d, function %s for var %d (%s)\n", list_l.get_st_hp(), bb->index, cgraph_node_name(cnode), id, vi->name);
		fflush(dump_file);
		#endif

		Node rnode(id, list_l);
		Node lnode(summ_node_id, list_l);
		ldef.insert(lnode.getNodeID());

		if(id > 4 && TREE_CODE(rhs) == SSA_NAME)
		{
//			fprintf(dump_file,"\nSSA RHS\n");
			visited_nodes.clear();

			ptr_arith = false;

			rdef = resolve_ssa(rnode.getNodeID(), false, bb, cnode); 

			ptr_arith_r = ptr_arith;
		}
		else
		{
			rdef.insert(rnode.getNodeID());
		}

		for(definitions::iterator lit = ldef.begin(); lit != ldef.end(); lit++)
		{
//			fprintf(dump_file,"\nPrinting ldef\n");
//			print_NodeID(*lit);
		
			for(definitions::iterator rit = rdef.begin(); rit != rdef.end(); rit++)
			{
//				fprintf(dump_file,"\nPrinting rdef\n");
//				print_NodeID(*rit);

				if(*lit == *rit)
				{
					continue;
				}	
		
				GPU gpu(*lit, *rit);

				gpu_id_type t = gpu.getGPUID();

				if(ptr_arith_r)
				{
					ptr_arith_map[t] = true;	
				}			

//				fprintf(dump_file,"\nHey Der\n");
//				gpu.printGPU();
				res.insert(t);		
			}
		}
	
		boundary_nodes.insert(rdef.begin(), rdef.end());

		return res;
	}

	tree lhs, rhs;

//	if(con->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && con->lhs.type == 1 && is_par_ret(lhs, caller, bb))

	constraint_t cons = VEC_index(constraint_t, aliases, id);

	lhs = VEC_index(csvarinfo_t,csvarmap,cons->lhs.var)->decl;
	rhs = VEC_index(csvarinfo_t,csvarmap,cons->rhs.var)->decl;

	node_id_type lnode, rnode;
	definitions ldef, rdef;

	IndirectionList l_list, r_list;

//	fprintf(dump_file,"\nJourney Begins\n");
//	fflush(dump_file);

	std::tuple< IndirectionList, IndirectionList > il_temp;
			
	il_temp = createIndirectionList(cons);

	l_list = get<0>(il_temp);
	r_list = get<1>(il_temp);

//	fprintf(dump_file,"\nIndirectionLists Created\n");
//	fflush(dump_file);

	Node l_node(cons->lhs.var, l_list);
        lnode = l_node.getNodeID();

//	fprintf(dump_file,"\nlnode Created\n");
//	l_node.printNode();
//	fflush(dump_file);

	Node r_node(cons->rhs.var, r_list);
        rnode = r_node.getNodeID();

//	fprintf(dump_file,"\nrnode Created\n");
//	r_node.printNode();
//	fflush(dump_file);
	bool ptr_arith_l = false, ptr_arith_r = false;

	#if 1
	if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && !is_par_ret(lhs, cnode, bb))
	{
//		fprintf(dump_file,"\nSSA LHS with no DEREF and no para-ret\n");
		ldef.insert(lnode);
	}
	#endif
	else if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && is_par_ret(lhs, cnode, bb))
	{
//		fprintf(dump_file,"\nSSA LHS with no DEREF but a para-ret\n");
		//visited_nodes.clear();
		//ldef = resolve_ssa(lnode, true, bb, cnode); 
		csvarinfo_t vi = cs_get_varinfo(cons->lhs.var);
		if(vi)
		{
			tree decl = vi->decl;
//			decl = SSAVAR(decl);
			vi = cs_lookup_vi_for_tree (decl);
			if(vi)
			{
				Node new_node(vi->id, l_list);
				ldef.insert(new_node.getNodeID());
//				printSetofNodeIDs(ldef);
			}
		}	
	}
	else if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME)
	{
//		fprintf(dump_file,"\nSSA LHS with DEREF\n");
		visited_nodes.clear();

		ptr_arith = false;

		ldef = resolve_ssa(lnode, true, bb, cnode); 

//		fprintf(dump_file, "\nHeap hey\n");
//		printSetofNodeIDs(ldef);

		ptr_arith_l = ptr_arith;
	}
	else
	{
//		fprintf(dump_file,"\nNON_SSA LHS\n");
//		Node new_node(cons->lhs.var, l_list);
//		new_node.printNode();
//		ldef.insert(new_node.getNodeID());

		ldef.insert(lnode);	
	}

	if(cons->rhs.var > 4 && TREE_CODE(rhs) == SSA_NAME)
	{
//		fprintf(dump_file,"\nSSA RHS\n");
		visited_nodes.clear();

		ptr_arith = false;

		rdef = resolve_ssa(rnode, false, bb, cnode); 

		ptr_arith_r = ptr_arith;
	}
	else
	{
//		fprintf(dump_file,"\nNON_SSA RHS\n");
//		Node new_node(cons->rhs.var, r_list);
//		new_node.printNode();
//		rdef.insert(new_node.getNodeID());
		rdef.insert(rnode);
	}

	for(definitions::iterator lit = ldef.begin(); lit != ldef.end(); lit++)
	{
//		fprintf(dump_file,"\nPrinting ldef\n");
//		print_NodeID(*lit);
		
		for(definitions::iterator rit = rdef.begin(); rit != rdef.end(); rit++)
		{
//			fprintf(dump_file,"\nPrinting rdef\n");
//			print_NodeID(*rit);

			if(*lit == *rit)
			{
				continue;
			}
		
			GPU gpu(*lit, *rit);

			gpu_id_type t = gpu.getGPUID();

			if(ptr_arith_l || ptr_arith_r)
			{
				ptr_arith_map[t] = true;	
			}			

//			fprintf(dump_file,"\nHey Der\n");
//			gpu.printGPU();

			res.insert(t);		
		}
	}
	
	boundary_nodes.insert(ldef.begin(), ldef.end());
	boundary_nodes.insert(rdef.begin(), rdef.end());

	return res;
}

definitions resolve_fp_ssa(unsigned int fp_var, basic_block bb, struct cgraph_node *cnode)
{
	node_id_type node;
	int *field_list;

	IndirectionList list(true, 1, 0, field_list);

	Node new_node(fp_var, list);	
	node = new_node.getNodeID();

	ptr_arith = false;

	visited_nodes.clear();

	return resolve_ssa(node, true, bb, cnode);
}

GPUSet map_para_args_fp_call(unsigned int callee_rep, unsigned int caller_rep, basic_block bb)
{
	struct cgraph_node *caller, *callee;
	gimple stmt;

	caller = func_numbering[caller_rep];
	callee = func_numbering[callee_rep];
	
	stmt = bb_call_stmt(bb);

	int j, argoffset = 1, i;
	tree arg, par;
	GPUSet res, temp;
	csvarinfo_t fi;

	tree decl = callee->decl;

	if(!decl)
		return res;

	fi = cs_get_vi_for_tree (decl, bb, caller);

	if(fi == NULL)
		return res;

	for (j = 0; j < gimple_call_num_args (stmt); j++)
	{
//		fprintf(dump_file,"\nArg\n");

		arg = gimple_call_arg (stmt, j);

		if (field_must_have_pointers (arg))
		{
			csvarinfo_t cvar = cs_first_vi_for_offset (fi, argoffset);

			if(cvar == NULL)
				continue;

			par = cvar->decl;

			if(par == NULL)
				return res;

			if(field_must_have_pointers(par))
			{
//				fprintf(dump_file,"\nBoth Pointers\n");

				VEC(ce_s, heap) *lhsc = NULL;
				VEC(ce_s, heap) *rhsc = NULL;

//				fprintf(dump_file, "\nParameter %s\n", alias_get_name(par));
//				fprintf(dump_file, "\nArgument %s\n", alias_get_name(arg));

				cs_get_constraint_for(par, &lhsc, bb, caller);
				cs_get_constraint_for(arg, &rhsc, bb, caller);

				struct constraint_expr *c;	
				struct constraint_expr *c2;
				unsigned int k1, k2;

               			FOR_EACH_VEC_ELT (ce_s, lhsc, k1, c)
				//while(VEC_length(ce_s, lhsc) != 0)
				{
					//c = VEC_last(ce_s, lhsc);

               				FOR_EACH_VEC_ELT (ce_s, rhsc, k2, c2)
					//while(VEC_length(ce_s, rhsc) != 0)
					{
						//c2 = VEC_last(ce_s, rhsc);

						constraint_t con = new_constraint (*c, *c2);

//						fprintf(dump_file, "\nHey Constraint\n");
//						print_constraint(con);

						temp = resolveConstraintSSA(con, bb, caller);

						res.insert(temp.begin(), temp.end());
					}
				}

   				VEC_free (ce_s, heap, lhsc);
   				VEC_free (ce_s, heap, rhsc);
			}
		}
	}

	return res;
}

#if 0
bool isDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	basic_block bb1, bb2;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	int b1, b2;
	GPB gpb1, gpb2;

	gpb1 = gpb_map[gpb_id1];
	gpb2 = gpb_map[gpb_id2];

	b1 = gpb1.getBBIndex();
	b2 = gpb2.getBBIndex();

	if(b1 == b2)
	{
		if(gpb_id1 < gpb_id2)
			return true;

		return false;
	}

	bool flag = false;
	
	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	bb1 = BASIC_BLOCK(b1);
	bb2 = BASIC_BLOCK(b2);

	if((dominated_by_p(CDI_DOMINATORS, bb1, bb2)))
	{
		flag = true;
	}

	pop_cfun();

	return flag;
}

bool isPDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	basic_block bb1, bb2;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	int b1, b2;
	GPB gpb1, gpb2;

	gpb1 = gpb_map[gpb_id1];
	gpb2 = gpb_map[gpb_id2];

	b1 = gpb1.getBBIndex();
	b2 = gpb2.getBBIndex();

	if(b1 == b2)
	{
		if(gpb_id1 < gpb_id2)
			return true;

		return false;
	}

	bool flag = false;
	
	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	bb1 = BASIC_BLOCK(b1);
	bb2 = BASIC_BLOCK(b2);

	if(dominated_by_p(CDI_POST_DOMINATORS, bb2, bb1))
	{
		flag = true;
	}

	pop_cfun();

	return flag;
}

bool isDomPDom(unsigned int gpb_id1, unsigned int gpb_id2, struct cgraph_node *cnode)
{
	basic_block bb1, bb2;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	int b1, b2;
	GPB gpb1, gpb2;

	gpb1 = gpb_map[gpb_id1];
	gpb2 = gpb_map[gpb_id2];

	b1 = gpb1.getBBIndex();
	b2 = gpb2.getBBIndex();

	if(b1 == b2)
	{
		if(gpb_id1 < gpb_id2)
			return true;

		return false;
	}

	bool flag = false;
	
	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

	bb1 = BASIC_BLOCK(b1);
	bb2 = BASIC_BLOCK(b2);

	if((dominated_by_p(CDI_DOMINATORS, bb1, bb2) && dominated_by_p(CDI_POST_DOMINATORS, bb2, bb1)))
//	(dominated_by_p(CDI_DOMINATORS, bb2, bb1) && dominated_by_p(CDI_POST_DOMINATORS, bb1, bb2)))
	{
		flag = true;
//		return true;
	}

	pop_cfun();

	return flag;

//	return false;
}
#endif

GPUSet get_global_info()
{
	struct varpool_node *node;
	tree t;

	GPUSet initial_decls;

	for (node = varpool_nodes; node; node = node->next)
        {
		t = node->decl;

		csvarinfo_t vi = cs_get_vi_for_tree(t, main_firstbb, main_cnode);

                if(field_must_have_pointers(t))
                {
			if (DECL_INITIAL (t))
			{
				VEC (ce_s, heap) *rhsc = NULL;

				cs_get_constraint_for_rhs (DECL_INITIAL (t), &rhsc, main_firstbb, main_cnode);

				struct constraint_expr lhs, *rhsp, rhs;
				unsigned i;

				lhs.var = vi->id;
				lhs.offset = 0;
				lhs.type = SCALAR;

				int *field_list;
				IndirectionList l_ind(true, 1, 0, field_list);
				IndirectionList r_ind;
				Node l_decl(vi->id, l_ind);

				FOR_EACH_VEC_ELT (ce_s, rhsc, i, rhsp)               // Vini: Why commented out????
				{
					rhs = *rhsp;

					if(rhs.offset == 0 && rhs.type == ADDRESSOF)
					{
						constraint_count++;

						Node r_decl(rhs.var, r_ind);

						GPU gpu(l_decl, r_decl);

						initial_decls.insert(gpu.getGPUID());

						continue;
					}

					cs_process_constraint (new_constraint (lhs, *rhsp), main_firstbb);
				}

				VEC_free (ce_s, heap, rhsc);
			}
		}
	}

	return initial_decls;

//	unsigned int main_cnum = ((function_info *)(main_cnode->aux))->func_num;

//	RIN[1] = initial_decls;
//	BRIN[1] = initial_decls;

//	fflush(dump_file);
//	fprintf(dump_file,"\nNumber of Intialization Constraints %d\n", VEC_length(constraint_t, aliases)); 	
//	fflush(dump_file);
}

GPG createNewGPG(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	basic_block bb = start_bb_of_fn(cnode);
	GPG res;
	GPB entry, gpb, exit;
	GPBSet gpbs, prev2, prev3, next1, next2;

	unsigned int x = res.GPB_count;

	GPUSet maygen, mustkill, temp;

	maygen = DownwardsExposedMayDefinitions[cnode_num];
	mustkill = DownwardsExposedMustDefinitions[cnode_num];

	if(maygen.empty())
	{
		res.GPB_count++;

		entry.setId(x);
		entry.setBBIndex(bb->index);
		entry.setGPUs(mustkill);
		res.gpb_map[x] = entry;

		gpbs.insert(x);
		res.setEntryGPB(x);
		res.setExitGPB(x);
		res.setGPBs(gpbs);

		return res;
	}
	else
	{
		res.GPB_count += 3;

		entry.setId(x);
		entry.setBBIndex(bb->index);
		entry.setGPUs(mustkill);
		next1.insert(x+1);
		next1.insert(x+2);
		res.setNext(x, next1);
		res.gpb_map[x] = entry;

		gpb.setId(x+1);
		gpb.setBBIndex(bb->index);
		gpb.setGPUs(maygen);
		prev2.insert(x);
		next2.insert(x+2);
		res.setPrev((x+1), prev2);
		res.setNext((x+1), next2);
		res.gpb_map[x+1] = gpb;

		exit.setId(x+2);
		exit.setBBIndex(bb->index);
		exit.setGPUs(temp);
		prev3.insert(x);
		prev3.insert(x+1);
		res.setPrev((x+2), prev3);
		res.gpb_map[x+2] = exit;
		
		gpbs.insert(x);
		gpbs.insert(x+1);
		gpbs.insert(x+2);
		res.setEntryGPB(x);
		res.setExitGPB(x+2);
		res.setGPBs(gpbs);

		return res;
	}
}

IndirectionList create_indirection_list(bool type, struct constraint_expr e)
{
	int field_list[IndirectionList::kSize];
	tree t;

//	fprintf(dump_file, "\nInside create_indirection_list %s-%d, %d, %d\n", get_var_name(e.var), e.var, e.type, e.offset);
//	fflush(dump_file);

	csvarinfo_t vi = cs_get_varinfo (e.var);

	if(vi == NULL)
	{
		IndirectionList list;
		return list;
	}

//	fprintf(dump_file, "\nAfter vi serach %d\n", vi->id);
//	fflush(dump_file);

//	if(is_aggregrate_type_varinfo(vi))
	if(type)
	{
//		fprintf(dump_file, "\nAggregrate true\n");
//		fflush(dump_file);

		if(e.type == 1)
		{
//			fprintf(dump_file, "\nScalar\n");
//			fflush(dump_file);

			field_list[0] = SFIELD;
			IndirectionList list(false, 0, 1, field_list);

			return list;	
		}
		else if(e.type == 2)
		{
//			fprintf(dump_file, "\nDeref\n");
//			fflush(dump_file);

			field_list[0] = SFIELD;
			field_list[1] = e.offset;
			IndirectionList list(false, 0, 2, field_list);

			return list;	
		}
		else
		{
//			fprintf(dump_file, "\nAddressof\n");
//			fflush(dump_file);

			IndirectionList list(false, 0, 0, field_list);

			return list;	
		}
	}
	else
	{
//		fprintf(dump_file, "\nAggregrate false\n");
//		fflush(dump_file);

		if(e.type == 1)
		{
//			fprintf(dump_file, "\nScalar\n");
//			fflush(dump_file);

			IndirectionList list(true, 1, 0, field_list);

			return list;	
		}
		else if(e.type == 2)
		{
//			fprintf(dump_file, "\nDeref\n");
//			fflush(dump_file);

			IndirectionList list(true, 2, 0, field_list);

			return list;	
		}
		else
		{
//			fprintf(dump_file, "\nAddressof\n");
//			fflush(dump_file);

			IndirectionList list(true, 0, 0, field_list);

			return list;	
		}
	}
}

std::tuple< IndirectionList, IndirectionList > createIndirectionList(constraint_t con)
{
//	fprintf(dump_file,"\nPrinting Constraint\n");
//	print_constraint(con);

	bool lagg, ragg;
	std::tuple< IndirectionList, IndirectionList > res;
	struct constraint_expr lhs, rhs;
	IndirectionList l, r;

	lhs = con->lhs;
	rhs = con->rhs;

	csvarinfo_t vi_l = cs_get_varinfo (lhs.var);
	csvarinfo_t vi_r = cs_get_varinfo (rhs.var);

	if(vi_l == NULL || vi_r == NULL)
	{
		return res;
	}

//	fprintf(dump_file, "\nAfter vi serach %d\n", vi->id);
//	fflush(dump_file);

//	if(is_aggregrate_type_varinfo(vi))

	if(lhs.var <= 4)
	{
		lagg = false;
	}
	else
	{
		lagg = isAggregrateNode(vi_l);
	}

	if(rhs.var <= 4)
	{
		ragg = false;
	}
	else
	{
		ragg = isAggregrateNode(vi_r);
	}

	if(lagg && ragg) // Both are aggregrate types
	{
		l = create_indirection_list(true, lhs);
		r = create_indirection_list(true, rhs);
	}
	else if(!lagg && !ragg) // Both are scalar types
	{
		l = create_indirection_list(false, lhs);
		r = create_indirection_list(false, rhs);
	}
	else
	{
		l = create_indirection_list(true, lhs);
		r = create_indirection_list(true, rhs);
	}

	#if 0
	fprintf(dump_file, "\nPrinting l: ");
	l.printIndirectionList();
	fprintf(dump_file, "\n");
	fprintf(dump_file, "\nPrinting r: ");
	r.printIndirectionList();
	fprintf(dump_file, "\n");
	#endif

	res = std::make_tuple(l, r);

	return res;
}

bool filter_constraint(unsigned int id, basic_block bb, struct cgraph_node *cnode) // Filter this constraint if this function returns true
{
	constraint_t cons = VEC_index(constraint_t, aliases, id);

	tree lhs = VEC_index(csvarinfo_t,csvarmap,cons->lhs.var)->decl;
	tree rhs = VEC_index(csvarinfo_t,csvarmap,cons->rhs.var)->decl;

	if(cons->lhs.var > 4 && TREE_CODE(lhs) == SSA_NAME && cons->lhs.type == 1 && !is_par_ret(lhs, cnode, bb))
	{
		return true;
	}

	return false;
}

bool needsInlining(unsigned int caller, unsigned int callee)
{

	struct cgraph_node *callee_node = func_numbering[callee];
	struct cgraph_node *caller_node = func_numbering[caller];

	#if 0
	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (callee_node->decl)), "exit") == 0)
	{
		return false;
	}
	#endif

	if(caller == callee)
	{
//		fprintf(dump_file, "\nSelf Recursive call %s\n", cgraph_node_name(caller_node), cgraph_node_name(callee_node));

		return false;
	}

	if(processed_functions.find(callee) != processed_functions.end())
	{
//		fprintf(dump_file, "\nProcessed Function %s\n", cgraph_node_name(callee_node));

		return true;
	}

//	fprintf(dump_file, "\nNot Processed Function %s\n", cgraph_node_name(callee_node));

	return false;

	#if 0
	if(callee_node)
	{
		#if !RECURSION
		if(caller == callee)
		{
			return false;
		}
		#endif

		if(((function_info *)(callee_node->aux))->has_fixed_pt())
		{
			fprintf(dump_file,"\nInlining Required Condition 1\n");
			fflush(dump_file);

			return true;
		}
		else
		{
			#if RECURSION
			if(caller == callee)
			{
				fprintf(dump_file,"\nInlining Required Condition 2\n");
				fflush(dump_file);

				return true;
			}
			#endif
		}
	}

	fprintf(dump_file,"\nReturning false\n");
	fflush(dump_file);

	return false;
	#endif
}

bool needsInliningRecursion(unsigned int caller, unsigned int callee)
{
	if(caller == callee)
	{
		return true;
	}

	return false;
}

void collectUpwardExposedVersions(GPUSet gen, struct cgraph_node *cnode)
{	
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	definitions l_temp, r_temp;
	unsigned int lvar, rvar;
	node_id_type lnode, rnode;
	Node nl, nr;

	l_temp = lhsUpwardsExposedDefinitions[caller_rep];
	r_temp = rhsUpwardsExposedDefinitions[caller_rep];

	for(GPUSet::iterator it = gen.begin(); it != gen.end(); it++)
	{

		lnode = get<0>(*it);
		rnode = get<1>(*it);

		nl = getNode(lnode);
		nr = getNode(rnode);

		lvar = get<0>(lnode);
		rvar = get<0>(rnode);

		if(CDV.find(lvar) != CDV.end() || nl.getList().Length() > 1)
		{
			l_temp.insert(lnode);
		}

		if(CDV.find(rvar) != CDV.end() || nr.getList().Length() >= 1)
		{
			r_temp.insert(rnode);
		}
	}
	
	lhsUpwardsExposedDefinitions[caller_rep] = l_temp;
	rhsUpwardsExposedDefinitions[caller_rep] = r_temp;
}

GPBSet get_bb_pred(basic_block bb, struct cgraph_node *cnode)
{
	GPBSet preds;
	GPBSet temp;

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;
	
	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	edge e;
        edge_iterator ei;
	basic_block bt;

	#if 0
	fprintf(dump_file, "\nInside get_bb_pred for %d\n", bb->index);
	fflush(dump_file);
	#endif

       	FOR_EACH_EDGE(e,ei,bb->preds)
       	{
//		fprintf(dump_file, "\nInside for loop\n");
//		fflush(dump_file);

               	bt = e->src;

		if(bt->index == 0)
		{
			continue;
		}

//		fprintf(dump_file,"\nCFG-pred %d\n", bt->index);
//		fflush(dump_file);

//		temp = ((block_information *)(bt->aux))->eblocks;	
		temp = BB_END[caller_rep][bt->index];

		preds.insert(temp.begin(), temp.end());	
	}

	#if 0
	fprintf(dump_file, "\nPreds: ");
	fflush(dump_file);
	print_set_integers(preds);
	fflush(dump_file);
	#endif

	return preds;
}

GPBSet get_bb_succ(basic_block bb, struct cgraph_node *cnode)
{
	GPBSet succs;
	GPBSet temp;
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	
//	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	edge e;
        edge_iterator ei;
	basic_block bt;

       	FOR_EACH_EDGE(e,ei,bb->succs)
       	{
//		fprintf(dump_file, "\nInside for loop\n");
//		fflush(dump_file);

               	bt = e->dest;

		if(bt->index == 0)
		{
			continue;
		}

//		fprintf(dump_file,"\nCFG-pred %d\n", bt->index);
//		fflush(dump_file);

//		temp = ((block_information *)(bt->aux))->sblocks;	
		temp = BB_START[cnode_num][bt->index];

		succs.insert(temp.begin(), temp.end());	
	}

	#if 0
	fprintf(dump_file, "\nSuccs: ");
//	fflush(dump_file);
	print_set_integers(succs);
//	fflush(dump_file);
	#endif

	return succs;
}

std::pair< GPBSet, GPBSet> GPG::set_pred_succ(basic_block bb, struct cgraph_node *cnode)
{
	GPBSet preds, succs;

//	struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

//	fprintf(dump_file,"\nInside set_red_preds_succs\n");
//	fflush(dump_file);

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

//	map< unsigned int, set< GPB* > > ori_red_map = ((function_info *)(cnode->aux))->ori_red_map;
	GPBSet temp;

	set< unsigned int > tmp1, tmp2;

	tmp1 = ((block_information *)(bb->aux))->pred_rel;

	tmp2 = ((block_information *)(bb->aux))->pred_with_back_edge_rel;

	tmp1.insert(tmp2.begin(), tmp2.end());

	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	basic_block bt, bs;	
	GPB gpb;

	for(set< unsigned int >::iterator it = tmp1.begin(); it != tmp1.end(); it++)
	{
		bt = BASIC_BLOCK(*it);

		if(((block_information *)(bt->aux))->call_block)
		{
//			temp = ori_red_map[caller_rep][bt->index];

			for(GPBSet::iterator bit = temp.begin(); bit != temp.end(); bit++)
			{
				gpb = gpb_map[*bit];

				if(gpb.getType() == 3)
				{
					preds.insert(*bit);
					break;
				}		
			}
		}
		else
		{
//		        preds.insert(ori_red_map[caller_rep][bt->index].begin(), ori_red_map[caller_rep][bt->index].end());
		}
	}

	tmp1 = ((block_information *)(bb->aux))->succ_rel;

	tmp2 = ((block_information *)(bb->aux))->succ_with_back_edge_rel;

	tmp1.insert(tmp2.begin(), tmp2.end());

	//struct function *fn = DECL_STRUCT_FUNCTION(cnode->decl);

	for(set< unsigned int >::iterator it = tmp1.begin(); it != tmp1.end(); it++)
	{
		bt = BASIC_BLOCK(*it);

		if(((block_information *)(bt->aux))->call_block)
		{
//			temp = ori_red_map[caller_rep][bt->index];

			for(GPBSet::iterator bit = temp.begin(); bit != temp.end(); bit++)
			{
				gpb = gpb_map[*bit];

				if(gpb.getType() == 3)
				{
					succs.insert(*bit);
					break;
				}		
			}
		}
		else
		{
//		        succs.insert(ori_red_map[caller_rep][bt->index].begin(), ori_red_map[caller_rep][bt->index].end());
		}
	}

	return make_pair(preds, succs);
}

bool analyze_callee_now(struct cgraph_node *callee)
{
	unsigned int callee_rep = ((function_info *)(callee->aux))->func_num;

//	fprintf(dump_file, "\nCallee to be considered for analyzing %s (%d)\n", cgraph_node_name(callee), callee_rep);
//	fflush(dump_file);

	vector< unsigned int >::iterator it; 

	if(processed_functions.find(callee_rep) == processed_functions.end())
	{
//		fprintf(dump_file, "\nNot Processed Yet\n");
//		fflush(dump_file);

		if(!is_present_in_worklist(callee_rep))
		{
//			fprintf(dump_file, "\nNot in the worklist -- Returning True\n");
//			fflush(dump_file);

			return true;
		}
		else // Identifying Recursive Call
		{
//			fprintf(dump_file, "\nAlready present in the worklist -- Returning False\n");
//			fflush(dump_file);

			return false;
		}
	}

//	fprintf(dump_file, "\nProcessed -- Returning False\n");
//	fflush(dump_file);

	// Already Processed
	return false;
}

//=================================================================================================================================================

GPG compute_gpus(basic_block bb, struct cgraph_node *cnode, GPG gpg)
{
//	FUNBEGIN();

	#if 0 
	fprintf(dump_file,"\nInside compute_gpus for %d and %s\n", bb->index, cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	GPUSet res, type_res;
	GPBSet ori_gpus;

	unsigned int gpb_id = gpg.GPB_count; 

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	it ai;
	unsigned int stmt_id;
	constraint_list & cons_list = ((block_information *)(bb->aux))->get_list();
	int length = 0; 
	int start = 0;

	set< unsigned int > f_cons_list, to_be_list;
	
	#if 1
	for(ai = cons_list.begin(); ai != cons_list.end(); ai++)
	{
		((function_info *)(cnode->aux))->num_stmts++;
		((function_info *)(cnode->aux))->num_trans_stmts++;

		if(!(*ai).get_bool())
		{
			stmt_id = (*ai).get_int();

			#if DATA_MEAS
			ori_gpus.insert(stmt_id);
			#endif

//			fprintf(dump_file, "\nUse %d %s\n", bb->index, cgraph_node_name(cnode));

//			length++;

			((function_info *)(cnode->aux))->num_nonptr_stmts++;
			((function_info *)(cnode->aux))->num_trans_nonptr_stmts++;

			res = resolve_constraint_SSA(stmt_id, bb, cnode, false);

			stmt_info_type key_t;

			for(GPUSet::iterator rit = res.begin(); rit != res.end(); rit++)
			{
				GPBSet sset;

				key_t = std::make_tuple(caller_rep, 0, *rit);

				sset = stmt_id_info[key_t];

				sset.insert(stmt_id+1);			

				stmt_id_info[key_t] = sset;
			}

			res = filterFlowInsensitiveData(res, cnode, 0);

			f_cons_list.insert(stmt_id);

//			continue;
		}
		else
		{
			stmt_id = (*ai).get_int();

			#if DATA_MEAS
			ori_gpus.insert(stmt_id);
			#endif

			if(!filter_constraint(stmt_id, bb, cnode))
			{
				length++;
			}
			else
			{
				res = resolve_constraint_SSA(stmt_id, bb, cnode, true);

				stmt_info_type key_t;
	
				for(GPUSet::iterator rit = res.begin(); rit != res.end(); rit++)
				{
					GPBSet sset;

					key_t = std::make_tuple(caller_rep, 0, *rit);

					sset = stmt_id_info[key_t];

					sset.insert(stmt_id+1);			

					stmt_id_info[key_t] = sset;
				}

				res = filterFlowInsensitiveData(res, cnode, 0);	

				f_cons_list.insert(stmt_id);
			}
		}
	}
	#endif

	#if 0
	for(set< unsigned int >::iterator it = f_cons_list.begin(); it != f_cons_list.end(); it++)
	{
		res = resolve_constraint_SSA(*it, bb, cnode, true);

		stmt_id = (*it);

		stmt_info_type key_t;

		for(GPUSet::iterator rit = res.begin(); rit != res.end(); rit++)
		{
			GPBSet sset;

			key_t = std::make_tuple(caller_rep, 0, *rit);

			sset = stmt_id_info[key_t];

			sset.insert(stmt_id+1);			

			stmt_id_info[key_t] = sset;
		}

		res = filterFlowInsensitiveData(res, cnode, 0);	
	}
	#endif

//	fprintf(dump_file, "\nLength for bb = %d and cnode = %s is %d\n", bb->index, cgraph_node_name(cnode), length);

//	length = cons_list.length();
//	length = f_cons_list.size();

//	fprintf(dump_file,"\nComputing GPUs for BB %d of Function %s, Number of Constraints %d\n", bb->index, cgraph_node_name(cnode), length);

	GPBSet in_preds = get_bb_pred(bb, cnode);
	GPBSet in_succs = get_bb_succ(bb, cnode);

	if(length == 0)
	{
//		return gpg;

		GPB gpb;
		gpb.setId(gpg.GPB_count++);
		
		gpb.setBBIndex(bb->index);

		gpb.setOrigGPUs(res);
//		gpb.setGPUs(res);
		
//		fprintf(dump_file,"\nHey Der %d\n", gpb.getBBIndex());
		
		unsigned int  x = gpg.GPB_count - 1;

		set< unsigned int > x_s;
		x_s.insert(x);
	
		BB_START[caller_rep][bb->index] = x_s;
		BB_END[caller_rep][bb->index] = x_s;

//		((block_information *)(bb->aux))->sblocks = x_s;
//		((block_information *)(bb->aux))->eblocks = x_s;

//		gpb.s_bb_block = true;
//		gpb.e_bb_block = true;

		if((start_bb_of_fn(cnode))->index == bb->index)
		{	
			gpg.setEntryGPB(x);
		}

		if((end_bb_of_fn(cnode))->index == bb->index)
		{	
			gpg.setExitGPB(x);
		}

//		fprintf(dump_file,"\nS-Block, Start %d, Length %d, BB %d, GPB %d, GPB_count %d\n", start, length, bb->index, gpb.getId(),((function_info *)(cnode->aux))->GPB_count);

//		ori_red_map[caller_rep][bb->index].insert(x);

		gpg.gpb_map[x] = gpb;

		gpg.addGPB(x, in_preds, in_succs, cnode);

//		fprintf(dump_file, "\nHey Der 1\n");
	}

	GPB prev_gpb;
	bool use;

	for(ai = cons_list.begin(); ai != cons_list.end(); ai++)
//	for(set< unsigned int >::iterator fit = f_cons_list.begin(); fit != f_cons_list.end(); fit++)
	{
		GPB gpb;

		set< unsigned int > x_s, x_e;

//		stmt_id = *fit;
		stmt_id = (*ai).get_int();
		use = (*ai).get_bool();

		if(f_cons_list.find(stmt_id) != f_cons_list.end())
		{
			continue;
		}

		#if 0
		if(use)
		{ 
			fprintf(dump_file,"\nPrinting Constraint\n");
			print_constraint(VEC_index(constraint_t, aliases, stmt_id));
		}
		#endif

//		fprintf(dump_file,"\nBefore resolve_constraint_SSA\n");

		res = resolve_constraint_SSA(stmt_id, bb, cnode, use);

		computeDefRefForGPUSet(cnode, res, true);

		#if 0
		fprintf(dump_file, "\nGPUs after SSA resolution for basic block %d function %s\n", bb->index, cgraph_node_name(cnode));
		printSetOfGPUs(res);
		#endif

//		collectTypeInfoForGPUSet(cnode, res, true);
//		recordDataDependenceForGPUSet(res);

//		fprintf(dump_file,"\nAfter resolve_constraint_SSA\n");

		#if 0
		if(res.empty())
		{
			continue;
		}
		#endif

		GPBSet set_temp;

		#if 0
		fprintf(dump_file,"\n Printing Constraint\n");	
		print_constraint(VEC_index(constraint_t, aliases, stmt_id));
		fprintf(dump_file,"\n Printing Corresponding GPUs\n");	
		printSetOfGPUs(res);
		fprintf(dump_file,"\nAfter resolve_constraint_SSA\n");
		#endif

		gpb.setId(gpg.GPB_count++);
		
		gpb.setBBIndex(bb->index);

		unsigned int x = gpg.GPB_count - 1;
		
		stmt_info_type key_t;

		for(GPUSet::iterator rit = res.begin(); rit != res.end(); rit++)
		{
			GPBSet sset;

			key_t = std::make_tuple(caller_rep, x, *rit);

			sset = stmt_id_info[key_t];

			sset.insert(stmt_id+1);			

			stmt_id_info[key_t] = sset;
		}	
	
		res = filterFlowInsensitiveData(res, cnode, x);

		gpb.setOrigGPUs(res);

//		gpb.setGPUs(res);

//		fprintf(dump_file,"\nHey Der %d\n", gpb.getBBIndex());

		if(start == 0 && length == 1)
		{
//			fprintf(dump_file,"\nS-Block, Start %d, Length %d, BB %d, GPB %d, GPB_count %d\n", start, length, bb->index, gpb.getId(), ((function_info *)(cnode->aux))->GPB_count);

			x_s.insert(x);

			BB_START[caller_rep][bb->index] = x_s;
			BB_END[caller_rep][bb->index] = x_s;

//			((block_information *)(bb->aux))->sblocks = x_s;
//			((block_information *)(bb->aux))->eblocks = x_s;

//			gpb.s_bb_block = true;
//			gpb.e_bb_block = true;

			if((start_bb_of_fn(cnode))->index == bb->index)
			{	
				gpg.setEntryGPB(x);
			}

			if((end_bb_of_fn(cnode))->index == bb->index)
			{	
				gpg.setExitGPB(x);
			}

			gpg.addGPB(x, in_preds, in_succs, cnode);
//			fprintf(dump_file,"\nS-Block, Start %d, Length %d, BB %d, GPB %d, GPB_count %d\n", start, length, bb->index, gpb.getId(), GPB_count);
		}
		else if(start+1 == length)
		{
			x_e.insert(x);

			BB_END[caller_rep][bb->index] = x_e;
//			((block_information *)(bb->aux))->eblocks = x_e;

//			gpb.e_bb_block = true;

//			gpb->setNext(get_bb_succ(bb, cnode));
//			fprintf(dump_file,"\nE-Block, Start %d, Length %d, BB %d, GPB %d, GPB_count %d\n", start, length, bb->index, gpb.getId(), ((function_info *)(cnode->aux))->GPB_count);
//			fprintf(dump_file,"\nCalling get_bb_succ\n");
			
			set_temp.insert(prev_gpb.getId());

//			fprintf(dump_file, "\nPred %d\n", prev_gpb.getId());

			if((end_bb_of_fn(cnode))->index == bb->index)
			{	
				gpg.setExitGPB(x);
			}

			gpg.addGPB(x, set_temp, in_succs, cnode);
		}
		else if(start == 0)
		{
			x_s.insert(x);

			BB_START[caller_rep][bb->index] = x_s;

//			((block_information *)(bb->aux))->sblocks = x_s;

//			gpb.s_bb_block = true;

			if((start_bb_of_fn(cnode))->index == bb->index)
			{	
				gpg.setEntryGPB(x);
			}

			GPBSet temp_succs;
			gpg.addGPB(x, in_preds, temp_succs, cnode);

//			fprintf(dump_file,"\nS-Block, Start %d, Length %d, BB %d, GPB %d, GPB_count %d\n", start, length, bb->index, gpb.getId(), ((function_info *)(cnode->aux))->GPB_count);
		}
		else
		{
			set_temp.insert(prev_gpb.getId());
//			gpb.setNext(get_bb_succ(bb, cnode));
//			fprintf(dump_file, "\nPred %d\n", prev_gpb.getId());

			GPBSet temp_succs;
			gpg.addGPB(x, set_temp, temp_succs, cnode);

//			fprintf(dump_file,"\nStart %d, Length %d, BB %d, GPB %d, GPB_count %d\n", start, length, bb->index, gpb.getId(), ((function_info *)(cnode->aux))->GPB_count);
		}
		
		start++;

		prev_gpb = gpb;

//		ori_red_map[caller_rep][bb->index].insert(x);

		gpg.gpb_map[x] = gpb;

//		fprintf(dump_file, "\nHey Der 2\n");
	}

//	fprintf(dump_file, "\nHyaaa\n");
//	fflush(dump_file);

	OriginalGPUs[caller_rep] = ori_gpus;

	return gpg;
}

bool is_present_in_worklist(unsigned int x)
{
	if(find(func_worklist.begin(), func_worklist.end(), x) != func_worklist.end())
		return true;

	return false;
}

void print_worklist()
{
	struct cgraph_node *cnode;

	fprintf(dump_file,"\nPrinting Worklist\n");

	for(list< unsigned int >::iterator it = func_worklist.begin(); it != func_worklist.end(); it++)
	{
		cnode = func_numbering[*it];
//		fprintf(dump_file,"\nPW1\n");

		fprintf(dump_file,"%s\t", cgraph_node_name(cnode));
//		fprintf(dump_file,"\nPW2\n");
	}

	fprintf(dump_file,"\n\n");
//	fprintf(dump_file,"\nEnd of Printing Worklist\n");
}

bool single_entry_loop(edge_type e, struct cgraph_node *cnode)
{
//	if(isDomPDom(get<0>(e), get<1>(e), cnode))
	{
		return true;
	}

	return false;
}

GPG normalize_cfg(struct cgraph_node *cnode)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	#if 0
	fprintf(dump_file,"\nInside normalize_cfg for Function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	basic_block bb;

	GPG gpg;	

	set< unsigned int > unreachable_bb = ((function_info *)(cnode->aux))->unreachable_bb;

//	map< unsigned int, set< GPB* > > ori_red_map = ((function_info *)(cnode->aux))->ori_red_map;

//	fprintf(dump_file,"\nIntermmediate normalize_cfg\n");
//	fflush(dump_file);

	FOR_EACH_BB(bb) 
	{
		#if 0
		fflush(dump_file);
//		fprintf(dump_file,"\nnormalize_cfg BB\n");
		fprintf(dump_file,"\nnormalize_cfg BB %d\n", bb->index);
		fflush(dump_file);
		#endif

		set< unsigned int > x_s, x_e;

		#if OPTIMIZE
		if(unreachable_bb.find(bb->index) != unreachable_bb.end())
		{
			continue;
		}
		#endif

		#if 0
		fflush(dump_file);
		fprintf(dump_file,"\nnormalize_cfg BB %d\n", bb->index);
		fflush(dump_file);
		#endif

//		fprintf(dump_file, "\nWhats wrong\n");
//		fflush(dump_file);

		if(((block_information *)(bb->aux))->call_block)
		{
			#if 0
			fprintf(dump_file,"\nA call block\n");
			fflush(dump_file);
			#endif

			gimple stmt = bb_call_stmt(bb);
			tree decl = get_called_fn_decl(stmt);

			if(TREE_CODE(decl) == FUNCTION_DECL)
//			if(!is_function_pointer(decl)) // Direct Call Block
			{
				struct cgraph_node *callee = cgraph_get_node(decl);

//				fprintf(dump_file, "\nDirect Call Block\n");

				if(!callee)
					continue;

				GPB gpb;
				gpb.setId(gpg.GPB_count++);
				gpb.setBBIndex(bb->index);

				#if 0
				if(identifyExitFunctionCnode(callee))
				{
					gpb.setExitCallBlock();
				}
				else
				#endif
				{
					gpb.setCallBlock();
					gpb.setCallee(((function_info *)(callee->aux))->func_num);
				}

				unsigned int x = gpg.GPB_count - 1;

//				fprintf(dump_file, "\nInserting GPB %d\n", x);

				x_s.insert(x);
//				x_e.insert(x);

				BB_START[caller_rep][bb->index] = x_s;
				BB_END[caller_rep][bb->index] = x_s;

//				((block_information *)(bb->aux))->sblocks = x_s;
//				((block_information *)(bb->aux))->eblocks = x_s;

//				gpb.s_bb_block = true;
//				gpb.e_bb_block = true;

//				gpb->setType(3);

				if((start_bb_of_fn(cnode))->index == bb->index)
				{
					gpg.setEntryGPB(x);
				}

				if((end_bb_of_fn(cnode))->index == bb->index)
				{
					gpg.setExitGPB(x);
				}

//				fprintf(dump_file, "\nHAHAHA\n");
				GPBSet preds = get_bb_pred(bb, cnode);			
				GPBSet succs = get_bb_succ(bb, cnode);			

				#if 0
				if(!identifyExitFunctionCnode(callee))
				{
					GPBSet succs = get_bb_succ(bb, cnode);			
				}
				#endif
	
//				ori_red_map[caller_rep][bb->index].insert(x);

				gpg.gpb_map[x] = gpb;

				gpg.addGPB(x, preds, succs, cnode);

				#if 0
//				if(!identifyExitFunctionCnode(callee))
				{
					if(analyze_callee_now(callee))
					{
						perform_analysis(callee);
					}
				}
				#endif
			}
			else // Indirect Call Block
			{
//				fprintf(dump_file,"\nIndirect Call Heya\n");
//				fflush(dump_file);

				#if 0 //NEW_APP
				GPB gpb;
				gpb.setId(gpg.GPB_count++);
				gpb.setBBIndex(bb->index);

				unsigned int x = gpg.GPB_count - 1;

//				fprintf(dump_file, "\nInserting GPB %d\n", x);

				x_s.insert(x);
//				x_e.insert(x);

				BB_START[caller_rep][bb->index] = x_s;
				BB_END[caller_rep][bb->index] = x_s;

				if((start_bb_of_fn(cnode))->index == bb->index)
				{
					gpg.setEntryGPB(x);
				}

				if((end_bb_of_fn(cnode))->index == bb->index)
				{
					gpg.setExitGPB(x);
				}

//				fprintf(dump_file, "\nHAHAHA\n");
				GPBSet preds = get_bb_pred(bb, cnode);			
				GPBSet succs = get_bb_succ(bb, cnode);			

				gpg.gpb_map[x] = gpb;

				gpg.addGPB(x, preds, succs, cnode);

				continue;
				#endif

				tree decl2 = SSA_NAME_VAR(decl);
				unsigned int fp_var = cs_get_vi_for_tree (decl, bb, cnode)->id;
				unsigned int fp_var_ssa = cs_get_vi_for_tree (decl2, bb, cnode)->id;

				Prototype obj;

//				obj = fp_details[fp_var_ssa];	
				obj = compute_Prototype(TREE_TYPE(decl2));

				#if 0
				fprintf(dump_file, "\nFP %s (%d) and its prototype\n", get_var_name(fp_var), fp_var);
				fprintf(dump_file, "\nFP %s (%d) and its prototype\n", get_var_name(fp_var_ssa), fp_var_ssa);
				obj.print();
				#endif

				definitions indirect_callees = resolve_fp_ssa(fp_var, bb, cnode);

				set< unsigned int > in_preds, in_succs, resolved_callees;
				definitions unresolved_callees;
				IndirectionList list;

				in_preds = get_bb_pred(bb, cnode);
				in_succs = get_bb_succ(bb, cnode);

				for(definitions::iterator it = indirect_callees.begin(); it != indirect_callees.end(); it++)
				{
					Node nt = getNode(*it);
					list = nt.getList();

					if(list.Length() == 0)
					{
						csvarinfo_t vi = cs_get_varinfo (get<0>(*it));
						tree decl;

						if(vi)
						{
							decl = vi->decl;

							if (TREE_CODE (decl) == FUNCTION_DECL) 
							{
								struct cgraph_node *callee = cgraph_get_node(decl);

								resolved_callees.insert(((function_info *)(callee->aux))->func_num);
							}
							else
							{
								unresolved_callees.insert(*it);
							}	
						}
						else
						{
							unresolved_callees.insert(*it);
						}	
					}
					else
					{
						unresolved_callees.insert(*it);
					}
				}

				if(!unresolved_callees.empty())
				{
					GPB gpb;

					gpb.setId(gpg.GPB_count++);
					unsigned int x = gpg.GPB_count - 1;

					x_s.insert(x);
					
					BB_START[caller_rep][bb->index] = x_s;
					BB_END[caller_rep][bb->index] = x_s;

//					((block_information *)(bb->aux))->sblocks = x_s;
//					((block_information *)(bb->aux))->eblocks = x_s;

//					gpb.s_bb_block = true;
//					gpb.e_bb_block = true;

					if((start_bb_of_fn(cnode))->index == bb->index)
					{	
						gpg.setEntryGPB(x);
					}

					if((end_bb_of_fn(cnode))->index == bb->index)
					{	
						gpg.setExitGPB(x);
					}

					gpb.setBBIndex(bb->index);
					gpb.setIndirectCallBlock();
					gpb.setIndirectCallees(unresolved_callees);

					#if FP
					definitions r_temp;
					r_temp = incompleteCallees[caller_rep];
					r_temp.insert(unresolved_callees.begin(), unresolved_callees.end());	
					incompleteCallees[caller_rep] = r_temp; 
					#endif

//					gpb->setType(3);

//					ori_red_map[caller_rep][bb->index].insert(x);

					gpb.proto = obj;

					gpg.gpb_map[x] = gpb;

					gpg.addGPB(x, in_preds, in_succs, cnode);
				}	

				for(set< unsigned int >::iterator rit = resolved_callees.begin(); rit != resolved_callees.end(); rit++)
				{
					GPB gpb;
					gpb.setId(gpg.GPB_count++);
					gpb.setBBIndex(bb->index);
					gpb.setCallBlock();
					gpb.setCallee(*rit);
					unsigned int x = gpg.GPB_count - 1;

					GPBSet tmp = BB_START[caller_rep][bb->index];
					tmp.insert(x);
					BB_START[caller_rep][bb->index] = tmp;

					tmp = BB_END[caller_rep][bb->index];
					tmp.insert(x);
					BB_END[caller_rep][bb->index] = tmp;

//					((block_information *)(bb->aux))->sblocks.insert(x);
//					((block_information *)(bb->aux))->eblocks.insert(x);

					if((start_bb_of_fn(cnode))->index == bb->index)
					{
						gpg.setEntryGPB(x);
					}

					if((end_bb_of_fn(cnode))->index == bb->index)
					{
						gpg.setExitGPB(x);
					}

//					fprintf(dump_file, "\nHAHAHA\n");

//					gpb.setNext(get_bb_succ(bb, cnode));			
	
//					ori_red_map[caller_rep][bb->index].insert(x);

					gpg.gpb_map[x] = gpb;

					gpg.addGPB(x, in_preds, in_succs, cnode);

					struct cgraph_node *cl;
					cl = func_numbering[*rit];

					#if 0
					if(analyze_callee_now(cl))
					{
						perform_analysis(cl);
					}
					#endif
				}
			}
		}
		else
		{
//			fprintf(dump_file,"\nNot a call block %d and %s\n", bb->index, cgraph_node_name(cnode));
//			fflush(dump_file);

			gpg = compute_gpus(bb, cnode, gpg);

//			fprintf(dump_file,"\nAfter compute_gpus %d and %s\n", bb->index, cgraph_node_name(cnode));
//			fflush(dump_file);
		}

//		fprintf(dump_file, "\nDer now\n");
//		fflush(dump_file);
	}	

	GPB exit_gpb;
	
	bb = end_bb_of_fn(cnode);
	GPBSet temp_pred = get_bb_pred(bb, cnode);

	#if 0
	fprintf(dump_file,"\n Exit BB %d %d\n", bb->index, ((function_info *)(cnode->aux))->GPB_count);
	fprintf(dump_file, "\nSet of Preds\n");
	print_set_integers(temp_pred);
	#endif

//	fprintf(dump_file,"\n Exit BB %d %d\n", bb->index, ((function_info *)(cnode->aux))->GPB_count);

	exit_gpb.setId(gpg.GPB_count++);
	exit_gpb.setBBIndex(bb->index);	
	unsigned int x = gpg.GPB_count - 1;

	set< unsigned int > x_s;
	x_s.insert(x);

	BB_START[caller_rep][bb->index] = x_s;
	BB_END[caller_rep][bb->index] = x_s;

	gpg.gpb_map[x] = exit_gpb;
	GPBSet temp_succ;
	gpg.addGPB(x, temp_pred, temp_succ, cnode);
	gpg.setExitGPB(x);

	#if 0
	fflush(dump_file);
	fprintf(dump_file,"\nNormalized R-CFG for procedure %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	gpg.printGPG(cnode);
	fflush(dump_file);

	fprintf(dump_file,"\nInitial GPG of Function %s, GPB Count = %d\n", cgraph_node_name(cnode), gpg.GPB_count);
	gpg.printInitialGPG(cnode);
	#endif

	#if PROFILING
	RETURN(gpg);
	#else	
	return gpg;
	#endif
}

void GPG::partial_analysis(struct cgraph_node *cnode, unsigned int callee)
{
	((function_info *)(cnode->aux))->count++;

	unsigned int num = ((function_info *)(cnode->aux))->func_num;

	func_worklist.push_front(num);

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	handlingSelectiveCalls(cnode, callee);

	#if 0
	fprintf(dump_file, "\nHey\nGPG after inlining call");
	printGPG(cnode);
	#endif

	localOptimizations(cnode, true);

//	sanitize(cnode, true);

	initialize_GPB_worklist(cnode);

//	fprintf(dump_file, "\nAnalyzing Function %s\n", cgraph_node_name(cnode));

	analyzeGPG(cnode, true);

	optimizeGPG(cnode, false);

//	sanitize(cnode, false);

	optimized_GPG_map[num] = *this;

//	fprintf(dump_file, "\nAgain optimized GPG of Function %s\n", cgraph_node_name(cnode));
//	printGPG(cnode);

//	generateDotFileForGPG(cnode, false, "opt");

	if(((function_info *)(cnode->aux))->count == 1)
	{
		deltaGPG_map[num] = optimized_GPG_map[num];
	}

	if(areCallBlocksPresentForRecursion(cnode))
	{
		bool recur;
		recur = processingRecursion(cnode);

		optimized_GPG_map[num] = *this;

//		fprintf(dump_file, "\nAgain optimized GPG of Function %s\n", cgraph_node_name(cnode));
//		printGPG(cnode);
	}

	pop_cfun();

	unsigned int fin_node = func_worklist.front();

	if(fin_node == num)
	{
		func_worklist.pop_front();
	}

//	fprintf(dump_file, "\nOptimized, now calling callers\n");

	after_recursion(cnode);
}

void GPG::computePointstoGPG(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	if(isTop())
	{
		return;
	}

	unsigned int current_node_id;
	GPB current_node;

	//bool isPointstoEdge(gpu_id_type gpu)

	while(!(Function_Worklist[cnode_num].empty()))
	{
		GPBList list_temp = Function_Worklist[cnode_num];

		current_node_id = list_temp.front();
		current_node = gpb_map[current_node_id];
		list_temp.pop_front();

		Function_Worklist[cnode_num] = list_temp;

		computePointstoGPB(current_node_id, cnode);
	}

	#if 0
	fprintf(dump_file, "\nGPG of function %s after analyses\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif

	GPUSet array_data, ptsout, new_array_data;
	unsigned int exit;

	exit = getExitGPB();
	ptsout = PTSOUT[exit];
	array_data = flowInsensitiveInformation[cnode_num];

	new_array_data = RGen(ptsout, array_data, cnode, 0);

	flowInsensitiveInformation[cnode_num] = new_array_data;
}

void perform_analysis_d(struct cgraph_node *cnode)
{
	unsigned int cnode_rep = ((function_info *)(cnode->aux))->func_num;

	#if PRINT_DATA
        fprintf(dump_file,"\n=========================DFV Pass %s  Order %d ==============================\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num);
        #endif

	#if OPTIMIZE
	basic_block start_bb = start_bb_of_fn(cnode);
	set< unsigned int > unreachable_bb = ((function_info *)(cnode->aux))->unreachable_bb;

	if(unreachable_bb.find(start_bb->index) != unreachable_bb.end())
	{
		return;
	}
	#endif	

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

//	fprintf(dump_file, "\nComputing Poinst-to Information for function %s (%d)\n", cgraph_node_name(cnode), cnode_rep);

	GPG g = optimized_GPG_map[cnode_rep];

//	g.printGPG(cnode);

	if(!g.isTop())
	{
//		fprintf(dump_file, "\nPTS - Optimized GPG for function %s\n", cgraph_node_name(cnode));
//		g.printGPG(cnode);

		g.initialize_GPB_worklist(cnode);

		g.computePointstoGPG(cnode);
	}

	pop_cfun();
}

void GPG::analyzeCallees(struct cgraph_node *caller)
{
	unsigned int caller_rep, callee_rep;
	struct cgraph_node *callee;

	caller_rep = ((function_info *)(caller->aux))->func_num;

	GPBSet gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock())
		{
			callee_rep = gpb.getCallee();

			callee = func_numbering[callee_rep];

			if(analyze_callee_now(callee))
			{
				perform_analysis(callee);
			}
		}
	}

	return;
}

void performAnalysis(struct cgraph_node *cnode)
{
	((function_info *)(cnode->aux))->count++;

	unsigned int cnode_rep = ((function_info *)(cnode->aux))->func_num;

	func_worklist.push_front(cnode_rep);

	#if PRINT_DATA
        fprintf(dump_file,"\n=========================Points-to Pass %s  Order %d ==============================\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num);
        #endif

	set<unsigned int> pars = ((function_info *)(cnode->aux))->get_params();

//	fprintf(dump_file, "\nParameters of function %s\n", cgraph_node_name(cnode)); 
//	fflush(dump_file);
//	print_set_integers(pars);
//	fflush(dump_file);

	#ifndef MRB
	unsigned int ret_id = ((function_info *)(cnode->aux))->get_ret_id();
	#endif
	#ifdef MRB
	set< unsigned int > ret_id = ((function_info *)(cnode->aux))->get_ret_id();
	#endif

//	fprintf(dump_file, "\nReturn ID for Function %s\n", cgraph_node_name(cnode));
//	fflush(dump_file);

	#ifndef MRB
//	fprintf(dump_file, "\nRet = %d\n", ret_id);	
//	fflush(dump_file);
	#endif
	#ifdef MRB
//	print_set_integers(ret_id);
//	fflush(dump_file);
	#endif

	basic_block start_bb = start_bb_of_fn(cnode);
	set< unsigned int > unreachable_bb = ((function_info *)(cnode->aux))->unreachable_bb;

	#if OPTIMIZE
	if(unreachable_bb.find(start_bb->index) != unreachable_bb.end())
	{
		return;
	}
	#endif	

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	boundary_nodes.clear();

	GPG g;

	unsigned int num = ((function_info *)(cnode->aux))->func_num;

	g = GPG_map[num];

	g.analyzeCallees(cnode);

	g.reachability(cnode);

	g.handlingCalls(cnode);

	#if 0
	fprintf(dump_file, "\nStatistics for Function %s\n", cgraph_node_name(cnode));	
	PRINT_PROFILE_STATS();
	#endif

	g.localOptimizations(cnode, true);

//	g.sanitize(cnode, true);

//	g.generateDotFileForGPG(cnode, true, "allcalls");

//	fprintf(dump_file, "\nGPG after inlining calls in GPG for function %s\n", cgraph_node_name(cnode));
//	g.printInitialGPG(cnode);

	#if 0
	if(g.returnNumberOfIndirectCallBlocks(cnode) != 0 || g.returnNumberOfIntervals(cnode) != 0)
	{
		fprintf(dump_file, "\nCreating Intervals\n");
		fflush(dump_file);
		g.createIntervals(cnode);
	}
	else
	{
		fprintf(dump_file, "\nNo Intervals\n");
		fflush(dump_file);
	}

	fprintf(dump_file, "\nGPG after creating intervals in GPG for function %s\n", cgraph_node_name(cnode));
	g.printInitialGPG(cnode);

	g.sanitize(cnode, true);

	g.generateDotFileForGPG(cnode, true);
	#endif

	GPG_map[num] = g;

	if(main_cnode->uid != cnode->uid)
	{
		g.insertBoundaryDefinitions(cnode);
	}

	g.initialize_GPB_worklist(cnode);

	g.analyzeGPG(cnode, false);

//	fprintf(dump_file, "\nGPG after analyses for function %s\n", cgraph_node_name(cnode));
//	g.printGPG(cnode);

//	g.generateDotFileForGPG(cnode, false, "anal");

//	generateDotFile(cnode);
//	generateDotFileForInitialGPG(cnode);

	g.optimizeGPG(cnode, false);

//	g.sanitize(cnode, false);

	optimized_GPG_map[num] = g;

//	fprintf(dump_file, "\nOptimized GPG in perform_analysis for Function %s\n", cgraph_node_name(cnode));
//	optimized_GPG_map[num].printGPG(cnode);

//	g.generateDotFileForGPG(cnode, false, "opt");

	#if 0
	if(g.returnNumberOfIndirectCallBlocks(cnode) != 0 || g.returnNumberOfIntervals(cnode) != 0)
	{
		g.createIntervals(cnode);

		g.sanitize(cnode, false);

		fprintf(dump_file, "\nAnother round of creating intervals in GPG for function %s\n", cgraph_node_name(cnode));
		g.printGPG(cnode);

		optimized_GPG_map[num] = g;

		g.generateDotFileForGPG(cnode, false);
	}
	#endif
		
	if(((function_info *)(cnode->aux))->count == 1)
	{
		deltaGPG_map[num] = optimized_GPG_map[num];
	}

//	fprintf(dump_file, "\nBefore checking for recursion\n");
//	fflush(dump_file);

	if(g.areCallBlocksPresentForRecursion(cnode))
	{
//		fprintf(dump_file, "\nHandling Recursion\n");

		bool recur;
		recur = g.processingRecursion(cnode);

		g.optimizeGPG(cnode, false);

		optimized_GPG_map[num] = g;

//		fprintf(dump_file, "\nResolving Recursive Calls for function %s\n", cgraph_node_name(cnode));
//		g.printGPG(cnode);

//		g.generateDotFileForGPG(cnode, false, "opt");
	}

//	fprintf(dump_file, "\nBefore inserting %s (%d) in processed_functions\n", cgraph_node_name(cnode), num);
//	fflush(dump_file);

	processed_functions.insert(num);

//	fprintf(dump_file, "\nAfter inserting %s (%d) in processed_functions\n", cgraph_node_name(cnode), num);
//	fflush(dump_file);

	#if 0
	fprintf(dump_file, "\nProcessed Function so far\n");
	fflush(dump_file);
	for(GPBSet::iterator it = processed_functions.begin(); it != processed_functions.end(); it++)
	{
		fprintf(dump_file, "\nProcessed Function %s (%d)\n", cgraph_node_name(func_numbering[*it]), *it);
		fflush(dump_file);
	}
	#endif

//	((function_info *)(cnode->aux))->fixed_pt = true;

	pop_cfun();

	unsigned int fin_node = func_worklist.front();

	if(fin_node == cnode_rep)
	{
		func_worklist.pop_front();
	}

	#if PRINT_DATA
        fprintf(dump_file,"\n=========================End of Points-to Pass %s  Order %d ==============================\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num);
        #endif

	g.after_recursion(cnode);
}

void GPG::post_processing(struct cgraph_node *cnode)
{
	GPBSet gpbs = getGPBs();
	GPB gpb;

	bool go_back = true;
	bool symgpb_present = false;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nInside post_processing of Function %s\n", cgraph_node_name(cnode));
	#endif

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isSymGPB())
		{
			symgpb_present = true;
	
			if(!gpb.isResolved())
			{
				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nOne of the SymGPBs %d is still not resolved completely for Function %s\n", *it, cgraph_node_name(cnode));
				#endif

				go_back = false;

				break;
			}
		}
	}

	struct cgraph_node *node;
	unsigned int callee, new_func;
	GPUSet temp;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\ngo_back = %d and symgpb_present = %d for Function %s\n", go_back, symgpb_present, cgraph_node_name(cnode));
	#endif

	GPBSet callees;

	if(go_back && symgpb_present)
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGoing Back and Calling enhanceGPG for Function %s\n", cgraph_node_name(cnode));
		#endif

		for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
		{
			gpb = gpb_map[*it];

			if(gpb.isSymGPB())
			{
				callees = gpb.getSetOfCallees();		

				#if DATA_MEAS
				fprintf(dump_file, "\nCall Chain Analyzed in Top_Down Manner of Size %d\n", callees.size()+1);
				#endif

				for(map< unsigned int, unsigned int >::reverse_iterator rit = REV_DFS_ORDER.rbegin(); rit != REV_DFS_ORDER.rend(); rit++) // Analyzing procedures in reverse post order
				{
					if(callees.find(rit->second) != callees.end())
					{
						node = func_numbering[rit->second];

						enhanceGPG(node, RIN[*it], BRIN[*it]);
					}
				}
			}
		}

		GPUSet empty;

		enhanceGPG(cnode, empty, empty);
	}
	

	#if 0
	if(go_back && symgpb_present)
	{
		while(!partial_func_worklist.empty())
		{
			GPUSet bi;

			new_func = partial_func_worklist.front();
			partial_func_worklist.pop_front();

			node = func_numbering[new_func];

			bi = BI[cnode_num][new_func];

			for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
			{
				gpb = gpb_map[*it];

				if(gpb.isSymGPB())
				{
					#if PRINT_DATA
					fprintf(dump_file, "\nGPB %d of Function %s\nRIN: ", *it, cgraph_node_name(cnode));
					printSetOfGPUs(RIN[*it]);
					fprintf(dump_file, "\nRGen: ");
					printSetOfGPUs(gpb.getGPUs());
					#endif	

					temp = RIN[*it];

//					temp = gpb.getGPUs();

					bi.insert(temp.begin(), temp.end());
				}
			}

			enhanceGPG(node, bi);
		}
	}
	#endif
}

void enhanceGPG(struct cgraph_node *cnode, GPUSet rin, GPUSet brin)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	#if 0 //PRINT_DATA
	unsigned int count = enhanceCount[cnode_num];
	count++;
	enhanceCount[cnode_num] = count;

	fprintf(dump_file, "\nEnhance Count for Function %s is %d\n", cgraph_node_name(cnode), count);
	fflush(dump_file);
	#endif

	#if DATA_MEAS
	fprintf(dump_file, "\nEnhanced GPG of Function %s\n", cgraph_node_name(cnode));
	#endif

	GPG g = partial_optimized_GPG_map[cnode_num];

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nInside enhanceGPG for Function %s with BI\n", cgraph_node_name(cnode));

	#if BLOCKING
	printSetOfGPUs(brin);
	#else
	printSetOfGPUs(rin);
	#endif

	fprintf(dump_file, "\nPartially Optimized GPG\n");
	g.printGPG(cnode);
	#endif

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	if(sym_gpgs.find(cnode_num) != sym_gpgs.end())
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nSymGPG introduced for function %s\n", cgraph_node_name(cnode));
		#endif

		g.initialize_GPB_worklist(cnode);

		#if BLOCKING
		g.analyzeGPGWithBI(cnode, false, brin);
		#else
		g.analyzeGPGWithBI(cnode, false, rin);
		#endif

		g.optimizeGPG(cnode, false);

		optimized_GPG_map[cnode_num] = g;
	}
	else
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nSymGPB contained in GPG for function %s\n", cgraph_node_name(cnode));
		#endif

		g.handlingSymGPBs(cnode);

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPG After handling SymGPBs for function %s\n", cgraph_node_name(cnode));
		g.printGPG(cnode);
		#endif

		g.initialize_GPB_worklist(cnode);

		GPUSet bi = BDEFS[cnode_num];

		g.analyzeGPGWithBI(cnode, false, bi);

		g.optimizeGPG(cnode, false);

		optimized_GPG_map[cnode_num] = g;
	}

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nEnhanced Optimized GPG for Function %s\n", cgraph_node_name(cnode));
	g.printGPG(cnode);
	#endif

	pop_cfun();

//	g.post_processing(cnode);
}

void perform_analysis(struct cgraph_node *cnode)
{
	((function_info *)(cnode->aux))->count++;

	unsigned int num = ((function_info *)(cnode->aux))->func_num;

	if(PROCESSING_COUNT[num] >=4)
	{
		fprintf(dump_file, "\nFunction %s processed 4 times\n", cgraph_node_name(cnode));
		fflush(dump_file);

		exit(1);
	}

	#if PRINT_DATA
        fprintf(dump_file,"\n=========================Points-to Pass %s  Order %d ==============================\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num);
        #endif

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	GPG g;

	#if FI_ANALYSIS && !CI_ANALYSIS
	flowInsensitiveContextSensitiveAnalysis(cnode);
	#else
	g = GPG_map[num];

	g.handlingCalls(cnode);
	
	#if DATA_MEAS
	Call_GPG_map[num] = g;
	#endif

//	g.computeDefRef(cnode, true);

	g.localOptimizations(cnode, true);

//	g.sanitize(cnode, true);

//	g.generateDotFileForGPG(cnode, true, "allcalls");

//	fprintf(dump_file, "\nGPG after inlining calls in GPG for function %s\n", cgraph_node_name(cnode));
//	g.printInitialGPG(cnode);

	g.initialize_GPB_worklist(cnode);

	g.analyzeGPG(cnode, false);

//	fprintf(dump_file, "\nGPG after analyses for function %s\n", cgraph_node_name(cnode));
//	g.printGPG(cnode);

//	g.generateDotFileForGPG(cnode, false, "anal");

//	g.collectTypeInfo(cnode, false);

//	g.recordDataDependence(cnode, false);

	g.optimizeGPG(cnode, false);

//	g.sanitize(cnode, false);

	optimized_GPG_map[num] = g;
	partial_optimized_GPG_map[num] = g;
	#endif

	#if PRINT_DATA
	fprintf(dump_file, "\nOptimized GPG in perform_analysis for Function %s\n", cgraph_node_name(cnode));
	optimized_GPG_map[num].printGPG(cnode);
	#endif

//	g.generateDotFileForGPG(cnode, false, "opt");

	#if !FI_ANALYSIS && !CI_ANALYSIS
	#if HEURISTICS
	g.shouldRepresentSymGPG(cnode);
	g.post_processing(cnode);
	#endif
	#endif

	processed_functions.insert(num);

	pop_cfun();

	PROCESSING_COUNT[num] += 1;

	#if PRINT_DATA
        fprintf(dump_file,"\n=========================End of Points-to Pass %s  Order %d Processing Count %d==============================\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num, PROCESSING_COUNT[num]);
        #endif

	#if PROFILING
	PRINT_PROFILE_STATS();
	#endif
}

void perform_analysis_again(struct cgraph_node *cnode)
{
	((function_info *)(cnode->aux))->count++;

	unsigned int num = ((function_info *)(cnode->aux))->func_num;

	#if PRINT_DATA
        fprintf(dump_file,"\n=========================Points-to Pass Again %s  Order %d ==============================\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num);
        #endif

	push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

	boundary_nodes.clear();

	GPG g, g_prev;
	GPUSet rout_prev, brout_prev, rout_new, brout_new;

	#if FI_ANALYSIS && !CI_ANALYSIS
	flowInsensitiveContextSensitiveAnalysis(cnode);
	#else
	g_prev = optimized_GPG_map[num];

	unsigned int end = g_prev.getExitGPB();
	rout_prev = g_prev.ROUT[end];
	brout_prev = g_prev.BROUT[end];

	g = deltaGPG_map[num];

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\ndeltaGPG for Function %s\n", cgraph_node_name(cnode));
	g.printGPG(cnode);
	#endif

	g.handlingRecursiveCalls(cnode);

	#if 0
	g.eliminateSelectiveSelfLoops(cnode, true);
	#endif

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\ndeltaGPG after call inlining for Function %s\n", cgraph_node_name(cnode));
	g.printGPG(cnode);
	#endif

	#if DATA_MEAS
	Call_GPG_map[num] = g;
	#endif

//	g.computeDefRef(cnode, true);

//	g.localOptimizations(cnode, true);

//	g.sanitize(cnode, true);

//	g.generateDotFileForGPG(cnode, true, "allcalls");

//	fprintf(dump_file, "\nGPG after inlining calls in GPG for function %s\n", cgraph_node_name(cnode));
//	g.printInitialGPG(cnode);

//	g.initialize_GPB_worklist(cnode);

	g.analyzeGPG(cnode, true);

//	g.eliminateSelectiveSelfLoops(cnode, false);

//	fprintf(dump_file, "\nGPG after analyses for function %s\n", cgraph_node_name(cnode));
//	g.printGPG(cnode);

//	g.generateDotFileForGPG(cnode, false, "anal");

//	g.collectTypeInfo(cnode, false);

//	g.recordDataDependence(cnode, false);

//	g.computeDefRef(cnode, false);

	g.optimizeGPG(cnode, false);

//	g.sanitize(cnode, false);

	optimized_GPG_map[num] = g;
	partial_optimized_GPG_map[num] = g;

	#if PRINT_DATA
	fprintf(dump_file, "\nOptimized GPG in perform_analysis_again for Function %s\n", cgraph_node_name(cnode));
	optimized_GPG_map[num].printGPG(cnode);
	#endif

	#if !FI_ANALYSIS && !CI_ANALYSIS
	#if HEURISTICS
	g.shouldRepresentSymGPG(cnode);
	g.post_processing(cnode);
	#endif
	#endif

//	g.generateDotFileForGPG(cnode, false, "opt");

	#if PRINT_DATA
        fprintf(dump_file,"\n=========================End of Points-to Pass Again %s  Order %d ==============================\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num);
        #endif

	end = g.getExitGPB();
	rout_new = g.ROUT[end];
	brout_new = g.BROUT[end];

	#if BLOCKING
	if((!(rout_new == rout_prev)) || (!(brout_new == brout_prev)))
	#else
	if((!(rout_new == rout_prev)))
	#endif
	{
//		fprintf(dump_file, "\nProcessing Callers Again in Recursion\n");

		unsigned int scc_num = func_scc_map[num];

		GPBSet funcs = SCC_MAP[scc_num];
		GPBSet leaves = leavesSCCs[scc_num];

		GPBSet caller_set = callers[num];
	
		for(GPBSet::iterator sit = caller_set.begin(); sit != caller_set.end(); sit++)
		{
			if(funcs.find(*sit) != funcs.end())
			{
				if(leaves.find(*sit) == leaves.end())
				{
					func_worklist_again.push_front(*sit);
				}
			}
		}
	}
	#endif

	pop_cfun();
}

void print_constraint(constraint_t con)
{
	int lhs_type, rhs_type;
        int lhs_var_id, rhs_var_id;
        const char *lhs_op, *rhs_op;
        csvarinfo_t lhs, rhs;

	lhs_type = con->lhs.type;
	rhs_type = con->rhs.type;
	lhs_var_id = con->lhs.var;
	rhs_var_id = con->rhs.var;
	lhs = VEC_index(csvarinfo_t,csvarmap,lhs_var_id);
	rhs = VEC_index(csvarinfo_t,csvarmap,rhs_var_id);
	unsigned int lhs_off = con->lhs.offset;
	unsigned int rhs_off = con->rhs.offset;
	lhs_op = lhs->name;
	rhs_op = rhs->name;
	fprintf(dump_file,"\nLHS Op: %s-%d LHS type: %d LHS Offset: %d\n RHS Op: %s-%d RHS type: %d RHS Offset: %d\n",lhs_op, lhs_var_id,lhs_type,lhs_off,rhs_op,rhs_var_id,rhs_type,rhs_off);

}

GPBList interval_set;
GPBSet already_added, IntervalSet;

void GPG::makeInterval(GPBSet interval_set, struct cgraph_node *cnode, bool direct)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	unsigned int x = GPB_count++;

	GPG res;

	std::map< unsigned int, GPG > intervals = getIntervals();
	GPBSet gpbs_res, temp_set, gpbs;

	gpbs = getGPBs();

//	res.setEntryGPB(interval_set.front());
//	res.setExitGPB(interval_set.back());

	GPBSet prev, next;

	for(GPBSet::iterator it = interval_set.begin(); it != interval_set.end(); it++)
	{
		GPBSet temp1, temp2;

		temp_set = getPrev(*it);
		prev.insert(temp_set.begin(), temp_set.end());

		set_intersection(temp_set.begin(), temp_set.end(), interval_set.begin(), interval_set.end(), inserter(temp1, temp1.end())); 
		res.setPrev(*it, temp1);

		temp_set = getNext(*it);
		next.insert(temp_set.begin(), temp_set.end());

		set_intersection(temp_set.begin(), temp_set.end(), interval_set.begin(), interval_set.end(), inserter(temp2, temp2.end())); 
		res.setNext(*it, temp2);

		gpbs_res.insert(*it);
	}

	for(GPBSet::iterator it = interval_set.begin(); it != interval_set.end(); it++)
	{
		prev.erase(*it);
		next.erase(*it);

		eliminateGPB(*it, cnode);
	}

	for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
	{
		for(GPBSet::iterator sit = interval_set.begin(); sit != interval_set.end(); sit++)
		{
			if(*it == *sit)
				continue;

			res.remNext(*it, *sit);
		}
	}

	for(GPBSet::iterator it = next.begin(); it != next.end(); it++)
	{
		for(GPBSet::iterator sit = interval_set.begin(); sit != interval_set.end(); sit++)
		{
			if(*it == *sit)
				continue;

			res.remPrev(*it, *sit);
		}
	}

	res.setGPBs(gpbs_res);

	GPBSet start_gpbs, end_gpbs, new_set;
	
	for(GPBSet::iterator it = gpbs_res.begin(); it != gpbs_res.end(); it++)
	{
		temp_set = res.getPrev(*it);

		if(temp_set.empty())
		{
//			fprintf(dump_file, "\nNo Predecessor for GPB %d\n", *it);

			start_gpbs.insert(*it);
		}
		
		temp_set = res.getNext(*it);

		if(temp_set.empty())
		{
//			fprintf(dump_file, "\nNo Successor for GPB %d\n", *it);

			end_gpbs.insert(*it);
		}
	}

	if(start_gpbs.size() > 1)
	{
		GPB art_start;

		unsigned int y = res.GPB_count++;

		art_start.setId(y);
		gpb_map[y] = art_start;

		res.setNext(y, start_gpbs);

		for(GPBSet::iterator it = start_gpbs.begin(); it != start_gpbs.end(); it++)
		{
			res.addPrev(*it, y);
		}

		new_set = res.getGPBs();
		new_set.insert(y);
		res.setGPBs(new_set);
		
		res.setEntryGPB(y);
	}
	else
	{
		res.setEntryGPB(*(start_gpbs.begin()));
	}

	if(end_gpbs.size() > 1)
	{
		GPB art_end;

		unsigned int z = res.GPB_count++;

		art_end.setId(z);
		gpb_map[z] = art_end;

		res.setPrev(z, end_gpbs);

		for(GPBSet::iterator it = end_gpbs.begin(); it != end_gpbs.end(); it++)
		{
			res.addNext(*it, z);
		}

		new_set = res.getGPBs();
		new_set.insert(z);
		res.setGPBs(new_set);
		
		res.setExitGPB(z);
	}
	else
	{
		res.setExitGPB(*(end_gpbs.begin()));
	}

	#if 0
	fprintf(dump_file, "\nRes Interval\n");
	res.printGPG(cnode);
	#endif

	GPB new_gpb;

	new_gpb.setId(x);

	if(direct)
	{
		new_gpb.setIntervalDirect();
	}
	else
	{
		new_gpb.setInterval();
	}

	new_gpb.setIntervalSet(gpbs_res);
	gpb_map[x] = new_gpb;
	
	addGPB(x, prev, next, cnode);

	intervals[x] = res;

	#if 0
	fprintf(dump_file, "\nHey Interval GPG with Interval id = %d\n", x);
	res.printGPG(cnode);
	fprintf(dump_file, "\ngpbs_res for Interval %d\n", x);
	print_set_integers(gpbs_res);
	#endif

	setIntervals(intervals);
}

void GPG::addToInterval(unsigned int gpb_id, struct cgraph_node *cnode)
{
//	fprintf(dump_file, "\nInside addToInterval\n");

	if(already_added.find(gpb_id) != already_added.end())
	{
		return;
	}

//	fprintf(dump_file, "\nNot in already_added set\n");

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPB gpb = gpb_map[gpb_id];
	GPBSet preds, temp, succs;

	if(gpb.isIndirectCallBlock() || gpb.isInterval())
	{
//		fprintf(dump_file, "\n%d is an indirect GPB\n", gpb_id);

		if(IntervalSet.empty())
		{
//			fprintf(dump_file, "\nFirst GPB of Interval Set\n");

			IntervalSet.insert(gpb_id);
			already_added.insert(gpb_id);

			succs = getNext(gpb_id);

//			fprintf(dump_file, "\nSuccessors of %d\n", gpb_id);
//			print_set_integers(succs);

			for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
			{
				if(already_added.find(*it) == already_added.end())
				{
					addToInterval(*it, cnode);
				}
			}
		}
		else
		{
//			fprintf(dump_file, "\n!First GPB of Interval Set\n");

			preds = getPrev(gpb_id);

//			fprintf(dump_file, "\nPrev of %d: ", gpb_id);
//			print_set_integers(preds);

//			fprintf(dump_file, "\nInterval Set so far\n");
//			print_set_integers(IntervalSet);

			set_difference(preds.begin(), preds.end(), IntervalSet.begin(), IntervalSet.end(), inserter(temp, temp.end()));

			if(temp.empty())
			{
				IntervalSet.insert(gpb_id);
				already_added.insert(gpb_id);
	
//				fprintf(dump_file, "\nPrev of %d: ", gpb_id);
//				print_set_integers(preds);
//				fprintf(dump_file, "\nAdd %d to Interval Set\nNew Interval Set\n", gpb_id);
//				print_list_integers(interval_set);

				succs = getNext(gpb_id);

//				fprintf(dump_file, "\nSuccessors of %d\n", gpb_id);
//				print_set_integers(succs);

				for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
				{
					if(already_added.find(*it) == already_added.end())
					{
						addToInterval(*it, cnode);
					}
				}
			}
		}
	}
}

void GPG::createIntervals(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();

//	fprintf(dump_file, "\nCreating Intervals for GPG\n");
//	printGPG(cnode);

//	interval_set.clear();
	already_added.clear();		

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		IntervalSet.clear();
//		interval_set.clear();
		addToInterval(*it, cnode);

		if(IntervalSet.size() > 1)
		{
//			fprintf(dump_file, "\nInterval Set\n");
//			print_set_integers(IntervalSet);

			makeInterval(IntervalSet, cnode, false);
		}	
	}
}

void GPG::addToIntervalForDirectCalls(unsigned int gpb_id, struct cgraph_node *cnode)
{
//	fprintf(dump_file, "\nInside addToInterval\n");

	if(already_added.find(gpb_id) != already_added.end())
	{
		return;
	}

//	fprintf(dump_file, "\nNot in already_added set\n");

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPB gpb = gpb_map[gpb_id];
	GPBSet preds, temp, succs;

	if(gpb.isCallBlock())
	{
//		fprintf(dump_file, "\n%d is a call GPB\n", gpb_id);

		if(IntervalSet.empty())
		{
//			fprintf(dump_file, "\nFirst GPB of Interval Set\n");

			IntervalSet.insert(gpb_id);
			already_added.insert(gpb_id);

			succs = getNext(gpb_id);

//			fprintf(dump_file, "\nSuccessors of %d\n", gpb_id);
//			print_set_integers(succs);

			for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
			{
				if(already_added.find(*it) == already_added.end())
				{
					addToIntervalForDirectCalls(*it, cnode);
				}
			}
		}
		else
		{
//			fprintf(dump_file, "\n!First GPB of Interval Set\n");

			preds = getPrev(gpb_id);

//			fprintf(dump_file, "\nPrev of %d: ", gpb_id);
//			print_set_integers(preds);

//			fprintf(dump_file, "\nInterval Set so far\n");
//			print_set_integers(IntervalSet);

			set_difference(preds.begin(), preds.end(), IntervalSet.begin(), IntervalSet.end(), inserter(temp, temp.end()));

			if(temp.empty())
			{
				IntervalSet.insert(gpb_id);
				already_added.insert(gpb_id);
	
//				fprintf(dump_file, "\nPrev of %d: ", gpb_id);
//				print_set_integers(preds);
//				fprintf(dump_file, "\nAdd %d to Interval Set\nNew Interval Set\n", gpb_id);
//				print_list_integers(interval_set);

				succs = getNext(gpb_id);

//				fprintf(dump_file, "\nSuccessors of %d\n", gpb_id);
//				print_set_integers(succs);

				for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
				{
					if(already_added.find(*it) == already_added.end())
					{
						addToIntervalForDirectCalls(*it, cnode);
					}
				}
			}
		}
	}
}

void GPG::createIntervalsForDirectCalls(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();

//	fprintf(dump_file, "\nCreating Intervals for GPG\n");
//	printGPG(cnode);

//	interval_set.clear();
	already_added.clear();		

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		IntervalSet.clear();
//		interval_set.clear();
		addToIntervalForDirectCalls(*it, cnode);

		if(IntervalSet.size() > 1)
		{
//			fprintf(dump_file, "\nInterval Set\n");
//			print_set_integers(IntervalSet);

			makeInterval(IntervalSet, cnode, true);
		}	
	}
}



GPUSet map_args_para_call(struct cgraph_node *callee, basic_block bb, struct cgraph_node * cnode)
{
	gimple_stmt_iterator gsi;
	gimple stmt;

	int j, argoffset = 1, i;
	tree arg, par;
	GPUSet res, temp_set;
	csvarinfo_t fi;
	unsigned int stmt_id = 0;

	tree decl = callee->decl;

	if(!decl)
		return res;

//	fprintf(dump_file,"\nInside print_set_ssa_rep Callee %s\n", cgraph_node_name(callee));

	fi = cs_get_vi_for_tree (decl, bb, cnode);

	if(fi == NULL)
		return res;

	// Iterate over the statements of current_block.
	for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi)) 
	{
		stmt = gsi_stmt (gsi);
//	        print_gimple_stmt(dump_file,stmt,0,0);

		if (is_gimple_call (stmt))
		{
			for (j = 0; j < gimple_call_num_args (stmt); j++)
			{
//				fprintf(dump_file,"\nArg\n");

				arg = gimple_call_arg (stmt, j);

				VEC(ce_s, heap) *lhsc = NULL;
				VEC(ce_s, heap) *rhsc = NULL;

				if (field_must_have_pointers (arg))
				{
					csvarinfo_t cvar = cs_first_vi_for_offset (fi, argoffset);

					if(cvar == NULL)
						continue;

					par = cvar->decl;

					if(par == NULL)
						return res;

					if(field_must_have_pointers(par))
					{
//						fprintf(dump_file,"\nBoth Pointers\n");

						cs_get_constraint_for(par, &lhsc, bb, callee);
						cs_get_constraint_for(arg, &rhsc, bb, cnode);

						struct constraint_expr *c;	

						while(VEC_length(ce_s, lhsc) > 0)
						{
							c = VEC_last(ce_s, lhsc);
							struct constraint_expr *c2;

							while(VEC_length(ce_s, rhsc) > 0)
							{
								c2 = VEC_last(ce_s, rhsc);

								constraint_t con = new_constraint (*c, *c2);
						
								temp_set = resolve_constraint_SSA(stmt_id, bb, cnode, true);

								res.insert(temp_set.begin(), temp_set.end());

								VEC_pop (ce_s, rhsc);
							}

							VEC_pop (ce_s, lhsc);
						}
					}
				}		

				argoffset++;
			}

		}
	}
	
	return res;
}

void getCallSitesInfo()
{
	struct cgraph_node * cnode;
	unsigned int cnode_num;
	GPBSet call_sites;
	GPBSet callees, temp;
	call_site_info info;
	GPG g;
	edge_type e;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		cnode_num = ((function_info *)(cnode->aux))->func_num;

		g = optimized_GPG_map[cnode_num];

		call_sites = g.getCallSites();

		for(GPBSet::iterator it = call_sites.begin(); it != call_sites.end(); it++)
		{
			callees = call_site_map[cnode_num][*it];
			e = std::make_pair(cnode_num, *it);

			for(GPBSet::iterator cit = callees.begin(); cit != callees.end(); cit++)
			{
				info = CallerCallSite[*cit];
				info.insert(e);	
				CallerCallSite[*cit] = info;
			}
		}
	}
}

void GPG::checkOneMoreOptimization(unsigned int gpb_id, struct cgraph_node *cnode)
{
	if(already_added.find(gpb_id) != already_added.end())
	{
		return;
	}

	GPBSet gpbs = getGPBs();
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet prev1, prev2, next1, next2;
	GPB gpb1, gpb2;
	GPUSet gpus1, gpus2;

	gpb1 = gpb_map[gpb_id];
		
	prev1 = getPrev(gpb_id);
	next1 = getNext(gpb_id);

	gpus1 = gpb1.getGPUs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb2 = gpb_map[*it];

		prev2 = getPrev(*it);
		next2 = getNext(*it);

		gpus2 = gpb2.getGPUs();

		if(prev1 == prev2 && next1 == next2)
		{
			if(gpus1 == gpus2)
			{
				already_added.insert(gpb_id);
				already_added.insert(*it);

				IntervalSet.insert(gpb_id);
				IntervalSet.insert(*it);
			}
		}
	}
}

void GPG::performOneMoreOptimization(GPBSet interval_set, struct cgraph_node *cnode)
{
	unsigned int gpb_id = *(interval_set.begin());

	interval_set.erase(gpb_id);

	for(GPBSet::iterator it = interval_set.begin(); it != interval_set.end(); it++)
	{
		eliminateGPB(*it, cnode);
	}
}

void GPG::oneMoreOptimization(struct cgraph_node *cnode)
{
	GPBSet gpbs = getGPBs();
	GPBSet prev, next;

	already_added.clear();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		IntervalSet.clear();
		checkOneMoreOptimization(*it, cnode);

		if(IntervalSet.size() > 1)
		{
			performOneMoreOptimization(IntervalSet, cnode);
		}
	}

	return;
}

void GPG::eliminateSelfLoops(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();
	GPB gpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock())
		{
			continue;
		}

		remPrev(*it, *it);
		remNext(*it, *it);
	}
}

void GPG::eliminateSelectiveSelfLoops(struct cgraph_node *cnode, bool orig)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs = getGPBs();
	GPB gpb;
	GPUSet gpus;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock())
		{
			continue;
		}

		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

		
		if(!areAdvancingGPUs(gpus))
		{
			remPrev(*it, *it);
			remNext(*it, *it);
		}
	}
}

unsigned int GPG::returnNumberOfControlFlowEdges(struct cgraph_node *cnode)
{
	if(isTop())
	{
		return 0;
	}

	GPBSet gpbs = getGPBs();
	GPBSet succs;
	unsigned int res = 0;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		succs = getNext(*it);

		res = res + succs.size();
	}

	return res;
}

std::map< unsigned int, GPBSet > in, out;

GPBSet GPG::computeIN(unsigned int gpb_id, struct cgraph_node *cnode)
{
	GPBSet res, temp, prev;

	prev = getPrev(gpb_id);

	for(GPBSet::iterator it = prev.begin(); it != prev.end(); it++)
	{
		temp = out[*it];
		
		res.insert(temp.begin(), temp.end());
	}

	return res;
}

void GPG::eliminateEmptyGPBsDFA(struct cgraph_node *cnode, bool orig)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	GPG res;

	if(isTop())
	{
		#if PROFILING
		RETURN_VOID();
		#else
		return;
		#endif
	}

	computeBackEdges(cnode);

	edge_set backedges = getBackEdges();

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	in.clear();
	out.clear();

	GPBList worklist, pending_list;
	GPBSet already_visited;
	GPBSet gpbs = getGPBs();

	std::map< unsigned int, GPB > new_gpb_map;

	unsigned int start = getEntryGPB();
	unsigned int end = getExitGPB();

	GPBSet succs, temp;
	unsigned int current;
	GPB gpb;
	
//	Initializing the worklist

	pending_list.push_back(start);

	while(!pending_list.empty())
	{
		current = pending_list.front();

		pending_list.pop_front();

		if(find(worklist.begin(), worklist.end(), current) == worklist.end())
		{
			worklist.push_back(current);
		}

		succs = getNext(current);

		for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
		{
			if(find(worklist.begin(), worklist.end(), *it) == worklist.end())
			if(find(pending_list.begin(), pending_list.end(), *it) == pending_list.end())
			{
				pending_list.push_back(*it);
			}	
		}
	}

	#if 0
	fprintf(dump_file, "\nPrinting Worklist for DFA\n");
	print_list_integers(worklist);
	fprintf(dump_file, "\nEnd of Printing Worklist for DFA\n");
	#endif

//	Analysis begins

	GPBSet prev_out, new_out;
	GPBSet oprev, onext;

	while(!worklist.empty())
	{
		current = worklist.front();

		worklist.pop_front();

//		fprintf(dump_file, "\nCurrent Node %d\n", current);

		gpb = gpb_map[current];

		oprev = getPrev(current);
		onext = getNext(current);

		temp = computeIN(current, cnode);
		in[current] = temp;

		if(current == start || current == end) // || oprev.empty() || onext.empty())
		{
//			fprintf(dump_file, "\nStart or End Node\n");

			GPBSet temp_set;

			temp_set.insert(current);
			out[current] = temp_set;

			new_out = temp_set;

			succs = getNext(current);

			for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
			{
				if(find(worklist.begin(), worklist.end(), *sit) == worklist.end())
				{
					worklist.push_front(*sit);
				}	
			}

			#if 0
			fprintf(dump_file, "\nIN of %d\n", current);
			print_set_integers(in[current]);
			fprintf(dump_file, "\nEnd of Printing IN\n");

			fprintf(dump_file, "\nOUT of %d\n", current);
			print_set_integers(out[current]);
			fprintf(dump_file, "\nEnd of Printing OUT\n");
			#endif

			continue;
		}

		prev_out = out[current];
	
		#if 0
		bool src_backedge = false;

		for(edge_set::iterator eit = backedges.begin(); eit != backedges.end(); eit++)
		{
			if(get<0>(*eit) == current)
			{
				GPBSet temp_set;

				temp_set.insert(current);
				out[current] = temp_set;

				new_out = temp_set;

				src_backedge = true;

				break;
			}
		}

		if(src_backedge)
		{
		}
		else
		#endif 
		if(orig)
		{
			if(gpb.isInitialEmpty())
			{
//				fprintf(dump_file, "\nOrig Empty %d\n", current);

				out[current] = temp;

				new_out = temp;
			}
			else
			{
//				fprintf(dump_file, "\nOrig not Empty %d\n", current);

				GPBSet temp_set;

				temp_set.insert(current);
				out[current] = temp_set;

				new_out = temp_set;
			}
		}
		else
		{
			if(gpb.isEmpty())
			{
//				fprintf(dump_file, "\nRed Empty %d\n", current);

				out[current] = temp;

				new_out = temp;
			}
			else
			{
//				fprintf(dump_file, "\nRed not Empty %d\n", current);

				GPBSet temp_set;

				temp_set.insert(current);
				out[current] = temp_set;

				new_out = temp_set;
			}
		}

		#if 0
		fprintf(dump_file, "\nIN of %d\n", current);
		print_set_integers(in[current]);
		fprintf(dump_file, "\nEnd of Printing IN\n");

		fprintf(dump_file, "\nPrev OUT of %d\n", current);
		print_set_integers(prev_out);
		fprintf(dump_file, "\nEnd of Printing PrevOUT\n");

		fprintf(dump_file, "\nNew OUT of %d\n", current);
		print_set_integers(out[current]);
		fprintf(dump_file, "\nEnd of Printing New OUT\n");
		#endif

		if(!(prev_out == new_out))
		{
//			fprintf(dump_file, "\nChange in OUT, Pushing Succs on Worklist\n");

			succs = getNext(current);

			for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
			{
				if(find(worklist.begin(), worklist.end(), *sit) == worklist.end())
				{
//					fprintf(dump_file, "\nPushing Succ %d on Worklist\n", *sit);

					worklist.push_front(*sit);
				}	
			}
		}
	}

	
//	Analysis terminates

	GPBSet new_gpbs, call_sites, new_call_sites;

	call_sites = getCallSites();
	GPB ngpb;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		GPBSet temp1, temp2;

		temp1 = in[*it];
		temp2 = out[*it];

//		fprintf(dump_file, "\nConsidering GPB %d\n", *it);

		if(*it == start || *it == end)
		{	
			new_gpbs.insert(*it);
			new_gpb_map[*it] = gpb_map[*it];

			if(!orig)
			{
				res.RIN[*it] = RIN[*it];
				res.BRIN[*it] = BRIN[*it];

				res.ROUT[*it] = ROUT[*it];
				res.BROUT[*it] = BROUT[*it];

				res.PTSIN[*it] = PTSIN[*it];
				res.PTSOUT[*it] = PTSOUT[*it];
			}
		}

		if(temp1.empty() || temp2.empty())
		{
//			fprintf(dump_file, "\nIllegal/start GPB %d\n", *it);

			continue;
		}
		
		if(!(temp1 == temp2))
		{
//			fprintf(dump_file, "\nNon-empty GPB %d\n", *it);

			new_gpbs.insert(*it);
			new_gpb_map[*it] = gpb_map[*it];

			if(!orig)
			{
				res.RIN[*it] = RIN[*it];
				res.BRIN[*it] = BRIN[*it];

				res.ROUT[*it] = ROUT[*it];
				res.BROUT[*it] = BROUT[*it];

				res.PTSIN[*it] = PTSIN[*it];
				res.PTSOUT[*it] = PTSOUT[*it];
			}

			for(GPBSet::iterator sit = temp1.begin(); sit != temp1.end(); sit++)
			{
				temp = res.getNext(*sit);
				temp.insert(temp2.begin(), temp2.end());

				res.setNext(*sit, temp);

//				fprintf(dump_file, "\nConnecting Next %d to ", *sit);
//				print_set_integers(temp);
			}

			for(GPBSet::iterator sit = temp2.begin(); sit != temp2.end(); sit++)
			{
				temp = res.getPrev(*sit);
				temp.insert(temp1.begin(), temp1.end());

				res.setPrev(*sit, temp);

//				fprintf(dump_file, "\nConnecting Prev %d to ", *sit);
//				print_set_integers(temp);
			}
		}
		#if 0
		else
		{
			fprintf(dump_file, "\nEmpty GPB %d\n", *it);
		}
		#endif
	}

	res.setGPBs(new_gpbs);
	res.setEntryGPB(start);
	res.setExitGPB(end);
	res.gpb_map = new_gpb_map;
	res.GPB_count = GPB_count;

	#if 0
	fprintf(dump_file, "\nBefore Sanitize Function\n");
	res.printInitialGPG(cnode);
	#endif

//	res.sanitize(cnode, orig);

	#if 0
	if(res.sanitize(cnode, orig))
	{
		fprintf(dump_file,"\nHigh Alert after Elimination of All Empty GPB\n");
		fflush(dump_file);
		fprintf(dump_file,"\nOld GPG\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		fprintf(dump_file,"\nNew GPG\n");
		fflush(dump_file);
		res.printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}
	#endif

	this->gpbs = res.gpbs;
	this->entry = res.entry;
	this->end = res.end;
	this->gpb_map = res.gpb_map;
	this->GPB_count = res.GPB_count;

	this->RIN = res.RIN;
	this->BRIN = res.BRIN;
	this->ROUT = res.ROUT;
	this->BROUT = res.BROUT;

	this->preds = res.preds;
	this->succs = res.succs;

	this->top = res.top;
	this->back_edges = res.back_edges;
	
	#if 0
	fprintf(dump_file, "\nPrinting New GPG after DFA\n");
	printGPG(cnode);
	#endif
	
	#if PROFILING
	RETURN_VOID();
	#else
	return;
	#endif
}

void constructInitialGPG()
{
	struct cgraph_node * cnode;
	GPG g;
	unsigned int cnode_num;
	GPUSet temp;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		cnode_num = ((function_info *)(cnode->aux))->func_num;

		boundary_nodes.clear();

		#if DATA_MEAS
		fprintf(dump_file, "\nConstructing Initial GPG for %s (%d)\n", cgraph_node_name(cnode), cnode_num);
		fflush(dump_file);
		#endif

		g = normalize_cfg(cnode);

//		g.generateDotFileForGPG(cnode, true, "initb");

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nNormalize CFG for %s\n", cgraph_node_name(cnode));
		g.printInitialGPG(cnode);
		#endif

		#if DATA_MEAS
		Initial_GPG_map[cnode_num] = g;
		#endif

		g.localOptimizations(cnode, true);

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nNormalize CFG after empty GPB elimination for %s\n", cgraph_node_name(cnode));
		g.printInitialGPG(cnode);
		#endif

//		g.sanitize(cnode, true);

		if(main_cnode->uid != cnode->uid)
		{
			temp = g.insertBoundaryDefinitions(cnode);

			BDEFS[cnode_num] = temp;
		}
		else
		{
			temp = get_global_info();

			temp = filterFlowInsensitiveData(temp, main_cnode, 0);

			BDEFS[cnode_num] = temp;
		}

//		g.generateDotFileForGPG(cnode, true, "inita");

		GPG_map[cnode_num] = g;

		pop_cfun();
	}

//	fprintf(dump_file, "\nConstructed Initial GPGs for all functions\n");
//	fflush(dump_file);
}

void constructGPGsForIndirectlyCalledFunctions()
{
	struct cgraph_node * cnode;
	unsigned int cnode_num;
	GPG g, g1;
	unsigned int gpus_size;
	GPBSet gpbs;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		cnode_num = ((function_info *)(cnode->aux))->func_num;

		if(processed_functions.find(cnode_num) == processed_functions.end())
		{
			perform_analysis(cnode);

			#if 0 //DATA_MEAS
			g = optimized_GPG_map[cnode_num];
			g1 = GPG_map[cnode_num];
		
			gpus_size = g.returnNumberOfReducedGPUs(cnode);
			gpbs = g1.getCallBlocks(cnode);

			if(gpus_size == 0 && gpbs.size() == 0)
			{
			}
			else
			{
				fprintf(dump_file, "\nIndirectly Called Function has a non-Identity Procedure Summary\n");
			}
			#endif
		}

		pop_cfun();
	}

//	fprintf(dump_file, "\nConstructed GPGs for all indirectly called functions\n");
//	fflush(dump_file);
}

void GPG::kLimitGPUsInGPG(struct cgraph_node *cnode, bool orig)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs;	
	GPUSet gpus, temp, res;
	GPB gpb;

	gpbs = getGPBs();

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(orig)
		{
			gpus = gpb.getOrigGPUs();
		}
		else
		{
			gpus = gpb.getGPUs();
		}

		for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
		{
			if(isAdvancingGPU(*git))
			{
				temp = convertAdvancingToKLimitedGPU(*git);

				res.insert(temp.begin(), temp.end());
			}
			else
			{
				res.insert(*git);
			}
		}

		if(orig)
		{
			gpb.setOrigGPUs(res);
		}
		else
		{
			gpb.setGPUs(res);
		}

		gpb_map[*it] = gpb;
	}
}

void processSCC(unsigned int num)
{
//	fprintf(dump_file, "\nProcessing SCC %d\n", num);

	set< unsigned int > funcs, leaves;
	unsigned int fnum;
	struct cgraph_node *cnode;

	funcs = SCC_MAP[num];

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nFunctions in SCC: ");
	print_set_integers(funcs);
	#endif

	map< unsigned int, unsigned int > temp_map = REV_ORDER[num];

	for(map< unsigned int, unsigned int >::reverse_iterator it = temp_map.rbegin(); it != temp_map.rend(); it++) // Analyzing procedures in reverse post order in a SCC
	{
		fnum = it->second;

//		fprintf(dump_file, "\nConsidering %d\n", fnum);

		if(fnum <= FCount) // It's a function
		{
			cnode = func_numbering[fnum];

			perform_analysis(cnode);
		}
		else  // It's a SCC
		{
			processSCC(fnum);
		}
	}

	leaves = leavesSCCs[num];

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nLeaves in SCC: ");
	print_set_integers(leaves);
	#endif

	GPG g_prev, g_new;
	unsigned int end;
	GPUSet rout_new, rout_prev, brout_new, brout_prev;

	func_worklist_again.clear();

	for(set< unsigned int >::reverse_iterator it = leaves.rbegin(); it != leaves.rend(); it++) // Analyzing leaves again in reverse post order
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nLeaves %d\n", *it);
		#endif

		func_worklist_again.push_back(*it);
	}

	unsigned int reprocess_cnode;

	while(!func_worklist_again.empty())
	{
		reprocess_cnode = func_worklist_again.front();
		func_worklist_again.pop_front();

		cnode = func_numbering[reprocess_cnode];

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nReprocessing of %s (%d)\n", cgraph_node_name(cnode), reprocess_cnode);
		#endif

		perform_analysis_again(cnode);
	}
}

void GPGConstruction()
{
	processed_functions.clear();

//	fprintf(dump_file, "\nInside GPGConstruction\nPrinting REV_DFS_ORDER\n");

	struct cgraph_node *cnode;
	unsigned int num;

	for(map< unsigned int, unsigned int >::reverse_iterator it = REV_DFS_ORDER.rbegin(); it != REV_DFS_ORDER.rend(); it++) // Analyzing procedures in reverse post order
	{
//		fprintf(dump_file, "\n%d->%d\n", it->first, it->second);
	
		num = it->second;

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nnum = %d, FCount = %d, SCC_Count = %d\n", num, FCount, SCC_Count);
		#endif
	
		if(num <= FCount) // It's a function
		{
			cnode = func_numbering[num];

			perform_analysis(cnode);
		}
		else  // It's a SCC
		{
			processSCC(num);
		}
	}
}

void GPG::BFS(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet S, succs;
	GPBList Q;
	unsigned int current;

	unsigned int entry = getEntryGPB();

	S.insert(entry);

	BFS_GPB[cnode_num][entry] = ++BFS_COUNT;
	REV_BFS_GPB[cnode_num][BFS_COUNT] = entry;

	Q.push_back(entry);

	while(!Q.empty())
	{
		current = Q.front();
		Q.pop_front();

		succs = getNext(current);

		for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
		{
			if(S.find(*it) == S.end())
			{
				S.insert(*it);

				BFS_GPB[cnode_num][*it] = ++BFS_COUNT;
				REV_BFS_GPB[cnode_num][BFS_COUNT] = *it;

				Q.push_back(*it);
			}
		}
	}
}
 

void GPG::DFS(unsigned int v, struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	LABEL_GPB[cnode_num][v] = true;

//	fprintf(dump_file, "\nInside DFS %d order %d\n", v, DFS_COUNT);

	GPBSet succs;
	unsigned int w;

	succs = getNext(v);

	for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
	{
		w = *it;

		if(!LABEL_GPB[cnode_num][w])
		{
			DFS(w, cnode);
		}
	}

	unsigned int order = DFS_COUNT;

	DFS_GPB[cnode_num][v] = DFS_COUNT;
	REV_DFS_GPB[cnode_num][DFS_COUNT] = v;	

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nAssigning DFS Order %d to GPB %d\n", order, v);
	fflush(dump_file);
	#endif

	DFS_COUNT--;
}

bool checkTypeCompatibility(GPUSet p_gpus, GPUSet s_gpus)
{
	GPUSet temp, inter_set;

	set_intersection(p_gpus.begin(), p_gpus.end(), s_gpus.begin(), s_gpus.end(), inserter(inter_set, inter_set.end()));

	if((inter_set == p_gpus) || (inter_set == s_gpus))
	{
//		fprintf(dump_file, "\nReturning False - Subset - coalescing\n");

		return false;
	}

	#if 0
	fprintf(dump_file, "\nInside checkTypeCompatibility\n");
	fprintf(dump_file, "\np_gpus\n");
	printSetOfGPUs(p_gpus);
	fprintf(dump_file, "\ns_gpus\n");
	printSetOfGPUs(s_gpus);
	#endif

	for(GPUSet::iterator pit = p_gpus.begin(); pit != p_gpus.end(); pit++)
	{
		GPUSet inter_set;

		#if 0
		fprintf(dump_file, "\nChecking comaptibility of:\n");
		print_GPU(*pit);
		#endif

		temp = typeCompatibleGPUs[*pit];

		#if 0
		fprintf(dump_file, "\ntemp\n");
		printSetOfGPUs(temp);
		#endif

		set_intersection(temp.begin(), temp.end(), s_gpus.begin(), s_gpus.end(), inserter(inter_set, inter_set.end()));

		if(!inter_set.empty())
		{
			#if 0
			fprintf(dump_file, "\nReturning True - No coalescing\n");
			fprintf(dump_file, "\np_gpus\n");
			printSetOfGPUs(p_gpus);
			fprintf(dump_file, "\ns_gpus\n");
			printSetOfGPUs(s_gpus);
			fprintf(dump_file, "\ninter_set\n");
			printSetOfGPUs(inter_set);
			#endif

			return true;
		}
	}

//	fprintf(dump_file, "\nReturning False - coalescing\n");

	return false;
}

bool isDerefPresent(GPUSet res)
{
	for(GPUSet::iterator it = res.begin(); it != res.end(); it++)
	{
		if(isDerefGPU(*it))
		{
//			fprintf(dump_file, "\nDeref Present\n");
//			fflush(dump_file);

			return true;
		}
	}

//	fprintf(dump_file, "\nDeref Not Present\n");
//	fflush(dump_file);

	return false;
}

bool isSubset(GPUSet p, GPUSet n)
{
	GPUSet temp;

	set_intersection(p.begin(), p.end(), n.begin(), n.end(), inserter(temp, temp.end()));
	
	if((temp == n) || (temp == p))
	{
		return true;
	}

	return false;
}

bool typeCompatibilityOfGPUs(GPUSet gpus_p, GPUSet gpus_n)
{
	GPUSet temp, fin_gpus;

	#if 0
	fprintf(dump_file, "\ngpus_p\n");
	fflush(dump_file);
	printSetOfGPUs(gpus_p);
	fflush(dump_file);
	fprintf(dump_file, "\ngpus_n\n");
	fflush(dump_file);
	printSetOfGPUs(gpus_n);
	fflush(dump_file);
	#endif

	#if 1
	set_tree_nodes a, b, c;

	for(GPUSet::iterator pit = gpus_p.begin(); pit != gpus_p.end(); pit++)
	{
		a = NodeType[get<0>(*pit)];

		for(GPUSet::iterator nit = gpus_n.begin(); nit != gpus_n.end(); nit++)
		{
			set_tree_nodes d, e;

			if(*pit == *nit)
			{
				continue;
			}
			else if(get<0>(*pit) == get<0>(*nit))
			{
				continue;
			}


			b = NodeType[get<0>(*nit)];
			c = NodeType[get<1>(*nit)];

			set_intersection(a.begin(), a.end(), b.begin(), b.end(), inserter(d, d.end()));
			set_intersection(a.begin(), a.end(), c.begin(), c.end(), inserter(e, e.end()));

			if((!(d.empty())) || (!(e.empty())))
			{
				return true;
			}
		}
	}
	#endif

	#if 0
	set_difference(gpus_p.begin(), gpus_p.end(), gpus_n.begin(), gpus_n.end(), inserter(fin_gpus, fin_gpus.end()));

	fprintf(dump_file, "\nfin_gpus\n");
	fflush(dump_file);
	printSetOfGPUs(fin_gpus);
	fflush(dump_file);

	for(GPUSet::iterator it = fin_gpus.begin(); it != fin_gpus.end(); it++)
	{
		GPUSet inter;

		fprintf(dump_file, "\nConsidering GPU for type matching\n");
		fflush(dump_file);
		print_GPU(*it);
		fflush(dump_file);

		temp = typeCompatibleGPUs[*it];

		fprintf(dump_file, "\ntemp\n");
		fflush(dump_file);
		printSetOfGPUs(temp);
		fflush(dump_file);

		set_intersection(gpus_n.begin(), gpus_n.end(), temp.begin(), temp.end(), inserter(inter, inter.end()));

		fprintf(dump_file, "\ninter\n");
		fflush(dump_file);
		printSetOfGPUs(inter);
		fflush(dump_file);

		if(!inter.empty())
		{
			fprintf(dump_file, "\nReturning true for typeCompatibility\n");
			fflush(dump_file);

			return true;
		}
	}

	fprintf(dump_file, "\nReturning false for typeCompatibility\n");
	fflush(dump_file);
	#endif

	return false;
}

bool typeCompatibility(set_tree_nodes nodes, GPUSet res)
{
	set_tree_nodes t;

	for(GPUSet::iterator it = res.begin(); it != res.end(); it++)
	{
		set_tree_nodes t1, t2;

		t = NodeType[get<0>(*it)];

		set_intersection(t.begin(), t.end(), nodes.begin(), nodes.end(), inserter(t1, t1.end()));

		if(!t1.empty())
//		if(nodes.find(t) != nodes.end())
		{
			return true;
		}		

		t = NodeType[get<1>(*it)];

		set_intersection(t.begin(), t.end(), nodes.begin(), nodes.end(), inserter(t2, t2.end()));

		if(!t2.empty())
//		if(nodes.find(t) != nodes.end())
		{
			return true;
		}
	}

	#if 0
	fprintf(dump_file, "\nReturning false for typeCompatibility\n");
	fflush(dump_file);
	#endif

	return false;
}

set_tree_nodes sourceTypes(GPUSet res)
{
	set_tree_nodes t;
	set_tree_nodes result;

	for(GPUSet::iterator it = res.begin(); it != res.end(); it++)
	{
		t = NodeType[get<0>(*it)];

		result.insert(t.begin(), t.end());			
	}

	return result;
}

void GPG::coalescingDFA(struct cgraph_node *cnode)
{
	if(isTop())
	{
		return;
	}

	GPBSet gpbs = getGPBs();

	if(gpbs.size() == 1)
	{
		return;
	}

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	unsigned int current_node_id;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nCoalescing GPBs for GPG of function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	std::map< unsigned int, GPUSet > InT, OutT;
//	std::map< unsigned int, set_tree_nodes > InT, OutT;

	INC.clear();
	OUTC.clear();

	already_coalesced.clear();

	initialize_GPB_worklist(cnode);

	unsigned int start, end;

	start = getEntryGPB();
	end = getExitGPB();

	GPBSet preds, succs;

	GPB gpb, t_gpb;
	GPUSet gpus, gpus_temp;

	bool temp, prev_in, prev_out, new_in, new_out;
	GPUSet p_in, n_in, p_out, n_out;
//	set_tree_nodes p_in, n_in, p_out, n_out;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++) // Initialization
	{
		INC[*it] = false;
		OUTC[*it] = false;
	}

	#if 0 //PRINT_DATA 
	fprintf(dump_file, "\nAfter Initialization\n");
	fflush(dump_file);
	#endif

	unsigned int size = gpbs.size();

	int * worklist = GPB_worklist[cnode_num];
	int i;
	bool change;
	std::map< unsigned int, unsigned int > rev_dfs_gpb = REV_DFS_GPB[cnode_num];
	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[cnode_num];

	for(i = 1; i <= size; i++)
	{
		change  =  false;
		
		if(worklist[i])
		{
			current_node_id = rev_dfs_gpb[i]; 

			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nAnalyzing GPB %d Function %s\n", current_node_id, cgraph_node_name(cnode));
			fflush(dump_file);
			#endif

			gpb = gpb_map[current_node_id];

			if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock())// || current_node_id == start || current_node_id == end)
			{
				#if 0
				fprintf(dump_file, "\nSpecial GPB %d\n", current_node_id);
				fflush(dump_file);
				#endif

				worklist[i] = false;

				INC[current_node_id] = false;
				OUTC[current_node_id] = false;

				continue;
			}

//			set_tree_nodes src_types; 

			prev_in = INC[current_node_id];
			prev_out = OUTC[current_node_id];

			p_in = InT[current_node_id];
			p_out = OutT[current_node_id];

//			GPUSet in_gpus = RIN[current_node_id];

			temp = false;
			GPUSet t_temp2;
//			set_tree_nodes t_temp2;

			#if 0
			fprintf(dump_file, "\nNot a special GPB %d\nPrev IN %d, Prev OUT %d", current_node_id, prev_in, prev_out);
			fflush(dump_file);
			fprintf(dump_file, "\nPrev INT %d\n", current_node_id);
			fflush(dump_file);
			printSetOfGPUs(InT[current_node_id]);
			fflush(dump_file);
			fprintf(dump_file, "\nPrev OUTT %d\n", current_node_id);
			fflush(dump_file);
			printSetOfGPUs(OutT[current_node_id]);
			fflush(dump_file);
			#endif

			preds = getPrev(current_node_id);
			succs = getNext(current_node_id);

			gpus = gpb.getGPUs();

//			src_types = sourceTypes(gpus);

			for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
			{
				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nPredecessor %d\n", *it);
				fflush(dump_file);
				#endif

				t_gpb = gpb_map[*it];

				GPUSet t_temp1;
//				set_tree_nodes t_temp1;

				if(t_gpb.isCallBlock() || t_gpb.isSymGPB() || t_gpb.isIndirectCallBlock())// || (start == *it) || (end == *it))
				{
					#if 0 //PRINT_DATA
					fprintf(dump_file, "\nCall Block\n");
					#endif

//					temp |= false; // add an assert
	
//					break;
				}	
				#if 1
				else if(OUTC[*it])
				{
					temp = true;

//					t_temp1 = OutT[*it];

					break;
				}
				#endif
				else
				{
					gpus_temp = OutT[*it]; 

					GPUSet gpus_in_gpb = t_gpb.getGPUs();

					#if 0
					fprintf(dump_file, "\nGPUs of %d\n", *it);
					fflush(dump_file);
					printSetOfGPUs(gpus_temp);
					fflush(dump_file);
					fprintf(dump_file, "\nGPUs of OUT of %d\n", *it);
					fflush(dump_file);
					printSetOfGPUs(OutT[*it]);
					fflush(dump_file);
					fprintf(dump_file, "\nGPUs of %d\n", current_node_id);
					fflush(dump_file);
					printSetOfGPUs(gpus);
					fflush(dump_file);
					#endif

					#if 0
					if(isSubset(gpus_temp, gpus))
					{
						fprintf(dump_file, "\nSubset Relation Satisfied\n");
						fflush(dump_file);

						t_temp1 = OutT[*it];
					}
					#endif
	
					GPUSet diff_gpus;

					set_difference(gpus_temp.begin(), gpus_temp.end(), gpus.begin(), gpus.end(), inserter(diff_gpus, diff_gpus.end()));

					if(gpus == gpus_temp)
					{
						temp = true;

//						t_temp1 = OutT[*it];

						break;
					}
					else if(gpus == gpus_in_gpb)
					{
						temp = true;

//						t_temp1 = OutT[*it];

						break;
					}

					else if(diff_gpus.empty())
					{
						temp = true;

//						t_temp1 = OutT[*it];

						break;
					}
					else if((isDerefPresent(gpus) || isDerefPresent(gpus_temp)) && checkDataDependenceForCoalescing(gpus_temp, gpus))
//					else if((isDerefPresent(gpus) || isDerefPresent(gpus_temp)) && typeCompatibility(OutT[*it], gpus))
					{
//						temp |= false;

//						break;

						// Remains empty
					}
					else
					{
						temp = true;

//						t_temp1 = OutT[*it];

						break;
					}

					#if 0
					if(t_temp1.empty())
					{
						temp = false;

						break;
					}
					#endif

//					temp = temp && OUTC[*it];

//					t_temp2.insert(t_temp1.begin(), t_temp1.end());
				}
			}

			#if 0
			if(temp && current_node_id != start)
			{
				if(!prev_in)
				{
					fprintf(dump_file, "\nFunction %s, Current GPB %d, temp %d, prev_in %d\n", cgraph_node_name(cnode), current_node_id, temp, prev_in);
					fflush(dump_file);
					exit(1);
				}
//				gcc_assert(!prev_in);
			}
			#endif

//			INC[current_node_id] = INC[current_node_id] && temp;

			INC[current_node_id] = temp;

			GPUSet empty_set;

			if(INC[current_node_id])
			{	
				for(GPBSet::iterator ti = preds.begin(); ti != preds.end(); ti++)
				{
					if(OUTC[*ti])
					{
						t_temp2.insert(OutT[*ti].begin(), OutT[*ti].end());
					}
				}

				InT[current_node_id] = t_temp2;
			}
			else
			{
				InT[current_node_id] = empty_set;
			}

//			fprintf(dump_file, "\nGPB %d Function %s INC %d\n", current_node_id, cgraph_node_name(cnode), INC[current_node_id]);

			temp = false;

			for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
			{
				t_gpb = gpb_map[*it];

				if(t_gpb.isCallBlock() || t_gpb.isSymGPB() || t_gpb.isIndirectCallBlock()) // || (start == *it) || (end == *it))
				{
//					temp |= false; // add an assert

//					break;
				}	
				else
				{
					temp |= INC[*it];
					
					#if 0
					if(!temp)
						break;
					#endif
				}
			}

			#if 0
			if(temp && current_node_id != end)
			{
				if(!prev_out)
				{
					fprintf(dump_file, "\nFunction %s, Current GPB %d, temp %d, prev_out %d\n", cgraph_node_name(cnode), current_node_id, temp, prev_out);
					fflush(dump_file);
					exit(1);
				}
	
//				gcc_assert(!prev_out);
			}
			#endif

//			OUTC[current_node_id] = OUTC[current_node_id] && temp;

			OUTC[current_node_id] = temp;

			if(INC[current_node_id])
			{
				gpus.insert(InT[current_node_id].begin(), InT[current_node_id].end());

				OutT[current_node_id] = gpus;
			}
			else
			{
				OutT[current_node_id] = gpus;
			}

			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nGPB %d Function %s OUTC %d\n", current_node_id, cgraph_node_name(cnode), OUTC[current_node_id]);

			fprintf(dump_file, "\nNew INC %d, New OUTC %d", INC[current_node_id], OUTC[current_node_id]);
			fflush(dump_file);
			fprintf(dump_file, "\nNew INT %d\n", current_node_id);
			fflush(dump_file);
			printSetOfGPUs(InT[current_node_id]);
			fflush(dump_file);
			fprintf(dump_file, "\nNew OUTT %d\n", current_node_id);
			fflush(dump_file);
			printSetOfGPUs(OutT[current_node_id]);
			fflush(dump_file);
			#endif

			if((!(prev_in == INC[current_node_id])))	
//			if((!(p_in == InT[current_node_id])) || (!(prev_in == INC[current_node_id])))	
			{
//				fprintf(dump_file, "\nIN Changed for GPB %d Function %s\n", current_node_id, cgraph_node_name(cnode));

				change = true;

				get_pred_gpbs(current_node_id, cnode);
			}

			if((!(p_out == OutT[current_node_id])) || (!(prev_out == OUTC[current_node_id])))	
			{
				change = true;

				get_succ_gpbs(current_node_id, cnode);
			}


			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nBefore updating the worklist\n");
			fflush(dump_file);
			#endif

			worklist[i] = false;

			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nProcessing of %d is over\n", current_node_id);
			fflush(dump_file);
			#endif
		}

		if(change)
		{
			i = 0;
		
			worklist = GPB_worklist[cnode_num];	
		}
	}

	free(GPB_worklist[cnode_num]);

// 	Mapping before transformation. Constructing \pi	(partition)

	CoalescingAbstraction abs(*this);
	unsigned int part_num = 1;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPB %d has INC %d and OUTC %d\n", *it, INC[*it], OUTC[*it]);
		#endif

		if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock()) // || (start == *it) || (end == *it))
		{
			already_coalesced.insert(*it);

			continue;	
		}

		if(already_coalesced.find(*it) != already_coalesced.end())
		{
			continue;
		}

		coalesceG.clear();

		collectGroup(*it, cnode);

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPBs in a Part %d\n", part_num);

		for(GPBSet::iterator cit = coalesceG.begin(); cit != coalesceG.end(); cit++)
		{
			fprintf(dump_file, "\nGPB %d\n", *cit);
		}
		#endif

		abs.addPart(part_num++, coalesceG);
	}

// 	Checking for the regular parts and reducing the parts to create regular parts

	unsigned int temp_part_num = part_num;

	for(unsigned int x = 1; x < temp_part_num; x++)
	{
		part_num = abs.makeRegularPart(x, part_num);
	}
	
// 	Transformation - Coalescing the GPBs in regular parts

	GPBSet cgpbs;
		
	for(unsigned int x = 1; x < part_num; x++)
	{
		cgpbs = abs.getGPBsFromPart(x);

		if(cgpbs.size() == 0)
		{
			continue;
		}
		else if(cgpbs.size() == 1)
		{
			continue;
		}

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPBs Coalecsing in Part %d\n", x);

		for(GPBSet::iterator cit = cgpbs.begin(); cit != cgpbs.end(); cit++)
		{
			fprintf(dump_file, "\nGPB %d\n", *cit);
		}
		#endif

		coalescingGroupOfGPBs(cgpbs, cnode);	
	}


	#if 0 // Old Coalescing - Transformation

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = gpb_map[*it];

		if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock()) // || (start == *it) || (end == *it))
		{
			already_coalesced.insert(*it);

			continue;	
		}

		if(already_coalesced.find(*it) != already_coalesced.end())
		{
			continue;
		}

//		fprintf(dump_file, "\nConsidering GPB %d\n", *it);
//		fflush(dump_file);

		coalesceG.clear();
		DFP_TEMP.clear();

		collectGroup(*it, cnode);

//		if(coalesceG.size() > 1)
		if(makeRegularPart()) // Added the check for part to be regular. Returns true if it is regular and hence coalescing is possible
//		if(coalesceG.size() > 1 && checkRegularPart()) // Added the check for part to be regular. Returns true if it is regular and hence coalescing is possible
		{
			coalescingGroupOfGPBs(coalesceG, cnode);	
		}
	}
	#endif

	#if 0 //PRINT_DATA
	if(checkGPGStructure(cnode, true))
	{
		fprintf(dump_file,"\nCoalescing Alert123 %s\n", cgraph_node_name(cnode));
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		generateDotFileForGPG(cnode, true, "call");
		exit(1);
	}

	fprintf(dump_file, "\nGPG after coalescing for Function %s\n", cgraph_node_name(cnode));
	printGPG(cnode);
	#endif
}

void GPG::coalescingDFAAlt(struct cgraph_node *cnode)
{
	if(isTop())
	{
		return;
	}

	GPBSet gpbs = getGPBs();

	if(gpbs.size() == 1)
	{
		return;
	}

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	unsigned int current_node_id;

	#if 0
	fprintf(dump_file, "\nCoalescing GPB\n");
	fflush(dump_file);
	#endif

	INC.clear();
	OUTC.clear();

	already_coalesced.clear();

	initialize_GPB_worklist(cnode);

	unsigned int start, end;

	start = getEntryGPB();
	end = getExitGPB();

	GPBSet preds, succs;

	GPB gpb, t_gpb;
	GPUSet gpus, gpus_temp;

	bool temp, prev_in, prev_out, new_in, new_out;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++) // Initialization
	{
		INC[*it] = true;
		OUTC[*it] = true;
	}

	#if 0
	fprintf(dump_file, "\nAfter Initialization\n");
	fflush(dump_file);
	#endif

	unsigned int size = gpbs.size();

	int * worklist = GPB_worklist[cnode_num];
	int i;
	bool change;
	std::map< unsigned int, unsigned int > rev_dfs_gpb = REV_DFS_GPB[cnode_num];
	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[cnode_num];

	for(i = 1; i <= size; i++)
	{
		change  =  false;

		if(worklist[i])
		{
			current_node_id = rev_dfs_gpb[i]; 

			#if 0
			fprintf(dump_file, "\nAnalyzing GPB %d\n", current_node_id);
			fflush(dump_file);
			#endif

			gpb = gpb_map[current_node_id];	

			if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock() || (end == current_node_id) || (start == current_node_id))
			{
				#if 0
				fprintf(dump_file, "\nSpecial GPB %d\n", current_node_id);
				fflush(dump_file);
				#endif

				worklist[i] = false;

				INC[current_node_id] = true;
				OUTC[current_node_id] = true;

				continue;
			}

			prev_in = INC[current_node_id];
			prev_out = OUTC[current_node_id];

			#if 0
			fprintf(dump_file, "\nNot a special GPB %d\nPrev IN %d, Prev OUT %d", current_node_id, prev_in, prev_out);
			fflush(dump_file);
			#endif

			preds = getPrev(current_node_id);
			succs = getNext(current_node_id);

			gpus = gpb.getGPUs();

//			if(!ret_ind_gpus(gpus).empty())
			if(checkGPUSetForCoalescing(gpus, cnode))
			{
				#if 0
				fprintf(dump_file, "\nGPB %d contains indirect GPUs\n", current_node_id);
				fflush(dump_file);
				#endif

				GPUSet tp1, tp2;

				temp = true;

				for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
				{
//					fprintf(dump_file, "\nPred %d\n", *it);

					t_gpb = gpb_map[*it];

					#if 0
					if(dfs_gpb[*it] >= dfs_gpb[current_node_id])
					{
						temp = false;
					}
					#endif

					if(t_gpb.isCallBlock() || t_gpb.isSymGPB() || t_gpb.isIndirectCallBlock())// || (start == *it) || (end == *it))
					{
						temp = false;
					}	
					else
					{
						gpus_temp = t_gpb.getGPUs();

						#if 0
						if(!((tp1 == gpus) || (tp1 == gpus_temp)))
//						if(!((gpus == gpus_temp)))// || gpus_temp.empty()))
						{
							temp = false;	
						}
						#endif

						if(checkTypeCompatibility(gpus_temp, gpus))
						{
//							fprintf(dump_file, "\nP Types are matched, hence no coalecing of %d and %d\n", *it, current_node_id);

							temp = false;
						}
					}
				}

				INC[current_node_id] = temp;

				temp = true;

				for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
				{
//					fprintf(dump_file, "\nSuccessor %d\n", *it);

					t_gpb = gpb_map[*it];

					#if 0		
					if(dfs_gpb[current_node_id] >= dfs_gpb[*it])
					{
						temp = false;
					}
					#endif	
					
					if(t_gpb.isCallBlock() || t_gpb.isSymGPB() || t_gpb.isIndirectCallBlock()) // || (start == *it) || (end == *it))
					{
						temp = false;
					}	
					else
					{
						gpus_temp = t_gpb.getGPUs();

						#if 0
						if(!((tp2 == gpus) || (tp2 == gpus_temp)))
//						if(!((gpus == gpus_temp)))// || gpus_temp.empty()))
						{
							temp = false;	
						}
						#endif

						if(checkTypeCompatibility(gpus, gpus_temp))
						{
//							fprintf(dump_file, "\nS Types are matched, hence no coalecing of %d and %d\n", current_node_id, *it);

							temp = false;
						}
					}
				}

				OUTC[current_node_id] = temp;
			}
			else
			{
//				fprintf(dump_file, "\nGPB %d does not contain indirect GPUs\n", current_node_id);
//				fflush(dump_file);

				temp = true;

				for(GPBSet::iterator it = preds.begin(); it != preds.end(); it++)
				{
//					t_gpb = gpb_map[cnode_num][*it];

					temp = temp & OUTC[*it];
				}

				INC[current_node_id] = temp;

				temp = true;

				for(GPBSet::iterator it = succs.begin(); it != succs.end(); it++)
				{
//					t_gpb = gpb_map[cnode_num][*it];

					temp = temp & INC[*it];
				}

				OUTC[current_node_id] = temp;
			}

//			fprintf(dump_file, "\nIN %d, OUT %d", INC[current_node_id], OUTC[current_node_id]);
//			fflush(dump_file);

			if(!(prev_in == INC[current_node_id]))
			{
//				fprintf(dump_file, "\nIN Changed: Pushing Predecessors\n");
//				fflush(dump_file);
	
//				fprintf(dump_file, "\nPrev IN %d, New IN %d\n", prev_in, INC[current_node_id]);
//				fflush(dump_file);
	
				change = true;

				get_pred_gpbs(current_node_id, cnode);
			}

			if(!(prev_out == OUTC[current_node_id]))
			{
//				fprintf(dump_file, "\nOUT Changed: Pushing Successors\n");
//				fflush(dump_file);
	
//				fprintf(dump_file, "\nPrev OUT %d, New OUT %d\n", prev_out, OUTC[current_node_id]);
//				fflush(dump_file);
	
				change = true;

				get_succ_gpbs(current_node_id, cnode);
			}	

			worklist[i] = false;
		}

		if(change)
		{
//			fprintf(dump_file, "\nStarting from 1\n");
//			fflush(dump_file);

			i = 1;
		
			worklist = GPB_worklist[cnode_num];
		}
	}

	#if 0
	fprintf(dump_file, "\nEnd of Analysis\n");
	fflush(dump_file);
	#endif

	free(GPB_worklist[cnode_num]);

	#if 0
	fprintf(dump_file, "\nActual Coalescing\n");
	fflush(dump_file);
	#endif

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		start = getEntryGPB();
		end = getExitGPB();

		gpb = gpb_map[*it];

		if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock() || (start == *it) || (end == *it))
		{
			already_coalesced.insert(*it);

			continue;	
		}

		if(already_coalesced.find(*it) != already_coalesced.end())
		{
			continue;
		}

		#if 0
		fprintf(dump_file, "\nConsidering GPB %d\n", *it);
		fflush(dump_file);
		#endif

		coalesceG.clear();

		collectGroup(*it, cnode);

		if(coalesceG.size() > 1)
		{
			coalescingGroupOfGPBs(coalesceG, cnode);	
		}
	}

	#if 0
	fprintf(dump_file, "\nAfter Coalescing\n");
	fflush(dump_file);
	#endif

	#if 1
	computeDownwardsExposedDefinitions(cnode);

	GPUSet mustkill = DownwardsExposedMustDefinitions[cnode_num]; 
	GPB new_gpb;
	int f[IndirectionList::kSize];
	IndirectionList el1(true, 0, 0, f);
	IndirectionList el2(false, 0, 0, f);
	GPUSet gpu_set;
	Node src;
	Node sn1(summ_node_id, el1);
	Node sn2(summ_node_id, el2);

	if(!mustkill.empty()) //Add definition free paths
	{
		#if 0
		for(GPUSet::iterator it = maygen.begin(); it != maygen.end(); it++)
		{
			src = getNode(get<0>(*it));

			if(src.getList().Length() > 1)
			{
				if(isStackGPU(*it))
				{
					GPU gpu(src, sn1, 0);

					gpu_set.insert(gpu.getGPUID());
				}
				else
				{	
					GPU gpu(src, sn2, 0);

					gpu_set.insert(gpu.getGPUID());
				}
			}
		}
		#endif

//		if(!gpu_set.empty())
		{
			start = getEntryGPB();
			end = getExitGPB();

			unsigned int x = GPB_count++;	

			new_gpb.setId(x);
			new_gpb.setBBIndex(2);
			new_gpb.setGPUs(mustkill);
//			new_gpb.setGPUs(gpu_set);
			gpb_map[x] = new_gpb;

			addNext(start, x);
			addPrev(end, x);

			addPrev(x, start);
			addNext(x, end);

			gpbs = getGPBs();
			gpbs.insert(x);
			setGPBs(gpbs);
		}
	}
	#endif
}

void GPG::collectGroup(unsigned int current_node_id, struct cgraph_node *cnode)
{
	#if 0
	fprintf(dump_file, "\nInside collectGroup for GPB %d\n", current_node_id);
	fflush(dump_file);
	#endif

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	unsigned int start = getEntryGPB();
	unsigned int end = getExitGPB();

	if(current_node_id == start || current_node_id == end)
	{
		return;
	}

	#if 0
	fprintf(dump_file, "\nStart GPB %d, End GPB %d\n", start, end);
	fflush(dump_file);
	#endif

	GPB gpb;

	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[cnode_num];

	GPBSet preds, succs;

	if(INC[current_node_id])
	{
		#if 0
		fprintf(dump_file, "\nIN for GPB %d true\n", current_node_id);
		fflush(dump_file);
		#endif

		preds = getPrev(current_node_id);

		already_coalesced.insert(current_node_id);
		coalesceG.insert(current_node_id);

		for(GPBSet::iterator pit = preds.begin(); pit != preds.end(); pit++)
		{
			gpb = gpb_map[*pit];

			if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock() || (start == *pit) || (end == *pit))
			{
				#if 0
				fprintf(dump_file, "\nDo Not coalesce Pred %d\n", *pit);
				fflush(dump_file);
				#endif

				already_coalesced.insert(*pit);
	
				continue;
			}
			else if(dfs_gpb[*pit] >= dfs_gpb[current_node_id])
			{
				continue;
			}

			if(already_coalesced.find(*pit) == already_coalesced.end())
			{
//				fprintf(dump_file, "\nPred %d not analyzed yet\n", *pit);
//				fflush(dump_file);

				collectGroup(*pit, cnode);
			}

			#if 0
			fprintf(dump_file, "\nAdding Pred to group %d\n", *pit);
			fflush(dump_file);
			#endif

			already_coalesced.insert(*pit);
			coalesceG.insert(*pit);
		}
	}

	if(OUTC[current_node_id])
	{
		#if 0
		fprintf(dump_file, "\nOUT for GPB %d true\n", current_node_id);
		fflush(dump_file);
		#endif

		succs = getNext(current_node_id);

		already_coalesced.insert(current_node_id);
		coalesceG.insert(current_node_id);

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			gpb = gpb_map[*sit];

			if(gpb.isCallBlock() || gpb.isSymGPB() || gpb.isIndirectCallBlock() || (start == *sit) || (end == *sit))
			{
				#if 0
				fprintf(dump_file, "\nDo Not coalesce Succ %d\n", *sit);
				fflush(dump_file);
				#endif

				already_coalesced.insert(*sit);
	
				continue;
			}
			else if(dfs_gpb[current_node_id] >= dfs_gpb[*sit])
			{
				continue;
			}

			if(already_coalesced.find(*sit) == already_coalesced.end())
			{
//				fprintf(dump_file, "\nSucc %d not analyzed yet\n", *sit);
//				fflush(dump_file);

				collectGroup(*sit, cnode);
			}

			#if 0
			fprintf(dump_file, "\nAdding Succ to group %d\n", *sit);
			fflush(dump_file);
			#endif

			already_coalesced.insert(*sit);
			coalesceG.insert(*sit);
		}
	}
}

bool GPG::makeRegularPart()
{
	if(coalesceG.size() <= 1)
	{
		return false;
	}

	if(checkRegularPart())
	{
		return true;
	}

	GPBSet succs;
	GPB gpb;
	GPBSet temp_coalesce;

	temp_coalesce = coalesceG;

	for(GPBSet::iterator it = temp_coalesce.begin(); it != temp_coalesce.end(); it++)
	{
		succs = getNext(*it);

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			if(temp_coalesce.find(*sit) == temp_coalesce.end())
			{
				coalesceG.erase(*it);

				break;
			}
		}
	}

	if(coalesceG.empty())
	{
		return false;
	}
	if(coalesceG != temp_coalesce)
	{
		return makeRegularPart();
	}

	return false;
}

bool GPG::checkRegularPart()
{
	GPBSet entry, exit, succs, preds;
	GPB gpb;
	definitions dfp_out;

	for(GPBSet::iterator it = coalesceG.begin(); it != coalesceG.end(); it++)
	{
		succs = getNext(*it);

		preds = getPrev(*it);

		for(GPBSet::iterator pit = preds.begin(); pit != preds.end(); pit++)
		{
			if(coalesceG.find(*pit) == coalesceG.end())
			{
				entry.insert(*it);

				break;
			}
		}

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			if(coalesceG.find(*sit) == coalesceG.end())
			{
				exit.insert(*it);

				dfp_out= DFP[*it];

				DFP_TEMP.insert(dfp_out.begin(), dfp_out.end());

				break;
			}
		}
	}

	GPBSet temp1, temp2;

	GPBSet::iterator it;

	it = entry.begin();

	temp1 = getPrev(*it);

	it++;
	
	for(; it != entry.end(); it++)
	{
		temp2 = getPrev(*it);

		if(temp1 != temp2)
		{
			return false;
		}				
	}

	it = exit.begin();

	temp1 = getNext(*it);

	it++;

	for(; it != exit.end(); it++)
	{
		temp2 = getNext(*it);

		if(temp1 != temp2)
		{
			return false;
		}
	}

	return true;
}

void GPG::collectTypeInfo(struct cgraph_node *cnode, bool orig)
{
	GPUSet gpus = returnGPUs(cnode, orig);

	#if 0
	fprintf(dump_file, "\nCollecting Type Info for function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	GPUSet temp_set;
	set_tree_nodes a, b, c;

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		a = NodeType[get<0>(*it)];

		#if 0
		if(a == NULL)
		{
			continue;
		}
		#endif

		for(GPUSet::iterator git = gpus.begin(); git != gpus.end(); git++)
		{
			set_tree_nodes t1, t2;

			if(*it == *git)
			{
				continue;
			}
		
			b = NodeType[get<0>(*git)];
			c = NodeType[get<1>(*git)];

			set_intersection(a.begin(), a.end(), b.begin(), b.end(), inserter(t1, t1.end()));
			set_intersection(a.begin(), a.end(), c.begin(), c.end(), inserter(t2, t2.end()));

			#if 0
			fprintf(dump_file, "\nCompatibility Testing\n");
			print_GPU(*it);
			print_GPU(*git);

//			print_node(dump_file, "\nA\n", a, 0);
//			print_node(dump_file, "\nB\n", b, 0);
//			print_node(dump_file, "\nC\n", c, 0);
			#endif

			if((!(t1.empty())) || (!(t2.empty())))
//			if((a == b) || (a == c))
			{
				#if 0
				fprintf(dump_file, "\nType Compatible\n");
				print_GPU(*it);
				print_GPU(*git);
				#endif

				temp_set = typeCompatibleGPUs[*it];

				temp_set.insert(*git);

				typeCompatibleGPUs[*it] = temp_set;
			}
			#if 0
			else
			{
				fprintf(dump_file, "\nNot Type Compatible\n");
				print_GPU(*it);
				print_GPU(*git);
			}
			#endif
		}
	}
}

void GPG::computeDefRef(struct cgraph_node *cnode, bool orig)
{
	GPUSet gpus = returnGPUs(cnode, orig);
	
	node_id_type s, t, si, ti;
	set_tree_nodes temp, def, ref;
	std::pair< set_tree_nodes, set_tree_nodes > res;
	Node lhs, rhs, lhsi, rhsi;
	unsigned int lvar, lvari, rvar, rvari;

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		s = get<0>(*it);
		t = get<1>(*it);

		lhs = getNode(s);	
		rhs = getNode(t);	

		lvar = get<0>(s);
		rvar = get<0>(t);

		if(CDV.find(lvar) != CDV.end())
		{
			lvari = --lvar;
		}
		else
		{
			lvari = ++lvar;
		}

		if(CDV.find(rvar) != CDV.end())
		{
			rvari = --rvar;
		}
		else
		{
			rvari = ++rvar;
		}
		
		lhsi = Node(lvari, lhs.getList());
		si = lhsi.getNodeID();

		rhsi = Node(rvari, rhs.getList());
		ti = rhsi.getNodeID();
		
//		fprintf(dump_file, "\nExtracting Types\n");
//		print_GPU(*it);

		set_tree_nodes null_set;
		null_set.insert(NULL);

		if(DefTypes.find(*it) == DefTypes.end())
		{
			res = computeTypeOfNode(s, true);

			temp = get<0>(res);

			def.insert(temp.begin(), temp.end());

			temp = get<1>(res);

			ref.insert(temp.begin(), temp.end());

			res = computeTypeOfNode(t, false);

			temp = get<1>(res);

			ref.insert(temp.begin(), temp.end());

			DefTypes[*it] = def;
			RefTypes[*it] = ref;

		}

//		print_node(dump_file, "\nNodeType s\n", NodeType[s], 0);
//		print_node(dump_file, "\nNodeType t\n", NodeType[t], 0);
	}

	recordDataDependenceForGPUSet(gpus);
}

void GPG::recordDataDependence(struct cgraph_node *cnode, bool orig)
{
	#if  0 //PRINT_DATA
	fprintf(dump_file, "\nInside recordDataDependence for Function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	GPUSet gpus = returnGPUs(cnode, orig);
	
	recordDataDependenceForGPUSet(gpus);

	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nEnd of recordDataDependence for Function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);
	#endif
}

void GPG::renumberGPBs(struct cgraph_node *cnode)
{
	if(isTop())
	{
		return;
	}

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	unsigned int gpb_count = 1;
	GPB gpb;

	GPBSet gpbs, new_gpbs;
	unsigned int start, end;
	unsigned int new_start, new_end;

	start = getEntryGPB();
	end = getExitGPB();

	gpbs = getGPBs();

	std::map< unsigned int, unsigned int > gpb_old_new_id;
	std::map< unsigned int, GPB > new_gpb_map;
	std::map< unsigned int, GPUSet > rin, rout, brin, brout, ptsin, ptsout;

	unsigned int x, y;
	GPBSet preds, succs;
	GPUSet gpus;

	GPG res;
	stmt_info_type key_t, key;
	GPBSet sset, temp_sset;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb_old_new_id[*it] = gpb_count;

		if(*it == start)
		{
			new_start = gpb_count;
		}

		if(*it == end)
		{
			new_end = gpb_count;
		}

		new_gpbs.insert(gpb_count);

		gpb = gpb_map[*it];

		gpb.setId(gpb_count);

		new_gpb_map[gpb_count] = gpb;

		gpus = gpb.getGPUs();

		for(GPUSet::iterator rit = gpus.begin(); rit != gpus.end(); rit++)
		{
			key_t = std::make_tuple(cnode_num, *it, *rit); 

			temp_sset = stmt_id_info[key_t];

//			stmt_id_info.erase(key_t);

			key = std::make_tuple(cnode_num, gpb_count, *rit);

			sset = stmt_id_info[key];

			sset.insert(temp_sset.begin(), temp_sset.end());

			stmt_id_info[key] = sset;
		}

		rin[gpb_count] = RIN[*it];
		brin[gpb_count] = BRIN[*it];

		#if BLOCKING
		rout[gpb_count] = ROUT[*it];
		brout[gpb_count] = BROUT[*it];
		#endif

		gpb_count++;
	}

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		x = gpb_old_new_id[*it];

		preds = getPrev(*it);
		succs = getNext(*it);

		for(GPBSet::iterator pit = preds.begin(); pit != preds.end(); pit++)
		{
			y = gpb_old_new_id[*pit];

			res.addPrev(x, y);
		}

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			y = gpb_old_new_id[*sit];

			res.addNext(x, y);
		}
	}

	res.setEntryGPB(new_start);
	res.setExitGPB(new_end);
	res.setGPBs(new_gpbs);
	res.gpb_map = new_gpb_map;
	res.GPB_count = gpb_count;
	res.RIN = rin;
	res.ROUT = rout;
	#if BLOCKING
	res.BRIN = brin;
	res.BROUT = brout;
	#endif

	#if 0
	res.RIN = rin;
	res.BRIN = brin;
	res.ROUT = rout;
	res.BROUT = brout;
	res.PTSIN = ptsin;
	res.PTSOUT = ptsout;
	#endif

	#if 0
	if(res.checkGPGStructure(cnode, false))
	{
		fprintf(dump_file,"\nHigh Alert after renumbering of GPBs\n");
		fflush(dump_file);
		printGPG(cnode);
		fflush(dump_file);
		exit(1);
	}	
	#endif

//	*this = res;

	this->gpbs = res.gpbs;
	this->entry = res.entry;
	this->end = res.end;
	this->gpb_map = res.gpb_map;
	this->GPB_count = res.GPB_count;

	this->RIN = res.RIN;
	this->BRIN = res.BRIN;
	this->ROUT = res.ROUT;
	this->BROUT = res.BROUT;

	this->preds = res.preds;
	this->succs = res.succs;

	this->top = res.top;
	this->back_edges = res.back_edges;
}

bool checkDataDependenceForCoalescing(GPUSet in, GPUSet gen)
{
	GPUSet temp;
	set_tree_nodes tree_nodes;

	for(GPUSet::iterator it = gen.begin(); it != gen.end(); it++)
	{
		GPUSet res;

		#if 0
		// Special Case for Array Types for Coalescing

		tree_nodes = DefTypes[*it];

		for(set_tree_nodes::iterator tit = tree_nodes.begin(); tit != tree_nodes.end(); tit++)
		{
			if(isArrayTree(*tit))
			{
				return true;
			}
		}
		// End of Special Case
		#endif

		temp = typeCompatibleGPUs[*it];

		set_intersection(temp.begin(), temp.end(), in.begin(), in.end(), inserter(res, res.end()));

		if(!res.empty())
		{
			return true;
		}
	}

	return false;
}

void GPG::computeBackEdges(struct cgraph_node *cnode)
{
	edge_set res;

	if(isTop())
	{
		setBackEdges(res);

		return;
	}

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPBSet gpbs, succs;

	gpbs = getGPBs();

	unsigned int size = gpbs.size();

	DFS_COUNT = size;

	std::map< unsigned int, bool > label;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		label[*it] = false;
	}

	LABEL_GPB[cnode_num] = label;

	unsigned int start = getEntryGPB();

	DFS(start, cnode);

	edge_type edge;

	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[cnode_num];

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		succs = getNext(*it);

		for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
		{
			if(dfs_gpb[*it] >= dfs_gpb[*sit])
			{
				edge = std::make_pair(*it, *sit);

				res.insert(edge);
			}
		}
	}

	setBackEdges(res);
}

#if 0
void GPG::identifyGPBsInLoop(struct cgraph_node *cnode)
{
	edge_set backedges = getBackEdges();
	unsigned int src, dest, current;
	GPB gpb;
	GPBSet succs;
	GPBSet worklist;

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	std::map< unsigned int, unsigned int > dfs_gpb = DFS_GPB[cnode_num];

	for(edge_set::iterator it = backedges.begin(); it != backedges.end(); it++)
	{
		GPBSet loop;

		src = get<0>(*it);
		dest = get<1>(*it);

		loop.insert(src);			
		loop.insert(dest);			

		worklist.insert(dest);

		while(!worklist.empty())
		{
			current = *(worklist.begin());

			worklist.erase(current);

			succs = getNext(current);

			for(GPBSet::iterator sit = succs.begin(); sit != succs.end(); sit++)
			{
				if(dfs_gpb[*it] >= dfs_gpb[*sit])
				{
					continue;
				}	

				if(loop.find(*sit) == loop.end())
				{
					loop.insert(*sit);
					worklist.insert(*sit);
				}
			}
		}
	}
}
#endif

#if DATA_MEAS
std::tuple< unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int > GPG::returnAllTypesOfGPUs(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	std::tuple< unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int > result;

	if(isTop())
	{
		result = std::make_tuple(0, 0, 0, 0, 0, 0, 0, 0);

		return result;
	}

	GPUSet gpus;
	gpus = returnGPUs(cnode, false);

	unsigned int total_gpus = 0;
	unsigned int scalar_gpus = 0;
	unsigned int fi_gpus = 0;
	unsigned int ci_gpus = 0;
	unsigned int ci_fi_gpus = 0;
	unsigned int use_gpus = 0;
	unsigned int ind_gpus = 0;
	unsigned int func_gpus = 0;

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		if(isBoundaryGPU(*it))
		{
			continue;
		}
	
		total_gpus++;

		if(isStackGPU(*it))
		{
			scalar_gpus++;
		}

		if(isPointstoEdge(*it))
		{
			ci_gpus++;
		}

		if(isUseGPU(*it))
		{
			use_gpus++;
		}

		if(isIndirectGPU(*it))
		{
			ind_gpus++;
		}

		if(is_function_pointer_var(get<0>(get<0>(*it))))
		{
			func_gpus++;
		}
	}

	U_GPUs.insert(gpus.begin(), gpus.end());

	GPUSet res_p, res_np;
	GPUSet temp;

	std::map< unsigned int, GPUSet > fip = FIP[cnode_num];
	std::map< unsigned int, GPUSet > finp = FINP[cnode_num];

	for(std::map< unsigned int, GPUSet >::iterator it = fip.begin(); it != fip.end(); it++)
	{
		temp = it->second;

		res_p.insert(temp.begin(), temp.end());
	}

	for(std::map< unsigned int, GPUSet >::iterator it = finp.begin(); it != finp.end(); it++)
	{
		temp = it->second;

		res_np.insert(temp.begin(), temp.end());
	}

	U_FI_GPUs.insert(res_p.begin(), res_p.end());
	U_FI_GPUs.insert(res_np.begin(), res_np.end());

	U_FIP_GPUs.insert(res_p.begin(), res_p.end());

	fi_gpus = res_p.size() + res_np.size();
	ci_fi_gpus = res_p.size();

	result = std::make_tuple(total_gpus, ci_gpus, scalar_gpus, ind_gpus, use_gpus, fi_gpus, ci_fi_gpus, func_gpus);

	return result;
}

void printStatistics(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPG i_gpg = Initial_GPG_map[cnode_num];
	GPG iae_gpg = GPG_map[cnode_num];

	GPG c_gpg = Call_GPG_map[cnode_num]; 
	GPG o_gpg = optimized_GPG_map[cnode_num]; 
//	GPG o_gpg = partial_optimized_GPG_map[cnode_num];

	if(o_gpg.isTop())
	{
		fprintf(dump_file, "\nTop GPG\n");
	}

	std::tuple< unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int > result_i, result_iae, result_c, result_o;

	unsigned int g_count_i, g_count_iae, g_count_c, g_count_o;
	unsigned int cf_count_i, cf_count_iae, cf_count_c, cf_count_o;

	unsigned int call_gpbs = 0;
	unsigned int empty_gpbs = 0;

	GPBSet gpbs;

	if(!i_gpg.isTop())
	{
		gpbs = i_gpg.getGPBs();
	}

	GPB gpb;
	GPUSet gpus;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		gpb = i_gpg.gpb_map[*it];

		if(gpb.isCallBlock() || gpb.isIndirectCallBlock())
		{
			call_gpbs++;

			continue;
		}

		gpus = gpb.getOrigGPUs();

		if(gpus.empty())
		{
			empty_gpbs++;
		}
	}

	g_count_i = gpbs.size();

	if(iae_gpg.isTop())
	{
		g_count_iae = 0;
	}
	else
	{
		g_count_iae = iae_gpg.getGPBs().size();
	}

	if(c_gpg.isTop())
	{
		g_count_c = 0;
	}
	else
	{
		g_count_c = c_gpg.getGPBs().size();
	}

	if(o_gpg.isTop())
	{
		g_count_o = 0;
	}
	else
	{
		g_count_o = o_gpg.getGPBs().size();
	}

	cf_count_i = i_gpg.returnNumberOfControlFlowEdges(cnode);
	cf_count_iae = iae_gpg.returnNumberOfControlFlowEdges(cnode);
	cf_count_c = c_gpg.returnNumberOfControlFlowEdges(cnode);
	cf_count_o = o_gpg.returnNumberOfControlFlowEdges(cnode);

	result_i = i_gpg.returnAllTypesOfGPUs(cnode);
//	result_iae = iae_gpg.returnAllTypesOfGPUs(cnode);
	result_c = c_gpg.returnAllTypesOfGPUs(cnode);
	result_o = o_gpg.returnAllTypesOfGPUs(cnode);

	i_gpg.computeBackEdges(cnode);
//	iae_gpg.computeBackEdges(cnode);
	c_gpg.computeBackEdges(cnode);
	o_gpg.computeBackEdges(cnode);

	GPUSet q_gpus = Queued[cnode_num];

	fprintf(dump_file, "\nCFG Details of Function before Inlining %s; Number of BBs: %u, Number of PTR ASSIGNS: %u, Number of NON_PTR ASSIGNS: %u, CF Edges: %u, CFG after inlining; Number of BBs: %u, Number of PTR ASSIGNS: %u, Number of NON_PTR ASSIGNS: %u, CF Edges: %u, GPG Details; Queued GPU: %u, Initial GPG: GPB Count:%u, Call GPBs: %u, Empty GPBs: %u, CF Edges: %u, Back Edges: %u, GPU Details; Total GPUs: %u, CI GPUs: %u, Scalar GPUs: %u, Indirect GPUs: %u, Use GPUs: %u, FI GPUs: %u, CI FI GPUs: %u, FP GPUs: %u, Initial GPG After Empty GPB Elimination; GPB Count:%u, CF Edges: %u, After Call Inlining GPG: GPB Count:%u, CF Edges: %u, Back Edges: %u, GPU Details; Total GPUs: %u, CI GPUs: %u, Scalar GPUs: %u, Indirect GPUs: %u, Use GPUs: %u, FI GPUs: %u, CI FI GPUs: %u, FP GPUs: %u, Optimized GPG: GPB Count:%u, CF Edges: %u, Back Edges: %u, GPU Details; Total GPUs: %u, CI GPUs: %u, Scalar GPUs: %u, Indirect GPUs: %u, Use GPUs: %u, FI GPUs: %u, CI FI GPUs: %u, FP GPUs: %u\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->num_bbs, ((function_info *)(cnode->aux))->num_stmts, ((function_info *)(cnode->aux))->num_nonptr_stmts, ((function_info *)(cnode->aux))->cf_edges, ((function_info *)(cnode->aux))->num_trans_bbs, ((function_info *)(cnode->aux))->num_trans_stmts, ((function_info *)(cnode->aux))->num_trans_nonptr_stmts, ((function_info *)(cnode->aux))->trans_cf_edges, q_gpus.size(), g_count_i, call_gpbs, empty_gpbs, cf_count_i, i_gpg.getBackEdges().size(), get<0>(result_i), get<1>(result_i), get<2>(result_i), get<3>(result_i), get<4>(result_i), get<5>(result_i), get<6>(result_i), get<7>(result_i), g_count_iae, cf_count_iae, g_count_c, cf_count_c, c_gpg.getBackEdges().size(), get<0>(result_c), get<1>(result_c), get<2>(result_c), get<3>(result_c), get<4>(result_c), get<5>(result_c), get<6>(result_c), get<7>(result_c), g_count_o, cf_count_o, o_gpg.getBackEdges().size(), get<0>(result_o), get<1>(result_o), get<2>(result_o), get<3>(result_o), get<4>(result_o), get<5>(result_o), get<6>(result_o), get<7>(result_o));
}

void printPointsToInformationStatistics(struct cgraph_node *cnode)
{
	unsigned int i = 0;

	GPUSet gpus;
	constraint_t con;

	for(; i < VEC_length(constraint_t, aliases); i++)
	{
		gpus = PTS_INFO[i+1];

		con = VEC_index(constraint_t, aliases, i);

		unsigned int d_size = 0;
		GPUSet f_gpus;

		for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
		{
			if(isPointstoInformation(*it))
			{
				#if PRINT_DATA
				f_gpus.insert(*it);
				#endif

				d_size++;
			}	
		}

		if(con)
		{
			if(con->lhs.type == DEREF)
			{
					
				fprintf(dump_file, "\nDeref Present for Stmt ID %d, Number of GPUs = %d\n", i, d_size);
		
				#if 0 //PRINT_DATA
				print_constraint(con);
				fprintf(dump_file, "\nGPUs\n");
				printSetOfGPUs(f_gpus);
				#endif

				continue;
			}
		}
				
		fprintf(dump_file, "\nDeref Absent for Stmt ID %d, Number of GPUs = %d\n", i, d_size);
			
		#if 0 //PRINT_DATA
		print_constraint(con);
		fprintf(dump_file, "\nGPUs\n");
		printSetOfGPUs(f_gpus);
		#endif
	}
} 

void printFIPointsToInformationStatistics(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	
	GPUSet gpus;

	gpus = FI_DATA_FI_ANALYSIS[cnode_num];	

	UFICS.insert(gpus.begin(), gpus.end());

	fprintf(dump_file, "\nFI PTS DATA: Number of GPUs = %d\n", gpus.size());
}

void printData()
{
	struct cgraph_node *cnode;

	unsigned int cnode_num;

	fprintf(dump_file, "\nProcedure Count %d\n", num_procs);

	#if !FI_ANALYSIS && !CI_ANALYSIS
	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		cnode_num = ((function_info *)(cnode->aux))->func_num;

		printStatistics(cnode);
		
		pop_cfun();
	}

	printPointsToInformationStatistics(main_cnode);

	fprintf(dump_file, "\nExported Definitions = %d\n", exportedDef.size());
	fprintf(dump_file, "\nImported Uses = %d\n", importedUse.size());

	fprintf(dump_file, "\nUnique FIP GPUs = %d\n", U_FIP_GPUs.size());
	fprintf(dump_file, "\nUnique Total FI GPUs = %d\n", U_FI_GPUs.size());
	fprintf(dump_file, "\nUnique FS GPUs = %d\n", U_GPUs.size());
	#endif

	#if FI_ANALYSIS && !CI_ANALYSIS
	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		cnode_num = ((function_info *)(cnode->aux))->func_num;

		printFIPointsToInformationStatistics(cnode);

		pop_cfun();
	}

	fprintf(dump_file, "\nUnique FICS GPUs = %d\n", UFICS.size());
	#endif

	#if FI_ANALYSIS && CI_ANALYSIS
	printFIPointsToInformationStatistics(main_cnode);
	#endif
}
#endif

void flowContextInsensitiveAnalysis()
{
	GPUSet res, temp;

	unsigned int i = 0;

	GPUSet gpus;
	constraint_t con;

	struct cgraph_node *cnode;
	basic_block bb;
	unsigned int stmt_id;
	bool use;
	it ai;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		FOR_EACH_BB(bb)
		{
			constraint_list & cons_list = ((block_information *)(bb->aux))->get_list();

			for(ai = cons_list.begin(); ai != cons_list.end(); ai++)
			{
				stmt_id = (*ai).get_int();
				use = (*ai).get_bool();

				temp = resolve_constraint_SSA(stmt_id, bb, cnode, use);

				res.insert(temp.begin(), temp.end());
			}
		}	
		
		pop_cfun();
	}

	GPUSet worklist;
	worklist = res;

	GPUSet result;
	gpu_id_type id;
	
	while(!worklist.empty())
	{
		GPUSet delta;

		id = *(worklist.begin());

		result.insert(id);

		delta.insert(id);		

		temp = RGen(worklist, delta, main_cnode, 0);

		worklist.erase(id);

		for(GPUSet::iterator it = temp.begin(); it != temp.end(); it++)
		{
			if(*it == id)
			{
				result.insert(*it);

				continue;
			}

			worklist.insert(*it);
			result.insert(*it);
		}
	}

	unsigned int main_cnode_num = ((function_info *)(main_cnode->aux))->func_num;

	FI_DATA_FI_ANALYSIS[main_cnode_num] = result;	
}

void flowInsensitiveContextSensitiveAnalysis(struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;
	unsigned int callee_num;

	basic_block bb;

	GPUSet gpus, temp;
	struct cgraph_node *callee;	
	it ai;
	bool use;
	unsigned int stmt_id;

	FOR_EACH_BB(bb)
	{
		if(((block_information *)(bb->aux))->call_block)
		{
			gimple stmt = bb_call_stmt(bb);
			tree decl = get_called_fn_decl(stmt);

			if(TREE_CODE(decl) == FUNCTION_DECL)
			{
				callee =  cgraph_get_node(decl);

				callee_num = ((function_info *)(callee->aux))->func_num;

				temp = FI_DATA_FI_ANALYSIS[callee_num];

				gpus.insert(temp.begin(), temp.end());
			}
		}
		else
		{
			constraint_list & cons_list = ((block_information *)(bb->aux))->get_list();

			for(ai = cons_list.begin(); ai != cons_list.end(); ai++)
			{
				stmt_id = (*ai).get_int();
				use = (*ai).get_bool();

				temp = resolve_constraint_SSA(stmt_id, bb, cnode, use);

				gpus.insert(temp.begin(), temp.end());
			}
		}
	}	

	GPUSet worklist;
	worklist = gpus;

	GPUSet result;
	gpu_id_type id;
	
	while(!worklist.empty())
	{
		GPUSet delta;

		id = *(worklist.begin());

		result.insert(id);

		delta.insert(id);		

		temp = RGen(worklist, delta, main_cnode, 0);

		worklist.erase(id);

		for(GPUSet::iterator it = temp.begin(); it != temp.end(); it++)
		{
			if(*it == id)
			{
				result.insert(*it);

				continue;
			}

			worklist.insert(*it);
			result.insert(*it);
		}
	}

	FI_DATA_FI_ANALYSIS[cnode_num] = result;	
}

/*

GPG createArtificialGPG()
{
	FILE *gpb_list, gpb_rel, gpb_contents;
	char i, r, g;
	unsigned int gpb_i, gpb_r1, gpb_r2;
	unsigned int gpu_s, gpu_d, gpu_ind;

	gpb_list = fopen("gpb-list.txt","r");
	gpb_rel = fopen("gpb-rel.txt","r");
	gpb_contents = fopen("gpb-contents.txt","r");

	unsigned count1 = 0;

	GPG gpg;

	while((i=fgetc(gpb_list))!=EOF)
	{
		printf("%c",i);
		
		gpb_i = atoi(i);

		count1 = 0;

		GPBSet preds, succs;

		char str[999];
		char gpu_info[999];

		printf("\nGPB %d\n", gpb_i);

		while (fscanf(gpb_rel, "%s", str)!=EOF)
		{
			gpb_r1 = atoi(str[0]);	
			gpb_r2 = atoi(str[1]);	

			if(count1 == 0 && gpb_i == gpb_r1)
			{
				succs.insert(gpb_r2);
				
				printf("\nSuccessor of %d is %d\n", gpb_i, gpb_r2);
			}
			else if(count1 > 0 && gpb_i == gpb_r2)
			{
				preds.insert(gpb_r1);
				
				printf("\nPredecessor of %d is %d\n", gpb_i, gpb_r1);
			}

			count1++;
		}	

		while (fscanf(gpb_contents, "%s", gpu_info)!=EOF)
		{
			gpb_r1 = atoi(gpu_info[0]);

			if(gpb_i == gpb_r1)
			{
				gpu_s = atoi(gpu_info[1]);
				gpu_d = atoi(gpu_info[2]);

				printf("%d, %d\n", gpu_s, gpu_d);
			}
		}	
	}

	fclose(gpb_list);
	fclose(gpb_rel);
	fclose(gpb_contents);
}
*/


