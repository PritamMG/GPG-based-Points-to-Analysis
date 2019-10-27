#include "GPB.h"
#include "cgraph_node.hpp"
#include <set>
#include <vector>

using namespace std;

//long GPB_count = 1;

#if 0
std::map< unsigned int, std::map< unsigned int, GPUSet > > RIN;
std::map< unsigned int, std::map< unsigned int, GPUSet > > ROUT;
std::map< unsigned int, std::map< unsigned int, GPUSet > > BRIN;
std::map< unsigned int, std::map< unsigned int, GPUSet > > BROUT;

std::map< unsigned int, std::map< unsigned int, GPUSet > > PTSIN;
std::map< unsigned int, std::map< unsigned int, GPUSet > > PTSOUT;
#endif

std::map< unsigned int, std::map< unsigned int, GPBSet > > BB_START;
std::map< unsigned int, std::map< unsigned int, GPBSet > > BB_END;
std::map< unsigned int, std::map< unsigned int, GPBSet > > call_site_map; 

//std::map< unsigned int, GPB > GPB::gpb_map;

//std::map< unsigned int, std::map< unsigned int, GPB > > gpb_map; 

std::map< unsigned int, std::map< unsigned int, bool > > visited_map; 

std::map< unsigned int, std::map< unsigned int, GPBSet > > ori_red_map;

std::map< unsigned int, std::map< unsigned int, unsigned int > > visited_count;

GPBSet GPB::getSetOfCallees()
{
	return set_callees;
}

void GPB::setSetOfCallees(GPBSet s)
{
	set_callees = s;
}

bool GPB::isInterval()
{
	return interval;
}

void GPB::setInterval()
{
	interval = true;
}

void GPB::resetInterval()
{
	interval = false;
}

bool GPB::isIntervalDirect()
{
	return interval_direct;
}

void GPB::setIntervalDirect()
{
	interval_direct = true;
}

void GPB::resetIntervalDirect()
{
	interval_direct = false;
}

GPBSet GPB::getIntervalSet()
{
	return interval_set;
}

void GPB::setIntervalSet(GPBSet s)
{
	interval_set = s;
}

GPB GPB::deep_copy()
{
	GPB gpb;

	gpb.id = getId();
	gpb.type = getType();
	gpb.call_block = isCallBlock();
	gpb.callee = getCallee();
	gpb.indirect_call_block = isIndirectCallBlock();
	gpb.indirect_callees = getIndirectCallees();
	gpb.gpus = getGPUs();
	gpb.orig_gpus = getOrigGPUs();
	gpb.may_gpus = getMayGPUs();
	gpb.must_gpus = getMustGPUs();
	gpb.bb_index = getBBIndex();

	return gpb;
}

bool GPB::isCallBlock()
{
	return call_block;
}

bool GPB::isIndirectCallBlock()
{
	return indirect_call_block;
}

void GPB::setCallBlock()
{
	call_block = true;
}

void GPB::resetCallBlock()
{
	call_block = false;
}

bool GPB::isExitCallBlock()
{
	return exit_call_block;
}

void GPB::setExitCallBlock()
{
	exit_call_block = true;
}

void GPB::resetExitCallBlock()
{
	exit_call_block = false;
}

void GPB::setIndirectCallBlock()
{
	indirect_call_block = true;
}

void GPB::resetIndirectCallBlock()
{
	indirect_call_block = false;
}

unsigned int GPB::getCallee()
{
	return callee;
}

void GPB::setCallee(unsigned int c)
{
	callee = c;
}

definitions GPB::getIndirectCallees()
{
	return indirect_callees;
}

void GPB::setIndirectCallees(definitions callees)
{
	indirect_callees = callees;
}

void GPB::addIndirectCallee(node_id_type n)
{
	indirect_callees.insert(n);
}

unsigned int GPB::getId()
{
	return id;
}

void GPB::setId(unsigned int i)
{
	id  = i;
}

unsigned int GPB::getBBIndex()
{
	return bb_index;
}

void GPB::setBBIndex(unsigned int b)
{
	bb_index = b;
}
	
unsigned int GPB::getType()
{
	return type;
}

void GPB::setType(unsigned int t)
{
	type = t;
}

bool GPB::isStartGPB()
{
	return (type == 0);
}

bool GPB::isEndGPB()
{
	return (type == 1);
}

bool GPB::isParaGPB()
{
	return (type == 2);
}

bool GPB::isReturnGPB()
{
	return (type == 3);
}

// BB Add element to the Set of GPUs in this GPB
void GPB::insertGPU(gpu_id_type gpu)
{
	gpus.insert(gpu);
}

void GPB::insertGPUOrig(gpu_id_type gpu)
{
	orig_gpus.insert(gpu);
}




// BB get gpus in the GPB
GPUSet GPB::getGPUs()
{
	return gpus;
}

void GPB::setGPUs(GPUSet g)
{
	gpus = g;
}

GPUSet GPB::getOrigGPUs()
{
	return orig_gpus;
}

void GPB::setOrigGPUs(GPUSet o)
{
	orig_gpus = o;
}

// BB get may gpus in the GPB
GPUSet GPB::getMayGPUs()
{
	return may_gpus;
}

void GPB::setMayGPUs(GPUSet g)
{
	may_gpus = g;
}

// BB get must gpus in the GPB
GPUSet GPB::getMustGPUs()
{
	return must_gpus;
}

void GPB::setMustGPUs(GPUSet g)
{
	must_gpus = g;
}

bool GPB::isInitialEmpty()
{
	if(isCallBlock())
	{
		return false;
	}

	if(isInterval())
	{
		return false;
	}

	if(isIndirectCallBlock())
	{
		return false;
	}

	GPUSet gpus = getOrigGPUs();

	if(gpus.empty())
		return true;

	return false;
}

bool GPB::isEmpty()
{
	if(isCallBlock())
	{
		return false;
	}

	if(isInterval())
	{
		return false;
	}

	if(isIndirectCallBlock())
	{
		return false;
	}

	GPUSet gpus = getGPUs();

	if(gpus.empty())
		return true;

	return false;
}

void GPB::printGPB(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	unsigned int id = getId();
	unsigned int type = getType();
	unsigned int empty_preds = 0, empty_succs = 0;
	GPB gpb;

	#if 0
	fprintf(dump_file, "\nGPB %d\n", id);	
	fflush(dump_file);
	#endif

	if(isSymGPB())
	{
//		fprintf(dump_file, "\nCase 1 %d\n", getCallee());	
//		fflush(dump_file);

		struct cgraph_node *callee = func_numbering[getCallee()];

		fprintf(dump_file, "\nSymGPB Call Block -- Callee %s\n", cgraph_node_name(callee));
	}
	else if(isCallBlock())
	{
//		fprintf(dump_file, "\nCase 2\n");	
//		fflush(dump_file);

		struct cgraph_node *callee = func_numbering[getCallee()];

		fprintf(dump_file, "\nDirect Call Block -- Callee %s\n", cgraph_node_name(callee));

		return;
	}
	else if(isIndirectCallBlock())
	{
//		fprintf(dump_file, "\nCase 3\n");	
//		fflush(dump_file);

		fprintf(dump_file, "\nIndirect Call Block\n");
		printDefinitions(getIndirectCallees());

		return;
	}

	GPUSet gpus = getGPUs();

	fprintf(dump_file, "\n\nList of GPUs\n");	

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		print_GPU(*it);
	}

	fprintf(dump_file, "\n");
}

void GPB::printInitialGPB(struct cgraph_node *cnode)
{
	unsigned int caller_rep = ((function_info *)(cnode->aux))->func_num;

	unsigned int id = getId();
	unsigned int type = getType();
	unsigned int empty_preds = 0, empty_succs = 0;
	GPB gpb;

//	fprintf(dump_file, "\nGPB %d\n", id);

	if(isSymGPB())
	{
		struct cgraph_node *callee = func_numbering[getCallee()];

		fprintf(dump_file, "\nSymGPB Call Block -- Callee %s\n", cgraph_node_name(callee));
	}
	else if(isCallBlock())
	{
		struct cgraph_node *callee = func_numbering[getCallee()];

		fprintf(dump_file, "\nDirect Call Block -- Callee %s\n", cgraph_node_name(callee));

		return;
	}
	else if(isInterval())
	{
		fprintf(dump_file, "\nInterval\n");
		print_set_integers(getIntervalSet());

		return;
	}
	else if(isIndirectCallBlock())
	{
		fprintf(dump_file, "\nIndirect Call Block\n");
		printDefinitions(getIndirectCallees());

		return;
	}

	GPUSet gpus = getOrigGPUs();

	fprintf(dump_file, "\n\nList of GPUs\n");	

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		print_GPU(*it);
	}

	fprintf(dump_file, "\n");
}

void printGPBList(GPBList list)
{
	for(GPBList::iterator it = list.begin(); it != list.end(); it++)
	{
		fprintf(dump_file, "%d\t", *it);
	}

	fprintf(dump_file, "\n\n");
}

bool GPB::isDirty()
{
	return dirty;
}

void GPB::setDirty()
{
	dirty = true;
}

void GPB::resetDirty()
{
	dirty = false;
}

bool GPB::isSymGPB()
{
	return sym_gpb;
}

void GPB::setSymGPB()
{
	sym_gpb = true;
}

void GPB::resetSymGPB()
{
	sym_gpb = false;
}

bool GPB::isResolved()
{
	return resolved;
}

void GPB::setResolved()
{
	resolved = true;
}

void GPB::resetResolved()
{
	resolved = false;
}
