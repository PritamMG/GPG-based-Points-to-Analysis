//#include "GPU.h"
#include "GPB.h"
#include "cgraph_node.hpp"
#include <string>

using namespace std;
using namespace std::tr1;

std::set< unsigned int > escaped;

std::map< unsigned int, std::map< unsigned int, GPUSet > > GPG_GPUs_map;

std::map< gpu_id_type, bool > ptr_arith_map;
//std::map< unsigned int, bool > ptr_arith_map;
std::map< unsigned int , GPUSet > PTS_INFO;
std::map< unsigned int, GPUSet > flowInsensitiveInformation;
std::map< unsigned int, std::map< unsigned int, GPUSet > > FIP;
std::map< unsigned int, std::map< unsigned int, GPUSet > > FINP;

std::map< unsigned int, GPUSet > Queued;

std::map< gpu_key_type, unsigned int > gpu_key;

std::map< unsigned int, GPUSet > FI_DATA_FI_ANALYSIS;

std::map< node_id_type, set_tree_nodes > NodeType;

std::map< gpu_id_type, set_tree_nodes > DefTypes;
std::map< gpu_id_type, set_tree_nodes > RefTypes;

GPUSet exportedDef, importedUse;

std::map< stmt_info_type, set< unsigned int > > stmt_id_info;

bool ptr_arith;

std::map< key_for_il, std::vector< Node > > NodeMap;

std::map< gpu_id_type, GPU > GPU::gpu_map;

std::map< gpu_id_type, GPUSet > typeCompatibleGPUs;

GPUSet queued_temp;

definitions visitedNodes, visitedFINodes;

unsigned int Node::getVarIndex()
{
	return var_index;
}
	
void Node::setVarIndex(unsigned int v)
{
	var_index = v;
}

IndirectionList Node::getList()
{
	return list;
}

void Node::setList(IndirectionList l)
{
	list = l;
}

node_id_type Node::getNodeID() const
{
	return node_id;
}
	
void Node::setNodeID(node_id_type n)
{
	node_id = n;
}

void Node::insertNodeInMap()
{
	unsigned int var = getVarIndex();

	IndirectionList l = getList();
	IndirectionList m;

	Node temp_node;
	unsigned int length = l.Length();

	key_for_il key = make_pair(var, length);

	std::vector< Node > temp_nodes = NodeMap[key];
	unsigned int index = 0;
	bool found = false;

//	fprintf(dump_file,"\nKey %d, %d %d\n", get<0>(key), get<1>(key), temp_nodes.size());

	for(std::vector< Node >:: iterator it = temp_nodes.begin(); it != temp_nodes.end(); it++)
	{
		temp_node = *it;

		m = temp_node.getList();

		if(l.isEqual(m)) // == temp_node.getList())
		{
//			fprintf(dump_file,"\nGotcha\n");
			found = true;
			break;
		}

		index++;	
	}

	if(!found)
	{
		index = temp_nodes.size();

//		fprintf(dump_file, "\nIndex %d\n", index);
	
		node_id_type id = std::make_tuple(var, length, index);

		setNodeID(id);

//		printNodeID();

		temp_nodes.push_back(*this);

		NodeMap[key] = temp_nodes;	

	}
	else
	{
//		fprintf(dump_file, "\nIndex %d\n", index);
	
		node_id_type id = std::make_tuple(var, length, index);

		setNodeID(id);

//		printNodeID();
	}
}

bool Node::operator==(const Node &n) const
{
	#if 0
	node_id_type node1, node2;

	node1 = getNodeID();
	node2 = n.getNodeID();

	if(get<0>(node1) == get<0>(node2) && get<1>(node1) == get<1>(node2))	
		return true;

	return false;
	#endif

	#if 1
	if(getNodeID() == n.getNodeID())
		return true;

	return false;
	#endif

	#if 0
	if(n1.getVarIndex() == n2.getVarIndex())
	{
		if(n1.getList() == n2.getList())
		{
			if(n1.getNodeID() == n2.getNodeID())
			{
				return true;
			}
		}
	}

	return false;
	#endif
}

Node getNode(node_id_type n)
{
	unsigned int var = get<0>(n);
	unsigned int length = get<1>(n);
	unsigned int index= get<2>(n);

	key_for_il key = make_pair(var, length);

	std::vector< Node > temp_nodes = NodeMap[key];

	return temp_nodes[index];
}

void Node::printNode()
{
	unsigned int var = getVarIndex();
	IndirectionList il = getList();

	fprintf(dump_file, "\nPrinting Node: Var %s (%d)\nIndirectionList: ", get_var_name(var), var);
	il.printIndirectionList();
	fprintf(dump_file, "\n\n");
//	printNodeID();
}

void Node::printNodeID()
{
	node_id_type n = getNodeID();

	fprintf(dump_file, "\nNode ID: %d, %d, %d\n", get<0>(n), get<1>(n), get<2>(n));
}

void print_NodeID(node_id_type n)
{
	Node node = getNode(n);

	node.printNode();
	fprintf(dump_file, "\nNode ID: %d, %d, %d\n", get<0>(n), get<1>(n), get<2>(n));
}

void printSetofNodeIDs(setOfNodes s)
{
	Node n;

	for(setOfNodes::iterator it = s.begin(); it != s.end(); it++)
	{
		n = getNode(*it);
		n.printNode();
	}
}

void printListofNodeIDs(listOfNodes l)
{
	Node n;

	for(listOfNodes::iterator it = l.begin(); it != l.end(); it++)
	{
		n = getNode(*it);
		n.printNodeID();
	}
}

void printSetofNodes(setOfNodes s)
{
	Node n;

	for(setOfNodes::iterator it = s.begin(); it != s.end(); it++)
	{
		n = getNode(*it);
		n.printNode();
	}
}

void printListofNodes(listOfNodes l)
{
	Node n;

	for(listOfNodes::iterator it = l.begin(); it != l.end(); it++)
	{
		n = getNode(*it);
		n.printNode();
	}
}

int getLengthOfList(node_id_type n_id)
{
	Node n = getNode(n_id);

	return n.getList().Length();
}

Node Node::conDep()
{
	unsigned int var = getVarIndex();

	if(var <= 4)
		return *this;

	if(CDV.find(var) != CDV.end())
	{
		return *this;
	}	
	else
	{
		IndirectionList list = getList();
		Node nt(var+1, list);

		return nt;
	}
}

GPU::GPU(Node s, Node t)
{
	node_id_type s_id, t_id;

	s_id = s.getNodeID();
	t_id = t.getNodeID();

	src = s_id;
	tgt = t_id;

	gpu_id_type id = std::make_tuple(s_id, t_id);

	setGPUID(id);

	gpu_map[id] = *this;
}

GPU::GPU(node_id_type s, node_id_type t)
{
	src = s;
	tgt = t;

	gpu_id_type id = std::make_tuple(s, t);

	setGPUID(id);

	gpu_map[id] = *this;
}


// == operator overloading
bool GPU::operator==(const GPU &gpu) const
{
	#if 0
	gpu_id_type g1, g2;
	g1 = getGPUID();
	g2 = gpu.getGPUID();

	if((get<0>(g1) == get<0>(g2)) && (get<1>(g1) == get<1>(g2)))
	{
		return true;
	}

	return false;
	#endif

	if(getGPUID() == gpu.getGPUID())
	{
		return true;
	}

	return false;

	#if 0
	return  ((getSource() == gpu.getSource()) &&
                (getTarget() == gpu.getTarget()) &&
                ((getStmtNum()) == gpu.getStmtNum()));
	#endif
}

gpu_id_type GPU::getGPUID() const
{
	return gpu_id;
}

void GPU::setGPUID(gpu_id_type g)
{
	gpu_id = g;
}

// get source and target
node_id_type GPU::getSource()
{
	return src;
}
	
void GPU::setSource(node_id_type s)
{
	src = s;
}

unsigned int GPU::getSourceVar()
{
	return get<0>(src);
}
	
IndirectionList GPU::getSourceList()
{
	return getNode(src).getList();
}

node_id_type GPU::getTarget()
{
	return tgt;
}

void GPU::setTarget(node_id_type t)
{
	tgt = t;
}

unsigned int GPU::getTargetVar()
{
	return get<0>(tgt);
}

IndirectionList GPU::getTargetList()
{
	return getNode(tgt).getList();
}

// get stmtnum
unsigned int GPU::getStmtNum()
{
	return stmt_num;
}

void GPU::setStmtNum(unsigned int s)
{
	stmt_num = s;
}

void GPU::printGPU()
{
	fprintf(dump_file,"\nSource %s (%d): ", get_var_name(getSourceVar()), getSourceVar());
	getSourceList().printIndirectionList();
	fprintf(dump_file,", Target %s (%d): ", get_var_name(getTargetVar()), getTargetVar());
	getTargetList().printIndirectionList();
//	fprintf(dump_file,", Stmt: %d\n\n", getStmtNum());

		
	#if 0
	fprintf(dump_file,"\nPrinting GPU\nSource %s (%d)\nIndirection List: ", get_var_name(getSourceVar()), getSourceVar());
	getSourceList().printIndirectionList();

	fprintf(dump_file,"\nTarget %s (%d)\nIndirection List: ", get_var_name(getTargetVar()), getTargetVar());
	getTargetList().printIndirectionList();

	fprintf(dump_file,"\nStatement Number %d\n", getStmtNum());
	#endif
}

definitions SSComposition(node_id_type n_id, gpu_id_type p_id)
{
	definitions res, new_nodes;

//	if(isPivotPresent(n_id, p_id))
	{
//		fprintf(dump_file, "\nPivot Present\n");

		if(isValidSSComposition(n_id, p_id))
		{
//			fprintf(dump_file, "\nValid Composition\n");

			if(isDesirableComposition(n_id, p_id))
			{
//				fprintf(dump_file, "\nDesirable Composition\n");

				IndirectionList src_list_n = getNode(n_id).getList();
				IndirectionList src_list_p = getNode(get<0>(p_id)).getList();

				IndirectionList dest_list_p = getNode(get<1>(p_id)).getList();

				std::vector< IndirectionList > rem, fin;

				rem = src_list_n.remainder(src_list_p);

				fin = dest_list_p.append_list(rem);

				unsigned int new_src;
				new_src = get<0>(get<1>(p_id));

				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					new_nodes = getAllNodes(new_src, *it);

					res.insert(new_nodes.begin(), new_nodes.end());
				}
			}
		}
	}

	return res;
}

definitions TSComposition(node_id_type n_id, gpu_id_type p_id)
{
	definitions res, new_nodes;

//	if(isPivotPresent(n_id, p_id))
	{
//		fprintf(dump_file, "\nPivot Present\n");

		if(isValidTSComposition(n_id, p_id))
		{
//			fprintf(dump_file, "\nValid Composition\n");

			if(isDesirableComposition(n_id, p_id))
			{
//				fprintf(dump_file, "\nDesirable Composition\n");
	
				IndirectionList src_list_p = getNode(get<0>(p_id)).getList();

				IndirectionList dest_list_n = getNode(n_id).getList();
				IndirectionList dest_list_p = getNode(get<1>(p_id)).getList();

				std::vector< IndirectionList > rem, fin;

				rem = dest_list_n.remainder(src_list_p);

				fin = dest_list_p.append_list(rem);

				unsigned int new_tgt;
				new_tgt = get<0>(get<1>(p_id));

				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					new_nodes = getAllNodes(new_tgt, *it);
				
					res.insert(new_nodes.begin(), new_nodes.end());	
				}
			}
		}
	}

	return res;
}


GPUSet ss_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	GPUSet res;
	definitions new_nodes;

	if(is_pivot_present_ss_composition(c_id, p_id))
	{
		if(is_valid_ss_composition(c_id, p_id))
		{
			if(is_desirable_ss_composition(c_id, p_id))
			{
				IndirectionList src_list_n = getNode(get<0>(c_id)).getList();
				IndirectionList src_list_p = getNode(get<0>(p_id)).getList();

				IndirectionList dest_list_n = getNode(get<1>(c_id)).getList();
				IndirectionList dest_list_p = getNode(get<1>(p_id)).getList();

				std::vector< IndirectionList > rem, fin;

				rem = src_list_n.remainder(src_list_p);

				fin = dest_list_p.append_list(rem);

				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					unsigned int new_tgt, new_src;
					new_src = get<0>(get<1>(p_id));
					new_tgt = get<0>(get<1>(c_id));

					new_nodes = getAllNodes(new_src, *it);
					Node node;

					for(definitions::iterator dit = new_nodes.begin(); dit != new_nodes.end(); dit++)
					{
						node = getNode(*dit);

						GPU t_gpu(node.getNodeID(), get<1>(c_id));

						res.insert(t_gpu.getGPUID());	
					}
				}
			}
		}
	}

	return res;
}

GPUSet ts_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	GPUSet res;
	definitions new_nodes;

	if(is_pivot_present_ts_composition(c_id, p_id))
	{
		if(is_valid_ts_composition(c_id, p_id))
		{
			if(is_desirable_ts_composition(c_id, p_id))
			{
				IndirectionList src_list_n = getNode(get<0>(c_id)).getList();
				IndirectionList src_list_p = getNode(get<0>(p_id)).getList();

				IndirectionList dest_list_n = getNode(get<1>(c_id)).getList();
				IndirectionList dest_list_p = getNode(get<1>(p_id)).getList();

				std::vector< IndirectionList > rem, fin;

				rem = dest_list_n.remainder(src_list_p);

				fin = dest_list_p.append_list(rem);

				for(std::vector< IndirectionList >::iterator it = fin.begin(); it != fin.end(); it++)
				{
					unsigned int new_tgt, new_src;
					new_src = get<0>(get<0>(c_id));
					new_tgt = get<0>(get<1>(p_id));

					new_nodes = getAllNodes(new_tgt, *it);
					Node node;

					for(definitions::iterator dit = new_nodes.begin(); dit != new_nodes.end(); dit++)
					{		
						node = getNode(*dit);

						GPU t_gpu(get<0>(c_id), node.getNodeID());

						res.insert(t_gpu.getGPUID());	
					}
				}
			}
		}
	}

	return res;
}

bool isPivotPresent(node_id_type n_id, gpu_id_type p_id)
{
	unsigned int src_n, src_p;

	src_n = get<0>(n_id);
	src_p = get<0>(get<0>(p_id));

	return (src_n == src_p);
}

bool isValidSSComposition(node_id_type n_id, gpu_id_type p_id)
{
	IndirectionList src_list_n = getNode(n_id).getList();
	IndirectionList src_list_p = getNode(get<0>(p_id)).getList();

	return src_list_p.isProperPrefix(src_list_n);
}

bool isValidTSComposition(node_id_type n_id, gpu_id_type p_id)
{
	IndirectionList src_list_n = getNode(n_id).getList();
	IndirectionList src_list_p = getNode(get<0>(p_id)).getList();

	return src_list_p.isPrefix(src_list_n);
}

bool isDesirableComposition(node_id_type n_id, gpu_id_type p_id)
{
	bool st_hp;

	IndirectionList src_list_p = getNode(get<0>(p_id)).getList();
	IndirectionList tgt_list_p = getNode(get<1>(p_id)).getList();

	st_hp = src_list_p.get_st_hp();

	if(!st_hp)
		return true;

	return tgt_list_p.doesNotExceed(src_list_p);
}

bool is_pivot_present_ss_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	unsigned int src_n, src_p;

	src_n = get<0>(get<0>(c_id));
	src_p = get<0>(get<0>(p_id));

	return (src_n == src_p);
}

bool is_pivot_present_ts_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	unsigned int tgt_n, src_p;

	tgt_n = get<0>(get<1>(c_id));
	src_p = get<0>(get<0>(p_id));

	return (tgt_n == src_p);
}

bool is_valid_ss_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	IndirectionList src_list_n = getNode(get<0>(c_id)).getList();
	IndirectionList src_list_p = getNode(get<0>(p_id)).getList();

	return src_list_p.isProperPrefix(src_list_n);
}

bool is_valid_ts_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	IndirectionList dest_list_n = getNode(get<1>(c_id)).getList();
	IndirectionList src_list_p = getNode(get<0>(p_id)).getList();

	return src_list_p.isPrefix(dest_list_n);
}

bool is_desirable_ss_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	bool st_hp;

	IndirectionList src_list_p = getNode(get<0>(p_id)).getList();
	IndirectionList tgt_list_p = getNode(get<1>(p_id)).getList();

	st_hp = src_list_p.get_st_hp();

	if(!st_hp)
		return true;

	return tgt_list_p.doesNotExceed(src_list_p);
}

bool is_desirable_ts_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	bool st_hp;

	IndirectionList src_list_p = getNode(get<0>(p_id)).getList();
	IndirectionList tgt_list_p = getNode(get<1>(p_id)).getList();

	st_hp = src_list_p.get_st_hp();

	if(!st_hp)
		return true;

	return tgt_list_p.doesNotExceed(src_list_p);
}

bool undesComposition(bool type, node_id_type n_id, gpu_id_type p_id)
{
	if(isPivotPresent(n_id, p_id))
	{
		if(type)
		{
			if(isValidSSComposition(n_id, p_id))
			{
				if(!isDesirableComposition(n_id, p_id))
				{
					return true;
				}
			}
		}
		else
		{
			if(isValidTSComposition(n_id, p_id))
			{
				if(!isDesirableComposition(n_id, p_id))
				{
					return true;
				}
			}
		}
	}

	return false;
}

bool undes_ss_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	if(is_pivot_present_ss_composition(c_id, p_id))
	{
		if(is_valid_ss_composition(c_id, p_id))
		{
			if(!is_desirable_ss_composition(c_id, p_id))
			{
				return true;
			}
		}
	}

	return false;
}
bool undes_ts_composition(gpu_id_type c_id, gpu_id_type p_id)
{
	if(is_pivot_present_ts_composition(c_id, p_id))
	{
		if(is_valid_ts_composition(c_id, p_id))
		{
			if(!is_desirable_ts_composition(c_id, p_id))
			{
				return true;
			}
		}
	}

	return false;
}

bool isDataDependent(gpu_id_type c_id, gpu_id_type p_id)
{
	Node g_src, g_tgt;
	g_src = getNode(get<0>(c_id));
	g_tgt = getNode(get<1>(c_id));

	Node src, tgt;
	src = getNode(get<0>(p_id));
	tgt = getNode(get<1>(p_id));

	IndirectionList list1, list2;

	list1 = g_src.getList();
	list2 = src.getList();

	if((!(list1.get_st_hp())) && (!(list2.get_st_hp())))
	{
		return false;
	}

	if(g_src.getList().Length() >= 2 || g_tgt.getList().Length() >= 2 || src.getList().Length() >= 2 || tgt.getList().Length() >= 2)
	{
//		fprintf(dump_file, "\nIndList Length > 2\n");

		return true;
	}

	if(is_pivot_present_ss_composition(c_id, p_id) && is_valid_ss_composition(c_id, p_id))
	{
//		fprintf(dump_file, "\nPivot Exist and SS composition possible\n");

		return true;
	}

	if(is_pivot_present_ts_composition(c_id, p_id) && is_valid_ts_composition(c_id, p_id))
	{
//		fprintf(dump_file, "\nPivot Exist and TS composition possible\n");

		return true;
	}

//	fprintf(dump_file, "\nNo Data Dependency\n");

	return false;
}

definitions FIGPUComposition(bool type, node_id_type n_id, GPUSet fi, struct cgraph_node *cnode)
{
	definitions res, temp;

	if(type)
	{
		for(GPUSet::iterator it = fi.begin(); it != fi.end(); it++)
		{
			temp = SSComposition(n_id, *it);

			res.insert(temp.begin(), temp.end());
		}
	}
	else
	{
		for(GPUSet::iterator it = fi.begin(); it != fi.end(); it++)
		{
			temp = TSComposition(n_id, *it);

			res.insert(temp.begin(), temp.end());
		}
	}

	return res;
}

definitions NodeReduction(bool type, node_id_type n_id, GPUSet rin, GPUSet used, struct cgraph_node *cnode) // Source = 1, Target = 0
{
	#if PROFILING
	FUNBEGIN();
	#endif

	definitions res, temp;

	visitedNodes.insert(n_id);

	bool composed = false;

        // Base Condition

	if(type) // source
	{
		if(getLengthOfList(n_id) == 1)
		{
			res.insert(n_id);

			#if PROFILING
			RETURN(res);
			#else
			return res;
			#endif
		}
	}
	else
	{
		if(getLengthOfList(n_id) == 0)
		{
			res.insert(n_id);

			#if PROFILING
			RETURN(res);
			#else
			return res;
			#endif
		}
	}
	
	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nResolving Node n\n");
	print_NodeID(n_id);
	fprintf(dump_file, "\nSet used\n");
	printSetOfGPUs(used);	
	fprintf(dump_file, "\ncomposed %d\n", composed);
	#endif

	GPUSet R;
	set_difference(rin.begin(), rin.end(), used.begin(), used.end(), inserter(R, R.end()));
	GPUSet fi_data;
	definitions fi_temp;
	unsigned int var, n_var, t_var;

	n_var = get<0>(n_id);

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	for(GPUSet::iterator it = R.begin(); it != R.end(); it++)
	{
		definitions c_res;
		GPUSet temp_used;

		t_var = get<0>(get<0>(*it));

		if(n_var != t_var)
		{
			continue;
		}

//		fprintf(dump_file, "\nProducer GPU\n");
//		print_GPU(*it);

		if(type)
			c_res = SSComposition(n_id, *it);
		else
			c_res = TSComposition(n_id, *it);

//		fprintf(dump_file, "\nc_res\n");
//		printDefinitions(c_res);

		if(!c_res.empty())
		{
			temp_used = used;

			temp_used.insert(*it);

			#if 0 // PRINT_DATA
			fprintf(dump_file, "\nProducer GPU\n");
			print_GPU(*it);
			#endif
			
			#if DATA_MEAS
			exportedDef.insert(*it);
			#endif

			for(definitions::iterator cit = c_res.begin(); cit != c_res.end(); cit++)
			{
				#if 0
				var = get<0>(*cit);

//				visitedFINodes.clear();

				fi_data = FIP[cnode_num][var];

//				fi_temp = FINodeReduction(type, *cit, cnode);

				if(!fi_data.empty())
				{
					fi_temp = FIGPUComposition(type, *cit, fi_data, cnode);

					if(fi_temp.empty())
					{
						if(visitedNodes.find(*cit) == visitedNodes.end())
						{
//							fprintf(dump_file, "\nHey der\n");

							temp = NodeReduction(type, *cit, rin, temp_used, cnode);
				
							res.insert(temp.begin(), temp.end());
						}

						continue;
					}

//					fprintf(dump_file, "\nfi_temp\n");
//					printDefinitions(fi_temp);

					for(definitions::iterator fit = fi_temp.begin(); fit != fi_temp.end(); fit++)
					{
						if(visitedNodes.find(*fit) == visitedNodes.end())
						{
//							fprintf(dump_file, "\nHey der\n");

							temp = NodeReduction(type, *fit, rin, temp_used, cnode);
				
							res.insert(temp.begin(), temp.end());
						}
					}
				}
				else
				#endif
				{
					if(visitedNodes.find(*cit) == visitedNodes.end())
					{
//						fprintf(dump_file, "\nHey der\n");

						temp = NodeReduction(type, *cit, rin, temp_used, cnode);
				
						res.insert(temp.begin(), temp.end());
					}
				}
			}

			composed = true;
		}
	}

	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nResolved Node n\n");
	print_NodeID(n_id);
	fprintf(dump_file, "\nSet used\n");
	printSetOfGPUs(used);	
	fprintf(dump_file, "\ncomposed %d\n", composed);
	#endif

	if(!composed)
	{
		res.insert(n_id);
	}

//	fprintf(dump_file, "\nReturning Gen in NodeReduction\n");
//	printSetofNodeIDs(res);

	#if PROFILING
	RETURN(res);
	#else
	return res;
	#endif
}

definitions NodeReductionWB(bool type, node_id_type n_id, GPUSet rin, GPUSet brin, GPUSet used, struct cgraph_node *cnode) // Source = 1, Target = 0
{
	#if PROFILING
	FUNBEGIN();
	#endif

	definitions res, temp;

	visitedNodes.insert(n_id);

	bool composed = false;

        // Base Condition

	if(type) // source
	{
		if(getLengthOfList(n_id) == 1)
		{
			res.insert(n_id);

			#if PROFILING
			RETURN(res);
			#else
			return res;
			#endif
		}
	}
	else
	{
		if(getLengthOfList(n_id) == 0)
		{
			res.insert(n_id);
			
			#if PROFILING
			RETURN(res);
			#else
			return res;
			#endif
		}
	}
	
	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nResolving Node n\n");
	print_NodeID(n_id);
	fprintf(dump_file, "\nSet used\n");
	printSetOfGPUs(used);	
	fprintf(dump_file, "\nRIN\n");
	printSetOfGPUs(rin);	
	fprintf(dump_file, "\nBRIN\n");
	printSetOfGPUs(brin);	
	#endif

	GPUSet R;
	set_difference(rin.begin(), rin.end(), used.begin(), used.end(), inserter(R, R.end()));
	GPUSet fi_data;
	definitions fi_temp;
	unsigned int var, n_var, t_var;

	n_var = get<0>(n_id);

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	for(GPUSet::iterator it = R.begin(); it != R.end(); it++)
	{
		definitions c_res;
		GPUSet temp_used;

		t_var = get<0>(get<0>(*it));

//		fprintf(dump_file, "\nProducer GPU\n");
//		print_GPU(*it);

		if(n_var != t_var)
		{
			continue;
		}

		if(type)
			c_res = SSComposition(n_id, *it);
		else
			c_res = TSComposition(n_id, *it);

		if(!c_res.empty())
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nComposition is possible with RIN\n");
			fflush(dump_file);
			#endif
	
			if(brin.find(*it) != brin.end())
			{
				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nComposition is possible with RIN and is not blocked as p is present in BRIN\n");
				print_GPU(*it);
				fflush(dump_file);
				#endif
	
//				fprintf(dump_file, "\nNot Blocked\n");

				#if DATA_MEAS
				exportedDef.insert(*it);
				#endif

				temp_used = used;

				temp_used.insert(*it);

				for(definitions::iterator cit = c_res.begin(); cit != c_res.end(); cit++)
				{
					#if 0 
					var = get<0>(*cit);

					fi_data = FIP[cnode_num][var];

//					visitedFINodes.clear();
//					fi_temp = FINodeReduction(type, *cit, cnode);

					if(!fi_data.empty())
					{
						fi_temp = FIGPUComposition(type, *cit, fi_data, cnode);

						if(fi_temp.empty())
						{
							if(visitedNodes.find(*cit) == visitedNodes.end())
							{
								temp = NodeReductionWB(type, *cit, rin, brin, temp_used, cnode);
			
								res.insert(temp.begin(), temp.end());
							}	
	
							continue;
						}

						for(definitions::iterator fit = fi_temp.begin(); fit != fi_temp.end(); fit++)
						{
							if(visitedNodes.find(*fit) == visitedNodes.end())
							{
								temp = NodeReductionWB(type, *fit, rin, brin, temp_used, cnode);
			
								res.insert(temp.begin(), temp.end());
							}
						}
					}
					else
					#endif
					{
						if(visitedNodes.find(*cit) == visitedNodes.end())
						{
							temp = NodeReductionWB(type, *cit, rin, brin, temp_used, cnode);
			
							res.insert(temp.begin(), temp.end());
						}
					}
				}

				composed = true;
			}
			else
			{
				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nComposition is possible with RIN and is blocked as p is not present in BRIN\n");
				print_GPU(*it);
				fflush(dump_file);
				#endif
	
//				fprintf(dump_file, "\nBlocked\n");
				queued_temp.insert(*it);
			}
		}
		else
		{
			if(undesComposition(type, n_id, *it))
			{
//				fprintf(dump_file, "\nUndesirable SS Composition\n");

				queued_temp.insert(*it);
			}
		}
	}

	if(!composed)
	{
//		fprintf(dump_file, "Cannot Be Further Reduced\n");
//		print_NodeID(n_id);

		res.insert(n_id);
	}

	#if 0
	fprintf(dump_file, "\nReturning Gen in NodeReductionWB\n");
	printSetofNodeIDs(res);
	#endif

	#if PROFILING
	RETURN(res);
	#else
	return res;
	#endif
}

GPUSet GPUReduction(gpu_id_type c_id, GPUSet rin, struct cgraph_node *cnode) // Source = 1, Target = 0
{
	GPUSet gen, used_l, used_r;

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	definitions def, ref;
	gpu_id_type id;

	visitedNodes.clear();

	def = NodeReduction(true, get<0>(c_id), rin, used_l, cnode);	

	visitedNodes.clear();

	ref = NodeReduction(false, get<1>(c_id), rin, used_r, cnode);	

	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nPrinting Def\n");
	printSetofNodeIDs(def);
	fprintf(dump_file, "\nPrinting Ref\n");
	printSetofNodeIDs(ref);
	#endif

	if(def.empty() || ref.empty())
	{
		return gen;
	}

//	unsigned int stmt_id = get<2>(c_id);
	unsigned int src_var, dst_var;
	Node rhs;
	int f[IndirectionList::kSize];
	node_id_type nnid;

	IndirectionList list;
	IndirectionList elist1(true, 0, 0, f);
	IndirectionList elist2(false, 0, 0, f);

	for(definitions::iterator dit = def.begin(); dit != def.end(); dit++)
	{
		src_var = get<0>(*dit);

		if(src_var <= 3)
		{
			continue;
		}

		for(definitions::iterator rit = ref.begin(); rit != ref.end(); rit++)
		{
			if(*dit == *rit)
				continue;
		
			dst_var = get<0>(*rit);
			rhs = getNode(*rit);
			list = rhs.getList();

			nnid = *rit;

			if(dst_var <= 4 && list.Length() > 0)
			{
				if(list.get_st_hp())
				{
					Node new_node(dst_var, elist1);

					nnid = new_node.getNodeID();
				}
				else
				{
					Node new_node(dst_var, elist2);

					nnid = new_node.getNodeID();
				}
			}

			GPU gpu(*dit, nnid);

			gen.insert(gpu.getGPUID());
		}
	}

	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nGen in GPUReduction\n");
	printSetOfGPUs(gen);
	#endif

	return gen;
}

std::tuple< GPUSet, GPUSet > GPUReductionWB(gpu_id_type c_id, GPUSet rin, GPUSet brin, struct cgraph_node *cnode) // Source = 1, Target = 0
{
	GPUSet gen, used_l, used_r, queued, temp;

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	definitions def, ref;
	gpu_id_type id;

	std::tuple< GPUSet, GPUSet > res;

	queued_temp.clear();
	visitedNodes.clear();

	//def = NodeReduction(true, get<0>(c_id), rin, used_l);	
	def = NodeReductionWB(true, get<0>(c_id), rin, brin, used_l, cnode);	

//	queued.insert(queued_temp.begin(), queued_temp.end());
	
//	queued_temp.clear();
	visitedNodes.clear();

	//ref = NodeReduction(false, get<1>(c_id), rin, used_r);	
	ref = NodeReductionWB(false, get<1>(c_id), rin, brin, used_r, cnode);	

	queued.insert(queued_temp.begin(), queued_temp.end());

	if(def.empty() || ref.empty())
	{
		res = std::make_tuple(gen, queued);

		return res;
	}

//	unsigned int stmt_id = get<2>(c_id);

//	fprintf(dump_file, "\nLHS-Def\n");
//	printDefinitions(def);
//	fprintf(dump_file, "\nRHS-Ref\n");
//	printDefinitions(ref);

	unsigned int src_var, dst_var;
	Node rhs;
	int f[IndirectionList::kSize];
	node_id_type nnid;
	IndirectionList list;
	IndirectionList elist1(true, 0, 0, f);
	IndirectionList elist2(false, 0, 0, f);

	for(definitions::iterator dit = def.begin(); dit != def.end(); dit++)
	{
		src_var = get<0>(*dit);

		if(src_var <= 3)
		{
			continue;
		}

		for(definitions::iterator rit = ref.begin(); rit != ref.end(); rit++)
		{
			if(*dit == *rit)
				continue;

			dst_var = get<0>(*rit);
			rhs = getNode(*rit);
			list = rhs.getList();

			nnid = *rit;

			if(dst_var <= 4 && list.Length() > 0)
			{
				if(list.get_st_hp())
				{
					Node new_node(dst_var, elist1);

					nnid = new_node.getNodeID();
				}
				else
				{
					Node new_node(dst_var, elist2);

					nnid = new_node.getNodeID();
				}
			}

			GPU gpu(*dit, nnid);

			gen.insert(gpu.getGPUID());
		}
	}

	res =  std::make_tuple(gen, queued);

	return res;
}


bool isUseGPU(gpu_id_type gpu)
{
	if(get<0>(get<0>(gpu)) == summ_node_id)
	{
		return true;
	}
	
	return false;
}

bool isPointstoEdge(gpu_id_type gpu)
{
	IndirectionList s_list, d_list;

	s_list = getNode(get<0>(gpu)).getList();
	d_list = getNode(get<1>(gpu)).getList();

	if(s_list.Length() == 1 && d_list.Length() == 0)
	{
		return true;
	}

	return false;
}

bool isKLimited(gpu_id_type gpu)
{
	IndirectionList s_list, d_list;

	s_list = getNode(get<0>(gpu)).getList();
	d_list = getNode(get<1>(gpu)).getList();

	if(s_list.get_st_hp() && s_list.Length() == k_thresh)
	{
		return true;
	}

	if(d_list.get_st_hp() && d_list.Length() == k_thresh)
	{
		return true;
	}

	return false;
}

bool isPointstoInformation(gpu_id_type gpu)
{
	if(isKLimited(gpu) || isPointstoEdge(gpu))
	{
		return true;
	}

	unsigned int lvar = get<0>(get<0>(gpu));
	unsigned int rvar = get<1>(get<0>(gpu));

	csvarinfo_t vil = cs_get_varinfo (lvar);
	csvarinfo_t vir = cs_get_varinfo (rvar);

	if(vil)
	{
		if(vil->is_heap_var || vil->is_art_var)
		{
			IndirectionList s_list, d_list;

			s_list = getNode(get<0>(gpu)).getList();
			d_list = getNode(get<1>(gpu)).getList();

			if(s_list.Length() >= 1)
			{
				if(d_list.Length() == 0)
				{
					return true;
				}

				if(vir)
				{
					if(vil->is_heap_var || vil->is_art_var)
					{
						if(d_list.Length() >= 1)
						{
							return true;
						}
					}
				}
			}
		}
	}

	return false;
}

bool isBoundaryGPU(gpu_id_type bg)
{
	unsigned int rvar = get<0>(get<1>(bg));
	unsigned int lvar = get<0>(get<0>(bg));
	IndirectionList list1, list2;
	Node n1, n2;

	n1 = getNode(get<0>(bg));
	n2 = getNode(get<1>(bg));

	list1 = n1.getList();
	list2 = n2.getList();

	if(CDV.find(rvar) != CDV.end())
	{
		if(lvar == rvar-1)
		{
			if(list1.isEqual(list2))
			{
				return true;
			}
		}
	}

	return false;

//	return (get<0>(get<0>(bg))+1 == get<0>(get<1>(bg)));
}

bool isIndirectGPU(gpu_id_type indg)
{
	if(isBoundaryGPU(indg))
	{
		return false;
	}
	
	IndirectionList list = getNode(get<0>(indg)).getList();

	int length = list.Length();

	return (length > 1);
}

bool isDerefGPU(gpu_id_type indg)
{
	IndirectionList list1, list2;

	if(isBoundaryGPU(indg))
	{
		return false;
	}
	else if(isKLimitedGPU(indg))
	{
		list2 = getNode(get<1>(indg)).getList();

		if(list2.Length() == 0)
		{
			return false;
		}
	}
	else if(isPointstoInformation(indg))
	{
		return false;
	}	
	
	list1 = getNode(get<0>(indg)).getList();

	int length1, length2;
	length1 = list1.Length();

	if(length1 <= 1)
	{
		list2 = getNode(get<1>(indg)).getList();

		length2 = list2.Length();

		if(length2 <= 1)
		{
			return false;
		}	
	}
		
	return true;
}

bool checkGPUSetForCoalescing(GPUSet gpus, struct cgraph_node *cnode)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPUSet queued = Queued[cnode_num];

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		if(isDerefGPU(*it))
		{
			return true;
		}
		
		if(queued.find(*it) != queued.end())
		{
			return true;
		}
	}

	return false;
}

GPUSet ret_ind_gpus(GPUSet r)
{
	GPUSet res;

	for(GPUSet::iterator it = r.begin(); it != r.end(); it++)
	{
		if(isIndirectGPU(*it))
		{
			res.insert(*it);
		}
	}

	return res;
}

GPUSet RGen(GPUSet rin, GPUSet delta, struct cgraph_node *cnode, unsigned int gpb_id)
{
	GPUSet gen, temp;

	#if 0 //PRINT_DATA 
	fprintf(dump_file, "\nDelta in RGen\n");
	printSetOfGPUs(delta);
	fprintf(dump_file, "\nRIN in RGen\n");
	printSetOfGPUs(rin);
	#endif

	GPU temp_gpu;
	gpu_id_type id;
	stmt_info_type key_t;

	GPUSet existing_gpus;
	
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	for(GPUSet::iterator it = delta.begin(); it != delta.end(); it++)
	{
//		id = stripUpwardsExposed(*it);
		id = *it;

		#if 0 //PRINT_DATA 
		fprintf(dump_file,"\nReducing c\n");
		fflush(dump_file);
		print_GPU(*it);
		fflush(dump_file);

		if(isPointstoEdge(id))
		{
			gen.insert(id);

			continue;
		}
		#endif

		temp = GPUReduction(id, rin, cnode);

		gen.insert(temp.begin(), temp.end());

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nResolved To...\n");
		printSetOfGPUs(temp);
		#endif

		key_t = std::make_tuple(cnode_num, gpb_id, id);

		set< unsigned int > sset = stmt_id_info[key_t];
		set< unsigned int > temp_set;

//		stmt_id_info.erase(key_t);

		for(GPUSet::iterator git = temp.begin(); git != temp.end(); git++)
		{
			#if DATA_MEAS
			if(*git != *it)
			{
				importedUse.insert(*it);
			}
			#endif

			key_t = std::make_tuple(cnode_num, gpb_id, *git);

			temp_set = stmt_id_info[key_t];

			temp_set.insert(sset.begin(), sset.end());

			stmt_id_info[key_t] = temp_set;
		}

		for(GPBSet::iterator sit = sset.begin(); sit != sset.end(); sit++)
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nInside Loop ....\n");
			#endif

			existing_gpus = PTS_INFO[*sit];

			existing_gpus.erase(id);

			existing_gpus.insert(temp.begin(), temp.end());

			PTS_INFO[*sit] = existing_gpus;	
		}

		#if 0
		fprintf(dump_file,"\nTemp Gen\n");
		fflush(dump_file);
		printSetOfGPUs(temp);
		fflush(dump_file);
		#endif
	}

	#if 0
	fprintf(dump_file,"\nGen\n");
	fflush(dump_file);
	printSetOfGPUs(gen);
	fflush(dump_file);
	#endif

	return gen;
}

bool toBeKilled(struct cgraph_node *cnode, GPUSet gen, unsigned int gpb_id, gpu_id_type w)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	stmt_info_type key;
	GPBSet sset, temp_sset;
	GPUSet gpus;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nGen\n");
	printSetOfGPUs(gen);
	#endif

	key = std::make_tuple(cnode_num, gpb_id, w);

	sset = stmt_id_info[key];

	for(GPBSet::iterator it = sset.begin(); it != sset.end(); it++)
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nInside loop\n");
		#endif

		GPUSet temp;

		gpus = PTS_INFO[*it];

		set_intersection(gpus.begin(), gpus.end(), gen.begin(), gen.end(), inserter(temp, temp.end()));

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPUs\n");
		printSetOfGPUs(gpus);
		fprintf(dump_file, "\nTemp\n");
		printSetOfGPUs(temp);
		#endif

		if(temp.size() > 1)
		{
			return false;
		}
		else if(temp.size() == 1)
		{
			gpu_id_type id;

			id = *(temp.begin());
	
			if(CDV.find(get<0>(get<0>(id))) != CDV.end())
			{
				return false;
			}
		}	
	}

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nOutside loop\n");
	#endif

	return true;
}


definitions Def(GPUSet red, gpu_id_type w)
{
	definitions res;

	for(GPUSet::iterator it = red.begin(); it != red.end(); it++)
	{
//		if(get<2>(*it) == get<2>(w))
		{
			res.insert(get<0>(*it));
		}
	}	

	#if 0
	fprintf(dump_file, "\nDefinitions for Kill\n");
	printDefinitions(res);
	#endif

	return res;
}

GPUSet Match(gpu_id_type w, GPUSet rin)
{
	GPUSet res;

	for(GPUSet::iterator it = rin.begin(); it != rin.end(); it++)
	{
		#if 0
		fprintf(dump_file, "\nConsidering for Matching\n");
		print_GPU(*it);

		print_NodeID(get<0>(*it));
		print_NodeID(get<0>(w));
		#endif

		if(get<0>(*it) == get<0>(w))
		{
//			fprintf(dump_file, "\nMatch Found\n");
			res.insert(*it);
		}
	}	

	return res;
}

GPUSet MatchSourceVar(GPUSet I, GPUSet G)
{
	GPUSet res;
	IndirectionList list;
	unsigned int var1, var2;

	for(GPUSet::iterator it = I.begin(); it != I.end(); it++)
	{
		list = getNode(get<0>(*it)).getList();

		if(list.stackIndirectionList())
		{
			var1 = get<0>(get<0>(*it));

			if(CDV.find(var1) != CDV.end())
			{
				--var1;
			}

			for(GPUSet::iterator git = G.begin(); git != G.end(); git++)
			{
				var2 = get<0>(get<0>(*git));

				if(CDV.find(var2) != CDV.end())
				{
					--var2;
				}

				if(var1 == var2)
				{
					res.insert(*it);
				}
			}
		}
	}

	return res;
}

GPUSet killBoundaryDefinition(gpu_id_type c_id)
{
	node_id_type id = get<0>(c_id);
	Node lhs = getNode(id);
	unsigned int var = get<0>(id);
	IndirectionList l = lhs.getList();
	unsigned int length = l.Length();
	GPUSet res;

	if(l.get_st_hp())
	{
		int f[IndirectionList::kSize];

		IndirectionList newl(true, length, 0 , f);

		if(CDV.find(var) != CDV.end())
		{
			Node n1(var-1, newl);
			Node n2(var, newl);

			GPU gpu(n1.getNodeID(), n2.getNodeID());	

//			fprintf(dump_file, "\nKilling BI GPU\n");
//			gpu.printGPU();
		
			res.insert(gpu.getGPUID());
		}
	}
	else
	{
		int f[IndirectionList::kSize];

		for(int i = 0; i < length; i++)
		{
			f[i] = SFIELD;
		}

		IndirectionList newl(false, 0, length, f);

		if(CDV.find(var) != CDV.end())
		{
			Node n1(var-1, newl);
			Node n2(var, newl);

			GPU gpu(n1.getNodeID(), n2.getNodeID());	

//			fprintf(dump_file, "\nKilling BI GPU\n");
//			gpu.printGPU();
		
			res.insert(gpu.getGPUID());
		}
	}

	return res;
}

GPUSet Kill(GPUSet red, GPUSet rin, struct cgraph_node *cnode, unsigned int gpb_id, definitions dfp)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	#if 0
	fprintf(dump_file,"\nInside Kill\n");
//	fprintf(dump_file,"\nInside Kill GPB %d\n", gpb_id);
//	fflush(dump_file);
//	fprintf(dump_file,"\nInside Kill for Function %s and GPB %d\n", cgraph_node_name(cnode), gpb_id);
//	fflush(dump_file);
	fprintf(dump_file, "\nRGEN\n");
	fflush(dump_file);
	printSetOfGPUs(red);
	fflush(dump_file);
	fprintf(dump_file, "\nRIN\n");
	fflush(dump_file);
	printSetOfGPUs(rin);
	fflush(dump_file);
	#endif

	GPUSet res, m_res;
	unsigned int src;
	IndirectionList list;
	Node src_node;
	unsigned int gpuid;

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	for(GPUSet::iterator it = red.begin(); it != red.end(); it++)
	{
		src_node = getNode(get<0>(*it));

		src = src_node.getVarIndex();

//		gpuid = get<2>(*it);

//		src = get<0>(get<0>(*it));

//		fprintf(dump_file, "\nSrc %d\n", src);

		#if 0
		list = src_node.getList();

		if(!list.get_st_hp())
		{
			continue;
		}
		#endif

		if(src == summ_node_id)
		{
			continue;
		}

		if(ptr_arith_map[*it])
		{
			continue;
		}

		if(art_var(src) || (escaped.find(src) != escaped.end()) || isArray(src)) // Weak update for heap and address escaped variables
		{
			#if 0
			fprintf(dump_file, "\nArray or Escaped => Weak Update\n");
			fflush(dump_file);
			#endif
		//	return res;

			continue;
		}

//		if(Def(red, *it).size() == 1) 
		if(toBeKilled(cnode, red, gpb_id, *it))
		{
			#if DATA_MEAS
			fprintf(dump_file, "\nStrong Update in Function %d %s GPB %d\n", cnode->uid, cgraph_node_name(cnode), gpb_id);
			#endif

			m_res = Match(*it, rin);

			res.insert(m_res.begin(), m_res.end());

			#if DATA_MEAS
			gpu_key_type gkey = std::make_tuple(gpb_id, cnode_num);
			unsigned int same_context = gpu_key[gkey];

			if(same_context != 0)
			{
				struct cgraph_node *callee = func_numbering[same_context];

				GPUSet callee_gpus = GPG_GPUs_map[same_context][cnode_num];
				GPUSet inter;

				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nGPB %d Function %s\n", gpb_id, cgraph_node_name(cnode));
				fprintf(dump_file, "\nm_res\n");
				printSetOfGPUs(m_res);
				fprintf(dump_file, "\ncallee_gpus\n");
				printSetOfGPUs(callee_gpus);
				#endif

				set_intersection(m_res.begin(), m_res.end(), callee_gpus.begin(), callee_gpus.end(), inserter(inter, inter.end()));

				for(GPUSet::iterator iit = inter.begin(); iit != inter.end(); iit++)
				{
					if(isBoundaryGPU(*iit))
					{
						inter.erase(*iit);
					}
				}

				GPUSet id_set;
				id_set.insert(*it);

				for(GPUSet::iterator at = inter.begin(); at != inter.end(); at++)
				{
					if(get<0>(*it) == get<0>(*at))
					{
						continue;
					}
				}

				if(m_res.find(*it) == m_res.end())
				if(!inter.empty())
				{
					if(!(id_set == m_res))
					{
						if(!(inter == id_set))
						{
							fprintf(dump_file, "\nSoundness Alert For Caller %s, Callee %s, GPB %d\n", cgraph_node_name(cnode), cgraph_node_name(callee), gpb_id);
							print_GPU(*it);
							fprintf(dump_file, "\nIntersection\n");
							printSetOfGPUs(inter);
						}
					}
				}
			}
			#endif

			m_res = killBoundaryDefinition(*it);

			res.insert(m_res.begin(), m_res.end());
		}

		#if 0
		else
		{
			fprintf(dump_file, "\nKill !required\n");
			fflush(dump_file);
		}
		#endif
	}

	GPUSet final_res;

	for(GPUSet:: iterator it = res.begin(); it != res.end(); it++)
	{
		if(dfp.find(get<0>(*it)) == dfp.end())	
		{
			final_res.insert(*it);
		}
	}

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nKill for GPB %d Function %s\n", gpb_id, cgraph_node_name(cnode));
	fflush(dump_file);
	printSetOfGPUs(final_res);
	fflush(dump_file);
	#endif

	#if PROFILING
	RETURN(final_res);
	#else
	return final_res;
	#endif
}

//Computing ROUT

GPUSet ROut(GPUSet rin, GPUSet rgen, GPUSet rkill)
{
	GPUSet rout;

	rout = rin;

	for(GPUSet::iterator it = rkill.begin(); it != rkill.end(); it++)
	{
		rout.erase(*it);
	}

	rout.insert(rgen.begin(), rgen.end());

	#if 0
	fprintf(dump_file, "\nROut\n");
	printSetOfGPUs(rout);
	#endif

	return rout;
}

GPUSet filterFlowInsensitiveData(GPUSet gen, struct cgraph_node *cnode, unsigned int gpb_id)
{
	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPUSet res, temp, temp_p, temp_np;
	unsigned int var, rvar;
	unsigned int id;

	GPUSet t_p, t_np;

	for(GPUSet::iterator it = gen.begin(); it != gen.end(); it++)
	{
		if(get<0>(*it) == get<1>(*it))
		{
			continue;
		}

		var = get<0>(get<0>(*it));
		rvar = get<0>(get<1>(*it));

//		id = get<2>(*it);

		#if 0
		fprintf(dump_file, "\nFiltering GPU for flow-insensitivity\n");
		print_GPU(*it);
		tree t = NodeType[get<0>(*it)];
		tree t1 = NodeType[get<1>(*it)];

		if(t != NULL)
		{
			print_node(dump_file, "\nLHS - TREE IN FI Filtering\n", t, 0);
		}

		if(t1 != NULL)
		{
			print_node(dump_file, "\nRHS - TREE IN FI Filtering\n", t1, 0);
		}
		#endif

		set_tree_nodes t1;

		t1 = DefTypes[*it];
//		t1 = NodeType[get<0>(*it)];

		if(var <= 3)
		{
			continue;
		}
		else if(var == summ_node_id)
		{
			if(isPointstoEdge(*it))
			{
				temp_p.insert(*it);
			}
			else
			{
				temp_np.insert(*it);
			}
		}
		else if(is_ssa_var(var))
		{
			if(isPointstoEdge(*it))
			{
				temp_p.insert(*it);
			}
			else
			{
				temp_np.insert(*it);
			}
		}
		#if 1
		else if(t1.size() == 1 && isArrayTree(*(t1.begin())))
		{
			if(isPointstoEdge(*it))
			{
				temp_p.insert(*it);
			}
			else
			{
				temp_np.insert(*it);
			}
		}
		#endif
		else if(ptr_arith_map[*it])
		{
//			fprintf(dump_file, "\nPTR-ARITH Flag set\n");

			if(isPointstoEdge(*it))
			{
				temp_p.insert(*it);
			}
			else
			{
				temp_np.insert(*it);
			}
		}
		else if(isArray(var))
		{
			if(isPointstoEdge(*it))
			{
				temp_p.insert(*it);
			}
			else
			{
				temp_np.insert(*it);
			}
		}
		else if(art_var(var) && isPointstoEdge(*it)) // Storing heap.data (only points-to edges) flow-insensitively
		{	
			temp_p.insert(*it);
		}
		else
		{
			#if 0
//			if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "Perl_yyparse") == 0) // Only for perlbench
			{
				std::string str = cs_get_varinfo(var)->name;
				if (strcmp (str.substr(0,3).c_str(), "PL_") == 0)
				{
					if(isPointstoEdge(*it))
					{
						temp_p.insert(*it);
					}
					else
					{
						temp_np.insert(*it);
					}
				}
				else
				{	
					res.insert(*it);
				}
			}
			else
			{
				res.insert(*it);
			}
			#endif

			res.insert(*it);
		}
	}

	stmt_info_type key;
	GPBSet temp_sset, sset;
	GPUSet temp_set;

	for(GPUSet::iterator it = temp_p.begin(); it != temp_p.end(); it++)
	{
		var = get<0>(get<0>(*it));

		key = std::make_tuple(cnode_num, gpb_id, *it);

		sset = stmt_id_info[key];

//		stmt_id_info.erase(key);

		key = std::make_tuple(cnode_num, 0, *it);

		temp_sset = stmt_id_info[key];

		temp_sset.insert(sset.begin(), sset.end());

		stmt_id_info[key] = temp_sset;

		for(GPBSet::iterator sit = sset.begin(); sit != sset.end(); sit++)
		{
			temp_set = PTS_INFO[*sit];
			temp_set.insert(*it);	
			PTS_INFO[*sit] = temp_set;
		}

		t_p = FIP[cnode_num][var];

		t_p.insert(*it);

		FIP[cnode_num][var] = t_p;
	}

	for(GPUSet::iterator it = temp_np.begin(); it != temp_np.end(); it++)
	{
		var = get<0>(get<0>(*it));

		key = std::make_tuple(cnode_num, gpb_id, *it);

		sset = stmt_id_info[key];

//		stmt_id_info.erase(key);

		key = std::make_tuple(cnode_num, 0, *it);

		temp_sset = stmt_id_info[key];

		temp_sset.insert(sset.begin(), sset.end());

		stmt_id_info[key] = temp_sset;

		for(GPBSet::iterator sit = sset.begin(); sit != sset.end(); sit++)
		{
			temp_set = PTS_INFO[*sit];
			temp_set.insert(*it);	
			PTS_INFO[*sit] = temp_set;
		}

		t_np = FINP[cnode_num][var];

		t_np.insert(*it);

		FINP[cnode_num][var] = t_np;
	}

//	set_difference(gen.begin(), gen.end(), temp.begin(), temp.end(), inserter(res, res.end()));

	return res;

//	return std::make_pair(res, temp);
}

std::tuple< GPUSet, GPUSet > ReachingGPUsAnalysis(GPUSet rin, GPUSet delta, struct cgraph_node *cnode, unsigned int gpb_id, definitions dfp)
{
//	fprintf(dump_file, "\nReaching GPUs Analysis\n");
//	fprintf(dump_file, "\nReaching GPUs Analysis without Blocking for GPB %d and %s\n", gpb_id, cgraph_node_name(cnode));
//	fflush(dump_file);

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPUSet rout, rgen, rkill, rgen_new, filter;
	std::tuple< GPUSet, GPUSet > res;
	
	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nRIN for GPB %d Function %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(rin);
	fprintf(dump_file, "\nDelta for GPB %d Function %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(delta);
	#endif

	rgen = RGen(rin, delta, cnode, gpb_id);

	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nrgen after computation for GPB %d Function %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(rgen);
	#endif

//	collectTypeInfoForGPUSet(cnode, rgen, true);
	
	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nrgen after filter flow-insensitive data\n");
	printSetOfGPUs(rgen);
	#endif

	computeDefRefForGPUSet(cnode, rgen, false);

	recordDataDependence(rin, rgen);

	rgen = filterFlowInsensitiveData(rgen, cnode, gpb_id);

	#if 0
	if(sanityCheck(rgen))
	{
		fprintf(dump_file, "\nAlert! Empty Indirection List computed while processing Function %s (No Blocking)\n", cgraph_node_name(cnode));
		printSetOfGPUs(rgen);
		exit(1);
	}
	#endif

	rkill = Kill(rgen, rin, cnode, gpb_id, dfp);

	rout = ROut(rin, rgen, rkill);

	#if 0
	GPUSet a_data = flowInsensitiveInformation[cnode_num];	
	GPUSet new_rout;

	set_difference(rout.begin(), rout.end(), a_data.begin(), a_data.end(), inserter(new_rout, new_rout.end()));
	#endif

//	compute_escaped(rgen, cnode);
	rgen_new = filterLocal(rgen, cnode);

	#if 0 // PRINT_DATA
	fprintf(dump_file, "\nrgen after filter local\n");
	printSetOfGPUs(rgen_new);
	#endif

//	set_difference(rgen.begin(), rgen.end(), filter.begin(), filter.end(), inserter(rgen_new, rgen_new.end()));

	res = std::make_tuple(rout, rgen_new);

	#if 0
	fprintf(dump_file, "\nROUT in RA\n");
	printSetOfGPUs(rout);
	fprintf(dump_file, "\nEND\n");
	#endif

	return res;
}

std::tuple< GPUSet, GPUSet > BRGen(GPUSet rin, GPUSet brin, GPUSet delta, struct cgraph_node *cnode, unsigned int gpb_id)
{
	GPUSet gen, temp, queued;
	std::tuple< GPUSet, GPUSet > res;

	#if 0
	fprintf(dump_file, "\nRIN\n");
	fflush(dump_file);
	printSetOfGPUs(rin);
	fflush(dump_file);
	fprintf(dump_file, "\nBRIN\n");
	fflush(dump_file);
	printSetOfGPUs(brin);
	fflush(dump_file);
	fprintf(dump_file, "\nDELTA\n");
	fflush(dump_file);
	printSetOfGPUs(delta);
	fflush(dump_file);
	fprintf(dump_file, "\nGen before\n");
	fflush(dump_file);
	printSetOfGPUs(gen);
	fflush(dump_file);
	#endif

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	gpu_id_type id;
	GPBSet temp_set;
	GPBSet sset;
	stmt_info_type key_t;

	GPUSet existing_gpus;
	
	for(GPUSet::iterator it = delta.begin(); it != delta.end(); it++)
	{
//		id = stripUpwardsExposed(*it);

		id = *it;

		#if 0 //PRINT_DATA
		fprintf(dump_file,"\nReducing c\n");
		fflush(dump_file);
		print_GPU(*it);
		fflush(dump_file);
		#endif
	
		#if 0
		if(isPointstoEdge(id))
		{
			gen.insert(id);

			continue;
		}
		#endif

		//temp = GPUReduction(*it, rin);
		res = GPUReductionWB(id, rin, brin, cnode);

		temp = get<0>(res);

		#if 0 //PRINT_DATA
		fprintf(dump_file,"\nTemp Gen\n");
		fflush(dump_file);
		printSetOfGPUs(temp);
		fflush(dump_file);
		#endif

		#if DATA_MEAS 
		gpu_key_type gkey = std::make_tuple(gpb_id, cnode_num);
		unsigned int same_context = gpu_key[gkey];

		if(same_context != 0)
		{
			struct cgraph_node *callee = func_numbering[same_context];

			GPUSet callee_gpus = GPG_GPUs_map[same_context][cnode_num];

			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nSame Context in BRGen Caller %s GPB %d Callee %s\n", cgraph_node_name(cnode), gpb_id, cgraph_node_name(callee));
			print_GPU(id);
			fprintf(dump_file, "\nGen\n");
			printSetOfGPUs(temp);
			fprintf(dump_file, "\nOld Callee GPUs\n");
			printSetOfGPUs(callee_gpus);
			#endif

			callee_gpus.erase(id);	

			for(GPUSet::iterator tit = temp.begin(); tit != temp.end(); tit++)
			{
				if(get<0>(*tit) == get<1>(*tit))
				{
					continue;
				}

				callee_gpus.insert(*tit);
			}

			GPG_GPUs_map[same_context][cnode_num] = callee_gpus;

			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nNew Callee GPUs\n");
			printSetOfGPUs(callee_gpus);
			#endif
		}
		#endif	

		key_t = std::make_tuple(cnode_num, gpb_id, id);

		sset = stmt_id_info[key_t];

//		stmt_id_info.erase(key_t);

		for(GPUSet::iterator git = temp.begin(); git != temp.end(); git++)
		{
			#if DATA_MEAS
			if(*git != *it)
			{
				importedUse.insert(*it);
			}
			#endif

			key_t = std::make_tuple(cnode_num, gpb_id, *git);

			temp_set = stmt_id_info[key_t];

			temp_set.insert(sset.begin(), sset.end());

			stmt_id_info[key_t] = temp_set;

			gen.insert(*git);
		}

		for(GPBSet::iterator sit = sset.begin(); sit != sset.end(); sit++)
		{
			existing_gpus = PTS_INFO[*sit];

			existing_gpus.erase(id);

			existing_gpus.insert(temp.begin(), temp.end());

			PTS_INFO[*sit] = existing_gpus;	
		}

//		gen.insert(temp.begin(), temp.end());

		temp = get<1>(res);

		queued.insert(temp.begin(), temp.end());
	}

	#if 0
	fprintf(dump_file,"\nGen\n");
	fflush(dump_file);
	printSetOfGPUs(gen);
	fflush(dump_file);
	#endif

	res = std::make_tuple(gen, queued);

	return res;
}

GPUSet Blocked(GPUSet rin, GPUSet rgen)
{
	#if PROFILING
	FUNBEGIN();
	#endif

	GPUSet res, temp;

	#if 0 //PRINT_DATA	
	fprintf(dump_file, "\nHey\n");
	fflush(dump_file);
	fprintf(dump_file, "\nInside brgen\n");
	fflush(dump_file);
	#endif

	if(rgen.empty())
	{
		#if PROFILING
		RETURN(res);
		#else
		return res;
		#endif
	}
	else
	{
		temp = ret_ind_gpus(rgen);

		if(!temp.empty())
		{
			GPUSet temp1;

			temp1 = computeBlockedGPUs(rin, temp);

			res.insert(temp1.begin(), temp1.end());
		}
		else
		{
			temp = ret_ind_gpus(rin);

			if(!temp.empty())
			{
				GPUSet temp1;

				temp1 = computeBlockedGPUs(temp, rgen);

				res.insert(temp1.begin(), temp1.end());
			}
		}
	}

	GPUSet fin_res;

	for(GPUSet::iterator it = res.begin(); it != res.end(); it++)
	{
		if(!isBoundaryGPU(*it))
		{
			fin_res.insert(*it);
		}
	}

	#if PROFILING
	RETURN(fin_res);
	#else
	return fin_res;
	#endif
}

//Computing ROUT

GPUSet BROut(GPUSet brin, GPUSet brgen, GPUSet brkill, GPUSet blocked)
{
	GPUSet brout;

	brout = brin;

	for(GPUSet::iterator it = brkill.begin(); it != brkill.end(); it++)
	{
		brout.erase(*it);
	}

	for(GPUSet::iterator it = blocked.begin(); it != blocked.end(); it++)
	{
		brout.erase(*it);
	}

	brout.insert(brgen.begin(), brgen.end());

	return brout;
}

void compute_escaped(GPUSet gen, struct cgraph_node *cnode)
{
	Node lhs, rhs;
	unsigned int lvar, rvar;
	
	for(GPUSet::iterator it = gen.begin(); 	it != gen.end(); it++)
	{
		lvar = get<0>(get<0>(*it));
		rvar = get<0>(get<1>(*it));

		if(CDV.find(lvar) != CDV.end())
		{
			--lvar;
		}

		if(CDV.find(rvar) != CDV.end())
		{
			--rvar;
		}

		if(isInScope(lvar, cnode))
		{
			if(!(isInScope(rvar, cnode)))
			{
				escaped.insert(rvar);
			}
		}
	}
}

bool sanityCheck(GPUSet gen)
{
	IndirectionList list;
	Node node;

	for(GPUSet::iterator it = gen.begin(); it != gen.end(); it++)
	{
		node = getNode(get<0>(*it));

		list = node.getList();

		if(list.Length() == 0)
		{
			return true;
		}
	}

	return false;
}

GPUSet RegenerateGPUs(GPUSet blocked, GPUSet brin, GPUSet brgen_temp)
{
	GPUSet res;
	unsigned int var;
	IndirectionList indlist;
	Node n;

	for(GPUSet::iterator it = blocked.begin(); it != blocked.end(); it++)
	{
		n = getNode(get<0>(*it));

		indlist = n.getList();	

		var = n.getVarIndex();

		if(CDV.find(var) == CDV.end())
		{
			Node n1(var, indlist);
			Node n2(var+1, indlist);

			GPU gpu(n1.getNodeID(), n2.getNodeID());	

			res.insert(gpu.getGPUID());
		}
		else
		{	
			Node n1(var-1, indlist);
			Node n2(var, indlist);

			GPU gpu(n1.getNodeID(), n2.getNodeID());	

			res.insert(gpu.getGPUID());
		}
	}

	return res;
}


std::tuple< GPUSet, GPUSet, GPUSet > ReachingGPUsAnalysisWB(GPUSet rin, GPUSet brin, GPUSet delta, struct cgraph_node *cnode, unsigned int gpb_id, definitions dfp)
{
	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nReaching GPUs Analysis with Blocking for GPB %d and %s\n", gpb_id, cgraph_node_name(cnode));
	fflush(dump_file);
	#endif

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	GPUSet brout, brgen, brkill, blocked, queued, brgen_temp, filter;
	std::tuple< GPUSet, GPUSet > temp;
	std::tuple< GPUSet, GPUSet, GPUSet > res;

	temp = BRGen(rin, brin, delta, cnode, gpb_id);
//	brgen_temp = RGen(rin, delta);

	brgen_temp = get<0>(temp);
	queued = get<1>(temp);

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nInside ReachingGPUsAnalysisWB for GPB %d and Function %s, Queued GPUs are:\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(queued);
	fprintf(dump_file, "\n\nEnd\n");
	#endif

//	collectTypeInfoForGPUSet(cnode, brgen_temp, true);
	
	computeDefRefForGPUSet(cnode, brgen_temp, false);

	recordDataDependence(brin, brgen_temp);

	brgen_temp = filterFlowInsensitiveData(brgen_temp, cnode, gpb_id);

	#if 0
	if(sanityCheck(brgen_temp))
	{
		fprintf(dump_file, "\nAlert! Empty Indirection List computed while processing Function %s\n", cgraph_node_name(cnode));
		exit(1);
	}
	#endif

//	fprintf(dump_file, "\nAfter Gen, Before Kill\n");
//	fprintf(dump_file, "\nAfter Gen, Before Kill for GPB %d and %s\n", gpb_id, cgraph_node_name(cnode));
//	fflush(dump_file);

	brkill = Kill(brgen_temp, brin, cnode, gpb_id, dfp);

	blocked = Blocked(brin, brgen_temp);

	GPUSet regen_blocked_gpus;

	regen_blocked_gpus = RegenerateGPUs(blocked, brin, brgen_temp);

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nBlocked GPUs for GPB %d Function %s\n", gpb_id, cgraph_node_name(cnode));
	printSetOfGPUs(blocked);
	#endif

	brout = BROut(brin, brgen_temp, brkill, blocked);

	brout.insert(regen_blocked_gpus.begin(), regen_blocked_gpus.end());

	#if 0
	GPUSet a_data = flowInsensitiveInformation[cnode_num];	
	GPUSet new_brout;

	set_difference(brout.begin(), brout.end(), a_data.begin(), a_data.end(), inserter(new_brout, new_brout.end()));
	#endif

//	compute_escaped(brgen_temp, cnode);

	#if 0
	fprintf(dump_file, "\nPristine brgen\n");
	fflush(dump_file);
	printSetOfGPUs(brgen_temp);
	fflush(dump_file);
	#endif	

	brgen = filterLocal(brgen_temp, cnode);
//	filter = filterLocal(brgen_temp, cnode);

	#if 0
	fprintf(dump_file, "\nBRGEN before filtering\n");
	fflush(dump_file);
	printSetOfGPUs(brgen_temp);
	fflush(dump_file);
	#endif	

//	set_intersection(brgen_temp.begin(), brgen_temp.end(), filter.begin(), filter.end(), inserter(brgen, brgen.end()));

	#if 0
	fprintf(dump_file, "\nBRGEN after filtering\n");
	fflush(dump_file);
	printSetOfGPUs(brgen);
	fflush(dump_file);
	#endif

	res = std::make_tuple(brout, queued, brgen);

	#if 0
	fprintf(dump_file, "\nBRGEN in RA\n");
	printSetOfGPUs(brgen);
	fprintf(dump_file, "\nEND\n");
	fprintf(dump_file, "\nBROUT in RA\n");
	printSetOfGPUs(brout);
	fprintf(dump_file, "\nEND\n");
	#endif

	return res;
}

GPUSet meet(GPUSet in1, GPUSet in2)
{
	GPUSet res = in1;

	res.insert(in2.begin(), in2.end());

	return res;
}

definitions getAllNodes(unsigned int n, IndirectionList list)
{
	definitions res;
	unsigned int new_var;

	if(list.get_st_hp() || n <= 4)
	{
		Node node(n, list);
		res.insert(node.getNodeID());
		return res;
	}

	csvarinfo_t vi = cs_get_varinfo (n);

	if(vi)
	{
		if(vi->is_heap_var || vi->is_art_var)
		{
			Node node(n, list);
			res.insert(node.getNodeID());
			return res;
		}	
	}

	#if 0
	fprintf(dump_file, "\nInside getAllNodes %s- %d\n", get_var_name(n), n);
	list.printIndirectionList();	

	fprintf(dump_file, "\nDer Der\n");
	#endif

	if(list.at(0) == AFIELD)
	{
//		fprintf(dump_file, "\nAny Field\nList Before\n");
//		list.printIndirectionList();

		list = list.changeFirstField();

//		fprintf(dump_file, "\nList After\n");
//		list.printIndirectionList();

		set< unsigned int > temp = cs_get_all_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, n), 0);

		for(set< unsigned int >::iterator it = temp.begin(); it != temp.end(); it++)
		{
			Node node(*it, list);

//			fprintf(dump_file, "\nNew Node Created\n");
//			node.printNode();

			res.insert(node.getNodeID());
		}
	}
	else
	{
//		fprintf(dump_file, "\nHey Der\n");
	
		csvarinfo_t var_info = cs_first_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, n), list.at(0));
//		fprintf(dump_file, "\nHold On\n");

		if(var_info)
		{
			new_var  = var_info->id;

			list = list.changeFirstField();

			Node node(new_var, list);

//			fprintf(dump_file, "\nNew Node Created\n");
//			node.printNode();

			res.insert(node.getNodeID());
		}
		else
		{
			Node node(n, list);

//			fprintf(dump_file, "\nNew Node with Old Info Created\n");
//			node.printNode();

			res.insert(node.getNodeID());
			return res;
		}
	}

	return res;
}

gpu_id_type stripUpwardsExposed(gpu_id_type id)
{
	Node lhs, rhs;
	node_id_type s, t, ns, nt;

	s = get<0>(id);
	t = get<1>(id);

	lhs = getNode(s);
	rhs = getNode(t);

	unsigned int svar, tvar;

	svar = lhs.getVarIndex();
	tvar = rhs.getVarIndex();

	if(CDV.find(svar) != CDV.end())
	{
		svar--;
		Node new_lhs(svar, lhs.getList());

		ns = new_lhs.getNodeID();
	}
	else
	{
		ns = s;
	}

	if(CDV.find(tvar) != CDV.end())
	{
		tvar--;
		Node new_rhs(tvar, rhs.getList());

		nt = new_rhs.getNodeID();
	}
	else
	{
		nt = t;
	}

	GPU gpu(getNode(ns), getNode(nt));

	return gpu.getGPUID();
}

#if 0
definitions get_all_nodes(unsigned int n, IndirectionList list)
{
	definitions res;

	if(n <= 4)
//	if(list.get_st_hp() || n <= 4)
	{
		Node node(n, list);
		res.insert(node.getNodeID());
		return res;
	}

	list = list.changeFirstField();

	if(list.at(0) == AFIELD)
	{
		set< unsigned int > temp = cs_get_all_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, n), 0);

		for(set< unsigned int >::iterator it = temp.begin(); it != temp.end(); it++)
		{
			Node node(*it, list);
			res.insert(node.getNodeID());
		}
	}
	if(list.at(0) == SFIELD)
	{
		set< unsigned int > temp = cs_get_all_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, n), 0);

		if(temp.empty())
		{
			for(set< unsigned int >::iterator it = temp.begin(); it != temp.end(); it++)
			{
				Node node(*it, list);
				res.insert(node.getNodeID());
			}	
		}
		else
		{
			n = cs_first_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, n), 0)->id;

			if(n)
			{
				Node node(n, list);
				res.insert(node.getNodeID());
			}
		}
	}	
	else
	{
		n = cs_first_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, n), list.at(0))->id;

		if(n)
		{
			Node node(n, list);
			res.insert(node.getNodeID());
		}
	}

	return res;
}
#endif

bool areDataDependent(GPUSet gpus1, GPUSet gpus2)
{
	if(gpus1 == gpus2)
		return true;

	for(GPUSet::iterator it1 = gpus1.begin(); it1 != gpus1.end(); it1++)
	{
		for(GPUSet::iterator it2 = gpus2.begin(); it2 != gpus2.end(); it2++)
		{
			if(isDataDependent(*it1, *it2))
			{
				return true;
			}
		}
	}

	return false;
}

bool areStructHeapData(GPUSet gpus)
{
	Node n;
	IndirectionList list;

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		n = getNode(get<0>(*it));
		list = n.getList();

		if(list.get_st_hp())
		{
			return false;
		}
	}
		
	return true;
}

bool areAdvancingGPUs(GPUSet gpus)
{
	Node n;
	unsigned int lvar, rvar;	
	IndirectionList list;

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		n = getNode(get<0>(*it));
		list = n.getList();

		if(!isKLimitedGPU(*it))
		{
			if(!list.get_st_hp())
			{
				lvar = get<0>(get<0>(*it));
				rvar = get<0>(get<1>(*it));

				if((rvar == lvar+1) || (rvar == lvar-1) || (rvar == lvar))
				{
					return true;
				}
			}
		}
	}
	
	return false;
}

bool isAdvancingGPU(gpu_id_type id)
{
	Node n;
	unsigned int lvar, rvar;	
	IndirectionList list;

	n = getNode(get<0>(id));
	list = n.getList();

	if(!list.get_st_hp())
	{
		lvar = get<0>(get<0>(id));
		rvar = get<0>(get<1>(id));

		if(lvar == rvar)
		{
			return true;
		}
		else
		{
			if(CDV.find(rvar) != CDV.end())
			{
				if(lvar == (rvar-1))
				{
					return true;
				}
			}
		}
	}

	return false;
}

bool isKLimitedGPU(gpu_id_type id)
{
	Node l, r;
	IndirectionList list1, list2;

	l = getNode(get<0>(id));
	r = getNode(get<1>(id));

	list1 = l.getList();
	list2 = r.getList();

	if(!list1.get_st_hp())
	{
		if(list1.getLength() == k_thresh)	
		{
			return true;
		}
	}

	if(!list2.get_st_hp())
	{
		if(list2.getLength() == k_thresh)	
		{
			return true;
		}
	}

	return false;
}

GPUSet convertAdvancingToKLimitedGPU(gpu_id_type id)
{
	GPUSet gpus, res, temp;

	if(isKLimitedGPU(id))
	{
		gpus.insert(id);

		return gpus;
	}

	res.insert(id);

	while(!(gpus == res))
	{
		gpus = res;

		for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
		{
			if(!isKLimitedGPU(*it))
			{
				temp = ss_composition(id, id);
				res.insert(temp.begin(), temp.end());
				temp = ts_composition(id, id);
				res.insert(temp.begin(), temp.end());
			}
		}
	}

	return gpus;
}

bool areSameSourceGPUs(GPUSet gpus)
{
	Node n;
	unsigned int var, nvar;	
	IndirectionList list;
	bool no = false;

	gpu_id_type id = *(gpus.begin());

	var = get<0>(get<0>(id));

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		n = getNode(get<0>(*it));
		list = n.getList();
		nvar = n.getVarIndex();
		no = false;

		if(!list.get_st_hp())
		{
			if(var == nvar)
			{
				no = true;
			} 
		}

		if(!no)
		{
			return false;
		}
	}
		
	return true;
}

void print_GPU(gpu_id_type id)
{
	GPU gpu = GPU::gpu_map[id];

//	fprintf(dump_file, "\nGPU Extracted\n");
//	fflush(dump_file);

	gpu.printGPU();

//	fprintf(dump_file, "\nPrinted GPU\n");
//	fflush(dump_file);
}

void printSetOfGPUs(GPUSet gpus)
{
//	fprintf(dump_file, "\nInside printSetOfGPUs %d\n", gpus.size());
//	fflush(dump_file);

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
//		fprintf(dump_file, "\n*it\n");
//		fflush(dump_file);

		print_GPU(*it);
	}
}

void printSetOfGPUIDs(GPUSet gpus)
{
	unsigned int a, b, c, d, e, f, g;

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		a = get<0>(get<0>(*it));
		b = get<1>(get<0>(*it));
		c = get<2>(get<0>(*it));

		d = get<0>(get<1>(*it));
		e = get<1>(get<1>(*it));
		f = get<2>(get<1>(*it));
		
//		g = get<2>(*it);

		fprintf(dump_file, " (%d %d %d %d %d %d) ", a, b, c, d, e, f);
	}
}

GPUSet filterLocal(GPUSet gen, struct cgraph_node *cnode)
{
	unsigned int lvar, rvar;
	GPUSet res;

	for(GPUSet::iterator it = gen.begin(); it != gen.end(); it++)
	{
		lvar = get<0>(get<0>(*it));
		rvar = get<0>(get<1>(*it));

		if(CDV.find(lvar) != CDV.end())
		{
			--lvar;
		}

		if(CDV.find(rvar) != CDV.end())
		{
			--rvar;
		}

		if(isInScope(lvar, cnode))
		{
			if(!is_ssa_var(rvar))
				res.insert(*it);

			if(!(isInScope(rvar, cnode)))
			{
				escaped.insert(rvar);
			}
		}
	}

	return res;
}

bool isInScope(unsigned int var, struct cgraph_node *cnode)
{
	if(var <= 4)
		return false;

	#if 0
	fprintf(dump_file, "\nChecking for In Scope for Var = %s (%d) in function %s\n", get_var_name(var), var, cgraph_node_name(cnode));
	fflush(dump_file);
	fprintf(dump_file, "\nIs Var Global = %d?\n", global_var(var));
	fflush(dump_file);
	fprintf(dump_file, "\nIs Var escaped = %d?\n", escaped.find(var) != escaped.end());
	fflush(dump_file);
	#endif

	set<unsigned int> pars = ((function_info *)(cnode->aux))->get_params();

	#if 0
	fprintf(dump_file, "\nParameters of function %s\n", cgraph_node_name(cnode)); 
	fflush(dump_file);
	print_set_integers(pars);
	fflush(dump_file);
	#endif

	#ifndef MRB
	unsigned int ret_id = ((function_info *)(cnode->aux))->get_ret_id();
	#endif
	#ifdef MRB
	set< unsigned int > ret_id = ((function_info *)(cnode->aux))->get_ret_id();
	#endif

	#if 0
	fprintf(dump_file, "\nReturn ID for Function %s\n", cgraph_node_name(cnode));
	fflush(dump_file);

	#ifndef MRB
	fprintf(dump_file, "\nRet = %d\n", ret_id);	
	fflush(dump_file);
	#endif
	#ifdef MRB
	print_set_integers(ret_id);
	fflush(dump_file);
	#endif
	#endif

	#ifndef MRB
	if((global_var(var)) || (var == ret_id) || (pars.find(var) != pars.end()) || (escaped.find(var) != escaped.end()))
	#endif
	#ifdef MRB
	if((global_var(var)) || (ret_id.find(var) != ret_id.end()) || (pars.find(var) != pars.end()) || (escaped.find(var) != escaped.end()))
	#endif
	{
		#if 0
		fprintf(dump_file, "\nReturning True\n");
		fflush(dump_file);
		#endif	
		return true;
	}

	#if 0
	fprintf(dump_file, "\nReturning False\n");
	fflush(dump_file);
	#endif

	return false;
}

void printDefinitions(definitions defs)
{
	Node n;
	unsigned int var;
	IndirectionList list;

	for(definitions::iterator it = defs.begin(); it != defs.end(); it++)
	{
		n = getNode(*it);
		var = n.getVarIndex();
		list = n.getList();

		fprintf(dump_file, "\nVar %s - %d\n", get_var_name(var), var);		
		list.printIndirectionList();
	}
}

void printDefinitionsList(definitions_list defs)
{
	Node n;
	unsigned int var;
	IndirectionList list;
	definitions d;

	for(definitions_list::iterator it = defs.begin(); it != defs.end(); it++)
	{
		d = *it;

		for(definitions::iterator sit = d.begin(); sit != d.end(); sit++)
		{
			n = getNode(*sit);
			var = n.getVarIndex();
			list = n.getList();

			fprintf(dump_file, "\nVar %s - %d\n", get_var_name(var), var);		
			list.printIndirectionList();
		}
	}
}

bool isArrayTree(tree t)
{
	if(t == NULL)
	{
		return false;		
	}

	if(TREE_TYPE(t) && TREE_CODE(TREE_TYPE(t)) && (TREE_CODE(TREE_TYPE(t)) == ARRAY_TYPE || TREE_CODE(TREE_TYPE(t)) == ARRAY_REF))
	{
		return true;
	}

	return false;
}

bool isArray(unsigned int var)
{

//      fprintf(dump_file,"\nInside check_array\n");

        if(CDV.find(var) != CDV.end())
        {
//              fprintf(dump_file,"\nCDV\n");
                var = var - 1;
        }

//      fprintf(dump_file,"\nVar %s\n",get_var_name(var));

	if(var <= 4 )
                return false;

        tree u = VEC_index(csvarinfo_t,csvarmap,var)->decl;

        if(TREE_CODE(TREE_TYPE(u)) == ARRAY_TYPE || TREE_CODE(TREE_TYPE(u)) == ARRAY_REF)
        {
                return true;
        }

        return false;
}

gpu_id_type getCopyGPU(node_id_type nid)
{
	Node lhs = getNode(nid);
	unsigned int var = get<0>(nid);
	unsigned int lvar, rvar;

	if(CDV.find(var) != CDV.end())
	{
		rvar = var;
		lvar = --var;
	}
	else
	{
		lvar = var;
		rvar = ++var;
	}	

	IndirectionList list = lhs.getList();

	Node n1(lvar, list);
	Node n2(rvar, list);

	GPU gpu(n1, n2);

	return gpu.getGPUID();

	#if 0
	int f[IndirectionList::kSize];
	unsigned int len = list.Length();

	if(list.get_st_hp())
	{
		IndirectionList l(true, len, 0, f);

		Node rhs(lhs.getVarIndex()+1, l);
		GPU gpu(lhs, rhs);

		return gpu.getGPUID();
	}
	else
	{
		for(int i = 0; i < len; i++)
		{
			f[i] = SFIELD;
		}

		IndirectionList l(false, 0, len, f);

		Node rhs(lhs.getVarIndex()+1, l);
		GPU gpu(lhs, rhs);

		return gpu.getGPUID();
	}
	#endif
}

bool isStackGPU(gpu_id_type id)
{
	Node n = getNode(get<0>(id));
	Node m = getNode(get<1>(id));

	IndirectionList llist = n.getList();
	IndirectionList rlist = m.getList();

	return (llist.get_st_hp() && rlist.get_st_hp());
}

definitions FINodeReduction(bool type, node_id_type n_id, struct cgraph_node *cnode) // Source = 1, Target = 0
{
	definitions res, temp;

        // Base Condition

	if(type) // source
	{
		if(getLengthOfList(n_id) == 1)
		{
			res.insert(n_id);

			return res;
		}
	}
	else
	{
		if(getLengthOfList(n_id) == 0)
		{
			res.insert(n_id);

			return res;
		}
	}

	visitedFINodes.insert(n_id);
	
	GPUSet fi_data;
	definitions fi_temp;
	unsigned int var, n_var, t_var;

	n_var = get<0>(n_id);

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	fi_data = FIP[cnode_num][n_var];

	#if 0
	fprintf(dump_file, "\nfi_data\n");
	printSetOfGPUs(fi_data);
	#endif

	fi_temp = FIGPUComposition(type, n_id, fi_data, cnode);

	for(definitions::iterator dit = fi_temp.begin(); dit != fi_temp.end(); dit++)
	{
		if(visitedFINodes.find(*dit) == visitedFINodes.end())
		{
			temp = FINodeReduction(type, *dit, cnode);

			res.insert(temp.begin(), temp.end());
		}
	}

	if(res.empty())
	{
		res.insert(n_id);
	}	

	return res;
}

GPUSet FIComposition(GPUSet delta, struct cgraph_node *cnode)
{
	definitions lhs, rhs;
	GPUSet res;

	for(GPUSet::iterator it = delta.begin(); it != delta.end(); it++)
	{
		visitedFINodes.clear();

		lhs = FINodeReduction(true, get<0>(*it), cnode);

		visitedFINodes.clear();

		rhs = FINodeReduction(false, get<1>(*it), cnode);

		for(definitions::iterator lit = lhs.begin(); lit != lhs.end(); lit++)
		{
			for(definitions::iterator rit = rhs.begin(); rit != rhs.end(); rit++)
			{
				if(*lit == *rit)
				{
					continue;
				}
				
				GPU gpu(*lit, *rit);

				res.insert(gpu.getGPUID());	
			}
		}
	}		

	return res;
}

GPUSet FIComp(GPUSet delta, struct cgraph_node *cnode)
{
	definitions lhs, rhs;
	GPUSet res, fi_data;
	unsigned int lvar, rvar;
	bool composed;

	unsigned int cnode_num = ((function_info *)(cnode->aux))->func_num;

	for(GPUSet::iterator it = delta.begin(); it != delta.end(); it++)
	{
		composed = false;

		lvar = get<0>(get<0>(*it));
		rvar = get<0>(get<1>(*it));

		fi_data = FIP[cnode_num][lvar];

		lhs = FIGPUComposition(true, get<0>(*it), fi_data, cnode);

		fi_data = FIP[cnode_num][rvar];

		rhs = FIGPUComposition(false, get<1>(*it), fi_data, cnode);

		for(definitions::iterator lit = lhs.begin(); lit != lhs.end(); lit++)
		{
			if(get<0>(*lit) < 4)
			{
				continue;
			}

			for(definitions::iterator rit = rhs.begin(); rit != rhs.end(); rit++)
			{
				if(*lit == *rit)
				{
					continue;
				}

				composed = true;
				
				GPU gpu(*lit, *rit);

				res.insert(gpu.getGPUID());	
			}
		}

		if(!composed)
		{
			res.insert(*it);
		}
	}		

	return res;
}

set_tree_nodes fieldsType(set_tree_nodes res, unsigned int field)
{
	set_tree_nodes temp, result;

	for(set_tree_nodes::iterator rit = res.begin(); rit != res.end(); rit++)
	{
		temp = findFieldType(*rit, field);

		result.insert(temp.begin(), temp.end());
	}

	return result;
}

set_tree_nodes findFieldType(tree t, unsigned int field)
{
	set_tree_nodes res;
	
	if(field == SFIELD) 
	{
//		fprintf(dump_file, "\nField is *\n");

		if(TREE_TYPE(t) && POINTER_TYPE_P(t))
		{
//			fprintf(dump_file, "\nPointer Type\n");

			t = TREE_TYPE(t);

//			print_node(dump_file, "\nPT\n", t, 0);

			res.insert(t);
		}
	}
	else if(field == AFIELD) 
	{
//		fprintf(dump_file, "\nANY Field\n");

		tree field_tree, field_type, offset;
		long bitpos = 0;

		for(field_tree = TYPE_FIELDS(t); field_tree; field_tree = TREE_CHAIN(field_tree))
		{
			if(TREE_CODE(field_tree) != FIELD_DECL)
			{
				continue;
			}

			if(type_must_have_pointers (field_tree))
			{
				continue;
			}

			field_type = strip_array_types (TREE_TYPE (field_tree));

			t = field_type;

			res.insert(t);
		}
	}
	else
	{
//		fprintf(dump_file, "\nField %d\n", field);

		tree field_tree, field_type, offset;
		long bitpos = 0;

		for(field_tree = TYPE_FIELDS(t); field_tree; field_tree = TREE_CHAIN(field_tree))
		{
			if(TREE_CODE(field_tree) != FIELD_DECL)
			{
				continue;
			}

			if(type_must_have_pointers (field_tree))
			{
				continue;
			}

			field_type = strip_array_types (TREE_TYPE (field_tree));

			offset = DECL_FIELD_OFFSET(field_tree);

			if(host_integerp(offset, 0) && host_integerp(bit_position(field_tree), 0))
			{
				bitpos = int_bit_position(field_tree);
			}
			else
			{
				bitpos = tree_low_cst(DECL_FIELD_BIT_OFFSET(field_tree), 0);
			}

			if(bitpos == field)
			{					
//				print_node(dump_file, "\nFIELD TREE\n", field_tree, 0);
//				print_node(dump_file, "\nFIELD TREE TYPE\n", field_type, 0);

				t = field_type;

				res.insert(t);
						
				break;
			}
		}
	}

	return res;
}

std::pair< set_tree_nodes, set_tree_nodes >  computeTypeOfNode(node_id_type n, bool lhs)
{
	Node node = getNode(n);

	std::pair< set_tree_nodes, set_tree_nodes > result;

	set_tree_nodes def, ref, res;

	IndirectionList list = node.getList();
	unsigned int var = get<0>(n);

	if(var <= 4)
	{
		return result;
	}
	
	tree t;
	
	t = cs_get_varinfo(var)->decl;

	t = SSAVAR(t);

	if(TREE_CODE(t) && TREE_CODE(t) == VAR_DECL)
	{
		t = TREE_TYPE(t);
	}
	else if(TREE_CODE(t) && TREE_CODE(t) == PARM_DECL)
	{
		t = TREE_TYPE(t);
	}
	else if(TREE_CODE(t) && TREE_CODE(t) == RESULT_DECL)
	{
		t = TREE_TYPE(t);
	}	
	else if(TREE_CODE(t) && TREE_CODE(t) == SSA_NAME)
	{
		t = TREE_TYPE(t);
	}	

	unsigned int length = list.Length();
	unsigned int i;
	unsigned int field;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nExtracting type for %d\n", lhs);
	print_node(dump_file, "\nTree t\n", t, 0);
	#endif

	if(lhs) // Compute Def and Ref for the source
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nLHS\n");
		fflush(dump_file);
		#endif

		if(length == 1)
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nLength = 1\n");
			fflush(dump_file);
			#endif

			def.insert(t);
		}
		else if(list.get_st_hp()) // Types for pointers to scalars
		{	
			#if 0 //PRINT_DATA	
			fprintf(dump_file, "\nLength != 1 and pointer to stack with indlev = %d\n", length);
			fflush(dump_file);
			#endif

			for(i = 1; i < length; i++)
			{
				ref.insert(t);

//				print_node(dump_file, "\nRef(t)\n", t, 0);

				if(TREE_TYPE(t) && POINTER_TYPE_P(t))
				{
//					print_node(dump_file, "\nTree_TYPE t\n", TREE_TYPE(t), 0);

					t = TREE_TYPE(t);

//					print_node(dump_file, "\nTree t\n", t, 0);

					t = SSAVAR(t);

//					print_node(dump_file, "\nH VD SSA\n", t, 0);

					if(TREE_CODE(t) && TREE_CODE(t) == VAR_DECL)
					{
						t = TREE_TYPE(t);

//						print_node(dump_file, "\nR VD\n", t, 0);
					}
					else if(TREE_CODE(t) && TREE_CODE(t) == PARM_DECL)
					{
						t = TREE_TYPE(t);
					}
					else if(TREE_CODE(t) && TREE_CODE(t) == RESULT_DECL)
					{
						t = TREE_TYPE(t);
					}	
					else if(TREE_CODE(t) && TREE_CODE(t) == SSA_NAME)
					{
						t = TREE_TYPE(t);
					}
				}
			}

			#if 0 //PRINT_DATA	
			print_node(dump_file, "\nDef(t)\n", t, 0);
			fflush(dump_file);
			#endif

			def.insert(t);
		}
		else // Types for pointers to structures
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nLength != 1 and pointer to structure with indlev = %d\n", length);
			fflush(dump_file);
			#endif

			res.insert(t);

			for(i = 0; i < length; i++)
			{
				ref.insert(res.begin(), res.end());

//				fprintf(dump_file, "\nRef(t)\n");
//				print_set_tree_nodes(res);

				field = list.at(i);

				res = fieldsType(res, field);

				set_tree_nodes res1;

				for(set_tree_nodes::iterator it = res.begin(); it != res.end(); it++)
				{
					t = *it;

					t = SSAVAR(t);

//					print_node(dump_file, "\nH VD SSA\n", t, 0);

					if(TREE_CODE(t) && TREE_CODE(t) == VAR_DECL)
					{
						t = TREE_TYPE(t);

//						print_node(dump_file, "\nR VD\n", t, 0);
					}
					else if(TREE_CODE(t) && TREE_CODE(t) == PARM_DECL)
					{
						t = TREE_TYPE(t);
					}
					else if(TREE_CODE(t) && TREE_CODE(t) == RESULT_DECL)
					{
						t = TREE_TYPE(t);
					}	
					else if(TREE_CODE(t) && TREE_CODE(t) == SSA_NAME)
					{
						t = TREE_TYPE(t);
					}

					res1.insert(t);
				}

				res.clear();
				res.insert(res1.begin(), res1.end());

				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nRef'(t)\n");
				print_set_tree_nodes(res);
				fflush(dump_file);
				#endif
			}

			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nDef(t)\n");
			print_set_tree_nodes(res);
			fflush(dump_file);
			#endif

			def.insert(res.begin(), res.end());
		}
	}
	else // Compute Ref for the target
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nRHS\n");
		fflush(dump_file);
		#endif

		if(length == 0)
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nLength = 0\n");
			fflush(dump_file);
			#endif

//			ref.insert(NULL);
		}	
		else if(length == 1)
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nLength = 1\n");
			fflush(dump_file);
			#endif

			ref.insert(t);
		}
		else if(list.get_st_hp())
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nLength != 1 and pointer to stack with indlev = %d\n", length);
			fflush(dump_file);
			#endif

			for(i = 1; i < length; i++)
			{
				ref.insert(t);

//				print_node(dump_file, "\nRef(t)\n", t, 0);

				if(TREE_TYPE(t) && POINTER_TYPE_P(t))
				{
					t = TREE_TYPE(t);

					t = SSAVAR(t);

//					print_node(dump_file, "\nH VD SSA\n", t, 0);

					if(TREE_CODE(t) && TREE_CODE(t) == VAR_DECL)
					{
						t = TREE_TYPE(t);

//						print_node(dump_file, "\nR VD\n", t, 0);
					}
					else if(TREE_CODE(t) && TREE_CODE(t) == PARM_DECL)
					{
						t = TREE_TYPE(t);
					}
					else if(TREE_CODE(t) && TREE_CODE(t) == RESULT_DECL)
					{
						t = TREE_TYPE(t);
					}	
					else if(TREE_CODE(t) && TREE_CODE(t) == SSA_NAME)
					{	
						t = TREE_TYPE(t);
					}
				}
			}
		}
		else
		{
			#if 0 //PRINT_DATA
			fprintf(dump_file, "\nLength != 1 and pointer to stack with indlev = %d\n", length);
			print_node(dump_file, "\ntree node\n", t, 0);
			fflush(dump_file);
			#endif

			res.insert(t);

			for(i = 0; i < length; i++)
			{
				ref.insert(res.begin(), res.end());

				#if 0 //PRINT_DATA
				fprintf(dump_file, "\nRef(t)\n");
				print_set_tree_nodes(res);
				fflush(dump_file);
				#endif

				field = list.at(i);

				res = fieldsType(res, field);

				set_tree_nodes res1;

				for(set_tree_nodes::iterator it = res.begin(); it != res.end(); it++)
				{
					t = *it;

					t = SSAVAR(t);

//					print_node(dump_file, "\nH VD SSA\n", t, 0);

					if(TREE_CODE(t) && TREE_CODE(t) == VAR_DECL)
					{
						t = TREE_TYPE(t);

//						print_node(dump_file, "\nR VD\n", t, 0);
					}
					else if(TREE_CODE(t) && TREE_CODE(t) == PARM_DECL)
					{
						t = TREE_TYPE(t);
					}
					else if(TREE_CODE(t) && TREE_CODE(t) == RESULT_DECL)
					{
						t = TREE_TYPE(t);
					}	
					else if(TREE_CODE(t) && TREE_CODE(t) == SSA_NAME)
					{
						t = TREE_TYPE(t);
					}

					res1.insert(t);
				}

				res.clear();
				res = res1;
			}
		}
	}

	result = std::make_pair(def, ref);

	return result;
}

set_tree_nodes extractTypeOfExpression(node_id_type n)
{
	Node node = getNode(n);

	set_tree_nodes res;	

	IndirectionList list = node.getList();
	unsigned int var = node.getVarIndex();

	tree t = cs_get_varinfo(var)->decl;

	unsigned int length = list.Length();

	if(length == 0)
	{
//		fprintf(dump_file, "\nAddress Of\n");

		res.insert(NULL);

		return res;
	}
	else if(length == 1)
	{
//		fprintf(dump_file, "\nOne Indirection\n");

		res.insert(t);

		return res;
	}
	else if(list.get_st_hp())
	{
//		print_node(dump_file, "\nPointer to Scalar\n", t, 0);

		res.insert(t);

		return res;
	}
	else
	{
//		print_node(dump_file, "\nPointer to Structure\n", t, 0);
		
//		fprintf(dump_file, "\nLength of List = %d\n", length);

		int i;
		unsigned int field;
		set_tree_nodes res;
		res.insert(t);

		for(i=0; i < length; i++)
		{
			field = list.at(i);

			res = fieldsType(res, field);
		}

		return res;
	}	
}

void collectTypeInfoForGPUSet(struct cgraph_node *cnode, GPUSet gpus, bool orig)
{
	node_id_type s, t, si, ti;
	set_tree_nodes temp;
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

		if(lvar <= 4)
		{
			NodeType[s] = null_set;
			NodeType[si] = null_set;
		}
		else if(NodeType.find(s) == NodeType.end())
		{
//			fprintf(dump_file, "\nNew Source Node\n");

			temp = extractTypeOfExpression(s);

			NodeType[s] = temp;
			NodeType[si] = temp;
		}

		if(rvar <= 4)
		{
			NodeType[t] = null_set;
			NodeType[ti] = null_set;
		}
		else if(NodeType.find(t) == NodeType.end())
		{
//			fprintf(dump_file, "\nNew Target Node\n");

			temp = extractTypeOfExpression(t);

			NodeType[t] = temp;
			NodeType[ti] = temp;
		}

//		print_node(dump_file, "\nNodeType s\n", NodeType[s], 0);
//		print_node(dump_file, "\nNodeType t\n", NodeType[t], 0);
	}
}

void computeDefRefForGPUSet(struct cgraph_node *cnode, GPUSet gpus, bool orig)
{
	node_id_type s, t, si, ti;
	set_tree_nodes temp, def, ref;
	std::pair< set_tree_nodes, set_tree_nodes > res;
	Node lhs, rhs, lhsi, rhsi;
	unsigned int lvar, lvari, rvar, rvari;
	IndirectionList llist, rlist;

	for(GPUSet::iterator it = gpus.begin(); it != gpus.end(); it++)
	{
		s = get<0>(*it);
		t = get<1>(*it);

		lhs = getNode(s);	
		rhs = getNode(t);	

		lvar = get<0>(s);
		rvar = get<0>(t);

		llist = lhs.getList();
		rlist = rhs.getList();

		if(llist.Length() != 1)
		{
			if(CDV.find(lvar) != CDV.end())
			{
				lvari = --lvar;
			}
			else
			{
				lvari = ++lvar;
			}

			lhsi = Node(lvari, llist);
			si = lhsi.getNodeID();
		}
		else
		{
			lhsi = lhs;
		}

		if(rlist.Length() != 0)
		{
			if(CDV.find(rvar) != CDV.end())
			{
				rvari = --rvar;
			}
			else
			{
				rvari = ++rvar;
			}
		
			rhsi = Node(rvari, rlist);
			ti = rhsi.getNodeID();
		}
		else
		{
			rhsi = rhs;
		}
		
		GPU n_gpu(lhsi, rhsi);
		gpu_id_type ngid = n_gpu.getGPUID();

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nExtracting Types\n");
		print_GPU(*it);
		print_GPU(ngid);
		#endif

		set_tree_nodes null_set;
		null_set.insert(NULL);

		if(DefTypes.find(*it) == DefTypes.end() && RefTypes.find(*it) == RefTypes.end())
		{
			if(!art_var(get<0>(s)))
			{
				res = computeTypeOfNode(s, true);

				temp = get<0>(res);

				def.insert(temp.begin(), temp.end());

				temp = get<1>(res);

				ref.insert(temp.begin(), temp.end());
			}

			if(!art_var(get<0>(t)))
			{
				res = computeTypeOfNode(t, false);

				temp = get<1>(res);

				ref.insert(temp.begin(), temp.end());
			}

			if(art_var(get<0>(s)))
			{
				def = ref;
			}

			if(art_var(get<0>(t)))
			{
				ref = def;
			}	

			#if 0 // PRINT_DATA
			fprintf(dump_file, "\nHey Def\n");
			print_set_tree_nodes(def);
			fprintf(dump_file, "\nHey Ref\n");
			print_set_tree_nodes(ref);
			#endif

			DefTypes[*it] = def;
			RefTypes[*it] = ref;

			DefTypes[ngid] = def;
			RefTypes[ngid] = ref;
		}

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nGPU\n");
		print_GPU(*it);
		fprintf(dump_file, "\nDef of GPU\n");
		print_set_tree_nodes(DefTypes[*it]);
		fprintf(dump_file, "\nRef of GPU\n");
		print_set_tree_nodes(RefTypes[*it]);
		#endif
	}

//	recordDataDependenceForGPUSet(gpus);
}

bool isDataDependencePresent(gpu_id_type p, gpu_id_type c)
{
	set_tree_nodes defp, defc, refc, res;

	defp = DefTypes[p];

	defc = DefTypes[c];
	refc = RefTypes[c];

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nDefp\n");
	print_set_tree_nodes(defp);
	fprintf(dump_file, "\nDefc\n");
	print_set_tree_nodes(defc);
	fprintf(dump_file, "\nRefc\n");
	print_set_tree_nodes(refc);
	#endif

	refc.insert(defc.begin(), defc.end());

	#if 0
	fprintf(dump_file, "\nRefc'\n");
	print_set_tree_nodes(refc);
	#endif

	set_intersection(defp.begin(), defp.end(), refc.begin(), refc.end(), inserter(res, res.end()));

	#if 0
	fprintf(dump_file, "\nres\n");
	print_set_tree_nodes(res);
	#endif

	if(!res.empty())
	{
		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nDDep True\n");
		fflush(dump_file);
		#endif

		return true;
	}

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nDDep False\n");
	fflush(dump_file);
	#endif

	return false;
}

void recordDataDependence(GPUSet p_gpus, GPUSet c_gpus)
{
	GPUSet temp;

	for(GPUSet::iterator pit = p_gpus.begin(); pit != p_gpus.end(); pit++)
	{
		if(isBoundaryGPU(*pit))
		{
			continue;
		}
		#if 0
		else if(!(isDerefGPU(*pit)))
		{
			continue;
		}
		#endif

		for(GPUSet::iterator cit = c_gpus.begin(); cit != c_gpus.end(); cit++)
		{
			if(*pit == *cit)
			{
				continue;
			}
			else if(get<0>(*pit) == get<0>(*cit))
			{
				continue;
			}
			else if(isBoundaryGPU(*cit))
			{
				continue;
			}
			else if((!(isDerefGPU(*pit))) && (!(isDerefGPU(*cit))))
			{
				continue;
			}

			#if  0 //PRINT_DATA
			fprintf(dump_file, "\nChecking DDep\n");
			fprintf(dump_file, "\np GPU\n");
			print_GPU(*pit);
			fprintf(dump_file, "\nc GPU\n");
			print_GPU(*cit);
			#endif

			#if 0
			fprintf(dump_file, "\nChecking DDep\n");
			fprintf(dump_file, "\np GPU\n");
			print_GPU(*pit);
			fprintf(dump_file, "\nDef of p GPU\n");
			print_set_tree_nodes(DefTypes[*pit]);
			fprintf(dump_file, "\nRef of p GPU\n");
			print_set_tree_nodes(RefTypes[*pit]);
			fprintf(dump_file, "\nc GPU\n");
			print_GPU(*cit);
			fprintf(dump_file, "\nDef of c GPU\n");
			print_set_tree_nodes(DefTypes[*cit]);
			fprintf(dump_file, "\nRef of c GPU\n");
			print_set_tree_nodes(RefTypes[*cit]);
			#endif

			if(isDataDependencePresent(*pit, *cit))
			{
				temp = typeCompatibleGPUs[*cit];	

				temp.insert(*pit);

				typeCompatibleGPUs[*cit] = temp;
			}
		}
	}
}

void recordDataDependenceForGPUSet(GPUSet gpus)
{
	GPUSet temp;

	for(GPUSet::iterator pit = gpus.begin(); pit != gpus.end(); pit++)
	{
		if(isBoundaryGPU(*pit))
		{
			continue;
		}
		#if 0
		else if(!(isDerefGPU(*pit)))
		{
			continue;
		}
		#endif

		for(GPUSet::iterator cit = gpus.begin(); cit != gpus.end(); cit++)
		{
			if(*pit == *cit)
			{
				continue;
			}
			else if(get<0>(*pit) == get<0>(*cit))
			{
				continue;
			}
			else if(isBoundaryGPU(*cit))
			{
				continue;
			}
			else if((!(isDerefGPU(*pit))) && (!(isDerefGPU(*cit))))
			{
				continue;
			}

			#if  0 //PRINT_DATA
			fprintf(dump_file, "\nChecking DDep\n");
			fprintf(dump_file, "\np GPU\n");
			print_GPU(*pit);
			fprintf(dump_file, "\nc GPU\n");
			print_GPU(*cit);
			#endif

			#if 0
			fprintf(dump_file, "\nChecking DDep\n");
			fprintf(dump_file, "\np GPU\n");
			print_GPU(*pit);
			fprintf(dump_file, "\nDef of p GPU\n");
			print_set_tree_nodes(DefTypes[*pit]);
			fprintf(dump_file, "\nRef of p GPU\n");
			print_set_tree_nodes(RefTypes[*pit]);
			fprintf(dump_file, "\nc GPU\n");
			print_GPU(*cit);
			fprintf(dump_file, "\nDef of c GPU\n");
			print_set_tree_nodes(DefTypes[*cit]);
			fprintf(dump_file, "\nRef of c GPU\n");
			print_set_tree_nodes(RefTypes[*cit]);
			#endif

			if(isDataDependencePresent(*pit, *cit))
			{
				temp = typeCompatibleGPUs[*cit];	

				temp.insert(*pit);

				typeCompatibleGPUs[*cit] = temp;
			}
		}
	}
}

GPUSet computeBlockedGPUs(GPUSet in, GPUSet bar)
{
	GPUSet temp, block;

	#if 0 //PRINT_DATA
	fprintf(dump_file, "\nIn\n");
	printSetOfGPUs(in);
	fflush(dump_file);
	fprintf(dump_file, "\nBar\n");
	printSetOfGPUs(bar);
	fflush(dump_file);
	#endif

//	recordDataDependenceForGPUSet(fin_gpus);
	recordDataDependence(in, bar);

	for(GPUSet::iterator it = bar.begin(); it != bar.end(); it++)
	{
		if(isBoundaryGPU(*it))
		{
			continue;
		}

		GPUSet res;

		temp = typeCompatibleGPUs[*it];

		#if 0 //PRINT_DATA
		fprintf(dump_file, "\nRIN GPU\n");
		print_GPU(*it);
		fprintf(dump_file, "\nCompatible GPUs\n");
		printSetOfGPUs(temp);
		#endif

		set_intersection(temp.begin(), temp.end(), in.begin(), in.end(), inserter(res, res.end()));

		if(!res.empty())
		{
			block.insert(res.begin(), res.end());
		}
	}

	return block;
}

bool skipFunction(unsigned int id)

{
	struct cgraph_node *cnode;

	cnode = func_numbering[id];

	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "MAYPOINTTO") == 0)
		return true;

	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "MUSTPOINTTO") == 0)
		return true;
	
	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "DOESNTPOINTTO") == 0)
		return true;

	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "POINTSTOSET") == 0)
		return true;

	return false;
}
