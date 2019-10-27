#include "CoalescingAbstraction.h"
#include <vector>

using namespace std;


void CoalescingAbstraction::addPart(unsigned int id, GPBSet set)
{
	cmap[id] = set;	

	for(GPBSet::iterator it = set.begin(); it != set.end(); it++)
	{
		reverse_cmap[*it] = id;
	}
}


void CoalescingAbstraction::removePart(unsigned int id)
{
	GPBSet set = cmap[id];

	cmap.erase(id); 

	for(GPBSet::iterator it = set.begin(); it != set.end(); it++)
	{
		reverse_cmap.erase(*it);
	}
}

void CoalescingAbstraction::addGPBFromPart(unsigned int id, unsigned int gpb_id)
{
	GPBSet set = cmap[id];

	set.insert(gpb_id);

	cmap[id] = set;

	reverse_cmap[gpb_id] = id;
}


void CoalescingAbstraction::removeGPBFromPart(unsigned int id, unsigned int gpb_id)	
{
	GPBSet set = cmap[id];

	if(set.find(gpb_id) != set.end())
	{
		set.erase(gpb_id);

		cmap[id] = set;
	}

	reverse_cmap.erase(gpb_id);
}

void CoalescingAbstraction::addGPBsFromPart(unsigned int id, GPBSet gpbs)
{
	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		addGPBFromPart(id, *it);
	}
}
	
void CoalescingAbstraction::removeGPBsFromPart(unsigned int id, GPBSet gpbs)
{
	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		removeGPBFromPart(id, *it);
	}
}

GPBSet CoalescingAbstraction::getEntryForPart(unsigned int id)
{
	GPBSet gpbs = cmap[id];
	GPBSet temp, entry;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		temp = g.getPrev(*it);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			if(gpbs.find(*pit) == gpbs.end())
			{
				entry.insert(*it);

				break;
			}
		}

	}

	return entry;	
}

GPBSet CoalescingAbstraction::getExitForPart(unsigned int id)
{
	GPBSet gpbs = cmap[id];
	GPBSet temp, exit;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		temp = g.getNext(*it);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			if(gpbs.find(*pit) == gpbs.end())
			{
				exit.insert(*it);

				break;
			}
		}

	}

	return exit;	
}

unsigned int CoalescingAbstraction::getPartNumber(unsigned int gpb_id)
{
	return reverse_cmap[gpb_id];
}

GPBSet CoalescingAbstraction::getGPBsFromPart(unsigned int id)
{
	return cmap[id];
}

GPBSet CoalescingAbstraction::getSuccPart(unsigned int id)
{
	GPBSet succs, gpbs, temp;

	gpbs = getExitForPart(id);

	unsigned int succ_id;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		temp = g.getNext(*it);

		for(GPBSet::iterator sit = temp.begin(); sit != temp.end(); sit++)
		{
			succ_id = getPartNumber(*sit);

			if(succ_id != id)
			{
				succs.insert(succ_id);
			}
		}	
	}

	return succs;
}

GPBSet CoalescingAbstraction::getPredPart(unsigned int id)
{
	GPBSet preds, gpbs, temp;

	gpbs = getEntryForPart(id);

	unsigned int pred_id;

	for(GPBSet::iterator it = gpbs.begin(); it != gpbs.end(); it++)
	{
		temp = g.getPrev(*it);

		for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
		{
			pred_id = getPartNumber(*pit);

			if(pred_id != id)
			{
				preds.insert(pred_id);
			}
		}	
	}

	return preds;
}

GPBSet CoalescingAbstraction::getNSuccPart(unsigned int id, unsigned int gpb_id)
{
	GPBSet succs, succs_part, temp;

	succs_part = getSuccPart(id);

	temp = g.getNext(gpb_id);

	unsigned int succ_id;

	for(GPBSet::iterator sit = temp.begin(); sit != temp.end(); sit++)
	{
		succ_id = getPartNumber(*sit);

		if(succ_id == id)
		{
			continue;
		}

		if(succs_part.find(succ_id) != succs_part.end())
		{	
			succs.insert(succ_id);
		}
	}	

	return succs;
}

GPBSet CoalescingAbstraction::getNPredPart(unsigned int id, unsigned int gpb_id)
{
	GPBSet preds, preds_part, temp;

	preds_part = getPredPart(id);

	temp = g.getPrev(gpb_id);

	unsigned int pred_id;

	for(GPBSet::iterator pit = temp.begin(); pit != temp.end(); pit++)
	{
		pred_id = getPartNumber(*pit);

		if(pred_id == id)
		{
			continue;	
		}

		if(preds_part.find(pred_id) != preds_part.end())
		{
			preds.insert(pred_id);
		}
	}	

	return preds;
}

bool CoalescingAbstraction::checkRegularPart(unsigned int id)
{
	GPBSet entry, exit, temp1, temp2;

	entry = getEntryForPart(id);
	exit = getExitForPart(id);

	GPBSet:: iterator it;

	it = entry.begin();

	temp1 = getNPredPart(id, *it);

	it++;

	for(; it != entry.end(); it++)
	{
		temp2 = getNPredPart(id, *it);

		if(temp1 != temp2)
		{
			return false;
		}
	}

	it = exit.begin();

	temp1 = getNSuccPart(id, *it);

	it++;

	for(; it != exit.end(); it++)
	{
		temp2 = getNSuccPart(id, *it);

		if(temp1 != temp2)
		{
			return false;
		}
	}

	return true;
}

unsigned int CoalescingAbstraction::makeRegularPart(unsigned int id, unsigned int part_num)
{
	if(cmap[id].size() <= 1)
	{
		return part_num;
	}

	if(checkRegularPart(id))
	{
		return part_num;
	}

	GPBSet succs;
	GPB gpb;
	GPBSet temp_coalesce;

	temp_coalesce = cmap[id];
	GPBSet coalesce = cmap[id];

	GPBSet exit = getExitForPart(id);

	for(GPBSet::iterator it = exit.begin(); it != exit.end(); it++)
	{
		removeGPBFromPart(id, *it);	
		
		GPBSet temp;

		temp.insert(*it);

		addPart(part_num++, temp);	
	}

	if(coalesce.empty())
	{
		return part_num;
	}

	if(coalesce != temp_coalesce)
	{
		removePart(id);

		addPart(part_num++, coalesce);

		makeRegularPart(part_num-1, part_num);
	}

	return part_num;
}
