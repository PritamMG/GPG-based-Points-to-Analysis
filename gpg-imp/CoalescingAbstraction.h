#ifndef Coalescing_H_
#define Coalescing_H_

#include "GPG.h"
#include "cgraph_node.hpp"
#include "basic_block.hpp"
#include <vector>
#include <map>
#include <string>

class CoalescingAbstraction
{
	private:

		GPG g;
		std::map< unsigned int, GPBSet > cmap;
		std::map< unsigned int, unsigned int > reverse_cmap;

	public:

		// Constructor
		CoalescingAbstraction(GPG gpg) {g = gpg;}

		void addPart(unsigned int id, GPBSet set);
		void removePart(unsigned int id);
		
		void addGPBFromPart(unsigned int id, unsigned int gpb_id);	
		void removeGPBFromPart(unsigned int id, unsigned int gpb_id);	

		void addGPBsFromPart(unsigned int id, GPBSet gpbs);	
		void removeGPBsFromPart(unsigned int id, GPBSet gpbs);	

		GPBSet getEntryForPart(unsigned int id);
		GPBSet getExitForPart(unsigned int id);

		GPBSet getSuccPart(unsigned int id);
		GPBSet getPredPart(unsigned int id);

		GPBSet getNSuccPart(unsigned int id, unsigned int gpb_id);
		GPBSet getNPredPart(unsigned int id, unsigned int gpb_id);

		unsigned int getPartNumber(unsigned int gpb_id);
		GPBSet getGPBsFromPart(unsigned int id);

		bool checkRegularPart(unsigned int id);
		unsigned int makeRegularPart(unsigned int id, unsigned int part_num);

};

#endif  

