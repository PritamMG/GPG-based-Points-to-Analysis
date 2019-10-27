#ifndef INDIRECTION_LIST_H_
#define INDIRECTION_LIST_H_

#include <algorithm> // std::copy
#include "parser.hpp"
#include "Profile.h"

#include <vector> 
#define SFIELD -1
#define AFIELD -2
#define k_thresh 3 // fi_thresh <= k_thresh
#define fi_thresh 3
#define GPB_THRESH 0

//using namespace std;

/**
 * level and list of fields of a pointer
 */
class IndirectionList {

	public:
		static const size_t kSize = 8;
		using iterator = int *;
		using const_iterator = const int *;	

		IndirectionList()
		{
			star_count = 0;
			length = 0;
			st_hp = false;
		}

		// PS default constructor
		IndirectionList(bool sh, int scount, int l, int f[kSize])
		{
			st_hp = sh;
			star_count = scount;
			length = l;

//			fprintf(dump_file,"\nst_hp %d, Star Count %d, Length %d\n", sh, scount, l);
//			fflush(dump_file);

			if(!st_hp)
			{
//				fprintf(dump_file,"\nAggregate Type\n");
//				fflush(dump_file);

				if(length > k_thresh)
				{
//					fprintf(dump_file, "\nK-limiting IL\n");
				
					length =  k_thresh;

					for(int i = 0; i < k_thresh; i++)
					{
						field_list[i] = f[i];

//						fprintf(dump_file,"\nf[%d] = %d\n", i, f[i]);
//						fflush(dump_file);
					}
				}
				else
				{
//					fprintf(dump_file, "\nNo K-limiting IL\n");
				
					for(int i = 0; i < length; i++)
					{
						field_list[i] = f[i];

//						fprintf(dump_file,"\nf[%d] = %d\n", i, f[i]);
//						fflush(dump_file);
					}
				}
			}

//			fprintf(dump_file,"\nScalar Type\n");
//			fflush(dump_file);

//			printIndirectionList();

//			fprintf(dump_file,"\nEnd of Constructor\n");
//			fflush(dump_file);
		}

		// PS insert a field into the list at the back
		IndirectionList insertField(int field);

		// PS remove a field into the list at the back
		IndirectionList removeFirstField();

		IndirectionList changeFirstField();

		IndirectionList append(IndirectionList ind_list); // ind_list1.append(ind_list2) => ind_list1 ++ ind_list2
		std::vector< IndirectionList > append_list(std::vector< IndirectionList > list);

		std::vector< IndirectionList > remainder(IndirectionList ind_list); // ind_list1.remainder(ind_list2) => ind_list1 = ind_list2 ++ ind_list_3
	
		// PS true if field list is empty, there are no struct's or array's involved
		bool isFieldListEmpty() {
		return !length;
		}

		// BB true if argument is a prefix of this indirection list,
		// BB else false
		bool isPrefix(IndirectionList );

		// BB true if argument is a proper prefix of this indirection list,
		// BB else false
		bool isProperPrefix(IndirectionList );

		// BB true if argument equals to this indirection list, else false
		bool isEqual(IndirectionList );

		// PS get the indirection level
		int getStarCount() const
		{ 
			return star_count;
		}

		// PS set the indirection level
		void setStarCount(int star_count)
		{
			star_count = star_count;
		}

		// PS get the st_hp
		bool get_st_hp() const
		{
			return st_hp;
		}

		// PS set the st_hp 
		void set_st_hp()
		{
			st_hp = true;
		}

		// PS reset the st_hp 
		void reset_st_hp()
		{
			st_hp = false;
		}

		// PS get the length of the field list
		int getLength() const
		{
			return length;
		}

		// PS set the length of the field list
		void setLength(int l)
		{
			length = l;
		}

		// PS begin iterator of the field list
		iterator begin()
		{
			return field_list;
		}

		const_iterator begin() const
		{
			return field_list;
		}

		// PS end iterator of teh field list
		iterator end()
		{
			return field_list + length;
		}

		const_iterator end() const
		{
			return field_list;
		}

		int &at(size_t i)
		{
			return field_list[i];
		}

		const int &at(size_t i) const
		{
		        return field_list[i];
		}

		unsigned int Length();
		bool stackIndirectionList();

		bool operator==(const IndirectionList &rhs) const;

		bool doesNotExceed(IndirectionList ind_list); // ind_list1->doesNotExceed(ind_list2) returns true when ind_list1->Length <= ind_list2->Length

		void printIndirectionList();

		bool checkIndirectionList();

	private:
		// counts the indirection level (i.e. start operator)
		int star_count;

		// the length of the array field_list
		int length;

		// the indirection-list list of field member's id
		// if prefix is(are) star(s), their cound is stored in star_count_
		int field_list[kSize];

		bool st_hp; // stack => true, heap => false	
};

void printFieldList(int *field_list, int length);
#endif
