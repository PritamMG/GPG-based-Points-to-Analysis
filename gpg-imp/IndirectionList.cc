#include "IndirectionList.h"
#include <cstring>
#include <cassert>

bool IndirectionList::isProperPrefix(IndirectionList ind_list) // ind_list1.is_prefix(ind_list2) => ind_list1 < ind_list2
{
	// Call isPrefix and check Length

	if(isPrefix(ind_list) && Length() < ind_list.Length())
		return true;

	return false;
}

bool IndirectionList::isPrefix(IndirectionList ind_list) // ind_list1.is_prefix(ind_list2) => ind_list1 <= ind_list2
{
	bool st_hp_1 = get_st_hp();
	bool st_hp_2 = ind_list.get_st_hp();

	if(Length() > ind_list.Length())
		return false;

	if(st_hp_1 && st_hp_2)
	{
		return getStarCount() <= ind_list.getStarCount();
	}
	else if(st_hp_1 && !st_hp_2)
	{
		int star_count_1 = getStarCount();
		int *field_list_2 = ind_list.begin();

		for(int i = 0; i < star_count_1; i++)
		{
			if((field_list_2[i] != SFIELD) && (field_list_2[i] != AFIELD))
			{
				return false;
			}
		}

		return true;
	}
	else if(!st_hp_2 && !st_hp_2)
	{
		int *field_list_1 = begin();
		int *field_list_2 = ind_list.begin();
		int length = getLength();

		for(int i = 0; i < length; i++)
		{
			if((field_list_1[i] != AFIELD) && (field_list_2[i] != AFIELD))
			{
				if(field_list_1[i] != field_list_2[i])
				{
					return false;
				}
			}
		}

		return true;
	}
	else 
	{
		int star_count_2 = ind_list.getStarCount();
		int *field_list_1 = begin();
		int length = Length();

		for(int i = 0; i < length; i++)
		{
			if((field_list_1[i] != SFIELD) && (field_list_1[i] != AFIELD))
			{
				return false;
			}
		}

		return true;
	}
}

bool IndirectionList::isEqual(IndirectionList ind_list)
{
	if(this->isPrefix(ind_list) && ind_list.isPrefix(*this))
	{
		return true;
	}

	return false;
}

std::vector< IndirectionList > IndirectionList::remainder(IndirectionList ind_list) // ind_list1.remainder(ind_list2) => ind_list1 = ind_list2 ++ ind_list_3
{
	std::vector< IndirectionList > res;
	int length1 = Length();
	int length2 = ind_list.Length();

	if(length1 < length2)
		return res;

	#if 0
	if(!ind_list->isPrefix(this))
		return res;	
	#endif

	bool st_hp_1 = get_st_hp();
	bool st_hp_2 = ind_list.get_st_hp();

	if(st_hp_1 && st_hp_2) // Both are scalars
	{
		int star_count_1 = getStarCount();
		int star_count_2 = ind_list.getStarCount();
		int field_list[IndirectionList::kSize];

		IndirectionList l(st_hp_1, star_count_1 - star_count_2, 0, field_list);
		res.push_back(l);	

		gcc_assert(res.size() == 1);

		return res;
	}
	else if(!st_hp_1 && st_hp_2) // First ind_list is heap and second is stack
	{
		int star_count_2 = ind_list.getStarCount();
		int *field_list_1 = begin();
		int field_list[IndirectionList::kSize];
		int i = 0;

		for(; i < star_count_2; i++)
		{
			if((field_list_1[i] != SFIELD) && (field_list_1[i] != AFIELD))
			{
				gcc_assert(res.size() == 1);

				return res;
			}
		}
		
		for(int l = i, m = 0; l < length1; l++, m++)
		{
			field_list[m] = field_list_1[l];
		}

		if(length1 == k_thresh)
		{
			IndirectionList t_list(st_hp_1, 0, length1-star_count_2, field_list);
//			res.push_back(t_list);

			for(int j = length-star_count_2; j < k_thresh; j++)
			{
				t_list = t_list.insertField(AFIELD);		
			}

			if(find(res.begin(), res.end(), t_list) == res.end())	
			{
				res.push_back(t_list);
			}

			gcc_assert(res.size() == 1);

			return res;
		}
		else
		{
			IndirectionList l(st_hp_1, 0, length1-star_count_2, field_list);
			res.push_back(l);

			gcc_assert(res.size() == 1);

			return res;
		}
	}
	else if(!st_hp_1 && !st_hp_2)
	{
		int *field_list_1 = begin();
		int *field_list_2 = ind_list.begin();
		int field_list[IndirectionList::kSize];
		int i;

		for(i = 0; i < length2; i++)
		{
			if((field_list_1[i] != AFIELD) && (field_list_2[i] != AFIELD))
			{
				if(field_list_1[i] != field_list_2[i])
				{
					gcc_assert(res.size() == 1);

					return res;
				}
			}
		}

		for(int l = i, m = 0; l < length1; l++, m++)
		{
			field_list[m] = field_list_1[l];
		}

		if(length1 == k_thresh)
		{
			IndirectionList t_list(st_hp_1, 0, length1-length2, field_list);
//			res.push_back(t_list);

			for(int j = length1-length2; j < k_thresh; j++)
			{
				t_list = t_list.insertField(AFIELD);		
			}

			if(find(res.begin(), res.end(), t_list) == res.end())	
			{
				res.push_back(t_list);
			}

			gcc_assert(res.size() == 1);

			return res;
		}
		else
		{
			IndirectionList t_list(st_hp_1, 0, length1-length2, field_list);
			res.push_back(t_list);

			gcc_assert(res.size() == 1);

			return res;
		}
	}
	else
	{
		int star_count_1 = getStarCount();
		int *field_list_2 = ind_list.begin();
		int field_list[IndirectionList::kSize];
		int i = 0;

		for(; i < length2; i++)
		{
			if((field_list_2[i] != SFIELD) && (field_list_2[i] != AFIELD))
			{
				gcc_assert(res.size() == 1);

				return res;
			}
		}

		for(int l = i, m = 0; l < length1; l++, m++)
		{
			field_list[m] = SFIELD;
		}

		IndirectionList t_list(st_hp_2, 0, length1-length2, field_list);
		res.push_back(t_list);

		gcc_assert(res.size() == 1);

		return res;
	}
}

#if 0
bool IndirectionList::isEqual(IndirectionList ind_list)
{
	int length = Length();

	if(ind_list.get_st_hp() == get_st_hp() && ind_list.getStarCount() == getStarCount() && ind_list.Length() == length)
	{
		for(int i = 0; i < length; i++)
		{
			if(ind_list.field_list[i] != field_list[i])
			{
				return false;
			}
		}

		return true;
	}

	return false;
}
#endif

IndirectionList IndirectionList::insertField(int field) 
{
//	assert(sizeof(field_list) != length + 1);
//	fprintf(stderr, "\nHiyyeee %d\n", length);

	int f[IndirectionList::kSize];

	if(length < fi_thresh)
	{
//		fprintf(stderr, "\nNot exceeded fi_thresh yet\n");
		for(int i = 0; i < length; i++)
		{
			f[i] = field_list[i];
		}
		
		f[length] = field;

//		field_list[length] = field;
//		length++;
		
		IndirectionList l(get_st_hp(), getStarCount(), length+1, f);
		return (l);
	}
	else if(length < k_thresh)
	{
//		fprintf(stderr, "\nexceeded fi_thresh but not k_thresh yet\n");

		for(int i = 0; i < length; i++)
		{
			f[i] = field_list[i];
		}
		
		f[length] = field;

//		field_list[length] = AFIELD;
//		length++;

		IndirectionList l(get_st_hp(), getStarCount(), length+1, f);
		return (l);
	}

	return *this;
}

IndirectionList IndirectionList::removeFirstField()
{
	int length = Length();
	int *field_list, *field_list1; 

	if(length == 0)
	{
		IndirectionList list;
		return list;
	}

	field_list1 = begin();
	int i;

	for(i = 0; i < length; i++)
	{
		field_list[i] = field_list1[i+1];
	}

	if(length == k_thresh)
	{
		field_list[i] = AFIELD;		
	}
	else
	{
		length--;
	}

	IndirectionList list(false, 0, length, field_list);
	return list;
}

IndirectionList IndirectionList::changeFirstField()
{
	int length = Length();
	int *field_list; 

	if(length == 0)
	{
		IndirectionList list;	
		return list;
	}

	field_list = begin();
	field_list[0] = SFIELD;

	IndirectionList list(false, 0, length, field_list);
	return list;
}

std::vector< IndirectionList > IndirectionList::append_list(std::vector< IndirectionList > list)
{
	std::vector< IndirectionList > res;

	for(std::vector< IndirectionList >::iterator it = list.begin(); it != list.end(); it++)
	{
		IndirectionList l;
		l = append(*it);

		if(find(res.begin(), res.end(), l) == res.end())
		{
			res.push_back(l);
		}
	}

	return res;
}

IndirectionList IndirectionList::append(IndirectionList ind_list) // ind_list1.append(ind_list2) => ind_list1 ++ ind_list2
{
	bool st_hp_1 = get_st_hp();
	bool st_hp_2 = ind_list.get_st_hp();
	IndirectionList new_ind_list;

	if(st_hp_1 && st_hp_2) 
	{
		int star_count_1 = getStarCount();
		int star_count_2 = ind_list.getStarCount();
		int *field_list_1;

		star_count_1 += star_count_2;

		IndirectionList l(st_hp_1, star_count_1, 0, field_list_1);
		return l;
	}
	else if(st_hp_1 && !st_hp_2)
	{
		int star_count_1 = getStarCount();
		int *field_list_2 = ind_list.begin();
		IndirectionList new_ind_list;

		for(int i = 0; i < star_count_1; i++)
		{
			new_ind_list = new_ind_list.insertField(SFIELD);
		}

		for(int i = 0; i < ind_list.getLength(); i++)
		{
			new_ind_list = new_ind_list.insertField(field_list_2[i]);
		}

		return new_ind_list;
	}
	else if(!st_hp_2 && !st_hp_2)
	{
		int *field_list = ind_list.begin();
		new_ind_list = *this;

		for (int i = 0; i < ind_list.getLength(); i++)
		{
			new_ind_list = new_ind_list.insertField(field_list[i]);
		}

		return new_ind_list; // IndirectionList::create(0, new_ind_list->getLength(), new_ind_list->begin(), st_hp_2);
	}
	else 
	{
		int star_count_2 = ind_list.getStarCount();
		new_ind_list = *this;
	
		for (int i = 0; i < star_count_2; i++)
		{
			new_ind_list = new_ind_list.insertField(SFIELD);
		}

		return new_ind_list; // IndirectionList::create(0, new_ind_list->getLength(), new_ind_list->begin(), st_hp_1);
	}
}

unsigned int IndirectionList::Length()
{
	if(get_st_hp())
	{
		return getStarCount();
	}
	
	return getLength();
}

bool IndirectionList::doesNotExceed(IndirectionList ind_list) // ind_list1->doesNotExceed(ind_list2) returns true when ind_list1->Length <= ind_list2->Length
{
	return (Length() <=  ind_list.Length());
}

bool IndirectionList::stackIndirectionList()
{
	return get_st_hp();
}

bool IndirectionList::operator==(const IndirectionList &rhs) const
{
	int length = getLength();

	if(rhs.get_st_hp() == get_st_hp() && rhs.getStarCount() == getStarCount() && rhs.getLength() == length)
	{
		for(int i = 0; i < length; i++)
		{
			if(rhs.field_list[i] != field_list[i])
			{
				return false;
			}
		}

		return true;
	}

	return false;
}

void IndirectionList::printIndirectionList()
{
	if(get_st_hp())
	{
//		fprintf(dump_file, "\nScalars Indirection List %d\n", list->getStarCount());
		
		for(int i = 0; i < getStarCount(); i++)
			fprintf(dump_file, "* ");

//		fprintf(dump_file, "\n");	
	}
	else
	{
		int *field_list = begin();

//		fprintf(dump_file, "\nAGGREGATE Indirection List\n");

		for(int i = 0; i < getLength(); i++)
		{
			if(field_list[i] == SFIELD)
			{
				fprintf(dump_file, "* ");
			}
			else if(field_list[i] == AFIELD)
			{
				fprintf(dump_file, "*' ");
			}
			else
			{
				fprintf(dump_file, "%d\t", field_list[i]);
			}
		}

//		fprintf(dump_file, "\n");	
	}
}

void printFieldList(int *field_list, int length)
{
	for(int i = 0; i < length; i++)
		fprintf(dump_file,"%d\t", field_list[i]);

	fprintf(dump_file, "\n\n");
}

bool IndirectionList::checkIndirectionList()
{

	if(get_st_hp())
	{
		int length = getLength();

		if(length != 0)
			return false;
	}
	else
	{
		if(getStarCount() != 0)
			return false;
	}

	return true;
}
