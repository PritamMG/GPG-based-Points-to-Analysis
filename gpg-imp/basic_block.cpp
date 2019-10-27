#include "basic_block.hpp"
#include "cgraph_node.hpp"

set< unsigned int > block_information::get_para_block()
{
	return para_block;
}

void block_information::set_para_block(set< unsigned int > x)
{
	para_block = x;
}

set< unsigned int > block_information::get_exit_block()
{
	return exit_block;
}

void block_information::set_exit_block(set< unsigned int > x)
{
	exit_block = x;
}

block_information::block_information(struct cgraph_node * f)
{
	node=f;
	call_block = false;
	return_block = false;
	start_block = false;
	end_block = false;
	pinitialized = 1;
	dinitialized = 1;
	order = 1;
}	

constraint_list & block_information::get_list()
{
	return cons;
}

struct cgraph_node * block_information::get_cfun()
{
	return node;
}

unsigned int block_information::get_order()
{
	return order;
}

void block_information::set_order(unsigned int o)
{
	order = o;
}

void block_information::incre_order()
{
	unsigned int temp = get_order();
	
	++temp;

	set_order(temp);
}

bool block_information::is_visited()
{
	return visited;
}

void block_information::set_visited()
{
	visited = true;
}

void block_information::reset_visited()
{
	visited = false;
}

//////////////////////////////////////////////////


