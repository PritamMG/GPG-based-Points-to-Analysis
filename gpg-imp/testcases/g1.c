#include<stdio.h>
#include<stdlib.h>

int *x, *y, *z, **p, a, b, c;

int non_deterministic_branch()
{
	return (rand() > .5);
}

//static __attribute__ ((noinline))  void foo()
void foo()
{
	int r;
	x = &a;  				/* gpu p1 */
	if (rand() > .5)
	//if (non_deterministic_branch())			
		y = &b; 			/* gpu p2 */
	*p = y;   				/* gpu p3 */
	z = &c;					/* gpu p4 */
}

int main()
{
	int r;
	y = &a;				/* gpu p5 */
	p = &y;				/* gpu p6 */
	if (r)
	//if (non_deterministic_branch())			
		foo();
}

/**************************************************************************************** 
	 
- Problem in compiling. 

	- Strange behaviour of the implementation on my Mac book air (Ubuntu 14.04),
          office desktop PC (Ubuntu 16.04.5 LTS), and my ASUS laptop (Ubuntu 16.04 LTS).

        - On my Mac book air, the impementation gives a segementation fault with the
          with the following message
	  	
		lto1: internal compiler error: Segmentation fault

          when any of the following things happen:

          a. the header of function foo contains the noinline attribute,
          b. `make run' compilation command includes the `-fno-inline' switch after `-O3'
          c. function foo is made recursive by inserting a call in the condition.

	  In each of the above cases, the errors disappear if the statement `l_temp.insert(lnode);' 
          in function collectUpwardExposedVersions in file GPG.cc (search for CHECK) is 
          commented out.


          This program above compiles as it is on office desktop and foo is not inlined. 
          On the Mac book air, the program doesn't compile unless the header changed to 
          plain "void foo()" (in which case foo is inlined).

        - On my office desktop, the behaviour for each of the cases is as follows:
        
          a. Error. It disappears when the line (with CHECK) is commented out in GPG.cc 
                    OR with -fno-inline command line switch with noinline in the header.
          b. No error. The program compiles and foo is not inlined.
          c. Error.

          Again, the error disappears when the line (with CHECK) is commented out in GPG.cc 

       - On my ASUS laptop (Ubuntu 16.04), the behaviour for each of the cases is as follows:
  
          a. No error. The program compiles and foo is not inlined.
          b. No error. The program compiles and foo is not inlined. However, if the command
             line says -fno-inline AND the function header also contains noiinline attribute,
             we still get an error.
	  c. No error. The program compiles and foo is not inlined.
           
       Is the non-deterministic behaviour because of the default compare function being
       different for the the STL library implementations on the two machines?

CHECK the remaining things

- Result of coalescing:

        - On my Mac book air, since inline cannot be stopped, there isn't much that can be tested for coalescing
          because all dependences are resolved for main.

	- On my office desktop

        a. With both -fno-inline on command line and noinline in foo header, the program compiles
           without commenting the CHECK line. Function foo is not inlined. The coalescing is
           exercised ((output is produced during coalescingDFA execution). The GPG for foo as:

	   GPB 1 = { x=&a }
           GPB 6 = { y=&b, *p'=y', *p'=&b, z=&c }
           GPB 5 = empty

           Control flow
                              1
                              |
                              6
                              |
                              5

            Coalescing of z=&c and y=b with *p'= ... is suprising because p could point to 
            y or z. Otherwise, the result looks fine.
                           
        b. Case b. No inline attribute by -fno-inline switch in the command. Program works
           fine. Function foo is not inlined, coalescing takes place and the result is same
           as in case a above.

           The input to coalescing contains five GPBs 

           GBP 1 = GPB 2 = GPB 5 = empty
           GPB 6 = { x=&a }
           GPB 7 = { y=&b, *p=y, *p=b, z=&c } // No upwards exposed variable.

           Control flow

                                   1
                                   |
                                   2
                                  / \
                                 6   \
                                 |   | 
                                 7   /
                                  \ /
                                   5

           I wonder how z=&c got into GPB 7.

	c. Recursive call. Program works by commenting out line (CHECK). Function foo does
           not undergo coalescing (no output during coalescingDFA execution). The last GPG
           for foo contained in the default dump file result.233i.gpg is as follows:

           GPB 1 = GPB2 = GPB 8 = GBB 5 = empty
           GPB 6 = { x=&1, z=&c }
           GPB 7 = { y=&b, *p=y, *p=b } // No upwards exposed variable.
           
           Control flow

                                   1
                                   |
                                   2
                                  / \
                                 6   \
                                / \   \
                               7   |  |
                                \ /   /
                                 8   /
                                  \ /
                                   5
     
            GPUs p1 and p4 that have a *p between them, seem to belong to the same GPB
            which is strange. Note however, that one line of the code is commented out
            so we cannot trust the result.
            This is the input to the coalescingDFA.
           
****************************************************************************************/
