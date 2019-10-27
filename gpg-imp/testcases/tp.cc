#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <iostream>
#include <set>

using namespace std;

void createArtificialGPG()
//GPG createArtificialGPG()
{
        FILE *gpb_list, gpb_rel, gpb_contents;
        char i, r, g;
        unsigned int gpb_i, gpb_r1, gpb_r2;
        unsigned int gpu_s, gpu_d, gpu_ind;

        gpb_list = fopen("gpb-list.txt","r");
        gpb_rel = fopen("gpb-rel.txt","r");
        gpb_contents = fopen("gpb-contents.txt","r");

        unsigned count1 = 0;

        //GPG gpg;

        while((i=fgetc(gpb_list))!=EOF)
        {
                printf("%c",i);
                
                gpb_i = atoi(i);

                count1 = 0;

                set< unsigned int > preds, succs;
                //GPBSet preds, succs;
		//GPUSet res;

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

				// Read Indirection List for source and destination - Check IndirectionList.h

				//IndirectionList i_s(gpu_info[...], gpu_info[,...],...);
				//IndirectionList i_d(gpu_info[...], gpu_info[,...],...);

				//Node l_s(gpu_s, i_s);
				//Node r_d(gpu_d, i_d);

				// GPU gpu(l_s.getNodeID(), r_d.getNodeID());
				// res.insert(gpu.getGPUID());
                        }
                }

		//gpg.addGPB(gpb_id, preds, succs, NULL);
        }

        fclose(gpb_list);
        fclose(gpb_rel);
        fclose(gpb_contents);

	//return gpg;
}

int main()
{
	createArtificialGPG();
}
