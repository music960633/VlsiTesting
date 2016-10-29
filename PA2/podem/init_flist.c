/**********************************************************************/
/*           routines building the dummy input and output gate list;  */
/*           building the fault list;                                 */
/*           calculating the total fault coverage.                    */
/*                                                                    */
/*           Author: Hi-Keung Tony Ma                                 */
/*           last update : 10/29/1987                                 */
/**********************************************************************/

#include <stdio.h>
#include "global.h"
#include "miscell.h"

int num_of_gate_fault;
extern int debug;

/* the way of fault collapsing is different from what we teach in class
   need modification */
generate_fault_list()
{
    int i,j,k;
    wptr w;
    nptr n;
    fptr f;
    int fault_num;  

    first_fault = NIL(struct FAULT);  // start of fault list 
    num_of_gate_fault = 0; // totle number of faults in the whole circuit

    /* walk through every wire in the circuit*/
    for (i = ncktwire - 1; i >= 0; i--) {
      w = sort_wlist[i]; // each wire w
        n = w->inode[0]; // w is the gate n output wire

	/* for each gate, create a gate output stuck-at zero (SA0) fault */
        if (!(f = ALLOC(1,struct FAULT))) error("No more room!");
        f->node = n;
        f->io = GO;
        f->fault_type = STUCK0;
        f->to_swlist = i;
	/* for AND NOR NOT BUF, their GI fault is equivalent to GO SA0 fault */
        switch (n->type) {   
            case   AND:
            case   NOR:
            case   NOT:
            case   BUF:
                f->eqv_fault_num = 1;
                for (j = 0; j < w->inode[0]->nin; j++) {
                    if (w->inode[0]->iwire[j]->nout > 1) f->eqv_fault_num++;
                }
                break;
            case INPUT:
            case    OR:
            case  NAND: 
            case   EQV:
            case   XOR: f->eqv_fault_num = 1; break;
        }
        num_of_gate_fault += f->eqv_fault_num; // accumulate total fault count
        f->pnext = first_fault;  // insert into the fault list
        f->pnext_undetect = first_fault; // initial undetected fault list contains all faults
        first_fault = f;

	/* for each gate, create a gate output stuck-at one (SA1) fault */
        if (!(f = ALLOC(1,struct FAULT))) error("No more room!");
        f->node = n;
        f->io = GO;
        f->fault_type = STUCK1;
        f->to_swlist = i;
	/* for OR NAND NOT BUF, their GI fault is equivalent to GO SA1 fault */
        switch (n->type) {
            case    OR:
            case  NAND:
            case   NOT:
            case   BUF:
                f->eqv_fault_num = 1;
                for (j = 0; j < w->inode[0]->nin; j++) {
                    if (w->inode[0]->iwire[j]->nout > 1) f->eqv_fault_num++;
                }
                break;
            case INPUT:
            case   AND:
            case   NOR: 
            case   EQV:
            case   XOR: f->eqv_fault_num = 1; break;
        }
        num_of_gate_fault += f->eqv_fault_num;
        f->pnext = first_fault;
        f->pnext_undetect = first_fault;
        first_fault = f;

	/*if w has multiple fanout branches,   */
        if (w->nout > 1) {
            for (j = 0 ; j < w->nout; j++) {
                n = w->onode[j];
		/* create SA0 for OR NOR EQV XOR gate inputs  */
                switch (n->type) {
                    case OUTPUT:
                    case    OR:
                    case   NOR: 
                    case   EQV:
                    case   XOR:
                        if (!(f = ALLOC(1,struct FAULT))) error("No more room!");
                        f->node = n;
                        f->io = GI;
                        f->fault_type = STUCK0;
                        f->to_swlist = i;
                        f->eqv_fault_num = 1;
			/* f->index is the index number of gate input, 
			   which GI fault is associated with*/
                        for (k = 0; k < n->nin; k++) {  
                            if (n->iwire[k] == w) f->index = k;
                        }
                        num_of_gate_fault++;
                        f->pnext = first_fault;
                        f->pnext_undetect = first_fault;
                        first_fault = f;
                        break;
                }

		/* create SA1 for AND NAND EQV XOR gate inputs  */
                switch (n->type) {
                    case OUTPUT:
                    case   AND:
                    case  NAND: 
                    case   EQV:
                    case   XOR:
                        if (!(f = ALLOC(1,struct FAULT))) error("Room more room!");
                        f->node = n;
                        f->io = GI;
                        f->fault_type = STUCK1;
                        f->to_swlist = i;
                        f->eqv_fault_num = 1;
                        for (k = 0; k < n->nin; k++) {
                            if (n->iwire[k] == w) f->index = k;
                        }
                        num_of_gate_fault++;
                        f->pnext = first_fault;
                        f->pnext_undetect = first_fault;
                        first_fault = f;
                        break;
                }
            }
        }
    }

    /*walk through all fautls, assign fault_no one by one  */
    for (f = first_fault, fault_num = 0; f; f = f->pnext, fault_num++) {
        f->fault_no = fault_num;
    }

    fprintf(stdout,"#number of equivalent faults = %d\n", fault_num);
    return;  
}/* end of generate_fault_list */


/* computing the actual fault coverage */
compute_fault_coverage()
{
    register double gate_fault_coverage,eqv_gate_fault_coverage;
    register int no_of_detect,eqv_no_of_detect,eqv_num_of_gate_fault;
    register fptr f;

    debug = 0;
    no_of_detect = 0;
    gate_fault_coverage = 0;
    eqv_no_of_detect = 0;
    eqv_gate_fault_coverage = 0;
    eqv_num_of_gate_fault = 0;
    
    for (f = first_fault; f; f = f->pnext) {

        if (debug) {
            if (!f->detect) {
                switch (f->node->type) {
                   case INPUT:
                        fprintf(stdout,"primary input: %s\n",f->node->owire[0]->name);
                      break;
                    case OUTPUT:
                        fprintf(stdout,"primary output: %s\n",f->node->iwire[0]->name);
                      break;
                    default:
                        fprintf(stdout,"gate: %s ;",f->node->name);
                        if (f->io == GI) {
                            fprintf(stdout,"input wire name: %s\n",f->node->iwire[f->index]->name);
                        }
                        else {
                            fprintf(stdout,"output wire name: %s\n",f->node->owire[0]->name);
                        }
                      break;
                }
                fprintf(stdout,"fault_type = ");
                switch (f->fault_type) {
                   case STUCK0:
                      fprintf(stdout,"s-a-0\n"); break;
                   case STUCK1:
                      fprintf(stdout,"s-a-1\n"); break;
                }
                fprintf(stdout,"no of equivalent fault = %d\n",f->eqv_fault_num);
                fprintf(stdout,"detection flag = %d\n",f->detect);
                fprintf(stdout,"\n");
            }
        }

         if (f->detect == TRUE) {
              no_of_detect += f->eqv_fault_num;
            eqv_no_of_detect++;
          }
          eqv_num_of_gate_fault++;
    }
    if (num_of_gate_fault != 0) 
    gate_fault_coverage = (((double) no_of_detect) / num_of_gate_fault) * 100;
    if (eqv_num_of_gate_fault != 0) 
    eqv_gate_fault_coverage = (((double) eqv_no_of_detect) / eqv_num_of_gate_fault) * 100;
    
    /* print out fault coverage results */
    fprintf(stdout,"\n");
    fprintf(stdout,"#FAULT COVERAGE RESULTS :\n");
    fprintf(stdout,"#number of test vectors = %d\n",in_vector_no);
    fprintf(stdout,"#total number of gate faults = %d\n",num_of_gate_fault);
    fprintf(stdout,"#total number of detected faults = %d\n",no_of_detect);
    fprintf(stdout,"#total gate fault coverage = %5.2f%%\n",gate_fault_coverage);
    fprintf(stdout,"#number of equivalent gate faults = %d\n",eqv_num_of_gate_fault);
    fprintf(stdout,"#number of equivalent detected faults = %d\n",eqv_no_of_detect);
    fprintf(stdout,"#equivalent gate fault coverage = %5.2f%%\n",eqv_gate_fault_coverage);
    fprintf(stdout,"\n");
    return;  
}/* end of compute_fault_coverage */


/* for each PI and PO in the whole circuit,
   create a dummy PI gate to feed each PI wire 
   create a dummy PO gate to feed each PO wire. */
/* why do we need dummy gate? */
create_dummy_gate()
{
    register int i,j;
    register int num_of_dummy;
    register nptr n,*n2;
    char sgate[25];
    char intstring[25];
    nptr getnode();

    num_of_dummy = 0;

    /* create a dummy PI gate for each PI wire */
    for (i = 0; i < ncktin; i++) {
      num_of_dummy++;
	  
      /* the dummy gate name is  "dummay_gate#"  */ 
      sprintf(intstring, "%d", num_of_dummy); 
      sprintf(sgate,"dummy_gate%s",intstring);

      /* n is the dummy PI gate, cktin[i]is the original PI wire.  feed n to cktin[i] */ 
      n = getnode(sgate);
      n->nout = 1;
      n->type = INPUT;
      if (!(n->owire = ALLOC(1,wptr))) error("No more room!");
      n->owire[0] = cktin[i];
      if (!(cktin[i]->inode = ALLOC(1,nptr))) error("No more room!");
      cktin[i]->inode[0] = n;
      cktin[i]->nin = 1;
    } // for i

    /* create a dummy PO gate for each PO wire */
    for (i = 0; i < ncktout; i++) {
      num_of_dummy++;

      //  itoa(num_of_dummy,intstring);
      sprintf(intstring, "%d", num_of_dummy); 
      sprintf(sgate,"dummy_gate%s",intstring);

      /*  n is the dummy PO gate, cktout[i] is the original PO wire.  feed cktout[i] to n */
      n = getnode(sgate);
      n->nin = 1;
      n->type = OUTPUT;
      if (!(n->iwire = ALLOC(1,wptr))) error("No more room!");
      n->iwire[0] = cktout[i];
      cktout[i]->nout++;
      
      /* copy the original onode array, insert the dummy gate n */
      if (!(n2 = ALLOC(cktout[i]->nout,nptr))) error("No more room!");
      n2[(cktout[i]->nout - 1)] = n;  
      for (j = 0; j < (cktout[i]->nout - 1); j++) {   
	n2[j] = cktout[i]->onode[j];
      }

      /* replace the old onode array */
      if (cktout[i]->onode) free(cktout[i]->onode);
      cktout[i]->onode = n2;

    } // for i
    return;
}/* end of create_dummy_gate */


/*
*   The itoa function,  (this is not used anymore)
*/

reverse(s)  /*  reverse string s in place */
char s[];
{
   int c,i,j;

   for(i=0,j = strlen(s) - 1;i<j;i++,j--) {
      c = s[i];
      s[i] = s[j];
      s[j] = c;
   }
}

itoa(n,s)   /*  convert n to characters in s */
int n;
char s[];
{
   int i,sign;

   if ((sign = n) < 0) { /* record sign */
       n = -n;
   }
   i = 0;
   do {   /*  generate digits in reverse order */
        s[i++] = n % 10 + '0' ;  /* get next digit */
   } while ((n/=10) > 0); /* delete it */
   if (sign < 0) {
       s[i++] = '-';
   }
   s[i] = '\0';
   reverse(s);

}  /*   end of itoa  */


