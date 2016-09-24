/**********************************************************************/
/*           This is the podem test pattern generator for atpg        */
/*                                                                    */
/*           Author: Hi-Keung Tony Ma                                 */
/*           last update : 07/11/1988                                 */
/**********************************************************************/

#include <stdio.h>
#include "global.h"
#include "miscell.h"

#define U  2
#define D  3
#define B  4 // D_bar
#define CONFLICT 2

extern int backtrack_limit; // maximum number of backtracked allowed, defatult is 50
extern int total_attempt_num;  // number of patterns per fault, default is 1
int no_of_backtracks;  // current number of backtracks
int find_test;  // TRUE when a test pattern is found
int no_test; // TRUE when it is proven that no test exists for this fault 
int unique_imply;

/* generates a single pattern for a single fault */
podem(fault, current_backtracks)
fptr fault;
int *current_backtracks;
{
    register int i,j;
    register nptr n;

    register wptr wpi; // points to the PI currently being assigned
    register wptr decision_tree; // the top of  LIFO stack of design_tree
    register wptr wtemp,wfault;    
    wptr test_possible();
    wptr fault_evaluate();
    long rand();
    int set_uniquely_implied_value();
    int attempt_num = 0;  // counts the number of pattern generated so far for the given fault
    void display_fault();

    /* initialize all circuit wires to unknown */
    for (i = 0; i < ncktwire; i++) {
        sort_wlist[i]->value = U;
    }
    no_of_backtracks = 0;
    find_test = FALSE;
    no_test = FALSE;
    decision_tree = NIL(struct WIRE);
    wfault = NIL(struct WIRE);
    
    mark_propagate_tree(fault->node);

    /* Fig 7 starts here */
    /* set the initial goal, assign the first PI.  Fig 7.P1 */
    switch (set_uniquely_implied_value(fault)) {
        case TRUE: // if a  PI is assigned 
	  sim();  // Fig 7.3
	  if (wfault = fault_evaluate(fault)) forward_imply(wfault);// propagate fault effect
	  if (check_test()) find_test = TRUE; // if fault effect reaches PO, done. Fig 7.10
	  break;
        case CONFLICT:
	  no_test = TRUE; // cannot achieve initial objective, no test
	  break;
        case FALSE: 
	  break;  //if no PI is reached, keep on backtracing. Fig 7.A 
    }

    /* loop in Fig 7.ABC 
     * quit the loop when either one of the three conditions is met: 
     * 1. number of backtracks is equal to or larger than limit
     * 2. no_test
     * 3. already find a test pattern AND no_of_patterns meets required total_attempt_num */
    while ((no_of_backtracks < backtrack_limit) && !no_test &&
        !(find_test && (attempt_num == total_attempt_num))) {
      
        /* check if test possible.   Fig. 7.1 */
        if (wpi = test_possible(fault)) {
            wpi->flag |= CHANGED;
	    /* insert a new PI into decision_tree */ 
            wpi->pnext = decision_tree;
            decision_tree = wpi;
        }
        else { // no test possible using this assignment, backtrack. 

            while (decision_tree && !wpi) {
	      /* if both 01 already tried, backtrack. Fig.7.7 */
	      if (decision_tree->flag & ALL_ASSIGNED) {
		decision_tree->flag &= ~ALL_ASSIGNED;  // clear the ALL_ASSIGNED flag
		decision_tree->value = U; // do not assign 0 or 1
		decision_tree->flag |= CHANGED; // this PI has been changed
		/* remove this PI in decision tree.  see dashed nodes in Fig 6 */
		wtemp = decision_tree;
		decision_tree = decision_tree->pnext;
		wtemp->pnext = NIL(struct WIRE);
	      }  
	      /* else, flip last decision, flag ALL_ASSIGNED. Fig. 7.8 */
                else {
		  decision_tree->value = decision_tree->value ^ 1; // flip last decision
		  decision_tree->flag |= CHANGED; // this PI has been changed
		  decision_tree->flag |= ALL_ASSIGNED;
		  no_of_backtracks++;
		  wpi = decision_tree; 
                }
            } // while decision tree && ! wpi
            if (!wpi) no_test = TRUE; //decision tree empty,  Fig 7.9
        } // no test possible

/* this again loop is to generate multiple patterns for a single fault 
 * this part is NOT in the original PODEM paper  */
again:  if (wpi) {
            sim();
            if (wfault = fault_evaluate(fault)) forward_imply(wfault);
            if (check_test()) {
                find_test = TRUE;
		/* if multiple patterns per fault, print out every test cube */
                if (total_attempt_num > 1) {
                    if (attempt_num == 0) {
                        display_fault(fault);
                    }
                    display_io(); 
                }
                attempt_num++; // increase pattern count for this fault

		/* keep trying more PI assignments if we want multiple patterns per fault
		 * this is not in the original PODEM paper*/
                if (total_attempt_num > attempt_num) {
                    wpi = NIL(struct WIRE);
                    while (decision_tree && !wpi) {
		      /* backtrack */
                        if (decision_tree->flag & ALL_ASSIGNED) {
                            decision_tree->flag &= ~ALL_ASSIGNED;
                            decision_tree->value = U;
                            decision_tree->flag |= CHANGED;
                            wtemp = decision_tree;
                            decision_tree = decision_tree->pnext;
                            wtemp->pnext = NIL(struct WIRE);
                        }
			/* flip last decision */
                        else {
                            decision_tree->value = decision_tree->value ^ 1;
                            decision_tree->flag |= CHANGED;
                            decision_tree->flag |= ALL_ASSIGNED;
                            no_of_backtracks++;
                            wpi = decision_tree;
                        }
                    }
                    if (!wpi) no_test = TRUE;
                    goto again;  // if we want multiple patterns per fault
                } // if total_attempt_num > attempt_num
            }  // if check_test()
        } // again
    } // while (three conditions)

    /* clear everthing */
    for (wpi = decision_tree; wpi; wpi = wtemp) {
         wtemp = wpi->pnext;
         wpi->pnext = NIL(struct WIRE);
         wpi->flag &= ~ALL_ASSIGNED;
    }
    *current_backtracks = no_of_backtracks;
    unmark_propagate_tree(fault->node);
    if (find_test) {
      /* normally, we want one pattern per fault */
        if (total_attempt_num == 1) {
	  
	  for (i = 0; i < ncktin; i++) {
	    switch (cktin[i]->value) {
	    case 0:
	    case 1: break;
	    case D: cktin[i]->value = 1; break;
	    case B: cktin[i]->value = 0; break;
	    case U: cktin[i]->value = rand()&01; break; // random fill U
	    }
	  }
	  display_io();
        }
        else fprintf(stdout, "\n");  // do not random fill when multiple patterns per fault
        return(TRUE);
    }
    else if (no_test) {
        /*fprintf(stdout,"redundant fault...\n");*/
        return(FALSE);
    }
    else {
        /*fprintf(stdout,"test aborted due to backtrack limit...\n");*/
        return(MAYBE);
    }
}/* end of podem */


/* drive D or B to the faulty gate (aka. GUT) output
 * insert D or B into the circuit.
 * returns w (the faulty gate output) if GUT output is set to D or B successfully.
 * returns NULL if if faulty gate output still remains unknown  */
wptr
fault_evaluate(fault)
fptr fault;
{
    register int i;
    register int temp1;
    register wptr w;

    if (fault->io) { // if fault is on GUT gate output
      w = fault->node->owire[0]; // w is GUT output wire
        if (w->value == U) return(NULL);
        if (fault->fault_type == 0 && w->value == 1) w->value = D; // D means 1/0
        if (fault->fault_type == 1 && w->value == 0) w->value = B; // B_bar 0/1
        return(w);
    }
    else { // if fault is GUT gate input
        w = fault->node->iwire[fault->index]; 
        if (w->value == U) return(NULL);
        else {
            temp1 = w->value;
            if (fault->fault_type == 0 && w->value == 1) w->value = D;
            if (fault->fault_type == 1 && w->value == 0) w->value = B;
            if (fault->node->type == OUTPUT) return(NULL);
            evaluate(fault->node);  // five-valued, evaluate one gate only, sim.c
            w->value = temp1;
	    /* if GUT gate output changed */
            if (fault->node->owire[0]->flag & CHANGED) {
	      fault->node->owire[0]->flag &= ~CHANGED; // stop GUT output change propagation 
	      return (fault->node->owire[0]); // returns the output wire of GUT
            }
            else return(NULL); // faulty gate output does not change
        }
    }
}/* end of fault_evaluate */


/* iteratively foward implication
 * in a depth first search manner*/ 
forward_imply(w)
wptr w;
{
    register int i;

    for (i = 0; i < w->nout; i++) {
        if (w->onode[i]->type != OUTPUT) {
            evaluate(w->onode[i]);
            if (w->onode[i]->owire[0]->flag & CHANGED)
	      forward_imply(w->onode[i]->owire[0]); // go one level further
            w->onode[i]->owire[0]->flag &= ~CHANGED;
        }
    }
    return;
}/* end of forward_imply */


/* Fig 8 
 * this function determines objective_wire and objective_level. 
 * it returns the newly assigned PI if test is possible. 
 * it returns NULL if no test is possible. */
wptr
test_possible(fault)
fptr fault;
{
    register nptr n;
    register wptr object_wire;
    register int object_level;
    nptr find_propagate_gate();
    wptr find_pi_assignment();
    int trace_unknown_path();

    /* if the fault is not on primary output */
    if (fault->node->type != OUTPUT) {

      /* if the faulty gate (aka. gate under test, G.U.T.) output is not U,  Fig. 8.1 */ 
      if (fault->node->owire[0]->value ^ U) {

	  /* if GUT output is not D or D_bar, no test possible */
	  if (!((fault->node->owire[0]->value == B) ||
                (fault->node->owire[0]->value == D))) return(NULL);

	  /* find the next gate n to propagate, Fig 8.5*/
	  if (!(n = find_propagate_gate(fault->node->owire[0]->level)))
	    return(NULL);

	  /*determine objective level according to the type of n.   Fig 8.8*/ 
            switch(n->type) {
                case  AND:
                case  NOR: object_level = 1; break;

                case NAND:
                case   OR: object_level = 0; break;
                default:
                  /*---- comment out due to error for C2670.sim ---------
                  fprintf(stderr,
                          "Internal Error(1st bp. in test_possible)!\n");
                  exit(-1);
                  -------------------------------------------------------*/
                  return(NULL);
            }
	    /* object_wire is the gate n output. */
            object_wire = n->owire[0];
      }  // if faulty gate output is not U.   (fault->node->owire[0]->value ^ U) 

      else { // if faulty gate output is U

	    /* if X path disappear, no test possible  */
            if (!(trace_unknown_path(fault->node->owire[0])))
                return(NULL);

	    /* if fault is on GUT otuput,  Fig 8.2*/
            if (fault->io) {
	        /* objective_level is opposite to stuck fault  Fig 8.3 */ 
                if (fault->fault_type) object_level = 0;
                else object_level = 1;
		/* objective_wire is on faulty gate output */
                object_wire = fault->node->owire[0];
            }

	    /* if fault is on GUT input, Fig 8.2*/ 
            else {
	      /* if faulted input is not U  Fig 8.4 */
                if (fault->node->iwire[fault->index]->value  ^ U) {
		  /* determine objective value according to GUT type. Fig 8.9*/
                    switch (fault->node->type) {
                        case  AND:
                        case  NOR: object_level = 1; break;
                        case NAND:
                        case   OR: object_level = 0; break;
                        default:
                     /*---- comment out due to error for C2670.sim ---------
                            fprintf(stderr,
                               "Internal Error(2nd bp. in test_possible)!\n");
                            exit(-1);
                     -------------------------------------------------------*/
                            return(NULL);
                    }
		    /*objective wire is GUT output. */
                    object_wire = fault->node->owire[0];
                }  // if faulted input is not U

                else { // if faulted input is U
		    /*objective level is opposite to stuck fault.    Fig 8.10*/
                    if (fault->fault_type) object_level = 0;
                    else object_level = 1;
		    /* objective wire is faulty wire itself */
                    object_wire = fault->node->iwire[fault->index];
                }
            }
        }
    } // if fault not on PO

    else { // else if fault on PO
        /* if faulty PO is still unknown */
        if (fault->node->iwire[0]->value == U) {
	    /*objective level is opposite to the stuck fault */ 
            if (fault->fault_type) object_level = 0;
            else object_level = 1;
	    /* objective wire is the faulty wire itself */
            object_wire = fault->node->iwire[0];
        }

        else {
          /*--- comment out due to error for C2670.sim ---
            fprintf(stderr,"Internal Error(1st bp. in test_possible)!\n");
            exit(-1);
	  */
            return(NULL);
        }
    }// else if fault on PO

    /* find a pi to achieve the objective_level on objective_wire.
     * returns NULL if no PI is found.  */ 
    return(find_pi_assignment(object_wire,object_level));
   

}/* end of test_possible */


/* backtrace to PI, assign a PI to achieve the objective.  Fig 9
 * returns the wire pointer to PI if succeed.
 * returns NULL if no such PI found.                             */
wptr
find_pi_assignment(object_wire,object_level)
wptr object_wire;
int object_level;
{
    register wptr new_object_wire;
    register int new_object_level;
    wptr find_hardest_control(),find_easiest_control();

    /* if PI, assign the same value as objective Fig 9.1, 9.2 */
    if (object_wire->flag & INPUT) {
    object_wire->value = object_level;
    return(object_wire);
    }

    /* if not PI, backtrace to PI  Fig 9.3, 9.4, 9.5*/
    else {
        switch(object_wire->inode[0]->type) {
        case   OR:
        case NAND:
	  if (object_level) new_object_wire = find_easiest_control(object_wire->inode[0]);  // decision gate
	  else new_object_wire = find_hardest_control(object_wire->inode[0]); // imply gate
                break;
        case  NOR:
        case  AND:
        if (object_level) new_object_wire = find_hardest_control(object_wire->inode[0]);
        else new_object_wire = find_easiest_control(object_wire->inode[0]);
                break;
        case  NOT:
        case  BUF:
        new_object_wire = object_wire->inode[0]->iwire[0];
        break;
        }

    switch (object_wire->inode[0]->type) {
        case  BUF:
        case  AND:
        case   OR: new_object_level = object_level; break;
	  /* flip objective value  Fig 9.6 */
        case  NOT:
        case  NOR:
        case NAND: new_object_level = object_level ^ 1; break;
        }
        if (new_object_wire) return(find_pi_assignment(new_object_wire,new_object_level));
        else return(NULL);
    }
}/* end of find_pi_assignment */


/* Fig 9.4 */
wptr
find_hardest_control(n)
nptr n;
{
    register int i;
    /* because gate inputs are arranged in a increasing level order,
     * larger input index means harder to control */
    for (i = n->nin - 1; i >= 0; i--) {
        if (n->iwire[i]->value  == U) return(n->iwire[i]);
    }
    return(NULL);
}/* end of find_hardest_control */


/* Fig 9.5 */
wptr
find_easiest_control(n)
nptr n;
{
    register int i;

    for (i = 0; i < n->nin; i++) {
        if (n->iwire[i]->value  == U) return(n->iwire[i]);
    }
    return(NULL);
}/* end of find_easiest_control */


/* Find the eastiest propagation gate.   Fig 8.5, Fig 8.6 
 * returns the next gate with D or B on inputs, U on output, nearest to PO
 * returns NULL if no such gate found. */
nptr
find_propagate_gate(level)
int level;
{
    register int i,j;
    register wptr w;
    int trace_unknown_path();

    /* check every wire in decreasing level order
     * so that wires nearer to PO is checked earlier. */
    for (i = ncktwire - 1; i >= 0; i--) {
        /* if reach the same level as the fault, then no propagation path exists */
        if (sort_wlist[i]->level == level) return(NULL);
	/* gate outptu is U */
	/* a marked gate means it is on the path to PO */
        if ((sort_wlist[i]->value == U) &&
            (sort_wlist[i]->inode[0]->flag & MARKED)) { 
	    /*  cehck all gate intputs */  
            for (j = 0; j < sort_wlist[i]->inode[0]->nin; j++) {
                w = sort_wlist[i]->inode[0]->iwire[j];
		/* if there is ont gate intput is D or B */
                if ((w->value == D) || (w->value == B)) {
		  if (trace_unknown_path(sort_wlist[i])) // check X path  Fig 8.6
		      return(sort_wlist[i]->inode[0]); // succeed.  returns this gate
                   break;
                }
            }
        }
    }
}/* end of find_propagate_gate */


/* DFS search for X-path , Fig 8.6
 * returns TRUE if X pth exists
 * returns NULL if no X path exists*/
trace_unknown_path(w)
wptr w;
{
    register int i;
    register wptr wtemp;
	//TODO search X-path
	//HINT if w is PO, return TRUE, if not, check all its fanout 
	//------------------------------------- hole ---------------------------------------
    
	
	
	//----------------------------------------------------------------------------------
    return(FALSE); // X-path disappear
}/* end of trace_unknown_path */


/* Check if any D or D_bar reaches PO. Fig 7.4 */
check_test()
{
	
	register int i,is_test;

    is_test = FALSE;
	//TODO check if any fault effect reach PO
	//HINT check every PO for their value
	//--------------------------------- hole -------------------------------------------
    
	
	
	
	//----------------------------------------------------------------------------------
    return(is_test);
}/* end of check_test */

/* exhaustive search of all nodes on the path from n to PO */
mark_propagate_tree(n)
nptr n;
{
    register int i,j;

    if (n->flag & MARKED) return;
    n->flag |= MARKED; // MARKED means this node is on the path to PO 
    /* depth first search */
    for (i = 0; i < n->nout; i++) {
        for (j = 0; j < n->owire[i]->nout; j++) {
            mark_propagate_tree(n->owire[i]->onode[j]);
        }
    }
    return;
}/* end of mark_propagate_tree */

/* clear all the MARKS */ 
unmark_propagate_tree(n)
nptr n;
{
    register int i,j;

    if (n->flag & MARKED) {
        n->flag &= ~MARKED;
        for (i = 0; i < n->nout; i++) {
            for (j = 0; j < n->owire[i]->nout; j++) {
                unmark_propagate_tree(n->owire[i]->onode[j]);
            }
        }
    }
    return;
}/* end of unmark_propagate_tree */

/* set the initial objective.  
 * returns TRUE if we can backtrace to a PI to assign
 * returns CONFLICT if it is impossible to achieve or set the initial objective*/
set_uniquely_implied_value(fault)
fptr fault;
{
    register wptr w;
    register int pi_is_reach = FALSE;
    register int i;

    if (fault->io) w = fault->node->owire[0];  //  gate output fault, Fig.8.3
    else { // gate input fault.  Fig. 8.4 
        w = fault->node->iwire[fault->index]; 

        switch (fault->node->type) {
            case NOT:
            case BUF:
	      return(NULL);

	      /* assign all side inputs to non-controlling values */
            case AND:
            case NAND:
                 for (i = 0; i < fault->node->nin; i++) {
                     if (fault->node->iwire[i] != w) {
                         switch (backward_imply(fault->node->iwire[i],1)) {
                             case TRUE: pi_is_reach = TRUE; break;
                             case CONFLICT: return(CONFLICT); break;
                             case FALSE: break;
                         }
                     }
                 }
                 break;

            case OR:
            case NOR:
                 for (i = 0; i < fault->node->nin; i++) {
                     if (fault->node->iwire[i] != w) {
                         switch (backward_imply(fault->node->iwire[i],0)) {
                             case TRUE: pi_is_reach = TRUE; break;
                             case CONFLICT: return(CONFLICT); break;
                             case FALSE: break;
                         }
                     }
                 }
                 break;
        }
    } // else , gate input fault 
     
    /* fault excitation */
	//TODO fault excitation
	//HINT use backward_imply function to check if fault can excite or not
	//------------------------------------ hole ----------------------------------------
    
	
	
	
	//----------------------------------------------------------------------------------

    return(pi_is_reach);
}/* end of set_uniquely_implied_value */

/*do a backward implication of the objective: set current_wire to logic_level 
 *implication means a natural consequence of the desired objective. 
 *returns TRUE if the backward implication reaches at least one PI 
 *returns FALSE if the backward implication reaches no PI */
backward_imply(current_wire,logic_level)
wptr current_wire;
int logic_level;
{
    register int pi_is_reach = FALSE;
    register int i;

    if (current_wire->flag & INPUT) { // if PI
        if (current_wire->value != U &&  
            current_wire->value != logic_level) { 
            return(CONFLICT); // conlict with previous assignment
        }
        current_wire->value = logic_level; // assign PI to the objective value
        current_wire->flag |= CHANGED; 
	// CHANGED means the logic value on this wire has recently been changed
        return(TRUE);
    }
    else { // if not PI
        switch (current_wire->inode[0]->type) {
	  /* assign NOT input opposite to its objective ouput */
          /* go backward iteratively.  depth first search */
            case NOT:
                switch (backward_imply(current_wire->inode[0]->iwire[0],
                    (logic_level ^ 1))) {
                    case TRUE: pi_is_reach = TRUE; break;
                    case CONFLICT: return(CONFLICT); break;
                    case FALSE: break;
                }
                break;

		/* if objective is NAND output=zero, then NAND inputs are all ones  
		 * keep doing this back implication iteratively  */
            case NAND:
                if (!logic_level) {
                    for (i = 0; i < current_wire->inode[0]->nin; i++) {
                        switch (backward_imply(current_wire->inode[0]->iwire[i],1)) {
                            case TRUE: pi_is_reach = TRUE; break;
                            case CONFLICT: return(CONFLICT); break;
                            case FALSE: break;
                        }
                    }
                }
                break;

            case AND:
                if (logic_level) {
                    for (i = 0; i < current_wire->inode[0]->nin; i++) {
                        switch (backward_imply(current_wire->inode[0]->iwire[i],1)) {
                            case TRUE: pi_is_reach = TRUE; break;
                            case CONFLICT: return(CONFLICT); break;
                            case FALSE: break;
                        }
                    }
                }
                break;

            case OR:
                if (!logic_level) {
                    for (i = 0; i < current_wire->inode[0]->nin; i++) {
                        switch (backward_imply(current_wire->inode[0]->iwire[i],0)) {
                            case TRUE: pi_is_reach = TRUE; break;
                            case CONFLICT: return(CONFLICT); break;
                            case FALSE: break;
                        }
                    }
                }
                break;

            case NOR:
                if (logic_level) {
                    for (i = 0; i < current_wire->inode[0]->nin; i++) {
                        switch (backward_imply(current_wire->inode[0]->iwire[i],0)) {
                            case TRUE: pi_is_reach = TRUE; break;
                            case CONFLICT: return(CONFLICT); break;
                            case FALSE: break;
                        }
                    }
                }
                break;

            case BUF:
                switch (backward_imply(current_wire->inode[0]->iwire[0],logic_level)) {
                    case TRUE: pi_is_reach = TRUE; break;
                    case CONFLICT: return(CONFLICT); break;
                    case FALSE: break;
               }
                break;
        }
	
        return(pi_is_reach);  
    }
}/* end of backward_imply */
