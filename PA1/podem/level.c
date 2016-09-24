/**********************************************************************/
/*           This is the levelling routine for atpg                   */
/*                                                                    */
/*           Author: Tony Hi-Keung Ma                                 */
/*           last update : 1/27/1987                                  */
/**********************************************************************/


#include <stdio.h>
#include "global.h"
#include "miscell.h"


void
level_circuit()
{
    register wptr w,wfirst,wtemp;
    register nptr nfirst,nlast,ncurrent,nprelast;
    register int wire_index,i,j,k;
    register int schedule,level = 0;

    nfirst = NIL(struct NODE);  // first node in the event list, use the pnext pointer to form a linked queue 
    nlast = NIL(struct NODE);   // last node in the event list 
    wfirst = NIL(struct WIRE);  // stack of wires to be labeled for a given level
    sort_wlist = ALLOC(ncktwire,wptr); // wire list array, sorted from PI to PO

    /* levels are propagated from PI to PO (like events) */
    /* build up the initial node event list */
    for (wire_index = 0; wire_index < ncktin; wire_index++) { // loop of PI
        sort_wlist[wire_index] = cktin[wire_index];
        cktin[wire_index]->wlist_index = wire_index;  
        cktin[wire_index]->flag |= MARKED; // MARKED means the PI is already leveled
        cktin[wire_index]->level = level;  // PI level =0 
        for (i = 0; i < cktin[wire_index]->nout; i++) {  // loop every fanout node of a PI
	  if (!(cktin[wire_index]->onode[i]->pnext) && // if this node not yet in event list
	      cktin[wire_index]->onode[i] != nlast) {   
	    cktin[wire_index]->onode[i]->pnext = nfirst;  //add to the front of event list
	    nfirst = cktin[wire_index]->onode[i]; 
	  }
	  if (!nlast) nlast = nfirst;  
        }  // for i
    } // for wire_index
    nprelast = nlast;  // nprelast points to the last node of event list for a given level

    /*  the event list linked queue is like this
	n             nnnnnnnnnnnnnnnnnnnnnnnnnnnnnNNNNNNNNNNNNNNNNNNNNNNNNNNNNN
	^             ^                           ^                            ^
	ncurrent      nfist                       nprelast                     nlast

	ncurrent points to the node under evaluation now
	nfirst points to the front of the queue  (exit)
	nlast points to the end of queue (entrance)
	n = nodes to be evaluated for this level
        N = nodes to be evaluated for the next level
    */

    while(nfirst) {  // go through all nodes in the event list (for this level)
      ncurrent = nfirst;  // get a node from the front of event list
      nfirst = nfirst->pnext;
      ncurrent->pnext = NIL(struct NODE);
      schedule = TRUE;
      for (i = 0; i < ncurrent->nin; i++) {  // check every gate input
	if (!(ncurrent->iwire[i]->flag & MARKED)) { // if any one gate input is not marked yet
	  schedule = FALSE;  // do not schedule this event
	}
      } // for i
      if (schedule) {  
	for (j = 0; j < ncurrent->nout; j++) {
	  sort_wlist[wire_index] = ncurrent->owire[j]; //insert node output wire to sort_wlist
	  ncurrent->owire[j]->wlist_index = wire_index; 
	  wire_index++;
	  ncurrent->owire[j]->pnext = wfirst; // push node output to stack to be leveled
	  wfirst = ncurrent->owire[j];
	  for (k = 0; k < ncurrent->owire[j]->nout; k++) {  // propagate the event to fanout node
	    if (!(ncurrent->owire[j]->onode[k]->pnext) &&  // if not in the event list
		ncurrent->owire[j]->onode[k] != nlast) {  
	      nlast->pnext = ncurrent->owire[j]->onode[k];  // append to end of event list   
	      nlast = ncurrent->owire[j]->onode[k];
	      if (!nfirst) nfirst = nlast;  
	    }
	  }
	}
      } // if schedule
      else {  // if this node is not scheduled
	if (!(ncurrent->pnext) && ncurrent != nlast) {  
	  nlast->pnext = ncurrent; 
	  nlast = ncurrent;
	}
	if (!nfirst) nfirst = nlast;  
      }


      /* when finish all nodes in the event list for a given level,
	 mark level to all wires in the stack*/ 
      if (ncurrent == nprelast) {  
	level++;
	for (w = wfirst; w; w = wtemp) {  // pop every wire in the stack and mark them
	  wtemp = w->pnext;
	  w->pnext = NIL(struct WIRE);
	  w->flag |= MARKED;
	  w->level = level;
	}
	wfirst = NIL(struct WIRE);
	nprelast = nlast;
      }  // if ncurent
    }  // while (nfirst) , starts the next level


    /* after the whole circuit is done, unmark each wire */
    for (i = 0; i < ncktwire; i++) {
        sort_wlist[i]->flag &= ~MARKED;
    }
}/* end of level */

/* for all gates in the circuits,
   put smaller level gate input before the larger level gate input 
   so that we can speed up the evaluation of a gate */
void
rearrange_gate_inputs()
{
    register int i,j,k;
    register wptr wtemp;
    register nptr n;

    for (i = ncktin; i < ncktwire; i++) {  
      if (n = sort_wlist[i]->inode[0]) { // check every gate in the circuit 
	for (j = 0; j < n->nin; j++) {  // check every pait of gate inputs
                for (k = j + 1; k < n->nin; k++) { 
		  if (n->iwire[j]->level > n->iwire[k]->level) {// if order is wrong
		    wtemp = n->iwire[j];  // swap the gate inptuts
		    n->iwire[j] = n->iwire[k];
		    n->iwire[k] = wtemp;
		  }
                }
	}
      }
    }  // for i
}/* end of rearrange_gate_inputs */
