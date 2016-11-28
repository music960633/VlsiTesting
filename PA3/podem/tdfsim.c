/**********************************************************************/
/*           Parallel-Fault Event-Driven Fault Simulator              */
/*                                                                    */
/*           Author: CCM                                              */
/*           last update : 22/10/2016                                 */
/**********************************************************************/

#include <stdio.h>
#include "global.h"
#include "miscell.h"

//DO YOUR PA#3 CODE HERE

/* pack 16 faults into one packet.  simulate 16 faults togeter. 
 * the following variable name is somewhat misleading */
#define num_of_pattern 16

static unsigned int Mask[16] = {
  0x00000003, 0x0000000c, 0x00000030, 0x000000c0,
  0x00000300, 0x00000c00, 0x00003000, 0x0000c000,
  0x00030000, 0x000c0000, 0x00300000, 0x00c00000,
  0x03000000, 0x0c000000, 0x30000000, 0xc0000000
};

static unsigned int Unknown[16] = {
  0x00000001, 0x00000004, 0x00000010, 0x00000040,
  0x00000100, 0x00000400, 0x00001000, 0x00004000,
  0x00010000, 0x00040000, 0x00100000, 0x00400000,
  0x01000000, 0x04000000, 0x10000000, 0x40000000
};

int num_of_tdf_fault;
wptr first_faulty_wire;  // points to the start of the linked list 
extern int debug;

transition_delay_fault_simulation(vectors, num_vectors, total_detect_num)
  char *vectors[];
  int num_vectors;
  int *total_detect_num;
{
  int i , j, current_detect_num;
  fptr transition_sim_a_vector();
  fptr f, flist;

  /* for every vector */
  generate_tdf_fault_list();
  flist = first_fault;
  /*
  for (f = flist; f; f = f->pnext_undetect) {
    printf("%s %d %d\n", f->node->name, f->io, f->eqv_fault_num);
  }
  */
  printf("num of TDF fault: %d\n", num_of_tdf_fault);
  for (i = num_vectors - 1; i >= 0; i--) {
    flist = transition_sim_a_vector(vectors[i], flist, &current_detect_num);
    *total_detect_num += current_detect_num;
    fprintf(stderr,"vector[%d] detects %d faults (%d)\n", i,
            current_detect_num,*total_detect_num);
  }
  /* return flist; */
}

fptr
transition_sim_a_vector(vector, flist, num_of_current_detect)
  char* vector;
  fptr flist;
  int* num_of_current_detect;
{
  int i, nv;
  fptr f;
  fptr transition_sim_v2();
 
  /* check V1 */
  for (i = 0; i < ncktin; i++) {
    nv = ctoi(vector[i]);
    sort_wlist[i]->value = nv;
  }
  for (i = 0; i < ncktwire; i++) {
    if (i < ncktin) {
      sort_wlist[i]->flag |= CHANGED;
    }
    else {
      sort_wlist[i]->value = 2;
    }
  }
  sim();
  for (f = flist; f; f = f->pnext_undetect) {
    if (f->fault_type == sort_wlist[f->to_swlist]->value)
      f->activate = TRUE;
    else
      f->activate = FALSE;
  }
  /* check V2 */
  for (i = 0; i < ncktin; i++) {
    if (i == 0)
      nv = ctoi(vector[ncktin]);
    else
      nv = ctoi(vector[i - 1]);
    sort_wlist[i]->value = nv;
  }
  for (i = 0; i < ncktwire; i++) {
    if (i < ncktin) {
      sort_wlist[i]->flag |= CHANGED;
    }
    else {
      sort_wlist[i]->value = 2;
    }
  }
  flist = transition_sim_v2(flist, num_of_current_detect); 
  return flist;
}

generate_tdf_fault_list()
{
  int i,j,k;
  wptr w;
  nptr n;
  fptr f;
  int fault_num;  

  first_fault = NIL(struct FAULT);  // start of fault list 
  num_of_tdf_fault = 0; // totle number of faults in the whole circuit

  /* walk through every wire in the circuit*/
  for (i = ncktwire - 1; i >= 0; i--) {
    w = sort_wlist[i]; // each wire w
    n = w->inode[0]; // w is the gate n output wire

    /* for each gate, create a gate output slow-to-rise (STR) fault */
    if (!(f = ALLOC(1,struct FAULT))) error("No more room!");
    f->node = n;
    f->io = GO;
    f->fault_type = STR;
    f->to_swlist = i;
    switch (n->type) {   
      case   NOT:
      case   BUF:
        f->eqv_fault_num = 1;
        for (j = 0; j < w->inode[0]->nin; j++) {
          if (w->inode[0]->iwire[j]->nout > 1) f->eqv_fault_num++;
        }
        break;
      case   AND:
      case   NOR:
      case INPUT:
      case    OR:
      case  NAND: 
      case   EQV:
      case   XOR: f->eqv_fault_num = 1; break;
    }
    num_of_tdf_fault += f->eqv_fault_num; // accumulate total fault count
    f->pnext = first_fault;  // insert into the fault list
    f->pnext_undetect = first_fault; // initial undetected fault list contains all faults
    first_fault = f;

    /* for each gate, create a gate output slow-to-fall one (STF) fault */
    if (!(f = ALLOC(1,struct FAULT))) error("No more room!");
    f->node = n;
    f->io = GO;
    f->fault_type = STF;
    f->to_swlist = i;
    switch (n->type) {
      case   NOT:
      case   BUF:
        f->eqv_fault_num = 1;
        for (j = 0; j < w->inode[0]->nin; j++) {
          if (w->inode[0]->iwire[j]->nout > 1) f->eqv_fault_num++;
        }
        break;
      case    OR:
      case  NAND:
      case INPUT:
      case   AND:
      case   NOR: 
      case   EQV:
      case   XOR: f->eqv_fault_num = 1; break;
    }
    num_of_tdf_fault += f->eqv_fault_num;
    f->pnext = first_fault;
    f->pnext_undetect = first_fault;
    first_fault = f;

    /*if w has multiple fanout branches */
    if (w->nout > 1) {
      for (j = 0 ; j < w->nout; j++) {
        n = w->onode[j];
        switch (n->type) {
          case OUTPUT:
          case    OR:
          case   NOR: 
          case   AND:
          case  NAND:
          case   EQV:
          case   XOR:
            /* create STR */
            if (!(f = ALLOC(1,struct FAULT))) error("No more room!");
            f->node = n;
            f->io = GI;
            f->fault_type = STR;
            f->to_swlist = i;
            f->eqv_fault_num = 1;
            for (k = 0; k < n->nin; k++) {  
              if (n->iwire[k] == w) f->index = k;
            }
            num_of_tdf_fault++;
            f->pnext = first_fault;
            f->pnext_undetect = first_fault;
            first_fault = f;

            /* create STF */
            if (!(f = ALLOC(1,struct FAULT))) error("Room more room!");
            f->node = n;
            f->io = GI;
            f->fault_type = STF;
            f->to_swlist = i;
            f->eqv_fault_num = 1;
            for (k = 0; k < n->nin; k++) {
              if (n->iwire[k] == w) f->index = k;
            }
            num_of_tdf_fault++;
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

  //fprintf(stdout,"#number of equivalent faults = %d\n", fault_num);
  return;  
}/* end of generate_tdf_fault_list */

  fptr
transition_sim_v2(flist, num_of_current_detect)
  fptr flist;
  int *num_of_current_detect;
{
  wptr w,faulty_wire,wtemp;
  /* array of 16 fptrs, which points to the 16 faults in a simulation packet  */
  fptr simulated_fault_list[num_of_pattern];
  fptr f,ftemp;
  int fault_type;
  register int i,j,k,start_wire_index;
  register int num_of_fault;  
  int fault_sim_evaluate();
  wptr get_faulty_wire();
  int sim();
  static int test_no = 0;

  test_no++;
  num_of_fault = 0; // counts the number of faults in a packet

  /* num_of_current_detect is used to keep track of the number of undetected
   * faults detected by this vector, initialize it to zero */
  *num_of_current_detect = 0;

  /* Keep track of the minimum wire index of 16 faults in a packet.
   * the start_wire_index is used to keep track of the
   * first gate that needs to be evaluated.
   * This reduces unnecessary check of scheduled events.*/
  start_wire_index = 10000;
  first_faulty_wire = NULL;

  /* initialize the circuit - mark all inputs as changed and all other
   * nodes as unknown (2) */
  for (i = 0; i < ncktwire; i++) {
    if (i < ncktin) {
      sort_wlist[i]->flag |= CHANGED;
    }
    else {
      sort_wlist[i]->value = 2;
    }
  }

  sim(); /* do a fault-free simulation, see sim.c */
  if (debug) { display_io(); }

  /* expand the fault-free 0,1,2 value into 32 bits (2 = unknown)  
   * and store it in wire_value1 (good value) and wire_value2 (faulty value)*/
  for (i = 0; i < ncktwire; i++) {
    switch (sort_wlist[i]->value) {

      case 1: sort_wlist[i]->wire_value1 = ALL_ONE;  // 11 represents logic one
              sort_wlist[i]->wire_value2 = ALL_ONE; break;
      case 2: sort_wlist[i]->wire_value1 = 0x55555555; // 01 represents unknown
              sort_wlist[i]->wire_value2 = 0x55555555; break;
      case 0: sort_wlist[i]->wire_value1 = ALL_ZERO; // 00 represents logic zero
              sort_wlist[i]->wire_value2 = ALL_ZERO; break;
    }
    sort_wlist[i]->pnext = NULL;
  } // for i

  /* walk through every undetected fault 
   * the undetected fault list is linked by pnext_undetect */
  for (f = flist; f; f = f->pnext_undetect) {
    if (f->detect == REDUNDANT) { continue;} /* ignore redundant faults */
    if (f->activate == FALSE) { continue; }

    /* consider only active (aka. excited) fault
     * (sa1 with correct output of 0 or sa0 with correct output of 1) */
    if (f->fault_type != sort_wlist[f->to_swlist]->value) {

      /* if f is a primary output or is directly connected to an primary output
       * the fault is detected */
      if ((f->node->type == OUTPUT) ||
          (f->io == GO && sort_wlist[f->to_swlist]->flag & OUTPUT)) {
        f->detect = TRUE;
      }
      else {

        /* if f is an gate output fault */
        if (f->io == GO) {

          /* if this wire is not yet marked as faulty, mark the wire as faulty
           * and insert the corresponding wire to the list of faulty wires. */
          if (!(sort_wlist[f->to_swlist]->flag & FAULTY)) {
            sort_wlist[f->to_swlist]->pnext = first_faulty_wire;
            first_faulty_wire = sort_wlist[f->to_swlist];
            first_faulty_wire->flag |= FAULTY;
          }

          /* add the fault to the simulated fault list and inject the fault */
          simulated_fault_list[num_of_fault] = f;
          inject_fault_value(sort_wlist[f->to_swlist], num_of_fault,
                             f->fault_type); 

          /* mark the wire as having a fault injected 
           * and schedule the outputs of this gate */
          sort_wlist[f->to_swlist]->flag |= FAULT_INJECTED;
          for (k = 0; k < sort_wlist[f->to_swlist]->nout; k++) {
            sort_wlist[f->to_swlist]->onode[k]->owire[0]->flag |=
              SCHEDULED;
          }

          /* increment the number of simulated faults in this packet */
          num_of_fault++;
          /* start_wire_index keeps track of the smallest level of fault in this packet.
           * this saves simulation time.    */
          start_wire_index = MIN(start_wire_index,f->to_swlist);
        }  // if gate output fault

        /* the fault is a gate input fault */
        else {

          /* if the fault is propagated, set faulty_wire equal to the faulty wire.
           * faulty_wire is the gate output of f.  */
          if (faulty_wire = get_faulty_wire(f,&fault_type)) {

            /* if the faulty_wire is a primary output, it is detected */
            if (faulty_wire->flag & OUTPUT) {
              f->detect = TRUE;
            }

            else {

              /* if faulty_wire is not already marked as faulty, mark it as faulty
               * and add the wire to the list of faulty wires. */
              if (!(faulty_wire->flag & FAULTY)) {
                faulty_wire->pnext = first_faulty_wire;
                first_faulty_wire = faulty_wire;
                first_faulty_wire->flag |= FAULTY;
              }

              /* add the fault to the simulated list and inject it */
              simulated_fault_list[num_of_fault] = f;
              inject_fault_value(faulty_wire, num_of_fault,
                                 fault_type);

              /* mark the faulty_wire as having a fault injected 
               *  and schedule the outputs of this gate */
              faulty_wire->flag |= FAULT_INJECTED;
              for (k = 0; k < faulty_wire->nout; k++) {
                faulty_wire->onode[k]->owire[0]->flag |=
                  SCHEDULED;
              }


              num_of_fault++;
              start_wire_index = MIN(start_wire_index, f->to_swlist);
            }
          }
        }
      } // if  gate input fault
    } // if fault is active


    /*
     * fault simulation of a packet 
     */

    /* if this packet is full (16 faults)
     * or there is no more undetected faults remaining,
     * do the fault simulation */
    if ((num_of_fault == num_of_pattern) || !(f->pnext_undetect)) {

      /* starting with start_wire_index, evaulate all scheduled wires
       * start_wire_index helps to save time. */
      for (i = start_wire_index; i < ncktwire; i++) {
        if (sort_wlist[i]->flag & SCHEDULED) {
          sort_wlist[i]->flag &= ~SCHEDULED;
          fault_sim_evaluate(sort_wlist[i]);
        }
      } /* event evaluations end here */

      /* check detection and reset wires' faulty values
       * back to fault-free values.
       */
      for (w = first_faulty_wire; w; w = wtemp) {
        wtemp = w->pnext;
        w->pnext = NIL(struct WIRE);
        //printf("before : %d\n", w->flag);
        w->flag &= ~FAULTY;
        w->flag &= ~FAULT_INJECTED;
        w->fault_flag &= ALL_ZERO;
        //printf("after  : %d\n", w->flag);
        if (w->flag & OUTPUT) { // if primary output 
          for (i = 0; i < num_of_fault; i++) { // check every undetected fault
            if (!(simulated_fault_list[i]->detect)) {
              if ((w->wire_value2 & Mask[i]) ^      // if value1 != value2
                  (w->wire_value1 & Mask[i])) {
                if (((w->wire_value2 & Mask[i]) ^ Unknown[i])&&  // and not unknowns
                    ((w->wire_value1 & Mask[i]) ^ Unknown[i])){
                  simulated_fault_list[i]->detect = TRUE;  // then the fault is detected
                }
              }
            }
          }
        }
        w->wire_value2 = w->wire_value1;  // reset to fault-free values
      }  // for w = first_faulty_wire
      /*check();
        check2();*/
      num_of_fault = 0;  // reset the counter of faults in a packet
      start_wire_index = 10000;  //reset this index to a very large value.
      first_faulty_wire = NULL;
    } // end fault sim of a packet

  }  // end loop. for f = flist


  /* the following two loops are both for fault dropping  */  
  /* drop detected faults from the FRONT of the undetected fault list */
  while(flist) {
    if (flist->detect == TRUE) {
      /* printf("(%s %d %d %d)\n", flist->node->name, flist->io, flist->fault_type, flist->eqv_fault_num); */
      (*num_of_current_detect) += flist->eqv_fault_num;
      f = flist->pnext_undetect;
      flist->pnext_undetect = NULL;
      flist = f;
    }
    else {break;}
  }

  /* drop detected faults from WITHIN the undetected fault list*/
  if (flist) {
    for (f = flist; f->pnext_undetect; f = ftemp) {
      if (f->pnext_undetect->detect == TRUE) { 
        /* printf("(%s %d %d %d)\n", f->pnext_undetect->node->name, f->pnext_undetect->io, f->pnext_undetect->fault_type, f->pnext_undetect->eqv_fault_num); */
        (*num_of_current_detect) += f->pnext_undetect->eqv_fault_num;
        f->pnext_undetect = f->pnext_undetect->pnext_undetect;
        ftemp = f;
      }
      else {
        ftemp = f->pnext_undetect;
      }
    }
  }
  return(flist);
}/* end of fault_sim_a_vector */
