#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "global.h"
#include "miscell.h"

#define U  2
#define D  3
#define B  4 // D_bar
#define CONFLICT 2

extern int time_limit;
extern int backtrack_limit;     // maximum number of backtracked allowed, defatult is 50
extern int detect_num;          // number of patterns per fault, default is 1
/* recorded vectors */
char **all_vectors, **tmp_vectors;
int no_of_all_vectors;
int cap_of_all_vectors;
/* DFS counter */
int ref_counter;

struct _Stack {
  wptr wire;
  int frame;
  int value;
};
typedef struct _Stack Stack;

int
my_strncmp(s1, s2, n)
char *s1;
char *s2;
int n;
{
  int i;
  for (i = 0; i < n; i++)
    if (s1[i] != s2[i])
      return 1;
  return 0;
}

wptr
get_next_wire(w)
wptr w;
{
  int id = w->wlist_index;
  if (id + 1 < ncktin)
    return sort_wlist[id + 1];
  return NULL;
}

wptr
get_prev_wire(w)
wptr w;
{
  int id = w->wlist_index;
  if (id - 1 >= 0)
    return sort_wlist[id - 1];
  return NULL;
}

init_counter()
{
  int i;
  ref_counter = 0;
  for (i = 0; i < ncktwire; i++)
    sort_wlist[i]->counter = 0;
}

inc_counter()
{
  int i;
  if (ref_counter == 1000000000) {
    ref_counter = 0;
    for (i = 0; i < ncktwire; i++)
      sort_wlist[i]->counter = 0;
  }
  ref_counter += 1;
}

tdf_atpg() {
    printf("#compress = %d, detect_num = %d\n", compress, detect_num);
    fptr flist, undetect_fault;
    fptr fault_under_test;
    fptr f, ftemp;
    int i, j;
    int total_detect_num = 0;
    int total_no_of_backtracks = 0;
    int current_backtracks;
    int no_of_aborted_faults = 0;
    int no_of_redundant_faults = 0;
    int no_of_calls = 0;
    clock_t st_time = clock();
    /* generated test vectors */
    char **vectors = (char**)malloc(detect_num * sizeof(char*));
    int no_of_vectors;
    /* initialize all_vectors */
    all_vectors = (char**)malloc(1000 * sizeof(char*));
    cap_of_all_vectors = 1000;
    no_of_all_vectors = 0;
    /* function declaration */
    int tdf_podem();
    fptr tdf_simulate_vectors();
    void random_switch_pattern();
    /* generate TDF fault list */
    fault_under_test = first_fault;
    undetect_fault = first_fault;
    init_counter();
    /* TDF ATPG */
    while (fault_under_test && (clock() - st_time) / CLOCKS_PER_SEC < time_limit) {
        /*
        for (f = undetect_fault; f; f = f->pnext_undetect) {
          printf("%s s-a-%d %s\n", f->node->name, f->fault_type, f->io?"output":"input");
        }
        */
        switch (tdf_podem(fault_under_test, fault_under_test->detect_num, &current_backtracks, vectors, &no_of_vectors, TRUE)) {
	    case MAYBE:
                no_of_aborted_faults++;
                break;
                /* do not need to break here, still apply the vectors */
            case TRUE:
                /* add to all_vectors */
                for (i = 0; i < no_of_vectors; i++) {
                  /* increase capacity */
                  if (no_of_all_vectors == cap_of_all_vectors) {
                    tmp_vectors = malloc(2 * cap_of_all_vectors * sizeof(char*));
                    for (j = 0; j < cap_of_all_vectors; j++)
                      tmp_vectors[j] = all_vectors[j];
                    cap_of_all_vectors *= 2;
                    free(all_vectors);
                    all_vectors = tmp_vectors;
                  }
                  all_vectors[no_of_all_vectors] = vectors[i];
                  no_of_all_vectors += 1;
                }
                undetect_fault = tdf_simulate_vectors(vectors, no_of_vectors, undetect_fault, &total_detect_num);
                assert(fault_under_test->detect = TRUE);
                in_vector_no +=  no_of_vectors;
                break;
	    case FALSE:
                fault_under_test->detect = REDUNDANT;
                no_of_redundant_faults++;
                break;
        }
        fault_under_test->test_tried = TRUE;
        fault_under_test = NULL;
        for (f = undetect_fault; f; f = f->pnext_undetect) {
            if (!f->test_tried) {
                fault_under_test = f;
                break;
            }
        }
        total_no_of_backtracks += current_backtracks; // accumulate number of backtracks
        no_of_calls++;
    }
    fprintf(stderr, "number of abort: %d\n", no_of_aborted_faults);
    if (compress) {
        flist = generate_detected_fault_list();
        tdf_reverse_compression(flist);
        random_switch_pattern();
        flist = generate_detected_fault_list();
        tdf_reverse_compression(flist);
        random_switch_pattern();
        flist = generate_detected_fault_list();
        tdf_reverse_compression(flist);
        /* random_switch_pattern();
        flist = generate_detected_fault_list();
        tdf_reverse_compression(flist); */
    }
    tdf_display_patterns(all_vectors, in_vector_no);
}

/* generates patterns for a single fault */
int tdf_podem(fault, no_of_detect, current_backtracks, vectors, no_of_vectors, reset)
fptr fault;
int no_of_detect;
int *current_backtracks;
char **vectors;
int *no_of_vectors;
int reset;
{
    register int i,j;
    register nptr n;

    register wptr wpi; // points to the PI currently being assigned
    register wptr wtemp,wfault;    
    fptr next_fault;
    wptr tdf_test_possible();
    wptr tdf_fault_evaluate();
    int tdf_set_uniquely_implied_value();

    Stack *stack = malloc((ncktin + 1) * sizeof(Stack));
    Stack *pstack;
    int nstack = 0;
    int no_of_backtracks;           // current number of backtracks
    int find_test;                  // TRUE when a test pattern is found
    int no_test;                    // TRUE when it is proven that no test exists for this fault 
    
    /* initialize all circuit wires to unknown */
    if (reset) {
        for (i = 0; i < ncktwire; i++) {
            sort_wlist[i]->value = U;
            sort_wlist[i]->value2 = U;
            sort_wlist[i]->flag |= CHANGED;
            sort_wlist[i]->flag2 |= CHANGED;
        }
        *current_backtracks = 0;
    }
    if (fault->detect_num > no_of_detect)
        no_of_detect = fault->detect_num;
    *no_of_vectors = 0;
    find_test = FALSE;
    no_test = FALSE;
    wfault = NIL(struct WIRE);

    tdf_mark_propagate_tree(fault->node);

    /* Fig 7 starts here */
    /* set the initial goal, assign the first PI.  Fig 7.P1 */
    switch (tdf_set_uniquely_implied_value(fault)) {
        case TRUE: // if a  PI is assigned 
          sim();
	  sim2();  // Fig 7.3
	  if (wfault = tdf_fault_evaluate(fault)) {
            tdf_forward_imply(wfault);// propagate fault effect
          }
          // if fault effect reaches PO, done. Fig 7.10
	  if (tdf_check_test(fault)){
            find_test = TRUE;
          }
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
            printf("OK\n");
     * 3. already find a test pattern AND no_of_patterns meets required detect_num */
    while ((*current_backtracks < backtrack_limit) && !no_test && !find_test) {
        /* check if test possible.   Fig. 7.1 */
        if (wpi = tdf_test_possible(fault)) {
	    /* insert a new PI into decision_tree */
            stack[nstack].wire = wpi;
            stack[nstack].frame = wpi->frame;
            stack[nstack].value = (wpi->frame == 1 ? wpi->value : wpi->value2);
            nstack += 1;
        }
        else { // no test possible using this assignment, backtrack. 
            while (nstack > 0 && !wpi) {
              pstack = stack + (nstack - 1);
	      /* if both 01 already tried, backtrack. Fig.7.7 */
              if (pstack->frame == 1) {
                if (pstack->value == 2) {
                  pstack->wire->value = U;
                  pstack->wire->flag |= CHANGED;
                  if (wtemp = get_next_wire(pstack->wire)) {
                    wtemp->value2 = U;
                    wtemp->flag2 |= CHANGED;
                  }
                  nstack -= 1;
                  *current_backtracks++;
                }
                else {
                  pstack->value = 2;
                  pstack->wire->value = pstack->wire->value ^ 1;
                  pstack->wire->flag |= CHANGED;
                  if (wtemp = get_next_wire(pstack->wire)) {
                    wtemp->value2 = wtemp->value2 ^ 1;
                    wtemp->flag2 |= CHANGED;
                    assert(pstack->wire->value == wtemp->value2);
                  }
                  wpi = pstack->wire;
                }
              }
              else {
                if (pstack->value == 2) {
                  pstack->wire->value2 = U;
                  pstack->wire->flag2 |= CHANGED;
                  if (wtemp = get_prev_wire(pstack->wire)) {
                    wtemp->value = U;
                    wtemp->flag |= CHANGED;
                  }
                  nstack -= 1;
                  *current_backtracks++;
                }
                else {
                  pstack->value = 2;
                  pstack->wire->value2 = pstack->wire->value2 ^ 1;
                  pstack->wire->flag2 |= CHANGED;
                  if (wtemp = get_prev_wire(pstack->wire)) {
                    wtemp->value = wtemp->value ^ 1;
                    wtemp->flag |= CHANGED;
                    assert(pstack->wire->value2 == wtemp->value);
                  }
                  wpi = pstack->wire;
                }
              }
            } // while decision tree && ! wpi
            if (!wpi) no_test = TRUE; //decision tree empty,  Fig 7.9
        } // no test possible

        if (wpi) {
            sim();
            sim2();
            if (wfault = tdf_fault_evaluate(fault)) tdf_forward_imply(wfault);
            if (tdf_check_test(fault)) {
                find_test = TRUE;
            }  // if check_test()
        } // again
    } // while (three conditions)
    tdf_unmark_propagate_tree(fault->node);

    if (find_test) {
        if (compress) {
            next_fault = fault->pnext_undetect;
            if (next_fault) {
                tdf_podem(next_fault, no_of_detect, current_backtracks, vectors, no_of_vectors, FALSE);
            }
        } 
        tdf_fill_pattern(vectors, no_of_vectors, no_of_detect);
        assert(*no_of_vectors >= no_of_detect);
    }
    /* undo decision */
    for (i = 0; i < nstack; i++) {
        pstack = stack + i;
        if (pstack->frame == 1) {
            pstack->wire->value = U;
            pstack->wire->flag |= CHANGED;
            if (wtemp = get_next_wire(pstack->wire)) {
              wtemp->value2 = U;
              wtemp->flag2 |= CHANGED;
            }
        }
        else {
            pstack->wire->value2 = U;
            pstack->wire->flag2 |= CHANGED;
            if (wtemp = get_prev_wire(pstack->wire)) {
              wtemp->value = U;
              wtemp->flag |= CHANGED;
            }
        }
    }
    free(stack);
    
    if (find_test) {
        return TRUE;
    }
    else if (no_test) {
        return FALSE;
    }
    else {
        return MAYBE;
    }
}/* end of podem */


/* drive D or B to the faulty gate (aka. GUT) output
 * insert D or B into the circuit.
 * returns w (the faulty gate output) if GUT output is set to D or B successfully.
 * returns NULL if if faulty gate output still remains unknown  */
wptr
tdf_fault_evaluate(fault)
fptr fault;
{
    register int i;
    register int temp1;
    register wptr w;

    if (fault->io) { // if fault is on GUT gate output
        w = fault->node->owire[0]; // w is GUT output wire
        if (w->value2 == U) return(NULL);
        if (fault->fault_type == 0 && w->value2 == 1) w->value2 = D; // D means 1/0
        if (fault->fault_type == 1 && w->value2 == 0) w->value2 = B; // B_bar 0/1
        return(w);
    }
    else { // if fault is GUT gate input
        w = fault->node->iwire[fault->index];
        if (w->value2 == U) return(NULL);
        else {
            temp1 = w->value2;
            if (fault->fault_type == 0 && w->value2 == 1) w->value2 = D;
            if (fault->fault_type == 1 && w->value2 == 0) w->value2 = B;
            if (fault->node->type == OUTPUT) return(NULL);
            evaluate2(fault->node);  // five-valued, evaluate one gate only, sim.c
            w->value2 = temp1;
	    /* if GUT gate output changed */
            if (fault->node->owire[0]->flag2 & CHANGED) {
	      fault->node->owire[0]->flag2 &= ~CHANGED; // stop GUT output change propagation
	      return (fault->node->owire[0]); // returns the output wire of GUT
            }
            else return(NULL); // faulty gate output does not change
        }
    }
}/* end of fault_evaluate */


/* iteratively foward implication
 * in a depth first search manner*/ 
tdf_forward_imply(w)
wptr w;
{
    register int i;

    for (i = 0; i < w->nout; i++) {
        if (w->onode[i]->type != OUTPUT) {
            evaluate2(w->onode[i]);
            if (w->onode[i]->owire[0]->flag2 & CHANGED) {
	      tdf_forward_imply(w->onode[i]->owire[0]); // go one level further
            }
            w->onode[i]->owire[0]->flag2 &= ~CHANGED;
        }
    }
    return;
}/* end of forward_imply */


/* Fig 8 
 * this function determines objective_wire and objective_level. 
 * it returns the newly assigned PI if test is possible. 
 * it returns NULL if no test is possible. */
wptr
tdf_test_possible(fault)
fptr fault;
{
    register nptr n;
    register wptr object_wire;
    register int object_level;
    register int object_frame = 0;
    nptr tdf_find_propagate_gate();
    wptr tdf_find_pi_assignment();
    int tdf_trace_unknown_path2();
    
    /* if the fault is not on primary output */
    if (fault->node->type != OUTPUT) {
      
      /* if the faulty gate (aka. gate under test, G.U.T.) output is not U,  Fig. 8.1 */ 
      if ( (( fault->io && fault->node->owire[0]->value == fault->fault_type) || 
            (!fault->io && fault->node->iwire[fault->index]->value == fault->fault_type)) && 
           fault->node->owire[0]->value2 ^ U) {

	  /* if GUT output is not D or D_bar, no test possible */
	  if (!((fault->node->owire[0]->value2 == B) ||
                (fault->node->owire[0]->value2 == D))) return(NULL);

	  /* find the next gate n to propagate, Fig 8.5*/
	  if (!(n = tdf_find_propagate_gate(fault->node->owire[0]->level)))
	    return(NULL);

	  /*determine objective level according to the type of n.   Fig 8.8*/ 
          switch(n->type) {
              case  AND:
              case  NOR: object_level = 1; break;
              case NAND:
              case   OR: object_level = 0; break;
              default:
                return(NULL);
          }
          /* object_wire is the gate n output. */
          object_wire = n->owire[0];
          object_frame = 2;
      } 

      else if (( fault->io && fault->node->owire[0]->value == fault->fault_type) ||
               (!fault->io && fault->node->iwire[fault->index]->value == fault->fault_type)) { // if faulty gate output is U and activated

          /* if X path disappear, no test possible  */
          inc_counter();
          if (!(tdf_trace_unknown_path2(fault->node->owire[0])))
              return(NULL);

          /* if fault is on GUT otuput,  Fig 8.2*/
          if (fault->io) {
              /* objective_level is opposite to stuck fault  Fig 8.3 */ 
              object_level = fault->fault_type ^ 1;
              /* objective_wire is on faulty gate output */
              object_wire = fault->node->owire[0];
          }

          /* if fault is on GUT input, Fig 8.2*/ 
          else {
            /* if faulted input is not U  Fig 8.4 */
              if (fault->node->iwire[fault->index]->value2 ^ U) {
                /* determine objective value according to GUT type. Fig 8.9*/
                  switch (fault->node->type) {
                      case  AND:
                      case  NOR: object_level = 1; break;
                      case NAND:
                      case   OR: object_level = 0; break;
                      default:
                          return(NULL);
                  }
                  /*objective wire is GUT output. */
                  object_wire = fault->node->owire[0];
              }  // if faulted input is not U

              else { // if faulted input is U
                  /*objective level is opposite to stuck fault.    Fig 8.10*/
                  object_level = fault->fault_type ^ 1;
                  /* objective wire is faulty wire itself */
                  object_wire = fault->node->iwire[fault->index];
              }
          }
          object_frame = 2;
      }
      else { /* v1 activate */
          /* if fault is on GUT otuput,  Fig 8.2*/
          if (fault->io) {
              /* objective_level is opposite to stuck fault  Fig 8.3 */ 
              object_level = fault->fault_type;
              /* objective_wire is on faulty gate output */
              object_wire = fault->node->owire[0];
          }

          /* if fault is on GUT input, Fig 8.2*/ 
          else {
              /*objective level is opposite to stuck fault.    Fig 8.10*/
              object_level = fault->fault_type;
              /* objective wire is faulty wire itself */
              object_wire = fault->node->iwire[fault->index];
          }
          object_frame = 1;
      }
    } // if fault not on PO

    else { // else if fault on PO
        /* if faulty PO is still unknown */
        if (fault->node->iwire[0]->value ^ U) {
	    /*objective level is opposite to the stuck fault */ 
            object_level = fault->fault_type ^ 1;
	    /* objective wire is the faulty wire itself */
            object_wire = fault->node->iwire[0];
            object_frame = 2;
        }

        else {
            object_level = fault->fault_type;
            object_wire = fault->node->iwire[0];
            object_frame = 1;
        }
    }// else if fault on PO

    /* find a pi to achieve the objective_level on objective_wire.
     * returns NULL if no PI is found.  */ 
    assert(object_frame == 1 || object_frame == 2);
    return tdf_find_pi_assignment(object_wire, object_level, object_frame);
   
}/* end of test_possible */


/* backtrace to PI, assign a PI to achieve the objective.  Fig 9
 * returns the wire pointer to PI if succeed.
 * returns NULL if no such PI found.                             */
wptr
tdf_find_pi_assignment(object_wire, object_level, object_frame)
wptr object_wire;
int object_level;
{
    register wptr new_object_wire;
    register int new_object_level;
    wptr tdf_find_hardest_control(), tdf_find_easiest_control();
    wptr wtmp;

    /* if PI, assign the same value as objective Fig 9.1, 9.2 */
    if (object_wire->flag & INPUT) {
      if (object_frame == 1) {
        object_wire->value = object_level;
        object_wire->flag |= CHANGED;
        object_wire->frame = object_frame;
        if (wtmp = get_next_wire(object_wire)) {
          wtmp->value2 = object_level;
          wtmp->flag2 |= CHANGED;
        }
      }
      else {
        object_wire->value2 = object_level;
        object_wire->flag2 |= CHANGED;
        object_wire->frame = object_frame;
        if (wtmp = get_prev_wire(object_wire)) {
          wtmp->value = object_level;
          wtmp->flag |= CHANGED;
        }
      }
      return(object_wire);
    }

    /* if not PI, backtrace to PI  Fig 9.3, 9.4, 9.5*/
    else {
        switch(object_wire->inode[0]->type) {
        case   OR:
        case NAND:
	  if (object_level)
            new_object_wire = tdf_find_easiest_control(object_wire->inode[0], object_frame);  // decision gate
	  else
            new_object_wire = tdf_find_hardest_control(object_wire->inode[0], object_frame); // imply gate
          break;
        case  NOR:
        case  AND:
          if (object_level)
            new_object_wire = tdf_find_hardest_control(object_wire->inode[0], object_frame);
          else
            new_object_wire = tdf_find_easiest_control(object_wire->inode[0], object_frame);
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
        if (new_object_wire) {
          return tdf_find_pi_assignment(new_object_wire, new_object_level, object_frame);
        }
        else return(NULL);
    }
}/* end of find_pi_assignment */

/* Fig 9.4 */
wptr
tdf_find_hardest_control(n, object_frame)
nptr n;
int object_frame;
{
    register int i;
    /* because gate inputs are arranged in a increasing level order,
     * larger input index means harder to control */
    for (i = n->nin - 1; i >= 0; i--) {
      if (object_frame == 1 && n->iwire[i]->value == U) return n->iwire[i];
      if (object_frame == 2 && n->iwire[i]->value2 == U) return n->iwire[i];
    }
    return(NULL);
}/* end of find_hardest_control */


/* Fig 9.5 */
wptr
tdf_find_easiest_control(n, object_frame)
nptr n;
int object_frame;
{
    register int i;

    for (i = 0; i < n->nin; i++) {
        if (object_frame == 1 && n->iwire[i]->value == U) return n->iwire[i];
        if (object_frame == 2 && n->iwire[i]->value2 == U) return n->iwire[i];
    }
    return(NULL);
}/* end of find_easiest_control */


/* Find the eastiest propagation gate.   Fig 8.5, Fig 8.6 
 * returns the next gate with D or B on inputs, U on output, nearest to PO
 * returns NULL if no such gate found. */
nptr
tdf_find_propagate_gate(level)
int level;
{
    register int i,j,k;
    register wptr w;
    int tdf_trace_unknown_path2();

    /* check every wire in decreasing level order
     * so that wires nearer to PO is checked earlier. */
    for (i = ncktwire - 1; i >= 0; i--) {
        /* if reach the same level as the fault, then no propagation path exists */
        if (sort_wlist[i]->level == level) return(NULL);
	/* gate outptu is U */
	/* a marked gate means it is on the path to PO */
        if ((sort_wlist[i]->value2 == U) &&
            (sort_wlist[i]->inode[0]->flag & MARKED)) { 
	    /*  cehck all gate intputs */  
            for (j = 0; j < sort_wlist[i]->inode[0]->nin; j++) {
                w = sort_wlist[i]->inode[0]->iwire[j];
		/* if there is ont gate intput is D or B */
                if ((w->value2 == D) || (w->value2 == B)) {
                  inc_counter();
		  if (tdf_trace_unknown_path2(sort_wlist[i])) // check X path  Fig 8.6
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
tdf_trace_unknown_path2(w)
wptr w;
{
    register int i;
    register wptr wtemp;

    w->counter = ref_counter;
    if (w->flag2 & OUTPUT) return(TRUE); // X path exists
    for (i = 0; i < w->nout; i++) {
        wtemp = w->onode[i]->owire[0];
        if (wtemp->value2 == U && wtemp->counter != ref_counter) {
            if(tdf_trace_unknown_path2(wtemp)) return(TRUE);
        }
    }
    return(FALSE); // X-path disappear
}/* end of trace_unknown_path */


/* Check if any D or D_bar reaches PO. Fig 7.4 */
tdf_check_test(fault)
fptr fault;
{
    register int i, is_test;
    
    if (fault->io) {
      if (fault->node->owire[0]->value != fault->fault_type)
        return FALSE;
    }
    else {
      if (fault->node->iwire[fault->index]->value != fault->fault_type)
        return FALSE;
    }
    is_test = FALSE;
    for (i = 0; i < ncktout; i++) {
        if ((cktout[i]->value2 == D) || (cktout[i]->value2 == B)) {
            is_test = TRUE;
            break;
        }
    }
    return(is_test);
}/* end of check_test */

/* exhaustive search of all nodes on the path from n to PO */
tdf_mark_propagate_tree(n)
nptr n;
{
    register int i,j;

    if (n->flag & MARKED) return;
    n->flag |= MARKED; // MARKED means this node is on the path to PO 
    /* depth first search */
    for (i = 0; i < n->nout; i++) {
        for (j = 0; j < n->owire[i]->nout; j++) {
            tdf_mark_propagate_tree(n->owire[i]->onode[j]);
        }
    }
    return;
}/* end of mark_propagate_tree */

/* clear all the MARKS */ 
tdf_unmark_propagate_tree(n)
nptr n;
{
    register int i,j;

    if (n->flag & MARKED) {
        n->flag &= ~MARKED;
        for (i = 0; i < n->nout; i++) {
            for (j = 0; j < n->owire[i]->nout; j++) {
                tdf_unmark_propagate_tree(n->owire[i]->onode[j]);
            }
        }
    }
    return;
}/* end of unmark_propagate_tree */

/* set the initial objective.  
 * returns TRUE if we can backtrace to a PI to assign
 * returns CONFLICT if it is impossible to achieve or set the initial objective*/
tdf_set_uniquely_implied_value(fault)
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
                         switch (tdf_backward_imply2(fault->node->iwire[i],1)) {
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
                         switch (tdf_backward_imply2(fault->node->iwire[i],0)) {
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
    switch (tdf_backward_imply(w,(fault->fault_type))) {
        case TRUE: pi_is_reach = TRUE; break;
        case CONFLICT: return(CONFLICT); break;
        case FALSE: break;  
    }
    switch (tdf_backward_imply2(w,(fault->fault_type ^ 1))) {
        case TRUE: pi_is_reach = TRUE; break;
        case CONFLICT: return(CONFLICT); break;
        case FALSE: break;  
    }

    return(pi_is_reach);
}/* end of set_uniquely_implied_value */

/*do a backward implication of the objective: set current_wire to logic_level 
 *implication means a natural consequence of the desired objective. 
 *returns TRUE if the backward implication reaches at least one PI 
 *returns FALSE if the backward implication reaches no PI */
tdf_backward_imply(current_wire,logic_level)
wptr current_wire;
int logic_level;
{
    register int pi_is_reach = FALSE;
    register int i;
    wptr next_wire;

    if (current_wire->flag & INPUT) { // if PI
        if (current_wire->value != U &&
            current_wire->value != logic_level) {
            return(CONFLICT); // conlict with previous assignment
        }
        current_wire->value = logic_level; // assign PI to the objective value
        current_wire->flag |= CHANGED;
        if (next_wire = get_next_wire(current_wire)) {
          next_wire->value2 = logic_level;
          next_wire->flag2 |= CHANGED;
        }
	// CHANGED means the logic value on this wire has recently been changed
        return(TRUE);
    }
    else { // if not PI
        switch (current_wire->inode[0]->type) {
	  /* assign NOT input opposite to its objective ouput */
          /* go backward iteratively.  depth first search */
            case NOT:
                switch (tdf_backward_imply(current_wire->inode[0]->iwire[0],
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
                        switch (tdf_backward_imply(current_wire->inode[0]->iwire[i],1)) {
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
                        switch (tdf_backward_imply(current_wire->inode[0]->iwire[i],1)) {
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
                        switch (tdf_backward_imply(current_wire->inode[0]->iwire[i],0)) {
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
                        switch (tdf_backward_imply(current_wire->inode[0]->iwire[i],0)) {
                            case TRUE: pi_is_reach = TRUE; break;
                            case CONFLICT: return(CONFLICT); break;
                            case FALSE: break;
                        }
                    }
                }
                break;

            case BUF:
                switch (tdf_backward_imply(current_wire->inode[0]->iwire[0],logic_level)) {
                    case TRUE: pi_is_reach = TRUE; break;
                    case CONFLICT: return(CONFLICT); break;
                    case FALSE: break;
               }
                break;
        }
	
        return(pi_is_reach);  
    }
}/* end of backward_imply */

tdf_backward_imply2(current_wire,logic_level)
wptr current_wire;
int logic_level;
{
    register int pi_is_reach = FALSE;
    register int i;
    wptr prev_wire;

    if (current_wire->flag2 & INPUT) { // if PI
        if (current_wire->value2 != U &&
            current_wire->value2 != logic_level) {
            return(CONFLICT); // conlict with previous assignment
        }
        current_wire->value2 = logic_level; // assign PI to the objective value
        current_wire->flag2 |= CHANGED;
        if (prev_wire = get_prev_wire(current_wire)) {
          prev_wire->value = logic_level;
          prev_wire->flag |= CHANGED;
        }
	// CHANGED means the logic value on this wire has recently been changed
        return(TRUE);
    }
    else { // if not PI
        switch (current_wire->inode[0]->type) {
	  /* assign NOT input opposite to its objective ouput */
          /* go backward iteratively.  depth first search */
            case NOT:
                switch (tdf_backward_imply2(current_wire->inode[0]->iwire[0],
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
                        switch (tdf_backward_imply2(current_wire->inode[0]->iwire[i],1)) {
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
                        switch (tdf_backward_imply2(current_wire->inode[0]->iwire[i],1)) {
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
                        switch (tdf_backward_imply2(current_wire->inode[0]->iwire[i],0)) {
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
                        switch (tdf_backward_imply2(current_wire->inode[0]->iwire[i],0)) {
                            case TRUE: pi_is_reach = TRUE; break;
                            case CONFLICT: return(CONFLICT); break;
                            case FALSE: break;
                        }
                    }
                }
                break;

            case BUF:
                switch (tdf_backward_imply2(current_wire->inode[0]->iwire[0],logic_level)) {
                    case TRUE: pi_is_reach = TRUE; break;
                    case CONFLICT: return(CONFLICT); break;
                    case FALSE: break;
               }
                break;
        }
	
        return(pi_is_reach);  
    }
}/* end of backward_imply2 */

/* generate multiple patterns by filling unknowns */
tdf_fill_pattern(vectors, no_of_vectors, no_of_detects)
char **vectors;
int *no_of_vectors;
int no_of_detects;
{
  int i, j;
  char *pattern;
  while (*no_of_vectors < no_of_detects) {
    pattern = (char*)malloc(ncktin + 1);
    for (j = 0; j < ncktin; j++) {
      switch (cktin[j]->value) {
        case 0:
        case B: pattern[j] = '0'; break;
        case 1:
        case D: pattern[j] = '1'; break;
        case U: pattern[j] = '0' + (rand() & 1); break;
        default: printf("something is wrong in tdf_fill_pattern.\n");
      }
    }
    switch (cktin[0]->value2) {
      case 0:
      case B: pattern[ncktin] = '0'; break;
      case 1:
      case D: pattern[ncktin] = '1'; break;
      case U: pattern[ncktin] = '0' + (rand() & 1); break;
      default: printf("something is wrong in tdf_fill_pattern.\n");
    }
    vectors[*no_of_vectors] = pattern;
    *no_of_vectors += 1;
  }
}

tdf_reverse_compression(flist)
fptr flist;
{
    fptr f;
    char **comp_vectors = malloc(in_vector_no * sizeof(char*));
    int no_of_comp_vectors = 0;
    int i, j, detect_num, useful;
    printf("# before compression: %d\n", in_vector_no);
    for(i = in_vector_no - 1; i >= 0; i--) {
        flist = tdf_sim_a_vector(all_vectors[i], flist, &detect_num, &useful);
        if(useful == TRUE) {
            comp_vectors[no_of_comp_vectors] = all_vectors[i];
            no_of_comp_vectors += 1;
        }
        else {
            free(all_vectors[i]);
        }
    }
    free(all_vectors);
    all_vectors = comp_vectors;
    in_vector_no = no_of_all_vectors = no_of_comp_vectors;
    printf("# after compression: %d\n", in_vector_no);
}

void
random_switch_pattern()
{
  int i, j;
  char* tmp;
  for (i = 0; i < in_vector_no; i++) {
    j = rand() % (i+1);
    tmp = all_vectors[i];
    all_vectors[i] = all_vectors[j];
    all_vectors[j] = tmp;
  }
}
