/**********************************************************************/
/*           This is the logic simulator for atpg                     */
/*                                                                    */
/*           Author: Hi-Keung TonyMa                                 */
/*           last update : 09/25/1987                                 */
/**********************************************************************/

#include <stdio.h>
#include "global.h"
#include "miscell.h"
#include "logic_tbl.h"


/*
*   sim
*
*   RETURNS
*       no value is returned
*
*   SIDE-EFFECTS
*       changes the logic values inside some wires' data structures
*
*   perform the logic simulation 
*   event-driven technique coupled with levelling mechanism is employed
*   single pattern, no fault injected
*/

void
sim()
{
    int i, j;
    int evaluate();

    /* for every input */
    for (i = 0; i < ncktin; i++) {

      /* if a input has changed, schedule the gates connected to it */
        if (sort_wlist[i]->flag & CHANGED) {
            sort_wlist[i]->flag &= ~CHANGED;
            for (j = 0; j < sort_wlist[i]->nout; j++) {
                if (sort_wlist[i]->onode[j]->nout) {
                    sort_wlist[i]->onode[j]->owire[0]->flag |= SCHEDULED;
                }
            }
        }
    } // for every input

    /* evaluate every scheduled gate & propagate any changes
     * walk through all wires in increasing order
     * Because the wires are sorted according to their levels,
     * it is correct to evaluate the wires in increasing order.   */
    for (i = ncktin; i < ncktwire; i++) {
        if (sort_wlist[i]->flag & SCHEDULED) {
            sort_wlist[i]->flag &= ~SCHEDULED;
            evaluate(sort_wlist[i]->inode[0]);
            if (sort_wlist[i]->flag & CHANGED) {
                sort_wlist[i]->flag &= ~CHANGED;
                for (j = 0; j < sort_wlist[i]->nout; j++) {
                    if (sort_wlist[i]->onode[j]->nout) {
                        sort_wlist[i]->onode[j]->owire[0]->flag |= SCHEDULED;
                    }
                }
            }
        }
    }
    return;
}/* end of sim */

evaluate(n)
nptr n;
{
    unsigned int old_value, new_value;
    int i;

    old_value = n->owire[0]->value;

    /* decompose a multiple-input gate into multiple levels of two-input gates  
     * then look up the truth table of each two-input gate
     */
    switch(n->type) {
        case AND:
        case BUF:
        case NAND:
            new_value = 1;
            for (i = 0; i < n->nin; i++) {
                new_value = ANDTABLE[n->iwire[i]->value][new_value];
            }
            if (n->type == NAND) {
                new_value = INV[new_value];
            }
            break;
        case OR:
        case NOR:
            new_value = 0;
            for (i = 0; i < n->nin; i++) {
                new_value = ORTABLE[n->iwire[i]->value][new_value];
            }
            if (n->type == NOR) {
                new_value = INV[new_value];
            }
            break;
        case NOT:
            new_value = INV[n->iwire[0]->value];
            break;
        case XOR:
            new_value = XORTABLE[n->iwire[0]->value][n->iwire[1]->value];
            break;
        case EQV:
            new_value =INV[(XORTABLE[n->iwire[0]->value][n->iwire[1]->value])];
            break;
    }
    if (old_value != new_value) {
        n->owire[0]->flag |= CHANGED;
        n->owire[0]->value = new_value;
    }
    return;
}/* end of evaluate */


/*
* unpack an unsigned integer and return a particular bit
*/
char
unpack(value,bit_no)
unsigned int value;
int bit_no;
{
    register int bit_value;

    bit_value = (value >> (bit_no - 1)*2) & 3;
    switch(bit_value) {
        case 0: return('0'); break;
        case 1: return('x'); break;
        case 3: return('1'); break;
    }
} /* end of unpack */

int
ctoi(c)
char c;
{
   if(c == '2') return(2);
   if(c == '1') return(1);
   if(c == '0') return(0);
}

