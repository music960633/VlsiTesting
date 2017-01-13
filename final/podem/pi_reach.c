
/**********************************************************************/
/*           This is the routine to set up the                        */
/*           pi_reach array of each wire                              */
/*                                                                    */
/*           Author: Tony Hi-Keung Ma                                 */
/*           last update : 5/24/1986                                  */
/**********************************************************************/


#include <stdio.h>
#include "global.h"
#include "miscell.h"


setup_pi_reach()
{
    register wptr w;
    register int i;

    for (i = 0; i < ncktwire; i++) {
        sort_wlist[i]->pi_reach = ALLOC(ncktin,short);
    }
    for (i = 0; i < ncktin; i++) {
        increment_pi_reach(cktin[i],i);
    }
    return;
}/* end of setup_pi_reach */


increment_pi_reach(wire,pi)
wptr wire;
int pi;
{
    register int i;

    (wire->pi_reach[pi])++;
    for (i = 0; i < wire->nout; i++) {
        if (wire->onode[i]->nout) {
            increment_pi_reach(wire->onode[i]->owire[0],pi);
        }
    }
    return;
}/* end of increment_pi_reach */
