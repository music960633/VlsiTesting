#include <stdio.h>
#include "global.h"
#include "miscell.h"

#define U  2
#define D  3
#define B  4

extern char *filename;

display_line(fault)
fptr fault;
{
    register int i;
    char unpack();

    for (i = 0; i < ncktin; i++) {
        switch (cktin[i]->value) {
            case 0: fprintf(stdout,"0"); break;
            case 1: fprintf(stdout,"1"); break;
            case U: fprintf(stdout,"x"); break;
            case D: fprintf(stdout,"D"); break;
            case B: fprintf(stdout,"B"); break;
        }
    }
    fprintf(stdout," ");
    for (i = 0 ; i < fault->node->nin; i++) {
        fprintf(stdout,"%s = ",fault->node->iwire[i]->name);
        switch (fault->node->iwire[i]->value) {
            case 0: fprintf(stdout,"0"); break;
            case 1: fprintf(stdout,"1"); break;
            case U: fprintf(stdout,"x"); break;
            case D: fprintf(stdout,"D"); break;
            case B: fprintf(stdout,"B"); break;
        }
        fprintf(stdout,"; ");
    }
    fprintf(stdout,"output = ");
    switch (fault->node->owire[0]->value) {
        case 0: fprintf(stdout,"0"); break;
        case 1: fprintf(stdout,"1"); break;
        case U: fprintf(stdout,"x"); break;
        case D: fprintf(stdout,"D"); break;
        case B: fprintf(stdout,"B"); break;
    }
    fprintf(stdout,"\n");
    return;
}/* end of display_line */


/*
* print primary input and output lines' values
*/
display_io()
{
    register int i;
    char unpack();


    fprintf(stdout,"T\'");
    for (i = 0; i < ncktin; i++) {
        switch (cktin[i]->value) {
            case 0: fprintf(stdout,"0"); break;
            case 1: fprintf(stdout,"1"); break;
            case U: fprintf(stdout,"x"); break;
            case D: fprintf(stdout,"1"); break;
            case B: fprintf(stdout,"0"); break;
        }
    }
    fprintf(stdout,"'");
/*
    fprintf(stdout," ");
    for (i = 0; i < ncktout; i++) {
        switch (cktout[i]->value) {
            case 0: fprintf(stdout,"0"); break;
            case 1: fprintf(stdout,"1"); break;
            case U: fprintf(stdout,"x"); break;
            case D: fprintf(stdout,"D"); break;
            case B: fprintf(stdout,"B"); break;
        }
    }
*/
    fprintf(stdout,"\n");
    return;
}/* end of display_io */


display_undetect(undetect_fault)
fptr undetect_fault;
{
    register int i;
    register fptr f;
    register wptr w;
    FILE *out,*fopen();
    char ufile[40];

    sprintf(ufile,"%s.uf",filename); 
    out = fopen(ufile,"w");
    for (f = undetect_fault; f; f = f->pnext_undetect) {
        switch (f->node->type) {
            case INPUT:
                fprintf(out,"primary input: %s\n",f->node->owire[0]->name);
                break;
            case OUTPUT:
                fprintf(out,"primary output: %s\n",f->node->iwire[0]->name);
                break;
            default:
                fprintf(out,"gate: %s ;",f->node->name);
                if (f->io == GI) {
                    fprintf(out,"input wire name: %s\n",
                            f->node->iwire[f->index]->name);
                }
                else {
                    fprintf(out,"output wire name: %s\n",
                            f->node->owire[0]->name);
                }
                break;
        }
        fprintf(out,"fault_type = ");
        switch (f->fault_type) {
            case STUCK0:
                fprintf(out,"s-a-0\n"); break;
            case STUCK1:
                fprintf(out,"s-a-1\n"); break;
        }
        fprintf(out,"detection flag =");
        switch (f->detect) {
            case FALSE:
                fprintf(out," aborted\n");
                break;
            case REDUNDANT:
                fprintf(out," redundant\n");
                break;
            case TRUE:
                fprintf(out," internal error\n");
                break;
        }
        fprintf(out,"fault no. = %d\n", f->fault_no);
        /*if (f->io) w = f->node->owire[0];
        else w = f->node->iwire[f->index];
        for (i = 0; i < ncktin; i++) {
            fprintf(out,"%d ",w->pi_reach[i]);
        }
        fprintf(out,"\n");*/
        fprintf(out,"\n");
    }
    fclose(out);
    return;
}/* end of display_undetect */


void
display_fault(f)
fptr f;
{
    register int i;
    register wptr w;

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
                fprintf(stdout,"input wire name: %s\n",
                        f->node->iwire[f->index]->name);
            }
            else {
                fprintf(stdout,"output wire name: %s\n",
                        f->node->owire[0]->name);
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
    fprintf(stdout,"detection flag =");
    switch (f->detect) {
        case FALSE:
            fprintf(stdout," aborted\n");
            break;
        case REDUNDANT:
            fprintf(stdout," redundant\n");
            break;
        case TRUE:
            fprintf(stdout," internal error\n");
            break;
    }
    fprintf(stdout,"\n");
}/* end of display_fault */
