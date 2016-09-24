/**********************************************************************/
/*           This is the input processor for atpg                     */
/*                                                                    */
/*           Author: Tony Hi Keung Ma                                 */
/*           last update : 10/13/1987                                 */
/**********************************************************************/


#include <stdio.h>
#include "global.h"
#include "miscell.h"

#define LSIZE   500       /* line length */
#define NUM_OF_INPUT 1500  /* maximum number of inputs */
#define NUM_OF_OUTPUT 1500 /* maximum number of outputs */

int debug = 0;            /* != 0 if debugging;  this is a switch of debug mode */

char *filename;           /* current input file */
int lineno = 0;           /* current line number */
char *targv[100];        /* pointer to tokens on current command line */
int targc;                /* number of args on current command line */
int file_no = 0;         /* number of current file */
wptr *temp_cktin;        /* temporary input wire list */
wptr *temp_cktout;       /* temporary output wire list */

/* eq() routine checks the equivalence of two character strings
 * return TRUE if they are equal, otherwise return FALSE
*/
eq(string1,string2)
register char *string1,*string2;
{
    while(*string1 && *string2) {
        if(*string1++ != *string2++) return(FALSE);
    }
    if (!(*string2)) return(*string1 == '\0');
    return(*string2 == '\0');
}/* end of eq */


/* convert the name into integer to index the hashtable */
int
hashcode(name)
char *name;
{ 
    int i = 0;
    int j = 0;

    while (*name && j < 8) {
        i = i*10 + (*name++ - '0');
        j++;
    }
    i = i%HASHSIZE;
    return(i<0 ? i + HASHSIZE : i);
}/* end of hashcode */


/* nfind checks the existence of a node
 * return the node pointer if it exists; otherwise return a NULL pointer
 */
nptr
nfind(name)
char *name;
{ 
    nptr ntemp;

    /* search the linked list of hast_nlist[code],
     the list is linked by the hnext pointers*/
    for (ntemp= hash_nlist[hashcode(name)]; ntemp != 0; ntemp = ntemp->hnext) {
      if (eq(name,ntemp->name)) return(ntemp);  // if node is found 
    }
    return(NULL);
}/* end of nfind */


/* wfind checks the existence of a wire
 * return the wire pointer if it exists; otherwise return a NULL pointer
 */
wptr
wfind(name)
char *name;
{
    wptr wtemp;

    for (wtemp= hash_wlist[hashcode(name)]; wtemp != 0; wtemp = wtemp->hnext) {
        if (eq(name,wtemp->name)) return(wtemp);
    }
    return(NULL);
}/* end of wfind */


/* get wire structure and return the wire pointer */
wptr
getwire(wirename)
char *wirename;
{
    wptr w;
    char *name;
    int hash_no;
    char *malloc();

    if (w = wfind(wirename)) { return(w); }

    /* allocate new wire from free storage */
    if (!(w = ALLOC(1,struct WIRE))) { error("No more room!"); }
    ncktwire++;

    /* initialize wire entries */

    hash_no = hashcode(wirename);
    w->hnext = hash_wlist[hash_no];
    hash_wlist[hash_no] = w;
    w->pnext = NULL;
    w->name = name = malloc(strlen(wirename) + 1);
    while (*name++ = *wirename++);
    return(w);
}/* end of getwire */


/* get node structure and return the node pointer */
nptr getnode(nodename)
char *nodename;
{
    nptr n;
    char *name;
    int hash_no;
    char *malloc();
  
    if (n = nfind(nodename)) error("node defined twice");
  
    /* allocate new node from free storage */
    if (!(n = ALLOC(1,struct NODE))) error("No more room!");

    /* initialize node entries */

    hash_no = hashcode(nodename);
    n->hnext = hash_nlist[hash_no];
    hash_nlist[hash_no] = n;
    n->pnext = NULL;
    n->name = name = malloc(strlen(nodename) + 1);
    while (*name++ = *nodename++);
    return(n);
}/* end of getnode */

      
/* new gate */
newgate()
{
    nptr n;
    wptr w;
    int i;
    int iwire_index = 0;

    if ((targc < 5) || !(eq(targv[targc - 2],";")))
                error("Bad Gate Record");
    n = getnode(targv[0]);
    ncktnode++;
    n->type = FindType(targv[1]);
    n->nin = targc - 4;
    if (!(n->iwire = ALLOC(n->nin,wptr))) error("No More Room!");
    i = 2;
    /* connect the iwire and owire */
    while (i < targc) {
        if (eq(targv[i],";")) break;
        w = getwire(targv[i]); 
        n->iwire[iwire_index] = w;
        w->nout++;
        iwire_index++;
        i++;
    }
    if (i == 2 || ((i + 2) != targc)) error("Bad Gate Record");
    i++;
    w = getwire(targv[i]); 
    n->nout = 1;
    if (!(n->owire = ALLOC(1,wptr))) error("No More Room!");
    *n->owire = w;
    w->nin++;
    return;
}/* end of newgate */

/* each PO is treated like a wire */
/* dummy PO gate will be added later, see init_flist.c */
set_output()
{
    wptr w;
    int i,j;
        void exit();

    for (i = 1; i < targc; i++) {
        w = getwire(targv[i]);
        for (j = 0; j < ncktout; j++) {
            if (w == temp_cktout[j]) {
                fprintf(stderr,"net %s is declared again as output around line %d\n",w->name,lineno);
                exit(-1);
            }
        }
        temp_cktout[ncktout] = w;
        ncktout++;
    }
    return;
}/* end of set_output */
      
/* each PI is treated like a wire */
/* dummy PI gate will be added later, see init_flist.c */
set_input(pori)
int pori;
{
    wptr w;
    int i,j;
        void exit();

    for (i = 1; i < targc; i++) {
         w = getwire(targv[i]);
         for (j = 0; j < ncktin; j++) {
             if (w == temp_cktin[j]) {
                 fprintf(stderr,"net %s is declared again as input around line %d\n",w->name,lineno);
                exit(-1);
            }
        }
        temp_cktin[ncktin] = w;
        if (pori == 1) {
            temp_cktin[ncktin]->flag |= PSTATE;
        }
        ncktin++;
    }
    return;
}/* end of set_input */
      

/* parse input line into tokens, filling up targv and setting targc */
parse_line(line)
char *line;
{
    char **carg = targv;
    char ch;

    targc = 0;
    while (ch = *line++) {
        if (ch <= ' ') continue;
        targc++;
        *carg++ = line-1;
        while ((ch = *line) && ch > ' ') line++;
        if (ch) *line++ = '\0';
    }
    *carg = 0;
}/* end of parse_line */


void
input(infile)
char *infile;
{ 
    int i;
    char line[LSIZE];
    FILE *in;


    for (i = 0; i < HASHSIZE; i++) {
        hash_wlist[i] = NULL;
        hash_nlist[i] = NULL;
    }
    if (!(temp_cktin = ALLOC(NUM_OF_INPUT,wptr)))
                error("No More Room!");
    if (!(temp_cktout = ALLOC(NUM_OF_OUTPUT,wptr)))
                error("No More Room!");
    ncktin = 0;
    ncktout = 0;
    filename = infile;
    if ((in = fopen(infile,"r")) == NULL) {
        fprintf(stderr,"Cannot open input file %s\n",infile);
        exit(-1);
    }
    while (1) {
        if (fgets(line,LSIZE,in) != line) break;
        lineno++;
        parse_line(line);
        if (targv[0] == NULL) continue;
        if (eq(targv[0],"name")) {
            if (targc != 2) error("Wrong Input Format!");
                        continue;
                }
        switch (targv[0][0]) {
            case '#':    break;

            case 'D': debug = 1 - debug; break;

            case 'g': newgate(); break;

            case 'i': set_input(0); break;

            case 'p': set_input(1); break;

            case 'o': set_output(); break;

            case 'n': set_output(); break;

            default:
                fprintf(stderr,"Unrecognized command around line %d in file %s\n",lineno,filename);
                 break;
        }
    }
    fclose(in);
    create_structure();
    fprintf(stdout,"\n");
    fprintf(stdout,"#Circuit Summary:\n");
    fprintf(stdout,"#---------------\n");
    fprintf(stdout,"#number of inputs = %d\n",ncktin);
    fprintf(stdout,"#number of outputs = %d\n",ncktout);
    fprintf(stdout,"#number of gates = %d\n",ncktnode);
    fprintf(stdout,"#number of wires = %d\n",ncktwire);
    if (debug) display_circuit();
}/* end of input */


/* when we create a new gate, its iwire and owire are connect.
   but the inode and onode of each wire are not connected yet.
   this function connects the inode and onode for each wire in the whole ckt.  */
create_structure()
{
    wptr w;
    nptr n;
    int i, j, k;

    if (!(cktin = ALLOC(ncktin,wptr))) error("No More Room!"); // array of PI 
    if (!(cktout = ALLOC(ncktout,wptr))) error("No More Room!"); // array of PO 
    
    for (i = 0; i < ncktin; i++) {
        cktin[i] = temp_cktin[i];
        cktin[i]->flag |= INPUT;
    }
    cfree(temp_cktin);

    for (i = 0; i < ncktout; i++) {
        cktout[i] = temp_cktout[i];
        cktout[i]->flag |= OUTPUT;
    }
    cfree(temp_cktout);

    /* foreach wire, create inode array and onode array*/
    for (i = 0; i < HASHSIZE; i++) {
        for (w = hash_wlist[i]; w; w = w->hnext) {
                        if (w->nin > 0)
                    if (!(w->inode = ALLOC(w->nin,nptr)))
                                        error("No More Room!");
                        if (w->nout > 0)
                    if (!(w->onode = ALLOC(w->nout,nptr)))
                                        error("No More Room!");
        }
    } // for i

    /*walk through every node in the circuit  */
    for (i = 0; i < HASHSIZE; i++) {
      for (n = hash_nlist[i]; n; n = n->hnext) { // for each node n in the circuit

	for (j = 0; j < n->nin; j++) {  //insert node n into the onode of its iwires
	  for (k = 0; n->iwire[j]->onode[k]; k++);
	  n->iwire[j]->onode[k] = n;
	}

	for (j = 0; j < n->nout; j++) { //insert node n into the inode of its owires  
	  for (k = 0; n->owire[j]->inode[k]; k++);
	  n->owire[j]->inode[k] = n;
	} // for j
      }// for n
    } // for i
    return;
}/* end of create_structure */


FindType(gatetype)
char *gatetype;
{
    if (!(strcmp(gatetype,"and"))) return(AND);
    if (!(strcmp(gatetype,"AND"))) return(AND);
    if (!(strcmp(gatetype,"nand"))) return(NAND);
    if (!(strcmp(gatetype,"NAND"))) return(NAND);
    if (!(strcmp(gatetype,"or"))) return(OR);
    if (!(strcmp(gatetype,"OR"))) return(OR);
    if (!(strcmp(gatetype,"nor"))) return(NOR);
    if (!(strcmp(gatetype,"NOR"))) return(NOR);
    if (!(strcmp(gatetype,"not"))) {
        if (targc != 5) error("Bad Gate Record");
        return(NOT);
    }
    if (!(strcmp(gatetype,"NOT"))) {
        if (targc != 5) error("Bad Gate Record");
        return(NOT);
    }
    if (!(strcmp(gatetype,"buf"))) {
        if (targc != 5) error("Bad Gate Record");
        return(BUF);
    }
    if (!(strcmp(gatetype,"xor"))) {
        if (targc != 6) error("Bad Gate Record");
        return(XOR);
    }
    if (!(strcmp(gatetype,"eqv"))) {
        if (targc != 6) error("Bad Gate Record");
        return(EQV);
    }
    error("unreconizable gate type");
}/* end of FindType */


/*
* print error message and die
*/
error(message)
char *message;
{
    fprintf(stderr,"%s around line %d in file %s\n",message,lineno,filename);
    exit(0);
}/* end of error */


/*
* get the elapsed cputime
* (call it the first time with message "START")
*/ 
struct tbuffer {
    long utime;
    long stime;
    long cutime;
    long cstime;
} Buffer;

double StartTime, LastTime;

timer(file,mesg1,mesg2)
FILE *file;
char *mesg1,*mesg2;
{
    long junk;
    if(strcmp(mesg1,"START") == 0) {
        junk = times(&Buffer);
        StartTime = (double)(Buffer.utime);
        LastTime = StartTime;
        return;
    }
    junk = times(&Buffer);
    fprintf(file,"#atpg: cputime %s %s: %.1fs %.1fs\n", mesg1,mesg2,
         (Buffer.utime-LastTime)/60.0, (Buffer.utime-StartTime)/60.0);
    LastTime = Buffer.utime;
    return;
}/* end of timer */


/* this function is acitve only when the debug variable (input.c) is turned on */
display_circuit()
{
    register nptr n;
    register wptr w;
    register int i,j;

    fprintf(stdout,"\n");
    for (i = 0; i < HASHSIZE; i++) {
          for (n = hash_nlist[i]; n; n = n->hnext) {
             fprintf(stdout,"%s ",n->name);
             switch(n->type) {
                case AND :
                   fprintf(stdout,"and ");
                   break;
                case NAND :
                   fprintf(stdout,"nand ");
                   break;
                case OR :
                   fprintf(stdout,"or ");
                   break;
                case NOR :
                   fprintf(stdout,"nor ");
                   break;
                case BUF :
                   fprintf(stdout,"buf ");
                   break;
                case NOT :
                   fprintf(stdout,"not ");
                   break;
                case XOR :
                   fprintf(stdout,"xor ");
                   break;
                case EQV :
                   fprintf(stdout,"eqv ");
                   break;
            }
            for (j = 0; j < n->nin; j++) {
                fprintf(stdout,"%s ",n->iwire[j]->name);
            }
            fprintf(stdout,"; ");
            for (j = 0; j < n->nout; j++) {
                fprintf(stdout,"%s\n",n->owire[j]->name);
            }
        }
    }
    fprintf(stdout,"i ");
    for (i = 0 ; i < ncktin; i++) {
          fprintf(stdout,"%s ",cktin[i]->name);
      }
    fprintf(stdout,"\n");
    fprintf(stdout,"o ");
    for (i = 0 ; i < ncktout; i++) {
          fprintf(stdout,"%s ",cktout[i]->name);
      }
    fprintf(stdout,"\n");

    fprintf(stdout,"\n");
    for (i = 0; i < HASHSIZE; i++) {
          for (w = hash_wlist[i]; w; w = w->hnext) {
            fprintf(stdout,"%s ",w->name);
            for (j = 0; j < w->nin; j++) {
                fprintf(stdout,"%s ",w->inode[j]->name);
             }
            fprintf(stdout,";");
            for (j = 0; j < w->nout; j++) {
                fprintf(stdout,"%s ",w->onode[j]->name);
             }
            fprintf(stdout,"\n");
          }
    }
    return;
} /* end of display_circuit */
