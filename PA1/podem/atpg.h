/**********************************************************************/
/*           automatic test pattern generation                        */
/*           global data structures header file                       */
/*                                                                    */
/*           Author: Tony Hi Keung Ma                                 */
/*           last update : 09/28/1987                                 */
/**********************************************************************/


typedef struct WIRE *wptr;
typedef struct NODE *nptr;

struct WIRE {
    char *name;            /* asciz name of wire */
    nptr *inode;           /* nodes driving this wire */
    nptr *onode;           /* nodes driven by this wire */
    short nin;             /* number of input nodes */
    short nout;            /* number of output nodes */
    int value;             /* logic value [0|1|2] of the wire, fault-free sim */
    int flag;              /* flag word */
    wptr pnext;            /* general usage link */
    wptr hnext;            /* hash bucket link */
    int level;             /* level of the wire */
    short *pi_reach;       /* array of no. of paths reachable from each pi, for podem */

    int wire_value1;       /* (32 bits) represents fault-free value for this wire. 
			      the same [00|11|01] replicated by 16 times (for pfedfs) */
    int wire_value2;       /* (32 bits) represents values of this wire 
			      in the presence of 16 faults. (for pfedfs) */

    int fault_flag;        /* indicates the fault-injected bit position, for pfedfs */
    int wlist_index;       /* index into the sorted_wlist array */
};

// a node is a gate
struct NODE {
    char *name;            /* ascii name of node */
    wptr *iwire;           /* wires driving this node */
    wptr *owire;           /* wires driven by this node */
    short nin;             /* number of input wires */
    short nout;            /* number of output wires */
    int type;              /* node type */
    int flag;              /* flag word */
    nptr pnext;            /* general usage link */
    nptr hnext;            /* hash bucket link */
};

#define HASHSIZE 3911

/* types of gate */
#define NOT       1
#define NAND      2
#define AND       3
#define INPUT     4
#define NOR       5
#define OR        6
#define OUTPUT    8
#define XOR      11
#define BUF      17
#define EQV	      0	/* XNOR gate */
#define SCVCC    20

/* possible value for wire flag */
#define SCHEDULED       1
#define ALL_ASSIGNED    2
/*#define INPUT         4*/
/*#define OUTPUT        8*/
#define MARKED         16
#define FAULT_INJECTED 32
#define FAULTY         64
#define CHANGED       128
#define FICTITIOUS    256
#define PSTATE       1024
