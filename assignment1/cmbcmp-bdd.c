/* Combinational Comparison with BDDs */

/*	This program takes the names of two files from the command line.
	The files should describe circuits in ISCAS 85 format.
	The program will then print either that the two circuits are
	functionally equivalent (same input names in the same order,
	same output names in the same order, and outputs have same
	logical functionality), or else the program will give a specific
	input vector that proves the two circuits different.
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "cudd.h"

#define MAXLINE 256	/* Maximum length of each input line read. */

/* Definitions of wire types, used in type field of wire structure. */
#define	INPUT	0	/* Primary input */
#define	AND	1
#define	NAND	2
#define	OR	3
#define NOR	4
#define XOR	5
#define XNOR	6	/* Are inputs equal? */
#define BUFF	7	/* Non-inverting buffer:  output = input */
#define NOT	8
#define FROM	9	/* Fanout branch:  output = input */

struct wire_	{
			char	*name;		/* Name of this wire. */
			int	type;	/* Type of gate driving this wire. */
			int	fanincount;	/* Number of fanins. */
			int	*fanins;	/* Array of fanin indices. */
			DdNode	*bdd;		/* BDD for this wire */
		};
typedef struct wire_ *wire;

struct circuit_	{
			char	*name;		/* Name of the circuit. */
			int	wirecount;	/* Number of wire indices. */
			wire	*wires;		/* Array of all wires */
			int	inputcount;	/* Number of primary inputs. */
			int	*inputs;	/* Array of input indices. */
			int	outputcount;	/* Number of primary outputs. */
			int	*outputs;	/* Array of output indices. */
		};
typedef struct circuit_ *circuit;

DdManager *gbm;	/* Global BDD manager. */

int translate_wiretype(char *typename)
	/* Helper function for parse_iscas85(). */
	/* Returns the wire type constant for the given string. */
{
    if (strncmp("inpt",typename,4)==0) return INPUT;
    if (strncmp("and",typename,4)==0) return AND;
    if (strncmp("nand",typename,4)==0) return NAND;
    if (strncmp("or",typename,4)==0) return OR;
    if (strncmp("nor",typename,4)==0) return NOR;
    if (strncmp("xor",typename,4)==0) return XOR;
    if (strncmp("xnor",typename,4)==0) return XNOR;
    if (strncmp("buff",typename,4)==0) return BUFF;
    if (strncmp("not",typename,4)==0) return NOT;
    if (strncmp("from",typename,4)==0) return FROM;

    fprintf(stderr,"cmbcmp:  Illegal wire type \"%s\"\n",typename);
    exit(1);
}

int parse_iscas85(FILE *f, circuit c)
	/* Reads an ISCAS 85 circuit from stream f, building up circuit c. */
{
    int inputcount = 0;
    int outputcount = 0;
    int maxindex = -1;
    char linebuf[MAXLINE];
    int index, fanins, fanouts;
    char wirename[MAXLINE], wiretype[MAXLINE];
    int i;
    int fanindex;

    /* Make first pass to count primary inputs, primary outputs, and wires. */
    while (fgets(linebuf,MAXLINE,f) != NULL) {
	if (linebuf[0]=='*') continue;	/* Skip comment lines. */

	/* Pick out the relevant data from the line. */
	sscanf(linebuf,"%d %*s %*s %d %d",&index,&fanouts,&fanins);
	if (index>maxindex) maxindex = index;
	if (fanouts==0) outputcount++;	/* Only outputs have no fanout. */
	if (fanins==0) inputcount++;	/* Only inputs have no fanin. */
	if (fanins>0) fgets(linebuf,MAXLINE,f);	/* Discard fanin line. */
	if (fanouts>1) {
	    while (fanouts-- > 0)
		fgets(linebuf,MAXLINE,f);	/* Discard fanout lines. */
	}
    }

    /* Now that we know how big to make the arrays, allocate memory. */
    c->wirecount = maxindex+1;
    /* Allocate a contiguous array we can index for every wire. */
    c->wires = (wire *)malloc((maxindex+1)*sizeof(wire));
    bzero(c->wires,(maxindex+1)*sizeof(wire));	/* Clear out the space. */
    c->inputcount = inputcount;
    c->inputs = (int *)malloc(inputcount*sizeof(int));
    c->outputcount = outputcount;
    c->outputs = (int *)malloc(outputcount*sizeof(int));

    /* Second pass actually reads the circuit. */
    rewind(f);
    inputcount = 0;
    outputcount = 0;
    while (fgets(linebuf,MAXLINE,f) != NULL) {
	if (linebuf[0]=='*') continue;	/* Skip comment lines. */

	/* Pick out the relevant data from the line. */
	sscanf(linebuf,"%d %s %s %d %d",&index,wirename,wiretype,&fanouts,&fanins);

	/* Create the new wire. */
	c->wires[index] = (wire)malloc(sizeof(struct wire_));
	c->wires[index]->name = strdup(wirename);
	c->wires[index]->type = translate_wiretype(wiretype);
	c->wires[index]->fanincount = fanins;
	c->wires[index]->fanins = (int *)malloc(sizeof(int)*fanins);
	c->wires[index]->bdd = NULL;

	/* If it's a primary input or primary output, record that fact. */
	if (fanins==0) c->inputs[inputcount++] = index; /* primary input. */
	if (fanouts==0) c->outputs[outputcount++] = index; /* primary output. */

	/* Read the fanins. */
	if (fanins>0) {
	    for (i=0; i<fanins; i++) {
		fscanf(f,"%d",&(c->wires[index]->fanins[i]));
	    }
	    fgets(linebuf,MAXLINE,f);	/* Discard rest of line. */
	}

	/* Read the fanout lines if fanouts>1. */
	if (fanouts>1) {
	    for (i=0; i<fanouts; i++) {
		/* This is annoying.  I need to create additional wires for
		   each fanout because of the way the input format works. */
		fscanf(f,"%d %s",&fanindex,wirename);
		/* Create the fanout branch wire. */
		c->wires[fanindex] = (wire)malloc(sizeof(struct wire_));
		c->wires[fanindex]->name = strdup(wirename);
		c->wires[fanindex]->type = FROM;
		c->wires[fanindex]->fanincount = 1;
		c->wires[fanindex]->fanins = (int *)malloc(sizeof(int));
		c->wires[fanindex]->fanins[0] = index;
		c->wires[fanindex]->bdd = NULL;
		fgets(linebuf,MAXLINE,f);	/* Discard rest of line. */
	    }
	}
    }

    return 1;	/* Didn't bother to do any error checking. */
}

circuit read_iscas85_file(char *filename)
	/* This routine reads in an ISCAS 85 format circuit from the file. */
{
    FILE *f;
    circuit c;
	
    f = fopen(filename,"r");
    if (!f) {
	fprintf(stderr,"cmbcmp:  cannot open file \"%s\"\n",filename);
	return NULL;
    }

    c = (circuit)malloc(sizeof(*c));
    if (!c) {
	fprintf(stderr,"cmbcmp:  cannot allocate memory\n");
	return NULL;
    }

    c->name = filename;

    /* Parse the circuit into c, returning NULL if error. */
    if (!parse_iscas85(f,c)) {
	fprintf(stderr,"cmbcmp:  error reading circuit in file \"%s\"\n",filename);
	free((void *)c);
	return NULL;
    }

    fclose(f);

    return c;
}

void build_bdd_for_wire(wire w, circuit c)
	/* Builds the BDD for w recursively from primary inputs. */
{
    int i;
    DdNode *temp1, *temp2;

    if (w->bdd != NULL) return;	/* BDD already built. */

    /* Build BDD for each fanin. */
    for (i=0; i < w->fanincount; i++) {
	build_bdd_for_wire(c->wires[w->fanins[i]],c);
    }

    switch (w->type) {
	case INPUT:
	    fprintf(stderr,"Error:  Uninitialized primary input.\n");
	    break;
	case AND:
	    temp1 = Cudd_ReadOne(gbm);
	    Cudd_Ref(temp1);
	    for (i=0; i < w->fanincount; i++) {
		temp2 = Cudd_bddAnd(gbm,temp1,c->wires[w->fanins[i]]->bdd);
		Cudd_Ref(temp2);
		Cudd_RecursiveDeref(gbm,temp1);
		temp1 = temp2;
	    }
	    w->bdd = temp1;
	    break;
	case NAND:
	    temp1 = Cudd_ReadOne(gbm);
	    Cudd_Ref(temp1);
	    for (i=0; i < w->fanincount; i++) {
		temp2 = Cudd_bddAnd(gbm,temp1,c->wires[w->fanins[i]]->bdd);
		Cudd_Ref(temp2);
		Cudd_RecursiveDeref(gbm,temp1);
		temp1 = temp2;
	    }
	    w->bdd = Cudd_Not(temp1);
	    Cudd_Ref(w->bdd);
	    Cudd_RecursiveDeref(gbm,temp1);
	    break;
	case OR:
	    /* FIX THIS!!! */
	    /* YOUR CODE GOES HERE. */
        temp1 = Cudd_ReadLogicZero(gbm);
	    Cudd_Ref(temp1);
	    for (i=0; i < w->fanincount; i++) {
		temp2 = Cudd_bddOr(gbm,temp1,c->wires[w->fanins[i]]->bdd);
		Cudd_Ref(temp2);
		Cudd_RecursiveDeref(gbm,temp1);
		temp1 = temp2;
	    }
	    w->bdd = temp1;
	    break;
	case NOR:
	    /* FIX THIS!!! */
	    /* YOUR CODE GOES HERE. */
        temp1 = Cudd_ReadLogicZero(gbm);
	    Cudd_Ref(temp1);
	    for (i=0; i < w->fanincount; i++) {
		temp2 = Cudd_bddOr(gbm,temp1,c->wires[w->fanins[i]]->bdd);
		Cudd_Ref(temp2);
		Cudd_RecursiveDeref(gbm,temp1);
		temp1 = temp2;
	    }
	    w->bdd = Cudd_Not(temp1);
	    Cudd_Ref(w->bdd);
	    Cudd_RecursiveDeref(gbm,temp1);
	    break;
	case XOR:
	    w->bdd = Cudd_bddXor(gbm,c->wires[w->fanins[0]]->bdd,c->wires[w->fanins[1]]->bdd);
	    Cudd_Ref(w->bdd);
	    break;
	case XNOR:
	    w->bdd = Cudd_bddXnor(gbm,c->wires[w->fanins[0]]->bdd,c->wires[w->fanins[1]]->bdd);
	    Cudd_Ref(w->bdd);
	    break;
	case BUFF:
	    w->bdd = c->wires[w->fanins[0]]->bdd;
	    Cudd_Ref(w->bdd);
	    break;
	case NOT:
	    /* FIX THIS!!! */
	    /* YOUR CODE GOES HERE. */
        w->bdd = Cudd_Not(c->wires[w->fanins[0]]->bdd);
	    Cudd_Ref(w->bdd);
	    break;
	case FROM:
	    w->bdd = c->wires[w->fanins[0]]->bdd;
	    Cudd_Ref(w->bdd);
	    break;
	default:
	    fprintf(stderr,"Error:  Illegal wire type.\n");
	    exit(1);
    }
}

void print_bdd_name(DdNode *v, circuit c)
	/* Prints the name of BDD variable v in circuit c. */
{
    int i;

    for (i=0; i < c->inputcount; i++) {
	if (v == c->wires[c->inputs[i]]->bdd) {
	    printf("%s",c->wires[c->inputs[i]]->name);
	    break;
	}
    }
}

DdNode *Cudd_Else(DdNode *foo)
{
	if (Cudd_IsComplement(foo)) {
		return Cudd_Not(Cudd_E(foo));
	} else {
		return Cudd_E(foo);
	}
}

DdNode *Cudd_Then(DdNode *foo)
{
	if (Cudd_IsComplement(foo)) {
		return Cudd_Not(Cudd_T(foo));
	} else {
		return Cudd_T(foo);
	}
}

void print_violating_assignment(DdNode *x, DdNode *y, circuit c)
	/* Prints a vector that makes x!=y.  Circuit c is needed to
	   give names to variables. */
{
    DdNode *diff;
    DdNode *foo, *temp, *v;

    diff = Cudd_bddXor(gbm,x,y);
    Cudd_Ref(diff);

    if (diff==Cudd_ReadLogicZero(gbm)) {
	fprintf(stderr,"Error:  print_violating_assignment called with equal BDDs.\n");
	return;
    }


    foo = diff;
    while (foo!=Cudd_ReadOne(gbm)) {
	printf("\t");

	v = Cudd_ReadVars(gbm,Cudd_NodeReadIndex(foo));
	print_bdd_name(v,c);	/* Print the name for that input. */

	temp = Cudd_Else(foo);
	if (temp==Cudd_ReadLogicZero(gbm)) {
	    /* FIX THIS!!! */
	    printf(" = 1\n");
	    temp = Cudd_Then(foo);
	} else {
	    /* FIX THIS!!! */
	    printf(" = 0\n");
	}

	foo = temp;
    }
    printf("\t(All other variables are irrelevant.)\n");

    Cudd_RecursiveDeref(gbm,diff);
}

int main(int argc, char *argv[])
{
    circuit circuit1, circuit2;
    int i;

    /* Make sure program invoked with two arguments. */
    if (argc !=3) {
	fprintf(stderr,"cmbcmp:  usage:  cmbcmp file1 file2\n");
	exit(1);
    }

    circuit1 = read_iscas85_file(argv[1]);
    if (!circuit1) exit(1);
    circuit2 = read_iscas85_file(argv[2]);
    if (!circuit2) exit(1);

    /* Check that the two circuits have the same inputs. */
    if (circuit1->inputcount != circuit2->inputcount) {
	printf("Circuits have different number of inputs:\n");
	printf("\tCircuit \"%s\" has %d inputs.\n",
				circuit1->name,circuit1->inputcount);
	printf("\tCircuit \"%s\" has %d inputs.\n",
				circuit2->name,circuit2->inputcount);
	exit(0);
    }
    for (i=0; i < circuit1->inputcount; i++) {
	/* Make sure all the names agree. */
	if (strcmp(circuit1->wires[circuit1->inputs[i]]->name,
		   circuit2->wires[circuit2->inputs[i]]->name)!=0) {
	    printf("Primary input %d differs between circuits:\n",i);
	    printf("\tIn circuit \"%s\", input %d is named \"%s\".\n",
		circuit1->name,i,circuit1->wires[circuit1->inputs[i]]->name);
	    printf("\tIn circuit \"%s\", input %d is named \"%s\".\n",
		circuit2->name,i,circuit2->wires[circuit2->inputs[i]]->name);
	    exit(0);
	}
    }

    /* Check that the two circuits have the same outputs. */
    if (circuit1->outputcount != circuit2->outputcount) {
	printf("Circuits have different number of outputs:\n");
	printf("\tCircuit \"%s\" has %d outputs.\n",
				circuit1->name,circuit1->outputcount);
	printf("\tCircuit \"%s\" has %d outputs.\n",
				circuit2->name,circuit2->outputcount);
	exit(0);
    }
    for (i=0; i < circuit1->outputcount; i++) {
	/* Make sure all the names agree. */
	if (strcmp(circuit1->wires[circuit1->outputs[i]]->name,
		   circuit2->wires[circuit2->outputs[i]]->name)!=0) {
	    printf("Primary output %d differs between circuits:\n",i);
	    printf("\tIn circuit \"%s\", output %d is named \"%s\".\n",
		circuit1->name,i,circuit1->wires[circuit1->outputs[i]]->name);
	    printf("\tIn circuit \"%s\", output %d is named \"%s\".\n",
		circuit2->name,i,circuit2->wires[circuit2->outputs[i]]->name);
	    exit(0);
	}
    }

    /* OK, at this point, we know the two circuits have corresponding
	inputs and outputs.  Your mission is compare the logical functionality
	of the two circuits.  Good luck! */

    /* Initialize a new BDD manager. */
    gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);

    /* Create BDD variables for the inputs. */
    for (i=0; i < circuit1->inputcount; i++) {
	circuit1->wires[circuit1->inputs[i]]->bdd =
		Cudd_bddNewVar(gbm);
	circuit2->wires[circuit2->inputs[i]]->bdd =
		circuit1->wires[circuit1->inputs[i]]->bdd;
	Cudd_Ref(circuit1->wires[circuit1->inputs[i]]->bdd);
    }

    /* Check BDD for each primary output. */
    for (i=0; i < circuit1->outputcount; i++) {
	build_bdd_for_wire(circuit1->wires[circuit1->outputs[i]], circuit1);
	build_bdd_for_wire(circuit2->wires[circuit2->outputs[i]], circuit2);
	if (circuit1->wires[circuit1->outputs[i]]->bdd !=
		circuit2->wires[circuit2->outputs[i]]->bdd) {
	    /* This output is different! */
	    printf("Output %d \"%s\" differs for input vector:\n",
			i,circuit1->wires[circuit1->outputs[i]]->name);
	    print_violating_assignment(
			circuit1->wires[circuit1->outputs[i]]->bdd,
			circuit2->wires[circuit2->outputs[i]]->bdd,
			circuit1);
	    exit(0);
	}

	/* Primary outputs have no fanouts, so I can free these BDDs. */
	Cudd_RecursiveDeref(gbm,circuit1->wires[circuit1->outputs[i]]->bdd);
	circuit1->wires[circuit1->outputs[i]]->bdd = NULL;
	Cudd_RecursiveDeref(gbm,circuit2->wires[circuit2->outputs[i]]->bdd);
	circuit2->wires[circuit2->outputs[i]]->bdd = NULL;
    }

    printf("Circuits are functionally equivalent.\n");

    return 0;
}
