/**CFile**********************************************************************

  FileName    [testdddmp.c]

  PackageName [dddmp]

  Synopsis    [A simple test function for Dddmp package]

  Description []

  Author      [Gianpiero Cabodi & Stefano Quer]

  Copyright   [Politecnico di Torino(Italy)]

******************************************************************************/

#include <string.h>
#include <stdio.h>
#include "dddmpInt.h"


/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define DDDMPTEST_MAX_FILENAME_LENGTH 256
#define DDDMPTEST_MAX_STRING_LENGTH 80
#define DDDMPTEST_MAX_OPERAND 20
#define DDDMP_NVARS_DEFAULT 50

#if !defined(RAND_MAX) && defined(sun) && defined(sparc)
#define RAND_MAX 2147483647
#endif

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void OneCreate(DdManager *dd, DdNode **operand);
static void ZeroCreate(DdManager *dd, DdNode **operand);
static void LeafCreate(DdManager *dd, DdNode **operand);
static void BddCreate(DdManager *dd, DdNode **operand);
static void A2B(void);
static void B2A(void);
static void HeaderRead(void);
static void Help(void);
static void OrderNamesLoad(int nddvars);
static int * IntArrayLoad(int nddvars);
static void BddLoad(DdManager *dd, DdNode **operand);
static void Operation(DdManager *dd, DdNode **operand);
static void BddStore(DdManager *dd, DdNode **operand);
static void DynamicReordering(DdManager *dd);
static void SetLoadMatchmode();

/**AutomaticEnd***************************************************************/

char ** varmatchnames=NULL;  /* array of variable names (accessed by ids) */
int * varmatchauxids=NULL;   /* array of variable auxids (accessed by ids) */
int * varcomposeids=NULL;    /* array of new ids (accessed by ids) */
Dddmp_VarMatchType varmatchmode;
Dddmp_VarInfoType varoutinfo;
char varname[DDDMPTEST_MAX_STRING_LENGTH];
char * row;

int
main(
  int argc,
  char **argv
)
{
  DdManager *dd;
  int i;
  DdNode **operand;

  /* ------------------ Echo command line and arguments ---------------- */
  fprintf (stdout, "#");
  for (i=0; i<argc; i++)
    fprintf (stdout, " %s", argv[i]);
  fprintf (stdout, "\n");
  if (argc>1) {
    Help();
  }

  /* ---------------------- CUDD inizialization ------------------------ */

  dd = Cudd_Init (DDDMP_NVARS_DEFAULT, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0); 
  if (dd==NULL) {
    fprintf (stderr, "Dddmp Test Error : DdManager is not inizializated\n");
    return (0);
  }

  varmatchmode = DDDMP_VAR_MATCHIDS;
  varoutinfo = DDDMP_VARIDS;

  /* ------------------- Manage command line parameters ----------------- */

  row = (char*) malloc (DDDMPTEST_MAX_STRING_LENGTH * sizeof(char));
  operand = (DdNode **) malloc (DDDMPTEST_MAX_OPERAND * sizeof (DdNode *));
  if (row==NULL || operand==NULL) {
    fprintf (stderr, "Allocation error!\n");
    return (0);
  }
  for (i=0; i<DDDMPTEST_MAX_OPERAND; i++)
     operand[i] = NULL;

  while (1) {
    fprintf (stdout, "TestDddmp> ");
    fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
    if (row[0]=='\n') {
      continue;
    }
    if (strncmp(row, "help", 4)==0) {
      Help();
    } else if (strncmp(row, "onl", 3)==0) {
        OrderNamesLoad (Cudd_ReadSize(dd));
    } else if (strncmp(row, "oil", 3)==0) {
        varmatchauxids=IntArrayLoad(Cudd_ReadSize(dd));
    } else if (strncmp(row, "cil", 3)==0) {
        varcomposeids=IntArrayLoad(Cudd_ReadSize(dd));
    } else if (strncmp(row, "slm", 3)==0) {
        SetLoadMatchmode ();
    } else if (strncmp(row, "bl", 2)==0) {
        BddLoad (dd, operand);
    } else if (strncmp(row, "op", 2)==0) {
        Operation (dd, operand);
    } else if (strncmp(row, "oc", 2)==0) {
        OneCreate (dd, operand);
    } else if (strncmp(row, "zc", 2)==0) {
        ZeroCreate (dd, operand);
    } else if (strncmp(row, "lc", 2)==0) {
        LeafCreate (dd, operand);
    } else if (strncmp(row, "bc", 2)==0) {
        BddCreate (dd, operand);
    } else if (strncmp(row, "a2b", 3)==0) {
        A2B ();
    } else if (strncmp(row, "b2a", 3)==0) {
        B2A ();
    } else if (strncmp(row, "hr", 2)==0) {
        HeaderRead ();
    } else if (strncmp(row, "bs", 2)==0) {
        BddStore (dd, operand);
    } else if (strncmp(row, "dr", 2)==0) {
        DynamicReordering (dd);
    } else if (strncmp(row, "quit", 4)==0) {
        break;
    } else {
        fprintf (stderr, "Command not found: %s\n", row);
    }
  }

  fprintf (stdout, "End of test.\n");
  Cudd_Quit (dd);
  return (1);
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/
                                                                       
/**Function********************************************************************

Synopsis    [Create a One-BDD Leaf.]

Description [Create a One-BDD Leaf.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
OneCreate(
  DdManager *dd,
  DdNode **operand   /* array of operand */
)
{
  int i;

  fprintf (stdout, "Which BDDs [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &i);

  operand[i] = Cudd_ReadOne(dd);

  return;
}

/**Function********************************************************************

Synopsis    [Create a Zero-BDD Leaf.]

Description [Create a Zero-BDD Leaf.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
ZeroCreate(
  DdManager *dd,
  DdNode **operand   /* array of operand */
)
{
  int i;
  DdNode *one;

  fprintf (stdout, "Which BDDs [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &i);

  one = Cudd_ReadOne(dd);
  operand[i] = Cudd_Not(one);

  return;
}

/**Function********************************************************************

Synopsis    [Create a One-Node BDD.]

Description [Create a One-Node BDD.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
LeafCreate(
  DdManager *dd,
  DdNode **operand   /* array of operand */
)
{
  int i, j;
  DdNode *f;

  fprintf (stdout, "Which BDDs [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &i);
  fprintf (stdout, "Index: ");
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &j);

  f = Cudd_bddIthVar (dd, j);
  Cudd_Ref(f);
  operand[i] = f;

  return;
}

/**Function********************************************************************

Synopsis    [Create a BDD.]

Description [Create a BDD: Variable index and number of cubes selection.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
BddCreate(
  DdManager *dd,
  DdNode **operand   /* array of operand */
)
{
  int nb, nv, vi0, vi1, nc, i, j;
  DdNode **vet, *f, *g, *h;

  fprintf (stdout, "Which BDDs [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &nb);
  fprintf (stdout, "Variables Index [n-m] (m-n = number of variables): ");
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d-%d", &vi0, &vi1);
  nv = vi1-vi0+1;
  fprintf (stdout, "How many cubes [1..]: ");
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &nc);

  /* Leaf Creation */
  vet = (DdNode **) malloc (nv * sizeof (DdNode *));
  for (i=0; i<nv; i++)
     vet[i] = Cudd_bddIthVar (dd, vi0+i);

  /* Cubes and BDD creation */
  f = Cudd_Not (Cudd_ReadOne(dd));
  for (i=0; i<nc; i++)
    {
    g = Cudd_ReadOne (dd);
    for (j=0; j<nv; j++)
      {
      if ( ((float) rand())/((float) RAND_MAX) > 0.5 ) {
        h = Cudd_bddAnd (dd, g, vet[j]);
      } else {
        h = Cudd_bddAnd (dd, g, Cudd_Not (vet[j]));
      }
      Cudd_Ref (h);
      Cudd_RecursiveDeref (dd, g);
      g = h;
      }
    h = Cudd_bddOr (dd, f, g);
    Cudd_Ref (h);
    Cudd_RecursiveDeref (dd, f);
    Cudd_RecursiveDeref (dd, g);
    f = h;
    }
      
  operand[nb] = f;

  return;
}

/**Function********************************************************************

Synopsis    [Transform a BDD from the ASCII to the Binary format].]

Description [Input and Output file selection.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
A2B(
  void
)
{
  fprintf (stderr, "Not yet Implemented!!!\n");

  return;
}

/**Function********************************************************************

Synopsis    [Transform a BDD from the Binary to the ASCII format].]

Description [Input and Output file selection.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
B2A(
  void
)
{
  fprintf (stderr, "Not yet Implemented!!!\n");

  return;
}

/**Function********************************************************************

Synopsis    [Read the Header of a filke containing a BDD.]

Description [File name Selection.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
HeaderRead(
  void
)
{
  fprintf (stderr, "Not yet Implemented!!!\n");

  return;
}

/**Function********************************************************************

Synopsis    [Print the Help messages.] 

Description [Print the Help messages.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
Help(
  void
)
{
  fprintf (stdout, "Commands:\n");
  fprintf (stdout, "\thelp : Print this set of messages.\n");
  fprintf (stdout, "\tonl  : Load the order from a file (varnames).\n");
  fprintf (stdout, "\toil  : Load the order from a file (varauxids).\n");
  fprintf (stdout, "\tcil  : Load compose IDs from a file.\n");
  fprintf (stdout, "\tslm  : Set Load matchmode for variables.\n");
  fprintf (stdout, "\tbl   : Load a BDD from a file.\n");
  fprintf (stdout,
    "\top   : Operation (or, and, xor, not, =) between BDDs.\n");
  fprintf (stdout, "\toc   : Create a terminal-one BDD.\n");
  fprintf (stdout, "\tzc   : Create a terminal-zero BDD.\n");
  fprintf (stdout, "\tlc   : Create a single variable BDD (1 node).\n");
  fprintf (stdout, "\tbc   : Create a random BDD.\n");
  fprintf (stdout,
    "\ta2b  : Convert a file from the ASCII format to the binary one.\n");
  fprintf (stdout, "\t       (Not Yet Implemented)\n");
  fprintf (stdout,
    "\tb2a  : Convert a file from the binary format to the ASCII one.\n");
  fprintf (stdout, "\t       (Not Yet Implemented)\n");
  fprintf (stdout, "\thr   : Read the header from a file.\n");
  fprintf (stdout, "\t       (Not Yet Implemented)\n");
  fprintf (stdout, "\tbs   : Store a BDD into a file.\n");
  fprintf (stdout, "\tdr   : Activate Dynamic Reordering.\n");
  fprintf (stdout, "\tquit : Quit the test program.\n");
  
  return;
}


/**Function********************************************************************

Synopsis    [Load the BDD order from a file (varnames).] 

Description [Load the BDD order from a file (varnames).]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
OrderNamesLoad(
  int nddvars
)
{
  /* ------------------- Read optional ord file ------------------------ */

  FILE *fp;
  char filename[DDDMPTEST_MAX_OPERAND];
  int i;
  char buf[DDDMPTEST_MAX_STRING_LENGTH];

  fprintf (stdout, "File : ");
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%s", filename);

  fp = fopen(filename, "r");
  if (fp == NULL) {
    fprintf (stdout, "Couldn't open %s\n", filename);
    return;
  }

  varoutinfo = DDDMP_VARNAMES;
  varmatchnames=DDDMP_ALLOC(char *, nddvars);
  if (varmatchnames==NULL) {
    fprintf (stdout, "Error allocating memory\n");
  } else {
    i=0;
    while (fgets(buf, DDDMPTEST_MAX_STRING_LENGTH, fp)!=NULL) {
      if (buf[0]=='#') {
        continue;
      }
      if (i>=nddvars) {
        fprintf (stdout, "Number of variables in files higher than DD manager vars (%d)\n",nddvars);
        fprintf (stdout, "Exceeding variables ignored\n");
        fprintf (stdout, "You might increase the DDDMP_NVARS_DEFAULT constant\n");
        break;
      }
      sscanf(buf, "%s", varname);
      varmatchnames[i]=DDDMP_ALLOC(char, strlen(varname));
      if (varmatchnames[i]==NULL) {
	fprintf (stdout, "Error allocating memory\n");
      } else {
        strcpy(varmatchnames[i], varname);
      }
      i++;
    }
    for (;i<nddvars;i++)
      varmatchnames[i]=NULL;
  }

  fclose(fp);

  return;
}

/**Function********************************************************************

Synopsis    [Load the BDD order from a file (varauxids).] 

Description [Load the BDD order from a file (varauxids).]

SideEffects []

SeeAlso     []

******************************************************************************/
static int *
IntArrayLoad(
  int nddvars
)
{
  /* ------------------- Read optional ord file ------------------------ */

  FILE *fp;
  char filename[DDDMPTEST_MAX_OPERAND];
  int i;
  char buf[DDDMPTEST_MAX_STRING_LENGTH];
  int *array;

  fprintf (stdout, "File : ");
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%s", filename);

  fp = fopen(filename, "r");
  if (fp == NULL) {
    fprintf (stdout, "Couldn't open %s\n", filename);
    return (NULL);
  }

  array=DDDMP_ALLOC(int,nddvars);
  if (array==NULL) {
    fprintf (stdout, "Error allocating memory\n");
  } else {
    i=0;
    while (fgets(buf, DDDMPTEST_MAX_STRING_LENGTH, fp)!=NULL) {
      if (buf[0]=='#') {
        continue;
      }
      if (i>=nddvars) {
        fprintf (stdout, "Number of variables in files higher than DD manager vars (%d)\n",nddvars);
        fprintf (stdout, "Exceeding variables ignored\n");
        fprintf (stdout, "You might increase the DDDMP_NVARS_DEFAULT constant\n");
        break;
      }
      sscanf(buf, "%d", &array[i++]);
    }
    for (;i<nddvars;i++)
      array[i]= -1;
  }

  fclose(fp);

  return (array);
}


/**Function********************************************************************

Synopsis    [Load a BDD from a file.]

Description [Load a BDD from a file.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
BddLoad(
  DdManager *dd,
  DdNode **operand   /* array of operand */
)
{
  /* ----------------------- Loading operands --------------------------- */

  char filename[DDDMPTEST_MAX_OPERAND];
  int i;
  DdNode *f;

  fprintf (stdout, "File : ");
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%s", filename);

  fprintf (stdout, "Which BDDs [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &i);
  
  fprintf (stdout, "Loading %s ...\n", filename);
  f = Dddmp_cuddBddLoad(dd, varmatchmode, varmatchnames, varmatchauxids, 
                    varcomposeids, DDDMP_MODE_DEFAULT, filename, NULL);
  if (f==NULL) {
    fprintf (stderr, "Dddmp Test Error : %s is not loaded from file\n",
             filename);
  } else {
    operand[i] = f;
  }

  return;
} 



/**Function********************************************************************

Synopsis    [Perform an Operation among BDDs.]

Description [Perform an Operation among BDDs.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
Operation(
  DdManager *dd,
  DdNode **operand   /* array of operand */
)
{
  DdNode *f, *g, *h;
  char buf[DDDMPTEST_MAX_STRING_LENGTH];
  int i;

  /* --------------------- compute operation --------------------------- */

  fprintf (stdout, "Operation [or,and,xor,!,buf(=)] : ");
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%s", buf);
  fprintf (stdout, "Source1 [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &i);
  f = operand[i];

  if ((strcmp(buf, "or")==0)|| (strcmp(buf, "OR")==0)) {
    fprintf (stdout, "Source2 [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
    fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
    sscanf (row, "%d", &i);
    g = operand[i];
    h = Cudd_bddOr(dd, f, g);
    Cudd_RecursiveDeref(dd, f);
    Cudd_Ref(h);
    Cudd_RecursiveDeref(dd, g);
  } else if ((strcmp(buf, "and")==0) || (strcmp(buf, "AND")==0)) {
      fprintf (stdout, "Source2 [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
      fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
      sscanf (row, "%d", &i);
      g = operand[i];
      h = Cudd_bddAnd(dd, f, g);
      Cudd_Ref(h);
      Cudd_RecursiveDeref(dd, f);
      Cudd_RecursiveDeref(dd, g);
  } else if ((strcmp(buf, "xor")==0) || (strcmp(buf, "XOR")==0)) {
      fprintf (stdout, "Source2 [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
      fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
      sscanf (row, "%d", &i);
      g = operand[i];
      h = Cudd_bddXor(dd, f, g);
      Cudd_Ref(h);
      Cudd_RecursiveDeref(dd, f);
      Cudd_RecursiveDeref(dd, g);
  } else if (strcmp(buf, "!")==0) {
      h = Cudd_Not(f);
      Cudd_Ref(h);
      Cudd_RecursiveDeref(dd, f);
  } else if ((strcmp(buf, "buf")==0)|| (strcmp(buf, "BUF")==0)) {
      h = f;
  } else {
      fprintf (stderr, "Dddmp Test Error : Operation %s unknown\n", buf);
      h = NULL;
  }

  fprintf (stdout, "Destination [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &i);
  operand[i] = h;

  return;
}

/**Function********************************************************************

Synopsis    [Store a BDD in a file.]

Description [Store a BDD in a file.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
BddStore(
  DdManager *dd,
  DdNode **operand   /* array of operand */
)
{
  /* ------------------------ store results --------------------------- */
  int i;
  char filename[DDDMPTEST_MAX_OPERAND];
  int status;
  DdNode *f;

  fprintf (stdout, "Which BDDs [0..%d]: ", DDDMPTEST_MAX_OPERAND-1);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &i);
  
  fprintf (stdout, "File : ");
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%s", filename);

  fprintf (stdout, "Storing %s ...\n", filename);
  f = operand[i];
  status = Dddmp_cuddBddStore(dd, NULL, f, varmatchnames, varmatchauxids, 
                          DDDMP_MODE_TEXT, varoutinfo, filename, NULL);
  if (status!=1) {
    fprintf (stderr, "Dddmp Test Error : BDD in not stored\n");
  }

  return;
}
/**Function********************************************************************

Synopsis    [Store a BDD in a file.]

Description [Store a BDD in a file.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
DynamicReordering(
  DdManager *dd
)
{
  /* ------------------------ store results --------------------------- */
  Cudd_ReorderingType approach = CUDD_REORDER_SIFT;

  fprintf (stdout, "reordering approach (1..17): "); fflush(stdout);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", (int *) &approach);

  Cudd_ReduceHeap(dd,approach,5);
  
  return;
}

/**Function********************************************************************

Synopsis    [Selects variable matching mode.]

Description [Selects variable matching mode.]

SideEffects []

SeeAlso     []

******************************************************************************/
static void
SetLoadMatchmode()
{
  int sel;

  fprintf (stdout, "Variable matchmode:\n");
  fprintf (stdout, "Match IDs                                (1)\n");
  fprintf (stdout, "Match permIDs                            (2)\n");
  fprintf (stdout, "Match names      (must have been loaded) (3)\n");
  fprintf (stdout, "Match auxids     (must have been loaded) (4)\n");
  fprintf (stdout, "Match composeids (must have been loaded) (5)\n");
  fprintf (stdout, "Your choice: ");fflush(stdout);
  fgets (row, DDDMPTEST_MAX_STRING_LENGTH, stdin);
  sscanf (row, "%d", &sel);

  switch (sel) {
    case 1:
      varmatchmode = DDDMP_VAR_MATCHIDS;
      break;
    case 2:
      varmatchmode = DDDMP_VAR_MATCHPERMIDS;
      break;
    case 3:
      if (varmatchnames == NULL) {
        fprintf (stdout, "Variable names need to be loaded (see help)\n");
      }
      varmatchmode = DDDMP_VAR_MATCHNAMES;
      break;
    case 4:
      if (varmatchauxids == NULL) {
        fprintf (stdout, "Variable auxids need to be loaded (see help)\n");
      }
      varmatchmode = DDDMP_VAR_MATCHAUXIDS;
      break;
    case 5:
      if (varcomposeids == NULL) {
        fprintf (stdout, "Variable composeids need to be loaded (see help)\n");
      }
      varmatchmode = DDDMP_VAR_COMPOSEIDS;
      break;
    default:
      fprintf (stderr, "Wrong choice!\n");
      break;
  }

}
