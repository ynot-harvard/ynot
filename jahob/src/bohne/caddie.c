/* CADDIE: the CAml cuDD Interface
 * Our CAML chews the CUDD
 */

// Cudd headers
#include "util.h"
#include "cudd.h"

// Caml-C interface headers
#include "mlvalues.h"
#include "alloc.h"
#include "memory.h"
#include "custom.h"
#include "callback.h"

// Macros for extracting information from Caml wrappers
#define Bdd_mgr(x) ((*(caddie_node **) (Data_custom_val(x)))->M)
#define Bdd_node(x) ((*(caddie_node **) (Data_custom_val(x)))->node)
#define Bdd_ptr(x) ((*(caddie_node **) (Data_custom_val(x))))

#define Map_size(x) ((*(caddie_map **) (Data_custom_val(x)))->size)
#define Map_mgr(x) ((*(caddie_map **) (Data_custom_val(x)))->M)
#define Map_old(x) ((*(caddie_map **) (Data_custom_val(x)))->old)
#define Map_new(x) ((*(caddie_map **) (Data_custom_val(x)))->new)
#define Map_ptr(x) ((*(caddie_map **) (Data_custom_val(x))))

#define Manager(x) ((*(DdManager **) (Data_custom_val(x))))

// Useful macros for bdd operations
#define Bdd_sameMgr(x,y) (Bdd_mgr(x) == Bdd_mgr(y))
#define Bdd_op(f,x,y) caddie_nodeWrap(Bdd_mgr(x),f(Bdd_mgr(x),Bdd_node(x),Bdd_node(y)))
#define Bdd_isTrue(x) (Bdd_node(x) == caddie_trueNode(Bdd_mgr(x)))
#define Bdd_isFalse(x) (Bdd_node(x) == caddie_falseNode(Bdd_mgr(x)))
#define Add_isOne(x) (Bdd_node(x) == caddie_trueNode(Bdd_mgr(x)))
#define Add_isZero(x) (Bdd_node(x) == caddie_zeroNode(Bdd_mgr(x)))

// void* array to hold the function pointers for add Operations
static void *addOp[7] = {Cudd_addPlus, Cudd_addTimes, Cudd_addDivide, Cudd_addMinus, Cudd_addAgreement, Cudd_addMaximum, Cudd_addMinimum};

// void* array to hold the function pointers for zadd Operations
static void *zaddOp[6] ={Cudd_addTimes, Cudd_addOr, Cudd_addNand, Cudd_addNor, Cudd_addXor, Cudd_addXnor};

// array for reordering types
Cudd_ReorderingType reorderType[21] = { CUDD_REORDER_SAME,
					CUDD_REORDER_NONE,
					CUDD_REORDER_RANDOM,
					CUDD_REORDER_RANDOM_PIVOT,
					CUDD_REORDER_SIFT,
					CUDD_REORDER_SIFT_CONVERGE,
					CUDD_REORDER_SYMM_SIFT,
					CUDD_REORDER_SYMM_SIFT_CONV,
					CUDD_REORDER_WINDOW2,
					CUDD_REORDER_WINDOW3,
					CUDD_REORDER_WINDOW4,
					CUDD_REORDER_WINDOW2_CONV,
					CUDD_REORDER_WINDOW3_CONV,
					CUDD_REORDER_WINDOW4_CONV,
					CUDD_REORDER_GROUP_SIFT,
					CUDD_REORDER_GROUP_SIFT_CONV,
					CUDD_REORDER_ANNEALING,
					CUDD_REORDER_GENETIC,
					CUDD_REORDER_LINEAR,
					CUDD_REORDER_LINEAR_CONVERGE,
					CUDD_REORDER_EXACT };
typedef struct caddie_node caddie_node; // bdd and add nodes
typedef struct caddie_map caddie_map; // variable mappings

struct caddie_node
{
  DdManager	*M; // pointer to the DD manager
  DdNode	*node; // pointer to bdd/add node
};

struct caddie_map
{
  int		size; // number of vars in each list
  DdManager	*M; // manager associated with map
  DdNode	**old; // array of bdd/add nodes
  DdNode	**new; // array of bdd/add nodes
  // the structure is used for mapping old <-> new vars.
  // the mapping works both ways
  // implicit is the assumption that old and new are disjoint
};

/* Function to raise the InvalidMgr exception
 * Raised when the bdd manager in question has not been initialized
 */
void raise_mgrError()
{
  raise_constant(*caml_named_value("invalid mgr"));
}

/* Function to raise the DiffMgr exception
 * Raised when two BDD/ADD operands belong to diff. managers
 */
void raise_diffMgr()
{
  raise_constant(*caml_named_value("diff mgr"));
}


/* Finalization function for a BDD/ADD manager
 */
static void caddie_mgrFinalize(value foo)
{
  CAMLparam1(foo);
  if (Manager(foo) != NULL) {
    Cudd_Quit(Manager(foo));
  }
  CAMLreturn0;
}

/* Finalization function for a BDD/ADD node
 */
static void caddie_nodeFinalize(value foo)
{
  CAMLparam1(foo);
  Cudd_RecursiveDeref(Bdd_mgr(foo),Bdd_node(foo));
  stat_free((caddie_node *) Bdd_ptr(foo));
  CAMLreturn0;
}

/* Finalization function for a variable map
 */
static void caddie_mapFinalize(value foo)
{
  CAMLparam1(foo);
  stat_free((DdNode **) Map_old(foo));
  stat_free((DdNode **) Map_new(foo));
  stat_free((caddie_map *) Map_ptr(foo));
  CAMLreturn0;
}

/* Wrapper for DdNodes. Allocates space for caddie_node
 * and creates a finalized block. Also increments the ref. count.
 */
value caddie_nodeWrap(DdManager *M, DdNode *node)
{
  CAMLparam0();
  CAMLlocal1(result);
  caddie_node *n;

  if (M== NULL) {
    raise_mgrError();
  } else {
    n = (caddie_node *) stat_alloc(sizeof(caddie_node));
    /* stat_alloc essentially does a malloc. If out of memory,
     * it raises an exception
     */
    n->M = M;
    n->node = node;
    
    Cudd_Ref(node);

    result = alloc_final(2,&caddie_nodeFinalize,0,1);
    Bdd_ptr(result) = n;
  }

  CAMLreturn(result);
}

/* Wrap a varMap
 */
value caddie_mapWrap(DdManager *M, int size, DdNode **old, DdNode **new)
{
  CAMLparam0();
  CAMLlocal1(result);
  caddie_map *m;

  if (M==NULL) {
    raise_mgrError();
  } else {
    m = (caddie_map *) stat_alloc(sizeof(caddie_map));
    m->size = size;
    m->M = M;
    m-> old = old;
    m-> new = new;

    result = alloc_final(2,&caddie_mapFinalize,0,1);
    Map_ptr(result) = m;
    CAMLreturn(result);
  }
}


/* Initialize a DdManager. 
 * The finalization function for the manager takes care of quitting
 */
value caddie_init(value numvars, value numslots,value cachesize, value maxmem)
{
  CAMLparam4(numvars,numslots,cachesize,maxmem);
  CAMLlocal1(result);
  DdManager *M;
  M = Cudd_Init(Int_val(numvars),0,Int_val(numslots),
		Int_val(cachesize),Long_val(maxmem));
  result = alloc_final(2,&caddie_mgrFinalize,0,1);
  Manager(result) = (DdManager *) M;
  CAMLreturn(result);
}

/* Exit a DdManager
 * This function calls Cudd_quit and sets M to NULL
 * It is not necessary to call this function -- the
 * finalization function for the manager also
 * calls Cudd_quit, if not already done
 */
value caddie_exit(value M)
{
  CAMLparam1(M);
  if (Manager(M) == NULL) {
    raise_mgrError();
  }
  Cudd_Quit(Manager(M));
  Manager(M) = NULL;
  CAMLreturn (Val_unit);
}

/* Enable Automatic dynamic reordering
 */
value caddie_dynEnable(value M, value r)
{
  CAMLparam2(M,r);
  if (Manager(M)==NULL) {
    raise_mgrError();
  } else {
    Cudd_AutodynEnable(Manager(M),reorderType[Int_val(r)]);
    CAMLreturn(Val_unit);
  }
}

/* Disable Automatic dynamic reordering
 */
value caddie_dynDisable(value M)
{
  CAMLparam1(M);
  if (Manager(M)==NULL) {
    raise_mgrError();
  } else {
    Cudd_AutodynDisable(Manager(M));
    CAMLreturn(Val_unit);
  }
}


/* Return the bdd node for true or add node for 1
 */
value caddie_true(value M)
{
  CAMLparam1(M);
  if (Manager(M)==NULL) {
    raise_mgrError();
  }
  CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_ReadOne(Manager(M))));
}

/* Similar to caddie_true, but called from within C.
 * argument is of type DdManager* and not value.
 * returns a DdNode and not a value
 */
DdNode *caddie_trueNode(DdManager *M)
{
  if (M==NULL) {
    raise_mgrError();
  }
  return(Cudd_ReadOne(M));
}

/* Return the bdd node for false
 */
value caddie_false(value M)
{
  CAMLparam1(M);
  if (Manager(M)==NULL) {
    raise_mgrError();
  }
  CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_ReadLogicZero(Manager(M))));
}

/* Similar to caddie_trueNode
 */
DdNode *caddie_falseNode(DdManager *M)
{
  if (M==NULL) {
    raise_mgrError();
  }
  return(Cudd_ReadLogicZero(M));
}

/* Return the add node for 0
 */
value caddie_zero(value M)
{
  CAMLparam1(M);
  if (Manager(M)==NULL) {
    raise_mgrError();
  }
  CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_ReadZero(Manager(M))));
}

/* Similar to caddie_zero but for calling from within C
 */
DdNode *caddie_zeroNode(DdManager *M)
{
  if (M==NULL) {
    raise_mgrError();
  } else {
    return(Cudd_ReadZero(M));
  }
}

/* Return the add node for Plus Infinity
 */
value caddie_plusInf(value M)
{
  CAMLparam1(M);
  if (Manager(M) == NULL) {
    raise_mgrError();
  }
  CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_ReadPlusInfinity(Manager(M))));
}

/* Return the add node for Minus Infinity
 */
value caddie_minusInf(value M)
{
  CAMLparam1(M);
  if (Manager(M) == NULL) {
    raise_mgrError();
  }
  CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_ReadMinusInfinity(Manager(M))));
}

/* Return the add for a constant or create it
 */
value caddie_addConst(value M, value c)
{
  CAMLparam2(M,c);
  if (Manager(M) == NULL) {
    raise_mgrError();
  }
  CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_addConst(Manager(M),Double_val(c))));
}

/* Return the background valued add
 */
value caddie_addReadBack(value M)
{
  CAMLparam1(M);
  if (Manager(M) == NULL) {
    raise_mgrError();
  }
  CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_ReadBackground(Manager(M))));
}

/* Set the background value for Add's
 */
value caddie_addSetBack(value d)
{
  CAMLparam1(d);
  if (Bdd_mgr(d) == NULL) {
    raise_mgrError();
  }
  Cudd_SetBackground(Bdd_mgr(d),Bdd_node(d));
  CAMLreturn(Val_unit);
}

/* Checks to see if DDnode is a constant (as opposed to internal)
 */
value caddie_isConst(value d)
{
  CAMLparam1(d);
  if (Bdd_mgr(d) == NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(Val_bool(Cudd_IsConstant(Bdd_node(d))));
  }
}

/* Check for equality between two DDs
 */
value caddie_equal(value d1, value d2)
{
  CAMLparam2(d1,d2);
  if ((Bdd_mgr(d1) == Bdd_mgr(d2))) {
    CAMLreturn(Bdd_node(d1) == Bdd_node(d2) ? Val_true: Val_false);
  } else {
    raise_diffMgr();
  }
}

value caddie_bddCountMinterm(value M, value B, value i) {
 CAMLparam3(M,B,i);
 double num ;
 if (Manager(M) == NULL) {
   raise_mgrError();
 }
 if((Bdd_mgr(B) != Manager(M))) {
   raise_diffMgr();
 }
 num = Cudd_CountMinterm(Manager(M), Bdd_node(B), Int_val(i));
 CAMLreturn(copy_double(num)); 
}

/* Return the ith bdd variable projection function
 */
value caddie_bddIthVar(value M, value i)
{
  CAMLparam2(M,i);
  if (Manager(M) == NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_bddIthVar(Manager(M),Int_val(i))));
  }
}

/* Return the bdd for a new variable
 */
value caddie_bddNewVar(value M)
{
  CAMLparam1(M);
  if (Manager(M) == NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_bddNewVar(Manager(M))));
  }
}

/* Return the add for the ith var
 */
value caddie_addIthVar(value M, value I)
{
  CAMLparam2(M,I);
  if (Manager(M)==NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_addIthVar(Manager(M),Int_val(I))));
  }
}

/* Return the add for a new variable
 */
value caddie_addNewVar(value M)
{
  CAMLparam1(M);
  if (Manager(M)==NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Manager(M),Cudd_addNewVar(Manager(M))));
  }
}


/* Complement a BDD
 */
value caddie_bddNot(value f)
{
  CAMLparam1(f);
  CAMLreturn(caddie_nodeWrap(Bdd_mgr(f),Cudd_Not(Bdd_node(f))));
}

/* BDD ITE
 */
value caddie_bddIte(value f, value g, value h)
{
  CAMLparam3(f,g,h);
  if (Bdd_sameMgr(f,g) && Bdd_sameMgr(f,h)) {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(f),Cudd_bddIte(Bdd_mgr(f),Bdd_node(f),Bdd_node(g),Bdd_node(h))));
  } else {
    raise_diffMgr();
  }
}

/* BDD THEN node
 */
value caddie_bddThen (value f) {
 CAMLparam1(f);
 DdNode *result;
 result = Cudd_T(Bdd_node (f));

 CAMLreturn (caddie_nodeWrap(Bdd_mgr(result), result));
}

/* BDD ELSE node
 */
value caddie_bddElse (value f) {
 CAMLparam1(f);
 DdNode *result;
 result = Cudd_E(Bdd_node (f));

 CAMLreturn (caddie_nodeWrap(Bdd_mgr(result), result));
 
}

/* BDD AND
 */
value caddie_bddAnd(value f, value g)
{
  CAMLparam2(f,g);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(Bdd_op(Cudd_bddAnd,f,g));
  } else {
    raise_diffMgr();
  }
}

/* BDD NAND
 */
value caddie_bddNand(value f, value g)
{
  CAMLparam2(f,g);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(Bdd_op(Cudd_bddNand,f,g));
  } else {
    raise_diffMgr();
  }
}

/* BDD OR
 */
value caddie_bddOr(value f, value g)
{
  CAMLparam2(f,g);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(Bdd_op(Cudd_bddOr,f,g));
  } else {
    raise_diffMgr();
  }
}

/* BDD NOR
 */
value caddie_bddNor(value f, value g)
{
  CAMLparam2(f,g);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(Bdd_op(Cudd_bddNor,f,g));
  } else {
    raise_diffMgr();
  }
}


/* BDD XOR
 */
value caddie_bddXor(value f, value g)
{
  CAMLparam2(f,g);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(Bdd_op(Cudd_bddXor,f,g));
  } else {
    raise_diffMgr();
  }
}

/* BDD BIIMP
 */
value caddie_bddBiimp(value f, value g)
{
  CAMLparam2(f,g);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(Bdd_op(Cudd_bddXnor,f,g));
  } else {
    raise_diffMgr();
  }
}

/* BDD IMP
 */
value caddie_bddImp(value f, value g)
{
  CAMLparam2(f,g);
  CAMLreturn(caddie_bddIte(f,g,caddie_nodeWrap(Bdd_mgr(f),caddie_trueNode(Bdd_mgr(f)))));
}

/* Complement an ADD
 * complement of 0 is 1; complement of everything else is 0
 * works well for Negating 0/1 ADDs
 */
value caddie_addCmpl(value b)
{
  CAMLparam1(b);
  if (Bdd_mgr(b)==NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(b),Cudd_addCmpl(Bdd_mgr(b),Bdd_node(b))));
  }
}

/* Convert boolean value to bdd
 */
value caddie_fromBool(value M, value e)
{
  CAMLparam2(M,e);
  if (Manager(M) == NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(Bool_val(e)?caddie_true(M):caddie_false(M));
  }
}

/* Convert (true/false) bdd to boolean
 */
value caddie_toBool(value b)
{
  CAMLparam1(b);  if (Bdd_mgr(b) == NULL) {
    raise_mgrError();
  } else if (Bdd_isTrue(b)) {
    CAMLreturn(Val_true);
  } else if (Bdd_isFalse(b)) {
    CAMLreturn(Val_false);
  } else {
    invalid_argument("Not a BDD leaf node");
  }
}

/* Convert bool to zero/one add
 */
value caddie_zFromBool(value M,value e)
{
  CAMLparam2(M,e);
  if (Manager(M) == NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(Bool_val(e)?caddie_true(M):caddie_zero(M));
  }
}

/* Convert a (zero/one) add to bool
 */
value caddie_zToBool(value b)
{
  CAMLparam1(b);
  if (Bdd_mgr(b) == NULL) {
    raise_mgrError();
  } else if (Add_isOne(b)) {
    CAMLreturn(Val_true);
  } else if (Add_isZero(b)) {
    CAMLreturn(Val_false);
  } else {
    invalid_argument("Not a 0/1 ADD leaf Node");
  }
}

/* Return the value of an ADD constant node
 */
value caddie_addVal(value b)
{
  CAMLparam1(b);
  if (Bdd_mgr(b) == NULL) {
    raise_mgrError();
  } else if (Cudd_IsConstant(Bdd_node(b))) {
    CAMLreturn(copy_double(Cudd_V(Bdd_node(b))));
  } else {
    invalid_argument("Not a constant ADD node");
  }
}

/* Add a variable to a cube
 */
value caddie_addVar(value c, value i)
{
  CAMLparam2(c,i);
  CAMLreturn(caddie_nodeWrap(Bdd_mgr(c),Cudd_bddAnd(Bdd_mgr(c),Bdd_node(c),Cudd_bddIthVar(Bdd_mgr(c),Int_val(i)))));
}


/* Universal Quantification
 */
value caddie_forall(value c, value b)
{
  CAMLparam2(c,b);
  if (Bdd_sameMgr(c,b)) {
    CAMLreturn(Bdd_op(Cudd_bddUnivAbstract,b,c));
  } else {
    raise_diffMgr();
  }
}

/* Existential Quanitification
 */
value caddie_exists(value c, value b)
{
  CAMLparam2(b,c);
  if (Bdd_sameMgr(c,b)) {
    CAMLreturn(Bdd_op(Cudd_bddExistAbstract,b,c));
  } else {
    raise_diffMgr();
  }
}


/* Create a varMap
 */
value caddie_toMap(value m, value list_a, value list_b)
{
  CAMLparam3(m,list_a,list_b);
  int size, i;
  DdNode **old, **new;
  DdManager *M;

  M = Manager(m);
  if (M == NULL) {
    raise_mgrError();
  } else {
    size = Wosize_val(list_a);
    old = (DdNode **) stat_alloc(sizeof(DdNode *) * size);
    new = (DdNode **) stat_alloc(sizeof(DdNode *) * size);

    for (i=0;i<size;i++) {
      old[i] = Cudd_bddIthVar(M,Int_val(Field(list_a,i)));
      new[i] = Cudd_bddIthVar(M,Int_val(Field(list_b,i)));
    }

    CAMLreturn(caddie_mapWrap(M,size,old,new));
  }
}

/* replace
 */
value caddie_replace(value b, value m)
{
  CAMLparam2(b,m);

  CAMLreturn(caddie_nodeWrap(Bdd_mgr(b),Cudd_bddSwapVariables(Bdd_mgr(b),Bdd_node(b),Map_old(m),Map_new(m),Map_size(m))));
  
}

/* Apply an Op to two Add's
 */
value caddie_addApply(value O, value f, value g)
{
  CAMLparam3(O,f,g);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(f),Cudd_addApply(Bdd_mgr(f),addOp[Int_val(O)],Bdd_node(f),Bdd_node(g))));
  } else {
    raise_diffMgr();
  }
}

/* Apply an Op to two 0/1 ADD's
 */
value caddie_zaddApply(value O, value f, value g)
{
  CAMLparam3(O,f,g);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(f),Cudd_addApply(Bdd_mgr(f),zaddOp[Int_val(O)],Bdd_node(f),Bdd_node(g))));
  } else {
    raise_diffMgr();
  }
}

/* ITE for ADDs
 */
value caddie_addIte(value f, value g, value h)
{
  CAMLparam3(f,g,h);
  if (Bdd_sameMgr(f,g) && Bdd_sameMgr(f,h)) {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(f),Cudd_addIte(Bdd_mgr(f),Bdd_node(f),Bdd_node(g),Bdd_node(h))));
  } else {
    raise_diffMgr();
  }
}

/* Compose(f,g,v) - replaces variable with index v with
 * the 0/1 ADD g in f
 */
value caddie_addCompose(value f, value g, value v)
{
  CAMLparam3(f,g,v);
  if (Bdd_sameMgr(f,g)) {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(f),Cudd_addCompose(Bdd_mgr(f),Bdd_node(f),Bdd_node(g),Int_val(v))));
  } else {
    raise_diffMgr();
  }
}

/* Return the max constant add for a given ADD
 */
value caddie_addMax(value b)
{
  CAMLparam1(b);
  if (Bdd_mgr(b) == NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(b),Cudd_addFindMax(Bdd_mgr(b),Bdd_node(b))));
  }
}

/* Return the min constant add for a given ADD
 */
value caddie_addMin(value b)
{
  CAMLparam1(b);
  if (Bdd_mgr(b) == NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(b),Cudd_addFindMin(Bdd_mgr(b),Bdd_node(b))));
  }
}

/* Print a DD
 */
value caddie_print(value d)
{
  CAMLparam1(d);
  Cudd_PrintDebug(Bdd_mgr(d),Bdd_node(d),0,2);
  CAMLreturn(Val_unit);
}

/* Does nothing
 * Useful for conversions between types which have the
 * same C representation
 */
value caddie_nop(value foo)
{
  CAMLparam1(foo);
  CAMLreturn(foo);
}

/* Convert an ADD to a BDD
 * If the ADD is a 0/1 ADD, it is a mapping from arithmetic 0/1
 * to logic 0/1.
 * For arbitrary ADDs, anything other than 0 is mapped to logic 1
 */
value caddie_addBddPattern(value b)
{
  CAMLparam1(b);
  if (Bdd_mgr(b)==NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(b),Cudd_addBddPattern(Bdd_mgr(b),Bdd_node(b))));
  }
}

/* Convert a BDD to a 0/1 ADD
 */
value caddie_bddAdd(value b)
{
  CAMLparam1(b);
  if (Bdd_mgr(b) == NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(b),Cudd_BddToAdd(Bdd_mgr(b),Bdd_node(b))));
  }
}


/* Convert and ADD to a BDD. if the ith bit of the (integer)
 * discriminant is 1, it is replaced by logic 1
 */
value caddie_addIthBit(value b, value i)
{
  CAMLparam2(b,i);
  if (Bdd_mgr(b)==NULL) {
    raise_mgrError();
  } else {
    CAMLreturn(caddie_nodeWrap(Bdd_mgr(b),Cudd_addBddIthBit(Bdd_mgr(b),Bdd_node(b),Int_val(i))));
  }
}

/* Return the product BDD of the variables in the support of b */
value caddie_bddSupport (value f) {
  CAMLparam1(f);
  CAMLreturn(caddie_nodeWrap(Bdd_mgr(f),Cudd_Support(Bdd_mgr(f),Bdd_node(f))));
}

value caddie_bddIndex (value f) {
  CAMLparam1(f);
  CAMLreturn(Val_int(Cudd_NodeReadIndex(Bdd_node(f))));
}

void _recursiveComputeSupportSet (DdNode *dd, int *supp) {
  if(Cudd_IsConstant(dd)) {
    return;
  } else {
    DdNode *th, *el;
    int index = Cudd_NodeReadIndex(dd);
    supp [index] = 1;
    th = Cudd_T(dd);
    el = Cudd_E(dd);
    _recursiveComputeSupportSet(th, supp);
    _recursiveComputeSupportSet(el, supp);

  }
}

value caddie_bddSupportSet (value f) {
  CAMLparam1(f);
  CAMLlocal2(head, tmp);

  DdNode *bnd = Bdd_node (f);
  DdManager *mgr = (DdManager *)(Bdd_mgr(f));
  
  DdNode *b = Cudd_Support(mgr, bnd);

  int size = Cudd_ReadSize(mgr);
  int *support = ALLOC(int, size);
  int i;

  if(support == NULL || b == NULL) {
    /* raise out of memory. */
    
    exit (1);
  }

  Cudd_Ref (b);

  for (i=0; i < size; i++) {
    support[i] = 0;
  }
  _recursiveComputeSupportSet(b, support);
  head = Val_int (0);
  for(i=0; i < size; i++) {
    if(support[i]==1) {
      tmp = alloc_small(2,0);
      Field (tmp, 0) = Val_int(i);
      Field (tmp, 1) = head;
      head = tmp;
    }
  }
  Cudd_RecursiveDeref(mgr, b);
  FREE(support);

  CAMLreturn (head);

}

value caddie_forEachCube(value b, value fn)
{
  CAMLparam2(b, fn);
  CAMLlocal1(carr);
  int i;
  int *cube;
  CUDD_VALUE_TYPE val;
  DdGen *gen;
  DdManager *mg = (DdManager *)(Bdd_mgr(b));
  DdNode *bnd = Bdd_node(b);
  
  Cudd_Ref (bnd);

  if (Bdd_mgr(b)==NULL)
    raise_mgrError();

  caml_register_global_root(&fn);

  Cudd_ForeachCube(mg, bnd, gen, cube, val) {
     if(Cudd_ReadSize(mg) <= Max_young_wosize) 
	carr = caml_alloc_small(Cudd_ReadSize(mg), 0);
     else
	carr = caml_alloc_shr(Cudd_ReadSize(mg), 0);
    for(i=0; i < Cudd_ReadSize(mg); i++) {
      initialize(&Field(carr, i), Val_int(cube[i]));
    }
    callback(fn, carr);
  }

  caml_remove_global_root(&fn);

  CAMLreturn0;
}

value caddie_forEachNode (value bdd, value fn)
{
  CAMLparam2(bdd, fn);
  
  DdGen *gen;
  DdManager *mg = (DdManager *)(Bdd_mgr(bdd));
  DdNode *bnd = Bdd_node(bdd);
  DdNode *node;

  caml_register_global_root(&fn);

  if (Bdd_mgr(bdd)==NULL)
    raise_mgrError();
  Cudd_ForeachNode(mg, bnd, gen, node) {
    callback(fn, caddie_nodeWrap(mg, node));
  }

  caml_remove_global_root(&fn);
  
  CAMLreturn0;
}


/* compute the cofactor of f wrt g */
value caddie_bddCofactor (value f, value g) {
  CAMLparam2(f,g);
  DdNode *fnd = Bdd_node(f), *gnd = Bdd_node(g);
  DdNode *result = NULL;

  /* chek same mgr */
  if(Bdd_mgr(f) == Bdd_mgr(g)) {
    result = Cudd_bddConstrain(Bdd_mgr(f), fnd, gnd);
  } else {
    raise_diffMgr();
  }
  assert(result!=NULL);
  CAMLreturn (caddie_nodeWrap(Bdd_mgr(f), result));
}

/* compute the cofactor of f wrt g */
value caddie_bddVarCofactor (value f, value g) {
  CAMLparam2(f,g);
  DdNode *fnd = Bdd_node(f), *gnd = Bdd_node(g);
  DdNode *result = NULL;

  /* chek same mgr */
  if(Bdd_mgr(f) == Bdd_mgr(g)) {
    result = Cudd_Cofactor(Bdd_mgr(f), fnd, gnd);
  } else {
    raise_diffMgr();
  }
  assert(result!=NULL);
  CAMLreturn (caddie_nodeWrap(Bdd_mgr(f), result));
}

/**Function********************************************************************

  Synopsis    [Functional composition of a function by a variable.]

  SideEffects []

******************************************************************************/
value caddie_bddCompose (value f, value g, value vbl) {
  CAMLparam3(f,g,vbl);

  DdNode * result;

  if((Bdd_mgr(f) == Bdd_mgr(g)) && (Bdd_mgr(f) == Bdd_mgr(vbl))) {
    result = Cudd_bddCompose(Bdd_mgr(f), Bdd_node(f), Bdd_node(g), Cudd_NodeReadIndex(Bdd_node(vbl)));
    assert(result!=NULL);
    CAMLreturn (caddie_nodeWrap(Bdd_mgr(f), result));
  } else {
    raise_diffMgr();
  }
}

/*TO DO */
value caddie_bddSubstitute (value f, value arr1, value arr2) {
  CAMLparam3(f,arr1, arr2);
  CAMLreturn (f);
}

/**Function********************************************************************

  Synopsis    [Returns the BDD of the top variable.]

  Description [Returns the BDD of the top variable of the argument. If
  the argument is constant, it returns the constant function itself.]

  SideEffects []

******************************************************************************/
value caddie_bddTopVar (value f) {
  CAMLparam1(f);
  DdNode *node = Bdd_node(f);
  DdNode *result;

  if(Cudd_IsConstant(node)) {
    result = node;
  } else {
    int index = Cudd_NodeReadIndex (node);
    result = Cudd_bddIthVar(Bdd_mgr(f), index);
  }
  CAMLreturn (caddie_nodeWrap (Bdd_mgr(f), result)); 
  
}





