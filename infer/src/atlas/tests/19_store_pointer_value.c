/* Atlas test: storing a pointer value through dereference
   Expected: store_dereference_address_assign path taken,
   substitution map updated to link the destination to the stored pointer */

#include <stdlib.h>

void store_pointer_value() {
    int **pp = (int **)malloc(sizeof(int *));
    int *q = (int *)malloc(sizeof(int));
    *pp = q;
    int *r = *pp;
    *r = 99;
    free(q);
    free(pp);
}


/*
	
   BUG
   we seem to gobble up the reference q PointsToBlock when connecting the PointsTo predicates

   TRACE:

================
[SIL_LOAD]
[SIL_INSTR_RHS]: Lvar(q)
[RHS_EXPR]: q
OK
Current:
q -(4)-> block * pp -(8)-> block
(Base(q)==q) & (End(q)==(q+4)) & (Base(pp)==pp) & (End(pp)==(pp+8))
----------------
Missing:


----------------
Vars:
(return;0) (r;1) (q;2) (pp;3) (n$8;8)
----------------
Substitutions:
{n$8==q;}
----------------
Types:
(void;0) (int*;1) (int*;2) (int**;3) (int*;8)
================
[SIL_LOAD]
[SIL_INSTR_RHS]: Lvar(pp)
[RHS_EXPR]: pp
OK
Current:
q -(4)-> block * pp -(8)-> block
(Base(q)==q) & (End(q)==(q+4)) & (Base(pp)==pp) & (End(pp)==(pp+8))
----------------
Missing:


----------------
Vars:
(return;0) (r;1) (q;2) (pp;3) (n$8;8) (n$7;9)
----------------
Substitutions:
{n$8==q;n$7==pp;}
----------------
Types:
(void;0) (int*;1) (int*;2) (int**;3) (int*;8) (int**;9)
================
[SIL_STORE]
[SIL_INSTR_LHS]: Var(n$7)
[SIL_INSTR_RHS]: Var(n$8)
[LHS_EXPR]: pp
[RHS_EXPR]: q
[Block_fragments] - found 1 in state.current ; found 0 in state.missing
[LHS] - typ=int* ; id=3 ; offset=0
OK
Current:
(pp+0) -(8)-> Var(10) * Var(10) -(4)-> block
(Base(Var(10))==Var(10)) & (End(Var(10))==(Var(10)+4)) & (Base(pp)==pp) & (End(pp)==(pp+8))
----------------
Missing:

----------------
Vars:
(return;0) (r;1) (q;2) (pp;3) (n$8;8) (n$7;9)
----------------
Substitutions:
{n$8==q;n$7==pp;}
----------------
Types:
(void;0) (int*;1) (int*;2) (int**;3) (int*;8) (int**;9) (int*;10)
*/
