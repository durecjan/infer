/* Atlas test: self-referential pointer store (*p = p)
   Expected: store_dereference_address_assign path taken,
   the new ExpPointsTo source must be updated via expr_replace
   to use the fresh destination id instead of the original expression,
   ensuring consistency after substitution */

#include <stdlib.h>

void self_referential_pointer() {
    int **p = (int **)malloc(sizeof(int *));
    *p = (int *)p;
    int *q = *p;
    free(p);
}
	
// BUG: subst_apply seems to gobble up the reference, however here, we expect p -(8)-> Var(7) and subst p=Var(7)

/* TRACE:

OK
Current:
p -(8)-> block
(Base(p)==p) & (End(p)==(p+8))
----------------
Missing:


----------------
Vars:
(return;0) (q;1) (p;2) (n$5;5) (n$4;6) 
----------------
Substitutions:
{n$5==p;n$4==p;}
----------------
Types:
(void;0) (int*;1) (int**;2) (int*;5) (int**;6) 
================
[SIL_STORE]
[SIL_INSTR_LHS]: Var(n$4)
[SIL_INSTR_RHS]: Cast(int*, Var(n$5))
[LHS_EXPR]: p
[RHS_EXPR]: p
[Block_fragments] - found 1 in state.current ; found 0 in state.missing
[LHS] - typ=int* ; id=2 ; offset=0
OK
Current:
(Var(7)+0) -(8)-> Var(7)
(Base(Var(7))==Var(7)) & (End(Var(7))==(Var(7)+8))
----------------
Missing:


----------------
Vars:
(return;0) (q;1) (p;2) (n$5;5) (n$4;6) 
----------------
Substitutions:
{n$5==p;n$4==p;}
----------------
Types:
(void;0) (int*;1) (int**;2) (int*;5) (int**;6) (int*;7) 
*/
