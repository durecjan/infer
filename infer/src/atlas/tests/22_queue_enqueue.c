#include "queue.h"

void enqueue(struct queue *q, char *data) {
    struct node *n = (struct node *)malloc(sizeof(struct node));
    if (n == NULL) return;

    n->data = data;
    n->next = NULL;

    if (q->tail == NULL) {
        q->head = n;
        q->tail = n;
    } else {
        q->tail->next = n;
        q->tail = n;
    }
}


/*

BUG

description:
flow is correct, on line (if (n == NULL) return;), we filter out failed malloc state, at line (if (q->tail == NULL)) we do not filter out any state since the solver result is Uknown and we add the condition to state.missing.pure of the respective states - there are also no duplicated intermediate debug prints, suggesting this is not a issue of exec_instr, however at the end of the debug prints, there is this:

[SIL_METADATA]: APPLY_ABSTRACTION; [line 15, column 9]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 10, column 5]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 10, column 5]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 10, column 5]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 10, column 5]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 10, column 5]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 10, column 5]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 10, column 5]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 10, column 5]

and within the debug prints, there is this:

[SIL_METADATA]: APPLY_ABSTRACTION; [line 5, column 20]
[SIL_METADATA]: APPLY_ABSTRACTION; [line 12, column 9]

so it would seem that infer, via sil, is creating these duplicates that would be filtered out via join since they are equal (even in the aspect of cell variable ids) and we are not doing anything in AtlasTransfer.run to prevent this and with the current implementation of said method, we get 3 final states corresponding to the "malloc failed case", 8 final states corresponding to the "q->tail == NULL" case and 8 more final states corresponding to the "q->tail != NULL" case - all of them are complete duplicates and are equal in every aspect

PROCFG GRAPH TRACE :

void enqueue(struct queue *q, char *data) { S_1 summary for enqueue
4	    struct node *n = (struct node *)malloc(sizeof(struct node)); I_19
5	    if (n == NULL) return; I_15 C_16 I_18 C_17 J_14
6
7	    n->data = data; I_13
8	    n->next = NULL; I_12
9
10	    if (q->tail == NULL) { I_5 C_6 C_7 J_3 I_4
11	        q->head = n; I_9
12	        q->tail = n; I_8
13	    } else {
14	        q->tail->next = n; I_11
15	        q->tail = n; I_10
16	    }
17	} E_2

node1   preds:      succs:19    exn: Start

[struct node *n = (struct node *)malloc(sizeof(struct node));]
node19  preds:1     succs:15    exn: Instructions

[if (n == NULL) return;]
node15  preds:19    succs:16 17 exn: Instructions
node16  preds:15    succs:18    exn: Conditional true Branch
node18  preds:16    succs:2     exn: Instructions
node17  preds:15    succs:14    exn: Conditional false Branch
node14  preds:17    succs:13    exn: Join

[n->data = data;]
node13  preds:14    succs:12    exn: Instructions

[n->next = NULL;]
node12  preds:13    succs:5     exn: Instructions

[if (q->tail == NULL)]
node5   preds:12    succs:6 7   exn: Instructions
node6   preds:5     succs:9     exn: Conditional true Branch
node7   preds:5     succs:11    exn: Conditional false Branch
node3   preds:10 8  succs:4     exn: Join
node4   preds:3     succs:2     exn: Instructions

[q->head = n;]
node9   preds:6     succs:8     exn: Instructions

[q->tail = n;]
node8   preds:9     succs:3     exn: Instructions

[q->tail->next = n;]
node11  preds:7     succs:10    exn: Instructions

[q->tail = n;]
node10  preds:11    succs:3     exn: Instructions



*/
