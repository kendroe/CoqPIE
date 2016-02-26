
#include <stdio.h>
#include <stdlib.h>

#define VAR_COUNT 10

char assignments[VAR_COUNT];

struct clause {
    struct clause *next;
    char positive_lit[VAR_COUNT];
    char negative_lit[VAR_COUNT];
    char watch_var[VAR_COUNT];
    struct clause *watch_next[VAR_COUNT];
    struct clause *watch_prev[VAR_COUNT];
} *clauses;

struct clause *watches[VAR_COUNT];

struct assignments_to_do {
    struct assignments_to_do *next, *prev;
    int var;
    char value;
    int unit_prop;
} *assignments_to_do_head, *assignments_to_do_tail;

struct assignment_stack {
    struct assignment_stack *next;
    int var;
    char value;
    char unit_prop;
} *stack;


int solve()
{
    int backtrack = 0;
    while (1) {
        int i, var, value, have_var, prop;
        struct assignments_to_do *todo;
        struct clause *clause;
        have_var = 0;
        if (backtrack) {
            backtrack = 0;
            var = stack->var;
            value = stack->value;
            struct stack *n = stack->next;
            free(stack);
            stack = n;
            have_var = 1;
            assignments[var] = 0;
        } else {
            value = 1;
            for (i = 0; i < VAR_COUNT; ++i) {
                if (assignments[i]==0) {
                    var = i;
                    have_var = 1;
                }
            }
        }
        if (!have_var) return 1;
        todo = malloc(sizeof(struct assignments_to_do));
        todo->next = assignments_to_do_head;
        todo->prev = NULL;
        if (assignments_to_do_tail==NULL) {
            assignments_to_do_tail = todo;
        } else {
            assignments_to_do_head->prev = todo;
        }
        assignments_to_do_head = todo;
        todo->var = var;
        todo->value = value;
        todo->unit_prop = 0;
        printf("***** CHOOSING %d to be %d\n", var, value);
        while (assignments_to_do_tail != NULL) {
            printf("    Processing var %d with value %d\n", assignments_to_do_tail->var, assignments_to_do_tail->value);
            var = assignments_to_do_tail->var;
            value = assignments_to_do_tail->value;
            prop = assignments_to_do_tail->unit_prop;
            if (assignments_to_do_tail->prev==NULL) {
                free(assignments_to_do_tail);
                assignments_to_do_head = NULL;
                assignments_to_do_tail = NULL;
            } else {
                struct assignments_to_do *x = assignments_to_do_tail->prev;
                free(assignments_to_do_tail);
                assignments_to_do_tail = x;
                x->next = NULL;
            }
            if (assignments[var]==0) {
                assignments[var] = value;
                printf("    Setting value\n");
                struct assignment_stack *s = malloc(sizeof(struct assignment_stack));
                s->next = stack;
                stack = s;
                s->var = var;
                s->value = value;
                s->unit_prop = prop;
                struct clause *nc;
                for (clause = watches[var]; clause; clause = nc) {
                    printf("        Processing clause %x\n", clause);
                    nc = clause->watch_next[var];
                    if ((value == 2 && clause->negative_lit[var]) ||
                        (value == 1 && clause->positive_lit[var])) {
                        printf("            Processing watch\n");
                        int j;
                        int non_watch;
                        int has_non_watch = 0;
                        int skip = 0;
                        for (j = 0; j < VAR_COUNT; ++j) {
                            if (clause->positive_lit[j]) {
                                if (assignments[j] == 2) skip = 1;
                            }
                            if (clause->negative_lit[j]) {
                                if (assignments[j] == 1) skip = 1;
                            }
                            if (!assignments[j] && clause->watch_var[j]==0) {
                                non_watch = j;
                                has_non_watch = 1;
                            }
                        }
                        if (skip) {
                            printf("                Case 0: Skipping\n");
                        } else {
                            if (has_non_watch) {
                                printf("                Case 1: moving watch %d %d\n", var, non_watch);
                                clause->watch_next[non_watch] = watches[non_watch];
                                clause->watch_var[non_watch] = 1;
                                if (watches[non_watch]) {
                                    watches[non_watch]->watch_prev[non_watch] = clause;
                                }
                                watches[non_watch] = clause;
                                clause->watch_var[var] = 0;
                                if (clause->watch_prev[var]) {
                                    clause->watch_prev[var]->watch_next[var] = clause->watch_next[var];
                                } else {
                                    watches[var] = clause->watch_next[var];
                                }
                                if (clause->watch_next[var]) {
                                    clause->watch_next[var]->watch_prev[var] = clause->watch_prev[var];
                                }
                            } else {
                                printf("                Case 2: Adding unit prop\n");
                                int k, v, val;
                                for (k = 0; k < VAR_COUNT; ++k) {
                                    if (clause->watch_var[k] && assignments[k]==0) {
                                        v = k;
                                        if (clause->positive_lit[v]) {
                                            val = 2;
                                        }
                                        if (clause->negative_lit[v]) {
                                            val = 1;
                                        }
                                    }
                                }
                                struct assignments_to_do *todo = malloc(sizeof(struct assignments_to_do));
                                todo->next = assignments_to_do_head;
                                todo->prev = NULL;
                                if (assignments_to_do_tail==NULL) {
                                    assignments_to_do_tail = todo;
                                } else {
                                    assignments_to_do_head->prev = todo;
                                }
                                assignments_to_do_head = todo;
                                printf("                Queuing propagation var %d to %d\n", v, val);
                                todo->var = v;
                                todo->value = val;
                                todo->unit_prop = 1;
                            }
                        }
                    }
                }
            } else if (assignments[var] != value) {
                printf("*** Backtracking due to %d with %d ***\n", var, value);
                while (assignments_to_do_head) {
                    todo = assignments_to_do_head->next;
                    free(assignments_to_do_head);
                    assignments_to_do_head = todo;
                }
                assignments_to_do_tail = NULL;
                while (stack && (stack->unit_prop || stack->value==2)) {
                    printf("    dropping %d with value %d prop %d\n", stack->var, stack->value, stack->unit_prop);
                    struct assignment_stack *n = stack->next;
                    assignments[stack->var] = 0;
                    free(stack);
                    stack = n;
                }
                if (stack==NULL) {
                    printf("Back track exit\n");
                    return 0;
                }
                stack->value = 2;
                assignments[stack->var] = 2;
                backtrack = 1;
            }
        }
    }
}

main()
{
    char line[5000];
    
    while (!feof(stdin)) {
        gets(line);
        if (isdigit(line[0]) || line[0]=='-') {
            printf("Adding clause %s\n", line);
            int i;
            struct clause *cl = malloc(sizeof(struct clause));
            printf("Allocating clause %x\n", cl);
            cl->next = clauses;
            clauses = cl;
            for (i = 0; i < VAR_COUNT; ++i) {
                cl->watch_next[i] = NULL;
                cl->watch_prev[i] = NULL;
                cl->watch_var[i] = 0;
                cl->positive_lit[i] = 0;
                cl->negative_lit[i] = 0;
            }
            char *c = line;
            int count = 0;
            while (*c=='-' || isdigit(*c)) {
                int x = atoi(c);
                while (*c=='-' || isdigit(*c)) ++c;
                while (*c==' ') ++c;
                if (x < 0) {
                    x = 0-x;
                    --x;
                    cl->negative_lit[x] = 1;
                } else {
                    --x;
                    cl->positive_lit[x] = 1;
                }
                if (count < 2) {
                    cl->watch_next[x] = watches[x];
                    if (watches[x]) {
                        watches[x]->watch_prev[x] = cl;
                    }
                    watches[x] = cl;
                    cl->watch_var[x] = 1;
                    ++count;
                }
            }
        }
    }
    int i;
    for (i = 0; i < VAR_COUNT; ++i) {
        printf("Watches for %d\n", i);
        struct clause *cl = watches[i];
        while (cl) {
            printf("    %x\n", cl);
            cl = cl->watch_next[i];
        }
    }
    if (solve()) {
        printf("SAT\n");
        int i;
        for (i = 0; i < VAR_COUNT; ++i) {
            printf("var %d is %d\n", i, assignments[i]);
        }
    } else {
        printf("UNSAT\n");
    }
    printf("Done\n");
}


#ifdef XX
invariants:
(* Declare the heap space used by the various data structures *)
TREE(clauses,v0,sizeof(struct clause),[next]) **
TREE(assignments_to_do_head,v1,sizeof(struct assignments_to_do),[next]) **
TREE(stack,v2,sizeof(struct assignment_stack),[next]) **
ARRAY(assignments,v3,VAR_COUNT) **
ARRAY(watches,v4,VAR_COUNT) **
(* Assertions that the stack and assignments array contain the same set
 of assignments *)
forall v5 in TreeRecords(v2),
[nth(v3,(v2,v5)-->var))====(v2,v5)-->value] **
forall v5 in RANGE(0,VAR_COUNT),
([nth(v3,v5)====#0] *\/
                       exists v6 in TreeRecords(v2),
                       [((v2,v6)-->var====v5 //\\
                       (v2,v6)-->value====nth(v3,v5))])
                       (* Assertion defining the prev pointer in the assignments_to_do
                       doubly linked list *)
                       forall v5 in TreeRecords(v1)
                       [(v5,v1)-->prev====#0 //\\ assignments_to_do_head==v5) \\//
                       (v5,v1)-->prev inTree v1 //\\ (v5,(v5,v1)-->prev)-->next====v5)] **
                       foreach v5 in RANGE(0,VAR_COUNT) .
                       (* Define the basic linked list connecting the watch variables
                       inside the clauses linked list *)
                       TreePath nth(v4,v5) sizeof(clause) [watch_next+v5] v0 v6 **
                       (* Define the prev variable (and the fact that if null we are at
                       the head of the list *)
                       forall v7 in v6
                       [(v6,v7)--->(#watch_prev+v5))==#0 //\\ nth(v4,v5)==v6) \\//
                       (v6,(v6,v7)--->(#watch_prev+v5))--->(watch_next+v5))====v7)]
                       foreach v5 in v0
                       (*
                       * make sure that if the watch_var field is non-zero (pointing to
                       * a variable) that watch_next and watch_prev put this clause into
                       * the linked list for the watch variable.
                       *)
                       forall v6 in RANGE(0,VAR_COUNT) .
                       [
                       (not((v0,v5)--->(watch_var++++v6))====#0) //\\
                       (not((v0,v5)--->(watch_prev++++v6)====#0) \\//
                       nth(v4,v6)====v5)) \\//
                       ((v0,v5)--->(watch_var++++v6))====#0 //\\
                       (v0,v5)--->(watch_prev++++v6)====#0 //\\
                       not(nth(v4,v6)====v5))] **
                       (* Make sure there are precisely two watch variables per clause *)
                       sum v6 RANGE(0,VAR_COUNT) ite((v5,v0)--->(watch_var++++v6)),#1,#0) #2 **
                       (* Watch variable invariant--case 1:  All but one variable in the
                       clause are assigned, any watch variable pointing to an assigned
                       variable is pointing to a variable that was assigned after all
                       other assigned variables in the clause.  Also, one of the two
                       watch variables points to the one unassigned variable *)
                       (((sum v6 in RANGE(0,VAR_COUNT) .
                       (((v0,v5)--->(#positive_lit++++v6)) //\\
                       ite(nth(v3,v6)====#1),#1,#0))+
                       (((v0,v5)--->(#negative_lit++++v6)) //\\ nth(v3,v6)====#2)?#1:#0))
                       (* Needs fixing *)
                       == VAR_COUNT-1 **
                       (* The one unassigned literal is a watch *)
                       (forall v6 in RANGE(0,VAR_COUNT)
                       (v0,v5)--->(#watch_var++++v6)>#0 \\//
                       nth(v3,v6)====#0) **
                       forall v6 in RANGE(0,VAR_COUNT), forall v7 in RANGE(0,VAR_COUNT),
                       (v0,v5)--->(#watch_var++++v6) \\//
                       not((v0,v5)--->(#watch_var++++v7)) \\//
                       nth(v3,v6)====#0 \\// nth(v3,v7)====0 \\// v6====v7 \\//
                       exists v8 in v2
                       (v2,v8)-->var==v6 //\\
                       exists v9 in find(v2,v8)
                       (v2,v9)-->var==v7
                       ) *\\//*
                       (* Watch variable invariant case 2: One of the assignments already
                       satisfies the clause, if a watch variable is assigned a value,
                       then that value must be a satisfying assignment or occured
                       after a satisfying assignment *)
                       (exists v6 in RANGE(0,VAR_COUNT) . (v0,v5)--->(#positive_lit++++v6) //\\ nth(v3,v6)==#2 //\\
                       (v0,v5)--->(#negative_lit++++v6) //\\ nth(v3,v6)====#1) //\\
                       (forall v6 in RANGE(0,VAR_COUNT)
                       (v0,v5)--->(watch_var+v6)====#0 \\//
                       exists v7 in v2
                       (v2,v7)-->var==v6 //\\
                       exists v8 in find(v2,v7)
                       (((v0,v5)--->(positive_lit++++(v2,v8)-->var)>0 //\\ (v2,v8)-->value==#2) \\//
                       ((v0,v5)--->(negative_lit++++(v2,v8)-->var)>0 //\\ (v2,v8)-->value==#1)) //\\
                       (* Watch variable invariant case 3: both watch variables point to
                       unassigned variables *)
                       (forall v6 in RANGE(0,VAR_COUNT) . (v0,v5)--->(watch_var+v6)====#0 \\// nth(v3,v6)====0)*/
#endif

