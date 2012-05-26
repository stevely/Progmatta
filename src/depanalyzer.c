/*
 * depanalyzer.c
 * By Steven Smith
 */

#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "depanalyzer.h"

/*
 * Step 1: Create initial binding groups
 *
 * This involves grouping up all identically named bindings and all explicitly
 * typed bindings.
 */

/*
 * Checks for the ident in the given tree already existing in the given
 * program. If it already exists it will be placed with its corresponding
 * bind, otherwise a new bind will be created for it.
 */
static void check_for_match( program *prog, token *tree ) {
    token *t, *bg;
    if( !prog || !tree ) {
        return;
    }
    /* Check explicit group first */
    if( prog->expl ) {
        /* Check for equivalent idents */
        for( t = prog->expl->lhs; t; t = t->next ) {
            /* Check for match */
            if( strcmp(t->value.s, tree->lhs->value.s) == 0 ) {
                /* Insert the token into the end of its bind */
                t = t->lhs;
                while( t->next ) {
                    t = t->next;
                }
                t->next = tree;
                return;
            }
        }
    }
    /* Check implicit groups next */
    if( prog->impl ) {
        /* Slightly trickier for implicit binds due to multiple bind groups */
        for( bg = prog->impl; bg; bg = bg->next  ) {
            for( t = bg->lhs; t; t = t->next ) {
                /* Check for match */
                if( strcmp(t->value.s, tree->lhs->value.s) == 0 ) {
                    /* Insert the token into the end of its bind */
                    t = t->lhs;
                    while( t->next ) {
                        t = t->next;
                    }
                    t->next = tree;
                    return;
                }
            }
        }
    }
    /* Failed to find it, create new implicit bindgroup */
    bg = (token*)malloc(sizeof(token));
    bg->type = tok_Bindgroup;
    bg->rhs = NULL;
    bg->next = NULL;
    bg->line_number = tree->line_number;
    /* Bind */
    bg->lhs = (token*)malloc(sizeof(token));
    bg->lhs->type = tok_Bind;
    bg->lhs->lhs = tree;
    bg->lhs->rhs = NULL;
    bg->lhs->next = NULL;
    bg->lhs->line_number = tree->line_number;
    bg->lhs->value.s = tree->lhs->value.s;
    /* Insert new bindgroup */
    if( !prog->impl ) {
        prog->impl = bg;
    }
    else {
        /* Find last bindgroup */
        for( t = prog->impl; t->next; t = t->next );
        t->next = bg;
    }
}

program * generate_initial_bg( token *tree ) {
    program *prog;
    token *t, *t2;
    if( !tree ) {
        return NULL;
    }
    prog = (program*)malloc(sizeof(program));
    prog->expl = NULL;
    prog->impl = NULL;
    prog->imports = NULL;
    prog->exports = NULL;
    while( tree ) {
        /* Clear the next field so we can reorganize later */
        t = tree->next;
        tree->next = NULL;
        /* Implicit binds */
        if( tree->type == tok_Assign ) {
            check_for_match(prog, tree);
        }
        /* Explicit binds */
        else if( tree->type == tok_Typesig || tree->type == tok_Kernel ) {
            if( !prog->expl ) {
                prog->expl = (token*)malloc(sizeof(token));
                prog->expl->type = tok_Bindgroup;
                prog->expl->rhs = NULL;
                prog->expl->next = NULL;
                prog->expl->line_number = tree->line_number;
                /* Bind */
                prog->expl->lhs = (token*)malloc(sizeof(token));
                prog->expl->lhs->type = tok_Bind;
                prog->expl->lhs->lhs = tree;
                prog->expl->lhs->rhs = NULL;
                prog->expl->lhs->next = NULL;
                prog->expl->lhs->line_number = tree->line_number;
                prog->expl->lhs->value.s = tree->lhs->value.s;
            }
            else {
                /* Need to check to make sure this is the only sig for this ident */
                t2 = prog->expl->lhs;
                while( t2 ) {
                    if( strcmp(t2->lhs->value.s, tree->lhs->value.s) == 0 ) {
                        printf("ERROR: Declaration for \"%s\" found preceding "
                            "type signature!\n", t2->lhs->value.s);
                        printf(" Line number %d (originally found on line %d.\n",
                            tree->line_number, t2->line_number);
                        goto gib_end;
                    }
                    /* Skip the incrementor for the last item */
                    if( t2->next ) {
                        t2 = t2->next;
                    }
                    else {
                        break;
                    }
                }
                /* All good, add it to the end of the explicit binding group */
                if( t2 ) {
                    t2->next = (token*)malloc(sizeof(token));
                    t2->next->type = tok_Bind;
                    t2->next->lhs = tree;
                    t2->next->rhs = NULL;
                    t2->next->next = NULL;
                    t2->next->line_number = tree->line_number;
                    t2->next->value.s = tree->lhs->value.s;
                }
                else {
                    printf("ERROR: Hit an impossible NULL!\n");
                }
            }
        }
        else if( tree->type == tok_Import ) {
            if( !prog->imports ) {
                prog->imports = tree;
            }
            else {
                /* Find the end of the imports list */
                for( t2 = prog->imports; t2->next; t2 = t2->next );
                t2->next = tree;
            }
        }
        else if( tree->type == tok_Export ) {
            if( !prog->exports ) {
                prog->exports = tree;
            }
            else {
                /* Find the end of the exports list */
                for( t2 = prog->exports; t2->next; t2 = t2->next );
                t2->next = tree;
            }
        }
        else {
            printf("ERROR: Invalid top-level declaration on line number %d!\n",
                tree->line_number);
        }
        /* Short for "generate_initial_bindgroups end", if you were wondering */
        gib_end:
        /* Grab the next token */
        tree = t;
    }
    return prog;
}

/*
 * Step 2: Generate dependency lists. Dependency lists are simply linked-lists
 * of identifiers, where the first identifier is the binding and the following
 * identifiers are the dependencies. Identifiers found to be declared in the
 * explicitly-typed bind group will be ignored.
 */

static void traverse_tree_for_deps( program *prog, token *tree, dep_list *deps,
    int level ) {
    dep_list_item *item;
    token *t;
    for( ; tree; tree = tree->next ) {
        if( tree->type == tok_parens || tree->type == tok_brackets ) {
            traverse_tree_for_deps(prog, tree->lhs, deps, level);
        }
        else if( tree->type == tok_letexpr ) {
            traverse_tree_for_deps(prog, tree->lhs, deps, level+1);
            traverse_tree_for_deps(prog, tree->rhs, deps, level+2);
        }
        else if( tree->type == tok_lamexpr ) {
            traverse_tree_for_deps(prog, tree->rhs, deps, level+1);
        }
        else if( tree->type == tok_caseexpr ) {
            traverse_tree_for_deps(prog, tree->lhs, deps, level);
            traverse_tree_for_deps(prog, tree->rhs, deps, level);
        }
        else if( tree->type == tok_Bind ) {
            for( t = tree->lhs; t; t = t->next ) {
                traverse_tree_for_deps(prog, t, deps, level);
            }
        }
        else if( tree->type == tok_Assign ) {
            traverse_tree_for_deps(prog, tree->rhs, deps, level+2);
        }
        else if( tree->type == tok_Case ) {
            traverse_tree_for_deps(prog, tree->rhs, deps, level+1);
        }
        else if( tree->type == tok_ident ) {
            if( tree->index == level ) {
                /* Recursion check */
                if( strcmp(tree->value.s, deps->ident->ident) != 0 ) {
                    /* Dependency already in list check */
                    for( item = deps->dl; item; item = item->next ) {
                        if( strcmp(tree->value.s, item->ident) == 0 ) {
                            goto ttfd_fdil;
                        }
                    }
                    /* Dependency in explicitly-typed list */
                    if( prog->expl ) {
                        for( t = prog->expl->lhs; t; t = t->next ) {
                            if( strcmp(t->value.s, tree->value.s) == 0 ) {
                                goto ttfd_fdil;
                            }
                        }
                    }
                    /* Can add to the dependency list */
                    if( deps->dl ) {
                        /* Find last item in list */
                        for( item = deps->dl; item->next; item = item->next );
                        item->next = (dep_list_item*)malloc(sizeof(dep_list_item));
                        item->next->next = NULL;
                        item->next->ident = tree->value.s;
                    }
                    else {
                        deps->dl = (dep_list_item*)malloc(sizeof(dep_list_item));
                        deps->dl->next = NULL;
                        deps->dl->ident = tree->value.s;
                    }
                }
                /* traverse_tree_for_deps, found dependency in list */
                ttfd_fdil:
                continue;
            }
        }
    }
}

dep_list * generate_dependency_list( program *prog ) {
    dep_list *dl = NULL;
    dep_list *dl2;
    token *t, *t2;
    for( t = prog->impl; t; t = t->next ) {
        if( t->type == tok_Bindgroup && t->lhs->type == tok_Bind ) {
            if( dl ) {
                dl2 = (dep_list*)malloc(sizeof(dep_list));
                dl2->prev = dl;
                dl = dl2;
            }
            else {
                dl = (dep_list*)malloc(sizeof(dep_list));
                dl->prev = NULL;
            }
            dl->tok = t;
            dl->dl = NULL;
            dl->visited = 0;
            dl->ident = (dep_list_item*)malloc(sizeof(dep_list_item));
            dl->ident->next = NULL;
            dl->ident->ident = t->lhs->value.s;
            for( t2 = t->lhs->lhs; t2; t2 = t2->next ) {
                traverse_tree_for_deps(prog, t2, dl, 0);
            }
        }
        else {
            printf("ERROR! Failed to find a top-level declaration on line number %d!\n",
                t->line_number);
            free_dep_list(dl);
            return NULL;
        }
    }
    return dl;
}

/*
 * Step 3: Perform the dependency analysis. This involves performing a depth-
 * first search on the dependency graph produced by the dependency lists.
 * A callstack is maintained in order to detect loops. If a loop is detected,
 * the binding groups involved are merged and the search restarted..
 */

typedef struct callstack {
    dep_list *deps;
    struct callstack *prev;
} callstack;

typedef struct ordered_bgs {
    token *bg;
    struct ordered_bgs *prev;
} ordered_bgs;

static callstack *cs = NULL;
static ordered_bgs *obgs = NULL;
static ordered_bgs *obgs_last = NULL;

static void add_to_callstack( dep_list *deps ) {
    callstack *new_stack = (callstack*)malloc(sizeof(callstack));
    new_stack->deps = deps;
    new_stack->prev = cs;
    cs = new_stack;
}

static int in_callstack( dep_list *dep ) {
    callstack *stack;
    for( stack = cs; stack; stack = stack->prev ) {
        if( stack->deps == dep ) {
            return 1;
        }
    }
    return 0;
}

static void pop_callstack() {
    callstack *stack = cs;
    if( cs ) {
        cs = cs->prev;
        free(stack);
    }
}

static void add_to_dep_list( token *tok ) {
    ordered_bgs *o = (ordered_bgs*)malloc(sizeof(ordered_bgs));
    o->bg = tok;
    o->prev = NULL;
    if( !obgs ) {
        obgs = o;
    }
    else {
        obgs_last->prev = o;
    }
    obgs_last = o;
}

static dep_list * find_dep( dep_list_item *dep, dep_list *list ) {
    dep_list_item *d;
    for( ; list; list = list->prev ) {
        for( d = list->ident; d; d = d->next ) {
            if( strcmp(d->ident, dep->ident) == 0 ) {
                return list;
            }
        }
    }
    return NULL;
}

static void merge_callstack( dep_list *list ) {
    dep_list *d1, *d2;
    dep_list_item *i1, *i2, *i3, *last;
    token *tok;
    d1 = cs->prev->deps;
    d2 = cs->deps;
    /* We merge into d1, so if d2 is the top of the list we have to swap them */
    if( list == d2 ) {
        d2 = d1;
        d1 = list;
    }
    /* Step 1: Merge ident lists */
    for( i1 = d1->ident; i1->next; i1 = i1->next );
    i1->next = d2->ident;
    /* Step 2: Merge dependencies */
    for( i1 = d1->dl; i1->next; i1 = i1->next );
    last = i1;
    i1 = NULL;
    i2 = d2->dl;
    while( i2 ) {
        for( i1 = d1->dl; i1; i1 = i1->next ) {
            /* Check for duplicates */
            if( strcmp(i1->ident, i2->ident) == 0 ) {
                break;
            }
        }
        /* Dupe found */
        if( i1 ) {
            i2 = i2->next;
        }
        else {
            last->next = i2;
            last = last->next;
            i2 = i2->next;
            last->next = NULL;
        }
    }
    /* Step 2b: Remove dependencies found in ident list */
    for( i2 = d1->ident; i2; i2 = i2->next ) {
        for( i1 = d1->dl; i1; i1 = i1->next ) {
            /* Check for dependencies in ident list */
            if( strcmp(i1->ident, i2->ident) == 0 ) {
                break;
            }
        }
        /* Bad dependency found */
        if( i1 ) {
            /* Check for head of the list */
            if( i1 == d1->dl ) {
                d1->dl = i1->next;
                free(i1);
            }
            else {
                for( i3 = d1->dl; i3->next != i1; i3 = i3->next );
                i3->next = i1->next;
                free(i1);
            }
        }
    }
    /* Step 3: Merge tokens */
    for( tok = d1->tok->lhs; tok->next; tok = tok->next );
    tok->next = d2->tok->lhs;
    /* Step 4: Remove d2 from list */
    for( ; list->prev != d2; list = list->prev );
    list->prev = d2->prev;
    free(d2->tok);
    free(d2);
    /* Step 5: Clear visited flag */
    d1->visited = 0;
    /* Step 6: Pop stack */
    pop_callstack();
}

static jmp_buf jump_buf;

static dep_list * analyze_deps( dep_list *dep, dep_list *full_list ) {
    dep_list_item *d;
    dep_list *d2, *d3;
    if( in_callstack(dep) ) {
        return dep;
    }
    else {
        if( dep->visited ) {
            return NULL;
        }
        add_to_callstack(dep);
        for( d = dep->dl; d; d = d->next ) {
            d2 = find_dep(d, full_list);
            if( d2 == NULL ) {
                fprintf(stderr, "Undeclared value: %s\n", d->ident);
                continue;
            }
            d3 = analyze_deps(d2, full_list);
            if( d3 ) {
                d = d3->ident;
                merge_callstack(full_list);
                d3 = find_dep(d, full_list);
                if( d3 != cs->deps ) {
                    return d3;
                }
                else {
                    while( cs ) {
                        pop_callstack();
                    }
                    longjmp(jump_buf, 1);
                    return NULL;
                }
            }
        }
        dep->visited = 1;
        add_to_dep_list(dep->tok);
        pop_callstack();
        return NULL;
    }
}

static void perform_dep_analysis( dep_list *deps ) {
    dep_list *d;
    d = deps;
    while( d ) {
        if( !d->visited ) {
            if( !setjmp(jump_buf) ) {
                analyze_deps(d, deps);
            }
            else {
                /* Reset loop due to finding a dependency loop */
                d = deps;
            }
        }
        else {
            d = d->prev;
        }
    }
}

program * perform_dependency_analysis( program *prog ) {
    ordered_bgs *o;
    token *tok, *tok_end;
    dep_list *deps;
    /* Step 1: Generate dependency list */
    deps = generate_dependency_list(prog);
    printdeplist(deps);
    /* Step 2: Perform the dependency analysis */
    perform_dep_analysis(deps);
    /* Step 3: Merge the binding groups back into a single tree */
    tok = tok_end = NULL;
    while( obgs ) {
        if( tok ) {
            tok_end->next = obgs->bg;
            tok_end = tok_end->next;
        }
        else {
            tok = tok_end = obgs->bg;
        }
        o = obgs;
        obgs = obgs->prev;
        free(o);
    }
    if( tok_end ) {
        tok_end->next = NULL;
    }
    prog->impl = tok;
    free_dep_list(deps);
    while( cs ) {
        pop_callstack();
    }
    return prog;
}

/*
 * Utility functions
 */

void printprog( program *prog ) {
    if( !prog ) {
        return;
    }
    if( prog->imports ) {
        printf("<Imports>\n");
        printtree(prog->imports);
        printf("\n");
    }
    if( prog->exports ) {
        printf("<Exports>\n");
        printtree(prog->exports);
        printf("\n");
    }
    if( prog->expl ) {
        printf("<Explicit Bindings>\n");
        printtree(prog->expl);
        printf("\n");
    }
    if( prog->impl ) {
        printf("<Implicit Bindings>\n");
        printtree(prog->impl);
        printf("\n");
    }
}

void free_program( program *prog ) {
    if( !prog ) {
        return;
    }
    if( prog->imports ) {
        free_token_tree(prog->imports);
    }
    if( prog->exports ) {
        free_token_tree(prog->exports);
    }
    if( prog->expl ) {
        free_token_tree(prog->expl);
    }
    if( prog->impl ) {
        free_token_tree(prog->impl);
    }
    free(prog);
}

void printdeplist( dep_list *dl ) {
    dep_list_item *i;
    while( dl ) {
        i = dl->ident;
        while( i ) {
            if( i->next ) {
                printf("%s ", i->ident);
            }
            else {
                printf("%s: ", i->ident);
            }
            i = i->next;
        }
        i = dl->dl;
        while( i ) {
            printf("%s ", i->ident);
            i = i->next;
        }
        printf("\n");
        dl = dl->prev;
    }
}

void free_dep_list( dep_list *dl ) {
    dep_list_item *i1, *i2;
    dep_list *dl2;
    while( dl ) {
        i1 = dl->ident;
        while( i1 ) {
            i2 = i1;
            i1 = i1->next;
            free(i2);
        }
        i1 = dl->dl;
        while( i1 ) {
            i2 = i1;
            i1 = i1->next;
            free(i2);
        }
        dl2 = dl;
        dl = dl->prev;
        free(dl2);
    }
}
