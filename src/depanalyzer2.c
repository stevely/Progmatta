/*
 * depanalyzer2.c
 * By Steven Smith
 */

#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "depanalyzer.h"

/*
 * Here we perform dependency analysis on our bind groups. This achieves two
 * things:
 * 1) It orders the groups such that no bind group references a symbol declared
 *    in a later bind group. This allows type inference to be performed on binds
 *    independently, since binds can only referencing earlier binds which have
 *    already had type inference performed on them. This helps guarantee the
 *    most general types are generated.
 * 2) Mutually-recursive groups are merged. Again, this is to maintain bind
 *    independence. Mutually-recursive groups obviously can't have type
 *    inference performed on them independently (assuming none of the binds are
 *    explicitly typed), but if we only merge mutually-recursive groups we can
 *    maintain independence from the rest of the binds.
 */

/*
 * Step 1: Generate dependency lists.
 */

#define streq(a,b) (strcmp(a,b) == 0)

/*
 * Lookup a Bind token with equivalent ident as the given token. Returns NULL on
 * lookup failure (doesn't exist).
 */
static token * token_lookup( token *binds, token *tok ) {
    while( binds ) {
        if( strcmp(binds->value.s, tok->value.s) == 0 ) {
            return binds;
        }
        binds = binds->next;
    }
    return NULL;
}

/*
 * Lookup a dependency with equivalent ident as the given token. Returns NULL
 * on lookup failure (doesn't exist).
 */
static dep_list_item * dep_lookup( dep_list *deps, token *tok ) {
    dep_list_item *item;
    item = deps->dl;
    while( item ) {
        if( strcmp(item->ident, tok->value.s) == 0 ) {
            return item;
        }
        item = item->next;
    }
    return NULL;
}

static dep_list_item * new_dep_list_item( char *id ) {
    dep_list_item *result;
    result = (dep_list_item*)malloc(sizeof(dep_list_item));
    result->next = NULL;
    result->ident = id;
    return result;
}

/*
 * Traverses the given tree for potential dependencies. Assumes the program is
 * given as a Bindgroup. Only top level binds that are not explicitly typed are
 * candidates for being dependencies.
 */
static void traverse_tree_for_deps( token *prog, token *tree, dep_list *deps,
    int level ) {
    dep_list_item *item;
    if( !tree ) {
        return;
    }
    /* Simple tree traversal */
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
        traverse_tree_for_deps(prog, tree->lhs, deps, level);
        traverse_tree_for_deps(prog, tree->next, deps, level);
    }
    else if( tree->type == tok_Assign ) {
        traverse_tree_for_deps(prog, tree->rhs, deps, level+2);
    }
    else if( tree->type == tok_Case ) {
        traverse_tree_for_deps(prog, tree->rhs, deps, level+1);
    }
    else if( tree->type == tok_Bindgroup ) {
        traverse_tree_for_deps(prog, tree->lhs, deps, level);
        traverse_tree_for_deps(prog, tree->rhs, deps, level);
        traverse_tree_for_deps(prog, tree->next, deps, level);
    }
    /* Idents = potential dependencies */
    else if( tree->type == tok_ident) {
        /* Index = level -> top-level bind */
        if( tree->index == level ) {
            /* Only worry about dependencies if it's not simple recursion */
            if( strcmp(tree->value.s, deps->ident->ident) != 0 ) {
                /* Skip if the bind already exists in the dependency list or
                   if it is an explicit bind */
                if( !dep_lookup(deps, tree)
                 && !token_lookup(prog->rhs, tree) ) {
                    /* Can we add it to the dependency list? */
                    if( deps->dl ) {
                        /* Find last item in the list */
                        for( item = deps->dl; item->next; item = item->next );
                        item->next = new_dep_list_item(tree->value.s);
                    }
                    else {
                        deps->dl = new_dep_list_item(tree->value.s);
                    }
                }
            }
        }
    }
}

static dep_list * generate_deps( token *tree ) {
    dep_list *dl, *dl2;
    token *t;
    dl = NULL;
    t = tree;
    /* Skip explicit bind group */
    if( t->rhs ) {
        t = t->next;
    }
    while( t ) {
        /* Create our dependency list */
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
        dl->ident = new_dep_list_item(t->lhs->value.s);
        traverse_tree_for_deps(tree, t->lhs, dl, 0);
        t = t->next;
    }
    return dl;
}

dep_list * generate_dependency_list( program *prog ) {
    return generate_deps(prog->tree);
}

/*
 * Step 2: Perform the dependency analysis. This involves performing a depth-
 * first search on the dependency graph produces by the dependency list.
 * A callstack is maintained in order to detect loops. If a loop is detected,
 * the binding groups involved are merged and the search restarted.
 */

typedef struct callstack {
    char *id;
    struct callstack *prev;
} callstack;

static callstack * add_to_callstack( callstack *cs, dep_list *deps ) {
    callstack *result;
    result = (callstack*)malloc(sizeof(callstack));
    result->id   = deps->ident->ident;
    result->prev = cs;
    return result;
}

static int in_callstack( callstack *cs, dep_list *dep ) {
    dep_list_item *i;
    while( cs ) {
        for( i = dep->ident; i; i = i->next ) {
            if( strcmp(cs->id, i->ident) == 0 ) {
                return 1;
            }
        }
        cs = cs->prev;
    }
    return 0;
}

static callstack * pop_callstack( callstack *cs ) {
    callstack *result;
    if( cs ) {
        result = cs->prev;
        free(cs);
        return result;
    }
    else {
        return NULL;
    }
}

static token * add_to_tree( token *tree, token *tok ) {
    token *t;
    if( !tree ) {
        /* Next field is unused for dependency analysis, so we can destructively
           update it */
        tok->next = NULL;
        return tok;
    }
    /* Find end of the list */
    for( t = tree; t->next; t = t->next );
    t->next = tok;
    tok->next = NULL;
    return tree;
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

static dep_list * dep_lookup_s( dep_list *list, char *id ) {
    dep_list_item *i;
    while( list ) {
        for( i = list->ident; i; i = i->next ) {
            if( strcmp(i->ident, id) == 0 ) {
                return list;
            }
        }
        list = list->prev;
    }
    return NULL;
}

static callstack * merge_callstack( callstack *cs, dep_list *list ) {
    dep_list *d1, *d2;
    dep_list_item *i1, *i2, *i3, *last;
    token *tok;
    d1 = dep_lookup_s(list, cs->prev->id);
    d2 = dep_lookup_s(list, cs->id);
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
            }
            else {
                for( i3 = d1->dl; i3->next != i1; i3 = i3->next );
                i3->next = i1->next;
            }
            free(i1);
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
    return pop_callstack(cs);
}

static dep_list * analyze_deps( dep_list *dep, dep_list *full_list,
    token **tree, callstack **cs, jmp_buf jump_buf ) {
    dep_list_item *d;
    dep_list *d2, *d3;
    if( in_callstack(*cs, dep) ) {
        return dep;
    }
    else {
        if( dep->visited ) {
            return NULL;
        }
        *cs = add_to_callstack(*cs, dep);
        for( d = dep->dl; d; d = d->next ) {
            d2 = find_dep(d, full_list);
            if( d2 == NULL ) {
                fprintf(stderr, "Undeclared value: %s\n", d->ident);
                continue;
            }
            d3 = analyze_deps(d2, full_list, tree, cs, jump_buf);
            if( d3 ) {
                d = d3->ident;
                *cs = merge_callstack(*cs, full_list);
                d3 = find_dep(d, full_list);
                if( dep_lookup_s(d3, (*cs)->id) ) {
                    return d3;
                }
                else {
                    while( *cs ) {
                        *cs = pop_callstack(*cs);
                    }
                    longjmp(jump_buf, 1);
                    return NULL;
                }
            }
        }
        dep->visited = 1;
        *tree = add_to_tree(*tree, dep->tok);
        *cs = pop_callstack(*cs);
        return NULL;
    }
}

static token * perform_dep_analysis( dep_list *deps ) {
    dep_list *d;
    callstack *cs;
    token *tree;
    jmp_buf jump_buf;
    cs = NULL;
    d = deps;
    tree = NULL;
    while( d ) {
        if( !d->visited ) {
            /* analyze_deps() will either succeed, in which case nothing will
               happen, or a loop will be detected and longjmp() will be called
               to bring us back here with a non-zero value. */
            if( !setjmp(jump_buf) ) {
                analyze_deps(d, deps, &tree, &cs, jump_buf);
            }
            /* Loop detected, longjmp() called */
            else {
                /* Restart dependency analysis (visited flag isn't cleared) */
                d = deps;
            }
        }
        else {
            d = d->prev;
        }
    }
    return tree;
}

program * perform_dependency_analysis( program *prog ) {
    dep_list *deps;
    /* Step 1: Generate dependency list */
    deps = generate_dependency_list(prog);
    printdeplist(deps); /* For debugging purposes */
    /* Step 2: Perform the dependency analysis */
    prog->tree = perform_dep_analysis(deps);
    /* Step 3: Free dependency lists */
    free_dep_list(deps);
    return prog;
}
