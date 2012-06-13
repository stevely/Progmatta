/*
 * bindgroup.c
 * By Steven Smith
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "depanalyzer.h"

/*
 * Here we create the initial bind groups. This just bundles up assignments and
 * type signatures for the same bind into individual binds and bind groups.
 */

/*
 * Simple symbol table used to generate initial bind groups.
 */
typedef struct sym_table {
    char *id;
    token *tok;
    struct sym_table *next;
} sym_table;

static sym_table * new_symbol( char *id, token *tok ) {
    sym_table *result;
    result = (sym_table*)malloc(sizeof(sym_table));
    result->id = id;
    result->tok = tok;
    result->next = NULL;
    return result;
}

static void free_sym_table( sym_table *tbl ) {
    sym_table *next;
    if( tbl ) {
        next = tbl->next;
        free(tbl);
        free_sym_table(next);
    }
}

/*
 * Checks to see if the ident of the given token exists in the symbol table.
 * If it does, returns the corresponding token.
 * If it doesn't, returns NULL.
 */
static token * lookup_symbol( sym_table *tbl, token *tree ) {
    char *id;
    id = tree->lhs->value.s;
    while( tbl ) {
        /* Found match */
        if( tbl->id && strcmp(tbl->id, id) == 0 ) {
            return tbl->tok;
        }
        else {
            tbl = tbl->next;
        }
    }
    return NULL;
}

/*
 * Checks that the ident of the given token already exists in the symbol table.
 * If it does, it will be inserted with the entry's bind.
 * If it doesn't, a new entry will be created for it.
 */
static void insert_symbol( sym_table *tbl, token *tree ) {
    token *t, *bg;
    if( !tree ) {
        return;
    }
    t = lookup_symbol(tbl, tree);
    /* Symbol already exists */
    if( t ) {
        if( t->lhs ) {
            t = t->lhs->lhs;
        }
        else {
            t = t->rhs->lhs;
        }
        /* Insert at end of the bind */
        while( t->next ) {
            t = t->next;
        }
        t->next = tree;
    }
    /* Symbol doesn't exist, have to insert into table */
    else {
        /* Since this is an assign, we can assume it's an implicit bind. If an
           explicit bind shows up later, we'll catch it and raise an error. */
        /* Bind group */
        bg = (token*)malloc(sizeof(token));
        bg->type = tok_Bindgroup;
        bg->rhs  = NULL;
        bg->next = NULL;
        bg->line_number = tree->line_number;
        /* Bind */
        bg->lhs = (token*)malloc(sizeof(token));
        t = bg->lhs;
        t->type    = tok_Bind;
        t->lhs     = tree;
        t->rhs     = NULL;
        t->next    = NULL;
        t->value.s = tree->lhs->value.s;
        t->line_number = tree->line_number;;
        /* Insert into symbol table */
        while( tbl->next ) {
            tbl = tbl->next;
        }
        tbl->next = new_symbol(t->value.s, bg);
    }
}

/*
 * Creates a new entry in the symbol table for an explicit bind. This skips the
 * lookup (as it will already be done) and inserts on the bind group's RHS to
 * signify that this is an explicit bind.
 */
static void insert_expl_symbol( sym_table *tbl, token *tree ) {
    token *t, *bg;
    if( !tree ) {
        return;
    }
    /* Bind group */
    bg = (token*)malloc(sizeof(token));
    bg->type = tok_Bindgroup;
    bg->lhs  = NULL;
    bg->next = NULL;
    bg->line_number = tree->line_number;
    /* Bind */
    bg->rhs = (token*)malloc(sizeof(token));
    t = bg->rhs;
    t->type    = tok_Bind;
    t->lhs     = tree;
    t->rhs     = NULL;
    t->next    = NULL;
    t->value.s = tree->lhs->value.s;
    t->line_number = tree->line_number;
    /* Insert into symbol table */
    while( tbl->next ) {
        tbl = tbl->next;
    }
    tbl->next = new_symbol(t->value.s, bg);
}

/*
 * Generates the resulting program from the given symbol table. This involves
 * merging the bind groups into a single tree, then merging all the explicit
 * binds into a single bind group at the head of the list.
 */
static token * generate_tree_from_table( sym_table *tbl ) {
    token *tree, *t, *t2, *t3, *temp;
    tree = NULL;
    /* Step 1: Merge trees from symbol table */
    while( tbl ) {
        if( !tree ) {
            tree = tbl->tok;
            t = tbl->tok;
        }
        else {
            t->next = tbl->tok;
            t = t->next;
        }
        tbl = tbl->next;
    }
    /* Step 2: Merge explicit binds into the first bind group's RHS */
    t = tree;
    t2 = t;
    /* Find first explicit bind group */
    /* If it's the first bind, then we don't do anything */
    if( t2 && t2->lhs ) {
        while( t2->next ) {
            /* Is it an explicit bind? */
            if( t2->next->rhs ) {
                /* Move t2->next to the head of the tree */
                t3 = t2->next->next;
                t2->next->next = tree;
                tree = t2->next;
                t2->next = t3;
                break;
            }
            t2 = t2->next;
        }
    }
    else if( t2 && t2->rhs ) {
        t2 = t2->next;
    }
    /* Found an explicit bind group */
    if( tree && tree->rhs ) {
        t3 = tree;
        /* Find remaining explicit bind groups */
        while( t2 ) {
            if( t2->rhs ) {
                t3->next = t2->rhs;
                t3 = t3->next;
                /* Have to free the merged bind group */
                temp = t2;
                t2 = t2->next;
                free(temp);
            }
            else {
                t2 = t2->next;
            }
        }
    }
    return tree;
}

/* Forward declaration */
static token * gen_bindgroups( token *tree );

/*
 * We need to find any let binds and generate bind groups for them.
 */
static void search_for_lets( token *tree ) {
    if( !tree ) {
        return;
    }
    if( tree->type == tok_letexpr ) {
        tree->lhs = gen_bindgroups(tree->lhs);
    }
    /* We want to skip checking the LHS if we have a letexpr since we'll do it
       as part of generating the bind groups. */
    else if( tree->lhs ) {
        search_for_lets(tree->lhs);
    }
    if( tree->rhs ) {
        search_for_lets(tree->rhs);
    }
    if( tree->next ) {
        search_for_lets(tree->next);
    }
}

/*
 * Generate initial bind groups. This simply groups up assignments with
 * identical binds and puts them into bind groups/binds. This preps the tree for
 * the actual dependency analysis performed afterwards.
 */
static token * gen_bindgroups( token *tree ) {
    token *t, *next;
    sym_table *tbl;
    if( !tree ) {
        return NULL;
    }
    /* Insert dummy value as head of symbol table to simplify logic */
    tbl = new_symbol(NULL, NULL);
    while( tree ) {
        /* Clear the next field so we can reorganize later */
        next = tree->next;
        tree->next = NULL;
        /* Declarations */
        if( tree->type == tok_Assign ) {
            insert_symbol(tbl, tree);
            search_for_lets(tree->rhs);
        }
        /* Type declarations */
        else if( tree->type == tok_Typesig || tree->type == tok_Kernel ) {
            t = lookup_symbol(tbl, tree);
            /* Type sigs must appear before declarations. If the symbol already
               exists in the symbol table, then it's an error. */
            if( t ) {
                printf("ERROR: Type signature for \"%s\" already exists! "
                       "Original found on line %d, second found on line %d.\n",
                       tbl->id, t->line_number, tree->line_number);
                return NULL;;
            }
            else {
                insert_expl_symbol(tbl, tree);
            }
        }
        else {
            printf("ERROR: Invalid top-level declaration on line number %d!\n",
                   tree->line_number);
        }
        /* Grab the next token */
        tree = next;
    }
    tree = generate_tree_from_table(tbl);
    free_sym_table(tbl);
    return tree;
}

/*
 * Separate the imports/exports from the tree, then generate the initial bind groups.
 */
program * generate_initial_bg( token *tree ) {
    token *tr, *t, *next;
    program *prog;
    if( !tree ) {
        return NULL;
    }
    prog = (program*)malloc(sizeof(program));
    prog->expl    = NULL;
    prog->impl    = NULL;
    prog->tree    = NULL;
    prog->imports = NULL;
    prog->exports = NULL;
    /* Grab leading imports/exports */
    while( tree ) {
        next = tree->next;
        if( tree->type == tok_Import ) {
            tree->next = NULL;
            if( !prog->imports ) {
                prog->imports = tree;
            }
            else {
                /* Find the end of the imports list */
                for( t = prog->imports; t->next; t = t->next );
                t->next = tree;
            }
        }
        else if( tree->type == tok_Export ) {
            tree->next = NULL;
            if( !prog->imports ) {
                prog->imports = tree;
            }
            else {
                /* Find the end of the imports list */
                for( t = prog->imports; t->next; t = t->next );
                t->next = tree;
            }
        }
        else {
            break;
        }
        tree = next;
    }
    /* Grab remaining imports/exports */
    tr = tree;
    if( tr ) {
        while( tr->next ) {
            next = tr->next->next;
            /* Imports */
            if( tr->next->type == tok_Import ) {
                tr->next->next = NULL;
                if( !prog->imports ) {
                    prog->imports = tr->next;
                }
                else {
                    /* Find the end of the imports list */
                    for( t = prog->imports; t->next; t = t->next );
                    t->next = tr->next;
                }
                tr->next = next;
            }
            /* Exports */
            else if( tr->next->type == tok_Export ) {
                tr->next->next = NULL;
                if( !prog->exports ) {
                    prog->exports = tr->next;
                }
                else {
                    /* Find the end of the imports list */
                    for( t = prog->exports; t->next; t = t->next );
                    t->next = tr->next;
                }
                tr->next = next;
            }
            tr = tr->next;
        }
    }
    prog->tree = gen_bindgroups(tree);
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
    if( prog->tree ) {
        printf("<Bindings>\n");
        printtree(prog->tree);
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
