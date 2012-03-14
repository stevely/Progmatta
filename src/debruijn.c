/*
 * debruijn.c
 * By Steven Smith
 */

#include <stdlib.h>
#include <string.h>
#include "debruijn.h"

/*
 * Step 1: Generate de Bruijn indices
 *
 * De Bruijn indices simplify the process of generating dependencies by marking
 * how many binding scopes back an identifier is declared.
 */

typedef struct enviro {
    struct enviro *parent;
    struct enviro *next;
    char *val;
    int index;
} enviro;

enviro *env = NULL;

static enviro * new_enviro( enviro *parent, enviro *next, char *val, int index ) {
    enviro *new = (enviro*)malloc(sizeof(enviro));
    if( !new ) {
        printf("Failed to malloc enviro!\n");
        return NULL;
    }
    else {
        new->parent = parent;
        new->next = next;
        new->val = val;
        new->index = index;
        return new;
    }
}

static void insert_into_enviro( char *ident, int level ) {
    enviro *e;
    if( !env ) {
        env = new_enviro(NULL, NULL, ident, level);
    }
    else {
        if( env->index != level ) {
            e = new_enviro(env, NULL, ident, level);
            env = e;
        }
        else if( env->index == level ) {
            for( e = env; e->next; e = e->next );
            e->next = new_enviro(e->parent, NULL, ident, level);
        }
        else {
            printf("ERROR! Tried to insert ident %s at level %d, when "
                   "current level is %d!\n", ident, level, env->index);
        }
    }
}

static void delete_enviro_level( int level ) {
    enviro *e, *e2;
    if( !env || env->index < level ) {
        return;
    }
    while( env && env->index >= level ) {
        e = env;
        env = env->parent;
        while( e ) {
            e2 = e;
            e = e->next;
            free(e2);
        }
    }
}

static void generate_debruijns_for_expr( token *tree, int level );

static void generate_debruijns_for_case( token *tree, int level ) {
    token *t, *t2;
    char c;
    /* Step 1: Generate the indices for the expression being cased upon */
    generate_debruijns_for_expr(tree->lhs, level);
    /* Step 2: Go through the cases */
    for( t = tree->rhs; t; t = t->next ) {
        /* Step 2a: LHS, ie. the pattens */
        for( t2 = t->lhs; t2; t2 = t2->next ) {
            if( t2->type == tok_ident ) {
                c = *(t2->value.s);
                /* Check for type constructor */
                if( c < 'A' || c > 'Z' ) {
                    insert_into_enviro(t2->value.s, level+1);
                }
            }
        }
        /* Step 2b: RHS */
        generate_debruijns_for_expr(t->rhs, level+1);
        delete_enviro_level(level+1);
    }
}

static void generate_debruijns_for_lambda( token *tree, int level ) {
    token *t;
    /* Step 1: Grab values being bound to the lambda */
    for( t = tree->lhs; t; t = t->next ) {
        insert_into_enviro(t->value.s, level+1);
    }
    /* Step 2: Generate the indices for the expression at the next level */
    generate_debruijns_for_expr(tree->rhs, level+1);
    delete_enviro_level(level+1);
}

void generate_debruijns_for_let( token *tree, int level ) {
    token *t1, *t2;
    char c;
    /* Step 1: Grab the bindings at the current level */
    for( t1 = tree->lhs; t1; t1 = t1->next ) {
        if( t1->type == tok_Assign ) {
            insert_into_enviro(t1->lhs->value.s, level+1);
        }
    }
    /* Step 2: Traverse the tree for the assignments */
    for( t1 = tree->lhs; t1; t1 = t1->next ) {
        if( t1->type == tok_Assign ) {
            /* We skip the first ident because we grabbed it in step 1 */
            for( t2 = t1->lhs->next; t2; t2 = t2->next ) {
                if( t2->type == tok_ident ) {
                    c = *(t2->value.s);
                    /* Check for type constructor */
                    if( c < 'A' || c > 'Z' ) {
                        insert_into_enviro(t2->value.s, level+2);
                    }
                }
            }
            /* The level is +2 because +1 is the binds in the LHS of the assign */
            generate_debruijns_for_expr( t1->rhs, level+2);
            delete_enviro_level(level+2);
        }
    }
    /* Step 3: Traverse RHS of let-binding */
    generate_debruijns_for_expr( tree->rhs, level+1);
    delete_enviro_level(level+1);
}

static void generate_debruijns_for_expr( token *tree, int level ) {
    enviro *e1, *e2;
    for( ; tree; tree = tree->next ) {
        if( tree->type == tok_ident ) {
            /* Step 1: Find the ident */
            e1 = env;
            do {
                e2 = e1->parent;
                while( e1 ) {
                    if( strcmp(e1->val, tree->value.s) == 0 ) {
                        /* Step 2: Set the index */
                        tree->index = level - e1->index + 1;
                        goto gdfe_match;
                    }
                    else {
                        e1 = e1->next;
                    }
                }
                e1 = e2;
            } while( e2 );
            /* Failed to find a match */
            printf("Unknown identifier: %s (line %d)\n", tree->value.s,
                tree->line_number);
            return;
            gdfe_match:
            continue;
        }
        else if( tree->type == tok_parens ) {
            generate_debruijns_for_expr(tree->lhs, level);
        }
        else if( tree->type == tok_brackets ) {
            generate_debruijns_for_expr(tree->lhs, level);
        }
        else if( tree->type == tok_letexpr ) {
            generate_debruijns_for_let(tree, level);
        }
        else if( tree->type == tok_lamexpr ) {
            generate_debruijns_for_lambda(tree, level);
        }
        else if( tree->type == tok_caseexpr ) {
            generate_debruijns_for_case(tree, level);
        }
    }
}

static void add_fake_prelude() {
    insert_into_enviro("add", 1);
    insert_into_enviro("multiply", 1);
    insert_into_enviro("dec", 1);
    insert_into_enviro("if", 1);
    insert_into_enviro("gt", 1);
    insert_into_enviro("toPtr", 1);
    insert_into_enviro("mapK", 1);
    insert_into_enviro("toArray", 1);
}

token * generate_debruijns( token *tree ) {
    token t; /* Fake root node so we can leverage the let version */
    t.lhs = tree;
    t.rhs = NULL; /* Will result in the RHS being ignored */
    add_fake_prelude(); /* FIXME */
    generate_debruijns_for_let(&t, 0);
    delete_enviro_level(0); /* Free up the environment */
    return tree;
}
