/*
 * desugarer.c
 * By Steven Smith
 */

#include "desugarer.h"

/*
 * Converts "[a]" into "(List (a))"
 * Works for both types and expressions.
 */
static token * desugar_brackets( token *tree ) {
    token *t;
    if( !tree ) {
        return tree;
    }
    if( tree->type == tok_brackets ) {
        /* Step 1: Change brackets to parens */
        tree->type = tok_parens;
        /* Step 2: Make our new List identifier */
        t = (token*)malloc(sizeof(token));
        t->line_number = tree->line_number;
        t->type = tok_ident;
        t->value.s = "List";
        t->lhs = NULL;
        t->rhs = NULL;
        t->keep = 0;
        /* Step 3: Make a parens container for the contained value */
        t->next = (token*)malloc(sizeof(token));
        t->next->line_number = tree->line_number;
        t->next->type = tok_parens;
        t->next->lhs = tree->lhs;
        t->next->rhs = NULL;
        t->next->next = NULL;
        t->next->keep = 0;
        /* Step 4: Point our brackets-now-parens to our new tokens */
        tree->lhs = t;
    }
    tree->rhs  = desugar_brackets(tree->rhs);
    tree->lhs  = desugar_brackets(tree->lhs);
    tree->next = desugar_brackets(tree->next);
    return tree;
}

token * desugar_tree( token *tree ) {
    return desugar_brackets(tree);
}
