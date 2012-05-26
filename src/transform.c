/*
 * transform.c
 * By Steven Smith
 */

#include "transform.h"

static typed_token * strip_typesigs2( typed_token *tok ) {
    typed_token *t;
    /* Remove any leading typesigs */
    while( tok && tok->type == tok_Typesig ) {
        tok = tok->next;
    }
    if( !tok ) {
        return NULL;
    }
    /* Remove any remaining typesigs */
    t = tok;
    while( t->next ) {
        if( t->next->type == tok_Typesig ) {
            t->next = t->next->next;
        }
        else {
            t = t->next;
        }
    }
    return tok;
}

static typed_token * strip_typesigs( typed_token *tok ) {
    typed_token *t;
    t = tok;
    while( t ) {
        if( t->type == tok_Bind ) {
            t->lhs = strip_typesigs2(t->lhs);
        }
        t = t->next;
    }
    return tok;
}

typed_token * transform_tree( typed_token *tok ) {
    return strip_typesigs(tok);
}
