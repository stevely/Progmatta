/*
 * prettyprint.c
 * By Steven Smith
 */

#include <stdlib.h>
#include <string.h>
#include "prettyprint.h"

static char tyvars[] = "abcdefghijklmnopqrstuvwxyz";

static int is_func( type *t ) {
    if( t->type != type_con ) {
        return 0;
    }
    return strcmp(t->val.tc->i, "(->)") == 0;
}

static int is_list( type *t ) {
    if( t->type != type_con ) {
        return 0;
    }
    return strcmp(t->val.tc->i, "List") == 0;
}

void pretty_print_type( type *t ) {
    switch( t->type ) {
    case type_var:
        printf("%s", t->val.tv->i);
        break;
    case type_con:
        printf("%s", t->val.tv->i);
        break;
    case type_gen:
        if( t->val.tg >= 26 ) {
            printf("v%d", t->val.tg);
        }
        else {
            printf("%c", tyvars[t->val.tg]);
        }
        break;
    case type_ap:
        /* Special case for type application */
        if( t->val.ta->l->type == type_ap && is_func(t->val.ta->l->val.ta->l) ) {
            printf("(");
            pretty_print_type(t->val.ta->l->val.ta->r);
            printf(" -> ");
            pretty_print_type(t->val.ta->r);
            printf(")");
        }
        /* Special case for lists */
        else if( is_list(t->val.ta->l) ) {
            printf("[");
            pretty_print_type(t->val.ta->r);
            printf("]");
        }
        else {
            pretty_print_type(t->val.ta->l);
            printf(" ");
            pretty_print_type(t->val.ta->r);
        }
        break;
    default:
        printf("bad type");
        break;
    }
}

void pretty_print_pred( pred *p ) {
    while( p ) {
        printf("%s ", p->i);
        pretty_print_type(p->t);
        if( p->next ) {
            printf(", ");
        }
        p = p->next;
    }
    printf(" => ");
}

void pretty_print_scheme( scheme *s ) {
    qual *q;
    q = s->q;
    if( q->p ) {
        pretty_print_pred(q->p);
    }
    pretty_print_type(q->val.t);
}

static void pretty_print_tree2( typed_token *tok, int indent ) {
    int i;
    if( !tok ) {
        return;
    }
    switch( tok->type ) {
    case tok_Assign:
        pretty_print_tree2(tok->lhs, indent);
        printf(" = ");
        pretty_print_tree2(tok->rhs, indent);
        printf("\n");
        break;
    case tok_Bind:
        printf("%s :: ", tok->value.s);
        pretty_print_scheme(tok->scheme);
        printf("\n");
        pretty_print_tree2(tok->lhs, indent);
        printf("\n");
        break;
    case tok_brackets:
        printf("[");
        pretty_print_tree2(tok->lhs, indent);
        printf("]");
        break;
    case tok_parens:
        printf("(");
        pretty_print_tree2(tok->lhs, indent);
        printf(")");
        break;
    case tok_letexpr:
        printf("let ");
        pretty_print_tree2(tok->lhs, indent);
        printf(" in ");
        pretty_print_tree2(tok->rhs, indent);
        break;
    case tok_caseexpr:
        printf("case ");
        pretty_print_tree2(tok->lhs, indent);
        printf(" of\n");
        pretty_print_tree2(tok->rhs, indent);
        break;
    case tok_case:
        pretty_print_tree2(tok->lhs, indent);
        printf(" -> ");
        pretty_print_tree2(tok->rhs, indent);
        printf("\n");
        break;
    case tok_Typesig:
        printf("--");
        pretty_print_tree2(tok->lhs, indent);
        printf(" :: ");
        pretty_print_tree2(tok->rhs, indent);
        printf("\n");
        break;
    case tok_funtype:
        pretty_print_tree2(tok->lhs, indent);
        printf(" -> ");
        pretty_print_tree2(tok->rhs, indent);
        break;
    case tok_ident:
        printf("%s", tok->value.s);
        break;
    case tok_int:
        printf("%ld", tok->value.i);
        break;
    case tok_float:
        printf("%f", tok->value.f);
        break;
    case tok_string:
        printf("\"%s\"", tok->value.s);
        break;
    /*
    case tok_Bindgroup:
        pretty_print_tree2(tok->lhs, indent+4);
        break;
        */
    default:
        printf("<?>");
        break;
    }
    if( tok->next ) {
        if( tok->type != tok_Assign && tok->type != tok_Typesig
         && tok->type != tok_Bind   && tok->type != tok_case ) {
            printf(" ");
        }
        else {
            for( i = 0; i < indent; i++ ) {
                printf(" ");
            }
        }
        pretty_print_tree2(tok->next, indent);
    }
}

void pretty_print_tree( typed_token *tok ) {
    pretty_print_tree2(tok, 0);
}
