/*
 * parsecomb.h
 * By Steven Smith
 */

#ifndef PARSECOMB_H_
#define PARSECOMB_H_

#include "lexer.h"

enum tokens {
    tok_Assign,
    tok_Assigns,
    tok_Bind,
    tok_Bindgroup,
    tok_Case,
    tok_Cases,
    tok_Constraint,
    tok_Export,
    tok_Identlist,
    tok_Import,
    tok_Kernel,
    tok_Moreports,
    tok_PortStmt,
    tok_Typesig,
    tok_Typestmt,
    tok_arrow,
    tok_brackets,
    tok_case,
    tok_caseexpr,
    tok_comma,
    tok_dubcolon,
    tok_dubarrow,
    tok_eq,
    tok_export,
    tok_float,
    tok_funtype,
    tok_ident,
    tok_import,
    tok_in,
    tok_int,
    tok_kernel,
    tok_lambda,
    tok_lamexpr,
    tok_lbracket,
    tok_let,
    tok_letexpr,
    tok_lparen,
    tok_newline,
    tok_nothing,
    tok_of,
    tok_otherwise,
    tok_parens,
    tok_period,
    tok_rbracket,
    tok_rparen,
    tok_string,
    tok_vals
};

typedef struct token {
    enum tokens type;
    struct token *lhs;
    struct token *rhs;
    struct token *next;
    union {
        long   i;
        double f;
        char  *s;
    } value;
    int index; /* For de Bruijn indices */
    int line_number;
    int keep; /* For garbage collection */
} token;

void printtok( token *tok );

void printtree( token *tok );

void free_token_tree( token *tok );

token * parse( lex_list *l );

#endif
