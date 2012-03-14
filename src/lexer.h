/*
 * lexer.h
 * By Steven Smith
 */

#ifndef LEXER_H_
#define LEXER_H_

#include <stdio.h>
#include <stdlib.h>

enum lexemes {
    lex_ident = 1, /* 0 is reserved for EOF/no more input */
    lex_int,
    lex_float,
    lex_string,
    lex_lparen,    /* (  */
    lex_rparen,    /* )  */
    lex_lbrace,    /* {  */
    lex_rbrace,    /* }  */
    lex_lbracket,  /* [  */
    lex_rbracket,  /* ]  */
    lex_arrow,     /* -> */
    lex_dubarrow,  /* => */
    lex_lambda,    /* \  */
    lex_colon,     /* :  */
    lex_typeof,    /* :: */
    lex_bar,       /* |  */
    lex_comma,     /* ,  */
    lex_semicolon, /* ;  */
    lex_eq,        /* =  */
    lex_dubeq,     /* == */
    lex_period,    /* .  */
    lex_dubperiod, /* .. */
    lex_backtick,  /* `  */
    lex_newline,
    /* Keywords */
    lex_case,
    lex_class,
    lex_export,
    lex_import,
    lex_kernel,
    lex_in,
    lex_instance,
    lex_let,
    lex_of,
    lex_otherwise,
    lex_type,
    lex_typeclass,
    lex_typesyn,
    lex_where
};

typedef struct lex_list {
    enum lexemes type;
    union {
        long   i;
        double f;
        char  *s;
    } value;
    int line_number;
    struct lex_list *next;
} lex_list;

lex_list * build_lex_list_f( FILE *fp );

lex_list * filter_extra_newlines( lex_list *lexes );

lex_list * filter_join_strings( lex_list *lexes );

void printlex( lex_list *lex );

void printlexlist( lex_list *lex );

#endif
