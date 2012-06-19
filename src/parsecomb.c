/*
 * parsecomb.c
 * By Steven Smith
 */

#include <stdarg.h>
#include "lexer.h"
#include "tokenizer.h"
#include "parsecomb.h"
#include "desugarer.h"

typedef struct output {
    lex_list *l;
    struct output *pnext;
    token *tok;
    enum tokens type;
    struct output *next; /* For garbage collection */
} output;

typedef output * (*parser)( lex_list *l );

#define Parser(name) static output * name( lex_list *l )

#define SimpleParser(name) \
    Parser(name) { \
        if( l && l->type == lex_##name ) { \
            return new_token(tok_##name, l, l->next); \
        } \
        else { \
            return NULL; \
        } \
    }

#define skip_newlines(l) \
    while( l && l->type == lex_newline ) { \
        l = l->next; \
    } \
    if( !l ) { \
        return NULL; \
    }

#define or if(!o)

#define bind(args...) bind_(l, args, NULL)

void printtok( token *tok ) {
    /* Degenerate case */
    if( !tok ) {
        printf("<null>");
        return;
    }
    switch(tok->type) {
    /* Vanilla types */
    case tok_Assign: printf("Assign"); break;
    case tok_Assigns: printf("Assigns"); break;
    case tok_Bindgroup: printf("Bindgroup"); break;
    case tok_Case: printf("Case"); break;
    case tok_Cases: printf("Cases"); break;
    case tok_Export: printf("Export"); break;
    case tok_Identlist: printf("Identlist"); break;
    case tok_Import: printf("Import"); break;
    case tok_Kernel: printf("Kernel"); break;
    case tok_Moreports: printf("Moreports"); break;
    case tok_PortStmt: printf("PortStmt"); break;
    case tok_Typesig: printf("Typesig"); break;
    case tok_arrow: printf("arrow"); break;
    case tok_brackets: printf("brackets"); break;
    case tok_case: printf("case"); break;
    case tok_caseexpr: printf("caseexpr"); break;
    case tok_dubcolon: printf("dubcolon"); break;
    case tok_eq: printf("eq"); break;
    case tok_export: printf("export"); break;
    case tok_funtype: printf("funtype"); break;
    case tok_import: printf("import"); break;
    case tok_in: printf("in"); break;
    case tok_kernel: printf("kernel"); break;
    case tok_lambda: printf("lambda"); break;
    case tok_lamexpr: printf("lamexpr"); break;
    case tok_lbracket: printf("lbracket"); break;
    case tok_let: printf("let"); break;
    case tok_letexpr: printf("letexpr"); break;
    case tok_lparen: printf("lparen"); break;
    case tok_newline: printf("newline"); break;
    case tok_nothing: printf("nothing"); break;
    case tok_of: printf("of"); break;
    case tok_otherwise: printf("otherwise"); break;
    case tok_parens: printf("parens"); break;
    case tok_period: printf("period"); break;
    case tok_rbracket: printf("rbracket"); break;
    case tok_rparen: printf("rparen"); break;
    case tok_vals: printf("val"); break;
    /* Types holding something */
    case tok_Bind:
        printf("Bind: %s", tok->value.s);
        break;
    case tok_ident:
        printf("ident: %s", tok->value.s);
        if( tok->index != 0 ) {
            printf(" (%d)", tok->index);
        }
        break;
    case tok_int:
        printf("int: %ld", tok->value.i);
        break;
    case tok_float:
        printf("float: %f", tok->value.f);
        break;
    case tok_string:
        printf("string: %s", tok->value.s);
        break;
    /* Badness has happened */
    default: printf("<<Unknown>>"); break;
    }
}

void printtree( token *tok ) {
    if( !tok ) {
        return;
    }
    printtok(tok);
    if( tok->lhs ) {
        printf(" (");
        printtree(tok->lhs);
        printf(")");
    }
    if( tok->rhs ) {
        printf(" (");
        printtree(tok->rhs);
        printf(")");
    }
    if( tok->next ) {
        printf(", ");
        printtree(tok->next);
    }
}

static output * bind_( lex_list *l, ...) {
    output *o, *o_tail, *o_curr;
    parser p;
    va_list ap;
    va_start(ap, l);
    o = NULL;
    o_tail = NULL;
    while( (p = va_arg(ap, parser)) ) {
        o_curr = (*p)(l);
        /* Parse fail */
        if( !o_curr ) {
            va_end(ap);
            return NULL;
        }
        /* Parse succeed */
        if( o ) {
            o_tail->pnext = o_curr;
            o_tail = o_curr;
        }
        else {
            o = o_curr;
            o_tail = o;
        }
        l = o_curr->l;
    }
    va_end(ap);
    /* Update current lex location */
    /* Not strictly necessary, but makes clang's analyzer happy */
    if( o_tail ) {
        o->l = o_tail->l;
    }
    return o;
}

/*
 * Output structs are intermediate structures that are completely useless once
 * parsing is complete. To simplify resource reclamation, we piggy-back onto
 * memory allocation and keep a list of allocated output structs. When parsing
 * completes, we can then free them all in one fell swoop.
 *
 * Keep in mind that this is neither fast nor efficient. It's simple.
 */

static output *output_stack = NULL;

static output * malloc_output() {
    output *o = (output*)malloc(sizeof(output));
    if( !o ) {
        return NULL;
    }
    if( output_stack ) {
        o->next = output_stack;
    }
    else {
        o->next = NULL;
    }
    output_stack = o;
    return o;
}

static void free_output() {
    output *temp;
    output *o = output_stack;
    while( o ) {
        temp = o;
        o = o->next;
        free(temp);
    }
    output_stack = NULL;
}

/*
 * Tokens are more permanent structures, but many extraneous tokens are
 * generated during the course of parsing due to failed parsing passes. To
 * reclaim memory, we piggy-back onto memory allocation and keep a list of
 * allocated tokens. When parsing completes, we free the unused tokens with a
 * mark-and-sweep collector.
 */

struct token_list {
    token *tok;
    struct token_list *next;
};

static struct token_list *tok_list = NULL;

static token * malloc_token() {
    struct token_list *tl = (struct token_list*)malloc(sizeof(struct token_list));
    if( !tl ) {
        return NULL;
    }
    tl->tok = (token*)malloc(sizeof(token));
    if( !tl->tok ) {
        free(tl);
        return NULL;
    }
    tl->tok->keep = 0;
    if( tok_list ) {
        tl->next = tok_list;
    }
    else {
        tl->next = NULL;
    }
    tok_list = tl;
    return tl->tok;
}

static void mark_token( token *tok ) {
    if( tok ) {
        tok->keep = 1;
        mark_token(tok->lhs);
        mark_token(tok->rhs);
        mark_token(tok->next);
    }
}

static void free_tokens( token *tok ) {
    struct token_list *tl, *tmp;
    mark_token(tok);
    tl = tok_list;
    while( tl ) {
        tmp = tl;
        tl = tl->next;
        if( !tmp->tok->keep ) {
            free(tmp->tok);
        }
        free(tmp);
    }
    /* tok_list is useless now-- every remaining token is in the given tree */
    tok_list = NULL;
}

void free_token_tree( token *tok ) {
    if( tok ) {
        free_token_tree(tok->lhs);
        free_token_tree(tok->rhs);
        free_token_tree(tok->next);
        free(tok);
    }
}

output * new_token( enum tokens tok, lex_list *l, lex_list *next ) {
    output *o = malloc_output();
    if( !o ) {
        return NULL;
    }
    o->tok = malloc_token();
    if( !o->tok ) {
        return NULL;
    }
    o->l = next;
    o->pnext = NULL;
    o->type = tok;
    o->tok->type = tok;
    o->tok->lhs = NULL;
    o->tok->rhs = NULL;
    o->tok->next = NULL;
    o->tok->line_number = l->line_number;
    o->tok->index = 0;
    switch( tok ) {
    case tok_int:
        o->tok->value.i = l->value.i;
        break;
    case tok_float:
        o->tok->value.f = l->value.f;
        break;
    case tok_string:
    case tok_ident:
        o->tok->value.s = l->value.s;
        break;
    default:
        o->tok->value.i = 0;
        break;
    }
    return o;
}

output * new_token_with_child( enum tokens tok, lex_list *l, output *child,
    lex_list *n ) {
    output *o = new_token(tok, l, n);
    o->tok->lhs = child->tok;
    return o;
}

output * new_token_with_lrhs( enum tokens tok, lex_list *l, output *lhs, output *rhs,
    lex_list *n ) {
    output *o = new_token(tok, l, n);
    o->tok->lhs = lhs->tok;
    o->tok->rhs = rhs->tok;
    return o;
}

output * new_token_with_child_and_next( enum tokens tok, lex_list *l, output *child,
    output *next, lex_list *n ) {
    output *o = new_token(tok, l, n);
    o->tok->lhs = child->tok;
    o->tok->next = next->tok;
    return o;
}

output * new_token_with_next( enum tokens tok, lex_list *l, output *h, output *t,
    lex_list *n ) {
    output *o = malloc_output();
    if( !o ) {
        return NULL;
    }
    o->l = n;
    o->pnext = NULL;
    o->type = tok;
    o->tok = h->tok;
    if( !t || t->type == tok_nothing ) {
        o->tok->next = NULL;
    }
    else {
        o->tok->next = t->tok;
    }
    o->tok->line_number = l->line_number;
    o->tok->index = 0;
    return o;
}

SimpleParser(arrow);
SimpleParser(eq);
SimpleParser(export);
SimpleParser(ident);
SimpleParser(import);
SimpleParser(in);
SimpleParser(kernel);
SimpleParser(lambda);
SimpleParser(lbracket);
SimpleParser(let);
SimpleParser(lparen);
SimpleParser(newline);
SimpleParser(of);
SimpleParser(otherwise);
SimpleParser(period);
SimpleParser(rbracket);
SimpleParser(rparen);
SimpleParser(string);

/* Special cases: can't call them int/float/case */
Parser(pint) {
    if( l && l->type == lex_int ) {
        return new_token(tok_int, l, l->next);
    }
    else {
        return NULL;
    }
}

Parser(pfloat) {
    if( l && l->type == lex_float ) {
        return new_token(tok_float, l, l->next);
    }
    else {
        return NULL;
    }
}

Parser(pcase) {
    if( l && l->type == lex_case ) {
        return new_token(tok_case, l, l->next);
    }
    else {
        return NULL;
    }
}

/* Sticking "typeof" in places breaks things */
Parser(dubcolon) {
    if( l && l->type == lex_typeof ) {
        return new_token(tok_dubcolon, l, l->next);
    }
    else {
        return NULL;
    }
}

Parser(nothing) {
    if( l ) {
        return new_token(tok_nothing, l, l);
    }
    else {
        return NULL;
    }
}

Parser(start);
Parser(Toplevel);
Parser(Topstmt);
Parser(Import);
Parser(Export);
Parser(Kernel);
Parser(Typesig);
Parser(Assign);
Parser(PortStmt);
Parser(Identlist);
Parser(Identvals);
Parser(Expr);
Parser(Assigns);
Parser(Type);
Parser(Moreports);
Parser(Redexpr);
Parser(Vals);
Parser(Valslist);
Parser(Cases);
Parser(Case);

/*
 * start: Toplevel
 */
Parser(start) {
    return Toplevel(l);
}

/*
 * Toplevel: Topstmt Toplevel
 *         | Topstmt
 */
Parser(Toplevel) {
    output *o;
       o = bind( Topstmt, Toplevel );
    or o = bind( Topstmt );
    if( o ) {
        return new_token_with_next(o->type, l, o, o->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * Topstmt: Import
 *        | Export
 *        | Kernel
 *        | Typesig
 *        | Assign
 */
Parser(Topstmt) {
    output *o;
       o = bind( Import );
    or o = bind( Export );
    or o = bind( Kernel );
    or o = bind( Typesig );
    or o = bind( Assign );
    return o;
}

/*
 * Import : import PortStmt newline
 */
Parser(Import) {
    output *o = bind( import, PortStmt, newline );
    if( o ) {
        return new_token_with_child(tok_Import, l, o->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * Export : export PortStmt newline
 */
Parser(Export) {
    output *o = bind( export, PortStmt, newline );
    if( o ) {
        return new_token_with_child(tok_Export, l, o->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * Assign: Identvals eq Expr newline
 *       | Identvals eq newline Expr newline
 */
Parser(Assign) {
    output *o;
       o = bind( Identvals, eq, Expr, newline );
    or o = bind( Identvals, eq, newline, Expr, newline );
    if( o ) {
        if( o->pnext->pnext->type == tok_newline ) {
            return new_token_with_lrhs(tok_Assign, l, o, o->pnext->pnext->pnext, o->l);
        }
        else {
            return new_token_with_lrhs(tok_Assign, l, o, o->pnext->pnext, o->l);
        }
    }
    else {
        return NULL;
    }
}

/*
 * Assigns: Assign Assigns
 *        | Assign
 */
Parser(Assigns) {
    output *o;
       o = bind( Assign, Assigns );
    or o = bind( Assign );
    if( o ) {
        /* Will do the right thing even if only matched with one Assign */
        return new_token_with_next(tok_Assigns, l, o, o->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * Typesig: ident dubcolon Type newline
 */
Parser(Typesig) {
    output *o = bind( ident, dubcolon, Type, newline );
    if( o ) {
        return new_token_with_lrhs(tok_Typesig, l, o, o->pnext->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * Kernel: kernel Typesig
 */
Parser(Kernel) {
    output *o = bind( kernel, Typesig );
    if( o ) {
        /* Hijack the Typesig token and change it into a Kernel token */
        o->pnext->tok->type = tok_Kernel;
        return o->pnext;
    }
    else {
        return NULL;
    }
}

/*
 * Identlist: ident Identlist
 *          | ident
 */
Parser(Identlist) {
    output *o;
       o = bind( ident, Identlist );
    or o = bind( ident );
    if( o ) {
        return new_token_with_next(tok_Identlist, l, o, o->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * Identvals: ident Valslist
 *          | ident
 */
Parser(Identvals) {
    output *o;
       o = bind( ident, Valslist );
    or o = bind( ident );
    if( o ) {
        return new_token_with_next(tok_Identlist, l, o, o->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * PortStmt: ident Moreports
 */
Parser(PortStmt) {
    output *o = bind( ident, Moreports );
    if( o ) {
        return new_token_with_next(tok_PortStmt, l, o, o->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * Moreports: period ident Moreports
 *          | nothing
 */
Parser(Moreports) {
    output *o;
       o = bind( period, ident, Moreports );
    or o = bind( nothing );
    if( o ) {
        if( o->type == tok_nothing ) {
            return o;
        }
        else {
            return new_token_with_next(tok_Moreports, l, o->pnext, o->pnext->pnext,
                                       o->l);
        }
    }
    else {
        return NULL;
    }
}

/*
 * Type: ident arrow Type
 *     | ident
 *     | lparen Type rparen arrow Type
 *     | lbracket Type rbracket arrow Type
 *     | lparen Type rparen
 *     | lbracket Type rbracket
 */
Parser(Type) {
    output *lhs;
    output *o;
       o = bind( ident, arrow, Type );
    or o = bind( ident );
    or o = bind( lparen, Type, rparen );
    or o = bind( lbracket, Type, rbracket );
    if( o ) {
        if( o->type == tok_ident ) {
            /* Check for function */
            if( o->pnext ) {
                return new_token_with_lrhs(tok_funtype, l, o, o->pnext->pnext, o->l);
            }
            else {
                return o;
            }
        }
        /* Parens or brackets */
        else {
            if( o->type == tok_lparen ) {
                lhs = new_token_with_child(tok_parens, l, o->pnext, o->l);
            }
            else {
                lhs = new_token_with_child(tok_brackets, l, o->pnext, o->l);
            }
            /* Check for function */
            if( o->pnext->pnext->pnext ) {
                return new_token_with_lrhs(tok_funtype, l, lhs,
                                           o->pnext->pnext->pnext->pnext, o->l);
            }
            else {
                return lhs;
            }
        }
    }
    else {
        return NULL;
    }
}

/*
 * Expr: let Assigns in Expr
 *     | lambda Identlist arrow Expr
 *     | case Expr of newline Cases
 *     | Redexpr
 */
Parser(Expr) {
    output *o;
       o = bind( let, Assigns, in, Expr );
    or o = bind( lambda, Identlist, arrow, Expr );
    or o = bind( pcase, Expr, of, newline, Cases );
    or o = bind( Redexpr );
    if( o ) {
        if( o->type == tok_let ) {
            return new_token_with_lrhs(tok_letexpr, l, o->pnext,
                o->pnext->pnext->pnext, o->l);
        }
        else if( o->type == tok_lambda ) {
            return new_token_with_lrhs(tok_lamexpr, l, o->pnext,
                o->pnext->pnext->pnext, o->l);
        }
        else if( o->type == tok_case ) {
            return new_token_with_lrhs(tok_caseexpr, l, o->pnext,
                o->pnext->pnext->pnext->pnext, o->l);
        }
        else {
            return o;
        }
    }
    else {
        return NULL;
    }
}

/*
 * Redexpr: lparen Expr rparen Redexpr
 *        | lbracket Expr rbracket Redexpr
 *        | lparen Expr rparen
 *        | lbracket Expr rbracket
 *        | Vals Redexpr
 *        | Vals
 */
Parser(Redexpr) {
    output *o;
       o = bind( lparen, Expr, rparen, Redexpr );
    or o = bind( lbracket, Expr, rbracket, Redexpr );
    or o = bind( lparen, Expr, rparen );
    or o = bind( lbracket, Expr, rbracket );
    or o = bind( Vals, Redexpr );
    or o = bind( Vals );
    if( o ) {
        if( o->type == tok_lparen ) {
            if( o->pnext->pnext->pnext ) {
                return new_token_with_child_and_next(tok_parens, l, o->pnext,
                    o->pnext->pnext->pnext, o->l);
            }
            else {
                return new_token_with_child(tok_parens, l, o->pnext, o->l);
            }
        }
        else if( o->type == tok_lbracket ) {
            if( o->pnext->pnext->pnext ) {
                return new_token_with_child_and_next(tok_brackets, l, o->pnext,
                    o->pnext->pnext->pnext, o->l);
            }
            else {
                return new_token_with_child(tok_brackets, l, o->pnext, o->l);
            }
        }
        /* Vals Redexpr */
        else if( o->pnext ) {
            return new_token_with_next(tok_vals, l, o, o->pnext, o->l);
        }
        else {
            return o;
        }
    }
    else {
        return NULL;
    }
}

/*
 * Vals: ident
 *     | int
 *     | float
 *     | string
 */
Parser(Vals) {
    output *o;
       o = bind( ident );
    or o = bind( pint );
    or o = bind( pfloat );
    or o = bind( string );
    return o;
}

/*
 * Valslist: Vals Valslist
 *         | Vals
 */
Parser(Valslist) {
    output *o;
       o = bind( Vals, Valslist );
    or o = bind( Vals );
    if( o ) {
        return new_token_with_next(tok_vals, l, o, o->pnext, o->l);
    }
    else {
        return NULL;
    }
}

/*
 * Cases: Case newline Cases
 *      | Case
 */
Parser(Cases) {
    output *o;
       o = bind( Case, newline, Cases );
    or o = bind( Case );
    if( o ) {
        if( o->pnext ) {
            return new_token_with_next(tok_Case, l, o, o->pnext->pnext, o->l);
        }
        else {
            return o;
        }
    }
    else {
        return NULL;
    }
}

/*
 * Case: otherwise arrow Expr
 *     | Valslist arrow Expr
 */
Parser(Case) {
    output *o;
       o = bind( otherwise, arrow, Expr );
    or o = bind( Valslist, arrow, Expr );
    if( o ) {
        return new_token_with_lrhs(tok_Cases, l, o, o->pnext->pnext, o->l);
    }
    else {
        return NULL;
    }
}

token * parse( lex_list *l ) {
    token *result;
    output *o = bind( start );
    /* If we successfully parsed and successfully grabbed all input data */
    if( o ) {
        if( !o->l ) {
            result = o->tok;
            free_output();
            free_tokens(result);
            return desugar_tree(result);
        }
        else {
            printf("Parse error on line %d.\n", o->l->line_number);
            free_output();
            free_tokens(NULL); /* Free them all */
            return NULL;
        }
    }
    else {
        free_output();
        free_tokens(NULL); /* Free them all */
        return NULL;
    }
}
