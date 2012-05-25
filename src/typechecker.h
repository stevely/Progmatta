/*
 * typechecker.h
 * By Steven Smith
 */

#ifndef TYPECHECKER_H_
#define TYPECHECKER_H_

#include "parsecomb.h"
#include "depanalyzer.h"

typedef char id;

typedef struct kind {
    struct kind *l;
    struct kind *r;
} kind;

typedef struct type type;

typedef struct typevar {
    id *i;
    kind *k;
} typevar;

typedef struct typecon {
    id *i;
    kind *k;
} typecon;

typedef struct typeap {
    type *l;
    type *r;
} typeap;

struct type {
    enum {
        type_var,
        type_con,
        type_ap,
        type_gen
    } type;
    union {
        typevar *tv;
        typecon *tc;
        typeap  *ta;
        int tg;
    } val;
    struct type *next;
};

typedef struct pred {
    id *i;
    type *t;
    struct pred *next;
} pred;

typedef struct qual {
    enum {
        qual_type,
        qual_pred
    } type;
    pred *p;
    union {
        type *t;
        pred *p;
    } val;
} qual;

typedef struct kind_list {
    kind *k;
    struct kind_list *next;
} kind_list;

/* Qual should always contain a type, but we can't enforce that */
typedef struct scheme {
    kind_list *ks;
    qual *q;
} scheme;

typedef struct assump {
    id *i;
    scheme *s;
    struct assump *next;
} assump;

typedef struct typed_token {
    enum tokens type;
    struct typed_token *lhs;
    struct typed_token *rhs;
    struct typed_token *next;
    union {
        long   i;
        double f;
        char  *s;
    } value;
    int index; /* For de Bruijn indices */
    int line_number;
    scheme *scheme;
} typed_token;

scheme * find( id *i, assump *a );

void print_scheme( scheme *sc );

void free_typed_token( typed_token *tok );

void test_type_inference( program *prog );

assump * perform_type_inference( program *prog );

typed_token * infer_types( program *prog );

void printtypedtok( typed_token *tok );

void printtypedtree( typed_token *tok );
#endif
