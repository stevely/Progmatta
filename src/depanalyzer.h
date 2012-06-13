/*
 * typechecker.h
 * By Steven Smith
 */

#ifndef DEPANALYZER_H_
#define DEPANALYZER_H_

#include "parsecomb.h"

typedef struct {
    token *expl;
    token *impl;
    token *tree;
    token *imports;
    token *exports;
} program;

typedef struct dep_list_item {
    char *ident;
    struct dep_list_item *next;
} dep_list_item;

typedef struct dep_list {
    token *tok;
    int visited;
    dep_list_item *ident;
    dep_list_item *dl;
    struct dep_list *prev;
} dep_list;

program * generate_initial_bg( token *tree );

dep_list * generate_dependency_list( program *prog );

program * perform_dependency_analysis( program *prog );

void printprog( program *prog );

void free_program( program *prog );

void printdeplist( dep_list *dl );

void free_dep_list( dep_list *dl );

#endif
