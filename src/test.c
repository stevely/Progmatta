/*
 * test.c
 * By Steven Smith
 */

#include <stdio.h>
#include "lexer.h"
#include "tokenizer.h"
#include "parsecomb.h"
#include "debruijn.h"
#include "depanalyzer.h"
#include "typechecker.h"
#include "prettyprint.h"
#include "transform.h"

#define TEST_LEX (1 << 0)
#define TEST_TOK (1 << 1)
#define TEST_PAR (1 << 2)
#define TEST_DBI (1 << 3)
#define TEST_IBG (1 << 4)
#define TEST_DAN (1 << 5)
#define TEST_TCH (1 << 6)

int main( int argc, char **argv ) {
    int options, i;
    FILE *fp;
    lex_list *l;
    token *tree;
    program *prog;
    typed_token *typed_tree;
    if( argc == 1 ) {
        printf("Usage: %s [-ltpdiac] file\n", argv[0]);
        return 0;
    }
    /* Options */
    options = 0;
    if( *argv[1] == '-' ) {
        for( i = 1; argv[1][i]; i++ ) {
            switch( argv[1][i] ) {
            case 'l':
                options |= TEST_LEX;
                break;
            case 't':
                options |= TEST_TOK;
                break;
            case 'p':
                options |= TEST_PAR;
                break;
            case 'd':
                options |= TEST_DBI;
                break;
            case 'i':
                options |= TEST_IBG;
                break;
            case 'a':
                options |= TEST_DAN;
                break;
            case 'c':
                options |= TEST_TCH;
                break;
            default:
                printf("Unknown option %c\n", argv[1][i]);
                break;
            }
        }
        fp = fopen(argv[2], "r");
    }
    else {
        options = ~0; /* Set all options */
        fp = fopen(argv[1], "r");
    }
    if( !fp ) {
        printf("Failed to open file: %s\n", argv[1]);
        return 0;
    }
    /* Step 1: Lex file */
    l = build_lex_list_f(fp);
    fclose(fp);
    if( !l ) {
        printf("Error during lexing!\n");
        return 0;
    }
    l = filter_extra_newlines(l);
    l = filter_join_strings(l);
    if( options & TEST_LEX ) {
        printf("\n###Performing lex test...\n\n");
        printlexlist(l);
    }
    /* Step 2: Tokenize keywords */
    l = convert_keywords(l);
    if( options & TEST_TOK ) {
        printf("\n###Performing tokenizing test...\n\n");
        printlexlist(l);
    }
    /* Step 3: Parse */
    tree = parse(l);
    if( !tree ) {
        printf("Parse failure!\n");
        free_token_tree(tree);
        return 0;
    }
    else if( options & TEST_PAR ) {
        printf("\n###Performing parser test...\n\n");
        printtree(tree);
        printf("\n");
    }
    /* Step 4: Generate de Bruijn indices */
    tree = generate_debruijns(tree);
    if( options & TEST_DBI ) {
        printf("\n###Performing de Bruijn indices test...\n\n");
        printtree(tree);
        printf("\n");
    }
    /* Step 5: Generate initial bind group */
    prog = generate_initial_bg(tree);
    if( !prog ) {
        printf("Failed to generate initial binding groups!\n");
        return 0;
    }
    else if( options & TEST_IBG ) {
        printf("\n###Performing initial bind groups test...\n\n");
        printprog(prog);
        printf("\n");
    }
    /* Step 6: Perform dependency analysis */
    prog = perform_dependency_analysis(prog);
    if( options & TEST_DAN ) {
        printf("\n###Performing dependency analysis...\n\n");
        printprog(prog);
        printf("\n");
    }
    /* Step 7: Perform type inference */
    typed_tree = infer_types(prog);
    if( options & TEST_TCH ) {
        printf("\n###Performing type inference...\n\n");
        printtypedtree(typed_tree);
        printf("\n");
    }
    /* PHASE 2: Perform transformations on tree in preparation of code gen */
    /* Step 1: Print out initial tree */
    printf("\n###   PHASE TWO OF COMPILATION   ###");
    printf("\n###Performing pretty printing of tree...\n\n");
    pretty_print_tree(typed_tree);
    /* Step 2: Perform transformations */
    typed_tree = transform_tree(typed_tree);
    printf("\n###Performing tree transformation...\n\n");
    pretty_print_tree(typed_tree);
    free_program(prog);
    return 0;
}
