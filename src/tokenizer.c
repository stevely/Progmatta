/*
 * tokenizer.c
 * By Steven Smith
 */

#include <stdio.h>
#include <stdlib.h>
#include "tokenizer.h"
#include "lexer.h"

/*
 * The basic plan is to create a trie (prefix tree) containing every keyword.
 * Once the trie is created, keywords can be separated from general identifiers
 * by simply walking the trie. We'll either end on a node that doesn't refer to
 * a keyword, hit a leaf node with input remaining, or end on a node that refers
 * to a keyword. In the former two cases we leave it as a general identifier; in
 * the latter case we can convert it into a keyword and throw away the string.
 */

typedef struct keyword_trie {
    char c;
    enum lexemes lex;
    struct keyword_trie *next;
    struct keyword_trie *child;
} keyword_trie;

static keyword_trie *kw_trie = NULL;

static void insert_into_trie( char *name, enum lexemes l ) {
    char *c = name;
    keyword_trie *trie, *trie_parent, *trie_sibling;
    trie_sibling = NULL;
    if( !c ) {
        return;
    }
    /* If this is the first entry, we need to create the struct and move down */
    if( kw_trie == NULL ) {
        kw_trie = (keyword_trie*)malloc(sizeof(keyword_trie));
        kw_trie->c = *c;
        kw_trie->next = NULL;
        kw_trie->child = NULL;
        kw_trie->lex = lex_ident;
        c++;
        trie_parent = kw_trie;
        trie = NULL;
    }
    /* Otherwise start at the top level */
    else {
        trie_parent = NULL;
        trie = kw_trie;
    }
    while( *c ) {
        if( !trie ) {
            trie = (keyword_trie*)malloc(sizeof(keyword_trie));
            trie->c = *c;
            trie->next = NULL;
            trie->child = NULL;
            c++;
            /* Attach new node to sibling if it exists */
            if( trie_sibling ) {
                trie_sibling->next = trie;
                trie_sibling = NULL; /* Since we drop down a level */
            }
            /* Attack new node to parent otherwise */
            else if( trie_parent ) {
                trie_parent->child = trie;
            }
            /* Check if there's still characters left */
            if( *c ) {
                trie->lex = lex_ident;
                trie_parent = trie;
                trie = trie->child;
            }
            /* Hit the endpoint */
            else {
                trie->lex = l;
            }
        }
        /* Node already exists, so traverse */
        else {
            if( trie->c == *c ) {
                c++;
                if( *c == '\0' ) {
                    trie->lex = l;
                }
                trie_parent = trie;
                trie = trie->child;
                trie_sibling = NULL;
            }
            else {
                trie_sibling = trie;
                trie = trie->next;
            }
        }
    }
}

static void build_keyword_trie() {
    insert_into_trie("case",      lex_case);
    insert_into_trie("class",     lex_class);
    insert_into_trie("export",    lex_export);
    insert_into_trie("import",    lex_import);
    insert_into_trie("kernel",    lex_kernel);
    insert_into_trie("in",        lex_in);
    insert_into_trie("instance",  lex_instance);
    insert_into_trie("let",       lex_let);
    insert_into_trie("of",        lex_of);
    insert_into_trie("otherwise", lex_otherwise);
    insert_into_trie("type",      lex_type);
    insert_into_trie("typeclass", lex_typeclass);
    insert_into_trie("typesyn",   lex_typesyn);
    insert_into_trie("where",     lex_where);
}

static enum lexemes lookup_keyword( char *string ) {
    keyword_trie *kwt = kw_trie;
    char *s = string;
    if( !s ) {
        return lex_ident;
    }
    while( *s ) {
        if( !kwt ) {
            return lex_ident;
        }
        else {
            if( kwt->c == *s ) {
                s++;
                /* Check if we've reached the end */
                if( *s == '\0' ) {
                    return kwt->lex;
                }
                kwt = kwt->child;
            }
            else {
                kwt = kwt->next;
            }
        }
    }
    return lex_ident;
}

lex_list * convert_keywords( lex_list *lexes ) {
    enum lexemes lex;
    lex_list *list = lexes;
    build_keyword_trie();
    while( list ) {
        if( list->type == lex_ident ) {
            lex = lookup_keyword(list->value.s);
            /* We catch a keyword? */
            if( lex != lex_ident ) {
                /* Bye bye useless string */
                free(list->value.s);
                list->type = lex;
            }
        }
        list = list->next;
    }
    return lexes;
}
