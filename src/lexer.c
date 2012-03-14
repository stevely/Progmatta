/* 
 * lexer.c
 * By Steven Smith
 */

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lexer.h"

static lex_list *list  = NULL;
static lex_list *l_end = NULL;

#define LEX_IDENT_SIZE 256
#define LEX_BUF_SIZE 1024

static char ident_buf[LEX_IDENT_SIZE+1];
static char char_buf[LEX_BUF_SIZE];
static int charbuf_pos = LEX_BUF_SIZE; /* Forces input fetch on first attempt */
static int charbuf_end = LEX_BUF_SIZE;
static FILE *file = NULL;

static int get_next_char() {
    int i;
    if( !file ) {
        return EOF;
    }
    if( charbuf_pos >= LEX_BUF_SIZE ) {
        /* Out of buffer space, time to refill it */
        i = fread(char_buf, sizeof(char), LEX_BUF_SIZE, file);
        if( i != LEX_BUF_SIZE ) {
            /* EOF or errored */
            charbuf_end = i;
        }
        charbuf_pos = 0;
    }
    if( charbuf_pos < charbuf_end ) {
        return (int)char_buf[charbuf_pos++]; /* Incr after char retrieval */
    }
    else {
        return EOF;
    }
}

static lex_list * new_lexeme() {
    lex_list *l;
    l = (lex_list*)malloc(sizeof(lex_list));
    l->next = NULL;
    if( !list ) {
        list = l;
        l_end = l;
    }
    else {
        l_end->next = l;
        l_end = l;
    }
    return l;
}

static char * build_ident( int pos ) {
    char *s;
    s = (char*)malloc(sizeof(char) * (pos+1)); /* Need trailing \0 */
    strncpy(s, ident_buf, pos);
    s[pos] = '\0';
    return s;
}

static int valid_ident( int c ) {
    return (!isspace(c)) &&
        c != '(' && c != ')' && c != '{'  && c != '}'  && c != '['  && c != ']' &&
        c != '-' && c != '=' && c != '\\' && c != ':'  && c != '|'  && c != ',' &&
        c != ';' && c != '.' && c != '`'  && c != '\n' && c != '\r' && c != EOF;
}

lex_list * build_lex_list_f( FILE *fp ) {
    int curr_char;
    int ident_pos;
    int current_line;
    int comment_level;
    lex_list *l, *l2;
    if( !fp ) {
        return NULL;
    }
    file = fp;
    curr_char = get_next_char();
    current_line = 1;
    while( curr_char != EOF ) {
        /* First try for the single characters */
        if( curr_char == '(' ) {
            l = new_lexeme();
            l->type = lex_lparen;
            l->line_number = current_line;
        }
        else if( curr_char == ')' ) {
            l = new_lexeme();
            l->type = lex_rparen;
            l->line_number = current_line;
        }
        else if( curr_char == '}' ) {
            l = new_lexeme();
            l->type = lex_rbrace;
            l->line_number = current_line;
        }
        else if( curr_char == '[' ) {
            l = new_lexeme();
            l->type = lex_lbracket;
            l->line_number = current_line;
        }
        else if( curr_char == ']' ) {
            l = new_lexeme();
            l->type = lex_rbracket;
            l->line_number = current_line;
        }
        else if( curr_char == '\\' ) {
            l = new_lexeme();
            l->type = lex_lambda;
            l->line_number = current_line;
        }
        else if( curr_char == '|' ) {
            l = new_lexeme();
            l->type = lex_bar;
            l->line_number = current_line;
        }
        else if( curr_char == ',' ) {
            l = new_lexeme();
            l->type = lex_comma;
            l->line_number = current_line;
        }
        else if( curr_char == ';' ) {
            l = new_lexeme();
            l->type = lex_semicolon;
            l->line_number = current_line;
        }
        else if( curr_char == '`' ) {
            l = new_lexeme();
            l->type = lex_backtick;
            l->line_number = current_line;
        }

        /* Check for : or :: */
        else if( curr_char == ':' ) {
            l = new_lexeme();
            l->line_number = current_line;
            curr_char = get_next_char();
            /* :: */
            if( curr_char == ':' ) {
                l->type = lex_typeof;
            }
            else {
                l->type = lex_colon;
                continue; /* Skip advancing the current character */
            }
        }

        /* { might lead to {- which is a block comment */
        else if( curr_char == '{' ) {
            curr_char = get_next_char();
            /* Block comment */
            if( curr_char == '-' ) {
                comment_level = 1; /* Comments can nest */
                curr_char = get_next_char();
                while( comment_level != 0 ) {
                    /* Check for another comment level */
                    if( curr_char == '{' ) {
                        curr_char = get_next_char();
                        if( curr_char == '-' ) {
                            comment_level++;
                        }
                    }
                    /* Check for closing comment */
                    else if( curr_char == '-' ) {
                        curr_char = get_next_char();
                        if( curr_char == '}' ) {
                            comment_level--;
                        }
                    }
                    else if( curr_char == EOF ) {
                        /* TODO: Error */
                        return NULL;
                    }
                    else {
                        curr_char = get_next_char();
                    }
                }
            }
            /* Plain old left bracket */
            else {
                l = new_lexeme();
                l->type = lex_lbrace;
                l->line_number = current_line;
                continue; /* Skip advancing current character */
            }
        }

        /* For = we need to check the next character for another = or > */
        else if( curr_char == '=' ) {
            l = new_lexeme();
            l->line_number = current_line;
            curr_char = get_next_char();
            if( curr_char == '>' ) {
                l->type = lex_dubarrow;
            }
            else if( curr_char == '=' ) {
                l->type = lex_dubeq;
            }
            else {
                l->type = lex_eq;
                continue; /* Skip advancing current character */
            }
        }

        /* For . we need to check if it's a single or double */
        else if( curr_char == '.' ) {
            l = new_lexeme();
            l->line_number = current_line;
            curr_char = get_next_char();
            if( curr_char == '.' ) {
                l->type = lex_dubperiod;
            }
            else {
                l->type = lex_period;
                continue; /* Skip advancing current character */
            }
        }

        /* Check for -> or comments (--) */
        else if( curr_char == '-' ) {
            l = new_lexeme();
            l->line_number = current_line;
            curr_char = get_next_char();
            if( curr_char == '>' ) {
                l->type = lex_arrow;
            }
            else if( curr_char == '-' ) {
                /* One line comment, eat input until newline */
                l->type = lex_newline;
                do {
                    curr_char = get_next_char();
                } while( curr_char != EOF && curr_char != '\n' && curr_char != '\r' );
                /* Check for \n\r */
                current_line++;
                if( curr_char == '\n' ) {
                    curr_char = get_next_char();
                    if( curr_char != '\r' ) {
                        continue; /* Skip advancing current character */
                    }
                    /* Otherwise fall through */
                }
            }
            else {
                l->type = lex_ident;
                ident_buf[0] = '-';
                l->value.s = build_ident(1);
                continue; /* Skip advancing current character */
            }
        }

        /* Check for carriage return */
        else if( curr_char == '\n' ) {
            l = new_lexeme();
            l->type = lex_newline;
            l->line_number = current_line;
            current_line++;
            /* Have to check for \n\r */
            curr_char = get_next_char();
            if( curr_char != '\r' ) {
                continue; /* Didn't grab \r so we can't ignore it */
            }
            /* Otherwise we ignore the \r and fall through */
        }
        /* Making this a separate check just simplifies things */
        else if( curr_char == '\r' ) {
            l = new_lexeme();
            l->type = lex_newline;
            l->line_number = current_line;
            current_line++;
        }

        /* String handling */
        else if( curr_char == '"' ) {
            l = new_lexeme();
            l->type = lex_string;
            l->line_number = current_line;
            ident_pos = 0;
            while( 1 ) {
                curr_char = get_next_char();
                /* Escape sequences */
                if( curr_char == '\\' ) {
                    curr_char = get_next_char();
                    if( curr_char == '\\' ) {
                        ident_buf[ident_pos] = '\\';
                        ident_pos++;
                    }
                    else if( curr_char == 'n' ) {
                        ident_buf[ident_pos] = '\n';
                        ident_pos++;
                    }
                    else if( curr_char == 'r' ) {
                        ident_buf[ident_pos] = '\r';
                        ident_pos++;
                    }
                    else if( curr_char == 't' ) {
                        ident_buf[ident_pos] = '\t';
                        ident_pos++;
                    }
                    else if( curr_char == '0' ) {
                        ident_buf[ident_pos] = '\0';
                        ident_pos++;
                    }
                    else if( curr_char == '"' ) {
                        ident_buf[ident_pos] = '"';
                        ident_pos++;
                    }
                    else {
                        ident_buf[ident_pos] = (char)curr_char;
                        ident_pos++;
                    }
                }
                else if( curr_char == '\n' ) {
                    current_line++;
                }
                else if( curr_char == '\r' ) {
                    /* \n\r is one line */
                    if( ident_pos == 0 || ident_buf[ident_pos-1] != '\n' ) {
                        current_line++;
                    }
                }
                else if( curr_char == '"' ) {
                    break;
                }
                else if( curr_char == EOF ) {
                    /* TODO: Error */
                    return NULL;
                }
                else {
                    ident_buf[ident_pos] = (char)curr_char;
                    ident_pos++;
                }
                if( ident_pos == LEX_IDENT_SIZE ) {
                    /* Maxed out our ident buffer, make new string and restart */
                    ident_buf[ident_pos] = '\0';
                    l->value.s = build_ident(LEX_IDENT_SIZE);
                    l = new_lexeme();
                    l->type = lex_string;
                    l->line_number = current_line;
                    ident_pos = 0;
                }
            }
            if( ident_pos == 0 ) {
                printf("Empty string\n");
            }
            ident_buf[ident_pos] = '\0';
            l->value.s = build_ident(ident_pos);
        }

        /* Number literals */
        else if( isdigit(curr_char) ) {
            l = new_lexeme();
            l->line_number = current_line;
            l->type = lex_int; /* Default to int */
            ident_buf[0] = '0';
            ident_pos = 1;
            /* Check for hex */
            if( curr_char == '0' ) {
                curr_char = get_next_char();
                /* Got hex */
                if( curr_char == 'x' || curr_char == 'X' ) {
                    ident_buf[1] = 'x';
                    ident_pos = 2;
                    do {
                        curr_char = get_next_char();
                        if( isdigit(curr_char) ||
                            (curr_char >= 'a' && curr_char <= 'f') ||
                            (curr_char >= 'A' && curr_char <= 'F') ) {
                            ident_buf[ident_pos] = (char)curr_char;
                            ident_pos++;
                        }
                        else {
                            break;
                        }
                    } while( ident_pos < LEX_IDENT_SIZE-1 );
                    ident_buf[ident_pos] = '\0'; /* Needed for strtol */
                    l->value.i = strtol(ident_buf, NULL, 16);
                    continue; /* Skip advancing current character */
                }
            }
            /* Did not get hex */
            while( ident_pos < LEX_IDENT_SIZE-1 &&
                (isdigit(curr_char) || curr_char == '.') ) {
                if( curr_char == '.' ) {
                    /* Check to make sure this is the first period */
                    if( l->type == lex_int ) {
                        l->type = lex_float;
                    }
                    /* Second period might be of the form "1.0.", in which case
                       we want to grab "1.0" and continue from the second ".",
                       or it might be of the form "1..", in which case we want
                       to grab "1" and make a new ".." lexeme (since we already
                       grabbed both "."). */
                    else {
                        /* .. case */
                        if( ident_buf[ident_pos-1] == '.' ) {
                            ident_pos--;
                            l->type = lex_int;
                            /* Have to make ".." lexeme here since we ate input */
                            l2 = new_lexeme();
                            l2->type = lex_dubperiod;
                            l2->line_number = current_line;
                            /* Grab next character and bypass falling through */
                            curr_char = get_next_char();
                            break;
                        }
                        /* x.x. case */
                        else {
                            break;
                        }
                    }
                }
                ident_buf[ident_pos] = (char)curr_char;
                ident_pos++;
                curr_char = get_next_char();
            }
            ident_buf[ident_pos] = '\0';
            if( l->type == lex_int ) {
                l->value.i = strtol(ident_buf, NULL, 10);
            }
            else {
                l->value.f = strtod(ident_buf, NULL);
            }
            continue; /* Skip advancing current character */
        }

        /* Whitespace to ignore */
        else if( isspace(curr_char) ) {
            /* Do nothing */
        }

        /* Identifiers as a catch-all */
        else {
            l = new_lexeme();
            l->type = lex_ident;
            l->line_number = current_line;
            ident_buf[0] = curr_char;
            ident_pos = 1;
            curr_char = get_next_char();
            while( ident_pos < LEX_IDENT_SIZE-1 && valid_ident(curr_char) ) {
                ident_buf[ident_pos] = (char)curr_char;
                ident_pos++;
                curr_char = get_next_char();
            }
            ident_buf[ident_pos] = '\0';
            l->value.s = build_ident(ident_pos);
            continue; /* Skip advancing current character */
        }

        /* Grab next character and loop */
        curr_char = get_next_char();
    }
    /* Always ensure there's at least 1 trailing newline */
    if( l_end->type != lex_newline ) {
        l_end = new_lexeme();
        l_end->type = lex_newline;
        l_end->line_number = current_line;
    }
    return list;
}

/*
 * Simple filter that eats useless newlines. These include:
 * -Newlines before any other lexeme
 * -Instances where there are two or more newlines
 */
lex_list * filter_extra_newlines( lex_list *lexes ) {
    lex_list *l, *l2;
    if( !lexes ) {
        return NULL;
    }
    /* Starting newlines */
    while( lexes && lexes->type == lex_newline ) {
        l = lexes;
        lexes = lexes->next;
        free(l);
    }
    /* Three or more newlines in a row */
    l = list;
    while( l ) {
        if( l->type == lex_newline ) {
            if( l->next && l->next->type == lex_newline ) {
                l2 = l->next;
                l->next = l->next->next;
                free(l2);
                continue;
            }
        }
        l = l->next;
    }
    return lexes;
}

/*
 * Filter that joins adjacent strings. Will also eat newlines between two
 * otherwise adjacent strings.
 */
lex_list * filter_join_strings( lex_list *lexes ) {
    lex_list *l, *l2, *l3;
    int len;
    l = lexes;
    while( l ) {
        if( l->type == lex_string ) {
            l2 = l->next;
            l3 = NULL;
            /* Find the next non-newline lexeme */
            while( l2->type == lex_newline ) {
                l2 = l2->next;
            }
            if( l2 && l2->type == lex_string ) {
                /* Are the strings strictly adjacent? */
                if( l->next->type != lex_string ) {
                    l3 = l->next;
                }
                l->next = l2->next;
                len = strlen(l->value.s) + strlen(l2->value.s);
                l->value.s = (char*)realloc(l->value.s, sizeof(char) * (len + 1));
                strcat(l->value.s, l2->value.s);
                /* Free up now extraneous memory */
                free(l2->value.s);
                free(l2);
                /* Munch any newlines we're now jumping over */
                while( l3 && l3->type == lex_newline ) {
                    l2 = l3;
                    l3 = l3->next;
                    free(l2);
                }
            }
        }
        l = l->next;
    }
    return lexes;
}

void printlex( lex_list *lex ) {
    switch( lex->type ) {
    /* Vals */
    case lex_ident: printf("i:%s", lex->value.s); break;
    case lex_int: printf("%ld", lex->value.i); break;
    case lex_float: printf("%f", lex->value.f); break;
    case lex_string: printf("\"%s\"", lex->value.s); break;
    /* Lexemes */
    case lex_lparen: printf("("); break;
    case lex_rparen: printf(")"); break;
    case lex_lbrace: printf("["); break;
    case lex_rbrace: printf("]"); break;
    case lex_lbracket: printf("{"); break;
    case lex_rbracket: printf("}"); break;
    case lex_arrow: printf("->"); break;
    case lex_dubarrow: printf("=>"); break;
    case lex_lambda: printf("\\"); break;
    case lex_colon: printf(":"); break;
    case lex_typeof: printf("::"); break;
    case lex_bar: printf("|"); break;
    case lex_comma: printf(","); break;
    case lex_semicolon: printf(";"); break;
    case lex_eq: printf("="); break;
    case lex_dubeq: printf("=="); break;
    case lex_period: printf("."); break;
    case lex_dubperiod: printf(".."); break;
    case lex_backtick: printf("`"); break;
    case lex_newline: printf("\n"); break;
    /* Keywords */
    case lex_case: printf("case"); break;
    case lex_class: printf("class"); break;
    case lex_export: printf("export"); break;
    case lex_import: printf("import"); break;
    case lex_kernel: printf("kernel"); break;
    case lex_in: printf("in"); break;
    case lex_instance: printf("instance"); break;
    case lex_let: printf("let"); break;
    case lex_of: printf("of"); break;
    case lex_otherwise: printf("otherwise"); break;
    case lex_type: printf("type"); break;
    case lex_typeclass: printf("typeclass"); break;
    case lex_typesyn: printf("typesyn"); break;
    case lex_where: printf("where"); break;
    default: printf("<<unknown>>"); break;
    }
}

void printlexlist( lex_list *lex ) {
    while( lex ) {
        printlex(lex);
        if( lex->type != lex_newline ) {
            printf(" ");
        }
        lex = lex->next;
    }
}
