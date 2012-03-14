/*
 * typechecker.c
 * By Steven Smith
 */

#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include "gc.h"
#include "parsecomb.h"
#include "depanalyzer.h"

/*
*** Id.hs
type Id  = String

enumId  :: Int -> Id
enumId n = "v" ++ show n
*/

typedef char id;
static unsigned int curr_id = 0;

static id * enum_id() {
    char *c;
    c = (char*)GC_MALLOC(sizeof(char) * 8);
    snprintf(c, 8, "v%d", ++curr_id);
    return c;
}

static int id_eq( id *i1, id *i2 ) {
    return !strcmp(i1, i2);
}

/*
*** Kind.hs
data Kind  = Star | Kfun Kind Kind
             deriving Eq
*/

typedef struct kind {
    struct kind *l;
    struct kind *r;
} kind;

static int kind_eq( kind *k1, kind *k2 ) {
    /* Can't compare nulls */
    if( !k1 || !k2 ) {
        return 0;
    }
    /* Star == Star */
    if( !k1->l && !k2->l ) {
        return 1;
    }
    /* Star -> Star == Star -> Star */
    if( k1->l && k2->l ) {
        return kind_eq(k1->l, k2->l) && kind_eq(k1->r, k2->r);
    }
    /* Otherwise false */
    return 0;
}

static kind * kfun( kind *k1, kind *k2 ) {
    kind *result;
    result = (kind*)GC_MALLOC(sizeof(kind));
    result->l = k1;
    result->r = k2;
    return result;
}

static kind * kstar() {
    kind *result;
    result = (kind*)GC_MALLOC(sizeof(kind));
    result->l = NULL;
    result->r = NULL;
    return result;
}

static void print_kind( kind *k ) {
    if( !k ) {
        printf("<null>");
    }
    else if( k->l ) {
        print_kind(k->l);
        printf("->");
        print_kind(k->r);
    }
    else {
        printf("*");
    }
}

/*
*** Type.hs
data Type  = TVar Tyvar | TCon Tycon | TAp  Type Type | TGen Int
             deriving Eq

data Tyvar = Tyvar Id Kind
             deriving Eq

data Tycon = Tycon Id Kind
             deriving Eq
*/

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

static int type_eq( type *t1, type *t2 );

static int typevar_eq( typevar *t1, typevar *t2 ) {
    return id_eq(t1->i, t2->i) && kind_eq(t1->k, t2->k);
}

static int typecon_eq( typecon *t1, typecon *t2 ) {
    return id_eq(t1->i, t2->i) && kind_eq(t1->k, t2->k);
}

static int typeap_eq( typeap *t1, typeap *t2 ) {
    return type_eq(t1->l, t2->l) && type_eq(t1->r, t2->r);
}

static int type_eq( type *t1, type *t2 ) {
    /* Can't compare nulls */
    if( !t1 || !t2 ) {
        return 0;
    }
    /* Type mismatch */
    if( t1->type != t2->type ) {
        return 0;
    }
    /* Type variables */
    if( t1->type == type_var ) {
        return typevar_eq(t1->val.tv, t2->val.tv);
    }
    /* Type constants */
    else if (t1->type == type_con ) {
        return typecon_eq(t1->val.tc, t2->val.tc);
    }
    /* Type applications */
    else if (t1->type == type_ap ) {
        return typeap_eq(t1->val.ta, t2->val.ta);
    }
    /* Generic/quantified types */
    else if (t1->type == type_gen ) {
        return t1->val.tg == t2->val.tg;
    }
    /* Catch-all fail */
    else {
        return 0;
    }
}

static void print_type( type *t ) {
    switch( t->type ) {
    case type_var:
        printf("Tyvar %s: ", t->val.tv->i);
        print_kind(t->val.tv->k);
        break;
    case type_con:
        printf("Tycon %s: ", t->val.tc->i);
        print_kind(t->val.tc->k);
        break;
    case type_ap:
        printf("(");
        print_type(t->val.ta->l);
        printf(" `fn` ");
        print_type(t->val.ta->r);
        printf(")");
        break;
    case type_gen:
        printf("Tygen %d", t->val.tg);
        break;
    default:
        fprintf(stderr, "ERROR: Invalid type in print_type!\n");
        break;
    }
}

/*
class HasKind t where
  kind :: t -> Kind
instance HasKind Tyvar where
  kind (Tyvar v k) = k
instance HasKind Tycon where
  kind (Tycon v k) = k
instance HasKind Type where
  kind (TCon tc) = kind tc
  kind (TVar u)  = kind u
  kind (TAp t _) = case (kind t) of
                     (Kfun _ k) -> k
*/

static kind * get_kind( type *t ) {
    kind *k;
    if( !t ) {
        fprintf(stderr, "ERROR: Received null type in get_kind!\n");
        return NULL;
    }
    if( t->type == type_var ) {
        return t->val.tv->k;
    }
    else if( t->type == type_con ) {
        return t->val.tc->k;
    }
    else if (t->type == type_ap ) {
        k = get_kind(t->val.ta->l);
        return k->r;
    }
    else if( t->type == type_gen ) {
        return kstar();
    }
    else {
        fprintf(stderr, "ERROR: Invalid type in get_kind!\n");
        return NULL;
    }
}

static type * tyvar( typevar *t ) {
    type *result;
    result = (type*)GC_MALLOC(sizeof(type));
    result->type = type_var;
    result->val.tv = t;
    result->next = NULL;
    return result;
}

static typevar * new_tyvar( id *i, kind *k ) {
    typevar *result;
    result = (typevar*)GC_MALLOC(sizeof(typevar));
    result->i = i;
    result->k = k;
    return result;
}

static type * tycon( id *i, kind *k ) {
    type *result;
    result = (type*)GC_MALLOC(sizeof(type));
    result->type = type_con;
    result->val.tc = (typecon*)GC_MALLOC(sizeof(typecon));
    result->val.tc->i = i;
    result->val.tc->k = k;
    result->next = NULL;
    return result;
}

static type * tyap( type *t1, type *t2 ) {
    type *result;
    result = (type*)GC_MALLOC(sizeof(type));
    result->type = type_ap;
    result->val.ta = (typeap*)GC_MALLOC(sizeof(typeap));
    result->val.ta->l = t1;
    result->val.ta->r = t2;
    result->next = NULL;
    return result;
}

static type * tygen( int i ) {
    type *result;
    result = (type*)GC_MALLOC(sizeof(type));
    result->type = type_gen;
    result->val.tg = i;
    result->next = NULL;
    return result;
}

/*
 * Duplicates the given type. This is mostly useful for stripping out types
 * from type lists.
 */
static type * type_dup( type *t ) {
    if( t->type == type_var ) {
        return tyvar(new_tyvar(t->val.tv->i, t->val.tv->k));
    }
    else if( t->type == type_con ) {
        return tycon(t->val.tc->i, t->val.tc->k);
    }
    else if( t->type == type_ap ) {
        return tyap(type_dup(t->val.ta->l), type_dup(t->val.ta->r));
    }
    else if( t->type == type_gen ) {
        return tygen(t->val.tg);
    }
    else {
        fprintf(stderr, "ERROR: Invalid type in type_dup!\n");
        return NULL;
    }
}

static type * pair_types( type *t1, type *t2 ) {
    t1->next = t2;
    return t1;
}

/*
tUnit    = TCon (Tycon "()" Star)
tChar    = TCon (Tycon "Char" Star)
tInt     = TCon (Tycon "Int" Star)
tInteger = TCon (Tycon "Integer" Star)
tFloat   = TCon (Tycon "Float" Star)
tDouble  = TCon (Tycon "Double" Star)
*/

static type * tUnit;
static type * tChar;
static type * tInt;
static type * tFloat;
static type * tString;

/*
tList    = TCon (Tycon "[]" (Kfun Star Star))
tArrow   = TCon (Tycon "(->)" (Kfun Star (Kfun Star Star)))
tTuple2  = TCon (Tycon "(,)" (Kfun Star (Kfun Star Star)))
*/

static type * tList;
static type * tArrow;
static type * tTuple2;

static void generate_types() {
    tUnit  = tycon("()",    kstar());
    tChar  = tycon("Char",  kstar());
    tInt   = tycon("Int",   kstar());
    tFloat = tycon("Float", kstar());
    tString = tycon("String", kstar());
    tList = tycon("[]", kfun( kstar(), kstar()));
    tArrow = tycon("(->)", kfun( kstar(), kfun( kstar(), kstar())));
    tTuple2 = tycon("(,)", kfun( kstar(), kfun( kstar(), kstar())));
}

/* Skipping these so I don't go crazy
tTuple3
 = TCon (Tycon "(,,)" (Kfun Star (Kfun Star (Kfun Star Star))))
tTuple4
 = TCon (Tycon "(,,,)" (Kfun Star (Kfun Star (Kfun Star (Kfun Star Star)))))
tTuple5
 = TCon (Tycon "(,,,,)" (Kfun Star (Kfun Star (Kfun Star (Kfun Star (Kfun Star Star))))))
tTuple6
 = TCon (Tycon "(,,,,,)" (Kfun Star (Kfun Star (Kfun Star (Kfun Star (Kfun Star (Kfun Star Star)))))))
tTuple7
 = TCon (Tycon "(,,,,,,)" (Kfun Star (Kfun Star (Kfun Star (Kfun Star (Kfun Star (Kfun Star (Kfun Star Star))))))))
*/

/*
tString    :: Type
tString     = list tChar

infixr      4 `fn`
fn         :: Type -> Type -> Type
a `fn` b    = TAp (TAp tArrow a) b
*/

static type * tyap_fn( type *t1, type *t2 ) {
    return tyap(tyap(tArrow, t1), t2);
}

/* Note:
   'fold_fn' implements 'foldr fn t ts', as it is used multiple times
   Also, the copy here is shallow, so the contained types keep their next
   member. This shouldn't cause problems (I hope). */
static type * fold_fn( type *t1, type *t2 ) {
    if( !t2 ) {
        return t1;
    }
    else {
        return tyap_fn(type_dup(t2), fold_fn(t1, t2->next));
    }
}

/*
list       :: Type -> Type
list t      = TAp tList t

pair       :: Type -> Type -> Type
pair a b    = TAp (TAp tTuple2 a) b
*/

/*
*** Subst.hs
type Subst  = [(Tyvar, Type)]
*/

typedef struct subst {
    typevar *tv;
    type *type;
    struct subst *next;
} subst;

static void print_substs( subst *s ) {
    while( s ) {
        printf("%s (", s->tv->i);
        print_kind(s->tv->k);
        printf(") -> ");
        print_type(s->type);
        printf("\n");
        s = s->next;
    }
}

/*
nullSubst  :: Subst
nullSubst   = []

NOTE: This is represented as a null pointer
*/

/*
(+->)      :: Tyvar -> Type -> Subst
u +-> t     = [(u, t)]
*/

static subst * apply_subst( typevar *tv, type *t ) {
    subst *result;
    result = (subst*)GC_MALLOC(sizeof(subst));
    result->tv = tv;
    result->type = t;
    result->next = NULL;
    return result;
}

/* Note: Unused
static void concat_subst( subst *s1, subst *s2 ) {
    subst *s = s1;
    if( !s ) {
        return;
    }
    while( s->next ) {
        s = s->next;
    }
    s->next = s2;
}
*/

/*
class Types t where
  apply :: Subst -> t -> t
  tv    :: t -> [Tyvar]

instance Types Type where
  apply s (TVar u)  = case lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TAp l r) = TAp (apply s l) (apply s r)
  apply s t         = t

  tv (TVar u)  = [u]
  tv (TAp l r) = tv l `union` tv r
  tv t         = []

instance Types a => Types [a] where
  apply s = map (apply s)
  tv      = nub . concat . map tv
*/

/*
 * lookup: Haskell prelude function
 * lookup :: Eq a => a -> [(a, b)] -> Maybe b
 * Given a list of (a,b) and an a, returns the corresponding b if it exists.
 */
static type * lookup( typevar *tv, subst *s ) {
    while( s ) {
        if( typevar_eq(tv, s->tv) ) {
            return s->type;
        }
        s = s->next;
    }
    return NULL;
}

/*
 * Attempts to apply the substitution s to the type t, producing a new type.
 */
static type * apply( subst *s, type *t ) {
    type *result;
    if( !t ) {
        return NULL;
    }
    else if( t->type == type_var ) {
        result = lookup(t->val.tv, s);
        if( result ) {
            return pair_types(type_dup(result), apply(s, t->next));
        }
        else {
            return pair_types(type_dup(t), apply(s, t->next));
        }
    }
    else if( t->type == type_ap ) {
        return pair_types(tyap(apply(s, t->val.ta->l), apply(s, t->val.ta->r)),
            apply(s, t->next));
    }
    else {
        return pair_types(type_dup(t), apply(s, t->next));
    }
}

typedef struct typevar_list {
    typevar *tv;
    struct typevar_list *next;
} typevar_list;

/* Note; Unused
static int typevar_list_eq( typevar_list *tvl1, typevar_list *tvl2 ) {
    while( tvl1 && tvl2 ) {
        if( !typevar_eq(tvl1->tv, tvl2->tv) ) {
            return 0;
        }
        tvl1 = tvl1->next;
        tvl2 = tvl2->next;
    }
    return 1;
}
*/

static typevar_list * new_typevar_list( typevar *tv ) {
    typevar_list *result;
    result = (typevar_list*)GC_MALLOC(sizeof(typevar_list));
    result->tv = tv;
    result->next = NULL;
    return result;
}

/*
 * Nub removes all duplcates from the given list.
 */
static void nub( typevar_list *tvl ) {
    typevar_list *tvl2 = tvl;
    while( tvl ) {
        while( tvl2->next ) {
            /* Check for duplicates */
            if( typevar_eq(tvl->tv, tvl2->next->tv) ) {
                tvl2->next = tvl2->next->next;
            }
            else {
                tvl2 = tvl2->next;
            }
        }
        tvl = tvl2 = tvl->next;
    }
}

static typevar_list * typevar_list_join( typevar_list *tvl1,
    typevar_list *tvl2) {
    typevar_list *result, *curr;
    result = curr = NULL;
    /* Copy tvl1 */
    if( tvl1 ) {
        result = new_typevar_list(tvl1->tv);
        curr = result;
        tvl1 = tvl1->next;
        while( tvl1 ) {
            curr->next = new_typevar_list(tvl1->tv);
            curr = curr->next;
            tvl1 = tvl1->next;
        }
    }
    /* Copy tvl2 */
    if( !result && tvl2 ) {
        result = new_typevar_list(tvl2->tv);
        curr = result;
        tvl2 = tvl2->next;
    }
    while( tvl2 ) {
        curr->next = new_typevar_list(tvl2->tv);
        curr = curr->next;
        tvl2 = tvl2->next;
    }
    return result;
}

/*
 * Corresponds to the function 'tv'
 */
static typevar_list * type_vars( type *t ) {
    typevar_list *result, *r;
    if( t->type == type_var ) {
        result = (typevar_list*)GC_MALLOC(sizeof(typevar_list));
        result->tv = t->val.tv;
        result->next = NULL;
    }
    else if( t->type == type_ap ) {
        result = type_vars(t->val.ta->l);
        if( result ) {
            result->next = type_vars(t->val.ta->r);
        }
        else {
            result = type_vars(t->val.ta->r);
        }
    }
    else {
        result = NULL;
    }
    /* Lists of Types */
    if( t->next && result ) {
        r = result;
        while( r->next ) {
            r = r->next;
        }
        r->next = type_vars(t->next);
        nub(result);
    }
    return result;
}

/*
infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1
*/

/*
 * Compose substitutions
 */
static subst * comp_apply( subst *s1, subst *s2 ) {
    subst *list_head, *list_tail, *s;
    list_head = list_tail = s = NULL;
    while( s2 ) {
        s = apply_subst(s2->tv, apply(s1, s2->type));
        if( list_head ) {
            list_tail->next = s;
            list_tail = s;
        }
        else {
            list_head = s;
            list_tail = s;
        }
        s2 = s2->next;
    }
    if( list_tail ) {
        list_tail->next = s1;
    }
    else {
        list_head = s1;
    }
    return list_head;
}

/*
merge      :: Monad m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return (s1++s2) else fail "merge fails"
 where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v))
                   (map fst s1 `intersect` map fst s2)
*/

static typevar_list * intersect_subst( subst *s1, subst *s2 ) {
    typevar_list *tvl, *tvl_end, *new_tvl;
    subst *sub1, *sub2;
    tvl = NULL;
    sub1 = s1;
    /* Make list of typevars that exist in both substitutions */
    while( sub1 ) {
        sub2 = s2;
        while( sub2 ) {
            if( typevar_eq(sub1->tv, sub2->tv) ) {
                new_tvl = (typevar_list*)GC_MALLOC(sizeof(typevar_list));
                new_tvl->tv = (typevar*)GC_MALLOC(sizeof(typevar));
                new_tvl->tv->i = sub1->tv->i;
                new_tvl->tv->k = sub1->tv->k;
                new_tvl = NULL;
                if( tvl ) {
                    tvl_end = tvl_end->next = new_tvl;
                }
                else {
                    tvl = tvl_end = new_tvl;
                }
            }
            sub2 = sub2->next;
        }
        sub1 = sub1->next;
    }
    /* Get rid of duplicates */
    nub(tvl);
    return tvl;
}

static subst * merge( subst *s1, subst *s2 ) {
    typevar_list *tvl;
    subst *s;
    tvl = intersect_subst(s1, s2);
    /* Check to make sure merge is possible */
    while( tvl ) {
        if( !type_eq(apply(s1, tyvar(tvl->tv)), apply(s2, tyvar(tvl->tv))) ) {
            fprintf(stderr, "ERROR: Merge failed\n");
            return NULL;
        }
        tvl = tvl->next;
    }
    /* Concatenate substitutions */
    if( !s1 ) {
        return s2;
    }
    s = s1;
    while( s->next ) {
        s = s->next;
    }
    s->next = s2;
    return s1;
}

/*
 * elem: Haskell prelude function
 * elem :: Eq a => a -> [a] -> Bool
 * Returns true (1) if the given typevar is in the given list.
 */
static int elem( typevar *tv, typevar_list *tvl ) {
    while( tvl ) {
        /* Found the typevar in the list */
        if( typevar_eq(tv, tvl->tv) ) {
            return 1;
        }
        tvl = tvl->next;
    }
    /* Didn't find the typevar in the list */
    return 0;
}

/*
varBind :: Monad m => Tyvar -> Type -> m Subst

varBind u t | t == TVar u      = return nullSubst
            | u `elem` tv t    = fail "occurs check fails"
            | kind u /= kind t = fail "kinds do not match"
            | otherwise        = return (u +-> t)
*/

static subst * var_bind( typevar *tv, type *t ) {
    if( type_eq(t, tyvar(tv)) ) { 
        return NULL;
    }
    else if( elem(tv, type_vars(t)) ) {
        fprintf(stderr, "ERROR: Occurs check failed\n");
        return NULL;
    }
    else if( !kind_eq(tv->k, get_kind(t)) ) {
        fprintf(stderr, "ERROR: Kinds do not match: ");
        print_kind(tv->k);
        printf(", ");
        print_kind(get_kind(t));
        printf("\n");
        /*return NULL;*/
        return apply_subst(tv, t);
    }
    else {
        return apply_subst(tv, t);
    }
}

/*
*** Unify.hs
class Unify t where
  mgu :: Monad m => t -> t -> m Subst

instance Unify Type where
  mgu (TAp l r) (TAp l' r') = do s1 <- mgu l l'
                                 s2 <- mgu (apply s1 r) (apply s1 r')
                                 return (s2 @@ s1)
  mgu (TVar u) t        = varBind u t
  mgu t (TVar u)        = varBind u t
  mgu (TCon tc1) (TCon tc2)
             | tc1==tc2 = return nullSubst
  mgu t1 t2             = fail "types do not unify"

instance (Unify t, Types t) => Unify [t] where
  mgu (x:xs) (y:ys) = do s1 <- mgu x y
                         s2 <- mgu (apply s1 xs) (apply s1 ys)
                         return (s2 @@ s1)
  mgu []     []     = return nullSubst
  mgu _      _      = fail "lists do not unify"
*/

static subst * mgu_single( type *t1, type *t2 ) {
    subst *s1, *s2;
    if( (t1->type == type_ap) && (t2->type == type_ap) ) {
        s1 = mgu_single(t1->val.ta->l, t2->val.ta->l);
        s2 = mgu_single(apply(s1, t1->val.ta->r), apply(s1, t2->val.ta->r));
        return comp_apply(s2, s1);
    }
    else if( t1->type == type_var ) {
        return var_bind(t1->val.tv, t2);
    }
    else if( t2->type == type_var ) {
        return var_bind(t2->val.tv, t1);
    }
    else if( (t1->type == type_con) && (t2->type == type_con) ) {
        if( typecon_eq(t1->val.tc, t2->val.tc) ) {
            return NULL; /* Null substitution */
        }
    }
    /* Else fail */
    fprintf(stderr, "ERROR: Types do not unify: ");
    print_type(t1);
    printf(", ");
    print_type(t2);
    printf("\n");
    return NULL;
}

/*
static subst * mgu( type *t1, type *t2 ) {
    subst *s1, *s2;
    if( !t1 && !t2 ) {
        return NULL; *//* Null substitution *//*
    }
    else if( t1 && t2 ) {
        if( !t1->next && !t2->next ) {
            return mgu_single(t1, t2);
        }
        else if( !(t1->next && t2->next) ) {
            *//* The two lists much be the same length *//*
            fprintf(stderr, "ERROR: Lists do not unify\n");
            return NULL;
        }
        s1 = mgu_single(t1, t2);
        s2 = mgu(apply(s1, t1->next), apply(s1, t2->next));
        return comp_apply(s2, s1);
    }
    *//* Else fail *//*
    fprintf(stderr, "ERROR: Lists do not unify\n");
    return NULL;
}
*/

/*
class Match t where
  match :: Monad m => t -> t -> m Subst

instance Match Type where
  match (TAp l r) (TAp l' r') = do sl <- match l l'
                                   sr <- match r r'
                                   merge sl sr
  match (TVar u)   t | kind u == kind t = return (u +-> t)
  match (TCon tc1) (TCon tc2)
           | tc1==tc2         = return nullSubst
  match t1 t2                 = fail "types do not match"

instance Match t => Match [t] where
   match ts ts' = do ss <- sequence (zipWith match ts ts')
                     foldM merge nullSubst ss
*/

static subst * match( type *t1, type *t2 );

static subst * match_single( type *t1, type *t2 ) {
    subst *sl, *sr;
    if( (t1->type == type_ap) && (t2->type == type_ap) ) {
        sl = match(t1->val.ta->l, t2->val.ta->l);
        sr = match(t1->val.ta->r, t2->val.ta->r);
        return merge(sl, sr);
    }
    else if( (t1->type == type_var) && (t2->type == type_var) ) {
        if( kind_eq(get_kind(t1), get_kind(t2)) ) {
            return apply_subst(t1->val.tv, t2);
        }
    }
    else if( (t1->type == type_con) && (t2->type == type_con) ) {
        if( typecon_eq(t1->val.tc, t2->val.tc) ) {
            return NULL; /* Null substitution */
        }
    }
    /* Else fail */
    fprintf(stderr, "ERROR: Types do not match\n");
    return NULL;
}

static subst * match( type *t1, type *t2 ) {
    subst *s1, *s2;
    if( !t1 && !t2 ) {
        return NULL; /* Null substitution */
    }
    else if( t1 && t2 ) {
        s1 = match_single(t1, t2);
        s2 = match(t1->next, t2->next);
        return merge(s1, s2);
    }
    /* Else fail */
    fprintf(stderr, "ERROR: Lists do not match\n");
    return NULL;
}

/*
*** Pred.hs
data Qual t = [Pred] :=> t
              deriving Eq

data Pred   = IsIn Id [Type]
              deriving Eq
*/

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

static pred * dup_pred( pred *p ) {
    pred *result;
    result = (pred*)GC_MALLOC(sizeof(pred));
    result->i = p->i;
    result->t = p->t;
    if( p->next ) {
        result->next = dup_pred(p->next);
    }
    else {
        result->next = NULL;
    }
    return result;
}

/* The difference between this and the previous function is only dups 1 pred */
static pred * pred_dup( pred *p ) {
    pred *result;
    result = (pred*)GC_MALLOC(sizeof(pred));
    result->i = p->i;
    result->t = p->t;
    result->next = NULL;
    return result;
}

static int pred_eq( pred *p1, pred *p2 ) {
    if( p1 && p2 ) {
        if( id_eq(p1->i, p2->i) && type_eq(p1->t, p2->t) ) {
            return 1;
        }
    }
    return 0;
}

static int preds_eq( pred *p1, pred *p2 ) {
    if( !p1 && !p2 ) {
        return 1;
    }
    else if( !p1 || !p2 ) {
        return 0;
    }
    else {
        return pred_eq(p1, p2) && pred_eq(p1->next, p2->next);
    }
}

static int qual_eq( qual *q1, qual *q2 ) {
    if( !q1 && !q2 ) {
        return 1;
    }
    else if( !q1 || !q2 ) {
        return 0;
    }
    else {
        if( q1->type == q2->type ) {
            if( q1->type == qual_type ) {
                return preds_eq(q1->p, q2->p) && type_eq(q1->val.t, q2->val.t);
            }
            else {
                return preds_eq(q1->p, q2->p) && pred_eq(q1->val.p, q2->val.p);
            }
        }
        else {
            return 0;
        }
    }
}

static void print_pred_list( pred *p ) {
    while( p ) {
        printf("%s: ", p->i);
        print_type(p->t);
        if( p->next ) {
            printf(", ");
        }
        p = p->next;
    }
}

static void print_qual_type( qual *q ) {
    if( q->type == qual_type ) {
        printf("qual (");
    }
    else {
        printf("qual P (");
    }
    print_pred_list(q->p);
    printf(") ");
    print_type(q->val.t);
}

/*
predHead            :: Pred -> Id
predHead (IsIn i ts) = i

instance Types t => Types (Qual t) where
  apply s (ps :=> t) = apply s ps :=> apply s t
  tv (ps :=> t)      = tv ps `union` tv t

instance Types Pred where
  apply s (IsIn i ts) = IsIn i (apply s ts)
  tv (IsIn i ts)      = tv ts

instance Unify Pred where
   mgu = lift mgu

instance Match Pred where
   match = lift match
*/

static pred * is_in( id *i, type *t ) {
    pred *result;
    result = (pred*)GC_MALLOC(sizeof(pred));
    result->i = i;
    result->t = t;
    result->next = NULL;
    return result;
}

static pred * pred_join( pred *p1, pred *p2 ) {
    pred *result, *curr;
    result = curr = NULL;
    /* Copy p1 */
    if( p1 ) {
        result = is_in(p1->i, p1->t);
        curr = result;
        p1 = p1->next;
        while( p1 ) {
            curr->next = is_in(p1->i, p1->t);
            curr = curr->next;
            p1 = p1->next;
        }
    }
    /* Copy p2 */
    if( !result && p2 ) {
        result = is_in(p2->i, p2->t);
        curr = result;
        p2 = p2->next;
    }
    while( p2 ) {
        curr->next = is_in(p2->i, p2->t);
        curr = curr->next;
        p2 = p2->next;
    }
    return result;
}

static type * type_join( type *t1, type *t2 ) {
    type *result, *curr;
    result = curr = NULL;
    /* Copy t1 */
    if( t1 ) {
        result = type_dup(t1);
        curr = result;
        t1 = t1->next;
        while( t1 ) {
            curr->next = type_dup(t1);
            curr = curr->next;
            t1 = t1->next;
        }
    }
    /* Copy t2 */
    if( !result && t2 ) {
        result = type_dup(t2);
        curr = result;
        t2 = t2->next;
    }
    while( t2 ) {
        curr->next = type_dup(t2);
        curr = curr->next;
        t2 = t2->next;
    }
    return result;
}

static qual * qualified_type( pred *p, type *t ) {
    qual *result;
    result = (qual*)GC_MALLOC(sizeof(qual));
    result->type = qual_type;
    result->p = p;
    result->val.t = t;
    return result;
}

static qual * qualified_pred( pred *p1, pred *p2 ) {
    qual *result;
    result = (qual*)GC_MALLOC(sizeof(qual));
    result->type = qual_pred;
    result->p = p1;
    result->val.p = p2;
    return result;
}

static pred * apply_pred( subst *s, pred *p ) {
    pred *result;
    if( !p ) {
        return NULL;
    }
    result = is_in(p->i, apply(s, p->t));
    result->next = apply_pred(s, p->next);
    return result;
}

static qual * apply_qual( subst *s, qual *q ) {
    qual *result;
    if( q->type == qual_pred ) {
        result = qualified_pred(apply_pred(s, q->p), apply_pred(s, q->val.p));
    }
    else if( q->type == qual_type ) {
        result = qualified_type(apply_pred(s, q->p), apply(s, q->val.t));
    }
    else {
        fprintf(stderr, "ERROR: Bad qual tag in apply_qual\n");
        result = NULL;
    }
    return result;
}

/* Corresponds to the function 'tv' */
static typevar_list * type_vars_pred( pred *p ) {
    typevar_list *result;
    if( !p ) {
        return NULL;
    }
    else {
        result = type_vars(p->t);
        result->next = type_vars_pred(p->next);
        return result;
    }
}

/*
 * Note: This works slightly different than the Haskell version due to the fact
 * that the Haskell version uses 'union', while this uses 'nub'. The difference
 * is that union will keep duplicates in the first list, while the nub is
 * performed after the lists are joined in our version. This means the behavior
 * is slightly different, but I don't know why that would cause any problems.
 */
static typevar_list * type_vars_qual( qual *q ) {
    typevar_list *tvl1, *tvl2, *result;
    tvl1 = type_vars_pred(q->p);
    /* We have to match on the type, so this is all much more verbose */
    if( q->type == qual_type ) {
        tvl2 = type_vars(q->val.t);
    }
    else if( q->type == qual_pred ) {
        tvl2 = type_vars_pred(q->val.p);
    }
    else {
        fprintf(stderr, "ERROR: Bad qual tag in type_vars_qual\n");
        return NULL;
    }
    result = typevar_list_join(tvl1, tvl2);
    nub(result);
    return result;
}

/* Note; Unused
static subst * mgu_pred( pred *p1, pred *p2 ) {
    if( p1 && p2 && id_eq(p1->i, p2->i) ) {
        return mgu(p1->t, p2->t);
    }
    else {
        fprintf(stderr, "ERROR: Classes differ\n");
        return NULL;
    }
}
*/

static subst * match_pred( pred *p1, pred *p2 ) {
    if ( p1 && p2 && id_eq(p1->i, p2->i) ) {
        return match(p1->t, p2->t);
    }
    else {
        fprintf(stderr, "ERROR: Classes differ\n");
        return NULL;
    }
}

/* Note: lift is skipped because we need separate mgu and match functions
   anyway, and all lift is used for are those two functions.

lift m (IsIn i ts) (IsIn i' ts')
         | i == i'   = m ts ts'
         | otherwise = fail "classes differ"
*/

/*
type Class    = ([Tyvar], [Pred], [Inst])
type Inst     = Qual Pred
*/

typedef struct inst {
    qual *q;
    struct inst *next;
} inst;

typedef struct class {
    typevar_list *tv;
    pred *p;
    inst *i;
} class;

static inst * new_inst( qual *q, inst *next ) {
    inst *result;
    result = (inst*)GC_MALLOC(sizeof(inst));
    result->q = q;
    result->next = next;
    return result;
}

static class * new_class( typevar_list *tv, pred *p, inst *i ) {
    class *result;
    result = (class*)GC_MALLOC(sizeof(class));
    result->tv = tv;
    result->p = p;
    result->i = i;
    return result;
}

/*
data ClassEnv = ClassEnv { classes  :: Id -> Maybe Class,
                           defaults :: [Type] }
*/

typedef struct class_env {
    id *i;
    class *c;
    type *t;
    struct class_env *next;
} class_env;

static class * classes_in( class_env *ce, id *i ) {
    if( !ce ) {
        return NULL;
    }
    while( ce ) {
        if( id_eq(i, ce->i) ) {
            return ce->c;
        }
        ce = ce->next;
    }
    /* Given id not in the given class env */
    return NULL;
}

/*
sig       :: ClassEnv -> Id -> [Tyvar]
sig ce i   = case classes ce i of Just (vs, is, its) -> vs
*/

static typevar_list * sig( class_env *ce, id *i ) {
    class *c;
    c = classes_in(ce, i);
    if( c ) {
        return c->tv;
    }
    else {
        /* This shouldn't happen, so error message if it does */
        fprintf(stderr, "ERROR: sig failed\n");
        return NULL;
    }
}

/*
super     :: ClassEnv -> Id -> [Pred]
super ce i = case classes ce i of Just (vs, is, its) -> is
*/

static pred * super( class_env *ce, id *i ) {
    class *c;
    c = classes_in(ce, i);
    if( c ) {
        return c->p;
    }
    else {
        /* This shouldn't happen, so error message if it does */
        fprintf(stderr, "ERROR: super failed\n");
        return NULL;
    }
}

/*
insts     :: ClassEnv -> Id -> [Inst]
insts ce i = case classes ce i of Just (vs, is, its) -> its
*/

static inst * insts( class_env *ce, id *i ) {
    class *c;
    c = classes_in(ce, i);
    if( c ) {
        return c->i;
    }
    else {
        /* This shouldn't happen, so error message if it does */
        fprintf(stderr, "ERROR: insts failed\n");
        return NULL;
    }
}

/*
defined :: Maybe a -> Bool
defined (Just x) = True
defined Nothing  = False
*/
/* 'defined' is unused as we have to use pointers (with NULL) anyway */

/*
modify       :: ClassEnv -> Id -> Class -> ClassEnv
modify ce i c = ce{classes = \j -> if i==j then Just c
                                           else classes ce j}
*/

static class_env * modify( class_env *ce, id *i, class *c ) {
    class_env *result;
    result = (class_env*)GC_MALLOC(sizeof(class_env));
    result->i = i;
    result->c = c;
    result->t = ce->t;
    result->next = ce;
    return result;
}

/*
initialEnv :: ClassEnv
initialEnv  = ClassEnv { classes  = \i -> fail "class not defined",
                         defaults = [tInteger, tDouble] }
*/

static class_env * initial_env() {
    class_env *result;
    result = (class_env*)GC_MALLOC(sizeof(class_env));
    result->i = NULL;
    result->c = NULL;
    result->t = tInt;
    result->next = NULL;
    return result;
}

/*
type EnvTransformer = ClassEnv -> Maybe ClassEnv

infixr 5 <:>
(<:>)       :: EnvTransformer -> EnvTransformer -> EnvTransformer
(f <:> g) ce = do ce' <- f ce
                  g ce'

addClass                              :: Id -> [Tyvar] -> [Pred] -> EnvTransformer
addClass i vs ps ce
 | defined (classes ce i)              = fail "class already defined"
 | any (not . defined . classes ce . predHead) ps = fail "superclass not defined"
 | otherwise                           = return (modify ce i (vs, ps, []))
*/

static class_env * add_class( id *i, typevar_list *tv, pred *p,
    class_env *ce ) {
    class *c = new_class(tv, p, NULL);
    return modify(ce, i, c);
}

/*
addPreludeClasses :: EnvTransformer
addPreludeClasses  = addCoreClasses <:> addNumClasses

atyvar = Tyvar "a" Star
atype  = TVar atyvar
asig   = [atyvar]

mtyvar = Tyvar "m" (Kfun Star Star)
mtype  = TVar mtyvar
msig   = [mtyvar]

addCoreClasses ::   EnvTransformer
addCoreClasses  =   addClass "Eq" asig []
                <:> addClass "Ord" asig [IsIn "Eq" [atype]]
                <:> addClass "Show" asig []
                <:> addClass "Read" asig []
                <:> addClass "Bounded" asig []
                <:> addClass "Enum" asig []
                <:> addClass "Functor" msig []
                <:> addClass "Monad" msig []

addNumClasses  ::   EnvTransformer
addNumClasses   =   addClass "Num" asig [IsIn "Eq" [atype],
                                         IsIn "Show" [atype]]
                <:> addClass "Real" asig [IsIn "Num" [atype],
                                          IsIn "Ord" [atype]]
                <:> addClass "Fractional" asig [IsIn "Num" [atype]]
                <:> addClass "Integral" asig [IsIn "Real" [atype],
                                              IsIn "Enum" [atype]]
                <:> addClass "RealFrac" asig [IsIn "Real" [atype],
                                              IsIn "Fractional" [atype]]
                <:> addClass "Floating" asig [IsIn "Fractional" [atype]]
                <:> addClass "RealFloat" asig [IsIn "RealFrac" [atype],
                                               IsIn "Floating" [atype]]
*/

static class_env * prelude_classes() {
    type *atype;
    typevar_list *asig, *msig;
    class_env *ce;
    atype = tyvar(new_tyvar("a", kstar()));
    asig = type_vars(atype);
    msig = type_vars(tyvar(new_tyvar("m", kfun(kstar(), kstar()))));
    /* Core classes */
    ce = add_class("Eq",      asig, NULL, initial_env());
    ce = add_class("Ord",     asig, is_in("Eq", atype), ce);
    ce = add_class("Show",    asig, NULL, ce);
    ce = add_class("Read",    asig, NULL, ce);
    ce = add_class("Bounded", asig, NULL, ce);
    ce = add_class("Enum",    asig, NULL, ce);
    ce = add_class("Functor", msig, NULL, ce);
    ce = add_class("Monad",   msig, NULL, ce);
    /* Num classes */
    ce = add_class("Num",     asig, pred_join(is_in("Eq",   atype),
                                    pred_join(is_in("Show", atype),
                                              is_in("Ord",  atype))), ce);
    return ce;
}

/*
addInst                        :: [Pred] -> Pred -> EnvTransformer
addInst ps p@(IsIn i _) ce
 | not (defined (classes ce i)) = fail "no class for instance"
 | any (overlap p) qs           = fail "overlapping instance"
 | otherwise                    = return (modify ce i c)
   where its = insts ce i
         qs  = [ q | (_ :=> q) <- its ]
         c   = (sig ce i, super ce i, (ps:=>p) : its)
*/

static class_env * add_inst( pred *ps, pred *p, class_env *ce ) {
    id *i;
    inst *its;
    class *c;
    i = p->i;
    its = insts(ce, i);
    c = new_class(sig(ce, i), super(ce, i), new_inst(
        qualified_pred(ps, p), its));
    return modify(ce, i, c);
}

/*
overlap       :: Pred -> Pred -> Bool
overlap p q    = defined (mgu p q)

exampleInsts ::  EnvTransformer
exampleInsts =   addPreludeClasses
             <:> addInst [] (IsIn "Ord" [tUnit])
             <:> addInst [] (IsIn "Ord" [tChar])
             <:> addInst [] (IsIn "Ord" [tInt])
             <:> addInst [IsIn "Ord" [TVar (Tyvar "a" Star)],
                          IsIn "Ord" [TVar (Tyvar "b" Star)]]
                         (IsIn "Ord" [pair (TVar (Tyvar "a" Star))
                                           (TVar (Tyvar "b" Star))])
*/

static class_env * example_insts( class_env *ce ) {
    type *atype, *btype;
    atype = tyvar(new_tyvar("a", kstar()));
    btype = tyvar(new_tyvar("b", kstar()));
    ce = add_inst(NULL, is_in("Ord", tUnit), ce);
    ce = add_inst(NULL, is_in("Ord", tChar), ce);
    ce = add_inst(NULL, is_in("Ord", tInt), ce);
    ce = add_inst(pred_join(is_in("Ord", atype),
                            is_in("Ord", btype)),
                            is_in("Ord", pair_types(atype, btype)),
                            ce);
    return ce;
}

/*
bySuper :: ClassEnv -> Pred -> [Pred]
bySuper ce p@(IsIn i ts)
 = p : concat (map (bySuper ce) supers)
   where supers = apply s (super ce i)
         s      = zip (sig ce i) ts
*/
/* p : concat [bySuper ce (IsIn i′ t) | i′ <- super ce i] */

static pred * by_super( class_env *ce, pred *p ) {
    pred *head, *ps;
    if( !p ) {
        return NULL;
    }
    head = dup_pred(p);
    ps = super(ce, p->i);
    while( ps ) {
        head = pred_join(head, by_super(ce, is_in(ps->i, p->t)));
        ps = ps->next;
    }
    return head;
}

/*
byInst                   :: ClassEnv -> Pred -> Maybe [Pred]
byInst ce p@(IsIn i t)    = msum [ tryInst it | it <- insts ce i ]
 where tryInst (ps :=> h) = do u <- match h p
                               Just (map (apply u) ps)
*/

static pred * by_inst( class_env *ce, pred *p ) {
    inst *it;
    pred *result;
    qual *q;
    subst *s;
    it = insts(ce, p->i);
    result = NULL;
    while( it ) {
        q = it->q;
        /* We can only match against the same types, so q can only be a pred */
        s = match_pred(q->val.p, p);
        result = pred_join(result, apply_pred(s, q->val.p));
        it = it->next;
    }
    return result;
}

/*
entail        :: ClassEnv -> [Pred] -> Pred -> Bool
entail ce ps p = any (p `elem`) (map (bySuper ce) ps) ||
                 case byInst ce p of
                   Nothing -> False
                   Just qs -> all (entail ce ps) qs
*/

static int entail( class_env *ce, pred *ps, pred *p ) {
    pred *preds, *ps2;
    /* First, try to establish entailment through superclasses */
    ps2 = ps;
    while( ps2 ) {
        preds = by_super(ce, ps2);
        while( preds ) {
            if( pred_eq(preds, p) ) {
                return 1;
            }
            preds = preds->next;
        }
        ps2 = ps2->next;
    }
    /* That didn't work, so try through instances */
    preds = by_inst(ce, p);
    if( !preds ) {
        return 0;
    }
    while( preds ) {
        if( !entail(ce, ps, preds) ) {
            return 0;
        }
        preds = preds->next;
    }
    return 1;
}

/*
simplify   :: ([Pred] -> Pred -> Bool) -> [Pred] -> [Pred]
simplify ent = loop []
 where loop rs []                      = rs
       loop rs (p:ps) | ent (rs++ps) p = loop rs ps
                      | otherwise      = loop (p:rs) ps

reduce      :: ClassEnv -> [Pred] -> [Pred]
reduce ce    = simplify (scEntail ce) . elimTauts ce

elimTauts   :: ClassEnv -> [Pred] -> [Pred]
elimTauts ce ps = [ p | p <- ps, not (entail ce [] p) ]

scEntail        :: ClassEnv -> [Pred] -> Pred -> Bool
scEntail ce ps p = any (p `elem`) (map (bySuper ce) ps)
*/

/*
 * Note: I merge simplify and elimTauts, and skip scEntail as it is only an
 * optimization and I don't care about performance. This results in the above
 * four functions being reduced to a single 'reduce' function.
 */
static pred * reduce( class_env *ce, pred *ps ) {
    pred *result, *p, *p2;
    if( !ps ) {
        return NULL;
    }
    result = dup_pred(ps);
    /* Step 1: Remove leading preds that are entailed by other preds in list
       or result in a tautology (entailed by an empty list of preds) */
    while( entail(ce, result->next, result) || entail(ce, NULL, result) ) {
        result = result->next;
        if( !result ) {
            return NULL;
        }
    }
    /* Step 2: Remove all other preds that are entailed */
    p = result;
    while( p->next ) {
        /* Remove current pred so we don't check against itself */
        p2 = p->next;
        p->next = p2->next;
        if( !entail(ce, result, p2) && !entail(ce, NULL, p2) ) {
            /* Re-add removed pred */
            p->next = p2;
        }
        p = p->next;
    }
    return result;
}

/*
*** Scheme.hs
data Scheme = Forall [Kind] (Qual Type)
              deriving Eq
*/

typedef struct kind_list {
    kind *k;
    struct kind_list *next;
} kind_list;

static kind_list * new_kind_list( kind *k ) {
    kind_list *result;
    result = (kind_list*)GC_MALLOC(sizeof(kind_list));
    result->k = k;
    result->next = NULL;
    return result;
}

static int kind_list_eq( kind_list *ks1, kind_list *ks2 ) {
    if( !ks1 && !ks2 ) {
        return 1;
    }
    else if( !(ks1 && ks2) ) {
        return 0;
    }
    else {
        if( kind_eq(ks1->k, ks2->k) ) {
            return kind_list_eq(ks1->next, ks2->next);
        }
        else {
            return 0;
        }
    }
}

static void print_kind_list( kind_list *ks ) {
    printf("[");
    while( ks ) {
        print_kind(ks->k);
        if( ks->next ) {
            printf(", ");
        }
        ks = ks->next;
    }
    printf("]");
}

/* Qual should always contain a type, but we can't enfore that */
typedef struct scheme {
    kind_list *ks;
    qual *q;
} scheme;

static scheme * forall( kind_list *ks, qual *q ) {
    scheme *result;
    result = (scheme*)GC_MALLOC(sizeof(scheme));
    result->ks = ks;
    result->q = q;
    return result;
}

static int scheme_eq( scheme *sc1, scheme *sc2 ) {
    if( !sc1 || !sc2 ) {
        return 0;
    }
    return kind_list_eq(sc1->ks, sc2->ks) && qual_eq(sc1->q, sc2->q);
}

static void print_scheme( scheme *sc ) {
    printf("forall ");
    print_kind_list(sc->ks);
    printf(". ");
    print_qual_type(sc->q);
}

/*
instance Types Scheme where
  apply s (Forall ks qt) = Forall ks (apply s qt)
  tv (Forall ks qt)      = tv qt
*/

static scheme * apply_scheme( subst *s, scheme *sc ) {
    return forall(sc->ks, apply_qual(s, sc->q));
}

static typevar_list * type_vars_scheme( scheme *s ) {
    return type_vars_qual(s->q);
}

/*
quantify      :: [Tyvar] -> Qual Type -> Scheme
quantify vs qt = Forall ks (apply s qt)
 where vs' = [ v | v <- tv qt, v `elem` vs ]
       ks  = map kind vs'
       s   = zip vs' (map TGen [0..])
*/

static scheme * quantify( typevar_list *tvs, qual *q ) {
    typevar_list *tvs2, *tvs3;
    kind_list *ks, *ks2;
    subst *subs, *s;
    int i;
    /* Step 1: Generate list of type vars from the qualified type */
    tvs2 = type_vars_qual(q);
    /* Step 2: Strip out any type vars that aren't in tvs */
    while( tvs2 && !elem(tvs2->tv, tvs) ) {
        tvs2 = tvs2->next;
    }
    tvs3 = tvs2;
    if( tvs3 ) {
        while( tvs3->next ) {
            if( !elem(tvs3->next->tv, tvs) ) {
                tvs3->next = tvs3->next->next;
            }
            else {
                tvs3 = tvs3->next;
            }
        }
    }
    nub(tvs2);
    /* Step 3: Generate kind list from typevar list */
    ks = ks2 = NULL;
    for( tvs3 = tvs2; tvs3; tvs3 = tvs3->next ) {
        if( !ks ) {
            ks = ks2 = new_kind_list(tvs3->tv->k);
        }
        else {
            ks2->next = new_kind_list(tvs3->tv->k);
            ks2 = ks2->next;
        }
    }
    /* Step 4: Generate substitution list */
    i = 0;
    subs = s = NULL;
    for( tvs3 = tvs2; tvs3; tvs3 = tvs3->next ) {
        if( !subs ) {
            subs = s = apply_subst(tvs3->tv, tygen(i));
        }
        else {
            s->next = apply_subst(tvs3->tv, tygen(i));
            s = s->next;
        }
        i++;
    }
    /* Step 5: Generate final type scheme */
    return forall(ks, apply_qual(subs, q));
}

/*
toScheme      :: Type -> Scheme
toScheme t     = Forall [] ([] :=> t)
*/

static scheme * to_scheme( type *t ) {
    return forall(NULL, qualified_type(NULL, t));
}

/*
*** Assump.hs
data Assump = Id :>: Scheme
*/

typedef struct assump {
    id *i;
    scheme *s;
    struct assump *next;
} assump;

static assump * new_assump( id *i, scheme *s ) {
    assump *result;
    result = (assump*)GC_MALLOC(sizeof(assump));
    result->i = i;
    result->s = s;
    result->next = NULL;
    return result;
}

static assump * assump_join( assump *a1, assump *a2 ) {
    assump *result, *curr;
    result = curr = NULL;
    /* Copy a1 */
    if( a1 ) {
        result = new_assump(a1->i, a1->s);
        curr = result;
        a1 = a1->next;
        while( a1 ) {
            curr->next = new_assump(a1->i, a1->s);
            curr = curr->next;
            a1 = a1->next;
        }
    }
    /* Copy a2 */
    if( !result && a2 ) {
        result = new_assump(a2->i, a2->s);
        curr = result;
        a2 = a2->next;
    }
    while( a2 ) {
        curr->next = new_assump(a2->i, a2->s);
        curr = curr->next;
        a2 = a2->next;
    }
    return result;
}

static void print_assumps( assump *as ) {
    for( ; as; as = as->next ) {
        printf("%s: ", as->i);
        print_scheme(as->s);
        printf("\n");
    }
}

/*
instance Types Assump where
  apply s (i :>: sc) = i :>: (apply s sc)
  tv (i :>: sc)      = tv sc
*/

static assump * apply_assump( subst *s, assump *a ) {
    assump *result;
    if( !a ) {
        return NULL;
    }
    result = new_assump(a->i, apply_scheme(s, a->s));
    result->next = apply_assump(s, a->next);
    return result;
}

/* Corresponds to the function 'tv' */
static typevar_list * type_vars_assump( assump *a ) {
    return type_vars_scheme(a->s);
}

/*
find                 :: Monad m => Id -> [Assump] -> m Scheme
find i []             = fail ("unbound identifier: " ++ i)
find i ((i':>:sc):as) = if i==i' then return sc else find i as
*/

static scheme * find( id *i, assump *a ) {
    if( !a ) {
        fprintf(stderr, "ERROR: Unbound identifier: %s\n", i);
        return NULL;
    }
    if( id_eq(i, a->i) ) {
        return a->s;
    }
    else {
        return find(i, a->next);
    }
}

/*
*** Infer.hs
type Infer e t = ClassEnv -> [Assump] -> e -> TI ([Pred], t)

*** TIMonad.hs
newtype TI a = TI (Subst -> Int -> (Subst, Int, a))

instance Monad TI where
  return x   = TI (\s n -> (s,n,x))
  TI f >>= g = TI (\s n -> case f s n of
                            (s',m,x) -> let TI gx = g x
                                        in  gx s' m)

runTI       :: TI a -> a
runTI (TI f) = x where (s,n,x) = f nullSubst 0

getSubst   :: TI Subst
getSubst    = TI (\s n -> (s,n,s))
*/
/* Note: We use dirty, dirty imperative programming to avoid mucking about with
   monads and higher-order functions */

static subst * curr_subst = NULL;

/*
unify      :: Type -> Type -> TI ()
unify t1 t2 = do s <- getSubst
                 u <- mgu (apply s t1) (apply s t2)
                 extSubst u
*/

static void unify( type *t1, type *t2 ) {
    subst *s;
    s = mgu_single(apply(curr_subst, t1), apply(curr_subst, t2));
    curr_subst = comp_apply(s, curr_subst);
}

/*
trim       :: [Tyvar] -> TI ()
trim vs     = TI (\s n ->
                  let s' = [ (v,t) | (v,t) <-s, v `elem` vs ]
                      force = length (tv (map snd s'))
                  in  force `seq` (s', n, ()))

extSubst   :: Subst -> TI ()
extSubst s' = TI (\s n -> (s'@@s, n, ()))

newTVar    :: Kind -> TI Type
newTVar k   = TI (\s n -> let v = Tyvar (enumId n) k
                          in  (s, n+1, TVar v))
*/

static type * new_tvar( kind *k ) {
    return tyvar(new_tyvar(enum_id(), k));
}

/*
class Instantiate t where
  inst  :: [Type] -> t -> t
instance Instantiate Type where
  inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
  inst ts (TGen n)  = ts !! n
  inst ts t         = t
instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)
instance Instantiate t => Instantiate (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t
instance Instantiate Pred where
  inst ts (IsIn c t) = IsIn c (inst ts t)
*/

static type * inst_types( type *ts, type *t ) {
    type *result, *ts2;
    int i;
    if( t->type == type_ap ) {
        result = tyap(inst_types(ts, t->val.ta->l),
                      inst_types(ts, t->val.ta->r));
    }
    else if( t->type == type_gen ) {
        i = 0;
        ts2 = ts;
        while( i != t->val.tg ) {
            i++;
            if( !ts2 ) {
                fprintf(stderr,
                    "ERROR: Failed to look up TGen in inst_types\n");
                return NULL;
            }
            ts2 = ts2->next;
        }
        result = ts2;
    }
    else {
        result = t;
    }
    /* Recurse if we're dealing with a list of types */
    if( t->next ) {
        result->next = inst_types(ts, t->next);
    }
    return result;
}

static pred * inst_preds( type *ts, pred *p ) {
    pred *result;
    if( !p ) {
        return NULL;
    }
    else if( !p->next ) {
        result = is_in(p->i, inst_types(ts, p->t));
        result->next = inst_preds(ts, p->next);
        return result;
    }
    else {
        return is_in(p->i, inst_types(ts, p->t));
    }
}

static qual * inst_qual( type *ts, qual *q ) {
    return qualified_type(inst_preds(ts, q->p), inst_types(ts, q->val.t));
}

/*
freshInst               :: Scheme -> TI (Qual Type)
freshInst (Forall ks qt) = do ts <- mapM newTVar ks
                              return (inst ts qt)
*/

static qual * fresh_inst( scheme *s ) {
    kind_list *ks;
    ks = s->ks;
    type *t, *t_end;
    t = t_end = NULL;
    while( ks ) {
        if( !t ) {
            t = t_end = new_tvar(ks->k);
        }
        else {
            t_end->next = new_tvar(ks->k);
            t_end->next = t_end;
        }
        ks = ks->next;
    }
    return inst_qual(t, s->q);
}

/*
*** Lit.hs
data Literal = LitInt  Integer
             | LitChar Char
             | LitRat  Rational
             | LitStr  String
*/

static int is_literal( token *tok ) {
    switch( tok->type ) {
        case tok_float:
        case tok_int:
        case tok_string:
            return 1;
        default:
            return 0;
    }
}

/*
tiLit            :: Literal -> TI ([Pred],Type)
tiLit (LitChar _) = return ([], tChar)
tiLit (LitInt _)  = do v <- newTVar Star
                       return ([IsIn "Num" [v]], v)
tiLit (LitStr _)  = return ([], tString)
tiLit (LitRat _)  = do v <- newTVar Star
                       return ([IsIn "Fractional" [v]], v)
*/

typedef struct pred_type {
    pred *p;
    type *t;
} pred_type;

static pred_type * new_pred_type( pred *p, type *t ) {
    pred_type *result;
    result = (pred_type*)GC_MALLOC(sizeof(pred_type));
    result->p = p;
    result->t = t;
    return result;
}

static pred_type * ti_lit( token *tok ) {
    if( tok->type == tok_float ) {
        return new_pred_type(NULL, tChar);
    }
    else if( tok->type == tok_int ) {
        return new_pred_type(NULL, tInt);
    }
    else if( tok->type == tok_string ) {
        return new_pred_type(NULL, tString);
    }
    else {
        fprintf(stderr, "ERROR: ti_lit received token that is not a literal\n");
        return NULL;
    }
}

/*
*** Pat.hs
data Pat        = PVar Id
                | PWildcard
                | PAs  Id Pat
                | PLit Literal
                | PNpk Id Integer
                | PCon Assump [Pat]

                | PLazy Pat

tiPat :: Pat -> TI ([Pred], [Assump], Type)
*/

typedef struct pred_assump_type {
    pred *p;
    assump *a;
    type *t;
} pred_assump_type;

static pred_assump_type * new_pred_assump_type( pred *p, assump *a, type *t) {
    pred_assump_type *result;
    result = (pred_assump_type*)GC_MALLOC(sizeof(pred_assump_type));
    result->p = p;
    result->a = a;
    result->t = t;
    return result;
}

/*
tiPat (PVar i) = do v <- newTVar Star
                    return ([], [i :>: toScheme v], v)

tiPat PWildcard   = do v <- newTVar Star
                       return ([], [], v)

tiPat (PAs i pat) = do (ps, as, t) <- tiPat pat
                       return (ps, (i:>:toScheme t):as, t)

tiPat (PLit l) = do (ps, t) <- tiLit l
                    return (ps, [], t)

tiPat (PNpk i k)  = do t <- newTVar Star
                       return ([IsIn "Integral" [t]], [i:>:toScheme t], t)

tiPat (PCon (i:>:sc) pats) = do (ps,as,ts) <- tiPats pats
                                t'         <- newTVar Star
                                (qs :=> t) <- freshInst sc
                                unify t (foldr fn t' ts)
                                return (ps++qs, as, t')

tiPat (PLazy pat) = tiPat pat
*/

/* Forward reference */
static pred_assump_type * ti_pats( token *tok );

static pred_assump_type * ti_pat( token *tok ) {
    pred_type *pt;
    type *t;
    if( is_literal(tok) ) {
        pt = ti_lit(tok);
        return new_pred_assump_type(pt->p, NULL, pt->t);
    }
    else if( tok->type == tok_ident ) {
        /* Have to differentiate between wildcards, variables, and type
           constructors */
        /* Wildcard  _ */
        if( tok->value.s[0] == '_' && !tok->value.s[1] ) {
            return new_pred_assump_type(NULL, NULL, new_tvar(kstar()));
        }
        /* Variable [a-z] */
        else if( tok->value.s[0] >= 'a' && tok->value.s[0] <= 'z' ) {
            t = new_tvar(kstar());
            return new_pred_assump_type(NULL,
                                        new_assump(tok->value.s, to_scheme(t)),
                                        t);
        }
        /* Type constructor */
        /* TODO */
        return NULL;
    }
    else {
        fprintf(stderr,
        "ERROR: ti_pat received value that's not a literal or a identifier\n");
        return NULL;
    }
}

/*
tiPats     :: [Pat] -> TI ([Pred], [Assump], [Type])
tiPats pats = do psasts <- mapM tiPat pats
                 let ps = concat [ ps' | (ps',_,_) <- psasts ]
                     as = concat [ as' | (_,as',_) <- psasts ]
                     ts = [ t | (_,_,t) <- psasts ]
                 return (ps, as, ts)
*/

static pred_assump_type * ti_pats( token *tok ) {
    pred_assump_type *result, *next;
    if( !tok ) {
        return new_pred_assump_type(NULL, NULL, NULL);
    }
    result = ti_pat(tok);
    next = ti_pats(tok->next);
    result = new_pred_assump_type(pred_join(result->p, next->p),
                                  assump_join(result->a, next->a),
                                  type_join(result->t, next->t));
    return result;
}

/*
*** TIMain.hs
type Alt = ([Pat], Expr)

tiAlt                :: Infer Alt Type
tiAlt ce as (pats, e) = do (ps, as', ts) <- tiPats pats
                           (qs,t)  <- tiExpr ce (as'++as) e
                           return (ps++qs, foldr fn t ts)

tiAlts             :: ClassEnv -> [Assump] -> [Alt] -> Type -> TI [Pred]
tiAlts ce as alts t = do psts <- mapM (tiAlt ce as) alts
                         mapM (unify t) (map snd psts)
                         return (concat (map fst psts))
*/

/* Forward reference */
static pred_type * ti_expr( class_env *ce, assump *as, token *tok );

static pred_type * ti_alt( class_env *ce, assump *as, token *tok ) {
    pred_assump_type *pat;
    pred_type *pt, *result;
    if( tok->type != tok_Assign && tok->type != tok_lamexpr ) {
        fprintf(stderr, "ERROR: ti_alt received token that's not an "
                        "assignment or lambda expression\n");
        return NULL;
    }
    if( tok->type == tok_Assign ) {
        /* Assign->lhs = ident for function
           Assign->lhs->next = start of pattern */
        pat = ti_pats(tok->lhs->next);
    }
    else {
        pat = ti_pats(tok->lhs);
    }
    /* rhs = expr */
    pt = ti_expr(ce, assump_join(as, pat->a), tok->rhs);
    result = new_pred_type(pred_join(pat->p, pt->p), fold_fn(pt->t, pat->t));
    return result;
}

static pred * ti_alts( class_env *ce, assump *as, token *tok, type *t ) {
    pred_type *pt;
    pred *p;
    if( tok->type != tok_Bind ) {
        fprintf(stderr, "ERROR: ti_alts received token that's not a bind!\n");
        return NULL;
    }
    p = NULL;
    /* Get first assignment */
    tok = tok->lhs;
    while( tok ) {
        /* We skip explicit types */
        if( tok->type != tok_Typesig && tok->type != tok_Kernel ) {
            pt = ti_alt(ce, as, tok);
            unify(t, pt->t);
            p = pred_join(p, pt->p);
        }
        tok = tok->next;
    }
    return p;
}

/*
-----------------------------------------------------------------------------
data Expr = Var   Id
          | Lit   Literal
          | Const Assump
          | Ap    Expr Expr
          | Let   BindGroup Expr

          | Lam   Alt
          | If    Expr Expr Expr
          | Case  Expr [(Pat,Expr)]

-----------------------------------------------------------------------------

tiExpr                       :: Infer Expr Type
tiExpr ce as (Var i)          = do sc         <- find i as
                                   (ps :=> t) <- freshInst sc
                                   return (ps, t)
tiExpr ce as (Const (i:>:sc)) = do (ps :=> t) <- freshInst sc
                                   return (ps, t)
tiExpr ce as (Lit l)          = do (ps,t) <- tiLit l
                                   return (ps, t)
tiExpr ce as (Ap e f)         = do (ps,te) <- tiExpr ce as e
                                   (qs,tf) <- tiExpr ce as f
                                   t       <- newTVar Star
                                   unify (tf `fn` t) te
                                   return (ps++qs, t)
tiExpr ce as (Let bg e)       = do (ps, as') <- tiBindGroup ce as bg
                                   (qs, t)   <- tiExpr ce (as' ++ as) e
                                   return (ps ++ qs, t)

tiExpr ce as (Lam alt)
  = tiAlt ce as alt
tiExpr ce as (If e e1 e2)
  = do (ps,t)   <- tiExpr ce as e
       unify t tBool
       (ps1,t1) <- tiExpr ce as e1
       (ps2,t2) <- tiExpr ce as e2
       unify t1 t2
       return (ps++ps1++ps2, t1)
tiExpr ce as (Case e branches)
  = do (ps, t) <- tiExpr ce as e
       v       <- newTVar Star
       let tiBr (pat, f)
            = do (ps, as',t') <- tiPat pat
                 unify t t'
                 (qs, t'')   <- tiExpr ce (as'++as) f
                 unify v t''
                 return (ps++qs)
       pss <- mapM tiBr branches
       return (ps++concat pss, v)
*/

/* Case branches */
static pred * ti_branches( class_env *ce, assump *as, token *tok,
    type *t1, type *t2 ) {
    pred_assump_type *pat;
    pred_type *pt;
    pred *result;
    result = NULL;
    while( tok ) {
        if( tok->type != tok_Cases ) {
            fprintf(stderr, "ERROR: ti_branches didn't receive a case\n");
            return NULL;
        }
        pat = ti_pat(tok->lhs);
        unify(t1, pat->t);
        pt = ti_expr(ce, assump_join(as, pat->a), tok->rhs);
        unify(t2, pt->t);
        result = pred_join(result, pred_join(pat->p, pt->p));
        tok = tok->next;
    }
    return result;
}

static pred_type * ti_expr3( class_env *ce, assump *as, token *tok ) {
    pred_type *pt1;
    qual *q;
    type *t;
    if( tok->type == tok_ident ) {
        /* Const */
        if( tok->value.s[0] >= 'A' && tok->value.s[0] <= 'Z' ) {
            /* TODO */
            return NULL;
        }
        /* Val */
        else {
            q = fresh_inst(find(tok->value.s, as));
            pt1 = new_pred_type(q->p, q->val.t);
        }
    }
    else if( tok->type == tok_parens ) {
        pt1 = ti_expr(ce, as, tok->lhs);
    }
    else if( is_literal(tok) ) {
        pt1 = ti_lit(tok);
    }
    else if( tok->type == tok_letexpr ) {
        /* TODO */
        pt1 = NULL;
    }
    else if( tok->type == tok_lamexpr ) {
        pt1 = ti_alt(ce, as, tok);
    }
    else if( tok->type == tok_caseexpr ) {
        pt1 = ti_expr(ce, as, tok->lhs);
        t = new_tvar(kstar());
        pt1 = new_pred_type(pred_join(pt1->p,
            ti_branches(ce, as, tok->rhs, pt1->t, t)), t);
    }
    else {
        fprintf(stderr, "ERROR: ti_expr received something illegal\n");
        return NULL;
    }
    return pt1;
}

static pred_type * ti_expr2( class_env *ce, assump *as, token *tok,
    pred_type *pt ) {
    pred_type *pt2, *pt3;
    type *t;
    if( !tok ) {
        return pt;
    }
    pt2 = ti_expr3(ce, as, tok);
    /* Check for application */
    if( tok->next ) {
        if( pt ) {
            /* This is part of an application, so we unify against the given
               type and pass along the generated TVar. */
            t = new_tvar(kstar());
            unify(tyap_fn(pt2->t, t), pt->t);
            pt3 = new_pred_type(pred_join(pt->p, pt2->p), t);
            return ti_expr2(ce, as, tok->next, pt3);
        }
        else {
            /* Base case: Our first application, so we TI the first 2 right
               away, then pass along the generated TVar to the third ap. */
            pt3 = ti_expr3(ce, as, tok->next);
            t = new_tvar(kstar());
            unify(tyap_fn(pt3->t, t), pt2->t);
            pt3 = new_pred_type(pred_join(pt2->p, pt3->p), t);
            return ti_expr2(ce, as, tok->next->next, pt3);
        }
    }
    /* No application, still have to check if we have to unify */
    else {
        if( pt ) {
            /* Received a type, so we have to unify */
            t = new_tvar(kstar());
            unify(tyap_fn(pt2->t, t), pt->t);
            pt3 = new_pred_type(pred_join(pt->p, pt2->p), t);
            return pt3;
        }
        else {
            /* No application at all, so just return our TI'd expression. */
            return pt2;
        }
    }
}

static pred_type * ti_expr( class_env *ce, assump *as, token *tok ) {
    return ti_expr2(ce, as, tok, NULL);
}

/*
split :: Monad m => ClassEnv -> [Tyvar] -> [Tyvar] -> [Pred]
                      -> m ([Pred], [Pred])
split ce fs gs ps = do let ps' = reduce ce ps
                           (ds, rs) = partition (all (`elem` fs) . tv) ps'
                       rs' <- defaultedPreds ce (fs++gs) rs
                       return (ds, rs \\ rs')
*/

typedef struct pred_pair {
    pred *ds;
    pred *rs;
} pred_pair;

static pred_pair * new_pred_pair( pred *ds, pred *rs ) {
    pred_pair *result;
    result = (pred_pair*)GC_MALLOC(sizeof(pred_pair));
    result->ds = ds;
    result->rs = rs;
    return result;
}

static pred_pair * split( class_env *ce, typevar_list *fs, typevar_list *gs,
    pred *ps ) {
    pred *ps2;
    typevar_list *tvs;
    pred_pair *result;
    /* Useless code to bypass unused var 'gs' raising an error */
    if( gs ) {
        gs = NULL;
    }
    result = new_pred_pair(NULL, NULL);
    ps2 = reduce(ce, ps);
    /* Partition by (all (`elem` fs) . tv), resulting in (true, false) */
    while( ps2 ) {
        tvs = type_vars_pred(ps2);
        while( tvs ) {
            if( !elem(tvs->tv, fs) ) {
                break;
            }
            tvs = tvs->next;
        }
        /* tvs != NULL -> early break -> predicate is false */
        if( tvs ) {
            result->rs = pred_join(result->rs, pred_dup(ps2));
        }
        else {
            result->ds = pred_join(result->ds, pred_dup(ps2));
        }
        ps2 = ps2->next;
    }
    return result;
}

/*
type Ambiguity       = (Tyvar, [Pred])

ambiguities         :: ClassEnv -> [Tyvar] -> [Pred] -> [Ambiguity]
ambiguities ce vs ps = [ (v, filter (elem v . tv) ps) | v <- tv ps \\ vs ]

numClasses :: [Id]
numClasses  = ["Num", "Integral", "Floating", "Fractional",
               "Real", "RealFloat", "RealFrac"]

stdClasses :: [Id]
stdClasses  = ["Eq", "Ord", "Show", "Read", "Bounded", "Enum", "Ix",
               "Functor", "Monad", "MonadPlus"] ++ numClasses

candidates           :: ClassEnv -> Ambiguity -> [Type]
candidates ce (v, qs) = [ t' | let is = [ i | IsIn i t <- qs ]
                                   ts = [ t | IsIn i t <- qs ],
                               all ([TVar v]==) ts,
                               any (`elem` numClasses) is,
                               all (`elem` stdClasses) is,
                               t' <- defaults ce,
                               all (entail ce []) [ IsIn i [t'] | i <- is ] ]

withDefaults :: Monad m => ([Ambiguity] -> [Type] -> a)
                  -> ClassEnv -> [Tyvar] -> [Pred] -> m a
withDefaults f ce vs ps
    | any null tss  = fail "cannot resolve ambiguity"
    | otherwise     = return (f vps (map head tss))
      where vps = ambiguities ce vs ps
            tss = map (candidates ce) vps

defaultedPreds :: Monad m => ClassEnv -> [Tyvar] -> [Pred] -> m [Pred]
defaultedPreds  = withDefaults (\vps ts -> concat (map snd vps))

defaultSubst   :: Monad m => ClassEnv -> [Tyvar] -> [Pred] -> m Subst
defaultSubst    = withDefaults (\vps ts -> zip (map fst vps) ts)

-----------------------------------------------------------------------------

type Expl = (Id, Scheme, [Alt])

tiExpl :: ClassEnv -> [Assump] -> Expl -> TI [Pred]
tiExpl ce as (i, sc, alts)
        = do (qs :=> t) <- freshInst sc
             ps         <- tiAlts ce as alts t
             s          <- getSubst
             let qs'     = apply s qs
                 t'      = apply s t
                 fs      = tv (apply s as)
                 gs      = tv t' \\ fs
                 sc'     = quantify gs (qs':=>t')
                 ps'     = filter (not . entail ce qs') (apply s ps)
             (ds,rs)    <- split ce fs gs ps'
             if sc /= sc' then
                 fail "signature too general"
               else if not (null rs) then
                 fail "context too weak"
               else
                 return ds
*/

/* Performs list diff (\\) for types and type vars */
static type * type_tyvar_diff( type *t, typevar_list *tvs ) {
    type *t2;
    while( tvs ) {
        /* Check head of list t */
        while( t && t->type == type_var ) {
            if( typevar_eq(t->val.tv, tvs->tv) ) {
                t = t->next;
                tvs = tvs->next;
            }
            else {
                break;
            }
        }
        /* Check rest of list t */
        if( t ) {
            t2 = t;
            while( t2->next && tvs ) {
                if( t2->next->type == type_var ) {
                    if( typevar_eq(t2->next->val.tv, tvs->tv) ) {
                        t2->next = t2->next->next;
                        tvs = tvs->next;
                        continue;
                    }
                }
                t2 = t2->next;
            }
        }
        if( tvs ) {
            tvs = tvs->next;
        }
    }
    return t;
}

/* Performs list diff (\\) for two type var lists */
static typevar_list * typevar_list_diff( typevar_list *tv1,
    typevar_list *tv2 ) {
    typevar_list *tv3;
    while( tv2 ) {
        /* Check head of list tv1 */
        while( tv1 ) {
            if( typevar_eq(tv1->tv, tv2->tv) ) {
                tv1 = tv1->next;
                tv2 = tv2->next;
            }
            else {
                break;
            }
        }
        /* Check rest of list tv1 */
        if( tv1 ) {
            tv3 = tv1;
            while( tv3->next && tv2 ) {
                if( typevar_eq(tv3->next->tv, tv2->tv) ) {
                    tv3->next = tv3->next->next;
                    tv2 = tv2->next;
                    continue;
                }
                tv3 = tv3->next;
            }
        }
        if( tv2 ) {
            tv2 = tv2->next;
        }
    }
    return tv1;
}

/* Performs "filter (not . entail ce qs) (apply s ps)" */
static pred * filter_by_entail( class_env *ce, pred *qs, pred *ps ) {
    pred *ps2;
    /* Check head first */
    while( ps ) {
        if( entail(ce, qs, ps) ) {
            ps = ps->next;
        }
        else {
            break;
        }
    }
    /* Check rest next */
    if( ps ) {
        ps2 = ps;
        while( ps2->next ) {
            if( entail(ce, qs, ps2) ) {
                ps2->next = ps2->next->next;
            }
            else {
                ps2 = ps2->next;
            }
        }
    }
    return ps;
}

static pred * ti_expl( class_env *ce, assump *as, scheme *sc, token *tok ) {
    qual *q;
    pred *ps, *q2, *ps2;
    pred_pair *ds_rs;
    type *t;
    typevar_list *fs, *gs;
    scheme *sc2;
    if( tok->type != tok_Bind ) {   
        fprintf(stderr, "ERROR: ti_expl received token that's not a bind!\n");
        return NULL;
    }
    q = fresh_inst(sc);
    ps = ti_alts(ce, as, tok->lhs, q->val.t);
    /* let */
    q2 = apply_pred(curr_subst, q->p);
    t = apply(curr_subst, q->val.t);
    fs = type_vars_assump(apply_assump(curr_subst, as));
    gs = type_vars(type_tyvar_diff(t, fs));
    sc2 = quantify(gs, qualified_type(q2, t));
    ps2 = filter_by_entail(ce, q2, apply_pred(curr_subst, ps));
    ds_rs = split(ce, fs, gs, ps2);
    if( !scheme_eq(sc, sc2) ) {
        fprintf(stderr, "ERROR: signature too general: ");
        print_scheme(sc);
        printf(", ");
        print_scheme(sc2);
        printf("\n");
        return NULL;
    }
    else if( ds_rs->rs ) {
        fprintf(stderr, "ERROR: context too weak!\n");
        return NULL;
    }
    else {
        return ds_rs->ds;
    }
}

/*
type Impl   = (Id, [Alt])

restricted   :: [Impl] -> Bool
restricted bs = any simple bs
 where simple (i,alts) = any (null . fst) alts

-- type Infer e t = ClassEnv -> [Assump] -> e -> TI ([Pred], t)
-- tiImpls :: ClassEnv -> [Assump] -> [Impl] -> TI ([Pred], [Assump])

tiImpls         :: Infer [Impl] [Assump]
tiImpls ce as bs = do ts <- mapM (\_ -> newTVar Star) bs
                      let is    = map fst bs
                          scs   = map toScheme ts
                          as'   = zipWith (:>:) is scs ++ as
                          altss = map snd bs
                      pss <- sequence (zipWith (tiAlts ce as') altss ts)
                      s   <- getSubst
                      let ps'     = apply s (concat pss)
                          ts'     = apply s ts
                          fs      = tv (apply s as)
                          vss     = map tv ts'
                          gs      = foldr1 union vss \\ fs
                      (ds,rs) <- split ce fs (foldr1 intersect vss) ps'
                      if restricted bs then
                          let gs'  = gs \\ tv rs
                              scs' = map (quantify gs' . ([]:=>)) ts'
                          in return (ds++rs, zipWith (:>:) is scs')
                        else
                          let scs' = map (quantify gs . (rs:=>)) ts'
                          in return (ds, zipWith (:>:) is scs')
*/

/*
typedef struct typevar_list_list {
    typevar_list *tvs;
    struct typevar_list_list *next;
} typevar_list_list;

static typevar_list_list * new_typevar_list_list( typevar_list *tvs ) {
    typevar_list_list *result;
    result = (typevar_list_list*)GC_MALLOC(sizeof(typevar_list_list));
    result->tvs = tvs;
    result->next = NULL;
    return result;
}
*/

/*
 * Partitions the tvar list into two lists. One list represents the original
 * list with duplicates removed, and the other represents only those duplicates.
 * This roughly corresponds to the union and the intersection of a number of
 * lists that have been joined. The given list is nubbed list, while the
 * returned list contains the removed duplicates.
 */
static typevar_list * partition_tyvar_list( typevar_list *u ) {
    typevar_list *i, *i_end, *u2;
    i = i_end = NULL;
    u2 = u;
    while( u ) {
        while( u2->next ) {
            /* Check for duplicates */
            if( typevar_eq(u->tv, u2->next->tv) ) {
                if( !i ) {
                    i = i_end = u2->next;
                }
                else {
                    i_end->next = u2->next;
                    i_end = i_end->next;
                }
                u2->next = u2->next->next;
            }
            else {
                u2 = u2->next;
            }
        }
        u = u->next;
    }
    return i;
}

typedef struct pred_assump {
    pred *p;
    assump *a;
} pred_assump;

static pred_assump * new_pred_assump( pred *p, assump *a ) {
    pred_assump *result;
    result = (pred_assump*)GC_MALLOC(sizeof(pred_assump));
    result->p = p;
    result->a = a;
    return result;
}

static pred_assump * ti_impls( class_env *ce, assump *as, token *tok ) {
    token *tok2;
    type *ts, *ts_end, *ts2, *ts3;
    assump *as2, *as2_end, *as3, *as3_end;
    pred *pss, *ps2;
    pred_pair *ds_rs;
    typevar_list *fs, *vs, *is, *gs;
    tok2 = tok;
    pss = NULL;
    ts = ts_end = NULL;
    as2 = as2_end = NULL;
    while( tok2 ) {
        if( tok2->type != tok_Bind ) {
            fprintf(stderr, "ERROR: ti_impls found token that's not a bind!\n");
            return NULL;
        }
        /* Generate a new type var */
        if( ts_end ) {
            ts_end->next = new_tvar(kstar());
            ts_end = ts_end->next;
        }
        else {
            ts = new_tvar(kstar());
            ts_end = ts;
        }
        /* Make new assumps and type vars from our binds */
        if( as2_end ) {
            as2_end->next =
                new_assump(tok->value.s, to_scheme(ts_end));
            as2_end = as2_end->next;
        }
        else {
            as2 = new_assump(tok->value.s, to_scheme(ts_end));
            as2_end = as2;
        }
        tok2 = tok2->next;
    }
    /* Build up preds by doing type inference on the binds */
    as2 = assump_join(as2, as);
    tok2 = tok;
    ts2 = ts;
    while( tok2 && ts2 ) {
        pss = pred_join(pss, ti_alts(ce, as2, tok2, ts2));
        tok2 = tok2->next;
        ts2 = ts2->next;
    }
    ps2 = apply_pred(curr_subst, pss);
    ts2 = apply(curr_subst, ts);
    fs = type_vars_assump(apply_assump(curr_subst, as));
    /* map tv ts' */
    ts3 = ts2;
    vs = NULL;
    while( ts3 ) {
        vs = typevar_list_join(vs, type_vars(ts3));
        ts3 = ts3->next;
    }
    is = partition_tyvar_list(vs);
    gs = typevar_list_diff(vs, fs);
    ds_rs = split(ce, fs, is, ps2);
    /* We wrap up creating type schemes and assumptions to simplify code */
    as3 = as3_end = NULL;
    while( ts2 && tok ) {
        if( !as3 ) {
            as3 = as3_end = new_assump(tok->value.s,
                quantify(gs, qualified_type(ds_rs->rs, ts2)));
        }
        else {
            as3_end->next = new_assump(tok->value.s,
                quantify(gs, qualified_type(ds_rs->rs, ts2)));
            as3_end = as3_end->next;
        }
        tok = tok->next;
        ts2 = ts2->next;
    }
    return new_pred_assump(ds_rs->ds, as3);
}

/*
type BindGroup  = ([Expl], [[Impl]])

-- type Infer e t = ClassEnv -> [Assump] -> e -> TI ([Pred], t)
-- tiBindGroup :: ClassEnv -> [Assump] -> BindGroup -> TI ([Pred], [Assump])

tiBindGroup :: Infer BindGroup [Assump]
tiBindGroup ce as (es,iss) =
  do let as' = [ v:>:sc | (v,sc,alts) <- es ]
     (ps, as'') <- tiSeq tiImpls ce (as'++as) iss
     qss        <- mapM (tiExpl ce (as''++as'++as)) es
     return (ps++concat qss, as''++as')

tiSeq                  :: Infer bg [Assump] -> Infer [bg] [Assump]
tiSeq ti ce as []       = return ([],[])
tiSeq ti ce as (bs:bss) = do (ps,as')  <- ti ce as bs
                             (qs,as'') <- tiSeq ti ce (as'++as) bss
                             return (ps++qs, as''++as')
*/

/*
 * Generate a type from a type signature.
 */
static type * get_type_sig2( token *tok ) {
    if( tok->type == tok_ident ) {
        if( id_eq(tok->value.s, "()") ) {
            return tUnit;
        }
        else if( id_eq(tok->value.s, "Char") ) {
            return tChar;
        }
        else if( id_eq(tok->value.s, "Int") ) {
            return tInt;
        }
        else if( id_eq(tok->value.s, "Float") ) {
            return tFloat;
        }
        else if( id_eq(tok->value.s, "String") ) {
            return tString;
        }
        else {
            fprintf(stderr, "ERROR: Don't recognize the given type!\n");
            return NULL;
        }
    }
    else if( tok->type == tok_funtype ) {
        return tyap_fn( get_type_sig2(tok->lhs), get_type_sig2(tok->rhs) );
    }
    else {
        fprintf(stderr, "ERROR: Don't know how to handle the given type!\n");
        return NULL;
    }
}

static type * get_type_sig( token *tok ) {
    if( !tok || (tok->type != tok_Typesig && tok->type != tok_Kernel) ) {
        fprintf(stderr, "ERROR: get_type_sig didn't receive type signature! ");
        if( !tok ) {
            fprintf(stderr, "Token is null!\n");
        }
        else {
            printf("Received: ");
            printtok(tok);
            printf("\n");
        }
        return NULL;
    }
    return get_type_sig2(tok->rhs);
}

/*
 * We need a method to generate assumptions from explicit binds.
 */
static assump * bind_to_assump( token *tok ) {
    type *t;
    if( !tok || tok->type != tok_Bind ) {
        fprintf(stderr, "ERROR: bind_to_assump didn't receive a bind! ");
        fprintf(stderr, "Received: ");
        printtok(tok);
        fprintf(stderr, "\n");
        return NULL;
    }
    t = get_type_sig(tok->lhs);
    return new_assump(tok->value.s, forall(NULL, qualified_type(NULL, t)));
}

/*
 * Extracts the type scheme from the assumptions given for the given token, then
 * performing type inference on the bind with the produced scheme.
 */
static pred * ti_expl_from_token( class_env *ce, assump *as, token *tok ) {
    assump *as2;
    for( as2 = as; as2; as2 = as2->next ) {
        /* Match found */
        if( id_eq(as2->i, tok->value.s) ) {
            return ti_expl(ce, as, as2->s, tok);
        }
    }
    fprintf(stderr, "ERROR: ti_expl_from_token: couldn't find assump!\n");
    return NULL;
}

static pred_assump * ti_bindgroups( class_env *ce, assump *as, program *prog ) {
    pred_assump *impl, *impls;
    pred *qs;
    assump *as2, *as3;
    token *t;
    /* First we need to generate assumptions from our explicit binds */
    as2 = NULL;
    if( prog->expl ) {
        for( t = prog->expl->lhs; t; t = t->next ) {
            as2 = assump_join(as2, bind_to_assump(t));
        }
    }
    /* With our first round of assumptions, we can now do type inference for
       each of the bind groups in the implicit group, building up assumptions
       as we go. */
    impls = new_pred_assump(NULL, assump_join(as2, as));
    for( t = prog->impl; t; t = t->next ) {
        impl = ti_impls(ce, impls->a, t->lhs);
        impls->p = pred_join(impls->p, impl->p);
        impls->a = assump_join(impls->a, impl->a);
    }
    /* Type inference done for the implicit group, so now we can do the explicit
       group to make sure they are typed correctly. */
    as3 = assump_join(impls->a, assump_join(as2, as));
    qs = NULL;
    if( prog->expl ) {
        for( t = prog->expl->lhs; t; t = t->next ) {
            qs = pred_join(qs, ti_expl_from_token(ce, as3, t));
        }
    }
    return new_pred_assump(pred_join(impls->p, qs), assump_join(impls->a, as2));
}

/*
*** TIProg.hs
type Program = [BindGroup]

tiProgram :: ClassEnv -> [Assump] -> Program -> [Assump]
tiProgram ce as bgs = runTI $
                      do (ps, as') <- tiSeq tiBindGroup ce as bgs
                         s         <- getSubst
                         let rs     = reduce ce (apply s ps)
                         s'        <- defaultSubst ce [] rs
                         return (apply (s'@@s) as')
*/

static assump * ti_program( class_env *ce, assump *as, program *prog ) {
    pred_assump *ps_as;
    /*pred *rs; * Note: unused */
    ps_as = ti_bindgroups(ce, as, prog);
    /*rs = reduce(ce, apply_pred(curr_subst, ps_as->p)); * Note: unused */
    return apply_assump(curr_subst, ps_as->a);
}

static assump * prelude_functions() {
    assump *a;
    a = new_assump("add", forall(NULL, qualified_type(NULL,
        tyap_fn(tInt, tyap_fn(tInt, tInt)))));
    a = assump_join(a,
        new_assump("dec", forall(NULL, qualified_type(NULL,
        tyap_fn(tInt, tInt)))));
    return a;
}

void test_type_inference( program *prog ) {
    class_env *ce;
    assump *as, *result;
    generate_types();
    ce = example_insts(prelude_classes());
    as = prelude_functions();
    result = ti_program(ce, as, prog);
    print_assumps(result);
    print_substs(curr_subst);
}

/*
tiBindGroup' ce as bs = do (ps,as') <- tiBindGroup ce as bs
                           trim (tv (as'++as))
                           return (ps,as')

tiProgram' :: ClassEnv -> [Assump] -> Program -> [Assump]
tiProgram' ce as bgs = runTI $
  do (ps, as') <- tiSeq tiBindGroup' ce as bgs
     s         <- getSubst
     let rs     = reduce ce (apply s ps)
     s'        <- defaultSubst ce [] rs
     return (apply (s'@@s) as')

*/
