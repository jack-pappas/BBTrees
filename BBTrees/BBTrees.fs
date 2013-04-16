(*
    Copyright 1992-1996 Stephen Adams.

    This software may be used freely provided that:
      1. This copyright notice is attached to any copy, derived work,
         or work including all or part of this software.
      2. Any derived work must contain a prominent notice stating that
         it has been altered from the original.

*)
(*

Copyright 1992-1996 Stephen Adams
Copyright 2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

(*  This file has been heavily modified from the original version by Stephen Adams.
    The code was ported from Standard ML (SML) to F# as literally as possible to preserve
    correctness; after implementing some basic unit tests to check for correct behavior,
    a number of small modifications were made to maximize the efficiency of the code
    for running on the .NET CLR. *)

(* Address:  Electronics & Computer Science
             University of Southampton
         Southampton  SO9 5NH
         Great Britian
   E-mail:   sra@ecs.soton.ac.uk

   Comments:

     1.  The implementation is based on Binary search trees of Bounded
         Balance, similar to Nievergelt & Reingold, SIAM J. Computing
         2(1), March 1973.  The main advantage of these trees is that
         they keep the size of the tree in the node, giving a constant
         time size operation.

     2.  The bounded balance criterion is simpler than N&R's alpha.
         Simply, one subtree must not have more than `weight' times as
         many elements as the opposite subtree.  Rebalancing is
         guaranteed to reinstate the criterion for weight>2.23, but
         the occasional incorrect behaviour for weight=2 is not
         detrimental to performance.

     3.  There are two implementations of union.  The default,
         hedge_union, is much more complex and usually 20% faster.  I
         am not sure that the performance increase warrants the
         complexity (and time it took to write), but I am leaving it
         in for the competition.  It is derived from the original
         union by replacing the split_lt(gt) operations with a lazy
         version. The `obvious' version is called old_union.
*)

namespace BBTrees

[<AutoOpen>]
module internal Constants =
    /// Weight is a parameter to the rebalancing process.
    let [<Literal>] weight = 3


[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
type Set<'T when 'T : comparison> =
    /// Empty set.
    | E
    /// Node.
    | T of 'T * int * Set<'T> * Set<'T>

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Set =
    (* Private members *)

    let inline private lt (x, y) = x < y

    //
    let private size = function
        | E -> 0
        | T (_:'T,n,_,_) -> n

    // TODO : This is the same as 'size' -- can we remove one of them, or
    // is there some benefit (e.g., abstraction) for keeping both?
    let cardinality = function
        | E -> 0
        | T(_,n,_,_) -> n

    (*fun N(v,l,r) = T(v,1+size(l)+size(r),l,r)*)
    //
    let private N (value : 'T, l, r) : Set<'T> =
        match l, r with
        | E, E ->
            T (value, 1, E, E)
        | E, (T (_,n,_,_) as r) ->
            T (value, n+1, E, r)
        | (T (_,n,_,_) as l), E ->
            T (value, n+1, l, E)
        | (T (_,n,_,_) as l), (T (_,m,_,_) as r) ->
            T (value, n+m+1, l, r)

    //
    let inline private single_L (a, x, T(b,_,y,z)) =
        N (b, N (a,x,y), z)

    //
    let inline private single_R (b, T(a,_,x,y), z) =
        N (a, x, N(b,y,z))

    //
    let inline private double_L (a, w, T(c,_, T(b,_,x,y), z)) =
        N (b, N(a,w,x), N(c,y,z))

    //
    let inline private double_R (c, T(a,_,w, T(b,_,x,y)), z) =
        N (b, N (a,w,x), N (c,y,z))

    //
    let private T' (value : 'T, l, r) : Set<'T> =
        match l, r with
        | E, E ->
            T (value, 1, E, E)
        | E, T (_,_,E,E) ->
            T (value, 2, E, r)
        | T (_,_,E,E), E ->
            T (value, 2, l, E)
        | E, T (_,_, T(_,_,_,_), E) ->
            double_L (value, l, r)
        | T (_,_, E, T(_,_,_,_)), E ->
            double_R (value, l, r)

        (* these cases almost never happen with small weight *)
        | E, T (_,_, T(_,ln,_,_), T(_,rn,_,_)) ->
            if ln < rn then single_L (value, l, r)
            else double_L (value, l, r)

        | T (_,_, T(_,ln,_,_), T(_,rn,_,_)), E ->
            if ln > rn then single_R (value, l, r)
            else double_R (value, l, r)

        | E, T (_,_,E,_) ->
            single_L (value, l, r)
        | T (_,_,_,E), E ->
            single_R (value, l, r)

        | T (lv, ln, ll, lr), T (rv, rn, rl, rr) ->
            if rn >= weight * ln then (*right is too big*)
                if size rl < size rr then
                    single_L (value, l, r)
                else
                    double_L (value, l, r)
            
            elif ln >= weight * rn then  (*left is too big*)
                if size lr < size ll then
                    single_R (value, l, r)
                else
                    double_R (value, l, r)
            else
                T (value, ln+rn+1, l, r)

    //
    let rec add (set, x) : Set<'T> =
        match set with
        | E ->
            T (x, 1, E, E)
        | T (v, _, l, r) ->
            if lt (x, v) then
                T' (v, add (l, x), r)
            elif lt (v, x) then
                T' (v, l, add (r, x))
            else set

    //
    let rec private concat3 (l, value, r) : Set<'T> =
        match l, r with
        | E, r ->
            add (r, value)
        | l, E ->
            add (l, value)
        | T (v1, n1, l1, r1), T (v2, n2, l2, r2) ->
            if weight * n1 < n2 then
                T' (v2, concat3 (l, value, l2), r2)
            elif weight * n2 < n1 then
                T' (v1, l1, concat3 (r1, value, r))
            else
                N (value, l, r)

    //
    let rec private split_lt (set, x) =
        match set with
        | E -> E
        | T (v, _, l, r) ->
            if lt (x, v) then
                split_lt (l, x)
            elif lt (v, x) then
                concat3 (l, v, split_lt (r, x))
            else l

    //
    let rec private split_gt (set, x) =
        match set with
        | E -> E
        | T (v, _, l, r) ->
            if lt (v, x) then
                split_gt (r, x)
            elif lt (x, v) then
                concat3 (split_gt (l, x), v, r)
            else r

    //
    let rec private min = function
        | T (v, _, E, _) -> v
        | T (v, _, l, _) -> min l

    //
    let rec private delete' (l, r) =
        match l, r with
        | E, r -> r
        | l, E -> l
        | l, r ->
            T' (min r, l, delmin r)

    //
    and private delmin (set : Set<'T>) =
        match set with
        | E ->
            invalidArg "set" "The set is empty."
        | T (_, _, E, r) -> r
        | T (v, _, l, r) ->
            T' (v, delmin l, r)

    //
    let rec private concat (s1, s2) : Set<'T> =
        match s1, s2 with
        | E, s2 -> s2
        | s1, E -> s1
        | T (v1, n1, l1, r1), T (v2, n2, l2, r2) ->
            if weight * n1 < n2 then
                T' (v2, concat (s1, l2), r2)
            elif weight * n2 < n1 then
                T' (v1, l1, concat (r1, s2))
            else
                T' (min s2, s1, delmin s2)

    //
    let private fold (f, state, set : Set<'T>) =
        let rec fold' (state, set) =
            match set with
            | E -> state
            | T (v, _, l, r) ->
                fold' (f (v, fold' (state, r)), l)
        fold' (state, set)

    
    (* Public members *)

    //
    let empty<'T when 'T : comparison> : Set<'T> = E

    //
    let singleton x : Set<'T> =
        T (x, 1, E, E)

    //
    let rec private trim (lo, hi, s) : Set<'T> =
        match s with
        | E -> E
        | T (v, _, l, r) ->
            if lt (lo, v) then
                if lt (v, hi) then s
                else trim (lo, hi, l)
            else trim (lo, hi, r)

    //
    let rec private uni_bd (s1, s2, lo, hi) : Set<'T> =
        match s1, s2 with
        | s1, E -> s1
        | E, T (v, _, l, r) -> 
            concat3 (
                split_gt (l, lo),
                v,
                split_lt (r, hi))

        | T (v, _, l1, r1), T (v2, _, l2, r2) ->
            concat3(
                uni_bd (l1, trim (lo, v, s2), lo, v),
                v, 
                uni_bd (r1, trim (v, hi, s2), v, hi))
              (* inv:  lo < v < hi *)

               (*all the other versions of uni and trim are
               specializations of the above two functions with
               lo=-infinity and/or hi=+infinity *)

    //
    let rec private trim_lo (lo, set) : Set<'T> =
        match set with
        | E -> E
        | T (v, _, _, r) ->
            if lt (lo, v) then set
            else trim_lo (lo, r)

    //
    let rec private trim_hi (hi, set) : Set<'T> =
        match set with
        | E -> E
        | T (v, _, l, _) ->
            if lt (v, hi) then set
            else trim_hi (hi, l)

    //
    let rec private uni_hi (s1, s2, hi) : Set<'T> =
        match s1, s2 with
        | s1, E -> s1
        | E, T (v, _, l, r) ->
            concat3 (l, v, split_lt (r, hi))
        | T (v, _, l1, r1), T (v2, _, l2, r2) ->
            concat3(
                uni_hi (l1, trim_hi (v, s2), v),
                v, 
                uni_bd (r1, trim (v, hi, s2), v, hi))

    //
    let rec private uni_lo (s1, s2, lo) : Set<'T> =
        match s1, s2 with
        | s1, E -> s1
        | E, T (v, _, l, r) ->
            concat3 (split_gt (l, lo), v, r)
        | T (v, _, l1, r1), T (v2, _, l2, r2) ->
            concat3(
                uni_bd (l1, trim (lo, v, s2), lo, v),
                v, 
                uni_lo (r1, trim_lo (v, s2), v))

    //
    let hedge_union (s1, s2) : Set<'T> =
        match s1, s2 with
        | s1, E -> s1
        | E, T (_,_,_,_) -> s2
        | T (v, _, l1, r1), T (v2, _, l2, r2) ->
            concat3(
                uni_hi (l1, trim_hi (v, s2), v),
                v, 
                uni_lo (r1, trim_lo (v, s2), v))

    //
    let rec old_union (s1, s2) : Set<'T> =
        match s1, s2 with
        | E, s2 -> s2
        | s1, E -> s1
        | T (v, _, l, r), s2 ->
            let l2 = split_lt (s2, v)
            let r2 = split_gt (s2, v)
            concat3(
                old_union (l, l2),
                v,
                old_union (r, r2))

    (* The old_union version is about 20% slower than hedge_union in most cases *)
    //let inline union (s1, s2) = old_union(s1, s2)
    let inline union (s1, s2) : Set<'T> = hedge_union(s1, s2)

    //
    let rec difference (s1, s2) : Set<'T> =
        match s1, s2 with
        | E, _ -> E
        | s1, E -> s1
        | s1, T (v, _, l, r) ->
            let l2 = split_lt (s1, v)
            let r2 = split_gt (s1, v)
            concat (
                difference (l2, l),
                difference (r2, r))

    // NOTE : This function was originally called 'member' but the name
    // was changed since that's a keyword (reserved identifier) in F#.
    //
    let rec contains (x, set : Set<'T>) : bool =
        match set with
        | E -> false
        | T (v, _, l, r) ->
            if lt (x, v) then contains (x, l)
            elif lt (v, x) then contains (x, r)
            else true

    (*fun intersection (a,b) = difference(a,difference(a,b))*)

    //
    let rec intersection (s1, s2) : Set<'T> =
        match s1, s2 with
        | E, _ -> E
        | _, E -> E
        | s1, T (v, _, l, r) ->
            let l2 = split_lt (s1, v)
            let r2 = split_gt (s1, v)
        
            if contains (v, s1) then
                concat3 (
                    intersection (l2, l),
                    v,
                    intersection (r2, r))
            else
                concat (
                    intersection (l2, l),
                    intersection (r2, r))

    //
    let rec delete (set, x) : Set<'T> =
        match set with
        | E -> E
        | T(v, _, l, r) ->
            if lt (x, v) then
                T' (v, delete (l, x), r)
            elif lt (v, x) then
                T' (v, l, delete (r, x))
            else
                delete' (l, r)

    let inline private cons (x, l) = x :: l
    
    //
    let toList (set : Set<'T>) = fold (cons, [], set)

    //
    let fromList l : Set<'T> =
        (E, l) ||> List.fold (fun x y -> add (x, y))

