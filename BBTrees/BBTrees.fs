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
(*
    Copyright 1992-1996 Stephen Adams.

    This software may be used freely provided that:
      1. This copyright notice is attached to any copy, derived work,
         or work including all or part of this software.
      2. Any derived work must contain a prominent notice stating that
         it has been altered from the original.

*)
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
(*  This file has been heavily modified from the original version by Stephen Adams.
    The code was ported from Standard ML (SML) to F# with few changes; it was then modified
    to more closely adhere to "canonical" F# coding style and naming conventions,
    and to acheive better performance on the .NET CLR.  *)

namespace BBTrees


[<AutoOpen>]
module internal Constants =
    /// Weight is a parameter to the rebalancing process.
    let [<Literal>] weight = 3u


[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
type BBTree<'T when 'T : comparison> =
    /// Empty set.
    | E
    /// Node.
    // Left-Child * Right-Child * Value * Size
    | T of BBTree<'T> * BBTree<'T> * 'T * uint32

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module BBTree =
    /// The empty set.
    let empty<'T when 'T : comparison> : BBTree<'T> = E

    /// Creates a new set containing the given value.
    let singleton x : BBTree<'T> =
        T (E, E, x, 1u)

    /// Returns the number of elements in the set.
    let count (set : BBTree<'T>) =
        match set with
        | E -> 0u
        | T (_,_,_,n) -> n

    // NOTE : This function was originally called 'member' but the name
    // was changed since that's a keyword (reserved identifier) in F#.
    /// Tests whether the set contains the given value.
    let rec contains x (set : BBTree<'T>) : bool =
        match set with
        | E -> false
        | T (l, r, v, _) ->
            let c = compare x v
            if c < 0 then
                // x < v
                contains x l
            elif c = 0 then
                // x = v
                true
            else
                // x > v
                contains x r

    (*fun N(v,l,r) = T(v,1+size(l)+size(r),l,r)*)
    /// This is the smart constructor for T that ensures that the size of the tree is
    /// maintained correctly. The tree (v,l,r) must already be balanced.
    let private N (value : 'T, l, r) : BBTree<'T> =
        match l, r with
        | E, E ->
            T (E, E, value, 1u)
        | E, T (_,_,_,n) ->
            T ( E, r, value, n + 1u)
        | T (_,_,_,n), E ->
            T (l, E, value, n + 1u)
        | T (_,_,_,n), T (_,_,_,m) ->
            T (l, r, value, n + m + 1u)

    /// Single left-rotation.
    let inline private single_L (a, x, T (y, z, b, _)) : BBTree<'T> =
        N (b, N (a, x, y), z)

    /// Single right-rotation.
    let inline private single_R (b, T (x, y, a, _), z) : BBTree<'T> =
        N (a, x, N (b, y, z))

    /// Double left-rotation.
    let inline private double_L (a, w, T (T (x, y, b, _), z, c, _)) : BBTree<'T> =
        N (b, N (a, w, x), N (c, y, z))

    /// Double right-rotation.
    let inline private double_R (c, T (w, T (x, y, b, _), a, _), z) : BBTree<'T> =
        N (b, N (a, w, x), N (c, y, z))

    /// T' is used when the original tree was in balance and one of l or r has
    /// changed in size by at most one element, as in insertion or deletion of
    /// a single element.
    let private T' (value : 'T, l, r) : BBTree<'T> =
        match l, r with
        | E, E ->
            T (E, E, value, 1u)
        | E, T (E, E, _, _) ->
            T (E, r, value, 2u)
        | T (E, E, _,_), E ->
            T (l, E,value, 2u)
        | E, T (T (_,_,_,_), E, _, _) ->
            double_L (value, l, r)
        | T (E, T (_,_,_,_), _, _), E ->
            double_R (value, l, r)

        (* these cases almost never happen with small weight *)
        | E, T (T (_,_,_,ln), T (_,_,_,rn), _, _) ->
            if ln < rn then single_L (value, l, r)
            else double_L (value, l, r)

        | T (T (_,_,_,ln), T (_,_,_,rn), _, _), E ->
            if ln > rn then single_R (value, l, r)
            else double_R (value, l, r)

        | E, T (E,_,_,_) ->
            single_L (value, l, r)
        | T (_,E,_,_), E ->
            single_R (value, l, r)

        | T (ll, lr, _, ln), T (rl, rr, _, rn) ->
            if rn >= weight * ln then (* right is too big *)
                if count rl < count rr then
                    single_L (value, l, r)
                else
                    double_L (value, l, r)
            
            elif ln >= weight * rn then  (* left is too big *)
                if count lr < count ll then
                    single_R (value, l, r)
                else
                    double_R (value, l, r)
            else
                T (l, r, value, ln + rn + 1u)

    //
    let rec minElement (set : BBTree<'T>) =
        match set with
        | E ->
            invalidArg "set" "The set is empty"
        | T (E, _, v, _) -> v
        | T (l, _, _, _) -> minElement l

    //
    let rec private delete' (l, r) =
        match l, r with
        | E, r -> r
        | l, E -> l
        | l, r ->
            T' (minElement r, l, delmin r)

    //
    and private delmin (set : BBTree<'T>) =
        match set with
        | E ->
            invalidArg "set" "The set is empty."
        | T (E, r, _, _) -> r
        | T (l, r, v, _) ->
            T' (v, delmin l, r)

    /// Adds an element to the given set, returning a new set.
    /// No exception is raised if the set already contains the element.
    let rec add x (set : BBTree<'T>) =
        match set with
        | E ->
            T (E, E, x, 1u)
        | T (l, r, v, _) ->
            if x < v then
                T' (v, add x l, r)
            elif x > v then
                T' (v, l, add x r)
            else set

    /// Removes an element from the given set, returning a new set.
    /// No exception is raised if the set does not contain the element.
    let rec remove x set : BBTree<'T> =
        match set with
        | E -> E
        | T(l, r, v, _) ->
            let c = compare x v
            if c < 0 then
                // x < v
                T' (v, remove x l, r)
            elif c = 0 then
                // x = v
                delete' (l, r)
            else
                // x > v
                T' (v, l, remove x r)

    //
    let rec private concat (s1, s2) : BBTree<'T> =
        match s1, s2 with
        | E, _ -> s2
        | _, E -> s1
        | T (l1, r1, v1, n1), T (l2, r2, v2, n2) ->
            if weight * n1 < n2 then
                T' (v2, concat (s1, l2), r2)
            elif weight * n2 < n1 then
                T' (v1, l1, concat (r1, s2))
            else
                T' (minElement s2, s1, delmin s2)

    /// concat3 can join trees of arbitrary sizes. As with the other constructors,
    /// 'value' must be greater than every element in l and less than every element in r.
    let rec private concat3 (l, value, r) : BBTree<'T> =
        match l, r with
        | E, _ ->
            add value r
        | _, E ->
            add value l
        | T (l1, r1, v1, n1), T (l2, r2, v2, n2) ->
            if weight * n1 < n2 then
                T' (v2, concat3 (l, value, l2), r2)
            elif weight * n2 < n1 then
                T' (v1, l1, concat3 (r1, value, r))
            else
                N (value, l, r)

    //
    let rec private split_lt x set =
        match set with
        | E -> E
        | T (l, r, v, _) ->
            let c = compare x v
            if c < 0 then
                // x < v
                split_lt x l
            elif c = 0 then
                // x = v
                l
            else
                // x > v
                concat3 (l, v, split_lt x r)

    //
    let rec private split_gt x set =
        match set with
        | E -> E
        | T (l, r, v, _) ->
            let c = compare v x
            if c < 0 then
                // v < x
                split_gt x r
            elif c = 0 then
                // v = x
                r
            else
                // v > x
                concat3 (split_gt x l, v, r)

    //
    let rec private trim (lo, hi, set) : BBTree<'T> =
        match set with
        | E -> E
        | T (l, r, v, _) ->
            if lo < v then
                if v < hi then set
                else trim (lo, hi, l)
            else trim (lo, hi, r)

    //
    let rec private uni_bd (s1, s2, lo, hi) : BBTree<'T> =
        match s1, s2 with
        | _, E -> s1
        | E, T (l, r, v, _) -> 
            concat3 (
                split_gt lo l,
                v,
                split_lt hi r)

        | T (l1, r1, v1, _), T (_,_,_,_) ->
            (* invariant:  lo < v1 < hi *)
            concat3(
                uni_bd (l1, trim (lo, v1, s2), lo, v1),
                v1, 
                uni_bd (r1, trim (v1, hi, s2), v1, hi))

            (* all the other versions of uni and trim are specializations of the above two functions with:
                lo = -infinity and/or hi = +infinity *)

    //
    let rec private trim_lo (lo, set) : BBTree<'T> =
        match set with
        | E -> E
        | T (_, r, v, _) ->
            if lo < v then set
            else trim_lo (lo, r)

    //
    let rec private trim_hi (hi, set) : BBTree<'T> =
        match set with
        | E -> E
        | T (l, _, v, _) ->
            if v < hi then set
            else trim_hi (hi, l)

    //
    let rec private uni_hi (s1, s2, hi) : BBTree<'T> =
        match s1, s2 with
        | _, E -> s1
        | E, T (l, r, v, _) ->
            concat3 (l, v, split_lt hi r)
        | T (l1, r1, v1, _), T (_,_,_,_) ->
            concat3 (
                uni_hi (l1, trim_hi (v1, s2), v1),
                v1, 
                uni_bd (r1, trim (v1, hi, s2), v1, hi))

    //
    let rec private uni_lo (s1, s2, lo) : BBTree<'T> =
        match s1, s2 with
        | _, E -> s1
        | E, T (l, r, v, _) ->
            concat3 (split_gt lo l, v, r)
        | T (l1, r1, v, _), T (_,_,_,_) ->
            concat3 (
                uni_bd (l1, trim (lo, v, s2), lo, v),
                v, 
                uni_lo (r1, trim_lo (v, s2), v))

    /// Computes the union of two sets.
    // NOTE : This is the 'hedge_union' algorithm specified in the original paper.
    let union s1 s2 : BBTree<'T> =
        match s1, s2 with
        | s1, E -> s1
        | E, T (_,_,_,_) -> s2
        | T (l1, r1, v, _), T (_,_,_,_) ->
            concat3 (
                uni_hi (l1, trim_hi (v, s2), v),
                v, 
                uni_lo (r1, trim_lo (v, s2), v))

    /// Computes the union of two sets.
    // NOTE : This is the 'old_union' algorithm specified in the original paper.
    // In most cases, the old_union version is about 20% slower than hedge_union.
    //[<System.Obsolete("Use the 'union' function instead - it is implemented using a more efficient algorithm.")>]
    let rec unionOld s1 s2 : BBTree<'T> =
        match s1, s2 with
        | E, _ -> s2
        | _, E -> s1
        | T (l, r, v, _), _ ->
            let l2 = split_lt v s2
            let r2 = split_gt v s2
            concat3 (
                unionOld l l2,
                v,
                unionOld r r2)

    /// Removes the elements of the second set from the first.
    let rec difference s1 s2 : BBTree<'T> =
        match s1, s2 with
        | E, _ -> E
        | _, E -> s1
        | _, T (l, r, v, _) ->
            let l2 = split_lt v s1
            let r2 = split_gt v s1
            concat (
                difference l2 l,
                difference r2 r)

    /// Computes the intersection of the two sets.
    let rec intersection s1 s2 : BBTree<'T> =
        match s1, s2 with
        | E, _ -> E
        | _, E -> E
        | _, T (l, r, v, _) ->
            let l2 = split_lt v s1
            let r2 = split_gt v s1
        
            if contains v s1 then
                concat3 (
                    intersection l2 l,
                    v,
                    intersection r2 r)
            else
                concat (
                    intersection l2 l,
                    intersection r2 r)

    //
    let rec foldBack folder (set : BBTree<'T>) (state : 'State) =
        match set with
        | E -> state
        | T (l, r, v, _) ->
            // Fold over the right subtree.
            let state = foldBack folder r state

            // Apply the folder to the value of the current node.
            let state = folder v state

            // Fold over the left subtree.
            foldBack folder l state

    let inline private cons x l = x :: l

    let inline private flip f x y = f y x
    
    //
    let toList (set : BBTree<'T>) =
        // Fold backwards over the tree, so the resulting list is ordered from least-to-greatest
        // without having to reverse the list at the end.
        foldBack cons set []

    //
    let fromList list : BBTree<'T> =
        (E, list) ||> List.fold (flip add)

