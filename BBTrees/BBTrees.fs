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
    correctness. *)

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

type Set<'T when 'T : comparison> =
    | E
    | T of 'T * int * Set<'T> * Set<'T>

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Set =
    (* Private members *)

    /// Weight is a parameter to the rebalancing process.
    let private weight = 3

    let inline private lt (x, y) = x < y

    let private size = function
        | E -> 0
        | T (_:'T,n,_,_) -> n

    (*fun N(v,l,r) = T(v,1+size(l)+size(r),l,r)*)
    let private N = function
        | (v : 'T,E,E) ->
            T(v,1,E,E)
        | (v,E,(T(_,n,_,_) as r)) ->
            T(v,n+1,E,r)
        | (v, (T(_,n,_,_) as l), E) ->
            T(v,n+1,l,E)
        | (v, (T(_,n,_,_) as l), (T(_,m,_,_) as r)) ->
            T(v,n+m+1,l,r)

    let private single_L (a,x,T(b,_,y,z)) =
        N(b,N(a,x,y),z)

    let private single_R (b,T(a,_,x,y),z) =
        N(a,x,N(b,y,z))

    let private double_L (a,w,T(c,_,T(b,_,x,y),z)) =
        N(b,N(a,w,x),N(c,y,z))

    let private double_R (c,T(a,_,w,T(b,_,x,y)),z) =
        N(b,N(a,w,x),N(c,y,z))

    let private T' = function
        | (v,E,E) ->
            T(v,1,E,E)
        | (v,E,(T(_,_,E,E) as r)) ->
            T(v,2,E,r)
        | (v,(T(_,_,E,E) as l),E) ->
            T(v,2,l,E)
        | (_,E,T(_,_,T(_,_,_,_),E)) as p ->
            double_L p
        | (_,T(_,_,E,T(_,_,_,_)),E) as p ->
            double_R p

        (* these cases almost never happen with small weight *)
        | (_,E,T(_,_,T(_,ln,_,_),T(_,rn,_,_))) as p ->
            if ln<rn then single_L p else double_L p

        | (_,T(_,_,T(_,ln,_,_),T(_,rn,_,_)),E) as p ->
            if ln>rn then single_R p else double_R p

        | (_,E,T(_,_,E,_)) as p -> single_L p
        | (_,T(_,_,_,E),E) as p -> single_R p

        | (v,(T(lv,ln,ll,lr) as l),(T(rv,rn,rl,rr) as r)) as p ->
            if rn >= weight * ln then (*right is too big*)
                let rln = size rl
                let rrn = size rr
                if rln < rrn then single_L p else double_L p
            
            elif ln >= weight * rn then  (*left is too big*)
                let lln = size ll
                let lrn = size lr
                if lrn < lln then single_R p else double_R p
            else
                T(v,ln+rn+1,l,r)

    let rec add = function
        | E, x ->
            T(x,1,E,E)
        | (T(v,_,l,r) as set), x ->
            if lt(x,v) then T'(v,add(l,x),r)
            elif lt(v,x) then T'(v,l,add(r,x))
            else set

    let rec private concat3 = function
        | (E,v,r) -> add(r,v)
        | (l,v,E) -> add(l,v)
        | ((T(v1,n1,l1,r1) as l), v, (T(v2,n2,l2,r2) as r)) ->
            if weight*n1 < n2 then T'(v2,concat3(l,v,l2),r2)
            elif weight*n2 < n1 then T'(v1,l1,concat3(r1,v,r))
            else N(v,l,r)

    let rec private split_lt = function
        | (E,x) -> E
        | ((T(v,_,l,r) as t), x) ->
            if lt(x,v) then split_lt(l,x)
            elif lt(v,x) then concat3(l,v,split_lt(r,x))
            else l

    let rec private split_gt = function
        | (E,x) -> E
        | ((T(v,_,l,r) as t), x) ->
            if lt(v,x) then split_gt(r,x)
            elif lt(x,v) then concat3(split_gt(l,x),v,r)
            else r

    let rec private min = function
        | T(v,_,E,_) -> v
        | T(v,_,l,_) -> min l

    let rec private delete' = function
        | (E,r) -> r
        | (l,E) -> l
        | (l,r) ->
            let min_elt = min r
            T'(min_elt,l,delmin r)

    and private delmin = function
        | T(_,_,E,r) -> r
        | T(v,_,l,r) -> T'(v,delmin l,r)

    let rec private concat = function
        | (E, s2) -> s2
        | (s1, E) -> s1
        | ((T(v1,n1,l1,r1) as t1), (T(v2,n2,l2,r2) as t2)) ->
            if weight*n1 < n2 then T'(v2,concat(t1,l2),r2)
            elif weight*n2 < n1 then T'(v1,l1,concat(r1,t2))
            else T'(min t2,t1, delmin t2)

    let private fold (f,``base``,set) =
        let rec fold' (``base``,set) =
            match set with
            | E -> ``base``
            | T(v,_,l,r) ->
                fold'(f(v,fold'(``base``,r)),l)
        fold'(``base``,set)

    
    (* Public members *)

    let empty<'T when 'T : comparison> : Set<'T> = E

    let singleton x = T(x,1,E,E)

    let rec private trim = function
        | (lo,hi,E) -> E
        | (lo,hi,(T(v,_,l,r) as s)) ->
            if  lt(lo,v)  then
                if  lt(v,hi)  then  s
                else  trim(lo,hi,l)
            else trim(lo,hi,r)

    let rec private uni_bd = function
        | (s,E,lo,hi) -> s : Set<'T>
        | (E,T(v,_,l,r),lo,hi) -> 
            concat3(split_gt(l,lo),v,split_lt(r,hi))
        | (T(v,_,l1,r1), (T(v2,_,l2,r2) as s2),lo,hi) ->
            concat3(uni_bd(l1,trim(lo,v,s2),lo,v),
                v, 
                uni_bd(r1,trim(v,hi,s2),v,hi))
              (* inv:  lo < v < hi *)

               (*all the other versions of uni and trim are
               specializations of the above two functions with
               lo=-infinity and/or hi=+infinity *)

    let rec private trim_lo = function
        | (_,E) -> E
        | (lo, (T(v,_,_,r) as s)) ->
            if lt(lo,v) then s else trim_lo(lo,r)

    let rec private trim_hi = function
        | (_,E) -> E
        | (hi, (T(v,_,l,_) as s)) ->
            if lt(v,hi) then s else trim_hi(hi,l)

    let rec private uni_hi = function
        | (s,E,hi) -> s
        | (E,T(v,_,l,r),hi) ->
            concat3(l,v,split_lt(r,hi))
        | (T(v,_,l1,r1), (T(v2,_,l2,r2) as s2),hi) ->
            concat3(uni_hi(l1,trim_hi(v,s2),v),
                v, 
                uni_bd(r1,trim(v,hi,s2),v,hi))

    let rec private uni_lo = function
        | (s,E,lo) -> s
        | (E,T(v,_,l,r),lo) ->
            concat3(split_gt(l,lo),v,r)
        | (T(v,_,l1,r1), (T(v2,_,l2,r2) as s2),lo) ->
            concat3(uni_bd(l1,trim(lo,v,s2),lo,v),
                v, 
                uni_lo(r1,trim_lo(v,s2),v))

    let hedge_union = function
        | (s,E) -> s
        | (E,(T(v,_,l,r) as s)) -> s
        | (T(v,_,l1,r1), (T(v2,_,l2,r2) as s2)) ->
            concat3(uni_hi(l1,trim_hi(v,s2),v),
                v, 
                uni_lo(r1,trim_lo(v,s2),v))

    let rec old_union = function
        | (E,s2) -> s2
        | (s1,E) -> s1
        | ((T(v,_,l,r) as s1), s2) ->
            let l2 = split_lt(s2,v)
            let r2 = split_gt(s2,v)
            concat3(old_union(l,l2),v,old_union(r,r2))

    (* The old_union version is about 20% slower than hedge_union in most cases *)
    //let inline union (s1,s2) = old_union(s1,s2)
    let inline union (s1,s2) = hedge_union(s1,s2)

    let rec difference = function
        | (E,s) -> E
        | (s,E) -> s
        | (s, T(v,_,l,r)) ->
            let l2 = split_lt(s,v)
            let r2 = split_gt(s,v)
            concat(difference(l2,l),difference(r2,r))

    // NOTE : This function was originally called 'member' but the name
    // was changed since that's a keyword (reserved identifier) in F#.
    let contains (x,set) =
        let rec mem = function
            | E -> false
            | T(v,_,l,r) ->
                if lt(x,v) then mem l else if lt(v,x) then mem r else true
        mem set

    (*fun intersection (a,b) = difference(a,difference(a,b))*)

    let rec intersection = function
        | (E,_) -> E
        | (_,E) -> E
        | (s, T(v,_,l,r)) ->
            let l2 = split_lt(s,v)
            let r2 = split_gt(s,v)
        
            if contains(v,s) then
                concat3(intersection(l2,l),v,intersection(r2,r))
            else
                concat(intersection(l2,l),intersection(r2,r))

    let inline private cons (x,l) = x :: l

    let members set = fold(cons,[],set)

    let cardinality = function
        | E -> 0
        | T(_,n,_,_) -> n

    let rec delete = function
        | (E,x) -> E
        | ((T(v,_,l,r) as set), x) ->
            if lt(x,v) then T'(v,delete(l,x),r)
            elif lt(v,x) then T'(v,l,delete(r,x))
            else delete'(l,r)

    let fromList l =
        (E, l)
        ||> List.fold (fun x y -> add (x, y))

    type intset = Set<int>

