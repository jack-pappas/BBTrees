(*

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

module Tests.BBTrees

open BBTrees
open NUnit.Framework


[<Test>]
let basic () : unit =
    let add value set =
        Set.add (set, value)

    //
    let fibs =
        Set.empty
        |> add 1
        |> add 1
        |> add 2
        |> add 3
        |> add 5
        |> add 8

    //
    let primes =
        Set.empty
        |> add 2
        |> add 3
        |> add 5
        |> add 7
        |> add 11
        |> add 13
        |> add 17
        |> add 19

    Assert.AreEqual (5, Set.count fibs)
    Assert.AreEqual (8, Set.count primes)

    let intersect_fibs_primes = Set.intersection (fibs, primes)
    Assert.AreEqual (3, Set.count intersect_fibs_primes)

    let union_fibs_primes = Set.hedge_union (fibs, primes)
    Assert.AreEqual (10, Set.count union_fibs_primes)

    let diff_primes_fibs = Set.difference (primes, fibs)
    Assert.AreEqual (5, Set.count diff_primes_fibs)



(* Randomized tests *)

// TODO : Implement some randomized tests with QuickCheck which generate random lists,
//        create both an F# set and a BBTree from the list, convert them back to lists,
//        and compare them for equality. The tests should also perform some set-based
//        operations to make sure they work correctly.
