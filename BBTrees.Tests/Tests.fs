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


//
[<RequireQualifiedAccess>]
module private Data =
    let fibs () =
        BBTree.empty
        |> BBTree.add 1
        |> BBTree.add 1
        |> BBTree.add 2
        |> BBTree.add 3
        |> BBTree.add 5
        |> BBTree.add 8

    let primes () =
        BBTree.empty
        |> BBTree.add 2
        |> BBTree.add 3
        |> BBTree.add 5
        |> BBTree.add 7
        |> BBTree.add 11
        |> BBTree.add 13
        |> BBTree.add 17
        |> BBTree.add 19


[<Test>]
let count () : unit =
    let fibs = Data.fibs ()
    Assert.AreEqual (5, BBTree.count fibs)

    let primes = Data.primes ()
    Assert.AreEqual (8, BBTree.count primes)

[<Test>]
let intersection () : unit =
    let fibs = Data.fibs ()
    let primes = Data.primes ()

    let intersect_fibs_primes = BBTree.intersection fibs primes
    Assert.AreEqual (3, BBTree.count intersect_fibs_primes)

[<Test>]
let union () : unit =
    let fibs = Data.fibs ()
    let primes = Data.primes ()

    let union_fibs_primes = BBTree.union fibs primes
    Assert.AreEqual (10, BBTree.count union_fibs_primes)

[<Test>]
let unionOld () : unit =
    let fibs = Data.fibs ()
    let primes = Data.primes ()

    let unionOld_fibs_primes = BBTree.unionOld fibs primes
    Assert.AreEqual (10, BBTree.count unionOld_fibs_primes)

[<Test>]
let difference () : unit =
    let fibs = Data.fibs ()
    let primes = Data.primes ()

    let diff_primes_fibs = BBTree.difference primes fibs
    Assert.AreEqual (5, BBTree.count diff_primes_fibs)


(* Randomized tests *)

// TODO : Implement some randomized tests with FsCheck which generate random lists,
//        create both an F# set and a BBTree from the list, convert them back to lists,
//        and compare them for equality. The tests should also perform some set-based
//        operations to make sure they work correctly.


// TODO : Re-implement this test with FsCheck so we can test many random cases
[<Test>]
let ``union and unionOld produce the same results`` () : unit =
    let fibs = Data.fibs ()
    let primes = Data.primes ()

    let union_fibs_primes = BBTree.union fibs primes
    let unionOld_fibs_primes = BBTree.unionOld fibs primes
    Assert.AreEqual (
        BBTree.toList union_fibs_primes,
        BBTree.toList unionOld_fibs_primes)

