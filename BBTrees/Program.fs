module BBTrees.Program

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

assert (Set.cardinality fibs = 5)
assert (Set.cardinality primes = 8)

let intersect_fibs_primes =
    Set.intersection (fibs, primes)

assert (Set.cardinality intersect_fibs_primes = 3)

let union_fibs_primes =
    Set.hedge_union (fibs, primes)

assert (Set.cardinality union_fibs_primes = 10)

let diff_primes_fibs =
    Set.difference (primes, fibs)

assert (Set.cardinality diff_primes_fibs = 5)





printfn "Press any key to exit..."
System.Console.ReadKey () |> ignore
