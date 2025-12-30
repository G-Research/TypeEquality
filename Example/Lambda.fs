namespace TypeEquality.Example

(*

This example demonstrates Simply Typed Lambda Calculus (STLC) modeled using Higher-Order Abstract Syntax (HOAS).

Typically this requires GADTs, but we can use `Teq` objects to approximate!

The design is based on https://en.wikipedia.org/wiki/Generalized_algebraic_data_type#Higher-order_abstract_syntax

  Lift :: a                     -> Lam a        -- ^ lifted value
  Pair :: Lam a -> Lam b        -> Lam (a, b)   -- ^ product
  Lam  :: (Lam a -> Lam b)      -> Lam (a -> b) -- ^ lambda abstraction
  App  :: Lam (a -> b) -> Lam a -> Lam b        -- ^ function application
  Fix  :: Lam (a -> a)          -> Lam a        -- ^ fixed point

One difference in the implementation is that `Fix` must be a function of functions, since we have strict evaluation in F#:

  Fix  :: Lam ((a -> b) -> (a -> b))                -> Lam (a -> b)    -- ^ fixed point

And we also add `IfThenElse` in order to demonstrate factorial:

  IfThenElse  :: Lam bool -> Lam a -> Lam a         -> Lam a           -- ^ conditional operator

*)

open TypeEquality

(*

Here we define the type of the lambda calculus expressions, mirroring the above.

Note that in each case where the LHS introduces a new type variable, we must reach for a Crate.
See https://www.patrickstevens.co.uk/posts/2021-10-19-crates/

*)

type Lam<'a> =
    | Lift of 'a
    | Pair of LamPairCrate<'a>
    | Abstraction of LamAbstractionCrate<'a>
    | Application of LamApplicationCrate<'a>
    | Fix of LamFixCrate<'a>
    | IfThenElse of condition : Lam<bool> * consequent : Lam<'a> * alternative : Lam<'a>

and LamPairEvaluator<'a, 'ret> =
    abstract Eval<'i, 'j> : Lam<'i> * Lam<'j> * Teq<'i * 'j, 'a> -> 'ret

and LamPairCrate<'a> =
    abstract Apply<'ret> : LamPairEvaluator<'a, 'ret> -> 'ret

and LamAbstractionEvaluator<'a, 'ret> =
    abstract Eval<'i, 'j> : (Lam<'i> -> Lam<'j>) * Teq<'i -> 'j, 'a> -> 'ret

and LamAbstractionCrate<'a> =
    abstract Apply<'ret> : LamAbstractionEvaluator<'a, 'ret> -> 'ret

and LamApplicationEvaluator<'a, 'ret> =
    abstract Eval<'i, 'j> : Lam<'i -> 'j> * Lam<'i> * Teq<'j, 'a> -> 'ret

and LamApplicationCrate<'a> =
    abstract Apply<'ret> : LamApplicationEvaluator<'a, 'ret> -> 'ret

and LamFixEvaluator<'a, 'ret> =
    abstract Eval<'i, 'j> : Lam<('i -> 'j) -> ('i -> 'j)> * Teq<'i -> 'j, 'a> -> 'ret

and LamFixCrate<'a> =
    abstract Apply<'ret> : LamFixEvaluator<'a, 'ret> -> 'ret

(* Since constructing `Lam` objects is quite involved, we provide simple functions that are guaranteed to be well-formed *)

[<RequireQualifiedAccess>]
module Lam =

    /// Takes a value and raises it into a `Lam`
    let lift (a : 'a) : Lam<'a> =
        Lift a

    /// Given two `Lam` objects, creates on `Lam` representing them as a tuple
    let pair (x : Lam<'a>) (y : Lam<'b>) : Lam<'a * 'b> =
        let teq = Teq.Cong.pair Teq.refl Teq.refl
        Pair
            {
                new LamPairCrate<'a * 'b> with
                    member this.Apply<'ret>(e : LamPairEvaluator<'a * 'b, 'ret>) =
                        e.Eval(x, y, teq)
            }

    /// Given a function with domain and range in `Lam`, creates a single `Lam` representing this function in the calculus
    let abstraction (f : Lam<'a> -> Lam<'b>) : Lam<'a -> 'b> =
        let teq = Teq.Cong.func Teq.refl Teq.refl
        Abstraction
            {
                new LamAbstractionCrate<'a -> 'b> with
                    member this.Apply<'ret>(e : LamAbstractionEvaluator<'a -> 'b, 'ret>) =
                        e.Eval(f, teq)
            }

    /// Given a function and value in `Lam`, returns a `Lam` representing the application of the function to the value
    let application (f : Lam<'a -> 'b>) (x : Lam<'a>) : Lam<'b> =
        let teq = Teq.refl
        Application
            {
                new LamApplicationCrate<'b> with
                    member this.Apply<'ret>(e : LamApplicationEvaluator<'b, 'ret>) =
                        e.Eval(f, x, teq)
            }

    /// Given a function in `Lam` that expects a reference to itself, returns a new function that is recursive
    /// See https://en.wikipedia.org/wiki/Fixed-point_combinator
    let fix (f : Lam<('a -> 'b) -> ('a -> 'b)>) : Lam<'a -> 'b> =
        let teq = Teq.refl
        Fix
            {
                new LamFixCrate<'a -> 'b> with
                    member this.Apply(e : LamFixEvaluator<'a -> 'b, 'ret>) : 'ret =
                        e.Eval(f, teq)
            }

    /// A conditional that evaluates to `consequent` when `condition` evaluates `true` and `alternative` otherwise
    let ifThenElse (condition : Lam<bool>) (consequent : Lam<'a>) (alternative : Lam<'a>) : Lam<'a> =
        IfThenElse (condition, consequent, alternative)

    /// Fixed point helper
    let rec private fix' (f : ('a -> 'b) -> ('a -> 'b)) : 'a -> 'b =
        let z x = f (fix' f) x
        z

    /// Evaluates a `Lam` to its resulting value
    let rec eval<'a> (x : Lam<'a>) : 'a =
        match x with
        | Lift a -> a

        | Pair crate ->
            crate.Apply
                {
                    new LamPairEvaluator<'a, _> with
                        member this.Eval<'i, 'j>(x : Lam<'i>, y : Lam<'j>, teq : Teq<'i * 'j, 'a>) =
                            let i = eval x
                            let j = eval y
                            Teq.cast teq (i, j)
                }

        | Abstraction crate ->
            crate.Apply
                {
                    new LamAbstractionEvaluator<'a, _> with
                        member this.Eval<'i, 'j>(f : Lam<'i> -> Lam<'j>, teq : Teq<'i -> 'j, 'a>) =
                            let g = fun i -> eval (f (lift i))
                            Teq.cast teq g
                }

        | Application crate ->
            crate.Apply
              {
                  new LamApplicationEvaluator<'a, _> with
                      member this.Eval<'i, 'j>(f : Lam<'i -> 'j>, x : Lam<'i>, teq : Teq<'j, 'a>) =
                          let j = eval f (eval x )
                          Teq.cast teq j
              }

        | Fix crate ->
            crate.Apply
              {
                  new LamFixEvaluator<_, _> with
                      member this.Eval (lamF : Lam<('i -> 'j) -> ('i -> 'j)>, teq : Teq<'i -> 'j, 'a>)=
                          let f = eval lamF
                          let g = fix' f

                          Teq.cast teq g
              }

        | IfThenElse (condition, consequent, alternative) ->
            if eval condition then
                eval consequent
            else
                eval alternative

// Tests

open NUnit.Framework
open FsUnitTyped

[<TestFixture>]
module TestLam =

    let infix f x y =
        Lam.application (Lam.application (Lam.lift f) x) y

    let ( +. ) (x : Lam<int>) (y : Lam<int>) : Lam<int> =
        infix ( + ) x y

    let ( -. ) (x : Lam<int>) (y : Lam<int>) : Lam<int> =
        infix ( - ) x y

    let ( *. ) (x : Lam<int>) (y : Lam<int>) : Lam<int> =
        infix ( * ) x y

    let isLessThanEqualToZero (x : Lam<int>) : Lam<bool> =
        Lam.application (Lam.lift (fun x -> x <= 0)) x

    [<Test>]
    let ``Lam.eval works for Lam.lift`` () =
        let x = Lam.lift 123

        Lam.eval x
        |> shouldEqual 123

    [<Test>]
    let ``Lam.eval works for Lam.pair`` () =
        let x = Lam.pair (Lam.lift "abc") (Lam.lift true)

        Lam.eval x
        |> shouldEqual ("abc", true)

    [<Test>]
    let ``Lam.eval works for Lam.application and Lam.abstraction 1`` () =
        let addOne = Lam.abstraction (fun x -> x +. Lam.lift 1)
        let x = Lam.application addOne (Lam.lift 123)

        Lam.eval x
        |> shouldEqual 124

    [<Test>]
    let ``Lam.eval works for Lam.application and Lam.abstraction 2`` () =
        let x = Lam.lift 7 -. Lam.lift 3

        Lam.eval x
        |> shouldEqual 4

    [<Test>]
    let ``Lam.eval works for Lam.fix 1`` () =
        let f : Lam<(int -> int) -> (int -> int)> =
            Lam.abstraction
                (fun _ -> Lam.lift (fun _ -> 42))

        let g = Lam.fix f

        Lam.application g (Lam.lift 5)
        |> Lam.eval
        |> shouldEqual 42

    [<Test>]
    let ``Lam.eval works for Lam.fix 2`` () =
        let factGen =
            Lam.abstraction
                (fun f ->
                    Lam.abstraction
                        (fun n ->
                            Lam.ifThenElse
                                (isLessThanEqualToZero n)
                                (Lam.lift 1)
                                (n *. Lam.application f (n -. Lam.lift 1))))

        let fact = Lam.fix factGen

        Lam.application fact (Lam.lift 5)
        |> Lam.eval
        |> shouldEqual 120
