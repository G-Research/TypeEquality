namespace TypeEquality.Example

open TypeEquality

// We define a GADT by defining a generic type.
// In each DU case where we want to further constrain the generic argument 'a,
// we use a Teq to do so.
type Expr<'a> =
| Const of Teq<int,'a> * int
| Add of Teq<int,'a> * Expr<int> * Expr<int>
| IsZero of Teq<bool,'a> * Expr<int>
| If of Expr<bool> * Expr<'a> * Expr<'a>

// As creating GADTs directly involves lots of uses of Teq.refl,
// we create a module of easy-to-use constructor functions.
module Expr =
    let constant (i : int) : Expr<int> =
        Const (Teq.refl, i)

    let add (l : Expr<int>) (r : Expr<int>) : Expr<int> =
        Add (Teq.refl, l, r)

    let isZero (a : Expr<int>) =
        IsZero (Teq.refl, a)

    let ifExpr (condition : Expr<bool>) (t : Expr<'a>) (e : Expr<'a>) : Expr<'a> =
        If(condition, t, e)

    // Recursive evaluation of expressions.
    let rec eval<'a> (e : Expr<'a>) : 'a =
        match e with
        | Const (teq, x) ->
            // The Teq shows that int and 'a are the same type.
            // We have an int, so we use Teq.cast with the teq
            // to treat it as an 'a and return it.
            Teq.cast teq x
        | Add (teq, l, r) ->
            // Evaluate the arguments recursively to get two ints,
            // then add them.
            // To return this as an 'a, use Teq.cast.
            eval l + eval r
            |> Teq.cast teq
        | IsZero (teq, x) ->
            // Evaluating x gives us an int, comparing it to zero gives us
            // the bool we want.
            // Return it with Teq.cast as before.
            eval x = 0
            |> Teq.cast teq
        | If(cond, t, e) ->
            if eval cond then
                eval t
            else
                eval e

module ExampleExprs =

    // This will not compile, as Const is an Expr<int>:
    // let bad : Expr<bool> = Expr.constant 1

    // A valid expression:
    let valid = Expr.add (Expr.constant 1) (Expr.constant 1)
