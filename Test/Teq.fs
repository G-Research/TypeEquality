namespace TypeEquality.Test

open TypeEquality

open NUnit.Framework
open FsUnitTyped

[<TestFixture>]
module TestTeq =

    [<Test>]
    let ``Casting with Teq.refl is id`` () =
        let value = 42
        let t = Teq.refl
        Teq.cast t value
        |> shouldEqual value
        Teq.castFrom t value
        |> shouldEqual value

    [<Test>]
    let ``Cong.list does not throw`` () =
        let t : Teq<int,int> = Teq.refl
        Assert.DoesNotThrow(fun () -> Teq.Cong.list t |> ignore)

    [<Test>]
    let ``Teq.tryRefl returns a Teq when the types match`` () =
        let t = Teq.tryRefl<int, int>
        t |> Option.isSome |> shouldEqual true

    [<Test>]
    let ``Teq.tryRefl returns None when the types differ`` () =
        let t = Teq.tryRefl<int, string>
        t |> Option.isSome |> shouldEqual false
