namespace Teq.Test

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
