namespace TypeEquality

/// A type for witnessing type equality between 'a and 'b
type Teq<'a, 'b> = private Teq of ('a -> 'b) * ('b -> 'a)

/// Module for creating and using type equalities, primarily useful for Generalised Algebraic Data Types (GADTs)
/// Invariant: If you use this module (without reflection shenanigans) and the
/// code builds, it will be correct.
[<RequireQualifiedAccess>]
module Teq =

    /// The single constructor for Teq - witnesses equality between 'a and 'a
    /// It would be nice to accept any isomorphism (i.e. 1-1 mapping between
    /// values, but Refl is the only provably correct constructor we can create
    /// in F#, so we choose soundness over completeness here).
    let refl<'a> : Teq<'a,'a> = Teq (id, id)

    /// Order isn't important
    /// a = b => b = a
    /// If you always do this followed by a cast, you may as well just use castFrom
    let symmetry (Teq (ab, ba)) = Teq (ba, ab)

    /// Let's compose two type-equalities: a = b && b = c => a = c
    let transitivity (Teq (ab, ba) : Teq<'a,'b>) (Teq (bc, cb) : Teq<'b,'c>) : Teq<'a,'c> =
        // Obviously more efficient with a believeMe as below, but we like type
        // safety and this *can* be proven in the F# type system
        Teq (ab >> bc, cb >> ba)

    /// Converts an 'a to a 'b
    let cast (Teq (f, _)) a = f a

    /// Converts an 'a to a 'b
    /// Alias for cast
    let castTo teq a = cast teq a

    /// Converts a 'b to an 'a
    /// Equivalent to symmetry >> cast, but more efficient
    let castFrom (Teq (_, g)) b = g b

    /// Congruence: if x = y then f x = f y
    /// From a type-level perspective, this means, for example,
    /// iff 'a = 'b, then 'a list = 'b list.
    ///
    /// We do the munging below since we don't have type-level functions, so there
    /// is no such thing as, for example, Teq.cong List, to raise a
    /// Teq<'a,'b> to a Teq<'a list, 'b list>. Instead we must create a function for
    /// any functor (wrapping type) we might want, e.g. list, option, array.
    ///
    /// More efficient than mapping the application of the teq across the functor.
    /// i.e. Use Teq.Cong.list in preference to List.map (Teq.cast)
    ///
    /// If you need to make your own Teq.Cong.foo for your own functor 'Foo<_>', then the onus
    /// is on your to verify that doing that is sane, and to implement it yourself (since
    /// exposing the unsafe functions used internally here would make it too easy for
    /// consumers to shoot themselves in the foot).
    ///
    /// tl;dr - Lets you take a Teq in hand and safely convert it into a different Teq
    [<RequireQualifiedAccess>]
    module Cong =

        /// Clearly unsafe in general, but safe if we know 'a = 'b (which the Teq proves),
        /// and that there is some f such that f 'a = 'a2 = f 'b = 'b2, which we assume (and
        /// this assumption is why we don't make this public). Examples of valid values for
        /// f include list, array and option.
        let believeMe<'a,'b,'a2,'b2> (teq : Teq<'a,'b>) : Teq<'a2, 'b2> =
            unbox <| (refl : Teq<'a2,'a2>)

        let array<'a,'b> (prf : Teq<'a,'b>) : Teq<'a array, 'b array> =
            believeMe prf

        let list<'a,'b> (prf : Teq<'a,'b>) : Teq<'a list, 'b list> =
            believeMe prf

        let option<'a,'b> (prf : Teq<'a,'b>) : Teq<'a option, 'b option> =
            believeMe prf

        let domain<'domain1,'domain2,'range> (prf : Teq<'domain1,'domain2>) : Teq<'domain1 -> 'range, 'domain2 -> 'range> =
            believeMe prf

        let domainOf<'domain1, 'domain2, 'range1, 'range2> (prf: Teq<'domain1 -> 'range1, 'domain2 -> 'range2>) : Teq<'domain1, 'domain2> =
            believeMe prf

        let range<'domain,'range1,'range2> (prf : Teq<'range1,'range2>) : Teq<'domain -> 'range1, 'domain -> 'range2> =
            believeMe prf

        let rangeOf<'domain1, 'domain2, 'range1, 'range2> (prf: Teq<'domain1 -> 'range1, 'domain2 -> 'range2>) : Teq<'range1, 'range2> =
            believeMe prf

        let func<'domain1,'range1,'domain2,'range2> (domainPrf : Teq<'domain1,'domain2>) (rangePrf : Teq<'range1,'range2>) : Teq<'domain1 -> 'range1, 'domain2 -> 'range2> =
            transitivity
                (domain domainPrf)
                (range rangePrf)

        let fst<'fst1,'fst2,'snd> (prf : Teq<'fst1,'fst2>) : Teq<'fst1 * 'snd, 'fst2 * 'snd> =
            believeMe prf

        let snd<'snd1,'snd2,'fst> (prf : Teq<'snd1,'snd2>) : Teq<'fst * 'snd1, 'fst * 'snd2> =
            believeMe prf

        let pair<'fst1,'snd1,'fst2,'snd2> (fstPrf : Teq<'fst1,'fst2>) (sndPrf : Teq<'snd1,'snd2>) : Teq<'fst1 * 'snd1, 'fst2 * 'snd2> =
            transitivity
                (fst fstPrf)
                (snd sndPrf)
