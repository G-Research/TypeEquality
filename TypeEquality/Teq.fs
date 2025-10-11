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
    let refl<'a> : Teq<'a, 'a> = Teq (id, id)

    /// Returns a Teq when the two type parameters have the same value,
    /// otherwise returns None.
    let tryRefl<'a, 'b> : Teq<'a, 'b> option =
        if typeof<'a> = typeof<'b> then
            refl<'a> |> unbox |> Some
        else
            None

    /// Order isn't important
    /// a = b => b = a
    /// If you always do this followed by a cast, you may as well just use castFrom
    let symmetry (Teq (ab, ba)) = Teq (ba, ab)

    /// Let's compose two type-equalities: a = b && b = c => a = c
    let transitivity (Teq (ab, ba) : Teq<'a, 'b>) (Teq (bc, cb) : Teq<'b, 'c>) : Teq<'a, 'c> =
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

    /// Utility function to map an object of one type using a mapping function
    /// for a different type when we have a type equality between the two types
    let mapAs (Teq (f, g)) h a = a |> f |> h |> g

    /// The Cong module (short for congruence) contains functions that
    /// allow you safely transform Teqs into other Teqs that logically follow.
    ///
    /// Congruence: if x = y then f x = f y
    /// From a type-level perspective, this means, for example,
    /// iff 'a = 'b, then 'a list = 'b list.
    ///
    /// We do the munging below since we don't have type-level functions, so there
    /// is no such thing as, for example, Teq.cong List, to raise a
    /// Teq<'a, 'b> to a Teq<'a list, 'b list>. Instead we must create a function for
    /// any functor (wrapping type) we might want, e.g. list, option, array.
    ///
    /// More efficient than mapping the application of the teq across the functor.
    /// i.e. Use Teq.Cong.list in preference to List.map (Teq.cast)
    ///
    /// If you need to make your own Teq.Cong.foo for your own functor 'Foo<_>' using believeMe,
    /// then the onus is on you to verify that doing that is sane.
    [<RequireQualifiedAccess>]
    module Cong =

        /// Clearly unsafe in general, but safe if we know 'a = 'b (which the Teq proves),
        /// and that there is some f such that f 'a = 'a2 = f 'b = 'b2, which we assume (and
        /// this assumption is why we don't make this public). Examples of valid values for
        /// f include list, array and option.
        let believeMe<'a, 'b, 'a2, 'b2> (teq : Teq<'a, 'b>) : Teq<'a2, 'b2> =
            unbox <| (refl : Teq<'a2, 'a2>)

        /// Given a type equality between two types, returns the type equality on the corresponding array types.
        let array<'a, 'b> (prf : Teq<'a, 'b>) : Teq<'a array, 'b array> =
            believeMe prf

        /// Given a type equality between two array types, returns the type equality on the corresponding element types.
        let arrayOf<'a, 'b> (prf : Teq<'a array, 'b array>) : Teq<'a, 'b> =
            believeMe prf

        /// Given a type equality between two types, returns the type equality on the corresponding list types.
        let list<'a, 'b> (prf : Teq<'a, 'b>) : Teq<'a list, 'b list> =
            believeMe prf

        /// Given a type equality between two list types, returns the type equality on the corresponding element types.
        let listOf<'a, 'b> (prf : Teq<'a list, 'b list>) : Teq<'a, 'b> =
            believeMe prf

        /// Given a type equality between two types, returns the type equality on the corresponding set types.
        let set<'a, 'b when 'a : comparison and 'b : comparison> (prf : Teq<'a, 'b>) : Teq<Set<'a>, Set<'b>> =
            believeMe prf

        /// Given a type equality between two set types, returns the type equality on the corresponding element types.
        let setOf<'a, 'b when 'a : comparison and 'b : comparison> (prf : Teq<Set<'a>, Set<'b>>) : Teq<'a, 'b> =
            believeMe prf

        /// Given a type equality between two types, returns the type equality on the corresponding seq types.
        let seq<'a, 'b> (prf : Teq<'a, 'b>) : Teq<'a seq, 'b seq> =
            believeMe prf

        /// Given a type equality between two seq types, returns the type equality on the corresponding element types.
        let seqOf<'a, 'b> (prf : Teq<'a seq, 'b seq>) : Teq<'a, 'b> =
            believeMe prf

        /// Given a type equality between two types 'k1 and 'k2, returns the type equality
        /// on the types Map<'k1, 'v> and Map<'k2, 'v>), for any arbitrary 'v.
        let mapKey<'k1, 'k2, 'v when 'k1 : comparison and 'k2 : comparison> (prf : Teq<'k1, 'k2>) : Teq<Map<'k1, 'v>, Map<'k2, 'v>> =
            believeMe prf

        /// Given a type equality between two types 'v1 and 'v2, returns the type equality
        /// on the types Map<'k, 'v1> and Map<'k, 'v2>), for any arbitrary 'k.
        let mapValue<'v1, 'v2, 'k when 'k : comparison> (prf : Teq<'v1, 'v2>) : Teq<Map<'k, 'v1>, Map<'k, 'v2>> =
            believeMe prf

        /// Given a pair of type equalities, one for the keys of a Map and one for the values of a Map,
        /// returns the type equality for the corresponding Map type.
        let map<'k1, 'v1, 'k2, 'v2 when 'k1 : comparison and 'k2 : comparison> (keyPrf : Teq<'k1, 'k2>) (valuePrf : Teq<'v1, 'v2>) : Teq<Map<'k1, 'v1>, Map<'k2, 'v2>> =
            transitivity
                (key keyPrf)
                (value valuePrf)

        /// Given a type equality between two types 'ok1 and 'ok2, returns the type equality
        /// on the types Result<'ok1, 'error> and Result<'ok2, 'error>), for any arbitrary 'error.
        let resultOk<'ok1, 'ok2, 'error> (prf : Teq<'ok1, 'ok2>) : Teq<Result<'ok1, 'error>, Result<'ok2, 'error>> =
            believeMe prf

        /// Given a type equality between two types 'error1 and 'error2, returns the type equality
        /// on the types Result<'ok, 'error1> and Result<'ok, 'error2>), for any arbitrary 'ok.
        let error<'error1, 'error2, 'ok> (prf : Teq<'error1, 'error2>) : Teq<Result<'ok, 'error1>, Result<'ok, 'error2>> =
            believeMe prf

        /// Given a pair of type equalities, one for the Ok element of a pair and one for the Error element of a pair,
        /// returns the type equality for the corresponding Result type.
        let result<'ok1, 'error1, 'ok2, 'error2> (okPrf : Teq<'ok1, 'ok2>) (errorPrf : Teq<'error1, 'error2>) : Teq<Result<'ok1, 'error1>, Result<'ok2, 'error2>> =
            transitivity
                (ok okPrf)
                (error errorPrf)

        /// Given a type equality between two types, returns the type equality on the corresponding option types.
        let option<'a, 'b> (prf : Teq<'a, 'b>) : Teq<'a option, 'b option> =
            believeMe prf

        /// Given a type equality between two option types, returns the type equality on the corresponding element types.
        let optionOf<'a, 'b> (prf : Teq<'a option, 'b option>) : Teq<'a, 'b> =
            believeMe prf

        /// Given a type equality between two types 'domain1 and 'domain2, returns the type equality
        /// on the function types ('domain1 -> 'range) and ('domain2 -> 'range), for any arbitrary 'range.
        let domain<'domain1, 'domain2, 'range> (prf : Teq<'domain1, 'domain2>) : Teq<'domain1 -> 'range, 'domain2 -> 'range> =
            believeMe prf

        /// Given a type equality between two function types, returns the type equality on their corresponding domains.
        let domainOf<'domain1, 'domain2, 'range1, 'range2> (prf: Teq<'domain1 -> 'range1, 'domain2 -> 'range2>) : Teq<'domain1, 'domain2> =
            believeMe prf

        /// Given a type equality between two types 'range1 and 'range2, returns the type equality
        /// on the function types ('domain -> 'range1) and ('domain -> 'range2), for any arbitrary 'domain.
        let range<'domain, 'range1, 'range2> (prf : Teq<'range1, 'range2>) : Teq<'domain -> 'range1, 'domain -> 'range2> =
            believeMe prf

        /// Given a type equality between two function types, returns the type equality on their corresponding ranges.
        let rangeOf<'domain1, 'domain2, 'range1, 'range2> (prf: Teq<'domain1 -> 'range1, 'domain2 -> 'range2>) : Teq<'range1, 'range2> =
            believeMe prf

        /// Given a pair of type equalities, one for domains and one for ranges, returns the type equality for the corresponding function types.
        let func<'domain1, 'range1, 'domain2, 'range2> (domainPrf : Teq<'domain1, 'domain2>) (rangePrf : Teq<'range1, 'range2>) : Teq<'domain1 -> 'range1, 'domain2 -> 'range2> =
            transitivity
                (domain domainPrf)
                (range rangePrf)

        /// Given a type equality between two types 'fst1 and 'fst2, returns the type equality
        /// on the pair types ('fst1 * 'snd) and ('fst2 * 'snd), for any arbitrary 'snd.
        let fst<'fst1, 'fst2, 'snd> (prf : Teq<'fst1, 'fst2>) : Teq<'fst1 * 'snd, 'fst2 * 'snd> =
            believeMe prf

        /// Given a type equality between two types 'snd1 and 'snd2, returns the type equality
        /// on the pair types ('fst * 'snd1) and ('fst * 'snd2), for any arbitrary 'fst.
        let snd<'snd1, 'snd2, 'fst> (prf : Teq<'snd1, 'snd2>) : Teq<'fst * 'snd1, 'fst * 'snd2> =
            believeMe prf

        /// Given a pair of type equalities, one for the first element of a pair and one for the second element of a pair,
        /// returns the type equality for the corresponding pair types.
        let pair<'fst1, 'snd1, 'fst2, 'snd2> (fstPrf : Teq<'fst1, 'fst2>) (sndPrf : Teq<'snd1, 'snd2>) : Teq<'fst1 * 'snd1, 'fst2 * 'snd2> =
            transitivity
                (fst fstPrf)
                (snd sndPrf)

        /// Given a type equality between two types, returns the type equality on the corresponding Async types.
        let async<'a, 'b> (prf : Teq<'a, 'b>) : Teq<Async<'a>, Async<'b>> =
            believeMe prf

        /// Given a type equality between two Async types, returns the type equality on the corresponding return types.
        let asyncOf<'a, 'b> (prf : Teq<Async<'a>, Async<'b>>) : Teq<'a, 'b> =
            believeMe prf
