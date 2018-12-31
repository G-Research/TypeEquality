namespace TypeEquality

/// A type for witnessing type equality between 'a and 'b
type Teq<'a, 'b>

/// Module for creating and using type equalities, primarily useful for Generalised Algebraic Data Types (GADTs)
/// Invariant: If you use this module (without reflection shenanigans) and the
/// code builds, it will be correct.
[<RequireQualifiedAccess>]
module Teq =

    /// The single constructor for Teq - witnesses equality between 'a and 'a
    /// It would be nice to accept any isomorphism (i.e. 1-1 mapping between
    /// values, but Refl is the only provably correct constructor we can create
    /// in F#, so we choose soundness over completeness here).
    val refl<'a> : Teq<'a,'a>

    /// Returns a Teq when the two type parameters have the same value,
    /// otherwise returns None.
    val tryRefl<'a, 'b> : Teq<'a,'b> option

    /// Order isn't important
    /// a = b => b = a
    /// If you always do this followed by a cast, you may as well just use castFrom
    val symmetry : Teq<'a, 'b> -> Teq<'b, 'a>

    /// Let's compose two type-equalities: a = b && b = c => a = c
    val transitivity : Teq<'a,'b> -> Teq<'b,'c> -> Teq<'a,'c>

    ///// Converts an 'a to a 'b
    val cast : Teq<'a, 'b> -> ('a -> 'b)

    ///// Converts an 'a to a 'b
    ///// Alias for cast
    val castTo : Teq<'a, 'b> -> ('a -> 'b)

    ///// Converts a 'b to an 'a
    ///// Equivalent to symmetry >> cast, but more efficient
    val castFrom : Teq<'a, 'b> -> ('b -> 'a)

    ///// Congruence: if x = y then f x = f y
    ///// From a type-level perspective, this means, for example,
    ///// iff 'a = 'b, then 'a list = 'b list.
    /////
    ///// We do the munging below since we don't have type-level functions, so there
    ///// is no such thing as, for example, Teq.cong List, to raise a
    ///// Teq<'a,'b> to a Teq<'a list, 'b list>. Instead we must create a function for
    ///// any functor (wrapping type) we might want, e.g. list, option, array.
    /////
    ///// More efficient than mapping the application of the teq across the functor.
    ///// i.e. Use Teq.Cong.list in preference to List.map (Teq.cast)
    /////
    ///// If you need to make your own Teq.Cong.foo for your own functor 'Foo<_>', then the onus
    ///// is on your to verify that doing that is sane, and to implement it yourself (since
    ///// exposing the unsafe functions used internally here would make it too easy for
    ///// consumers to shoot themselves in the foot).
    /////
    ///// tl;dr - Lets you take a Teq in hand and safely convert it into a different Teq
    [<RequireQualifiedAccess>]
    module Cong =

        /// Clearly unsafe in general, but safe if we know 'a = 'b (which the Teq proves),
        /// and that there is some f such that f 'a = 'a2 = f 'b = 'b2, which we assume (and
        /// this assumption is why we don't make this public). Examples of valid values for
        /// f include list, array and option.
        val believeMe<'a,'b,'a2,'b2> : Teq<'a, 'b> -> Teq<'a2, 'b2>

        val array<'a,'b> : Teq<'a,'b> -> Teq<'a array, 'b array>

        val list<'a,'b> : Teq<'a,'b> -> Teq<'a list, 'b list>

        val option<'a,'b> : Teq<'a,'b> -> Teq<'a option, 'b option>

        val domain<'domain1,'domain2,'range> : Teq<'domain1,'domain2> -> Teq<'domain1 -> 'range, 'domain2 -> 'range>

        val domainOf<'domain1, 'domain2, 'range1, 'range2> : Teq<'domain1 -> 'range1, 'domain2 -> 'range2> -> Teq<'domain1, 'domain2>

        val range<'domain,'range1,'range2> : Teq<'range1,'range2> -> Teq<'domain -> 'range1, 'domain -> 'range2>

        val rangeOf<'domain1, 'domain2, 'range1, 'range2> : Teq<'domain1 -> 'range1, 'domain2 -> 'range2> -> Teq<'range1, 'range2>

        val func<'domain1,'range1,'domain2,'range2> : Teq<'domain1,'domain2> -> Teq<'range1,'range2> -> Teq<'domain1 -> 'range1, 'domain2 -> 'range2>

        val fst<'fst1,'fst2,'snd> : Teq<'fst1,'fst2> -> Teq<'fst1 * 'snd, 'fst2 * 'snd>

        val snd<'snd1,'snd2,'fst> : Teq<'snd1,'snd2> -> Teq<'fst * 'snd1, 'fst * 'snd2>

        val pair<'fst1,'snd1,'fst2,'snd2> : Teq<'fst1,'fst2> -> Teq<'snd1,'snd2> -> Teq<'fst1 * 'snd1, 'fst2 * 'snd2>
