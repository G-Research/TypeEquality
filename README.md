# TypeEquality

[![NuGet latest release](https://badgen.net/nuget/v/TypeEquality)](https://www.nuget.org/packages/TypeEquality)
[![NuGet latest pre-release](https://badgen.net/nuget/v/TypeEquality/pre)](https://www.nuget.org/packages/TypeEquality)
[![Build status](https://ci.appveyor.com/api/projects/status/xk2mp8igycy4avxd?svg=true)](https://ci.appveyor.com/project/G-Research/typeequality)

## Type equalities for F#

This library contains type equalities (Teqs) for F#.  These equalities
allow us to create type-safe abstractions by allowing us to encode
Generalised Algebraic Data Types (GADTs), as found in languages like
Haskell.

Ralf Hinze explains the concepts of GADTs and phantom types in
[_Fun with phantom types_](https://www.cs.ox.ac.uk/ralf.hinze/publications/With.pdf).
In particular, _Section 7, "A type equality type"_, covers the role of a type
equality in the encoding of GADTs.

## Usage

To use Teqs in your projects, you'll want to reference the main TypeEquality
project.  The project is available as a nuget package - https://www.nuget.org/packages/TypeEquality.  
This project provides a type `Teq<'a,'b>` of proofs that `'a`
and `'b` are the same type. By including these in the declaration of a
generic discriminated union, you can constrain the types each case
applies to, encoding a GADT.
An example of this may be found in the Example folder.

For more advanced usage, TypeEquality also allows you to reason about Teqs
using the functions in the Teq and Teq.Cong (congruence) modules.

The library has some unit tests in the Test/TypeEquality.Test.fsproj project.

## Contributing

We welcome new contributors! We'll happily receive PRs for bug fixes
or small changes. If you're contemplating something larger please get
in touch first by opening a GitHub Issue describing the problem and
how you propose to solve it.

## License

Copyright 2018 G-Research

Licensed under the Apache License, Version 2.0 (the "License"); you may not use these files except in compliance with the License.
You may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
