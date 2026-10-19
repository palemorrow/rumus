                                 _ __ _   _ _ __ ___  _   _ ___
                                | '__| | | | '_ ` _ \| | | / __|
                                | |  | |_| | | | | | | |_| \__ \
                                |_|   \__,_|_| |_| |_|\__,_|___/

        rumus is a regular expression engine written in agda that uses brzozowski
        derivatives [1] to decide membership and language equivalence. its decisions
        carry either the required proof or a refutation, with inequivalence represented
        by a string and evidence that exactly one expression accepts it

                                           matching:

          membership is an inductive relation whose constructors record the branch
          chosen in a union, the split used by concatenation, and the factors consumed
          by kleene iteration. consuming a symbol a computes the residual d/a r,
          whose semantics are characterized by an equivalence between membership
          propositions in the source and residual languages:

                                x in l(d/a r)  <=>  a::x in l(r)

           the matcher recurses on the input list and uses the two directions of this
           theorem to transport the final nullability decision back to the original
           expression. the boolean interface projects the tag of that decision, while
           the membership interface retains the proof or refutation shown below:

                                        match r x
                                            |
                                   decision (x in l(r))
                                            |
                               +------------+-------------+
                               |                          |
                           yes proof                  no refute
                               |                          |
                        proof of x in l(r)     (x in l(r)) -> empty type
                               |                          |
                              true                       false

           normalization flattens unions into sorted lists of distinct syntactic
           alternatives and applies language-preserving reductions for empty unions,
           empty products, epsilon factors, and nested stars. these preservation
           proofs compose with derivative correctness, allowing each residual to be
           normalized before the next symbol is consumed.

           the command ./build/rumus trace '(a|b)*abb' 'aabb' produces the residuals
           below, including the identical expressions reached after the two a steps:

                                   (a|b)*abb         input aabb
                                        |
                                       d/a
                                        v
                                (@|(a|b)*a)bb        input abb
                                        |
                                       d/a
                                        v
                                (@|(a|b)*a)bb        input bb
                                        |
                                       d/b
                                        v
                                (@|(a|b)*ab)b        input b
                                        |
                                       d/b
                                        v
                                 @|(a|b)*abb         input empty
                                        |
                                     nullable
                                        v
                                       true

                                          equivalence:

            partial derivative residuals [2] are indexed by literal occurrences,
            giving each expression a fixed basis containing every transition target.
            a deterministic state is either the initial expression or a take/skip
            selection over that basis, giving an enumeration of 1 + 2^k states for
            k literal occurrences

           r --> residuals --> subsets + initial --> qr --+
                                                        +--> qr x qs --> worklist
           s --> residuals --> subsets + initial --> qs --+                    |
                                                                             v
                                                                     proof or witness

          the checker traverses reachable pairs in breadth-first layers, retaining
          input paths and their lengths for each queued state. the history invariant
          records that every shorter input reaches states with equal nullability,
          so a mismatch supplies both a witness and a proof of minimal length

          termination follows from well-founded induction on the finite set of
          unvisited pairs. this set and its accessibility proof are erased by the
          compiler, so execution constructs only reached states and their outgoing
          transitions. exhausting the queue establishes a closed bisimulation whose
          correctness follows by induction on the remaining input

             for a*b and ab* the successor languages after b normalize to @ and #,
             so the empty string distinguishes that successor pair and prefixing b
             gives the counterexample returned for the initial pair:

                               a*b                           ab*
                                |                             |
                               d/b                           d/b
                                v                             v
                                @                             #
                                |                             |
                         nullable = true               nullable = false
                                |                             |
                                +--------------+--------------+
                                               |
                                          witness []
                                               |
                                           prefix b
                                               v
                                          witness [b]

           the powerset enumeration bounds the proof of termination without being
           evaluated by the executable, although the reachable machine can still
           have exponentially many states. only literals appearing in either source
           expression are explored and the support theorem places every symbol of
           an accepted string in that alphabet, extending equivalence to all strings

              generic matching and equivalence require decidable symbol equality,
              while normalization additionally takes an injective natural-number
              encoding to order the syntactic alternatives within unions

                                             build:

         the pinned toolchain consists of agda 2.8.0, standard library 2.3, ghc 9.6.7,
         and cabal-install 3.12.1.0, with make, curl, sha256sum, tar, and python 3.9
         or later also required. the compiler installation command is recorded in
         .github/actions/setup-agda/action.yml, which also installs them for ci

                                           make deps
                                           make test

          make deps downloads the standard library and checks its pinned sha-256,
          while make test type-checks the library and examples, compiles build/rumus,
          and runs the regressions. the tests compare matching against independent
          finite-language enumeration and check parser errors, normalization,
          equivalence and the validity of generated witnesses

            ci runs these checks on pushes, pull requests, and a weekly schedule,
            with separate workflows validating action definitions and source syntax.
            tagged and manual package builds run the same tests before uploading a
            linux executable archive and its sha-256 checksum as workflow artifacts

                                            library:

           the character api exposes decidable membership, boolean matching,
           normalization and equivalence with proofs or distinguishing strings
           while the generic modules separate semantics, derivatives, normalization,
           position automata and relation refinement. semantic modules use safe mode
           without the k axiom or project postulates with the language correspondence
           theorems applying to the expression returned by the parser. parsing has
           executable regressions and terminal io uses the standard library bindings

                                          references:

           [1] j. a. brzozowski, derivatives of regular expressions, 1964.
               https://doi.org/10.1145/321239.321249
           [2] v. m. antimirov, partial derivatives of regular expressions and finite
               automaton constructions, 1996.
               https://doi.org/10.1016/0304-3975(95)00182-4
