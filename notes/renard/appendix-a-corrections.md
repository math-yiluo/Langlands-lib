# Renard 2026 Appendix A: three source discrepancies and reuse routes

Author: Worker 6. Source audit dated 25 October 2026.

This note records three discrepancies in the French 9 July 2026 edition and the focused tasks that address them. It supplies mathematical counterexamples and source correspondence, not accepted Lean statements or proofs. Task publication, inspected Mathlib source and this documentation each have a different status from independent mathematical acceptance. The whole-book coverage ledger remains [coverage.md](coverage.md); the present note does not close Appendix A or change the parent program's scope.

## Sources and reading boundary

The governing source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, 296 PDF pages. Registered ID: `renard-2026-representations-groupes-reductifs-padiques`; SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The retained original is `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`. Printed body pages equal PDF page numbers minus six.

The findings below use original PDF258, PDF262–263 and PDF267–268, read in full. PDF258, PDF262, PDF263 and PDF267 were also visually inspected to check the disputed wording and arrows. PDF257 was read for the full-subcategory convention. These are selected passage audits, not a claim of complete Appendix A coverage.

The registered author errata `renard-2010-corrections-complements`, SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, are retained at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`. Its appendix corrections on PDF18–19 were read. They do not correct the three discrepancies below. This is a limited observation about that portion of the 2010 errata, not an exhaustive errata claim or a replacement reference edition.

## A.III.1 example 4: inverse endomorphisms need not be scalar inverses

At printed252/PDF258, the main definition requires every element of a multiplicative subset S of a commutative unital ring A to act invertibly on a unital A-module M. The parenthesis identifies this with the assertion that for every s in S and m in M there is t in A with `(ts) m = (st) m = m`. The parenthetical condition is stronger and is not equivalent to invertibility of the scalar endomorphism.

Take A = integers, S = the powers of 2, and M = rationals with its usual integer-module structure. Multiplication by each `2^n` is an invertible integer-linear endomorphism; multiplication by the rational `1/2^n` is its inverse. But for s = 2 and m = 1 no integer t satisfies `(2t) · 1 = 1`. The inverse endomorphism need not come from an element of A. Conversely, the parenthetical condition implies surjectivity because m is the image of t m under multiplication by s, and injectivity because `s m = 0` together with `t(s m) = m` forces m = 0.

Use endomorphism invertibility as the S-local predicate. The ordinary localized module and its universal property remain the correct construction. The task must preserve the zero-in-S case, arbitrary commutative unital rings, nonfaithful and non-finitely-generated modules, and independent ring/source/target universes.

The inspected Mathlib source `Algebra/Module/LocalizedModule/Basic.lean` supplies the actual `LocalizedModule S M`, `LocalizedModule.mkLinearMap`, inverse action via `divBy`, and `lift`, `lift_comp`, `lift_unique` and `IsLocalizedModule.is_universal`. These are reuse leads by Lean name; this note does not claim a new service-checked bridge. Do not replace the construction with an assumed `IsLocalizedModule` certificate.

Task `08bb9432-0606-45f0-a725-70e8b0dda929` owns the focused linear-map bridge and explicit integer/rational counterexample. Full-subcategory packaging remains separate: `ModuleCat.localizedModuleFunctor` in `Algebra/Category/ModuleCat/Localization.lean` targets modules over the localized ring, not directly the full subcategory of S-local A-modules. Its `Small` hypothesis must not silently restrict the independent-universe linear-map interface. Example 5's polynomial-module/endomorphism comparison, the assertions on PDF259, and localization exactness remain other obligations. The project's Jacquet character-coinvariant localization is a distinct construction.

## A.IV.1–A.IV.2: constant functors and factorization arrows

At printed256/PDF262, the source asserts that for a nonempty index category I, natural transformations between two constant functors correspond bijectively to morphisms between their values. Nonemptiness does not suffice for fullness.

Let I be the discrete category on two objects, and take the target category to be types. Put X = a singleton and Y = a two-element type. A natural transformation from constant X to constant Y may send the singleton to false at one index and true at the other: the only naturality conditions concern identity morphisms. No single function X → Y induces those two different components. Thus the diagonal constant-functor map on morphisms is not surjective.

Connectedness supplies the missing hypothesis for this auxiliary comparison. Naturality forces equal components along every arrow, hence along every connecting zigzag; nonemptiness provides a component from which to recover the base morphism. In the inspected Mathlib sources, `Functor/Const.lean` provides the constant functor and faithfulness for a nonempty index category, while `CategoryTheory/IsConnected.lean` provides `nat_trans_from_is_connected` and fullness for connected indices.

General limits and colimits must still allow arbitrary index categories, including empty and disconnected ones. A cone explicitly stores its vertex X and compatible legs. Its universal property quantifies over morphisms Y → X in the original category, not over arbitrary natural transformations between constant functors. Equivalently, a limiting cone gives `Hom(Y, X) ≃ Nat(const Y, D)` for every Y. This formulation works without connectedness. For an empty index, the vertex must remain explicit: the empty functor alone cannot remember it.

There are also arrow-direction errors. The limit paragraph's parenthesis on PDF262 says X → Y where the displayed transformation and the later concrete universal property require Y → X. The colimit prose on printed257/PDF263 says constant Y → constant X, and Y → X, whereas its displayed factorization `D → const X → const Y` correctly requires X → Y. The corrected cone/cocone formulation resolves these directions directly.

Task `57165880-67cc-47a1-9761-3960f6543b0b` owns this source bridge and the disconnected counterexample. It reuses actual Mathlib `Cone`, `Cocone`, their morphisms and `IsLimit`/`IsColimit`. Those latter objects carry data, so proposition wrappers must express their existence. Connectedness belongs only in the constant-functor full-faithfulness comparison, never as a new restriction on general limits. The individual example identifications, complete existence claims and later uses of limits remain separate source obligations.

## A.VI.1: subobject and quotient closure do not supply finite products

At printed261/PDF267, the source says that every full subcategory of A-mod closed under submodules and quotients is abelian. There is no finite-sum closure hypothesis. The definition of full subcategory on printed251/PDF257 uses a fully faithful inclusion, without a finite-sum convention. The following AB0 and AB1 explicitly require a zero object and finite products.

For a field K, consider the replete full subcategory of K-vector spaces of dimension zero or one. It contains zero and is closed under ambient subobjects and quotients. It has no categorical product of K with K, as follows.

Suppose P, with maps p,q : P → K, were such a product inside this subcategory. For every pair a,b in K, apply the universal property to the two maps K → K taking 1 to a and b. The resulting map K → P exhibits an element x with p(x) = a and q(x) = b. Therefore the linear map `P → K × K`, `x ↦ (p(x), q(x))`, is surjective. This contradicts `dim P ≤ 1` and `dim(K × K) = 2`. The argument excludes every possible internal product candidate, not just the ambient chosen product.

A correct sufficient criterion adds finite-product closure and zero containment to subobject and quotient closure. More generally, Mathlib's `CategoryTheory/Abelian/Subcategory.lean` constructs an abelian full subcategory from zero containment and closure under kernels, cokernels and finite products. `ObjectProperty/Kernels.lean` derives the kernel and cokernel hypotheses from subobject and quotient closure. Finite products in an abelian category are finite direct sums. This is a sufficient correction, not a characterization of all abelian full subcategories.

Task `5ee443d9-9b37-47d5-919d-7077bb34766a` owns the exact Prop statements for both corrected criteria and the counterexample. The predicate must use cardinal rank at most one, or finite-dimensionality together with finrank at most one: a bare finrank inequality admits infinite-dimensional spaces because finrank can then be zero. The no-product target must express the actual categorical universal property. Since Mathlib's `Abelian` contains a preadditive structure, a Prop target can use `Nonempty (Abelian ...)`; it must not assume this structure as an input.

The concrete formal counterexample uses the existing unital `ModuleCat`. It also explains the problem with the source's larger possibly-nonunital module category, since submodules and quotients of unital vector spaces remain unital. A formal embedding into that pending ambient category remains a separate adapter obligation. The equivalence of the source's AB axioms with Mathlib's definition and all A.VI.2 assertions remain open.

The existing Library module `Langlands/Representation/Category/Abelian.lean` explicitly proves finite-product closure before constructing the abelian category of smooth representations. The missing hypothesis in the book therefore does not identify a defect in that published theorem.

## Formalization and provenance boundary

The counterexamples and corrections above are internal mathematical diagnoses based on the original passages. They are not attributed to the book as its own results, and this note contains no new Lean declaration. The Mathlib navigation was checked against source at commit `5ed2965256430c3649e86755f9576b54eca72435`; declaration inspection and source-to-Lean bridges belong to the focused tasks.

The parent `f5d1f399-a1f8-4ab5-a981-90b92abd4857` retains every omitted assertion and must verify accepted statements, proofs and current publication before counting a task as mathematical coverage. In particular, the abelian-subcategory proof successor must be bound to the statement declarations after their publication. None of these corrections narrows the whole-book program to special linear groups, a particular field characteristic or finite-dimensional representation theory.
