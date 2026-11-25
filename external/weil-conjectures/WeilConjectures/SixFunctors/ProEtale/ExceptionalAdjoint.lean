/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-!
# The ambient exceptional right adjoint datum and exceptional-adjoint admissibility

Blueprint `sk-def-sf-admissible` names two hypotheses of different strength for a separated
finite-type `f : X ⟶ Y` with a compactification `X → X̄ → Y` whose proper part is `p`:

* clause (1), the *ambient exceptional right adjoint datum*
  `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint`: a uniform
  cohomological-dimension bound `FullCD(p, A; c)` for some `c`, together with a right adjoint
  of `Rf_!` on the unbounded derived categories of the small pro-étale sites
  (`AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint`);
* clauses (1)–(3), *exceptional-adjoint admissibility*
  `AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible`: clause (1) together with the
  preservation clauses, that a right adjoint `Rf^×` of `Rf_!` carries each constructible interval
  `D_c^[a, b](Y, A)` into `D_c^[a + c₁, b + c₂](X, A)` for constants `c₁, c₂` independent of
  `a, b` (2), and `Dctf(Y, A)` into `Dctf(X, A)` (3).

Both are *hypotheses*, and they **fail in general** (`sk-rem-sf-fullcd-scope`). Let `E` be an
elliptic curve over `𝔽̄_p`, `r ≠ p` a prime and `A` the category of `𝔽_r`-modules. Evaluating at
the pro-étale geometric generic point `T = Spec k(E)^sep` and taking the right adjoint, one
builds a pro-étale sheaf `F` with `Hⁿ(E_proét, F) ≅ Hⁿ(⊕_ℕ ℤ, 𝔽_r) ≠ 0` for all `n ≥ 1`. So
`FullCD` fails for the structure morphism `p` of `E`. Moreover countable products and coproducts
of pro-étale sheaves are exact, so `⊕ F[n] ≅ ∏ F[n]`, while `Rp_*` sends this to the
non-surjective `⊕ Hⁿ(E, F) → ∏ Hⁿ(E, F)` in degree `0`: `Rp_! = Rp_*` does not preserve
coproducts and has no right adjoint on `D`. A separate `t`-structure argument rules out a right
adjoint on `D⁺` as well. The sheaf `F` is not of étale origin. The blueprint's proof chain never
assumes these data: it uses the constructible `Rf^!` of
`theorem-f-shriek-ell-adic-coefficients--4`(vi) instead, and the data survive only as optional
hypotheses of `proposition-composition-open-restriction-compactifications-f--1`(a), of the second
half of `sk-thm-sf-package`(1), and of `theorem-existence-exceptional-inverse-image`(b).

On the *étale-origin* class the bound is a theorem, with `c = 2 dim X̄`: it follows from the
finiteness of proper direct images in ordinary étale cohomology together with the pro-étale
comparison. This does not give clause (1), which quantifies over all pro-étale sheaves.

## Implementation notes

The data are `structure`s, not `class`es: they are meant to be named and passed explicitly.

Clauses (2) and (3) are stated for *every* right adjoint `G` of `Rf_!`: the ambient right
adjoint `Rf^×` is not defined in this repository, since it does not exist in general. It is not
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`, which is the constructible `Rf^!` of
`theorem-f-shriek-ell-adic-coefficients--4` (vi). Both predicates are closed under isomorphism, so
this is no stronger than stating them for one right adjoint.

The blueprint's "compatibly with refinements" clause of `sk-def-sf-admissible` is not among
the fields: the repository has no refinement relation between compactifications to state it
against.

The constructible intervals and `Dctf` are those of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`, whose bounded
constructibility is étale origin; these agree with the blueprint's only at the finite coefficient
stages.

The purity chapter itself is stated on the small *étale* site, with
`AlgebraicGeometry.Etale.rightDerivedUpperShriek`, while the data here are about the pro-étale
`Rf^!`. The bridge between the two is the comparison of
`WeilConjectures.SixFunctors.ProEtale.Comparison`: the pro-étale constructible `Rf^!` is by
definition `ν_X^* ∘ f^× ∘ Rν_{Y,*}` (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`).

## Main definitions

- `AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE`: the uniform
  cohomological-dimension bound, stable under base change along the pro-étale site.
- `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint`: the ambient exceptional right
  adjoint datum, clause (1).
- `AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible`: exceptional-adjoint
  admissibility, clauses (1)–(3).

## Main statements

- `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint`: under clause (1),
  `Rf_!` is a left adjoint.
- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`, in
  `WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension`: the bound on the
  étale-origin class (blueprint `sk-prop-sf-fullcd-etale-origin`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}}

/-- Blueprint `sk-def-sf-admissible`: the bound `FullCD(p, A; c)`. This is blueprint
`def-weil-full-cohomological-dimension` (Full cohomological dimension).

Blueprint `def-weil-full-cohomological-dimension`: Full cohomological dimension

`p : X ⟶ Y` *has uniform cohomological dimension at most `c` at `A`* if the higher direct
images of `p`, and of all its base changes along objects of `Y_proét`, vanish above `c` on
*every* pro-étale sheaf of `A`-modules:

```
  X' --g'--> X
  |          |          R^r p'_* F = 0 for r > c, all F on X'_proét
  p'         p
  |          |
  v          v
  V.left --V.hom--> Y        V an object of Y_proét
```

This is the uniform bound that makes `Rp_*` preserve coproducts on the unbounded derived
category. The base changes are taken along the pro-étale site of `Y`, as in the blueprint, and
not along arbitrary morphisms of schemes: the latter is a strictly stronger hypothesis than
`sk-prop-sf-fullcd-etale-origin` can deliver.

Not satisfied in general, even for proper smooth `p`; see `sk-rem-sf-fullcd-scope` and the
module docstring. -/
def HasUniformCohomologicalDimensionLE (p : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ (V : Y.ProEt) ⦃X' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ V.left),
    IsPullback g' p' p V.hom →
      ∀ (F : Sheaf (Scheme.ProEt.topology X') A) (r : ℤ), (c : ℤ) < r →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
          ((R((p')_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- Blueprint `sk-def-sf-admissible`, clause (1): the ambient exceptional right adjoint datum.
This is blueprint `def-weil-ambient-exceptional-adjoint` (Ambient exceptional right adjoint
datum).

For a morphism `f : X ⟶ Y` with a chosen compactification: a uniform cohomological-dimension
bound `FullCD(p, A; c)` for the proper part `p` of the compactification, for some `c`, and the
existence of a right adjoint `Rf^×` of `Rf_!` on the unbounded derived categories of the small
pro-étale sites. The blueprint also asks that units, counits and comparison maps agree for
every refinement of the compactification; here `Rf_!` is formed with the one chosen
compactification, so this clause is empty.

Not satisfied in general; see `sk-rem-sf-fullcd-scope` and the module docstring. -/
structure HasAmbientExceptionalRightAdjoint (f : X ⟶ Y) [HasCompactification f] : Prop where
  /-- A uniform cohomological-dimension bound for the proper part of the compactification. -/
  exists_hasUniformCohomologicalDimensionLE :
    ∃ c : ℕ, HasUniformCohomologicalDimensionLE A (HasCompactification.compactification f).g c
  /-- The derived lower shriek `Rf_!` has a right adjoint `Rf^×`. -/
  isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint

/-- Blueprint `def-weil-ambient-exceptional-adjoint`: under the ambient exceptional right adjoint
datum, the derived lower shriek `Rf_!` is a left adjoint on the unbounded derived categories of
the small pro-étale sites. This is part of the datum. -/
theorem HasAmbientExceptionalRightAdjoint.isLeftAdjoint {f : X ⟶ Y} [HasCompactification f]
    (h : HasAmbientExceptionalRightAdjoint A f) : (R(f)_![A]).IsLeftAdjoint :=
  h.isLeftAdjoint_rightDerivedLowerShriek

section Admissibility

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Blueprint `sk-def-sf-admissible`: exceptional-adjoint admissibility, clauses (1)–(3).
This is blueprint `def-weil-exceptional-adjoint-admissibility` (Exceptional-adjoint
admissibility), at a finite coefficient stage.

Blueprint `def-weil-exceptional-adjoint-admissibility`: Exceptional-adjoint admissibility

The ambient exceptional right adjoint datum (1), together with the preservation clauses for
every right adjoint `G` of `Rf_!`: `G` preserves bounded constructibility and carries each
constructible interval `D_c^[a, b](Y, A)` into `D_c^[a + c₁, b + c₂](X, A)` for constants
`c₁, c₂` independent of `a, b` (2), and `G` carries `Dctf(Y, A)` into `Dctf(X, A)` (3).

Not satisfied in general; see `sk-rem-sf-fullcd-scope` and the module docstring. -/
structure IsExceptionalAdjointAdmissible (f : X ⟶ Y) [HasCompactification f] : Prop
    extends HasAmbientExceptionalRightAdjoint A f where
  /-- A right adjoint of `Rf_!` preserves bounded constructibility. -/
  boundedConstructible_le_inverseImage :
    ∀ ⦃G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)⦄, (R(f)_![A] ⊣ G) →
      DerivedCategory.boundedConstructible A Y ≤
        (DerivedCategory.boundedConstructible A X).inverseImage G
  /-- A right adjoint of `Rf_!` shifts the constructible intervals by constants independent of
  the interval. -/
  exists_homologyConcentratedIn_le_inverseImage :
    ∃ c₁ c₂ : ℤ, ∀ ⦃G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)⦄, (R(f)_![A] ⊣ G) →
      ∀ a b : ℤ, DerivedCategory.boundedConstructible A Y ⊓
          _root_.DerivedCategory.homologyConcentratedIn a b ≤
        (_root_.DerivedCategory.homologyConcentratedIn (a + c₁) (b + c₂)).inverseImage G
  /-- A right adjoint of `Rf_!` preserves `Dctf`. -/
  constructibleFiniteTor_le_inverseImage :
    ∀ ⦃G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)⦄, (R(f)_![A] ⊣ G) →
      DerivedCategory.constructibleFiniteTor A Y ≤
        (DerivedCategory.constructibleFiniteTor A X).inverseImage G

end Admissibility

end ProEtale

end AlgebraicGeometry
