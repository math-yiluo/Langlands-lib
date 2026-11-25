/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedGlobalSectionsTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit

/-!
# Cohomology at the coefficient stage `ℚ̄_ℓ`

Blueprint `def-weil-ordinary-compact-cohomology` defines, at every coefficient stage `Λ`, the
coefficient complexes `RΓ(Y, K) = Fib_s(Ra_{Y*} K)` and `RΓ_c(Y, K) = Fib_s(Ra_{Y!} K)` of an
object `K` of `D^b_c(Y, Λ)` and their cohomology; for a Weil complex they are applied to its
underlying complex. This file records the stage `Λ = ℚ̄_ℓ`:

- for objects of the derived category of sheaves of modules over the `ℓ`-adic constant sheaf
  `ℚ̄_ℓ,Y = colim_E C(-, E)` on the pro-étale site (`AlgebraicGeometry.ProEtale.AdicSheaf`; the
  bounded constructible objects form `D^b_c(Y, ℚ̄_ℓ)`), the derived pushforward `Ra_*`, resp. the
  direct image with compact support `Ra_!`, followed by derived global sections and `Hⁱ`
  (`AlgebraicGeometry.ProEtale.algClosedCohomology`,
  `AlgebraicGeometry.ProEtale.algClosedCompactlySupportedCohomology`). The coefficient sheaf is
  not the sheaf `U ↦ C(U, ℚ̄_ℓ)` of all continuous functions used at the stages `Λ = 𝒪_E, E`
  (`WeilConjectures.WeilSheaf.FieldCoefficientCohomology`): `ℚ̄_ℓ` is not locally compact, and
  a continuous map from a profinite set to `ℚ̄_ℓ` need not factor through any finite `E`;
- for objects `(E, K)` of the `2`-colimit model `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`
  (`AlgebraicGeometry.WeilComplexTwoColimit`), the cohomology of `ℚ̄_ℓ ⊗_E K`
  (`AlgebraicGeometry.WeilComplexTwoColimit.cohomology`,
  `AlgebraicGeometry.WeilComplexTwoColimit.compactlySupportedCohomology`), with its geometric
  Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] {Y s : Scheme.{u}} (a : Y ⟶ s)

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`: the coefficient complex
`RΓ(Y, K) = Fib_s(Ra_* K)` of a complex `K` of sheaves of modules over the `ℓ`-adic constant sheaf
`ℚ̄_ℓ,Y = colim_E C(-, E)` (`AlgebraicGeometry.ProEtale.adicConstantSheaf`) on the pro-étale site
of `Y`, along `a : Y ⟶ s`: the total right derived functor of the pushforward `a_*`, followed by
the right derived functor of the global sections of `s` (for `s = Spec k`, `k` algebraically
closed, the evaluation `Fib_s` at the geometric point). -/
noncomputable def algClosedRightDerivedGlobalSections :
    _root_.DerivedCategory (AdicSheaf l Y) ⥤ _root_.DerivedCategory (WeilCoefficients.{u} l) :=
  (a)_*ᵃ[l].rightDerivedFunctor ⋙ (adicGlobalSections l s).rightDerivedFunctor

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`: the cohomology
`Hⁱ(Y, K) = Hⁱ(Fib_s(Ra_* K))` of a complex `K` of sheaves of `ℚ̄_ℓ,Y`-modules on the pro-étale
site of `Y`, along `a : Y ⟶ s` (for `a` the structure morphism of a separated `k`-scheme of
finite type, `k` algebraically closed). -/
noncomputable def algClosedCohomology (i : ℤ) :
    _root_.DerivedCategory (AdicSheaf l Y) ⥤ WeilCoefficients.{u} l :=
  algClosedRightDerivedGlobalSections l a ⋙ _root_.DerivedCategory.homologyFunctor _ i

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`: the compactly supported
coefficient complex `RΓ_c(Y, K) = Fib_s(Ra_! K)` of a complex `K` of sheaves of
`ℚ̄_ℓ,Y`-modules on the pro-étale site of `Y`, along `a : Y ⟶ s` admitting a compactification
`Y ⟶[ī] Z ⟶[ḡ] s`: the direct image with compact support `Ra_! = Rḡ_* ∘ ī_!` (the exact
extension by zero along `ī`, then the total right derived functor of `ḡ_*`), followed by the
right derived functor of the global sections of `s`. -/
noncomputable def algClosedCompactlySupportedGlobalSections [HasCompactification a] :
    _root_.DerivedCategory (AdicSheaf l Y) ⥤ _root_.DerivedCategory (WeilCoefficients.{u} l) :=
  ((HasCompactification.compactification a).i)_!ᵃ[l].mapDerivedCategory ⋙
    ((HasCompactification.compactification a).g)_*ᵃ[l].rightDerivedFunctor ⋙
      (adicGlobalSections l s).rightDerivedFunctor

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`: the compactly supported
cohomology `Hⁱ_c(Y, K) = Hⁱ(Fib_s(Ra_! K))` of a complex `K` of sheaves of `ℚ̄_ℓ,Y`-modules on the
pro-étale site of `Y`, along `a : Y ⟶ s` admitting a compactification. -/
noncomputable def algClosedCompactlySupportedCohomology [HasCompactification a] (i : ℤ) :
    _root_.DerivedCategory (AdicSheaf l Y) ⥤ WeilCoefficients.{u} l :=
  algClosedCompactlySupportedGlobalSections l a ⋙ _root_.DerivedCategory.homologyFunctor _ i

end ProEtale

namespace WeilComplexTwoColimit

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`, `2`-colimit model: the
cohomology `Hʳ(X ⊗ k̄, K)` of an object `K = (E, K_E)` of
`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`, with its geometric Frobenius: the cohomology
(`AlgebraicGeometry.WeilComplex.cohomology`) of its image `ℚ̄_ℓ ⊗_E K_E` in the direct
`ℚ̄_ℓ`-stage (`AlgebraicGeometry.WeilComplexTwoColimit.toWeilComplex`). -/
noncomputable def cohomology (K : WeilComplexTwoColimit k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((toWeilComplex k₀ X).obj K).cohomology r

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`, `2`-colimit model: the
compactly supported cohomology `H_cʳ(X ⊗ k̄, K)` of an object `K = (E, K_E)` of
`D^b_{c,W}(X, ℚ̄_ℓ)`, with its geometric Frobenius: that
(`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`) of `ℚ̄_ℓ ⊗_E K_E`. -/
noncomputable def compactlySupportedCohomology [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (K : WeilComplexTwoColimit k₀ l X) (r : ℤ) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((toWeilComplex k₀ X).obj K).compactlySupportedCohomology r

end WeilComplexTwoColimit

end AlgebraicGeometry
