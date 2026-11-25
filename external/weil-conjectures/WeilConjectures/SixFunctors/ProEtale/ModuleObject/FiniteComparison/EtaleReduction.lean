/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived

/-!

# Reduction modulo `ℓⁿ` read on the small étale site

For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and `n : ℕ`, the coefficient change
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` sends a bounded constructible `𝒪_E`-complex `K` on the pro-étale site of `X`
to `K ⊗ᴸ 𝒪_E ⧸ ℓⁿ`. For the finite ring `𝒪_E ⧸ ℓⁿ` the blueprint reads the target on the small
étale site (`definition-constructible-sheaves`: "for finite `Λ = A_{E,n}`, and only there, the same
definitions may be read on the small étale site; the comparison `ν_T^*` identifies them with the
pro-étale categories"). This file defines this étale reading of the reduction,
```
Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ),   K ↦ Rν_* (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ),
```
(`AlgebraicGeometry.ProEtale.CondensedRing.etaleReduction`): the reduction of condensed
coefficients (`AlgebraicGeometry.ProEtale.boundedConstructibleIntegersModPowReduction`), the
identification of condensed `𝒪_E ⧸ ℓⁿ`-module objects with pro-étale sheaves of modules
(`AlgebraicGeometry.ProEtale.finiteCoefficientDerivedEquivalence`) and the comparison
`Rν_* : D(X_proét) ⥤ D(X_ét)`.

It states the coefficient comparisons of blueprint `proposition-six-operations-change-coefficients`
for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site, that the trace formula uses to
pass from integral to finite coefficients (blueprint `lemma-vanishing-local-term-zero-stalk`, last
step). They are compatibilities required from section `chap-Construction-of-f`, each exactly one
blueprint node:

* `nonempty_etaleReductionUpperStarIso`: pullback (`proposition-six-operations-change-coefficients`,
(1)), by the
  canonical isomorphism `etaleReductionUpperStarIso`;
* `exists_etaleReductionLowerShriekIso`: compactly supported direct image and exceptional
  inverse image, for proper morphisms (`lemma-change-coefficients-exceptional-inverse-image`, with
  the comparison `γ^!` of `lemma-change-coefficients-compact-support`), proved in the file
  `FiniteComparison/EtaleReductionLowerShriekIso.lean`;
* `nonempty_etaleReductionTensorIso`: tensor product
(`proposition-six-operations-change-coefficients`, (1));
* `boundedConstructibleFiniteTor_etaleReduction`: preservation of `Dctf`
  (`lemma-extension-scalars-preserves-dctf`, (3)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **The reduction modulo `ℓⁿ`, read on the small étale site**: `K ↦ Rν_* (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`,
from bounded constructible `𝒪_E`-complexes on `X_proét` to the derived category of étale sheaves
of `𝒪_E ⧸ ℓⁿ`-modules on `X`. -/
noncomputable def etaleReduction (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤
      DerivedCategory (Sheaf Y.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :=
  boundedConstructibleIntegersModPowReduction Y.left ℓ E n ⋙ (boundedConstructible _).ι ⋙
    (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
      R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])

/-! ### The coefficient comparisons for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` -/

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The canonical isomorphism: reduction modulo `ℓⁿ` commutes with pullback**,
`(f^* K)_{𝒪_E ⧸ ℓⁿ} ≅ f^* (K_{𝒪_E ⧸ ℓⁿ})` (blueprint
`proposition-six-operations-change-coefficients`, (1), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`,
read on the étale site, `definition-constructible-sheaves`).

It is the composite of the following canonical isomorphisms: the reduction commutes with
pullback on the condensed side (`boundedConstructibleUpperStarIntegersModPowReductionIso`), the
pullback of bounded constructible complexes is computed by the derived pullback
(`boundedConstructibleUpperStarCompatibility`), the comparison of the two finite-coefficient
models commutes with pullback (`leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso`),
and the inverse of the canonical base change morphism `Lf^* Rν_* ⟶ Rν_* Lf^*`
(`rightDerivedComparisonBaseChange`), which is invertible on complexes of étale origin
(`isIso_rightDerivedComparisonBaseChange_app`), as the reductions of bounded constructible
complexes are (`isEtaleOrigin_of_isConstructible`). -/
noncomputable def etaleReductionUpperStarIso (f : Z ⟶ Y) :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f ⋙
        etaleReduction ℓ E n Z ≅
      etaleReduction ℓ E n Y ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left) := by
  let T := PadicAlgCl.integersModPow ℓ E n
  let A := ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)
  let U := boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f
  let UA := boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ f
  let RY := boundedConstructibleIntegersModPowReduction Y.left ℓ E n
  let RZ := boundedConstructibleIntegersModPowReduction Z.left ℓ E n
  let ιY := (boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n)
    Y.left)).ι
  let ιZ := (boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n)
    Z.left)).ι
  let ΦY := (finiteCoefficientDerivedEquivalence Y.left T).functor
  let ΦZ := (finiteCoefficientDerivedEquivalence Z.left T).functor
  let νY := R(ν_*(Y.left)[A])
  let νZ := R(ν_*(Z.left)[A])
  let LMod := L((f.left)^*⟦Profinite.integersModPowRingObj ℓ E n⟧)
  let LMC := L(ProEtale.upperStar A f.left)
  let Let := L(Etale.upperStar A f.left)
  -- the reduction, read on pro-étale sheaves of `𝒪_E ⧸ ℓⁿ`-modules
  let P := RY ⋙ ιY ⋙ ΦY
  have hP (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
      DerivedCategory.plusEtaleOrigin A Y.left (P.obj K) :=
    (isEtaleOrigin_of_isConstructible T (RY.obj K).property).plusEtaleOrigin
  have : IsIso (Functor.whiskerLeft P (rightDerivedComparisonBaseChange A f.left)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun K ↦ isIso_rightDerivedComparisonBaseChange_app A f.left _ (hP K)
  let e₁ : (U ⋙ RZ) ⋙ ιZ ⋙ ΦZ ⋙ νZ ≅ (RY ⋙ UA) ⋙ ιZ ⋙ ΦZ ⋙ νZ :=
    Functor.isoWhiskerRight (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f) _
  let e₂ : RY ⋙ (UA ⋙ ιZ) ⋙ ΦZ ⋙ νZ ≅ RY ⋙ (ιY ⋙ LMod) ⋙ ΦZ ⋙ νZ :=
    Functor.isoWhiskerLeft RY
      (Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _)
  let e₃ : RY ⋙ ιY ⋙ (LMod ⋙ ΦZ) ⋙ νZ ≅ RY ⋙ ιY ⋙ (ΦY ⋙ LMC) ⋙ νZ :=
    Functor.isoWhiskerLeft RY (Functor.isoWhiskerLeft ιY (Functor.isoWhiskerRight
      (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f.left T) _))
  let e₄ : P ⋙ LMC ⋙ νZ ≅ P ⋙ νY ⋙ Let :=
    (asIso (Functor.whiskerLeft P (rightDerivedComparisonBaseChange A f.left))).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- Compatibility required from `chap-Construction-of-f` (to be proved there): blueprint
`proposition-six-operations-change-coefficients`, (1), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`,
read on the étale site (`definition-constructible-sheaves`). **Reduction modulo `ℓⁿ` commutes with
pullback**: `(f^* K)_{𝒪_E ⧸ ℓⁿ} ≅ f^* (K_{𝒪_E ⧸ ℓⁿ})`, by the canonical isomorphism
`etaleReductionUpperStarIso`. -/
theorem nonempty_etaleReductionUpperStarIso (f : Z ⟶ Y) :
    Nonempty (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f ⋙
        etaleReduction ℓ E n Z ≅
      etaleReduction ℓ E n Y ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)) :=
  ⟨etaleReductionUpperStarIso ℓ E n f⟩

omit [Fact (ringChar k).Prime] in
/-- Blueprint `proposition-six-operations-change-coefficients`, (1), for the coefficient map
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site (`definition-constructible-sheaves`). **Reduction modulo
`ℓⁿ` commutes with the tensor product**: `(K ⊗ᴸ M)_{𝒪_E ⧸ ℓⁿ} ≅ K_{𝒪_E ⧸ ℓⁿ} ⊗ᴸ M_{𝒪_E ⧸ ℓⁿ}`
(proved in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionTensor`). -/
theorem nonempty_etaleReductionTensorIso (K M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Nonempty ((etaleReduction ℓ E n Y).obj (K ⊗ M) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Y.left).obj
        ((etaleReduction ℓ E n Y).obj K)).obj ((etaleReduction ℓ E n Y).obj M)) :=
  nonempty_etaleReductionTensorIso_of_components ℓ E n K M

-- the coefficient hypotheses on `k` are part of the setting of the statement, unused by the proof
set_option linter.unusedSectionVars false in
/-- Compatibility required from `chap-Construction-of-f` (to be proved there): blueprint
`lemma-extension-scalars-preserves-dctf`, (3), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the
étale site (`definition-constructible-sheaves`). **Reduction modulo `ℓⁿ` preserves `Dctf`**: for a
bounded constructible `𝒪_E`-complex `K` (for which `Dᵇc = Dctf`, `proposition-ctf-equals-bc`), the
reduction `K_{𝒪_E ⧸ ℓⁿ}` is bounded constructible of finite Tor amplitude. -/
theorem boundedConstructibleFiniteTor_etaleReduction
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Etale.DerivedCategory.boundedConstructibleFiniteTor (integersModPowCoeff.{u} ℓ E n) Y.left
      ((etaleReduction ℓ E n Y).obj K) :=
  boundedConstructibleFiniteTor_etaleReduction_of_components ℓ E n K

end AlgebraicGeometry.ProEtale.CondensedRing
