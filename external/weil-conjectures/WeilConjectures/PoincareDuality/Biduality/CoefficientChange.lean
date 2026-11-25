/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.PoincareDuality.Biduality.CoefficientChangeBraided
public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IhomCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper

/-!
# Biduality along the coefficient change `𝒪_E ⟶ ℚ̄_ℓ`

Write `T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` for the extension of scalars along
`𝒪_E ⟶ E ⟶ ℚ̄_ℓ` on bounded constructible complexes. This file proves the last two steps of
blueprint `theorem-verdier-biduality` ((iii) and (iv)): `T_X` carries the double-dual morphism
of an integral complex to the double-dual morphism of its extension of scalars, and every bounded
constructible `ℚ̄_ℓ`-complex has an integral model, so `ℚ̄_ℓ`-biduality follows from
`𝒪_E`-biduality.

## Main results

- `ProEtale.CondensedRing.integersToPadicAlgClDualizingComplexIso`: `T_X ω_{X, 𝒪_E} ≅ ω_X`, from
  the coefficient comparisons for `Rf^!` (blueprint
  `lemma-change-coefficients-exceptional-inverse-image`).
- `ProEtale.CondensedRing.isIso_verdierBiduality_integersToPadicAlgCl_obj`: if `δ_{K₀}` is an
  isomorphism, so is `δ_{T_X K₀}`. This is the formal compatibility of the double-dual morphism
  with lax braided functors (`CategoryTheory.MonoidalClosed.isIso_map_toIhomIhom_iff`), `T_X`
  commuting with internal homs (blueprint `proposition-six-operations-change-coefficients`).
- `ProEtale.CondensedRing.isIso_verdierBiduality_of_integral`: `ℚ̄_ℓ`-biduality from
  `𝒪_E`-biduality, by integral models (`ProEtale.exists_padicAlgCl_iso_integralModel`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The extension of scalars of the integral dualizing complex is the dualizing complex:
`T_X ω_{X, 𝒪_E} ≅ ω_X`. It is the coefficient comparison for `Ra_X^!` along `𝒪_E ⟶ E` and
`E ⟶ ℚ̄_ℓ` (`boundedConstructibleUpperShriekExtendScalarsIso`,
`isIso_boundedConstructibleUpperShriekToPadicAlgCl`, blueprint
`lemma-change-coefficients-exceptional-inverse-image`) at the unit, followed by the unit comparisons
of the monoidal functors `T_X`. -/
noncomputable def integersToPadicAlgClDualizingComplexIso :
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).obj
        (PadicIntegersRingObj.dualizingComplex ℓ E.1 X) ≅
      dualizingComplex ℓ X :=
  haveI := isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E (Over.mkIdTerminal.from X)
  (constructibleToPadicAlgCl X.left ℓ E).mapIso
      ((boundedConstructibleUpperShriekExtendScalarsIso ℓ E (Over.mkIdTerminal.from X)).app
          (𝟙_ _) ≪≫
        (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E (Over.mkIdTerminal.from X)).mapIso
          (Functor.Monoidal.εIso (boundedConstructibleExtendScalars _ ℓ E)).symm) ≪≫
    asIso ((boundedConstructibleUpperShriekToPadicAlgCl ℓ E (Over.mkIdTerminal.from X)).app
      (𝟙_ _)) ≪≫
    (boundedConstructibleUpperShriek ℓ (Over.mkIdTerminal.from X)).mapIso
      (Functor.Monoidal.εIso (constructibleToPadicAlgCl _ ℓ E)).symm

variable {X}

attribute [local instance] boundedConstructibleBraiding
  PadicIntegersRingObj.boundedConstructibleBraiding

/-- **Biduality along `𝒪_E ⟶ ℚ̄_ℓ`** (blueprint `theorem-verdier-biduality`, (iii) and (iv)):
if the double-dual morphism `δ_{K₀}` of a bounded constructible `𝒪_E`-complex is an isomorphism,
so is the double-dual morphism of its extension of scalars `T_X K₀`. -/
theorem isIso_verdierBiduality_integersToPadicAlgCl_obj
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (hK₀ : IsIso (PadicIntegersRingObj.verdierBiduality ℓ E.1 K₀)) :
    IsIso (verdierBiduality ℓ
      ((boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).obj
        K₀)) := by
  let : BraidedCategory Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧ :=
    @ObjectProperty.fullBraidedSubcategory _ _ _ _ _ (DerivedCategory.braidedCategory' _)
  let := boundedConstructibleExtendScalarsLaxBraided ℓ E X
  let := constructibleToPadicAlgClLaxBraided ℓ E X
  have hT := isIso_ihomComparison_boundedConstructibleIntegersToPadicAlgCl ℓ E (X := X)
  have h₁ := (NatTrans.isIso_iff_isIso_app _).1 (hT K₀)
    (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)
  have h₂ := (NatTrans.isIso_iff_isIso_app _).1
    (hT ((ihom K₀).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)))
    (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)
  have : IsIso (toIhomIhom (PadicIntegersRingObj.dualizingComplex ℓ E.1 X) K₀) := hK₀
  have : IsIso (dualComparison
      (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E)
      (integersToPadicAlgClDualizingComplexIso ℓ E X).hom K₀) :=
    IsIso.comp_isIso
  have : IsIso (dualComparison
      (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E)
      (integersToPadicAlgClDualizingComplexIso ℓ E X).hom
      ((ihom K₀).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))) :=
    IsIso.comp_isIso
  exact (isIso_map_toIhomIhom_iff
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E)
    (integersToPadicAlgClDualizingComplexIso ℓ E X).hom K₀).1 inferInstance

/-- **`ℚ̄_ℓ`-biduality from `𝒪_E`-biduality** (blueprint `theorem-verdier-biduality`, (iv)):
if the double-dual morphisms of all bounded constructible `𝒪_E`-complexes on `X`, for all finite
subextensions `E`, are isomorphisms, so is the double-dual morphism of every bounded
constructible `ℚ̄_ℓ`-complex `K`: `K ≅ T_X K₀` for an integral model `K₀`. -/
theorem isIso_verdierBiduality_of_integral
    (h : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧),
      IsIso (PadicIntegersRingObj.verdierBiduality ℓ E.1 K₀))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierBiduality ℓ K) := by
  have := noetherianSpace_left_of_over X
  obtain ⟨E, K₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel (X := X.left) ℓ K
  have := isIso_verdierBiduality_integersToPadicAlgCl_obj ℓ E K₀ (h E K₀)
  exact (Verdier.isIso_bidualityMap_iff_of_iso (dualizingComplex ℓ X) e).1 this

end AlgebraicGeometry.ProEtale.CondensedRing
