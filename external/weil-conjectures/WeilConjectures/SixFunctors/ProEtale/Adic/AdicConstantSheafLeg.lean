/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarScalar
public import WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapReduction
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra

/-!
# The maps `ℓ⁻ⁿ : 𝒪_{E,X} ⟶ ℚ̄_ℓ,X` on sections

- `AlgebraicGeometry.ProEtale.adicConstantSheafLeg_hom_app`: the map
  `AlgebraicGeometry.ProEtale.adicConstantSheafLeg` is `f ↦ ℓ⁻ⁿ f` on sections, the
  sheafifications involved being computed by the counit of the sheafification adjunction.
- `AlgebraicGeometry.ProEtale.padicIntegersSheafMulOfLE`: the multiplication
  `𝒪_{E,X} ⟶ 𝒪_{F,X}`, `f ↦ o f`, by an element `o ∈ 𝒪_F` for `E ⊆ F`.
- `AlgebraicGeometry.ProEtale.padicIntegersSheafMulOfLE_comp_adicConstantSheafLeg`:
  `ℓ⁻ⁿ (o f) = (ℓ⁻ⁿ o) f`, the multiplication by the scalar `ℓ⁻ⁿ o` on `ℚ̄_ℓ,X` being
  `AlgebraicGeometry.ProEtale.weilSmulNatTrans`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The inclusion `E_X ⟶ ℚ̄_ℓ,X` on sections: `f ↦ (x ↦ f x)`. -/
lemma padicSubfieldSheafToPadicAlgClSheaf_comp_iso_hom_app (E : FiniteIntermediateField l)
    (U : X.ProEtᵒᵖ) (f : ((padicSubfieldSheaf X l E.1).obj.obj U)) :
    letI := normedFieldOfAlgebra l E.1
    ((padicSubfieldSheafToPadicAlgClSheaf X l E.1 ≫
      (padicAlgClSheafIsoAdicConstantSheaf X l).hom).hom.app U f).down.1 =
        (⟨algebraMap E.1 (PadicAlgCl l), continuous_algebraMap_padicAlgCl_of_algebra l E.1⟩ :
          C(E.1, PadicAlgCl l)).comp f.down := by
  let := normedFieldOfAlgebra l E.1
  let P := Functor.whiskerRight (continuousMapRingPresheafToPadicAlgCl X l
    (algebraMap E.1 (PadicAlgCl l)) (continuous_algebraMap_padicAlgCl_of_algebra l E.1)
    ⟨_, finiteDimensional_fieldRange_toAlgHom l E.1, fun t ↦ ⟨t, rfl⟩⟩)
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫ padicAlgClPresheafToAdicConstantSheaf X l
  have key : padicSubfieldSheafToPadicAlgClSheaf X l E.1 ≫
      (padicAlgClSheafIsoAdicConstantSheaf X l).hom = ⟨P⟩ := by
    simp only [padicSubfieldSheafToPadicAlgClSheaf, continuousMapRingSheafToPadicAlgClSheaf,
      Sheaf.sheafComposeToSheafify, padicAlgClSheafIsoAdicConstantSheaf, asIso_hom,
      padicAlgClSheafToAdicConstantSheaf, Adjunction.homEquiv_counit, Category.assoc,
      ← Functor.map_comp_assoc]
    rw [Iso.inv_comp_eq]
    exact ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).counit.naturality
      (⟨P⟩ : (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicSubfieldSheaf X l E.1) ⟶
        (sheafCompose (Scheme.ProEt.topology X) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
          (adicConstantSheaf l X)))
  rw [key]
  rfl

/-- The map `ℓ⁻ⁿ : 𝒪_{E,X} ⟶ ℚ̄_ℓ,X` on sections: `f ↦ ℓ⁻ⁿ f`. -/
lemma adicConstantSheafLeg_hom_app (E : FiniteIntermediateField l) (n : ℕ) (U : X.ProEtᵒᵖ)
    (f : (padicIntegersSheaf X l E.1).obj.obj U) (x : U.unop.left) :
    ((adicConstantSheafLeg X l E n).hom.app U f).down.1 x =
      ((l : PadicAlgCl l) ^ n)⁻¹ * algebraMap (integers l E.1) (PadicAlgCl l) (f.down x) := by
  have := padicSubfieldSheafToPadicAlgClSheaf_comp_iso_hom_app X l E U
    ((padicSubfieldSheafCocone X l E.1).ι.app n |>.hom.app U f)
  have h2 := congrArg (fun g ↦ g x) this
  refine h2.trans ?_
  change algebraMap E.1 (PadicAlgCl l) (((l : E.1) ^ n)⁻¹ * (f.down x : E.1)) = _
  rw [map_mul, map_inv₀, map_pow, map_natCast]
  rfl

variable {X l} {E F : FiniteIntermediateField l} (h : E.1 ≤ F.1)

variable (X) in
/-- Multiplication by `o ∈ 𝒪_F`, `𝒪_{E,X} ⟶ 𝒪_{F,X}`, `f ↦ o f`, for `E ⊆ F`. -/
noncomputable def padicIntegersSheafMulOfLE (o : integers l F.1) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf X l E.1) ⟶
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf X l F.1) :=
  letI := normedFieldOfAlgebra l F.1
  have := isTopologicalRing_integers l F.1
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicIntegersSheafMapOfLE X l h) ≫
    continuousMapAbSheafMul X (integers l F.1) o

lemma padicIntegersSheafMulOfLE_hom_app (o : integers l F.1) (U : X.ProEtᵒᵖ)
    (f : (padicIntegersSheaf X l E.1).obj.obj U) (x : U.unop.left) :
    ((padicIntegersSheafMulOfLE X h o).hom.app U f).down x =
      o * integersInclusion l h (f.down x) :=
  rfl

/-- `ℓ⁻ⁿ (o f) = (ℓ⁻ⁿ o) f`: the map `ℓ⁻ⁿ : 𝒪_{F,X} ⟶ ℚ̄_ℓ,X` after multiplication by `o ∈ 𝒪_F`
is the inclusion `𝒪_{E,X} ⟶ ℚ̄_ℓ,X` followed by the multiplication by the scalar `ℓ⁻ⁿ o`. -/
lemma padicIntegersSheafMulOfLE_comp_adicConstantSheafLeg (o : integers l F.1) (n : ℕ) :
    padicIntegersSheafMulOfLE X h o ≫ adicConstantSheafLeg X l F n =
      adicConstantSheafLeg X l E 0 ≫ (weilCoefficientsForgetAb l X).map
        ((weilSmulNatTrans l X (ULift.up (((l : PadicAlgCl l) ^ n)⁻¹ *
          algebraMap (integers l F.1) (PadicAlgCl l) o))).app (adicConstantSheaf l X)) := by
  ext U f
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
  change ((adicConstantSheafLeg X l F n).hom.app U _).down.1 x =
    (((l : PadicAlgCl l) ^ n)⁻¹ * algebraMap (integers l F.1) (PadicAlgCl l) o) *
      ((adicConstantSheafLeg X l E 0).hom.app U f).down.1 x
  rw [adicConstantSheafLeg_hom_app, adicConstantSheafLeg_hom_app, pow_zero, inv_one, one_mul,
    mul_assoc]
  congr 1

end AlgebraicGeometry.ProEtale
