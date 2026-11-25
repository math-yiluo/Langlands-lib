/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.ReductionTriangleDoubleMate
public import WeilConjectures.CategoryTheory.ObjectProperty.LiftCommShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionProperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionRestrictConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek

/-!
# Reduction modulo `ℓⁿ` commutes with `Rp^!` for proper `p`, on condensed coefficients

Let `p : X ⟶ Y` be a proper morphism of separated `k`-schemes of finite type, and write
`red : Dᵇc(-)⟦𝒪_E⟧ ⥤ Dᵇc(-)⟦𝒪_E ⧸ ℓⁿ⟧` for the reduction modulo `ℓⁿ` on bounded constructible
condensed coefficients (`ProEtale.CondensedRing.boundedConstructibleIntegersModPowReduction`).
Since `p` is proper, `Rp_! ≅ Rp_*` on `Dᵇc(-)⟦𝒪_E⟧`, so `Rp^!` is a right adjoint of `Rp_*`.
Let `H'` be any right adjoint of `Rp_*` on `Dᵇc(-)⟦𝒪_E ⧸ ℓⁿ⟧`.

This file proves that the exceptional comparison `Rp^! ⋙ red_X ⟶ red_Y ⋙ H'`, the mate of the
inverse of the pushforward comparison `γ : Rp_* ⋙ red_Y ≅ red_X ⋙ Rp_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersModPowReduction`), is an
isomorphism
(`ProEtale.CondensedRing.isIso_mateEquiv_boundedConstructibleLowerStarIntegersModPowReduction`),
assuming:

* the compatibilities of (Pull) with the natural reduction triangle on the full derived
  categories (`ProEtale.CondensedRing.IntegersModPowPullUnitCompatible`,
  `ProEtale.CondensedRing.IntegersModPowPullδCompatible`), which make `γ` an isomorphism;
* that restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` preserves bounded constructible complexes
  on `X` and on `Y` (`ProEtale.CondensedRing.RestrictScalarsIntegersModPowBoundedConstructible`),
  so that `red ⊣ Res` restricts to `Dᵇc` with its natural reduction triangle
  (`ProEtale.CondensedRing.boundedConstructibleIntegersModPowAdjunction`).

The proof is the formal argument `CategoryTheory.isIso_mateEquiv_mateEquiv_of_reductionTriangle'`:
the compatibilities of (Pull) restrict to `Dᵇc`
(`ProEtale.CondensedRing.boundedConstructibleUnitCompatible`,
`ProEtale.CondensedRing.boundedConstructibleδCompatible`), transpose to `Rp_*`, and then to `Rp^!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {n : ℕ}
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (hX : RestrictScalarsIntegersModPowBoundedConstructible ℓ E n X.left)
  (hY : RestrictScalarsIntegersModPowBoundedConstructible ℓ E n Y.left) (p : X ⟶ Y)

variable (ℓ E n) in
/-- The restricted (Pull) is (Pull) on the underlying complexes. -/
lemma boundedConstructibleUpperStarIntegersModPowReductionIso_hom_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n p).hom.app K).hom =
      (integersModPowReductionUpperStarIso ℓ E n p.left).hom.app K.obj := by
  rw [← cancel_mono ((integersModPowReductionUpperStarIso ℓ E n p.left).inv.app K.obj),
    Iso.hom_inv_id_app, ← boundedConstructibleUpperStarIntegersModPowReductionIso_inv_app_hom,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
  rfl

/-- **Restriction of scalars commutes with the pullback on bounded constructible complexes**:
`Res_Y ⋙ Lp^* ≅ Lp^* ⋙ Res_X`, the restriction of
`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso` along the inclusions. -/
noncomputable def boundedConstructibleRestrictionUpperStarIso :
    boundedConstructibleIntegersModPowRestriction hY ⋙
        boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p ≅
      boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ p ⋙
        boundedConstructibleIntegersModPowRestriction hX :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((derivedComapLeftDerivedUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
        p.left).app K.obj))
    (fun f ↦ (ObjectProperty.fullyFaithfulι _).map_injective
      ((derivedComapLeftDerivedUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
        p.left).hom.naturality f.hom))

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The restricted commutation of `Res` with the pullback is, on the underlying complexes,
`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso`. -/
lemma boundedConstructibleRestrictionUpperStarIso_hom_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    ((boundedConstructibleRestrictionUpperStarIso hX hY p).hom.app K).hom =
      (derivedComapLeftDerivedUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
        p.left).hom.app K.obj :=
  rfl

/-- **(Pull) is compatible with the units on bounded constructible complexes**, given that it is
on the full derived categories. -/
lemma boundedConstructibleUnitCompatible (hη : IntegersModPowPullUnitCompatible ℓ E n p.left)
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).map
        ((boundedConstructibleIntegersModPowAdjunction hY).unit.app M) ≫
      (boundedConstructibleRestrictionUpperStarIso hX hY p).hom.app
        ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M) =
    (boundedConstructibleIntegersModPowAdjunction hX).unit.app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).obj M) ≫
      (boundedConstructibleIntegersModPowRestriction hX).map
        ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n p).hom.app M) := by
  refine (ObjectProperty.fullyFaithfulι _).map_injective ?_
  have e₁ : ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).map
      ((boundedConstructibleIntegersModPowAdjunction hY).unit.app M)).hom =
      L((p.left)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowReduction Y.left ℓ E n)).unit.app M.obj) := by
    rw [← boundedConstructibleIntegersModPowAdjunction_unit_app_hom hY M]
    rfl
  have e₂ : ((boundedConstructibleIntegersModPowRestriction hX).map
      ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n p).hom.app M)).hom =
      (Mod.comap (integersModPowReduction X.left ℓ E n)).mapDerivedCategory.map
        ((integersModPowReductionUpperStarIso ℓ E n p.left).hom.app M.obj) := by
    rw [← boundedConstructibleUpperStarIntegersModPowReductionIso_hom_app_hom ℓ E n p M]
    rfl
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom]
  simp only [e₁, e₂, boundedConstructibleIntegersModPowAdjunction_unit_app_hom hX,
    boundedConstructibleRestrictionUpperStarIso_hom_app_hom]
  have h := hη M.obj
  exact h

/-- **The connecting morphisms commute with the pullback on bounded constructible complexes**,
given that they do on the full derived categories. -/
lemma boundedConstructibleδCompatible (hδ : IntegersModPowPullδCompatible ℓ E n p.left)
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).map
        ((boundedConstructibleIntegersModPowReductionδ hY).app M) ≫
      ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).commShiftIso
        (1 : ℤ)).hom.app M =
    (boundedConstructibleRestrictionUpperStarIso hX hY p).hom.app
        ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M) ≫
      (boundedConstructibleIntegersModPowRestriction hX).map
        ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n p).inv.app M) ≫
      (boundedConstructibleIntegersModPowReductionδ hX).app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).obj M) := by
  refine (ObjectProperty.fullyFaithfulι _).map_injective ?_
  have e₀ : ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).map
      ((boundedConstructibleIntegersModPowReductionδ hY).app M)).hom =
      L((p.left)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).map
        ((integersModPowReductionδ ℓ E n Y.left).app M.obj ≫
          ((boundedConstructible _).ι.commShiftIso (1 : ℤ)).inv.app M) :=
    rfl
  have e₁ : (((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).commShiftIso
      (1 : ℤ)).hom.app M).hom =
      (L((p.left)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).map
          (((boundedConstructible _).ι.commShiftIso (1 : ℤ)).hom.app M) ≫
        (L((p.left)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).commShiftIso (1 : ℤ)).hom.app M.obj) ≫
        ((boundedConstructible _).ι.commShiftIso (1 : ℤ)).inv.app
          ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).obj M) := by
    have := ObjectProperty.ι_map_lift_commShiftIso_hom_app _
      ((boundedConstructible _).ι ⋙ L((p.left)^*⟦Profinite.padicIntegersRingObj ℓ E⟧))
      (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ p K) (1 : ℤ) M
    rw [Functor.commShiftIso_comp_hom_app] at this
    exact this
  have e₂ : ((boundedConstructibleIntegersModPowRestriction hX).map
      ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n p).inv.app M)).hom =
      (Mod.comap (integersModPowReduction X.left ℓ E n)).mapDerivedCategory.map
        ((integersModPowReductionUpperStarIso ℓ E n p.left).inv.app M.obj) := by
    have := boundedConstructibleUpperStarIntegersModPowReductionIso_inv_app_hom ℓ E n p M
    exact congrArg (Mod.comap (integersModPowReduction X.left ℓ E n)).mapDerivedCategory.map
      this
  have h := hδ M.obj
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom]
  simp only [e₀, e₁, e₂, boundedConstructibleRestrictionUpperStarIso_hom_app_hom,
    boundedConstructibleIntegersModPowReductionδ_app_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.comp_id]
  have h' := h =≫ ((boundedConstructible _).ι.commShiftIso (1 : ℤ)).inv.app
    ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p).obj M)
  simp only [Category.assoc] at h'
  exact h'

/-- **Reduction modulo `ℓⁿ` commutes with `Rp^!` for a proper `p`**, on bounded constructible
condensed coefficients. Let `γ : Rp_* ⋙ red_Y ≅ red_X ⋙ Rp_*` be the pushforward comparison
(`boundedConstructibleLowerStarIntegersModPowReduction`), `Rp^!` the right adjoint of
`Rp_* ≅ Rp_!` on `Dᵇc(-)⟦𝒪_E⟧`, and `H'` any right adjoint of `Rp_*` on `Dᵇc(-)⟦𝒪_E ⧸ ℓⁿ⟧`. Then
the exceptional comparison `Rp^! ⋙ red_X ⟶ red_Y ⋙ H'`, the mate of `γ⁻¹`, is an isomorphism,
given the compatibilities of (Pull) with the natural reduction triangles and that restriction
of scalars preserves bounded constructible complexes on `X` and `Y`. -/
theorem isIso_mateEquiv_boundedConstructibleLowerStarIntegersModPowReduction [IsProper p.left]
    (hX : RestrictScalarsIntegersModPowBoundedConstructible ℓ E n X.left)
    (hY : RestrictScalarsIntegersModPowBoundedConstructible ℓ E n Y.left)
    (hη : IntegersModPowPullUnitCompatible ℓ E n p.left)
    (hδ : IntegersModPowPullδCompatible ℓ E n p.left)
    {H' : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤
      Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧}
    (adjH' : IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p ⊣ H')
    (γ : PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p ⋙
        boundedConstructibleIntegersModPowReduction Y.left ℓ E n ≅
      boundedConstructibleIntegersModPowReduction X.left ℓ E n ⋙
        IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p)
    (hγ : γ.hom = boundedConstructibleLowerStarIntegersModPowReduction ℓ E n p) :
    IsIso (mateEquiv
      ((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E p).ofNatIsoLeft
        (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p)) adjH' γ.inv) :=
  isIso_mateEquiv_mateEquiv_of_reductionTriangle' (boundedConstructibleIntegersModPowAdjunction hY)
    (boundedConstructibleIntegersModPowAdjunction hX)
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n p)
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n p)
    (boundedConstructibleRestrictionUpperStarIso hX hY p)
    (boundedConstructibleIntegersModPowReductionδ hY)
    (boundedConstructibleIntegersModPowReductionδ hX)
    _ adjH' ((ℓ : ℤ) ^ n) (boundedConstructibleIntegersModPowReduction_distinguished hY)
    (boundedConstructibleIntegersModPowReduction_distinguished hX)
    (boundedConstructibleUnitCompatible hX hY p hη) (boundedConstructibleδCompatible hX hY p hδ)
    γ hγ

end AlgebraicGeometry.ProEtale.CondensedRing
