/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationModel
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!

# The special fibre of a deformation model and the normal cone

The coordinate `t` vanishes on the special fibre `𝒳_s` of the deformation model
`𝒳 = D_I X ×_{𝔸¹_k} Spec k'⟦t⟧`, so `𝒳_s ⟶ D_I X` factors through the normal cone
`N_I X = D_I X ×_{𝔸¹_X} X` (`AlgebraicGeometry.ProEtale.CondensedRing
.deformationSpecialFibreToNormalCone`), naturally in `(X, I)`. The preimage of the zero section
`V(I) ⟶ N_I X` is the *zero section of the special fibre*
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationSpecialFibreZeroSection`), a closed
subscheme of `𝒳_s`. If the morphism of normal cones induced by `f : X ⟶ Y` lands in the zero
section (blueprint `lemma-normal-cones-contracting-ideals` (2)), so does the morphism of special
fibres (`AlgebraicGeometry.ProEtale.CondensedRing.range_deformationSpecialFibreMap_subset`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme AffineZariskiSite

section NormalCone

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The coordinate `t` vanishes on the special fibre: `𝒳_s ⟶ D_I X ⟶ 𝔸¹_X` factors through the
zero section of `𝔸¹_X`. -/
lemma deformationSpecialToTotal_toPolynomialSpec :
    deformationSpecialToTotal X I k' ≫ deformationTotalToSpace X I k' ≫
        I.deformationSpaceToPolynomialSpec =
      (deformationSpecialToTotal X I k' ≫ deformationTotalToBase X I k') ≫
        X.left.polynomialSpecZeroSection := by
  have hproj : I.deformationSpaceToPolynomialSpec ≫ X.left.polynomialSpecProj =
      I.deformationSpaceProj := by
    rw [IdealSheafData.deformationSpaceToPolynomialSpec,
      relativeGluingMap_toBase _ _ _ I.toPolynomialPresheaf_comp_polynomialToRees]
  rw [← cancel_mono X.left.polynomialSpecToAffineSpace]
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · simp only [Category.assoc, polynomialSpecToAffineSpace_over,
      polynomialSpecZeroSection_comp_polynomialSpecToAffineSpace, AffineSpace.zeroSection_over,
      Category.comp_id, deformationTotalToBase, hproj]
  · have e : (deformationSpecialToTotal X I k' ≫ deformationTotalToSpace X I k' ≫
        I.deformationSpaceToPolynomialSpec ≫ X.left.polynomialSpecToAffineSpace) ≫
          AffineSpace.map _ X.hom =
        (deformationSpecialFibre X I k').hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫
          AffineSpace.zeroSection _ _ := by
      simp only [Category.assoc]
      change deformationSpecialToTotal X I k' ≫ deformationTotalToSpace X I k' ≫
        deformationSpaceToAffineLine X I = _
      rw [(isPullback_deformationTotal X I k').w,
        reassoc_of% (isPullback_deformationSpecialFibre X I k').w,
        traitClosedPoint_traitToAffineLine]
    have h := congrArg (fun g ↦ g.appTop (AffineSpace.coord (Spec (.of k)) i)) e
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
      AffineSpace.zeroSection_appTop_coord, map_zero] at h
    simp only [Category.assoc, polynomialSpecZeroSection_comp_polynomialSpecToAffineSpace,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.zeroSection_appTop_coord,
      map_zero]
    exact h

/-- The special fibre of the deformation model maps to the normal cone `N_I X`, since the
coordinate `t` vanishes on it. -/
noncomputable def deformationSpecialFibreToNormalCone :
    (deformationSpecialFibre X I k').left ⟶ I.normalCone :=
  I.isPullback_normalConeToDeformationSpace.lift
    (deformationSpecialToTotal X I k' ≫ deformationTotalToSpace X I k')
    ((deformationSpecialToTotal X I k' ≫ deformationTotalToBase X I k') ≫
      inv (relativeGluingData X.left.coequifibered_toPolynomialZeroPresheaf).toBase)
    (by
      rw [Category.assoc, deformationSpecialToTotal_toPolynomialSpec, polynomialSpecZeroSection]
      simp only [Category.assoc])

/-- The map of the special fibre to the normal cone is the restriction of `𝒳 ⟶ D_I X`. -/
@[reassoc (attr := simp)]
lemma deformationSpecialFibreToNormalCone_normalConeToDeformationSpace :
    deformationSpecialFibreToNormalCone X I k' ≫ I.normalConeToDeformationSpace =
      (deformationModel X I k').i ≫ deformationTotalToSpace X I k' :=
  I.isPullback_normalConeToDeformationSpace.lift_fst _ _ _

variable {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
  {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')

/-- The map of special fibres to normal cones is natural. -/
@[reassoc]
lemma deformationSpecialFibreMap_toNormalCone :
    (deformationSpecialFibreMap f hJ k').left ≫ deformationSpecialFibreToNormalCone Y I k' =
      deformationSpecialFibreToNormalCone X J k' ≫
        IdealSheafData.normalConeMap f.left I J hJ := by
  rw [← cancel_mono I.normalConeToDeformationSpace, Category.assoc, Category.assoc,
    deformationSpecialFibreToNormalCone_normalConeToDeformationSpace,
    IdealSheafData.normalConeMap_normalConeToDeformationSpace,
    deformationSpecialFibreToNormalCone_normalConeToDeformationSpace_assoc]
  simp only [deformationModel_i, deformationSpecialFibreMap_toTotal_assoc,
    deformationTotalMap_toSpace]

end NormalCone

/-! ### The zero section of the special fibre -/

section ZeroSection

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The zero locus of the special fibre: the preimage `𝒳_s ×_{N_I X} V(I)` of the zero section of
the normal cone, as a `k'`-scheme. -/
noncomputable def deformationSpecialZeroLocus : Over (Spec (.of k')) :=
  Over.mk (pullback.fst (deformationSpecialFibreToNormalCone X I k') I.normalConeZeroSection ≫
    (deformationSpecialFibre X I k').hom)

/-- The zero section of the special fibre, the inclusion of the preimage of the zero section of
the normal cone. -/
noncomputable def deformationSpecialFibreZeroSection :
    deformationSpecialZeroLocus X I k' ⟶ deformationSpecialFibre X I k' :=
  Over.homMk (pullback.fst _ _) rfl

instance : IsClosedImmersion (deformationSpecialFibreZeroSection X I k').left :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (deformationSpecialZeroLocus X I k').hom :=
  inferInstanceAs (LocallyOfFiniteType ((deformationSpecialFibreZeroSection X I k').left ≫
    (deformationSpecialFibre X I k').hom))

instance [QuasiCompact X.hom] : QuasiCompact (deformationSpecialZeroLocus X I k').hom :=
  inferInstanceAs (QuasiCompact ((deformationSpecialFibreZeroSection X I k').left ≫
    (deformationSpecialFibre X I k').hom))

instance [IsSeparated X.hom] : IsSeparated (deformationSpecialZeroLocus X I k').hom :=
  inferInstanceAs (IsSeparated ((deformationSpecialFibreZeroSection X I k').left ≫
    (deformationSpecialFibre X I k').hom))

/-- The zero section of the special fibre is the preimage of the zero section of the normal
cone. -/
lemma range_deformationSpecialFibreZeroSection :
    Set.range (deformationSpecialFibreZeroSection X I k').left =
      deformationSpecialFibreToNormalCone X I k' ⁻¹' Set.range I.normalConeZeroSection :=
  Scheme.Pullback.range_fst _ _

variable {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
  {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')

/-- If the morphism of normal cones induced by `f` lands in the zero section, so does the morphism
of special fibres of the deformation models. -/
theorem range_deformationSpecialFibreMap_subset
    (h : Set.range (IdealSheafData.normalConeMap f.left I J hJ) ⊆
      Set.range I.normalConeZeroSection) :
    Set.range (deformationSpecialFibreMap f hJ k').left ⊆
      Set.range (deformationSpecialFibreZeroSection Y I k').left := by
  rw [range_deformationSpecialFibreZeroSection]
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, deformationSpecialFibreMap_toNormalCone,
    Scheme.Hom.comp_apply]
  exact h ⟨_, rfl⟩

end ZeroSection

end AlgebraicGeometry.ProEtale.CondensedRing
