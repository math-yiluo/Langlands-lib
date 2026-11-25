/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.TraceFormula.Specialization.ZeroSection
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!

# The geometric generic fibre of the deformation to the normal cone

Let `I` be an ideal sheaf on a `k`-scheme `X` and let `𝒳 = D_I X ×_{𝔸¹_k} Spec k'⟦t⟧` be the
deformation to the normal cone of `V(I)` over the trait
(`ProEtale.CondensedRing.deformationModel`). Over the punctured line `𝔾_m ⊆ 𝔸¹_k` the deformation
space is `X × 𝔾_m` (`IdealSheafData.isPullback_laurentSpecToDeformationSpace`), and the geometric
generic point `Spec Ω ⟶ Spec k'⟦t⟧ ⟶ 𝔸¹_k` lands in `𝔾_m`, since `t` is invertible in `Ω`. Hence
the geometric generic fibre of `𝒳` is the base change `X_Ω = X ×_k Spec Ω` of `X` along
`Spec Ω ⟶ Spec k`, with `ε : 𝒳_Ω ⟶ X` the first projection
(`ProEtale.CondensedRing.isPullback_deformationModel_ε`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The geometric generic point `Spec Ω ⟶ Spec k'⟦t⟧ ⟶ 𝔸¹_k` lies in the punctured line: the
coordinate `t` is a nonzero element of the field `Ω`. -/
noncomputable def traitGenericPointToPuncturedLine :
    Spec (.of (traitGenericField k')) ⟶ Scheme.Hom.puncturedLine (Spec (.of k)) :=
  IsOpenImmersion.lift (Scheme.Hom.puncturedLine (Spec (.of k))).ι
    (traitGenericPoint k' ≫ traitToAffineLine k k') (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      change y ∈ (traitGenericPoint k' ≫ traitToAffineLine k k') ⁻¹ᵁ
        Scheme.Hom.puncturedLine (Spec (.of k))
      rw [Scheme.preimage_basicOpen_top, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        traitToAffineLine, AffineSpace.homOfVector_appTop_coord, traitGenericPoint,
        ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
        Scheme.basicOpen_of_isUnit]
      · trivial
      refine IsUnit.map _ (Ne.isUnit ?_)
      change algebraMap (PowerSeries k') (traitGenericField k') PowerSeries.X ≠ 0
      rw [IsScalarTower.algebraMap_apply (PowerSeries k') (FractionRing (PowerSeries k'))]
      refine (map_ne_zero _).2 ?_
      exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero)))

@[reassoc (attr := simp)]
lemma traitGenericPointToPuncturedLine_ι :
    traitGenericPointToPuncturedLine k k' ≫ (Scheme.Hom.puncturedLine (Spec (.of k))).ι =
      traitGenericPoint k' ≫ traitToAffineLine k k' :=
  IsOpenImmersion.lift_fac _ _ _

namespace ProEtale.CondensedRing

open Scheme

variable {k} {X : Over (Spec (.of k))}

/-- The structure morphism `𝒳_Ω ⟶ Spec Ω` of the geometric generic fibre of the deformation to
the normal cone over the trait. -/
noncomputable def deformationGenericToPoint (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
    (k' : Type u) [Field k'] [Algebra k k'] :
    deformationGeneric X I k' ⟶ Spec (.of (traitGenericField k')) :=
  pullback.snd _ _

/-- Over the punctured line, `D_I X ⟶ X` is the projection `𝔾_{m,X} ⟶ X`. -/
lemma laurentSpecToDeformationSpace_deformationSpaceProj (I : X.left.IdealSheafData) :
    I.laurentSpecToDeformationSpace ≫ I.deformationSpaceProj =
      X.left.laurentSpecToPolynomialSpec ≫ X.left.polynomialSpecProj := by
  rw [IdealSheafData.laurentSpecToDeformationSpace,
    AffineZariskiSite.relativeGluingMap_toBase _ _ _ I.toReesPresheaf_comp_reesToLaurent,
    Scheme.laurentSpecToPolynomialSpec, AffineZariskiSite.relativeGluingMap_toBase _ _ _
      IdealSheafData.toPolynomialPresheaf_comp_polynomialToLaurent]

/-- **The geometric generic fibre of the deformation to the normal cone is the base change of
`X`**: for any ideal sheaf `I`, the square formed by `ε : 𝒳_Ω ⟶ X`, the structure morphisms
`𝒳_Ω ⟶ Spec Ω` and `X ⟶ Spec k`, and `Spec Ω ⟶ Spec k'⟦t⟧ ⟶ Spec k`, is a pullback. Over the
punctured line the deformation space is `𝔾_{m,X}`, and the geometric generic point of the trait
lies over the punctured line. -/
theorem isPullback_deformationModel_ε (I : X.left.IdealSheafData) :
    IsPullback (deformationModel X I k').ε (deformationGenericToPoint X I k') X.hom
      (traitGenericPoint k' ≫ traitToBase k k') := by
  have hL : IsPullback I.laurentSpecToDeformationSpace
      (Scheme.Hom.laurentSpecToPuncturedLine X.hom) (deformationSpaceToAffineLine X I)
      (Scheme.Hom.puncturedLine _).ι := by
    have := I.isPullback_laurentSpecToDeformationSpace.paste_vert
      (Scheme.Hom.isPullback_laurentSpecToPuncturedLine X.hom)
    rwa [Category.id_comp] at this
  have hG := (IsPullback.of_hasPullback (deformationTotalToTrait X I k')
    (traitGenericPoint k')).paste_horiz (isPullback_deformationTotal X I k')
  rw [← traitGenericPointToPuncturedLine_ι] at hG
  have h := (IsPullback.of_right' hG hL).paste_horiz (Scheme.Hom.isPullback_laurentSpec X.hom)
  have e : traitGenericPointToPuncturedLine k k' ≫ (Scheme.Hom.puncturedLine _).ι ≫
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) = traitGenericPoint k' ≫ traitToBase k k' :=
    by rw [traitGenericPointToPuncturedLine_ι_assoc, traitToAffineLine_over]
  rw [e, ← laurentSpecToDeformationSpace_deformationSpaceProj, ← Category.assoc,
    IsPullback.lift_fst, Category.assoc] at h
  exact h

end ProEtale.CondensedRing

end AlgebraicGeometry
