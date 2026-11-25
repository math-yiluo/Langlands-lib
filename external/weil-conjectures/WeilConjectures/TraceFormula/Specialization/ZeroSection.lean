/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.TraceFormula.Specialization.DeformationModelNormalCone

/-!

# The zero section of the deformation to the normal cone of a rational point

Let `x` be a rational point of a `k`-scheme `X`, with ideal `I = ker x`, and let
`𝒳 = D_I X ×_{𝔸¹_k} S` be the deformation to the normal cone of `x` over the trait
`S = Spec k'⟦t⟧` (`ProEtale.CondensedRing.deformationModel`). The section of the deformation space
over `𝔸¹_k` given by `x` (`Scheme.Hom.deformationSpaceSection`) base changes to a section
`ẽ : S ⟶ 𝒳` of `𝒳 ⟶ S` (`ProEtale.CondensedRing.deformationZeroSectionTotal`), the closed
immersion `Z × S ⟶ 𝒟_Z X` of blueprint `prose-E-04` for `Z = x`. Its special fibre is
the zero section `e` of the special fibre `N_x X ⊗ k'`
(`ProEtale.CondensedRing.deformationSpecialFibreZeroSection`).

The trait itself is a model of the point `Spec k` with special fibre the zero locus of `N_x X ⊗ k'`
(`ProEtale.CondensedRing.zeroSectionModel`), and `ẽ` is a morphism of models over `x` and `e`
(`ProEtale.CondensedRing.zeroSectionModelHom`). Its pullback exchange
`α : Le^* Ψ_𝒳 ⟶ Ψ_S Lx^*` is the first half of the zero-section map `ε_{X,x}` of blueprint
`prose-E-04`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme AffineZariskiSite

/-- The projection `Z₀ ⟶ V(I)` of the zero locus of the special fibre to the closed subscheme
`V(I)`. -/
noncomputable def deformationSpecialZeroLocusToQuotientSpec {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k'] :
    (deformationSpecialZeroLocus X I k').left ⟶ I.quotientSpec :=
  pullback.snd _ _

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (x : RationalPoint X)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The coordinate `t` of the deformation space of `ker x` is the projection of the deformation
space of the section `x` of the structure morphism. -/
lemma deformationSpaceToAffineLine_eq :
    deformationSpaceToAffineLine X x.left.ker = Scheme.Hom.deformationSpaceProj X.hom x.left :=
  rfl

/-- The section `ẽ : S ⟶ 𝒳` of the total space of the deformation to the normal cone of the
rational point `x` over the trait: the base change of the section `𝔸¹_k ⟶ D_x X` given by `x`
(blueprint `prose-E-04`, the closed immersion `Z × S ⟶ 𝒟_Z X` for `Z = x`). -/
noncomputable def deformationZeroSectionTotal : trait k' ⟶ deformationTotal X x.left.ker k' :=
  pullback.lift (traitToAffineLine k k' ≫ x.left.deformationSpaceSection) (𝟙 _) (by
    rw [Category.assoc, deformationSpaceToAffineLine_eq,
      Scheme.Hom.deformationSpaceSection_deformationSpaceProj (Over.w x)]
    simp)

@[reassoc (attr := simp)]
lemma deformationZeroSectionTotal_toSpace :
    deformationZeroSectionTotal X x k' ≫ deformationTotalToSpace X x.left.ker k' =
      traitToAffineLine k k' ≫ x.left.deformationSpaceSection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationZeroSectionTotal_toTrait :
    deformationZeroSectionTotal X x k' ≫ deformationTotalToTrait X x.left.ker k' = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The section `ẽ` lies over the constant map `S ⟶ Spec k ⟶ X` at `x`. -/
@[reassoc (attr := simp)]
lemma deformationZeroSectionTotal_toBase :
    deformationZeroSectionTotal X x k' ≫ deformationTotalToBase X x.left.ker k' =
      traitToBase k k' ≫ x.left := by
  rw [deformationTotalToBase, deformationZeroSectionTotal_toSpace_assoc,
    Scheme.Hom.deformationSpaceSection_toBase]
  exact traitToAffineLine_over_assoc k k' x.left

/-- The zero locus maps to `V(I)` compatibly with the inclusion into the special fibre. -/
@[reassoc]
lemma deformationSpecialZeroLocusToQuotientSpec_normalConeZeroSection (I : X.left.IdealSheafData) :
    deformationSpecialZeroLocusToQuotientSpec X I k' ≫ I.normalConeZeroSection =
      (deformationSpecialFibreZeroSection X I k').left ≫
        deformationSpecialFibreToNormalCone X I k' :=
  pullback.condition.symm

/-- The special fibre maps to `X` through the normal cone. -/
@[reassoc]
lemma deformationSpecialFibreToNormalCone_toBase (I : X.left.IdealSheafData) :
    deformationSpecialFibreToNormalCone X I k' ≫
        (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase =
      deformationSpecialToTotal X I k' ≫ deformationTotalToBase X I k' := by
  rw [← IdealSheafData.normalConeToDeformationSpace_deformationSpaceProj]
  change _ = (deformationModel X I k').i ≫ deformationTotalToSpace X I k' ≫ _
  rw [deformationSpecialFibreToNormalCone_normalConeToDeformationSpace_assoc]

/-- The map `Z₀ ⟶ V(I)` from the zero locus of the special fibre to the closed subscheme `V(I)` of
the point `x` factors through the structure morphism `Z₀ ⟶ Spec k' ⟶ Spec k`. -/
lemma deformationSpecialZeroLocusToQuotientSpec_eq :
    deformationSpecialZeroLocusToQuotientSpec X x.left.ker k' =
      (deformationSpecialZeroLocus X x.left.ker k').hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ x.left.toQuotientSpec := by
  have : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  -- maps into `V(I)` are determined by their composites to `Spec k`, since `V(I) ≅ Spec k`
  have hq : (relativeGluingData x.left.ker.coequifibered_toQuotientAlgebra).toBase ≫ X.hom =
      inv x.left.toQuotientSpec := by
    refine IsIso.eq_inv_of_hom_inv_id ?_
    rw [← Category.assoc, Scheme.Hom.toQuotientSpec_toBase]
    exact Over.w x
  refine (cancel_mono (inv x.left.toQuotientSpec)).1 ?_
  rw [Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id, ← hq,
    ← IdealSheafData.normalConeZeroSection_toBase, Category.assoc,
    deformationSpecialZeroLocusToQuotientSpec_normalConeZeroSection_assoc,
    deformationSpecialFibreToNormalCone_toBase_assoc, deformationTotalToBase_hom,
    reassoc_of% (isPullback_deformationSpecialFibre X x.left.ker k').w,
    traitClosedPoint_traitToBase]
  rfl

/-- The special fibre of the section `ẽ`: the zero section `e : Z₀ ⟶ N_x X ⊗ k'` followed by the
inclusion of the special fibre is the structure morphism `Z₀ ⟶ Spec k' ⟶ S` followed by `ẽ`. -/
lemma deformationSpecialFibreZeroSection_toTotal :
    (deformationSpecialFibreZeroSection X x.left.ker k').left ≫
        deformationSpecialToTotal X x.left.ker k' =
      ((deformationSpecialZeroLocus X x.left.ker k').hom ≫ traitClosedPoint k') ≫
        deformationZeroSectionTotal X x k' := by
  refine pullback.hom_ext ?_ ?_
  · change _ ≫ (deformationModel X x.left.ker k').i ≫ deformationTotalToSpace X x.left.ker k' =
      _ ≫ deformationZeroSectionTotal X x k' ≫ deformationTotalToSpace X x.left.ker k'
    rw [deformationZeroSectionTotal_toSpace,
      ← deformationSpecialFibreToNormalCone_normalConeToDeformationSpace,
      ← deformationSpecialZeroLocusToQuotientSpec_normalConeZeroSection_assoc,
      deformationSpecialZeroLocusToQuotientSpec_eq]
    simp only [Category.assoc]
    rw [traitClosedPoint_traitToAffineLine_assoc,
      ← Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace]
    rfl
  · change _ ≫ deformationSpecialToTotal X x.left.ker k' ≫ deformationTotalToTrait X x.left.ker k' =
      _ ≫ deformationZeroSectionTotal X x k' ≫ deformationTotalToTrait X x.left.ker k'
    rw [deformationZeroSectionTotal_toTrait, Category.comp_id,
      (isPullback_deformationSpecialFibre X x.left.ker k').w, ← Category.assoc,
      Over.w (deformationSpecialFibreZeroSection X x.left.ker k')]

/-- The geometric generic fibre `Spec Ω ⟶ 𝒳_Ω` of the section `ẽ`. -/
noncomputable def deformationZeroSectionGeneric :
    Spec (.of (traitGenericField k')) ⟶ deformationGeneric X x.left.ker k' :=
  pullback.lift (traitGenericPoint k' ≫ deformationZeroSectionTotal X x k') (𝟙 _) (by
    rw [Category.assoc, deformationZeroSectionTotal_toTrait, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma deformationZeroSectionGeneric_toTotal :
    deformationZeroSectionGeneric X x k' ≫ deformationGenericToTotal X x.left.ker k' =
      traitGenericPoint k' ≫ deformationZeroSectionTotal X x k' :=
  pullback.lift_fst _ _ _

/-- The trait `S = Spec k'⟦t⟧` as a model of the point `Spec k`, with special fibre the zero locus
`Z₀` of the special fibre `N_I X ⊗ k'` of the deformation to the normal cone: the *constant
family* `Z × S` of blueprint `lemma-nearby-cycles-constant-family` for `Z = Spec k`. -/
noncomputable def zeroSectionModel (I : X.left.IdealSheafData) :
    NearbyCyclesModel (point k).left (deformationSpecialZeroLocus X I k').left where
  total := trait k'
  generic := Spec (.of (traitGenericField k'))
  j := traitGenericPoint k'
  i := (deformationSpecialZeroLocus X I k').hom ≫ traitClosedPoint k'
  ε := traitGenericPoint k' ≫ traitToBase k k'

/-- The section `ẽ : S ⟶ 𝒳` as a morphism of models from the constant family of the point to the
deformation to the normal cone of `x`, over `x` and the zero section `e` of the special fibre. -/
noncomputable def zeroSectionModelHom :
    (zeroSectionModel X k' x.left.ker).Hom (deformationModel X x.left.ker k') x.left
      (deformationSpecialFibreZeroSection X x.left.ker k').left where
  total := deformationZeroSectionTotal X x k'
  generic := deformationZeroSectionGeneric X x k'
  comm_j := deformationZeroSectionGeneric_toTotal X x k'
  comm_i := deformationSpecialFibreZeroSection_toTotal X x k'
  comm_ε := by
    change deformationZeroSectionGeneric X x k' ≫ deformationGenericToTotal X x.left.ker k' ≫
      deformationTotalToBase X x.left.ker k' = (traitGenericPoint k' ≫ traitToBase k k') ≫ x.left
    rw [deformationZeroSectionGeneric_toTotal_assoc, deformationZeroSectionTotal_toBase,
      Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
