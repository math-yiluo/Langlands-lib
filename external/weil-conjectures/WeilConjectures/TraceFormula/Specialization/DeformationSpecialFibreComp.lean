/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationModel

/-!

# Functoriality of the morphisms of deformations

The morphisms of deformation spaces `D_J X' ⟶ D_I X` compose for arbitrary morphisms of schemes
(`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceMap_comp`), not only over open
immersions; hence so do the morphisms of total spaces and of special fibres of the deformation
models (`ProEtale.CondensedRing.deformationTotalMap_comp`,
`ProEtale.CondensedRing.deformationSpecialFibreMap_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.AffineZariskiSite

variable {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)
  (P : X.AffineZariskiSite → Prop) (hP : ∀ x : X, ∃ U, P U ∧ x ∈ U.1)

/-- The open cover of the relative spectrum `Spec_X F` by the charts `Spec F(U)` for the affine
opens `U` satisfying a property `P`, provided these opens cover `X`. -/
noncomputable def coverOfProp : (relativeGluingData H).glued.OpenCover where
  I₀ := {U // P U}
  X U := (relativeGluingData H).functor.obj U.1
  f U := colimit.ι (relativeGluingData H).functor U.1
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun z ↦ ?_, fun U ↦ (relativeGluingData H).cover.map_prop U.1⟩
    obtain ⟨U, hU, hz⟩ := hP ((relativeGluingData H).toBase z)
    refine ⟨⟨U, hU⟩, ?_⟩
    have hz' : z ∈ (relativeGluingData H).toBase ⁻¹ᵁ U.1 := hz
    rw [toBase_preimage] at hz'
    exact hz'

include hP in
/-- Two morphisms out of the relative spectrum `Spec_X F` agree if they agree on the charts
`Spec F(U)` for the affine opens `U` satisfying a property `P`, provided these cover `X`. -/
lemma hom_ext_of_prop {Y : Scheme.{u}} {f g : (relativeGluingData H).glued ⟶ Y}
    (hfg : ∀ U, P U → colimit.ι (relativeGluingData H).functor U ≫ f =
      colimit.ι (relativeGluingData H).functor U ≫ g) : f = g :=
  (coverOfProp H P hP).hom_ext _ _ fun U ↦ hfg U.1 U.2

end Scheme.AffineZariskiSite

/-- The morphisms of deformation spaces compose. -/
lemma Scheme.IdealSheafData.deformationSpaceMap_comp
    {X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    {I₃ : X₃.IdealSheafData} {I₂ : X₂.IdealSheafData} {I₁ : X₁.IdealSheafData}
    (hf : ∀ ⦃U' : X₁.AffineZariskiSite⦄ ⦃U : X₂.AffineZariskiSite⦄ (hU : U'.1 ≤ f ⁻¹ᵁ U.1),
      (I₂.siteIdeal U).map (f.appLE U.1 U'.1 hU).hom ≤ I₁.siteIdeal U')
    (hg : ∀ ⦃U' : X₂.AffineZariskiSite⦄ ⦃U : X₃.AffineZariskiSite⦄ (hU : U'.1 ≤ g ⁻¹ᵁ U.1),
      (I₃.siteIdeal U).map (g.appLE U.1 U'.1 hU).hom ≤ I₂.siteIdeal U')
    (hfg : ∀ ⦃U' : X₁.AffineZariskiSite⦄ ⦃U : X₃.AffineZariskiSite⦄
      (hU : U'.1 ≤ (f ≫ g) ⁻¹ᵁ U.1),
      (I₃.siteIdeal U).map ((f ≫ g).appLE U.1 U'.1 hU).hom ≤ I₁.siteIdeal U') :
    IdealSheafData.deformationSpaceMap f I₂ I₁ hf ≫ IdealSheafData.deformationSpaceMap g I₃ I₂ hg =
      IdealSheafData.deformationSpaceMap (f ≫ g) I₃ I₁ hfg := by
  refine AffineZariskiSite.hom_ext_of_prop I₁.coequifibered_toReesPresheaf
    (fun U₁ ↦ ∃ (U₂ : X₂.AffineZariskiSite) (U₃ : X₃.AffineZariskiSite),
      U₁.1 ≤ f ⁻¹ᵁ U₂.1 ∧ U₂.1 ≤ g ⁻¹ᵁ U₃.1) (fun x ↦ ?_) fun U₁ ⟨U₂, U₃, h₁, h₂⟩ ↦ ?_
  · obtain ⟨U₃, hU₃, hx₃, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X₃.isBasis_affineOpens (show g (f x) ∈ (⊤ : X₃.Opens) from trivial)
    obtain ⟨U₂, hU₂, hx₂, h₂⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X₂.isBasis_affineOpens (show f x ∈ g ⁻¹ᵁ U₃ from hx₃)
    obtain ⟨U₁, hU₁, hx₁, h₁⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X₁.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U₂ from hx₂)
    exact ⟨⟨U₁, hU₁⟩, ⟨⟨U₂, hU₂⟩, ⟨U₃, hU₃⟩, h₁, h₂⟩, hx₁⟩
  have hU : U₁.1 ≤ (f ≫ g) ⁻¹ᵁ U₃.1 := fun x hx ↦ by
    have := h₂ (h₁ hx)
    simpa using this
  rw [IdealSheafData.deformationSpaceMap, IdealSheafData.deformationSpaceMap,
    IdealSheafData.deformationSpaceMap, AffineZariskiSite.PullbackData.ι_comparison_assoc _ _ _ h₁,
    AffineZariskiSite.PullbackData.ι_comparison _ _ _ h₂,
    AffineZariskiSite.PullbackData.ι_comparison _ _ _ hU, ← Spec.map_comp_assoc]
  congr 2
  ext : 1
  simp only [IdealSheafData.extendedReesPullbackData_map, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom]
  rw [Ideal.extendedReesAlgebraMap_comp]
  congr 1
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

namespace ProEtale.CondensedRing

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  {X Y Z : Over (Spec (.of k))} (f : X ⟶ Y) (g : Y ⟶ Z)
  {I₃ : Z.left.IdealSheafData} {I₂ : Y.left.IdealSheafData} {I₁ : X.left.IdealSheafData}
  (hf : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I₂.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      I₁.siteIdeal U')
  (hg : ∀ ⦃U' : Y.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ g.left ⁻¹ᵁ U.1), (I₃.siteIdeal U).map (g.left.appLE U.1 U'.1 hU).hom ≤
      I₂.siteIdeal U')
  (hfg : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ (f ≫ g).left ⁻¹ᵁ U.1),
    (I₃.siteIdeal U).map ((f ≫ g).left.appLE U.1 U'.1 hU).hom ≤
      I₁.siteIdeal U')

/-- The morphisms of total spaces of deformation models compose. -/
lemma deformationTotalMap_comp :
    deformationTotalMap f hf k' ≫ deformationTotalMap g hg k' =
      deformationTotalMap (f ≫ g) hfg k' := by
  apply pullback.hom_ext
  · change _ ≫ deformationTotalToSpace _ _ k' = _ ≫ deformationTotalToSpace _ _ k'
    rw [Category.assoc, deformationTotalMap_toSpace, deformationTotalMap_toSpace_assoc,
      deformationTotalMap_toSpace]
    exact congrArg (deformationTotalToSpace X I₁ k' ≫ ·)
      (Scheme.IdealSheafData.deformationSpaceMap_comp f.left g.left hf hg hfg)
  · change _ ≫ deformationTotalToTrait _ _ k' = _ ≫ deformationTotalToTrait _ _ k'
    rw [Category.assoc, deformationTotalMap_toTrait, deformationTotalMap_toTrait,
      deformationTotalMap_toTrait]

/-- The morphisms of special fibres of deformation models compose. -/
lemma deformationSpecialFibreMap_comp :
    deformationSpecialFibreMap f hf k' ≫ deformationSpecialFibreMap g hg k' =
      deformationSpecialFibreMap (f ≫ g) hfg k' := by
  ext1
  apply pullback.hom_ext
  · change _ ≫ deformationSpecialToTotal _ _ k' = _ ≫ deformationSpecialToTotal _ _ k'
    rw [Over.comp_left, Category.assoc, deformationSpecialFibreMap_toTotal,
      deformationSpecialFibreMap_toTotal_assoc, deformationTotalMap_comp,
      deformationSpecialFibreMap_toTotal]
  · change _ ≫ (deformationSpecialFibre Z I₃ k').hom = _ ≫ (deformationSpecialFibre Z I₃ k').hom
    simp only [Over.w]

/-- The morphism of special fibres depends only on the underlying morphism. -/
lemma deformationSpecialFibreMap_eq_of_eq {f' : X ⟶ Y} (e : f = f')
    (hf' : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f'.left ⁻¹ᵁ U.1), (I₂.siteIdeal U).map (f'.left.appLE U.1 U'.1 hU).hom ≤
        I₁.siteIdeal U') :
    deformationSpecialFibreMap f hf k' = deformationSpecialFibreMap f' hf' k' := by
  subst e
  rfl

end ProEtale.CondensedRing

end AlgebraicGeometry
