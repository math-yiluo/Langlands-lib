/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# The tower of finite Galois subextensions as a limit of schemes

Let `Ω / L` be a (possibly infinite) Galois extension. This file proves that `Ω` is the filtered
colimit of its finite Galois subextensions `L'` in `CommRingCat`
(`FiniteGaloisIntermediateField.isColimitRingCocone`), hence that `Spec Ω` is the cofiltered
limit of the `Spec L'` (`FiniteGaloisIntermediateField.isLimitSpecCone`).

Base change along a fixed morphism preserves limits of connected diagrams over a base
(`CategoryTheory.Limits.isLimitPullbackDiagramCone`), so for a scheme `G` over `Spec L`,
`G ×_L Ω = lim_{L'} G ×_L L'` (`AlgebraicGeometry.isLimitGaloisLevelCone`), and likewise for any
further base change `W ×_G (G ×_L Ω) = lim_{L'} W ×_G (G ×_L L')`.
-/

@[expose] public section

universe v w u

open CategoryTheory Limits Opposite

/-! ### Base change of a limit cone over a base -/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {I : Type*} [Category I] {D : I ⥤ C} {S T : C} (f : T ⟶ S)
  (p : D ⟶ (Functor.const I).obj S) [∀ i, HasPullback f (p.app i)]

/-- The base change `i ↦ T ×_S D i` of a diagram `D` over `S` along `f : T ⟶ S`. -/
@[simps]
noncomputable def pullbackDiagram : I ⥤ C where
  obj i := pullback f (p.app i)
  map {i j} φ := pullback.map f (p.app i) f (p.app j) (𝟙 T) (D.map φ) (𝟙 S) (by simp)
    (by simp)
  map_id i := by
    apply pullback.hom_ext <;> simp
  map_comp φ ψ := by
    apply pullback.hom_ext <;> simp

/-- The projections `T ×_S D i ⟶ T`. -/
@[simps]
noncomputable def pullbackDiagramFst : pullbackDiagram f p ⟶ (Functor.const I).obj T where
  app i := pullback.fst _ _

variable (c : Cone D) (q : c.pt ⟶ S) (hq : ∀ i, c.π.app i ≫ p.app i = q) [HasPullback f q]

/-- The base change `T ×_S c.pt ⟶ T ×_S D i` of a cone `c` over `D`, for a morphism
`q : c.pt ⟶ S` compatible with the structure maps of `D`. -/
@[simps]
noncomputable def pullbackDiagramCone : Cone (pullbackDiagram f p) where
  pt := pullback f q
  π :=
    { app i := pullback.map f q f (p.app i) (𝟙 T) (c.π.app i) (𝟙 S) (by simp) (by simp [hq])
      naturality i j φ := by
        apply pullback.hom_ext <;> simp }

/-- **Base change preserves connected limits over a base**: if `c` is a limit cone of a diagram
`D` over `S` indexed by a connected category, then `T ×_S c.pt` is the limit of the `T ×_S D i`. -/
noncomputable def isLimitPullbackDiagramCone [IsConnected I] (hc : IsLimit c) :
    IsLimit (pullbackDiagramCone f p c q hq) := by
  let i₀ : I := Classical.arbitrary I
  have hfst (s : Cone (pullbackDiagram f p)) (i : I) :
      s.π.app i ≫ pullback.fst _ _ = s.π.app i₀ ≫ pullback.fst _ _ := by
    refine constant_of_preserves_morphisms (fun i ↦ s.π.app i ≫ pullback.fst _ _)
      (fun j₁ j₂ φ ↦ ?_) i i₀
    rw [← s.w φ]
    simp
  let lift₂ (s : Cone (pullbackDiagram f p)) : s.pt ⟶ c.pt :=
    hc.lift ⟨s.pt,
      { app i := s.π.app i ≫ pullback.snd _ _
        naturality i j φ := by
          rw [← s.w φ]
          simp }⟩
  have hlift₂ (s : Cone (pullbackDiagram f p)) (i : I) :
      lift₂ s ≫ c.π.app i = s.π.app i ≫ pullback.snd _ _ :=
    hc.fac _ i
  refine
    { lift s := pullback.lift (s.π.app i₀ ≫ pullback.fst _ _) (lift₂ s) ?_
      fac s i := ?_
      uniq s m hm := ?_ }
  · rw [Category.assoc, pullback.condition, ← hq i₀, reassoc_of% hlift₂]
  · apply pullback.hom_ext
    · simp [hfst s i]
    · simp [hlift₂]
  · apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hm i₀]
      simp
    · rw [pullback.lift_snd]
      refine hc.hom_ext fun i ↦ ?_
      rw [hlift₂, ← hm i]
      simp

end CategoryTheory.Limits

/-! ### `Ω` as the colimit of its finite Galois subextensions -/

namespace FiniteGaloisIntermediateField

variable (L Ω : Type u) [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω]

/-- The finite Galois subextensions of `Ω / L` form a filtered category. -/
instance : IsFiltered (FiniteGaloisIntermediateField L Ω) := inferInstance

/-- The diagram of the finite Galois subextensions `L'` of `Ω / L` in `CommRingCat`. -/
@[simps]
noncomputable def ringDiagram : FiniteGaloisIntermediateField L Ω ⥤ CommRingCat.{u} where
  obj L' := CommRingCat.of L'
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom

/-- The cocone of the inclusions `L' ⟶ Ω` of the finite Galois subextensions. -/
@[simps]
noncomputable def ringCocone : Cocone (ringDiagram L Ω) where
  pt := CommRingCat.of Ω
  ι := { app L' := CommRingCat.ofHom (algebraMap L' Ω) }

/-- **`Ω` is the filtered colimit of its finite Galois subextensions**: every element of `Ω`
lies in a finite Galois subextension. -/
noncomputable def isColimitRingCocone : IsColimit (ringCocone L Ω) := by
  have : ReflectsColimitsOfShape (FiniteGaloisIntermediateField L Ω)
      (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf _ _ (fun x ↦ ?_) fun i j xi xj h ↦ ?_
  · exact ⟨adjoin L {(show Ω from x)}, ⟨x, subset_adjoin L {(show Ω from x)} rfl⟩, rfl⟩
  · refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, Subtype.ext ?_⟩
    exact h

/-- The cofiltered diagram of the `Spec L'`, for the finite Galois subextensions `L'`. -/
noncomputable abbrev specDiagram :
    (FiniteGaloisIntermediateField L Ω)ᵒᵖ ⥤ AlgebraicGeometry.Scheme.{u} :=
  (ringDiagram L Ω).op ⋙ AlgebraicGeometry.Scheme.Spec

/-- The cone of the projections `Spec Ω ⟶ Spec L'`. -/
noncomputable abbrev specCone : Cone (specDiagram L Ω) :=
  AlgebraicGeometry.Scheme.Spec.mapCone (ringCocone L Ω).op

/-- **`Spec Ω` is the cofiltered limit of the `Spec L'`**, `Spec` being a right adjoint. -/
noncomputable def isLimitSpecCone : IsLimit (specCone L Ω) :=
  isLimitOfPreserves AlgebraicGeometry.Scheme.Spec (isColimitRingCocone L Ω).op

/-- The structure morphisms `Spec L' ⟶ Spec L`. -/
@[simps]
noncomputable def specProj :
    specDiagram L Ω ⟶ (Functor.const _).obj (AlgebraicGeometry.Spec (.of L)) where
  app L' := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap L L'.unop))
  naturality L' L'' f := by
    simp only [Functor.comp_obj, Functor.op_obj, AlgebraicGeometry.Scheme.Spec_obj,
      Functor.comp_map, Functor.op_map, AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op,
      ringDiagram_map, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
      ← AlgebraicGeometry.Spec.map_comp]
    rfl

omit [IsGalois L Ω] in
lemma specCone_π_app_comp_specProj_app (L' : (FiniteGaloisIntermediateField L Ω)ᵒᵖ) :
    (specCone L Ω).π.app L' ≫ (specProj L Ω).app L' =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap L Ω)) := by
  simp only [Functor.mapCone_pt, Cocone.op_pt, AlgebraicGeometry.Scheme.Spec_obj,
    Functor.mapCone_π_app, Cocone.op_π, Functor.const_obj_obj, Functor.op_obj, NatTrans.op_app,
    ringCocone_ι_app, AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op, specProj_app,
    ← AlgebraicGeometry.Spec.map_comp]
  rfl

end FiniteGaloisIntermediateField

/-! ### The tower `G ×_L L'` -/

namespace AlgebraicGeometry

open FiniteGaloisIntermediateField

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

variable (Ω) in
/-- The diagram of the base changes `G ×_L L'` along the finite Galois subextensions `L'`. -/
noncomputable abbrev galoisLevelDiagram : (FiniteGaloisIntermediateField L Ω)ᵒᵖ ⥤ Scheme.{u} :=
  pullbackDiagram h (specProj L Ω)

/-- The cone of the projections `G ×_L Ω ⟶ G ×_L L'`. -/
noncomputable abbrev galoisLevelCone : Cone (galoisLevelDiagram Ω h) :=
  pullbackDiagramCone h (specProj L Ω) (specCone L Ω)
    (Spec.map (CommRingCat.ofHom (algebraMap L Ω))) (specCone_π_app_comp_specProj_app L Ω)

/-- **`G ×_L Ω` is the cofiltered limit of the `G ×_L L'`.** -/
noncomputable def isLimitGaloisLevelCone : IsLimit (galoisLevelCone (Ω := Ω) h) :=
  have := IsCofiltered.isConnected (FiniteGaloisIntermediateField L Ω)ᵒᵖ
  isLimitPullbackDiagramCone _ _ _ _ _ (isLimitSpecCone L Ω)

variable (Ω) in
/-- The structure morphisms `G ×_L L' ⟶ G`. -/
@[simps]
noncomputable def galoisLevelProj : galoisLevelDiagram Ω h ⟶ (Functor.const _).obj G where
  app L' := pullback.fst _ _
  naturality L' L'' f := by simp

omit [IsGalois L Ω] in
lemma galoisLevelCone_π_app_comp_galoisLevelProj_app (L' : (FiniteGaloisIntermediateField L Ω)ᵒᵖ) :
    (galoisLevelCone (Ω := Ω) h).π.app L' ≫ (galoisLevelProj Ω h).app L' = pullback.fst _ _ := by
  simp

end AlgebraicGeometry
