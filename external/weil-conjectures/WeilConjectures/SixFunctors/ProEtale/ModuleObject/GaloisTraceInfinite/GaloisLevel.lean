/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFieldCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerLimit

/-!
# The finite Galois levels of a Galois base change

Let `Ω / L` be a Galois extension, `G` a scheme over `Spec L` and, for a finite Galois
subextension `L'`, `G_{L'} = G ×_L L'`. This file names the transition maps
`G_{L''} ⟶ G_{L'}` for `L' ≤ L''` (`AlgebraicGeometry.galoisLevelMap`), the projections
`G_Ω ⟶ G_{L'}` (`AlgebraicGeometry.galoisLevelProjection`) and the action of `Gal(L'/L)` on
`G_{L'}` (`AlgebraicGeometry.galoisLevelAction`), and proves that every automorphism of `L'` lifts
to `L''` compatibly with the transition maps
(`AlgebraicGeometry.exists_galoisLevelMap_comp_galoisLevelAction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace FiniteGaloisIntermediateField

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω]

/-- Every automorphism of a finite Galois subextension `L'` extends to a larger one `L''`. -/
lemma exists_algEquiv_inclusion_apply {L' L'' : FiniteGaloisIntermediateField L Ω}
    (hle : L' ≤ L'') (σ : L' ≃ₐ[L] L') :
    ∃ τ : L'' ≃ₐ[L] L'', ∀ x : L',
      IntermediateField.inclusion hle (σ x) = τ (IntermediateField.inclusion hle x) := by
  obtain ⟨χ, hχ⟩ := AlgEquiv.restrictNormalHom_surjective (F := L) (K₁ := L') Ω σ
  refine ⟨χ.restrictNormal L'', fun x ↦ Subtype.ext ?_⟩
  have h₁ := AlgEquiv.restrictNormal_commutes χ L'' (IntermediateField.inclusion hle x)
  have h₂ := AlgEquiv.restrictNormal_commutes χ L' x
  rw [← hχ]
  exact h₂.trans h₁.symm

end FiniteGaloisIntermediateField

namespace AlgebraicGeometry

open FiniteGaloisIntermediateField ProEtale

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

omit [IsGalois L Ω] in
instance (L' : (FiniteGaloisIntermediateField L Ω)ᵒᵖ) : Etale ((galoisLevelProj Ω h).app L') :=
  inferInstanceAs (Etale (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L'.unop)))))

omit [IsGalois L Ω] in
instance (L' : (FiniteGaloisIntermediateField L Ω)ᵒᵖ) : IsFinite ((galoisLevelProj Ω h).app L') :=
  inferInstanceAs (IsFinite (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L'.unop)))))

variable (Ω) in
/-- The transition map `G ×_L L'' ⟶ G ×_L L'` for finite Galois subextensions `L' ≤ L''`. -/
noncomputable def galoisLevelMap {L' L'' : FiniteGaloisIntermediateField L Ω}
    (hle : L' ≤ L'') :
    pullback h (Spec.map (CommRingCat.ofHom (algebraMap L L''))) ⟶
      pullback h (Spec.map (CommRingCat.ofHom (algebraMap L L'))) :=
  pullback.map h _ h _ (𝟙 G)
    (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hle).toRingHom))
    (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; rfl)

omit [IsGalois L Ω] in
lemma galoisLevelDiagram_map {L' L'' : FiniteGaloisIntermediateField L Ω} (hle : L' ≤ L'') :
    (galoisLevelDiagram Ω h).map (homOfLE hle).op = galoisLevelMap Ω h hle :=
  rfl

omit [IsGalois L Ω] in
@[reassoc (attr := simp)]
lemma galoisLevelMap_fst {L' L'' : FiniteGaloisIntermediateField L Ω} (hle : L' ≤ L'') :
    galoisLevelMap Ω h hle ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [galoisLevelMap]

/-- The projection `G ×_L Ω ⟶ G ×_L L'`. -/
noncomputable abbrev galoisLevelProjection (L' : FiniteGaloisIntermediateField L Ω) :
    pullback h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))) ⟶
      pullback h (Spec.map (CommRingCat.ofHom (algebraMap L L'))) :=
  pullback.map h _ h _ (𝟙 G) (Spec.map (CommRingCat.ofHom (algebraMap L' Ω))) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)

omit [IsGalois L Ω] in
lemma galoisLevelCone_π_app (L' : FiniteGaloisIntermediateField L Ω) :
    (galoisLevelCone (Ω := Ω) h).π.app (op L') = galoisLevelProjection h L' :=
  rfl

omit [IsGalois L Ω] in
@[reassoc (attr := simp)]
lemma galoisLevelProjection_fst (L' : FiniteGaloisIntermediateField L Ω) :
    galoisLevelProjection h L' ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp

omit [IsGalois L Ω] in
@[reassoc (attr := simp)]
lemma galoisLevelProjection_comp_galoisLevelMap {L' L'' : FiniteGaloisIntermediateField L Ω}
    (hle : L' ≤ L'') :
    galoisLevelProjection h L'' ≫ galoisLevelMap Ω h hle = galoisLevelProjection h L' :=
  (galoisLevelCone h).w (homOfLE hle).op

omit [IsGalois L Ω] in
@[reassoc]
lemma galoisLevelMap_comp {L' L'' L''' : FiniteGaloisIntermediateField L Ω} (h₁ : L' ≤ L'')
    (h₂ : L'' ≤ L''') (h₃ : L' ≤ L''') :
    galoisLevelMap Ω h h₂ ≫ galoisLevelMap Ω h h₁ = galoisLevelMap Ω h h₃ := by
  rw [← galoisLevelDiagram_map, ← galoisLevelDiagram_map, ← Functor.map_comp]
  rfl

omit [IsGalois L Ω] in
lemma galoisLevelMap_refl {L' : FiniteGaloisIntermediateField L Ω} (hle : L' ≤ L') :
    galoisLevelMap Ω h hle = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [galoisLevelMap]

/-- The action of `σ ∈ Gal(L'/L)` on `G ×_L L'`. -/
noncomputable abbrev galoisLevelAction (L' : FiniteGaloisIntermediateField L Ω)
    (σ : L' ≃ₐ[L] L') :
    pullback h (Spec.map (CommRingCat.ofHom (algebraMap L L'))) ⟶
      pullback h (Spec.map (CommRingCat.ofHom (algebraMap L L'))) :=
  pullbackAction h (Spec.map (CommRingCat.ofHom (algebraMap L L')))
    (specGaloisAction_comp (F := L) (L := L')) σ

/-- **Automorphisms lift along the transition maps**: for `L' ≤ L''` and `σ ∈ Gal(L'/L)` there is
`τ ∈ Gal(L''/L)` with `G_{L''} ⟶ G_{L'}` intertwining `τ` and `σ`. -/
theorem exists_galoisLevelMap_comp_galoisLevelAction {L' L'' : FiniteGaloisIntermediateField L Ω}
    (hle : L' ≤ L'') (σ : L' ≃ₐ[L] L') :
    ∃ τ : L'' ≃ₐ[L] L'', galoisLevelMap Ω h hle ≫ galoisLevelAction h L' σ =
      galoisLevelAction h L'' τ ≫ galoisLevelMap Ω h hle := by
  obtain ⟨τ, hτ⟩ := exists_algEquiv_inclusion_apply hle σ
  refine ⟨τ, ?_⟩
  apply pullback.hom_ext
  · simp [galoisLevelMap]
  · simp only [galoisLevelMap, Category.assoc, pullbackAction_snd, pullback.lift_snd,
      pullback.lift_snd_assoc, pullbackAction_snd_assoc, specGaloisAction]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    exact congrArg Subtype.val (hτ x)

omit [IsGalois L Ω] in
/-- The projection `G ×_L Ω ⟶ G ×_L L'` intertwines the action of `σ ∈ Gal(Ω/L)` and of its
restriction to `L'`. -/
lemma pullbackAction_comp_galoisLevelProjection (L' : FiniteGaloisIntermediateField L Ω)
    (σ : Ω ≃ₐ[L] Ω) :
    pullbackAction h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
        (specGaloisAction_comp (F := L) (L := Ω)) σ ≫ galoisLevelProjection h L' =
      galoisLevelProjection h L' ≫ galoisLevelAction h L' (σ.restrictNormal L') := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, pullbackAction_snd, pullback.lift_snd, pullback.lift_snd_assoc,
      pullbackAction_snd_assoc, specGaloisAction]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    exact (AlgEquiv.restrictNormal_commutes σ L' x).symm

end AlgebraicGeometry
