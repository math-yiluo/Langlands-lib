/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# The pro-étale sheaf of twisted sections of a descent cocycle

Let `f : V ⟶ Y` be a morphism of schemes and `c` a descent cocycle on the constant sheaf `S_V`
(`AlgebraicGeometry.IsDescentCocycle`). The twisted sections of `c`
(`AlgebraicGeometry.IsTwistedSection`) over the objects of the small pro-étale site of `Y` form
a sheaf of sets (`AlgebraicGeometry.isSheaf_proEtTwistedSectionsPresheaf`): locally constant
functions glue along pro-étale covers, open subsets descending along them. For a linear cocycle
on a `Λ`-module `M` they form a sheaf of `Λ`-modules
(`AlgebraicGeometry.proEtTwistedModuleSheaf`), whose restriction to the small étale site is the
étale sheaf of twisted sections `AlgebraicGeometry.twistedModuleSheaf`.

An equivariant linear map of linear cocycles induces morphisms of the étale and pro-étale sheaves
of twisted sections (`AlgebraicGeometry.twistedModuleSheafMap`,
`AlgebraicGeometry.proEtTwistedModuleSheafMap`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Y V : Scheme.{u}} (f : V ⟶ Y)

/-- The presheaf of twisted sections of a descent cocycle `c`, on the small pro-étale site of
`Y`. -/
noncomputable def proEtTwistedSectionsPresheaf {S : Type w} (c : ↥(pullback f f) → S → S) :
    Y.ProEtᵒᵖ ⥤ Type (max u w) where
  obj U := {σ : ↥(pullback f U.unop.hom) → S // IsTwistedSection f c U.unop.hom σ}
  map {U U'} g := ↾fun σ ↦
    ⟨σ.1 ∘ (pullbackMapRight f g.unop.left (MorphismProperty.Over.w g.unop)).base,
      σ.2.comp g.unop.left (MorphismProperty.Over.w g.unop)⟩
  map_id U := by
    ext σ : 3
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (𝟙 U.unop.left) _).base = σ.1
    rw [pullbackMapRight_id]
    rfl
  map_comp {U U' U''} g g' := by
    ext σ : 3
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (g'.unop.left ≫ g.unop.left) _).base =
      (σ.1 ∘ (pullbackMapRight f g.unop.left _).base) ∘ (pullbackMapRight f g'.unop.left _).base
    rw [pullbackMapRight_comp g.unop.left (MorphismProperty.Over.w g.unop) g'.unop.left
      (MorphismProperty.Over.w g'.unop)]
    rfl

lemma proEtTwistedSectionsPresheaf_map_coe {S : Type w} (c : ↥(pullback f f) → S → S)
    {U U' : Y.ProEt} (g : U' ⟶ U) (σ : (proEtTwistedSectionsPresheaf f c).obj (op U)) :
    ((proEtTwistedSectionsPresheaf f c).map g.op σ).1 =
      σ.1 ∘ (pullbackMapRight f g.left (MorphismProperty.Over.w g)).base :=
  rfl

variable {f}

/-- The base change to `V ×_Y U` of a pro-étale covering family of `U` is a pro-étale covering
family of `V ×_Y U`. -/
lemma ofArrows_pullbackMapRight_mem_proetalePrecoverage {U : Y.ProEt} {ι : Type (u + 1)}
    (Ui : ι → Y.ProEt) (π : ∀ i, Ui i ⟶ U)
    (hπ : Presieve.ofArrows (fun i ↦ (Ui i).left) (fun i ↦ (π i).left) ∈
      proetalePrecoverage U.left) :
    Presieve.ofArrows (fun i ↦ pullback f (Ui i).hom)
        (fun i ↦ pullbackMapRight f (π i).left (MorphismProperty.Over.w (π i))) ∈
      proetalePrecoverage (pullback f U.hom) :=
  Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPullback (fun i ↦ (π i).left) hπ
    (pullback.snd f U.hom) _ (fun i ↦ pullback.snd f (Ui i).hom)
    fun i ↦ isPullback_pullbackMapRight (π i).left (MorphismProperty.Over.w (π i))

variable (f) in
/-- **Twisted sections glue along pro-étale covering families.** -/
lemma isSheafFor_ofArrows_proEtTwistedSectionsPresheaf {S : Type w}
    (c : ↥(pullback f f) → S → S) {U : Y.ProEt} {ι : Type (u + 1)} (Ui : ι → Y.ProEt)
    (π : ∀ i, Ui i ⟶ U)
    (hπ : Presieve.ofArrows (fun i ↦ (Ui i).left) (fun i ↦ (π i).left) ∈
      proetalePrecoverage U.left) :
    (Presieve.ofArrows Ui π).IsSheafFor (proEtTwistedSectionsPresheaf f c) := by
  classical
  have hsurj (u : U.left) : ∃ i, ∃ x, (π i).left.base x = u := by
    obtain ⟨i, x, hx⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1
      (propQCPrecoverage_le_precoverage (P := @WeaklyEtale) _ hπ)).1 u
    exact ⟨i, x, hx⟩
  have := fun i ↦ ProEt.weaklyEtale_left (π i)
  let M (i : ι) := pullbackMapRight f (π i).left (MorphismProperty.Over.w (π i))
  have hMs (i : ι) : M i ≫ pullback.snd f U.hom = pullback.snd f (Ui i).hom ≫ (π i).left :=
    pullbackMapRight_snd _ _
  have hMf (i : ι) : M i ≫ pullback.fst f U.hom = pullback.fst f (Ui i).hom :=
    pullbackMapRight_fst _ _
  have hM (p : ↥(pullback f U.hom)) : ∃ i, ∃ q, (M i).base q = p := by
    obtain ⟨i, u, hu⟩ := hsurj ((pullback.snd f U.hom).base p)
    obtain ⟨q, hq, -⟩ := exists_pullbackMapRight_eq (f := f) (π i).left
      (MorphismProperty.Over.w (π i)) p u hu
    exact ⟨i, q, hq⟩
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- compatibility at points
  have hcompat (i j : ι) (q : ↥(pullback f (Ui i).hom)) (q' : ↥(pullback f (Ui j).hom))
      (h : (M i).base q = (M j).base q') : (x i).1 q = (x j).1 q' := by
    have : WeaklyEtale (pullback.fst (π i).left (π j).left ≫ (Ui i).hom) := inferInstance
    let Z : Y.ProEt := Scheme.ProEt.mk (pullback.fst (π i).left (π j).left ≫ (Ui i).hom)
    let g₁ : Z ⟶ Ui i := MorphismProperty.Over.homMk (pullback.fst _ _) rfl trivial
    let g₂ : Z ⟶ Ui j := MorphismProperty.Over.homMk (pullback.snd _ _) (by
      change pullback.snd _ _ ≫ (Ui j).hom = pullback.fst _ _ ≫ (Ui i).hom
      rw [← MorphismProperty.Over.w (π i), ← MorphismProperty.Over.w (π j),
        pullback.condition_assoc]) trivial
    have hg : g₁ ≫ π i = g₂ ≫ π j :=
      MorphismProperty.Over.Hom.ext pullback.condition
    have e := congrArg Subtype.val (hx i j Z g₁ g₂ hg)
    obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := M i) (g := M j) q q' h
    have hc : (pullback.fst (M i) (M j) ≫ pullback.snd f (Ui i).hom) ≫ (π i).left =
        (pullback.snd (M i) (M j) ≫ pullback.snd f (Ui j).hom) ≫ (π j).left := by
      rw [Category.assoc, Category.assoc, ← hMs, ← hMs]
      exact pullback.condition_assoc _
    let L : pullback (M i) (M j) ⟶ pullback f Z.hom :=
      pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.lift _ _ hc) (by
        change _ = _ ≫ pullback.fst _ _ ≫ (Ui i).hom
        simp [pullback.condition])
    have hL₁ : L ≫ pullbackMapRight f g₁.left (MorphismProperty.Over.w g₁) =
        pullback.fst (M i) (M j) := pullback.hom_ext (by simp [L]) (by simp [L, g₁])
    have hL₂ : L ≫ pullbackMapRight f g₂.left (MorphismProperty.Over.w g₂) =
        pullback.snd (M i) (M j) := by
      apply pullback.hom_ext
      · have := pullback.condition_assoc (f := M i) (g := M j) (pullback.fst f U.hom)
        rw [hMf, hMf] at this
        rw [Category.assoc, pullbackMapRight_fst]
        exact (pullback.lift_fst _ _ _).trans this
      · simp [L, g₂]
    have e' := congrFun e (L.base y)
    simp only [proEtTwistedSectionsPresheaf_map_coe, Function.comp_apply] at e'
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hL₁, hL₂, hy₁, hy₂] at e'
    exact e'
  choose ii qq hqq using hM
  let σ : ↥(pullback f U.hom) → S := fun p ↦ (x (ii p)).1 (qq p)
  have hσM (i : ι) (q : ↥(pullback f (Ui i).hom)) : σ ((M i).base q) = (x i).1 q :=
    hcompat _ _ _ _ (hqq _)
  have hσ : IsTwistedSection f c U.hom σ := by
    refine ⟨?_, fun w ↦ ?_⟩
    · refine IsLocallyConstant.iff_isOpen_fiber.2 fun a ↦ ?_
      refine Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage M
        (ofArrows_pullbackMapRight_mem_proetalePrecoverage Ui π hπ) _ fun i ↦ ?_
      have : (M i).base ⁻¹' (σ ⁻¹' {a}) = (x i).1 ⁻¹' {a} := by
        ext q
        simp [hσM]
      rw [this]
      exact (x i).2.1.isOpen_fiber a
    · obtain ⟨i, u, hu⟩ := hsurj
        ((pullback.fst (pullback.snd f U.hom) (pullback.snd f U.hom) ≫ pullback.snd f U.hom).base
          w)
      obtain ⟨w', hw'⟩ := exists_pairMapRight_eq (f := f) (π i).left
        (MorphismProperty.Over.w (π i)) w u hu
      have h₁ := congrArg (fun φ ↦ φ.base w') (pairMapRight_fst (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      have h₂ := congrArg (fun φ ↦ φ.base w') (pairMapRight_snd (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      have h₃ := congrArg (fun φ ↦ φ.base w') (pairMapRight_twistedPairMap (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      simp only [Scheme.Hom.comp_apply, hw'] at h₁ h₂ h₃
      rw [h₁, h₂, h₃, hσM, hσM]
      exact (x i).2.2 w'
  refine ⟨⟨σ, hσ⟩, fun i ↦ Subtype.ext (funext fun q ↦ hσM i q), fun t ht ↦ ?_⟩
  refine Subtype.ext (funext fun p ↦ ?_)
  obtain ⟨i, q, rfl⟩ : ∃ i q, (M i).base q = p := ⟨ii p, qq p, hqq p⟩
  have := congrFun (congrArg Subtype.val (ht i)) q
  simp only [proEtTwistedSectionsPresheaf_map_coe, Function.comp_apply] at this
  change t.1 ((M i).base q) = σ ((M i).base q)
  rw [this, hσM]

variable (f) in
/-- **The twisted sections of a descent cocycle form a sheaf on the small pro-étale site.** -/
theorem isSheaf_proEtTwistedSectionsPresheaf {S : Type w} (c : ↥(pullback f f) → S → S) :
    Presheaf.IsSheaf (Scheme.ProEt.topology Y) (proEtTwistedSectionsPresheaf f c) := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro U R hR
  obtain ⟨ι, Ui, π, rfl⟩ := R.exists_eq_ofArrows
  refine isSheafFor_ofArrows_proEtTwistedSectionsPresheaf f c Ui π ?_
  have := Scheme.ProEt.mem_precoverage_iff.1 hR
  rwa [Presieve.map_ofArrows] at this

end AlgebraicGeometry
