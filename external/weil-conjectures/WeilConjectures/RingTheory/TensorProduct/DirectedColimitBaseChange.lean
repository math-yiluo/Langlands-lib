/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-!
# Base change along a directed colimit of rings

Let `A = colim_i A_i` be a directed colimit of commutative rings, `i₀` an index and `M₀` an
`A_{i₀}`-module. For `i ≥ i₀` put `M_i = A_i ⊗_{A_{i₀}} M₀` and `M = A ⊗_{A_{i₀}} M₀`. Then every
element of `M` comes from some `M_i`, and an element of `M_i` vanishing in `M` already vanishes in
some `M_j`, `j ≥ i`: the module `M` is the directed colimit of the `M_i`.

## Main definitions

- `CommRingCat.DirectedColimitBaseChange.Stage F i₀ i`: the ring `A_i`, `i ≥ i₀`, as an
  `A_{i₀}`-algebra.
- `CommRingCat.DirectedColimitBaseChange.Point F c i₀`: the colimit `A` as an `A_{i₀}`-algebra.
- `CommRingCat.DirectedColimitBaseChange.toPoint`, `.transition`: the coprojections and
  transition maps, as `A_{i₀}`-algebra maps.

## Main results

- `CommRingCat.DirectedColimitBaseChange.exists_rTensor_toPoint_eq`: every element of
  `A ⊗ M₀` comes from some `A_i ⊗ M₀`.
- `CommRingCat.DirectedColimitBaseChange.exists_rTensor_transition_eq_zero`: an element of
  `A_i ⊗ M₀` vanishing in `A ⊗ M₀` vanishes in some `A_j ⊗ M₀`.

## References

- Stacks Project, Lemma 10.12.9, <https://stacks.math.columbia.edu/tag/00DD>
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat.DirectedColimitBaseChange

variable {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (i₀ : I)

/-- The ring `A_i` of a stage `i ≥ i₀`, regarded as an `A_{i₀}`-algebra. -/
def Stage (i : {i // i₀ ≤ i}) : Type u := F.obj i.1

instance (i : {i // i₀ ≤ i}) : CommRing (Stage F i₀ i) :=
  inferInstanceAs (CommRing (F.obj i.1))

instance (i : {i // i₀ ≤ i}) : Algebra (F.obj i₀) (Stage F i₀ i) :=
  (F.map (homOfLE i.2)).hom.toAlgebra

/-- The colimit `A` of the `A_i`, regarded as an `A_{i₀}`-algebra. -/
def Point : Type u := c.pt

instance : CommRing (Point F c) := inferInstanceAs (CommRing c.pt)

instance : Algebra (F.obj i₀) (Point F c) := (c.ι.app i₀).hom.toAlgebra

lemma ι_app_map_apply {i j : I} (f : i ⟶ j) (x : F.obj i) :
    c.ι.app j (F.map f x) = c.ι.app i x := by
  exact Cocone.w_apply c f x

/-- The coprojection `A_i → A`, as an `A_{i₀}`-algebra map. -/
noncomputable def toPoint (i : {i // i₀ ≤ i}) : Stage F i₀ i →ₐ[F.obj i₀] Point F c where
  toRingHom := (c.ι.app i.1).hom
  commutes' r := ι_app_map_apply F c (homOfLE i.2) r

lemma toPoint_apply (i : {i // i₀ ≤ i}) (x : Stage F i₀ i) :
    toPoint F c i₀ i x = c.ι.app i.1 (show F.obj i.1 from x) :=
  rfl

/-- The transition map `A_i → A_j`, as an `A_{i₀}`-algebra map. -/
noncomputable def transition {i j : {i // i₀ ≤ i}} (h : i ≤ j) :
    Stage F i₀ i →ₐ[F.obj i₀] Stage F i₀ j where
  toRingHom := (F.map (homOfLE h)).hom
  commutes' r := by
    change (F.map (homOfLE i.2) ≫ F.map (homOfLE h)) r = F.map (homOfLE j.2) r
    rw [← F.map_comp]
    rfl

lemma transition_apply {i j : {i // i₀ ≤ i}} (h : i ≤ j) (x : Stage F i₀ i) :
    transition F i₀ h x = F.map (homOfLE h) (show F.obj i.1 from x) :=
  rfl

instance : DirectedSystem (Stage F i₀) fun _ _ h ↦ (transition F i₀ h).toLinearMap where
  map_self i x := by
    rw [AlgHom.toLinearMap_apply, transition_apply]
    change F.map (𝟙 _) x = x
    rw [F.map_id]
    rfl
  map_map k j i hij hjk x := by
    simp only [AlgHom.toLinearMap_apply]
    rw [transition_apply, transition_apply, transition_apply]
    change (F.map (homOfLE hij) ≫ F.map (homOfLE hjk)) x = _
    rw [← F.map_comp]
    rfl

lemma toPoint_transition {i j : {i // i₀ ≤ i}} (h : i ≤ j) (x : Stage F i₀ i) :
    toPoint F c i₀ j (transition F i₀ h x) = toPoint F c i₀ i x :=
  ι_app_map_apply F c (homOfLE h) _

variable [IsDirectedOrder I]

instance : IsDirectedOrder {i // i₀ ≤ i} where
  directed a b := by
    obtain ⟨m, ha, hb⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨m, a.2.trans ha⟩, ha, hb⟩

/-- The comparison map from the module direct limit of the `A_i`, `i ≥ i₀`, to the colimit. -/
noncomputable def fromDirectLimit [DecidableEq {i // i₀ ≤ i}] :
    Module.DirectLimit (Stage F i₀) (fun _ _ h ↦ (transition F i₀ h).toLinearMap) →ₗ[F.obj i₀]
      Point F c :=
  Module.DirectLimit.lift _ _ _ _ (fun i ↦ (toPoint F c i₀ i).toLinearMap)
    fun _ _ h x ↦ by
      simp only [AlgHom.toLinearMap_apply]
      exact toPoint_transition F c i₀ h x

lemma bijective_fromDirectLimit [DecidableEq {i // i₀ ≤ i}] (hc : IsColimit c) :
    Function.Bijective (fromDirectLimit F c i₀) := by
  have : Nonempty I := ⟨i₀⟩
  have : Nonempty {i // i₀ ≤ i} := ⟨⟨i₀, le_rfl⟩⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    rw [fromDirectLimit, Module.DirectLimit.lift_of] at hz
    obtain ⟨k, f, g, hf⟩ := Concrete.isColimit_exists_of_rep_eq F hc
      (show F.obj i.1 from x) 0 (by rw [map_zero]; exact hz)
    obtain ⟨j, hj⟩ : ∃ j : {i // i₀ ≤ i}, j.1 = k := ⟨⟨k, i.2.trans (leOfHom f)⟩, rfl⟩
    subst hj
    rw [← Module.DirectLimit.of_f (hij := show i ≤ j from leOfHom f)]
    have h0 : transition F i₀ (show i ≤ j from leOfHom f) x = 0 := by
      rw [map_zero] at hf
      exact hf
    rw [AlgHom.toLinearMap_apply, h0, map_zero]
  · intro y
    obtain ⟨k, a, rfl⟩ := Concrete.isColimit_exists_rep F hc (show c.pt from y)
    obtain ⟨m, hk, hm⟩ := directed_of (· ≤ ·) k i₀
    refine ⟨Module.DirectLimit.of _ _ _ _ ⟨m, hm⟩
      (show Stage F i₀ ⟨m, hm⟩ from F.map (homOfLE hk) a), ?_⟩
    rw [fromDirectLimit, Module.DirectLimit.lift_of]
    exact ι_app_map_apply F c (homOfLE hk) a

section TensorProduct

variable (M₀ : Type u) [AddCommGroup M₀] [Module (F.obj i₀) M₀]

/-- The isomorphism `colim_{i ≥ i₀} (A_i ⊗ M₀) ≃ A ⊗ M₀`. -/
noncomputable def directLimitTensorEquiv [DecidableEq {i // i₀ ≤ i}] (hc : IsColimit c) :
    Module.DirectLimit (fun i ↦ Stage F i₀ i ⊗[F.obj i₀] M₀)
        (fun _ _ h ↦ (transition F i₀ h).toLinearMap.rTensor M₀) ≃ₗ[F.obj i₀]
      Point F c ⊗[F.obj i₀] M₀ :=
  (TensorProduct.directLimitLeft _ M₀).symm ≪≫ₗ
    LinearEquiv.rTensor M₀ (LinearEquiv.ofBijective _ (bijective_fromDirectLimit F c i₀ hc))

lemma directLimitTensorEquiv_of [DecidableEq {i // i₀ ≤ i}] (hc : IsColimit c)
    (i : {i // i₀ ≤ i}) (t : Stage F i₀ i ⊗[F.obj i₀] M₀) :
    directLimitTensorEquiv F c i₀ M₀ hc (Module.DirectLimit.of _ _ _ _ i t) =
      (toPoint F c i₀ i).toLinearMap.rTensor M₀ t := by
  rw [directLimitTensorEquiv, LinearEquiv.trans_apply,
    ← TensorProduct.directLimitLeft_rTensor_of, LinearEquiv.symm_apply_apply]
  change LinearMap.rTensor M₀ (fromDirectLimit F c i₀) _ = _
  rw [← LinearMap.rTensor_comp_apply]
  congr 2
  ext x
  simp [fromDirectLimit]

/-- **Base change along a directed colimit: elements come from a stage.** Every element of
`A ⊗_{A_{i₀}} M₀` is the image of an element of `A_i ⊗_{A_{i₀}} M₀` for some `i ≥ i₀`.

(blueprint: `lem-weil-pbc-directed-colimit-base-change-elementwise`) -/
theorem exists_rTensor_toPoint_eq (hc : IsColimit c) (x : Point F c ⊗[F.obj i₀] M₀) :
    ∃ (i : {i // i₀ ≤ i}) (t : Stage F i₀ i ⊗[F.obj i₀] M₀),
      (toPoint F c i₀ i).toLinearMap.rTensor M₀ t = x := by
  classical
  have : Nonempty {i // i₀ ≤ i} := ⟨⟨i₀, le_rfl⟩⟩
  obtain ⟨i, t, ht⟩ := Module.DirectLimit.exists_of ((directLimitTensorEquiv F c i₀ M₀ hc).symm x)
  refine ⟨i, t, ?_⟩
  rw [← directLimitTensorEquiv_of F c i₀ M₀ hc, ht, LinearEquiv.apply_symm_apply]

/-- **Base change along a directed colimit: zero elements vanish at a stage.** If
`t ∈ A_i ⊗_{A_{i₀}} M₀` maps to zero in `A ⊗_{A_{i₀}} M₀`, then it maps to zero in
`A_j ⊗_{A_{i₀}} M₀` for some `j ≥ i`.

(blueprint: `lem-weil-pbc-directed-colimit-base-change-elementwise`) -/
theorem exists_rTensor_transition_eq_zero (hc : IsColimit c) (i : {i // i₀ ≤ i})
    (t : Stage F i₀ i ⊗[F.obj i₀] M₀) (ht : (toPoint F c i₀ i).toLinearMap.rTensor M₀ t = 0) :
    ∃ (j : {i // i₀ ≤ i}) (h : i ≤ j), (transition F i₀ h).toLinearMap.rTensor M₀ t = 0 := by
  classical
  rw [← directLimitTensorEquiv_of F c i₀ M₀ hc, LinearEquiv.map_eq_zero_iff] at ht
  exact Module.DirectLimit.of.zero_exact ht

end TensorProduct

end CommRingCat.DirectedColimitBaseChange
