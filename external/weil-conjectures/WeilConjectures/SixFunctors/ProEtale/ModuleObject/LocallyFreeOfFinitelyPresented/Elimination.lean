/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank

/-!
# Local Gaussian elimination for `ℚ̲̄_ℓ`-modules of constant fibre rank

Let `W` be a quasi-compact quasi-separated scheme and `φ : (ℚ̲̄_ℓ,W)^m ⟶ (ℚ̲̄_ℓ,W)^n` a morphism of
free modules whose cokernel has the same fibre rank `d` at every point of `W`. Then every point
of `W` has an open neighbourhood `V` on which `coker φ` is free of rank `d`
(`ProEtale.CondensedRing.exists_isOpenImmersion_cokernel_iso_finiteFree`).

The entries of `φ` are continuous functions `W → ℚ̄_ℓ` (`ProEtale.CondensedRing.endValue`). If they
all vanish at a point `w`, the fibre rank at `w` is `n`, so `d = n` and the entries vanish at every
point (`ProEtale.CondensedRing.hasFiberRank_cokernel_iff_endValue_eq_zero`): `φ = 0` and
`coker φ` is free of rank `n`. Otherwise some entry `φ_{ab}` does not vanish at `w`; it then
vanishes nowhere on the clopen neighbourhood `V₀` of `w` where its value lies in the ball of
radius `|φ_{ab}(w)|` around `φ_{ab}(w)`, so it is invertible on `V₀`
(`ProEtale.CondensedRing.isIso_of_forall_ne_zero`), and Gaussian elimination at this pivot
(`CategoryTheory.Limits.exists_cokernel_iso_of_isIso_entry`) replaces `φ|_{V₀}` by a morphism
`(ℚ̲̄_ℓ,V₀)^{m-1} ⟶ (ℚ̲̄_ℓ,V₀)^{n-1}` with the same cokernel; we conclude by induction on `n`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- If the cokernel of `φ : (ℚ̲̄_ℓ,W)^m ⟶ (ℚ̲̄_ℓ,W)^n` has constant fibre rank `d` and the
entries of `φ` all vanish at some point, then `φ = 0` and `d = n`. -/
lemma eq_zero_of_hasFiberRank_of_endValue_eq_zero {W : Scheme.{u}} [CompactSpace W]
    [QuasiSeparatedSpace W] {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W) m ⟶
      Mod.finiteFree _ n) {d : ℕ} (hd : ∀ x, HasFiberRank ℓ (cokernel φ) x d) (w : W)
    (hw : ∀ a b, endValue ℓ (Mod.finFreeEntry φ a b) w = 0) : φ = 0 ∧ d = n := by
  obtain rfl : d = n :=
    (hd w).unique ((hasFiberRank_cokernel_iff_endValue_eq_zero φ w).2 hw)
  refine ⟨Mod.finFree_hom_ext fun a b ↦ ?_, rfl⟩
  rw [Mod.finFreeEntry_zero]
  exact eq_zero_of_forall_endValue_eq_zero fun x ↦
    (hasFiberRank_cokernel_iff_endValue_eq_zero φ x).1 (hd x) a b

/-- The clopen neighbourhood of `w` where the value of the section `t` lies in the ball of radius
`|t(w)|` around `t(w)`. -/
lemma isClopen_endValue_preimage_ball {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (t : End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W))) (w : W) :
    IsClopen (endValue ℓ t ⁻¹' Metric.ball (endValue ℓ t w) ‖endValue ℓ t w‖) :=
  (IsUltrametricDist.isClopen_ball _ _).preimage (continuous_endValue t)

/-- **Local freeness of cokernels of constant fibre rank.** Let `W` be quasi-compact and
quasi-separated and `φ : (ℚ̲̄_ℓ,W)^m ⟶ (ℚ̲̄_ℓ,W)^n` such that `coker φ` has fibre rank `d` at every
point. Then every point of `W` has an open neighbourhood on which `coker φ` is free of rank
`d`. -/
theorem exists_isOpenImmersion_cokernel_iso_finiteFree (n : ℕ) :
    ∀ {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W] {m : ℕ}
      (φ : Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W) m ⟶
        Mod.finiteFree _ n) {d : ℕ} (_ : ∀ x, HasFiberRank ℓ (cokernel φ) x d) (w : W),
      ∃ (V : Scheme.{u}) (j : V ⟶ W) (_ : IsOpenImmersion j), w ∈ Set.range j ∧
        Nonempty ((j)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj (cokernel φ) ≅
          Mod.finiteFree _ d) := by
  induction n with
  | zero =>
    intro W _ _ m φ d hd w
    obtain ⟨rfl, rfl⟩ := eq_zero_of_hasFiberRank_of_endValue_eq_zero φ hd w (fun a ↦ a.elim0)
    exact ⟨W, 𝟙 W, inferInstance, ⟨w, rfl⟩, ⟨(𝟙 W)^*⟦_⟧.mapIso cokernelZeroIsoTarget ≪≫
      upperStarFiniteFreeIso _ _ 0⟩⟩
  | succ n ih =>
    intro W _ _ m φ d hd w
    by_cases hw : ∀ a b, endValue ℓ (Mod.finFreeEntry φ a b) w = 0
    · obtain ⟨rfl, rfl⟩ := eq_zero_of_hasFiberRank_of_endValue_eq_zero φ hd w hw
      exact ⟨W, 𝟙 W, inferInstance, ⟨w, rfl⟩, ⟨(𝟙 W)^*⟦_⟧.mapIso cokernelZeroIsoTarget ≪≫
        upperStarFiniteFreeIso _ _ _⟩⟩
    push Not at hw
    obtain ⟨a, b, hab⟩ := hw
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := Nat.exists_eq_add_one_of_ne_zero (by
      rintro rfl
      exact b.elim0)
    -- the clopen neighbourhood `U` of `w` on which the pivot `φ_{ab}` vanishes nowhere
    let t := Mod.finFreeEntry φ a b
    have hU := isClopen_endValue_preimage_ball t w
    let U : W.Opens := ⟨_, hU.isOpen⟩
    have hwU : endValue ℓ t w ∈ Metric.ball (endValue ℓ t w) ‖endValue ℓ t w‖ := by
      simpa using hab
    have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU.isClosed.isCompact
    have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
    let ψ := upperStarFinFreeMap _ U.ι φ
    have hψ : IsIso (biproduct.ι _ b ≫ ψ ≫ biproduct.π _ a) := by
      refine isIso_of_forall_ne_zero (Mod.finFreeEntry ψ a b) fun v hv ↦ ?_
      rw [ι_upperStarFinFreeMap_π, endValue_restrictEnd] at hv
      have hvU : endValue ℓ t (U.ι v) ∈ Metric.ball (endValue ℓ t w) ‖endValue ℓ t w‖ := v.2
      rw [hv, Metric.mem_ball, dist_zero_left] at hvU
      exact lt_irrefl _ hvU
    obtain ⟨ψ', ⟨e⟩⟩ := exists_cokernel_iso_of_isIso_entry ψ a b
    have hd' (v : U.toScheme) : HasFiberRank ℓ (cokernel ψ') v d :=
      ((hd (U.ι v)).upperStar U.ι).of_iso ((cokernelUpperStarFinFreeMapIso _ U.ι φ).symm ≪≫ e)
    obtain ⟨V, j, _, ⟨v, hv⟩, ⟨e'⟩⟩ := ih ψ' hd' ⟨w, hwU⟩
    refine ⟨V, j ≫ U.ι, inferInstance, ⟨v, ?_⟩,
      ⟨(upperStarComp _ j U.ι).app _ ≪≫
        (j)^*⟦_⟧.mapIso ((cokernelUpperStarFinFreeMapIso _ U.ι φ).symm ≪≫ e) ≪≫ e'⟩⟩
    rw [Scheme.Hom.comp_apply, hv]
    simp

end AlgebraicGeometry.ProEtale.CondensedRing
