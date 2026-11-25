/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower
@[expose] public section
universe u v
namespace Algebra
/-- Source: Stacks Project, Lemma 07EZ(e), applied to finitely many elements.
(blueprint: lem-weil-pbc-common-strictly-standard-power).
Proof: for each element, finite free differentials are stably free (add the rank-zero
free module). Apply 07EZ(e) to obtain a positive threshold valid for every larger
exponent. Choose one plus the sum of all thresholds. Every threshold is bounded by
this sum, so all powers at that common positive exponent are strictly standard.
An empty index type has exponent one. Zero localizations have the empty basis and
are included in 07EZ(e). -/
theorem exists_common_strictlyStandard_power
    (R : Type u) (C : Type v) [CommRing R] [CommRing C] [Algebra R C]
    [FinitePresentation R C] {ι : Type} [Finite ι] (x : ι → C)
    (h : ∀ i, Smooth R (Localization.Away (x i)) ∧
      Module.Free (Localization.Away (x i))
        (KaehlerDifferential R (Localization.Away (x i)))) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ i, IsStrictlyStandardElement (R := R) (x i ^ c)  := by
  classical
  let _ := Fintype.ofFinite ι
  have hthreshold (i : ι) : ∃ e₀ : ℕ, 1 ≤ e₀ ∧ ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandardElement (R := R) (x i ^ e) := by
    let S := Localization.Away (x i)
    let M := KaehlerDifferential R S
    let : Smooth R S := (h i).1
    let : Module.Free S M := (h i).2
    let b := Module.Free.chooseBasis S M
    let q := Finsupp.lcongr (σ := RingHom.id S) (σ_inv := RingHom.id S)
      (Fintype.equivFin (Module.Free.ChooseBasisIndex S M))
      (LinearEquiv.refl S S)
    let e : M ≃ₗ[S]
        (Fin (Fintype.card (Module.Free.ChooseBasisIndex S M)) →₀ S) :=
      b.repr.trans q
    apply smooth_free_differentials_strictly_standard_power R C (x i) 0
      (Fintype.card (Module.Free.ChooseBasisIndex S M))
    exact ⟨(LinearEquiv.prodUnique (R := S) (M := M)
      (M₂ := Fin 0 →₀ S)).trans e⟩
  choose e₀ he₀ hpow using hthreshold
  refine ⟨1 + ∑ i, e₀ i, Nat.le_add_right 1 _, fun i ↦ ?_⟩
  apply hpow i
  exact le_trans (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (e₀ j))
    (Finset.mem_univ i)) (Nat.le_add_left _ _)
end Algebra
