/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.FirstOrderPowerSeriesComparison
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.RingTheory.SubsingletonH1CotangentOfCharP
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# A power series comparison map for a complete adically formally smooth algebra

Source: Stacks Project, More on Algebra, Tag 07EI (lemma-fs-implies-regular),
the prime-field reduction and the construction of the map to the power series ring.
(blueprint: lem-weil-pbc-fs-adic-power-series-comparison-map).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem lift_field_map {R : Type*} {K : Type*} {T : Type*}
    [CommRing R] [Field K] [CommRing T] [Algebra R K] [Algebra R T]
    [FormallySmooth R K] (N : Ideal T) [IsAdicComplete N T]
    (hclosed : N ^ 2 = ⨅ (m : ℕ) (_ : 1 ≤ m), N ^ 2 ⊔ N ^ m)
    (g : K →ₐ[R] T ⧸ N ^ 2) :
    ∃ f : K →+* T, (Ideal.Quotient.mk (N ^ 2)).comp f = g.toRingHom := by
  have hK : FormallySmoothAdic R K ⊥ := by
    intro D _ _ J hJ g _
    exact FormallySmooth.exists_lift J ⟨2, hJ⟩ g
  obtain ⟨f, hf, _⟩ := hK.exists_lift_into_complete ⊥ N (N ^ 2) 1 (by decide)
    (by simpa using N.pow_le_self (by decide : 2 ≠ 0)) hclosed g 1 (by decide)
    (by simp)
  exact ⟨f.toRingHom, congrArg AlgHom.toRingHom hf⟩

private theorem compatible_scalar_structure {k : Type u} {A T : Type v}
    [Field k] [CommRing A] [CommRing T] [Nontrivial T]
    [Algebra k A] [Algebra k T] (N : Ideal T) [IsAdicComplete N T]
    (hclosed : N ^ 2 = ⨅ (m : ℕ) (_ : 1 ≤ m), N ^ 2 ⊔ N ^ m)
    (g : A →+* T ⧸ N ^ 2) :
    ∃ (a : Algebra k T), letI := a
      ∃ g' : A →ₐ[k] T ⧸ N ^ 2, g'.toRingHom = g := by
  have hfieldlift : ∃ f : k →+* T,
      (Ideal.Quotient.mk (N ^ 2)).comp f = g.comp (algebraMap k A) := by
    obtain ⟨p, hp⟩ := CharP.exists k
    let := hp
    rcases CharP.char_is_prime_or_zero k p with hprime | hzero
    · let : Fact (Nat.Prime p) := ⟨hprime⟩
      have : CharP T p := charP_of_injective_algebraMap (algebraMap k T).injective p
      let := ZMod.algebra k p
      let := ZMod.algebra T p
      have : Module.Free k (KaehlerDifferential (ZMod p) k) := Module.Free.of_divisionRing k _
      have : Module.Projective k (KaehlerDifferential (ZMod p) k) := Module.Projective.of_free
      have : Subsingleton (H1Cotangent (ZMod p) k) :=
        subsingleton_h1Cotangent_of_charP p hprime.pos k
      have : FormallySmooth (ZMod p) k := FormallySmooth.mk inferInstance inferInstance
      let gk : k →ₐ[ZMod p] T ⧸ N ^ 2 :=
        { toRingHom := g.comp (algebraMap k A)
          commutes' := by
            intro r
            obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
            simp }
      exact lift_field_map N hclosed gk
    · subst p
      have : CharZero k := CharP.charP_to_charZero k
      let : Algebra ℚ T := ((algebraMap k T).comp (algebraMap ℚ k)).toAlgebra
      obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ k
      have : Algebra.IsAlgebraic
          (IntermediateField.adjoin ℚ (Set.range ((↑) : s → k))) k := hs.isAlgebraic_field
      have : FormallySmooth ℚ k :=
        FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
      let gk : k →ₐ[ℚ] T ⧸ N ^ 2 :=
        { toRingHom := g.comp (algebraMap k A)
          commutes' := fun q ↦ RingHom.map_rat_algebraMap _ q }
      exact lift_field_map N hclosed gk
  obtain ⟨f, hf⟩ := hfieldlift
  let a := f.toAlgebra
  let := a
  refine ⟨a, { toRingHom := g, commutes' := ?_ }, rfl⟩
  intro x
  exact (RingHom.congr_fun hf x).symm

/-- The comparison map constructed in the proof of Stacks Tag 07EI induces a surjection
on residues and extends the maximal ideal to the variables' ideal.
(blueprint: lem-weil-pbc-fs-adic-power-series-comparison-map)

Proof: First restrict formal smoothness from k to its prime field k₀. For a square-zero
lifting problem, lift the map from k using formal smoothness of characteristic-zero
field extensions, or the positive-characteristic field lifting theorem. Give the target
its k-algebra structure through this lift, and use the assumed adic formal smoothness
of A. A lift of a map killing m^q kills m^(2q).
By Cohen's coefficient-subring theorem, complete A contains a copy of its residue field K:
in equal characteristic the coefficient subring's maximal ideal (p) is zero. Identify it
with K by reduction. Choose lifts x₁,...,x_d of a K-basis of m/m². Nakayama identifies d
with m.spanFinrank. Set T = K[[X₁,...,X_d]] and N = (X₁,...,X_d). The coefficient field
and tangent basis identify A/m² and T/N², by sending x_i to X_i and fixing K.
Starting with the resulting map A → T/N², lift recursively to T/N^(r+2) from T/N^(r+1).
The kernels are square-zero because 2r+2 ≥ r+2 for r ≥ 1. Each lift kills a power of m,
so the adic formal smoothness over k₀ applies at every stage. Completeness of T supplies
a ring map f : A → T. Its reduction modulo N² is the prescribed isomorphism, although
f need not be K-linear. In particular the residue map is surjective, f(m) lies in N,
and the classes of f(x_i) span N/N². Nakayama in the Noetherian local ring T gives
N = (f(x_i)); thus Ideal.map f m = N. This proves both claims without claiming that
f itself is surjective or making any dimension comparison. Source: Tag 07EI, proof,
from the prime-field reduction through the construction of f and its tangent map. -/
theorem exists_powerSeries_comparison_of_formallySmoothAdic (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (h : FormallySmoothAdic k A (IsLocalRing.maximalIdeal A)) :
    ∃ f : A →+* MvPowerSeries (Fin (IsLocalRing.maximalIdeal A).spanFinrank)
        (IsLocalRing.ResidueField A),
      Ideal.map f (IsLocalRing.maximalIdeal A) =
        Ideal.span (Set.range (fun i : Fin (IsLocalRing.maximalIdeal A).spanFinrank ↦
          (MvPowerSeries.X i : MvPowerSeries (Fin (IsLocalRing.maximalIdeal A).spanFinrank)
            (IsLocalRing.ResidueField A)))) ∧
      Function.Surjective ((Ideal.Quotient.mk (Ideal.map f (IsLocalRing.maximalIdeal A))).comp
        f) := by
  let T := MvPowerSeries (Fin (IsLocalRing.maximalIdeal A).spanFinrank)
    (IsLocalRing.ResidueField A)
  let N : Ideal T := Ideal.span (Set.range (fun i ↦ (MvPowerSeries.X i : T)))
  have : IsAdicComplete N T := inferInstance
  have hNle : N ≤ IsLocalRing.maximalIdeal T := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    apply (IsLocalRing.mem_maximalIdeal (R := T) (MvPowerSeries.X i)).mpr
    rw [mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      MvPowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hclosed : N ^ 2 = ⨅ (m : ℕ) (_ : 1 ≤ m), N ^ 2 ⊔ N ^ m := by
    apply le_antisymm
    · exact le_iInf fun m ↦ le_iInf fun _ ↦ le_sup_left
    · calc
        (⨅ (m : ℕ) (_ : 1 ≤ m), N ^ 2 ⊔ N ^ m) ≤ N ^ 2 ⊔ N ^ 2 :=
          iInf_le_of_le (2 : ℕ) (iInf_le_of_le (by decide : 1 ≤ (2 : ℕ)) le_rfl)
        _ = N ^ 2 := sup_idem _
  obtain ⟨g₀, hsurj₀, hcomap₀⟩ := exists_firstOrder_powerSeries_comparison k A
  obtain ⟨a, g, hg₀⟩ := compatible_scalar_structure (k := k) N hclosed g₀
  let := a
  have hsurj : Function.Surjective g := by
    change Function.Surjective g.toRingHom
    rwa [hg₀]
  have hcomap : (N.map (Ideal.Quotient.mk (N ^ 2))).comap g.toRingHom =
      IsLocalRing.maximalIdeal A := by rw [hg₀]; exact hcomap₀
  have hg : ∀ x ∈ IsLocalRing.maximalIdeal A ^ 1,
      g x ∈ N.map (Ideal.Quotient.mk (N ^ 2)) := by
    intro x hx
    rw [pow_one] at hx
    change x ∈ (N.map (Ideal.Quotient.mk (N ^ 2))).comap g.toRingHom
    rwa [hcomap]
  obtain ⟨f, hf, hfm⟩ := h.exists_lift_into_complete
    (IsLocalRing.maximalIdeal A) N (N ^ 2) 1 (by decide)
    (by simpa using N.pow_le_self (by decide : 2 ≠ 0)) hclosed g 1 (by decide) hg
  have hred (x : A) : Ideal.Quotient.mk (N ^ 2) (f x) = g x :=
    DFunLike.congr_fun hf x
  have hle : (IsLocalRing.maximalIdeal A).map f.toRingHom ≤ N := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hfm x (by simpa using hx)
  have hspan : N ≤ (IsLocalRing.maximalIdeal A).map f.toRingHom ⊔ N ^ 2 := by
    intro x hx
    obtain ⟨y, hy⟩ := hsurj (Ideal.Quotient.mk (N ^ 2) x)
    have hym : y ∈ IsLocalRing.maximalIdeal A := by
      rw [← hcomap]
      change g y ∈ N.map (Ideal.Quotient.mk (N ^ 2))
      rw [hy]
      exact Ideal.mem_map_of_mem _ hx
    have hdiff : x - f y ∈ N ^ 2 := by
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      rw [hred, hy]
    exact Submodule.mem_sup.mpr
      ⟨f y, Ideal.mem_map_of_mem _ hym, x - f y, hdiff, by simp⟩
  have heq : (IsLocalRing.maximalIdeal A).map f.toRingHom = N := by
    apply le_antisymm hle
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian N)
      (show N ≤ Ideal.jacobson (⊥ : Ideal T) by
        rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
        exact hNle)
    simpa only [Ideal.smul_eq_mul, pow_two] using hspan
  refine ⟨f.toRingHom, heq, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy⟩ := hsurj (Ideal.Quotient.mk (N ^ 2) x)
  refine ⟨y, ?_⟩
  change Ideal.Quotient.mk _ (f y) = Ideal.Quotient.mk _ x
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [heq]
  apply N.pow_le_self (by decide : 2 ≠ 0)
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [hred, hy]

end Algebra
