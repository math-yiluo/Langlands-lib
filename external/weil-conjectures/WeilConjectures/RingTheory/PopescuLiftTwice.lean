/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.PopescuLiftOnce
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Killing an ideal through a smooth algebra over a square-zero base

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.5.2, Tag 07CL
(blueprint: lem-weil-pbc-popescu-lift-twice).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

-- Stacks 07CL, steps 2–3: construct the finite polynomial quotient and its evaluation.
set_option backward.isDefEq.respectTransparency false in
private theorem relation_presentation
    (R : Type u) [CommRing R] (B : Type w) [CommRing B] [Algebra R B]
    [FinitePresentation R B] (Λ : Type v) [CommRing Λ] [Algebra R Λ]
    (φ : B →ₐ[R] Λ) {ι : Type u} [Finite ι] {m : ℕ}
    (b : ι → B) (a : ι → Fin m → R) (y : Fin m → Λ)
    (hb : ∀ i, φ (b i) = ∑ j, a i j • y j) :
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra R C),
      FinitePresentation R C ∧ ∃ (ιB : B →ₐ[R] C) (ψ : C →ₐ[R] Λ) (x : Fin m → C),
        ψ.comp ιB = φ ∧ ∀ i, ιB (b i) = ∑ j, a i j • x j := by
  classical
  let := Fintype.ofFinite ι
  let P := MvPolynomial (Fin m) B
  let rel : ι → P := fun i ↦ MvPolynomial.C (b i) -
    ∑ j, a i j • MvPolynomial.X j
  let K : Ideal P := Ideal.span (Set.range rel)
  have hK : K.FG := Submodule.fg_span (Set.finite_range rel)
  have : FinitePresentation R P := inferInstance
  let C := P ⧸ K
  have : FinitePresentation R C := FinitePresentation.quotient hK
  let q : P →ₐ[R] C := Ideal.Quotient.mkₐ R K
  let ev : P →ₐ[R] Λ := MvPolynomial.aevalTower φ y
  have hev : ∀ i, ev (rel i) = 0 := by
    intro i
    simp only [ev, rel, map_sub, map_sum, map_smul]
    rw [MvPolynomial.aevalTower_C]
    apply sub_eq_zero.mpr
    rw [hb i]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (MvPolynomial.aevalTower_X φ y j).symm
  have hker : K ≤ RingHom.ker ev := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hev i
  let ψ : C →ₐ[R] Λ := Ideal.Quotient.liftₐ K ev (fun z hz ↦ hker hz)
  let ιB : B →ₐ[R] C := q.comp (IsScalarTower.toAlgHom R B P)
  refine ⟨C, inferInstance, inferInstance, inferInstance, ιB, ψ,
    fun j ↦ q (MvPolynomial.X j), ?_, ?_⟩
  · ext z
    change ev ((IsScalarTower.toAlgHom R B P) z) = φ z
    exact MvPolynomial.aevalTower_toAlgHom φ y z
  · intro i
    have hr : q (rel i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))
    simpa [rel, ιB, IsScalarTower.toAlgHom, P,
      MvPolynomial.algebraMap_eq, sub_eq_zero] using hr

-- Stacks 07CL, steps 1–6: kill a single element using flatness and lift-once.
set_option backward.isDefEq.respectTransparency false in
private theorem kill_one
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ :
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
        (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (hflat : RingHom.Flat (algebraMap R Λ))
    (B : Type w) [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] Λ) (h : B) (hhI : h ∈ I.map (algebraMap R B)) (hφ : φ h = 0) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B'),
      Smooth R B' ∧ ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
        α h = 0 ∧ β.comp α = φ := by
  classical
  obtain ⟨t, ht, b, hb⟩ :=
    (Submodule.mem_span_image_iff_exists_fun (R := B)
      (v := algebraMap R B)).mp hhI
  let ε : t → R := fun i ↦ i.val
  have hε : ∀ i, ε i ∈ I := fun i ↦ ht i.property
  have hh : (∑ i, ε i • b i) = h := by
    simpa [ε, Algebra.smul_def, mul_comm] using hb
  have : Module.Flat R Λ := (RingHom.flat_algebraMap_iff).mp hflat
  have hrel : ∑ i, ε i • φ (b i) = 0 := by
    simpa only [map_sum, map_smul] using congrArg φ hh |>.trans hφ
  obtain ⟨m, a, y, hba, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨C, _, _, _, ιB, ψ, x, hψ, hx⟩ := relation_presentation R B Λ φ b a y hba
  obtain ⟨B', _, _, hsm, N, _, hNI, g, χ, hχ⟩ :=
    exists_smooth_quotient_factorization R Λ I hI hΛ C ψ
  let q : B' →ₐ[R] B' ⧸ N := Ideal.Quotient.mkₐ R N
  have hIB : (I.map (algebraMap R B')) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  have hN : N ^ 2 = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      N ^ 2 ≤ (I.map (algebraMap R B')) ^ 2 := pow_le_pow_left' hNI 2
      _ = ⊥ := hIB
  obtain ⟨α, hα⟩ := FormallySmooth.comp_surjective R B N hN (g.comp ιB)
  let β : B' →ₐ[R] Λ := χ.comp q
  have hcomp : β.comp α = φ := by
    calc
      β.comp α = χ.comp (q.comp α) := rfl
      _ = χ.comp (g.comp ιB) := by rw [hα]
      _ = (χ.comp g).comp ιB := rfl
      _ = ψ.comp ιB := by rw [hχ]
      _ = φ := hψ
  choose ξ hξ using fun j ↦ Ideal.Quotient.mkₐ_surjective R N (g (x j))
  have hθ : ∀ i, α (b i) - ∑ j, a i j • ξ j ∈ N := by
    intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (α (b i) - ∑ j, a i j • ξ j) = 0
    rw [map_sub, map_sum]
    simp only [map_smul]
    have hi := DFunLike.congr_fun hα (b i)
    change q (α (b i)) = g (ιB (b i)) at hi
    rw [hi, hx, map_sum]
    simp only [map_smul, q, hξ, sub_self]
  have hεθ : ∀ i, ε i • (α (b i) - ∑ j, a i j • ξ j) = 0 := by
    intro i
    rw [Algebra.smul_def]
    apply Ideal.mem_bot.mp
    rw [← hIB, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hε i)) (hNI (hθ i))
  have hsum : ∑ i, ε i • (∑ j, a i j • ξ j) = 0 := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ha, zero_smul, Finset.sum_const_zero]
  refine ⟨B', inferInstance, inferInstance, hsm, α, β, ?_, hcomp⟩
  rw [← hh, map_sum]
  simp only [map_smul]
  calc
    ∑ i, ε i • α (b i) = ∑ i, ε i • (∑ j, a i j • ξ j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sub_eq_zero.mp (by simpa [smul_sub] using hεθ i)
    _ = 0 := hsum

-- Stacks 07CL, step 7: induct on a finite family in a fixed universe.
set_option backward.isDefEq.respectTransparency false in
private theorem kill_finite
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ :
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
        (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (hflat : RingHom.Flat (algebraMap R Λ))
    (n : ℕ) (B : Type (max u v w)) [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] Λ) (s : Fin n → B)
    (hsI : ∀ i, s i ∈ I.map (algebraMap R B)) (hsφ : ∀ i, φ (s i) = 0) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B'),
      Smooth R B' ∧ ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
        (∀ i, α (s i) = 0) ∧ β.comp α = φ := by
  induction n generalizing B with
  | zero =>
      exact ⟨B, inferInstance, inferInstance, inferInstance, AlgHom.id R B, φ,
        fun i ↦ Fin.elim0 i, rfl⟩
  | succ n ih =>
      obtain ⟨B₁, _, _, hB₁, α₁, β₁, hzero, hcomp⟩ :=
        kill_one R Λ I hI hΛ hflat B φ (s 0) (hsI 0) (hsφ 0)
      have hmap : (I.map (algebraMap R B)).map α₁.toRingHom =
          I.map (algebraMap R B₁) := by
        rw [Ideal.map_map]
        exact congrArg (fun f : R →+* B₁ ↦ I.map f) α₁.comp_algebraMap
      have htailI : ∀ i : Fin n, α₁ (s i.succ) ∈ I.map (algebraMap R B₁) := by
        intro i
        rw [← hmap]
        exact Ideal.mem_map_of_mem α₁ (hsI i.succ)
      have htailφ : ∀ i : Fin n, β₁ (α₁ (s i.succ)) = 0 := by
        intro i
        change (β₁.comp α₁) (s i.succ) = 0
        rw [hcomp, hsφ]
      obtain ⟨B₂, _, _, hB₂, α₂, β₂, htail, hcomp₂⟩ :=
        ih B₁ β₁ (fun i ↦ α₁ (s i.succ)) htailI htailφ
      refine ⟨B₂, inferInstance, inferInstance, hB₂, α₂.comp α₁, β₂, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ htail j) i
        simp only [AlgHom.comp_apply, hzero, map_zero]
      · rw [← AlgHom.comp_assoc, hcomp₂, hcomp]

/-- A map from a smooth algebra to a flat algebra kills a finitely generated ideal inside
`IB` through another smooth algebra, when `I` is square-zero and the reduction of the target
is ind-smooth. Source: Stacks Project, Smoothing Ring Maps, Lemma 16.5.2, Tag 07CL
(blueprint: lem-weil-pbc-popescu-lift-twice).

Proof (the seven steps of the node):
1. For a principal ideal `J = (h)`, write `h = ∑ εᵢ bᵢ` with `εᵢ ∈ I`. Flatness of `Λ`
   (def-weil-pbc-flat-ring-map) and lem-weil-pbc-flat-equational-criterion give elements
   `λⱼ` and coefficients `aᵢⱼ` with `φ(bᵢ) = ∑ aᵢⱼ λⱼ` and `∑ εᵢ aᵢⱼ = 0`.
2. Set `C = B[x₁,...,xₘ]/(bᵢ - ∑ aᵢⱼ xⱼ)`. Smoothness makes `B` finitely presented
   (def-weil-pbc-smooth-ring-map). The finite polynomial presentation of `C`
   (def-weil-pbc-mv-polynomial-ring, def-weil-pbc-finitely-presented-algebra),
   lem-weil-pbc-finite-presentation-quotient-fg-ideal and
   lem-weil-pbc-finite-presentation-base-change-composition make `C` finitely presented over `R`.
3. Evaluation `xⱼ ↦ λⱼ` gives `C → Λ`, restricting to `φ` on `B`, by the universal property
   in def-weil-pbc-mv-polynomial-ring and the relations from step 1.
4. Apply lem-weil-pbc-popescu-lift-once to factor `C → Λ` through `B'/J'`, where `B'` is
   smooth (def-weil-pbc-smooth-ring-map) and `J'` is finitely generated inside `IB'`.
   Define `β` by composing the quotient map with `B'/J' → Λ`.
5. Since `(J')² = 0`, lem-weil-pbc-smooth-ring-map-square-zero-lifting lifts
   `B → C → B'/J'` to `α : B → B'`. The factorization gives `β ∘ α = φ`.
6. Choose lifts `ξⱼ` of the images of `xⱼ`. Then `α(bᵢ) = ∑ aᵢⱼ ξⱼ + θᵢ` with `θᵢ ∈ J'`.
   Thus `α(h) = ∑ⱼ (∑ᵢ εᵢ aᵢⱼ) ξⱼ + ∑ᵢ εᵢ θᵢ = 0`: the first terms vanish by step 1,
   and the second by `I² = 0`. This kills the principal ideal.
7. Induct on a finite generating list of `J`. For the empty list take `B' = B` and the
   identity map. Otherwise kill the last generator by the principal case, then apply
   induction to the ideal generated by the images of the remaining generators. That ideal
   still lies in the extended ideal and is killed by the map to `Λ`. Compose the two
   factorizations; their composite kills all of `J` and still equals `φ` after mapping to `Λ`.
-/
theorem exists_smooth_factorization_killing_ideal
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ :
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
        (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (hflat : RingHom.Flat (algebraMap R Λ))
    (B : Type w) [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] Λ) (J : Ideal B) (hJfg : J.FG)
    (hJI : J ≤ I.map (algebraMap R B)) (hφJ : J ≤ RingHom.ker φ) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B'),
      Smooth R B' ∧ ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
        J ≤ RingHom.ker α ∧ β.comp α = φ := by
  classical
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  let B₀ := ULift.{max u v w} B
  let e : B₀ ≃ₐ[R] B := ULift.algEquiv
  have : Smooth R B₀ := Smooth.of_equiv e.symm
  let φ₀ : B₀ →ₐ[R] Λ := φ.comp e.toAlgHom
  let s₀ : Fin n → B₀ := fun i ↦ e.symm (s i)
  have hmap : (I.map (algebraMap R B)).map e.symm.toAlgHom.toRingHom =
      I.map (algebraMap R B₀) := by
    rw [Ideal.map_map]
    exact congrArg (fun f : R →+* B₀ ↦ I.map f) e.symm.toAlgHom.comp_algebraMap
  have hsJ : ∀ i, s i ∈ J := fun i ↦ hs ▸ Ideal.subset_span (Set.mem_range_self i)
  have hsI : ∀ i, s₀ i ∈ I.map (algebraMap R B₀) := by
    intro i
    rw [← hmap]
    exact Ideal.mem_map_of_mem e.symm (hJI (hsJ i))
  have hsφ : ∀ i, φ₀ (s₀ i) = 0 := by
    intro i
    simpa [φ₀, s₀] using hφJ (hsJ i)
  obtain ⟨B', _, _, hB', α₀, β, hzero, hcomp⟩ :=
    kill_finite R Λ I hI hΛ hflat n B₀ φ₀ s₀ hsI hsφ
  let α : B →ₐ[R] B' := α₀.comp e.symm.toAlgHom
  refine ⟨B', inferInstance, inferInstance, hB', α, β, ?_, ?_⟩
  · rw [← hs]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hzero i
  · ext z
    have hz := DFunLike.congr_fun hcomp (e.symm z)
    simpa [α, φ₀] using hz

end Algebra
