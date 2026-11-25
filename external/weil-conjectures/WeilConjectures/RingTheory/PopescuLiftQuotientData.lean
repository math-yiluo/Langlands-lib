/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftInduction
import WeilConjectures.RingTheory.StrictlyStandardBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.RingHom.Smooth

/-!
# Quotient data for the Popescu lifting induction

Source: Stacks Project, Lemma 07F8, final paragraph.
(blueprint: lem-weil-pbc-popescu-lift-quotient-data)
-/

@[expose] public section

universe u v w

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- Transport the witnesses, retaining the same relations and polynomial lifts. -/
private theorem strictlyStandard_equiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [FinitePresentation R S] [FinitePresentation R T]
    (e : S ≃ₐ[R] T) (a : S) (ha : IsStrictlyStandardElement (R := R) a) :
    IsStrictlyStandardElement (R := R) (e a) := by
  classical
  obtain ⟨n, m, c, P, hc, b, hab, hrel⟩ := ha
  refine ⟨n, m, c, P.ofAlgEquiv e, hc, fun s ↦ e (b s), ?_, ?_⟩
  · have hev (f : MvPolynomial (Fin n) R) :
        MvPolynomial.aeval (P.ofAlgEquiv e).val f = e (MvPolynomial.aeval P.val f) := by
      change MvPolynomial.aeval (e ∘ P.val) f = _
      exact (MvPolynomial.comp_aeval_apply P.val e.toAlgHom f).symm
    rw [hab, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [map_mul]
    congr 1
    calc
      e (Matrix.det _) = Matrix.det (e.toRingHom.mapMatrix _) := e.map_det _
      _ = _ := by
        congr 1
        funext j i
        exact (hev _).symm
  · intro j hj
    simpa [Presentation.ofAlgEquiv, Generators.ofAlgEquiv, Generators.σ] using hrel j hj

/-- Split the preceding powers into the first power and the preceding tail. -/
private theorem prefix_span_succ
    {S : Type*} [CommRing S] {n : ℕ} (π : Fin (n + 1) → S) (j : Fin n) :
    Ideal.span {y | ∃ i : Fin (n + 1), i.val < j.succ.val ∧ y = π i ^ 8} =
      Ideal.span (Set.range (fun _ : Fin 1 ↦ π 0 ^ 8)) ⊔
        Ideal.span {y | ∃ k : Fin n, k.val < j.val ∧ y = π k.succ ^ 8} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    revert hi
    refine Fin.cases (fun _ ↦ ?_) (fun k hk ↦ ?_) i
    · exact Ideal.mem_sup_left (Ideal.subset_span ⟨0, rfl⟩)
    · exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, Nat.lt_of_succ_lt_succ hk, rfl⟩)
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro y ⟨i, rfl⟩
      exact Ideal.subset_span ⟨0, Nat.zero_lt_succ _, rfl⟩
    · apply Ideal.span_le.mpr
      rintro y ⟨k, hk, rfl⟩
      exact Ideal.subset_span ⟨k.succ, Nat.succ_lt_succ hk, rfl⟩

/-- Compute the kernel of the preceding-tail quotient using surjectivity. -/
private theorem prefix_comap
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] {n : ℕ}
    (π : Fin (n + 1) → S) (p : S →+* T) (hp : Function.Surjective p)
    (hker : RingHom.ker p = Ideal.span (Set.range (fun _ : Fin 1 ↦ π 0 ^ 8)))
    (j : Fin n) :
    Ideal.comap p (Ideal.span
      {y | ∃ k : Fin n, k.val < j.val ∧ y = p (π k.succ) ^ 8}) =
      Ideal.span {y | ∃ i : Fin (n + 1), i.val < j.succ.val ∧ y = π i ^ 8} := by
  have himage : {y | ∃ k : Fin n, k.val < j.val ∧ y = p (π k.succ) ^ 8} =
      p '' {y | ∃ k : Fin n, k.val < j.val ∧ y = π k.succ ^ 8} := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨π k.succ ^ 8, ⟨k, hk, rfl⟩, map_pow p _ _⟩
    · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, map_pow p _ _⟩
  rw [himage, ← Ideal.map_span, Ideal.comap_map_of_surjective p hp,
    ← RingHom.ker_eq_comap_bot, hker,
    sup_comm, ← prefix_span_succ π j]

/-- Quotient representatives transport multiplication kernels to the tail. -/
private theorem tail_annihilator
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] {n : ℕ}
    (π : Fin (n + 1) → S) (p : S →+* T) (hp : Function.Surjective p)
    (hker : RingHom.ker p = Ideal.span (Set.range (fun _ : Fin 1 ↦ π 0 ^ 8)))
    (h : ∀ (i : Fin (n + 1))
      (x : S ⧸ Ideal.span {y | ∃ k : Fin (n + 1), k.val < i.val ∧ y = π k ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (j : Fin n)
    (x : T ⧸ Ideal.span {y | ∃ k : Fin n, k.val < j.val ∧ y = p (π k.succ) ^ 8}) :
    p (π j.succ) • x = 0 ↔ p (π j.succ) ^ 2 • x = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, rfl⟩ := hp x
  have hx := h j.succ (Ideal.Quotient.mk _ x)
  change Ideal.Quotient.mk _ (π j.succ * x) = 0 ↔
    Ideal.Quotient.mk _ (π j.succ ^ 2 * x) = 0 at hx
  change Ideal.Quotient.mk _ (p (π j.succ) * p x) = 0 ↔
    Ideal.Quotient.mk _ (p (π j.succ) ^ 2 * p x) = 0
  simp only [Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  rw [← map_mul, ← map_pow, ← map_mul]
  rw [← prefix_comap π p hp hker j] at hx
  simpa only [Ideal.mem_comap] using hx

/-- Smooth principal localizations are invariant under simultaneous ring isomorphisms. -/
private theorem singular_semi_le
    {R : Type*} {S : Type*} {A : Type*} {B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (eR : R ≃+* S) (eA : A ≃+* B)
    (hc : ∀ r, eA (algebraMap R A r) = algebraMap S B (eR r)) :
    Ideal.map eA.toRingHom (singularIdeal R A) ≤ singularIdeal S B := by
  unfold singularIdeal
  refine (Ideal.map_radical_le eA.toRingHom).trans (Ideal.radical_mono ?_)
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro a ha
  apply Ideal.subset_span
  change Smooth S (Localization.Away (eA a))
  have : Smooth R (Localization.Away a) := ha
  let E : Localization.Away a ≃+* Localization.Away (eA a) :=
    IsLocalization.ringEquivOfRingEquiv _ _ eA (Submonoid.map_powers eA a)
  have he : algebraMap S (Localization.Away (eA a)) =
      (E.toRingHom.comp (algebraMap R (Localization.Away a))).comp eR.symm.toRingHom := by
    ext r
    change algebraMap S _ r = E (algebraMap R _ (eR.symm r))
    rw [IsScalarTower.algebraMap_apply R A, IsScalarTower.algebraMap_apply S B]
    dsimp only [E]
    rw [IsLocalization.ringEquivOfRingEquiv_eq, hc, eR.apply_symm_apply]
  rw [← RingHom.smooth_algebraMap, he]
  exact ((RingHom.Smooth.of_bijective eR.symm.bijective).comp
    ((RingHom.smooth_algebraMap.mpr inferInstance).comp
      (RingHom.Smooth.of_bijective E.bijective)))

/-- Finite presentation is invariant under the same commuting isomorphism square. -/
private theorem finitePresentation_semi
    {R : Type*} {S : Type*} {A : Type*} {B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] [FinitePresentation R A]
    (eR : R ≃+* S) (eA : A ≃+* B)
    (hc : ∀ r, eA (algebraMap R A r) = algebraMap S B (eR r)) :
    FinitePresentation S B := by
  rw [← RingHom.finitePresentation_algebraMap]
  have he : algebraMap S B =
      (eA.toRingHom.comp (algebraMap R A)).comp eR.symm.toRingHom := by
    ext r
    change algebraMap S B r = eA (algebraMap R A (eR.symm r))
    rw [hc, eR.apply_symm_apply]
  rw [he]
  exact ((RingHom.FinitePresentation.of_bijective eA.bijective).comp
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)).comp
      (RingHom.FinitePresentation.of_bijective eR.symm.bijective)

/-- Equality of singular ideals follows by applying the inclusion in both directions. -/
private theorem singular_semi_eq
    {R : Type*} {S : Type*} {A : Type*} {B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (eR : R ≃+* S) (eA : A ≃+* B)
    (hc : ∀ r, eA (algebraMap R A r) = algebraMap S B (eR r)) :
    Ideal.map eA.toRingHom (singularIdeal R A) = singularIdeal S B := by
  apply le_antisymm (singular_semi_le eR eA hc)
  have hi : ∀ s, eA.symm (algebraMap S B s) = algebraMap R A (eR.symm s) := by
    intro s
    apply eA.injective
    rw [eA.apply_symm_apply, hc, eR.apply_symm_apply]
  have h := Ideal.map_mono (f := eA.toRingHom) (singular_semi_le eR.symm eA.symm hi)
  have hid : eA.toRingHom.comp eA.symm.toRingHom = RingHom.id B := by ext; simp
  simpa only [Ideal.map_map, hid, Ideal.map_id] using h

/-- The extended radical singular ideal is preserved by an isomorphic diagram. -/
private theorem popescuIdeal_semi_eq
    {R : Type*} {S : Type*} {A : Type*} {B : Type*} {L : Type*} {M : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing L] [CommRing M]
    [Algebra R A] [Algebra S B] [Algebra R L] [Algebra S M]
    (eR : R ≃+* S) (eA : A ≃+* B) (eL : L ≃+* M)
    (hc : ∀ r, eA (algebraMap R A r) = algebraMap S B (eR r))
    (α : A →ₐ[R] L) (β : B →ₐ[S] M)
    (hα : ∀ a, eL (α a) = β (eA a)) :
    Ideal.map eL.toRingHom (popescuIdeal α) = popescuIdeal β := by
  have hsing := singular_semi_eq eR eA hc
  have hcomp : eL.toRingHom.comp α.toRingHom = β.toRingHom.comp eA.toRingHom := by
    ext a
    exact hα a
  unfold popescuIdeal
  rw [Ideal.map_radical_of_surjective eL.surjective (by simp),
    Ideal.map_map, hcomp, ← Ideal.map_map, hsing]

/-- Transport the intermediate algebra, its factorization, and both ideal conditions. -/
private theorem resolution_semi
    {R S : Type u} {A B : Type v} {L M : Type w}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing L] [CommRing M]
    [Algebra R A] [Algebra S B] [Algebra R L] [Algebra S M]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [FinitePresentation R A] [FinitePresentation S B]
    (eR : R ≃+* S) (eA : A ≃+* B) (eL : L ≃+* M)
    (hcA : ∀ r, eA (algebraMap R A r) = algebraMap S B (eR r))
    (hcL : ∀ r, eL (algebraMap R L r) = algebraMap S M (eR r))
    (α : A →ₐ[R] L) (β : B →ₐ[S] M)
    (hα : ∀ a, eL (α a) = β (eA a)) (q : PrimeSpectrum L) (p : PrimeSpectrum M)
    (hq : PrimeSpectrum.comap eL.toRingHom p = q)
    (h : CanBePopescuResolved α q) : CanBePopescuResolved β p := by
  obtain ⟨C, hC, hRC, f, g, hfp, hgf, hle, hnot⟩ := h
  let : Algebra S C := ((algebraMap R C).comp eR.symm.toRingHom).toAlgebra
  have hcC (r : R) : algebraMap R C r = algebraMap S C (eR r) := by
    change algebraMap R C r = algebraMap R C (eR.symm (eR r))
    rw [eR.symm_apply_apply]
  let f' : B →ₐ[S] C :=
    { __ := f.toRingHom.comp eA.symm.toRingHom
      commutes' s := by
        change f (eA.symm (algebraMap S B s)) = algebraMap R C (eR.symm s)
        have hh := hcA (eR.symm s)
        rw [eR.apply_symm_apply] at hh
        rw [← hh, eA.symm_apply_apply, f.commutes] }
  let g' : C →ₐ[S] M :=
    { __ := eL.toRingHom.comp g.toRingHom
      commutes' s := by
        change eL (g (algebraMap R C (eR.symm s))) = algebraMap S M s
        rw [g.commutes, hcL, eR.apply_symm_apply] }
  have hf' (a : A) : f a = f' (eA a) := by
    change f a = f (eA.symm (eA a))
    rw [eA.symm_apply_apply]
  have hg' (c : C) : eL (g c) = g' c := rfl
  have hfp' : FinitePresentation S C := finitePresentation_semi eR (RingEquiv.refl C) hcC
  refine ⟨C, hC, inferInstance, f', g', hfp', ?_, ?_, ?_⟩
  · ext b
    obtain ⟨a, rfl⟩ := eA.surjective b
    rw [AlgHom.comp_apply, ← hf', ← hg']
    have hgfa : g (f a) = α a := AlgHom.congr_fun hgf a
    rw [hgfa, hα]
  · rw [← popescuIdeal_semi_eq eR eA eL hcA α β hα,
      ← popescuIdeal_semi_eq eR (RingEquiv.refl C) eL hcC g g' hg']
    exact Ideal.map_mono hle
  · intro hp
    apply hnot
    rw [← hq]
    exact Ideal.map_le_iff_le_comap.mp
      ((popescuIdeal_semi_eq eR (RingEquiv.refl C) eL hcC g g' hg').le.trans hp)

/-- The first generator vanishes, so the remaining powers generate the total image ideal. -/
private theorem tail_span_eq_map
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] {n : ℕ}
    (π : Fin (n + 1) → S) (p : S →+* T) (hzero : p (π 0 ^ 8) = 0) :
    Ideal.span (Set.range (fun j : Fin n ↦ p (π j.succ) ^ 8)) =
      Ideal.map p (Ideal.span (Set.range (fun i : Fin (n + 1) ↦ π i ^ 8))) := by
  rw [Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨j, rfl⟩
    apply Ideal.subset_span
    exact ⟨π j.succ ^ 8, ⟨j.succ, rfl⟩, map_pow p _ _⟩
  · apply Ideal.span_le.mpr
    rintro x ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [hzero]
      exact Ideal.zero_mem _
    · rw [map_pow]
      exact Ideal.subset_span ⟨j, rfl⟩

/-- Third-isomorphism equivalence with the second ideal supplied by an equality. -/
private def doubleQuotEquiv
    {S : Type*} [CommRing S] (J K : Ideal S) (U : Ideal (S ⧸ J))
    (hJK : J ≤ K) (hU : U = Ideal.map (Ideal.Quotient.mk J) K) :
    ((S ⧸ J) ⧸ U) ≃+* S ⧸ K :=
  (Ideal.quotEquivOfEq hU).trans (DoubleQuot.quotQuotEquivQuotOfLE hJK)

private theorem doubleQuotEquiv_mk_mk
    {S : Type*} [CommRing S] (J K : Ideal S) (U : Ideal (S ⧸ J))
    (hJK : J ≤ K) (hU : U = Ideal.map (Ideal.Quotient.mk J) K) (s : S) :
    doubleQuotEquiv J K U hJK hU
      (Ideal.Quotient.mk U (Ideal.Quotient.mk J s)) = Ideal.Quotient.mk K s := by
  subst U
  rfl

set_option linter.unusedVariables false in
/-- Construct the first quotient and transport the remaining-list hypotheses, without
using the induction assertion or concluding that this first quotient is resolved.
Source: Stacks Project, Lemma 07F8 (lemma-lift-solution), final paragraph.
(blueprint: lem-weil-pbc-popescu-lift-quotient-data)

Proof:
Let J be the ideal generated by the first eighth power and use its extensions to A and Λ.
Since α is an R-algebra map, it sends the extension in A into the extension in Λ. Thus
it induces α₀ by the quotient universal property. Since π₀ maps into q, its eighth power
and the generated ideal lie in q. The ideal correspondence for the surjective quotient
map gives the unique prime q₀ pulling back to q. Both compatibility equations follow
on quotient representatives. The quotient base is Noetherian. The quotient A₀ is the
base change of A to R₀, so it is finitely presented over R₀.
For j in Fin n use the image of π(j.succ) as the tail element. Its image belongs to q₀
by the prime compatibility equation. Quotienting R₀ by the preceding tail eighth powers
identifies with quotienting R by the powers indexed strictly below j.succ; the same
holds for Λ₀. Indeed both kernels are generated by π₀⁸ and the powers π(k.succ)⁸ for
k < j. Construct the identifications on representatives, where multiplication by the
tail element agrees with multiplication by π(j.succ). The original annihilator
hypotheses therefore give the two tail annihilator equivalences.
Strict standardness of π(j.succ) survives tensor base change by Lemma 07CC. The
quotient-tensor identification carries that tensor element to its quotient class:
transport the presentation and its Jacobian identities along this algebra equivalence.
Finally, quotienting by all tail powers has the same kernel as quotienting originally
by all n+1 powers. The corresponding algebra equivalences commute with the induced maps
and carry the final prime to the given one. Transport the given resolution factorization
along these equivalences: finite presentation is invariant under algebra equivalence;
principal localizations are isomorphic, preserving smoothness and hence singular ideals,
their mapped radicals, and both resolution ideal conditions. This supplies the tail
quotient resolution. No lifting or induction hypothesis is used in this construction.
The maps and prime in the conclusion are uniquely determined by their compatibility
with the surjective quotient maps; no arbitrary algebra carrier is chosen. -/
theorem popescuEighthPowerLifting_quotientData
    (n : ℕ) (hn : 1 ≤ n)
    (R : Type u) (A : Type v) (Λ : Type w)
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (π : Fin (n + 1) → R) (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hπ : ∀ i : Fin (n + 1), algebraMap R Λ (π i) ∈ q.asIdeal)
    (hR : ∀ (i : Fin (n + 1))
      (x : R ⧸ Ideal.span {y | ∃ j : Fin (n + 1), j.val < i.val ∧ y = π j ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hΛ : ∀ (i : Fin (n + 1))
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin (n + 1), j.val < i.val ∧ y = algebraMap R Λ (π j) ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hstandard : ∀ i : Fin (n + 1), IsStrictlyStandardElement (R := R) (algebraMap R A (π i)))
    (hresolved : PopescuEighthPowerQuotientResolved (n + 1) π α q) :
    let J := Ideal.span (Set.range (fun _ : Fin 1 ↦ π 0 ^ 8))
    let J_A := Ideal.map (algebraMap R A) J
    let J_Λ := Ideal.map (algebraMap R Λ) J
    let R₀ := R ⧸ J
    let A₀ := A ⧸ J_A
    let Λ₀ := Λ ⧸ J_Λ
    let τ : Fin n → R₀ := fun j ↦ Ideal.Quotient.mk J (π j.succ)
    ∃ (_ : FinitePresentation R₀ A₀) (α₀ : A₀ →ₐ[R₀] Λ₀) (q₀ : PrimeSpectrum Λ₀),
      α₀.toRingHom.comp (Ideal.Quotient.mk J_A) =
        (Ideal.Quotient.mk J_Λ).comp α.toRingHom ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
      (∀ j : Fin n, algebraMap R₀ Λ₀ (τ j) ∈ q₀.asIdeal) ∧
      (∀ (j : Fin n)
        (x : R₀ ⧸ Ideal.span {y | ∃ k : Fin n, k.val < j.val ∧ y = τ k ^ 8}),
        τ j • x = 0 ↔ τ j ^ 2 • x = 0) ∧
      (∀ (j : Fin n)
        (x : Λ₀ ⧸ Ideal.span
          {y | ∃ k : Fin n, k.val < j.val ∧ y = algebraMap R₀ Λ₀ (τ k) ^ 8}),
        τ j • x = 0 ↔ τ j ^ 2 • x = 0) ∧
      (∀ j : Fin n, IsStrictlyStandardElement (R := R₀) (algebraMap R₀ A₀ (τ j))) ∧
      PopescuEighthPowerQuotientResolved n τ α₀ q₀ := by
  classical
  let J := Ideal.span (Set.range (fun _ : Fin 1 ↦ π 0 ^ 8))
  let J_A := Ideal.map (algebraMap R A) J
  let J_Λ := Ideal.map (algebraMap R Λ) J
  let R₀ := R ⧸ J
  let A₀ := A ⧸ J_A
  let Λ₀ := Λ ⧸ J_Λ
  let τ : Fin n → R₀ := fun j ↦ Ideal.Quotient.mk J (π j.succ)
  have hfp : FinitePresentation R₀ A₀ :=
    FinitePresentation.equiv (TensorProduct.quotIdealMapEquivQuotTensor A J).symm
  have hmap : J_A ≤ Ideal.comap α.toRingHom J_Λ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change α (algebraMap R A r) ∈ J_Λ
    rw [α.commutes]
    exact Ideal.mem_map_of_mem (algebraMap R Λ) hr
  let αR := Ideal.quotientMapₐ J_Λ α hmap
  let α₀ : A₀ →ₐ[R₀] Λ₀ :=
    AlgHom.extendScalarsOfSurjective Ideal.Quotient.mk_surjective αR
  have hcomm : α₀.toRingHom.comp (Ideal.Quotient.mk J_A) =
      (Ideal.Quotient.mk J_Λ).comp α.toRingHom := by
    ext a
    rfl
  have hJq : J_Λ ≤ q.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro r ⟨i, rfl⟩
    change algebraMap R Λ (π 0 ^ 8) ∈ q.asIdeal
    rw [map_pow]
    exact Ideal.pow_mem_of_mem _ (hπ 0) 8 (by decide)
  let q₀ : PrimeSpectrum Λ₀ :=
    ⟨q.asIdeal.map (Ideal.Quotient.mk J_Λ), Ideal.isPrime_map_quotientMk_of_isPrime hJq⟩
  have hprime : PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_map_mk hJq
  refine ⟨hfp, α₀, q₀, hcomm, hprime, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hj := hπ j.succ
    rw [← hprime] at hj
    exact hj
  · exact tail_annihilator π (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      Ideal.mk_ker hR
  · have hker : RingHom.ker (Ideal.Quotient.mk J_Λ) =
        Ideal.span (Set.range (fun _ : Fin 1 ↦ algebraMap R Λ (π 0) ^ 8)) := by
      rw [Ideal.mk_ker]
      dsimp only [J_Λ, J]
      rw [Ideal.map_span]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, map_pow]
    have hmul : ∀ (i : Fin (n + 1))
        (x : Λ ⧸ Ideal.span
          {y | ∃ k : Fin (n + 1), k.val < i.val ∧ y = algebraMap R Λ (π k) ^ 8}),
        algebraMap R Λ (π i) • x = 0 ↔ algebraMap R Λ (π i) ^ 2 • x = 0 := by
      intro i x
      simpa only [← map_pow, IsScalarTower.algebraMap_smul Λ] using hΛ i x
    intro j x
    have ht := tail_annihilator (fun i ↦ algebraMap R Λ (π i))
      (Ideal.Quotient.mk J_Λ) Ideal.Quotient.mk_surjective hker hmul j x
    have he (r : R) : Ideal.Quotient.mk J_Λ (algebraMap R Λ r) =
        algebraMap R₀ Λ₀ (Ideal.Quotient.mk J r) := rfl
    rw [he, ← map_pow, IsScalarTower.algebraMap_smul Λ₀,
      IsScalarTower.algebraMap_smul Λ₀] at ht
    exact ht
  · intro j
    let e := TensorProduct.quotIdealMapEquivQuotTensor A J
    have hs := (standardElements_baseChange (R' := R₀)
      (algebraMap R A (π j.succ))).2 (hstandard j.succ)
    have he : e.symm (1 ⊗ₜ[R] algebraMap R A (π j.succ)) =
        algebraMap R₀ A₀ (τ j) := by
      apply e.injective
      simp only [AlgEquiv.apply_symm_apply]
      rfl
    rw [← he]
    exact strictlyStandard_equiv e.symm _ hs
  · let K := Ideal.span (Set.range (fun i : Fin (n + 1) ↦ π i ^ 8))
    let K_A := Ideal.map (algebraMap R A) K
    let K_Λ := Ideal.map (algebraMap R Λ) K
    let U := Ideal.span (Set.range (fun j : Fin n ↦ τ j ^ 8))
    let U_A := Ideal.map (algebraMap R₀ A₀) U
    let U_Λ := Ideal.map (algebraMap R₀ Λ₀) U
    have hJK : J ≤ K := by
      apply Ideal.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact Ideal.subset_span ⟨0, rfl⟩
    have hU : U = Ideal.map (Ideal.Quotient.mk J) K :=
      tail_span_eq_map π (Ideal.Quotient.mk J)
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0, rfl⟩))
    have hUA : U_A = Ideal.map (Ideal.Quotient.mk J_A) K_A := by
      dsimp only [U_A]
      rw [hU, Ideal.map_map]
      dsimp only [K_A]
      rw [Ideal.map_map]
      congr 1
    have hUΛ : U_Λ = Ideal.map (Ideal.Quotient.mk J_Λ) K_Λ := by
      dsimp only [U_Λ]
      rw [hU, Ideal.map_map]
      dsimp only [K_Λ]
      rw [Ideal.map_map]
      congr 1
    let R₁ := R₀ ⧸ U
    let A₁ := A₀ ⧸ U_A
    let Λ₁ := Λ₀ ⧸ U_Λ
    let eR : R₁ ≃+* R ⧸ K := doubleQuotEquiv J K U hJK hU
    let eA : A₁ ≃+* A ⧸ K_A :=
      doubleQuotEquiv J_A K_A U_A (Ideal.map_mono hJK) hUA
    let eΛ : Λ₁ ≃+* Λ ⧸ K_Λ :=
      doubleQuotEquiv J_Λ K_Λ U_Λ (Ideal.map_mono hJK) hUΛ
    have heR (r : R) : eR (Ideal.Quotient.mk U (Ideal.Quotient.mk J r)) =
        Ideal.Quotient.mk K r := doubleQuotEquiv_mk_mk J K U hJK hU r
    have heA (a : A) : eA (Ideal.Quotient.mk U_A (Ideal.Quotient.mk J_A a)) =
        Ideal.Quotient.mk K_A a := doubleQuotEquiv_mk_mk _ _ _ _ _ a
    have heΛ (a : Λ) : eΛ (Ideal.Quotient.mk U_Λ (Ideal.Quotient.mk J_Λ a)) =
        Ideal.Quotient.mk K_Λ a := doubleQuotEquiv_mk_mk _ _ _ _ _ a
    have hcA (r : R₁) : eA (algebraMap R₁ A₁ r) =
        algebraMap (R ⧸ K) (A ⧸ K_A) (eR r) := by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [heR]
      exact heA (algebraMap R A r)
    have hcΛ (r : R₁) : eΛ (algebraMap R₁ Λ₁ r) =
        algebraMap (R ⧸ K) (Λ ⧸ K_Λ) (eR r) := by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [heR]
      exact heΛ (algebraMap R Λ r)
    obtain ⟨hfpbar, αbar, qbar, hcommbar, hprimebar, hresbar⟩ := hresolved
    have hfp₁ : FinitePresentation R₁ A₁ :=
      FinitePresentation.equiv (TensorProduct.quotIdealMapEquivQuotTensor A₀ U).symm
    let α₁ : A₁ →ₐ[R₁] Λ₁ :=
      { __ := eΛ.symm.toRingHom.comp (αbar.toRingHom.comp eA.toRingHom)
        commutes' r := by
          apply eΛ.injective
          change eΛ (eΛ.symm (αbar (eA (algebraMap R₁ A₁ r)))) =
            eΛ (algebraMap R₁ Λ₁ r)
          rw [eΛ.apply_symm_apply, hcA, αbar.commutes, hcΛ] }
    let q₁ := PrimeSpectrum.comap eΛ.toRingHom qbar
    have hres₁ : CanBePopescuResolved α₁ q₁ := by
      apply resolution_semi eR.symm eA.symm eΛ.symm ?_ ?_ αbar α₁ ?_ qbar q₁ ?_ hresbar
      · intro r
        apply eA.injective
        rw [eA.apply_symm_apply, hcA, eR.apply_symm_apply]
      · intro r
        apply eΛ.injective
        rw [eΛ.apply_symm_apply, hcΛ, eR.apply_symm_apply]
      · intro a
        change eΛ.symm (αbar a) = eΛ.symm (αbar (eA (eA.symm a)))
        rw [eA.apply_symm_apply]
      · apply PrimeSpectrum.ext
        ext x
        change eΛ (eΛ.symm x) ∈ qbar.asIdeal ↔ x ∈ qbar.asIdeal
        rw [eΛ.apply_symm_apply]
    refine ⟨hfp₁, α₁, q₁, ?_, ?_, hres₁⟩
    · ext a
      apply eΛ.injective
      change eΛ (eΛ.symm (αbar (eA
        (Ideal.Quotient.mk U_A (Ideal.Quotient.mk J_A a))))) =
          eΛ (Ideal.Quotient.mk U_Λ (α₀ (Ideal.Quotient.mk J_A a)))
      rw [eΛ.apply_symm_apply, heA]
      have hca : α₀ (Ideal.Quotient.mk J_A a) = Ideal.Quotient.mk J_Λ (α a) :=
        RingHom.congr_fun hcomm a
      rw [hca, heΛ]
      exact RingHom.congr_fun hcommbar a
    · apply PrimeSpectrum.comap_injective_of_surjective
        (Ideal.Quotient.mk J_Λ) Ideal.Quotient.mk_surjective
      apply PrimeSpectrum.ext
      ext x
      change eΛ (Ideal.Quotient.mk U_Λ (Ideal.Quotient.mk J_Λ x)) ∈ qbar.asIdeal ↔
        Ideal.Quotient.mk J_Λ x ∈ q₀.asIdeal
      rw [heΛ]
      have hb := congrArg (fun p : PrimeSpectrum Λ ↦ x ∈ p.asIdeal) hprimebar
      have hq := congrArg (fun p : PrimeSpectrum Λ ↦ x ∈ p.asIdeal) hprime
      exact Iff.of_eq (hb.trans hq.symm)

end Algebra
