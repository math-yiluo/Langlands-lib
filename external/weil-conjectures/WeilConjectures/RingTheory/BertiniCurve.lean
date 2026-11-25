/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.RingTheory.BertiniConnected
public import WeilConjectures.RingTheory.BertiniHypersurface
public import WeilConjectures.RingTheory.BertiniSmooth
public import WeilConjectures.RingTheory.BertiniCurveAux
public import WeilConjectures.RingTheory.BertiniCurveLinear

/-!
# Ring-level Bertini: smooth connected curve sections of finite étale covers

Let `A` be a smooth finite type domain over an algebraically closed field `k`, with module of
differentials of rank `d ≥ 2`, `B` a finite étale `A`-algebra with connected spectrum, and `S` a
finite nonempty set of maximal ideals of `A`. We find an ideal `J` of `A` contained in every
`m ∈ S` such that `A ⧸ J` is a smooth domain of dimension one over `k` and `B ⧸ J B` has connected
spectrum (`Algebra.Smooth.exists_quotient_curve_connectedSpace`).

The proof cuts down by one generic hypersurface section at a time: a generic member `f` of a
linear system with base locus `S` gives a smooth domain `A ⧸ (f)` of one less dimension
(`Algebra.Smooth.exists_ne_zero_forall_notMem_sq` and `Algebra.Smooth.quotient_span_singleton`),
over which `B ⧸ f B` stays connected (`exists_ne_zero_forall_connectedSpace_quotient`).

## References

- Stacks Project, Tags 0FD5, 0FD6, 0G4F.
-/

@[expose] public section

universe u

/-- The connectedness of the spectrum is invariant under ring isomorphisms. -/
theorem PrimeSpectrum.connectedSpace_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) [ConnectedSpace (PrimeSpectrum R)] : ConnectedSpace (PrimeSpectrum S) :=
  (homeomorphOfRingEquiv e).surjective.connectedSpace (homeomorphOfRingEquiv e).continuous

/-- If `S` is an integral extension of `R` and `I` an ideal of `R` such that `S ⧸ I S` has
connected spectrum, then `R ⧸ I` has connected spectrum: by lying over, every prime of `R`
containing `I` is the contraction of a prime of `S` containing `I S`. -/
theorem PrimeSpectrum.connectedSpace_quotient_of_isIntegral {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (I : Ideal R)
    [ConnectedSpace (PrimeSpectrum (S ⧸ I.map (algebraMap R S)))] :
    ConnectedSpace (PrimeSpectrum (R ⧸ I)) := by
  refine Function.Surjective.connectedSpace
    (f := PrimeSpectrum.comap (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))) ?_
    (PrimeSpectrum.continuous_comap _)
  intro p
  set P := p.asIdeal.comap (Ideal.Quotient.mk I)
  have hIP : I ≤ P := fun x hx ↦ by
    simp [P, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ P := by
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P ⊥ hker
  rw [Ideal.under_def] at hQP
  have hIQ : I.map (algebraMap R S) ≤ Q := Ideal.map_le_iff_le_comap.2 (hQP ▸ hIP)
  refine ⟨⟨Q.map (Ideal.Quotient.mk _), Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.mem_quotient_iff_mem hIQ,
    ← Ideal.mem_comap, hQP, Ideal.mem_comap]

/-- The image of a maximal ideal containing `I` in `R ⧸ I` is maximal. -/
theorem Ideal.isMaximal_map_quotientMk {R : Type*} [CommRing R] {I m : Ideal R}
    (hm : m.IsMaximal) (hI : I ≤ m) : (m.map (Ideal.Quotient.mk I)).IsMaximal :=
  (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hm).resolve_left
    fun h ↦ hm.ne_top ((Ideal.eq_top_iff_one _).2 ((Ideal.mem_quotient_iff_mem hI (x := 1)).1
      (by rw [h]; exact Submodule.mem_top)))

section QuotientMapQuotient

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

/-- The base change of a finite algebra to `A ⧸ I` is finite. -/
theorem Module.Finite.quotientMapQuotient [Module.Finite A B] :
    Module.Finite (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  .equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv

/-- The base change of an étale algebra to `A ⧸ I` is étale. -/
theorem Algebra.Etale.quotientMapQuotient [Algebra.Etale A B] :
    Algebra.Etale (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm

/-- The scalar tower `k → A ⧸ I → B ⧸ I B`. -/
theorem IsScalarTower.quotientMapQuotient [Algebra k A] [Algebra k B] [IsScalarTower k A B] :
    IsScalarTower k (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k A (A ⧸ I), ← IsScalarTower.algebraMap_apply A (A ⧸ I),
      IsScalarTower.algebraMap_apply k A (B ⧸ I.map (algebraMap A B))]

end QuotientMapQuotient

open scoped Pointwise

/-- **One Bertini cut.** Let `A` be a smooth finite type domain over an algebraically closed field
`k` whose differentials have rank `e + 2`, `B` a finite étale `A`-algebra with connected spectrum
and `S` a finite nonempty set of maximal ideals. There is `f` in every `m ∈ S` such that
`A ⧸ (f)` is a smooth domain whose differentials have rank `e + 1` and `B ⧸ f B` has connected
spectrum: take a generic member of a linear system with base locus `S`.
(blueprint: `lemma-curve-preserving-finite-cover--1`) -/
theorem Algebra.Smooth.exists_mem_quotient_span_singleton_connectedSpace {k A B : Type u}
    [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Algebra.Smooth k A] {e : ℕ} (hA : Module.rank A Ω[A⁄k] = (e + 1 : ℕ) + 1)
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B] [Algebra k B]
    [IsScalarTower k A B] [ConnectedSpace (PrimeSpectrum B)]
    (S : Set (Ideal A)) (hS : S.Finite) (hSmax : ∀ m ∈ S, m.IsMaximal) (hSne : S.Nonempty) :
    ∃ f : A, (∀ m ∈ S, f ∈ m) ∧ IsDomain (A ⧸ Ideal.span {f}) ∧
      Algebra.Smooth k (A ⧸ Ideal.span {f}) ∧
      Module.rank (A ⧸ Ideal.span {f}) Ω[(A ⧸ Ideal.span {f})⁄k] = (e + 1 : ℕ) ∧
      ConnectedSpace (PrimeSpectrum (B ⧸ (Ideal.span {f}).map (algebraMap A B))) := by
  obtain ⟨M, v, hgen, hvS, hcot, hbase⟩ := exists_linearSystem_of_finite (k := k) S hS hSmax
  have : Algebra.Smooth k B := Algebra.Smooth.comp k A B
  have : IsDomain B := Algebra.Smooth.isDomain_of_connectedSpace (k := k)
  have hdim : 2 ≤ ringKrullDim A := by
    have := Algebra.Smooth.natCast_le_ringKrullDim (k := k) (A := A) (n := e + 2)
      (by rw [hA]; push_cast; ring)
    exact le_trans (by exact_mod_cast (by omega : 2 ≤ e + 2)) this
  have hS0 : ⊥ ∉ S := fun hbot ↦ by
    rw [ringKrullDim_eq_zero_of_isField (Ring.isField_iff_maximal_bot.mpr (hSmax ⊥ hbot))]
      at hdim
    norm_num at hdim
  obtain ⟨h, hh0, hh⟩ :=
    Algebra.Smooth.exists_ne_zero_forall_notMem_sq v S hS hgen hvS hcot hS0
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_connectedSpace_quotient (k := k) (B := B) hdim v S
    hS hSmax hSne hvS hbase
  obtain ⟨b, hb⟩ : ∃ b : Fin M → k, MvPolynomial.eval b (h * a) ≠ 0 := by
    by_contra! H
    exact mul_ne_zero hh0 ha0 (MvPolynomial.funext fun x ↦ by simpa using H x)
  rw [map_mul] at hb
  set f := ∑ i, b i • v i with hf
  have hfS (m : Ideal A) (hm : m ∈ S) : f ∈ m :=
    Ideal.sum_mem _ fun i _ ↦ Submodule.smul_of_tower_mem _ _ (hvS m hm i)
  obtain ⟨hsm, hrk⟩ :=
    Algebra.Smooth.quotient_span_singleton hA f (hh b (left_ne_zero_of_mul hb))
  have hconnB : ConnectedSpace (PrimeSpectrum (B ⧸ (Ideal.span {f}).map (algebraMap A B))) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact ha b (right_ne_zero_of_mul hb)
  have hinj : Function.Injective (algebraMap A B) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    rw [Algebra.algebraMap_eq_smul_one] at hx
    exact (smul_eq_zero.1 hx).resolve_right one_ne_zero
  have : ConnectedSpace (PrimeSpectrum (A ⧸ Ideal.span {f})) :=
    PrimeSpectrum.connectedSpace_quotient_of_isIntegral hinj _
  have : IsDomain (A ⧸ Ideal.span {f}) := Algebra.Smooth.isDomain_of_connectedSpace (k := k)
  exact ⟨f, hfS, this, hsm, hrk this, hconnB⟩

/-- The conclusion of the ring-level Bertini theorem is invariant under replacing `A ⧸ J` and
`B ⧸ J B` by isomorphic rings. -/
theorem Algebra.Smooth.curve_connectedSpace_of_equiv {k R R' T T' : Type u} [Field k]
    [CommRing R] [CommRing R'] [Algebra k R] [Algebra k R'] [CommRing T] [CommRing T']
    (e : R ≃ₐ[k] R') (e' : T ≃+* T')
    (h : IsDomain R ∧ Algebra.Smooth k R ∧ Module.rank R Ω[R⁄k] = 1 ∧
      ConnectedSpace (PrimeSpectrum T)) :
    IsDomain R' ∧ Algebra.Smooth k R' ∧ Module.rank R' Ω[R'⁄k] = 1 ∧
      ConnectedSpace (PrimeSpectrum T') := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨e.symm.injective.isDomain e.symm.toRingHom, .of_equiv e, ?_,
    PrimeSpectrum.connectedSpace_of_ringEquiv e'⟩
  rw [← KaehlerDifferential.rank_eq_of_algEquiv e, h₃]

/-- The induction behind `Algebra.Smooth.exists_quotient_curve_connectedSpace`, on the rank
`e + 1` of the differentials. (blueprint: `lemma-curve-preserving-finite-cover--1`) -/
theorem Algebra.Smooth.exists_quotient_curve_connectedSpace_aux {k : Type u} [Field k]
    [IsAlgClosed k] (e : ℕ) :
    ∀ (A B : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
      [Algebra.Smooth k A] [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B]
      [Algebra k B] [IsScalarTower k A B] [ConnectedSpace (PrimeSpectrum B)],
      Module.rank A Ω[A⁄k] = (e + 1 : ℕ) → ∀ S : Set (Ideal A), S.Finite →
      (∀ m ∈ S, m.IsMaximal) → S.Nonempty →
      ∃ J : Ideal A, J.FG ∧ (∀ m ∈ S, J ≤ m) ∧ IsDomain (A ⧸ J) ∧ Algebra.Smooth k (A ⧸ J) ∧
        Module.rank (A ⧸ J) Ω[(A ⧸ J)⁄k] = 1 ∧
        ConnectedSpace (PrimeSpectrum (B ⧸ J.map (algebraMap A B))) := by
  induction e with
  | zero =>
    intro A B _ _ _ _ _ _ _ _ _ _ _ _ hA S hS hSmax hSne
    refine ⟨⊥, Submodule.fg_bot, fun _ _ ↦ bot_le, ?_⟩
    refine Algebra.Smooth.curve_connectedSpace_of_equiv (AlgEquiv.quotientBot k A).symm
      ((RingEquiv.quotientBot B).symm.trans (Ideal.quotEquivOfEq (Ideal.map_bot).symm))
      ⟨inferInstance, inferInstance, ?_, inferInstance⟩
    rw [hA]
    simp
  | succ e ih =>
    intro A B _ _ _ _ _ _ _ _ _ _ _ _ hA S hS hSmax hSne
    obtain ⟨f, hfS, hdom, hsm, hrk, hconn⟩ :=
      Algebra.Smooth.exists_mem_quotient_span_singleton_connectedSpace (k := k) (B := B)
        (e := e) (by rw [hA]; push_cast; ring) S hS hSmax hSne
    set I : Ideal A := Ideal.span {f}
    have := Algebra.FiniteType.isNoetherianRing k A
    have : Algebra.FiniteType k (A ⧸ I) :=
      .of_surjective (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ_surjective k I)
    have := Algebra.Etale.quotientMapQuotient (B := B) I
    have := Module.Finite.quotientMapQuotient (B := B) I
    have := IsScalarTower.quotientMapQuotient (k := k) (B := B) I
    have hIm (m : Ideal A) (hm : m ∈ S) : I ≤ m := (Ideal.span_singleton_le_iff_mem _).2 (hfS m hm)
    obtain ⟨J', -, hJ'S, hJ'⟩ := ih (A ⧸ I) (B ⧸ I.map (algebraMap A B)) hrk
      (Ideal.map (Ideal.Quotient.mk I) '' S) (hS.image _)
      (fun _ ⟨m, hm, hm'⟩ ↦ hm' ▸ Ideal.isMaximal_map_quotientMk (hSmax m hm) (hIm m hm))
      (hSne.image _)
    set J : Ideal A := J'.comap (Ideal.Quotient.mkₐ k I)
    have hIJ : I ≤ J := fun x hx ↦ by
      simp [J, Ideal.Quotient.eq_zero_iff_mem.2 hx]
    have hJJ' : J.map (Ideal.Quotient.mkₐ k I) = J' :=
      Ideal.map_comap_of_surjective _ (Ideal.Quotient.mkₐ_surjective k I) J'
    refine ⟨J, IsNoetherian.noetherian J, fun m hm ↦ ?_, ?_⟩
    · intro x hx
      exact (Ideal.mem_quotient_iff_mem (hIm m hm)).1 (hJ'S _ ⟨m, hm, rfl⟩ hx)
    refine Algebra.Smooth.curve_connectedSpace_of_equiv
      ((Ideal.quotientEquivAlgOfEq k hJJ'.symm).trans (DoubleQuot.quotQuotEquivQuotOfLEₐ k hIJ))
      ((Ideal.quotEquivOfEq ?_).trans
        (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono (f := algebraMap A B) hIJ))) hJ'
    have hJJ'' : J.map (Ideal.Quotient.mk I) = J' :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J'
    rw [← hJJ'', Ideal.map_map, Ideal.map_map]
    rfl

/-- (I) **Ring-level Bertini.** Let `A` be a smooth finite type domain over an algebraically
closed field `k` whose differentials have rank `d ≥ 2`, `B` a finite étale `A`-algebra with
connected spectrum and `S` a finite nonempty set of maximal ideals of `A`. There is an ideal `J`
contained in every `m ∈ S` such that `A ⧸ J` is a smooth curve (a smooth domain whose
differentials have rank one) and `B ⧸ J B` has connected spectrum. This is the ring-level form of
the Bertini argument of Stacks 0FD5, 0FD6, 0G4F.
(blueprint: `lemma-curve-preserving-finite-cover--1`) -/
theorem Algebra.Smooth.exists_quotient_curve_connectedSpace {k A B : Type u} [Field k]
    [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Algebra.Smooth k A] {d : ℕ} (hd : 2 ≤ d) (hA : Module.rank A Ω[A⁄k] = d)
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B] [Algebra k B]
    [IsScalarTower k A B] [ConnectedSpace (PrimeSpectrum B)]
    (S : Set (Ideal A)) (hS : S.Finite) (hSmax : ∀ m ∈ S, m.IsMaximal) (hSne : S.Nonempty) :
    ∃ J : Ideal A, J.FG ∧ (∀ m ∈ S, J ≤ m) ∧ IsDomain (A ⧸ J) ∧ Algebra.Smooth k (A ⧸ J) ∧
      Module.rank (A ⧸ J) Ω[(A ⧸ J)⁄k] = 1 ∧
      ConnectedSpace (PrimeSpectrum (B ⧸ J.map (algebraMap A B))) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
  exact Algebra.Smooth.exists_quotient_curve_connectedSpace_aux e A B hA S hS hSmax hSne
