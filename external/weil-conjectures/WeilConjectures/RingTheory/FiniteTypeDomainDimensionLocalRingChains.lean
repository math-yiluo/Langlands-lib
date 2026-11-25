/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import WeilConjectures.RingTheory.PolynomialRingMaximalChainHeightDifference
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension

/-! Common maximal-chain length part of the finite type domain dimension theorem.

Source: Stacks Project, Algebra, Lemma Tag 00OS, proof steps 1--6
(blueprint: lem-weil-pbc-finite-type-domain-dimension-local-ring-chains)

Proof: present the domain as a quotient of a polynomial ring over the field.
Prime correspondence transfers maximal saturated chains to chains between the
kernel prime and maximal ideals. The polynomial height-difference theorem gives
their common length, and the same bound identifies it with the Krull dimension.
-/

@[expose] public section

universe u v

private theorem saturated_isMaxChain_of_nonempty {α : Type u} [PartialOrder α]
    (c : LTSeries α) (_hα : Nonempty α) (hmin : IsMin c.head) (hmax : IsMax c.last)
    (hcov : ∀ i : Fin c.length, c i.castSucc ⋖ c i.succ) :
    IsMaxChain (fun x y : α ↦ x ≤ y) (Set.range c) := by
  classical
  have hchain : IsChain (fun x y : α ↦ x ≤ y) (Set.range c) := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ _
    exact (le_total i j).imp (fun h ↦ c.monotone h) (fun h ↦ c.monotone h)
  refine ⟨hchain, ?_⟩
  intro t ht hsub
  apply Set.Subset.antisymm hsub
  intro x hx
  have hcomp (i : Fin (c.length + 1)) : c i ≤ x ∨ x ≤ c i := by
    by_cases he : c i = x
    · exact Or.inl he.le
    · exact ht (hsub ⟨i, rfl⟩) hx he
  have hxlast : x ≤ c.last := by
    rcases hcomp (Fin.last c.length) with h | h
    · exact hmax h
    · exact h
  have hex : ∃ j : ℕ, ∃ hj : j < c.length + 1, x ≤ c ⟨j, hj⟩ :=
    ⟨c.length, by omega, hxlast⟩
  let j := Nat.find hex
  obtain ⟨hj, hxj⟩ := Nat.find_spec hex
  change j < c.length + 1 at hj
  change x ≤ c ⟨j, hj⟩ at hxj
  have heq : x = c ⟨j, hj⟩ := by
    by_cases hj0 : j = 0
    · have hi0 : (⟨j, hj⟩ : Fin (c.length + 1)) = 0 := Fin.ext hj0
      have hxhead : x ≤ c.head := by rw [hi0] at hxj; exact hxj
      have hh : c.head ≤ x := hmin hxhead
      simpa [hj0, RelSeries.head] using le_antisymm hxhead hh
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      let i : Fin c.length := ⟨j - 1, by omega⟩
      have hnot : ¬ x ≤ c i.castSucc := by
        intro h
        exact Nat.find_min hex (show j - 1 < j by omega) ⟨by omega, h⟩
      have hprev : c i.castSucc < x :=
        lt_of_le_not_ge ((hcomp i.castSucc).resolve_right hnot) hnot
      have hsucc : c i.succ = c ⟨j, hj⟩ := by
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ, i]
        omega
      exact ((hcov i).eq_or_eq hprev.le (hsucc ▸ hxj)).resolve_left
        (ne_of_gt hprev) |>.trans hsucc
  exact ⟨⟨j, hj⟩, heq.symm⟩

private theorem maxChain_properties {α : Type*} [PartialOrder α]
    (c : LTSeries α) (hc : IsMaxChain (fun x y : α ↦ x ≤ y) (Set.range c)) :
    IsMin c.head ∧ IsMax c.last ∧ ∀ i : Fin c.length, c i.castSucc ⋖ c i.succ := by
  have mem_of_comparable (x : α)
      (h : ∀ j : Fin (c.length + 1), x ≤ c j ∨ c j ≤ x) : x ∈ Set.range c := by
    have hi := hc.1.insert (a := x) (by
      rintro _ ⟨j, rfl⟩ _
      exact h j)
    rw [hc.2 hi (Set.subset_insert _ _)]
    exact Set.mem_insert x _
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, rfl⟩ := mem_of_comparable x (fun j ↦ Or.inl (hx.trans (c.head_le j)))
    exact c.head_le j
  · intro x hx
    obtain ⟨j, rfl⟩ := mem_of_comparable x
      (fun j ↦ Or.inr ((c.monotone (Fin.le_last j)).trans hx))
    exact c.monotone (Fin.le_last j)
  · intro i
    refine ⟨c.step i, ?_⟩
    intro x hix hxi
    obtain ⟨j, rfl⟩ := mem_of_comparable x (fun j ↦ by
      by_cases hj : j ≤ i.castSucc
      · exact Or.inr ((c.monotone hj).trans hix.le)
      · have hij : i.succ ≤ j := by
          simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
          omega
        exact Or.inl (hxi.le.trans (c.monotone hij)))
    have h1 := c.strictMono.lt_iff_lt.mp hix
    have h2 := c.strictMono.lt_iff_lt.mp hxi
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2
    omega

private theorem longest_isMaxChain {α : Type*} [PartialOrder α]
    [FiniteDimensionalOrder α] :
    IsMaxChain (fun x y : α ↦ x ≤ y) (Set.range (LTSeries.longestOf α)) := by
  let c := LTSeries.longestOf α
  have bound (a : LTSeries α) : a.length ≤ c.length := a.longestOf_is_longest
  apply saturated_isMaxChain_of_nonempty c ⟨c.head⟩
  · intro x hx
    by_contra h
    have hlt : x < c.head := lt_of_le_not_ge hx h
    have hb := bound (c.cons x hlt)
    simp only [RelSeries.cons_length] at hb
    omega
  · intro x hx
    by_contra h
    have hlt : c.last < x := lt_of_le_not_ge hx h
    have hb := bound (c.snoc x hlt)
    simp only [RelSeries.snoc_length] at hb
    omega
  · intro i
    refine ⟨c.step i, ?_⟩
    intro x hx hy
    have hb := bound (c.insertNth i x hx hy)
    simp only [RelSeries.insertNth_length] at hb
    omega

/-- The Krull dimension of a finite type domain over a field is a natural
number, and every maximal prime chain has that common length.  The proof uses
the polynomial presentation and the height-difference theorem for maximal
chains (Steps 1--6 of Tag 00OS).

Proof: choose a finite-variable polynomial presentation. Comap preserves strict
prime chains, whose lengths are bounded by the height bound in the polynomial
ring, so the spectrum has finite dimension. A longest chain is maximal: a
nonminimal head, nonmaximal last, or missing intermediate prime would extend it.
For any maximal chain, maximality forces its head to be the zero prime, its
last to be maximal, and its consecutive pairs to be covers. Under prime
correspondence these become a saturated chain from the presentation kernel to
a maximal polynomial ideal. The endpoint has height equal to the number of
variables, so the height-difference theorem gives the same length for every
maximal chain. Compare with the longest chain, whose length is Krull dimension.
(blueprint: lem-weil-pbc-finite-type-domain-dimension-local-ring-chains) -/
theorem finiteTypeDomain_ringKrullDim_localizationAtMaximal_chains
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S] :
    ∃ (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞) ∧
      ∀ (p : LTSeries (PrimeSpectrum S)),
        IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p) →
          p.length = d := by
  classical
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k S)
  let P := MvPolynomial (Fin n) k
  let e := Ideal.primeSpectrumOrderIsoZeroLocusOfSurj f.toRingHom hf rfl
  let g : PrimeSpectrum S → PrimeSpectrum P := fun x ↦ (e x).val
  have hg : StrictMono g := fun _ _ h ↦ e.strictMono h
  have hbound (c : LTSeries (PrimeSpectrum S)) : c.length ≤ n := by
    let a := c.map g hg
    have hb := (MvPolynomial.maximalChain_height_difference n a.last.asIdeal).1
    have hlen := Order.length_le_height_last (p := a)
    rw [← PrimeSpectrum.height_eq_orderHeight] at hlen
    exact_mod_cast hlen.trans hb
  have hdimbound : ringKrullDim S ≤ (n : WithBot ℕ∞) := by
    unfold ringKrullDim Order.krullDim
    exact iSup_le fun c ↦ by exact_mod_cast hbound c
  have : FiniteRingKrullDim S := finiteRingKrullDim_iff_ne_bot_and_top.mpr
    ⟨ne_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) ringKrullDim_nonneg_of_nontrivial),
      ne_of_lt (hdimbound.trans_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n)))⟩
  let c := LTSeries.longestOf (PrimeSpectrum S)
  have hc := longest_isMaxChain (α := PrimeSpectrum S)
  have equal_lengths (a : LTSeries (PrimeSpectrum S))
      (ha : IsMaxChain (fun x y : PrimeSpectrum S ↦ x ≤ y) (Set.range a)) :
      a.length = c.length := by
    have length_formula (b : LTSeries (PrimeSpectrum S))
        (hb : IsMaxChain (fun x y : PrimeSpectrum S ↦ x ≤ y) (Set.range b)) :
        (b.length : ℕ∞) = (n : ℕ∞) - (RingHom.ker f.toRingHom).height := by
      obtain ⟨hmin, hmax, hcov⟩ := maxChain_properties b hb
      have hhead : b.head = ⊥ := le_bot_iff.mp (hmin bot_le)
      let B := b.map g hg
      have hker : B.head.asIdeal = RingHom.ker f.toRingHom := by
        change Ideal.comap f.toRingHom b.head.asIdeal = _
        rw [hhead, PrimeSpectrum.asIdeal_bot]
        rfl
      have : b.last.asIdeal.IsMaximal := PrimeSpectrum.isMax_iff.mp hmax
      have : B.last.asIdeal.IsMaximal := by
        change (Ideal.comap f.toRingHom b.last.asIdeal).IsMaximal
        exact Ideal.comap_isMaximal_of_surjective f.toRingHom hf
      have hdim := MvPolynomial.ringKrullDim_localizationAtMaximal n B.last.asIdeal
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height B.last.asIdeal
        (Localization.AtPrime B.last.asIdeal)] at hdim
      have hheight : B.last.asIdeal.height = (n : ℕ∞) := WithBot.coe_injective hdim
      have hBcov : ∀ i : Fin B.length, B i.castSucc ⋖ B i.succ := by
        intro i
        refine ⟨B.step i, ?_⟩
        intro x hx hy
        have hxker : RingHom.ker f.toRingHom ≤ x.asIdeal :=
          (e (b i.castSucc)).property.trans hx.le
        let X : PrimeSpectrum.zeroLocus (R := P) (RingHom.ker f.toRingHom) := ⟨x, hxker⟩
        have hx' : b i.castSucc < e.symm X := by
          have h := e.symm.strictMono (show e (b i.castSucc) < X from hx)
          simpa only [e.symm_apply_apply] using h
        have hy' : e.symm X < b i.succ := by
          have h := e.symm.strictMono (show X < e (b i.succ) from hy)
          simpa only [e.symm_apply_apply] using h
        exact (hcov i).2 hx' hy'
      have hformula := (MvPolynomial.maximalChain_height_difference n B.last.asIdeal).2
        B.head.asIdeal (show B.head.asIdeal ≤ B.last.asIdeal from B.head_le_last)
        B rfl rfl hBcov
      have hlength : B.length = b.length := rfl
      rw [hheight, hker, hlength] at hformula
      exact hformula
    exact_mod_cast (length_formula a ha).trans (length_formula c hc).symm
  refine ⟨c.length, ?_, equal_lengths⟩
  exact Order.krullDim_eq_length_of_finiteDimensionalOrder
