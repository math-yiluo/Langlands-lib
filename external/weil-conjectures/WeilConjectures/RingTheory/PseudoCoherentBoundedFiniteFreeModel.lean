/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.FiniteFreeSplitTopCancellation
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Finite free models at a cohomological upper bound

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U
(blueprint: lem-pc-pseudo-coherent-bounded-finite-free-model).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A pseudo-coherent object of `D(R)` with no cohomology above `b` admits a finite free
representative with no terms above `b`.
Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U, final assertion
(blueprint: lem-pc-pseudo-coherent-bounded-finite-free-model).

Proof:
1. Unpack pseudo-coherence to obtain a finite free representative `E` supported in
   degrees at most some integer `n`. Induct on the nonnegative excess of `n` over `b`.
2. At each successor step, transfer the vanishing of cohomology from `C` to the current
   representative. Its differential into the top degree is an epimorphism: the complex
   is exact there and the outgoing differential has zero target. Freeness of the top
   term gives a section of this epimorphism.
3. Apply `CochainComplex.exists_finiteFree_cancel_split_top`. It truncates at the preceding
   degree and adds a contractible two-term complex to restore freeness of the new top
   term. The projection and truncation inclusion form a quasi-isomorphism. Compose its
   image under `Q` with the current derived isomorphism, and use the induction hypothesis.
   At excess zero, the current representative already has the desired bound. -/
theorem exists_finiteFree_model_isStrictlyLE
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : DerivedCategory (ModuleCat.{v} R)) (b : ℤ) (hC : IsPseudoCoherent C)
    (hvan : ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj C)) :
    ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      Nonempty (Q.obj P ≅ C) := by
  classical
  have descend (k : ℕ) :
      ∀ (E : CochainComplex (ModuleCat.{v} R) ℤ), E.IsStrictlyLE (b + k) →
        (∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) →
        Nonempty (Q.obj E ≅ C) →
        ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
          P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
          Nonempty (Q.obj P ≅ C) := by
    induction k with
    | zero =>
        intro E hbound hfree e
        exact ⟨E, by simpa using hbound, hfree, e⟩
    | succ k ih =>
        intro E hbound hfree ⟨e⟩
        let n : ℤ := b + (k + 1 : ℕ)
        have hn : b < n := by dsimp [n]; omega
        have : E.IsStrictlyLE n := hbound
        have hzero : IsZero (E.homology n) :=
          (hvan n hn).of_iso
            ((homologyFunctorFactors (ModuleCat.{v} R) n).symm.app E ≪≫
              (homologyFunctor (ModuleCat.{v} R) n).mapIso e)
        have hexact : E.ExactAt n :=
          (HomologicalComplex.exactAt_iff_isZero_homology E n).2 hzero
        have hnext : E.d n (n + 1) = 0 :=
          (E.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _
        have hprev : (ComplexShape.up ℤ).prev n = n - 1 :=
          ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel (n - 1) n by
            change n - 1 + 1 = n
            omega)
        have hnextIndex : (ComplexShape.up ℤ).next n = n + 1 :=
          ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)
        have hepi : Epi (E.d (n - 1) n) := by
          have hg : (E.sc n).g = 0 := by
            change E.d n ((ComplexShape.up ℤ).next n) = 0
            rw [hnextIndex]
            exact hnext
          have hf := ((E.sc n).exact_iff_epi hg).1 hexact
          change Epi (E.d ((ComplexShape.up ℤ).prev n) n) at hf
          rwa [hprev] at hf
        have : Module.Free R (E.X n) := (hfree n).1
        let s : E.X n ⟶ E.X (n - 1) :=
          Projective.factorThru (𝟙 (E.X n)) (E.d (n - 1) n)
        have hs : s ≫ E.d (n - 1) n = 𝟙 (E.X n) :=
          Projective.factorThru_comp _ _
        obtain ⟨L, π, hLbound, hLfree, hπ⟩ :=
          CochainComplex.exists_finiteFree_cancel_split_top E n hbound hfree s hs
        have : QuasiIso π := hπ
        have hindex : n - 1 = b + (k : ℤ) := by dsimp [n]; omega
        rw [hindex] at hLbound
        exact ih L hLbound hLfree ⟨asIso (Q.map π) ≪≫ e⟩
  obtain ⟨E, n, hbound, hfree, e⟩ := hC
  have : E.IsStrictlyLE n := hbound
  exact descend (n - b).toNat E
    (E.isStrictlyLE_of_le n (b + ((n - b).toNat : ℤ)) (by omega)) hfree e

end DerivedCategory
