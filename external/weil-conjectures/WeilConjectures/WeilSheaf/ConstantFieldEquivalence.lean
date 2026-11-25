/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantFieldDecomposition
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCyclic
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClopenDecomposition
public import WeilConjectures.WeilSheaf.ConstantFieldRestriction

/-!
# Weil sheaves over a smaller base field

Let `k₀ ⊆ k'` be finite fields with `[k' : k₀] = m + 1` and `V` a `k'`-scheme, regarded also as a
`k₀`-scheme. The geometric fibre `V̄₀ = V ⊗_{k₀} k̄` is the disjoint union of the open and closed
subschemes `jᵢ : V̄' ⟶ V̄₀`, `jᵢ = θ ≫ Frⁱ`, `i ≤ m`, the Frobenius translates of the component
`θ : V̄' = V ⊗_{k'} k̄' ⟶ V̄₀` (`WeilConjectures.AlgebraicGeometry.ConstantFieldDecomposition`).
The Frobenius pullback of `V̄₀` moves the `i`-th piece to the `(i+1)`-st one, and the last piece
to the first one up to the Frobenius pullback of `V̄'` relative to `k'`. Hence
(`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition`) taking the first piece is an
equivalence between pro-étale Weil sheaves on `V` relative to `k₀` and relative to `k'`
(`AlgebraicGeometry.ProEtaleWeilSheaf.constantFieldFunctor`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

noncomputable section

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  (l : ℕ) [Fact l.Prime] {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  {m : ℕ} (hm : Module.finrank k₀ k' = m + 1)

/-- The `i`-th piece `jᵢ = θ ≫ Frⁱ : V̄' ⟶ V̄₀`. -/
def pieceMap (i : Fin (m + 1)) : (V ↘ Spec (CommRingCat.of k')).geometricFiber ⟶
    (V ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  componentMap hc ≫ ((V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (i : ℕ)).asIso.hom

instance (i : Fin (m + 1)) : IsOpenImmersion (pieceMap hc i) :=
  have : Algebra.IsAlgebraic k₀ k' := Algebra.IsAlgebraic.of_finite k₀ k'
  have : Module.Finite k₀ k' := Module.Finite.of_finite
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

include hm in
lemma existsUnique_mem_range_pieceMap (x : (V ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    ∃! i : Fin (m + 1), x ∈ Set.range (pieceMap hc i).base := by
  have : Algebra.IsAlgebraic k₀ k' := Algebra.IsAlgebraic.of_finite k₀ k'
  obtain ⟨i, hi, hu⟩ := Scheme.Hom.existsUnique_mem_range_geometricFiberComponentMap_comp _ _ hc x
  refine ⟨Fin.cast hm i, hi, fun j hj ↦ ?_⟩
  have := hu (Fin.cast hm.symm j) hj
  subst this
  exact Fin.ext rfl

include hm in
lemma disjoint_range_pieceMap :
    Pairwise fun i j : Fin (m + 1) ↦
      Disjoint (Set.range (pieceMap hc i).base) (Set.range (pieceMap hc j).base) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hi hj
  exact hij ((existsUnique_mem_range_pieceMap hc hm x).unique hi hj)

include hm in
lemma isClosed_range_pieceMap (i : Fin (m + 1)) : IsClosed (Set.range (pieceMap hc i).base) := by
  have h : (Set.range (pieceMap hc i).base)ᶜ = ⋃ j ∈ ({i}ᶜ : Set (Fin (m + 1))),
      Set.range (pieceMap hc j).base := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    obtain ⟨j, hj, -⟩ := existsUnique_mem_range_pieceMap hc hm x
    refine ⟨fun hx ↦ ⟨j, fun h ↦ hx (h ▸ hj), hj⟩, fun ⟨k, hk, hx⟩ hx' ↦ ?_⟩
    exact hk ((existsUnique_mem_range_pieceMap hc hm x).unique hx hx')
  rw [← isOpen_compl_iff, h]
  exact isOpen_biUnion fun j _ ↦ (pieceMap hc j).isOpenEmbedding.isOpen_range

include hm in
lemma isClosedImmersion_pieceMap (i : Fin (m + 1)) : IsClosedImmersion (pieceMap hc i) :=
  IsClosedImmersion.of_isOpenImmersion _ (isClosed_range_pieceMap hc hm i)

lemma pieceMap_comp_frobenius (k : Fin m) :
    pieceMap hc k.castSucc ≫ (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom =
      pieceMap hc k.succ := by
  simp only [pieceMap, Category.assoc, Fin.val_castSucc, Fin.val_succ, pow_succ',
    Aut.mul_asIso, Iso.trans_hom]

include hm in
lemma pieceMap_last_comp_frobenius :
    pieceMap hc (Fin.last m) ≫ (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom =
      (V ↘ Spec (CommRingCat.of k')).geometricGaloisFrobenius.asIso.hom ≫
        pieceMap (m := m) hc 0 := by
  have hr : Nat.card k' = Nat.card k₀ ^ (m + 1) := by
    have : Module.Finite k₀ k' := Module.Finite.of_finite
    let := Fintype.ofFinite k₀
    let := Fintype.ofFinite k'
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k₀),
      hm]
  have h := geometricGaloisFrobenius_hom_comp_componentMap hc (m + 1) hr
  simp only [pow_succ', Aut.mul_asIso, Iso.trans_hom] at h
  simp only [pieceMap, Category.assoc, Fin.val_last, Fin.val_zero, pow_zero]
  rw [reassoc_of% h]
  exact (Category.comp_id _).symm

include hm in
/-- The decomposition of the pro-étale sheaves on `V̄₀` into the `m + 1` pieces `jᵢ^*`, permuted
cyclically by the Frobenius pullback. -/
abbrev cyclicDecomposition :
    IsoAlgebra.CyclicDecomposition (WeilSheaf.frobeniusPullback k₀ l V)
      (WeilSheaf.frobeniusPullback k' l V) m where
  J i := (pieceMap hc i)^*ᵃ[l]
  α k := Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l
      (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).symm _ ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l (pieceMap_comp_frobenius hc k)
  β := Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l
      (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).symm _ ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l (pieceMap_last_comp_frobenius hc hm) ≪≫
    adicUpperStarComp l _ _ ≪≫ Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l
      (V ↘ Spec (CommRingCat.of k')).geometricGaloisFrobenius.asIso)
  fullyFaithful :=
    have := isClosedImmersion_pieceMap hc hm
    adicUpperStarPiFullyFaithful l (pieceMap hc) (disjoint_range_pieceMap hc hm)
      fun x ↦ (existsUnique_mem_range_pieceMap hc hm x).exists
  essSurj :=
    have := isClosedImmersion_pieceMap hc hm
    adicUpperStarPi_essSurj l (pieceMap hc) (disjoint_range_pieceMap hc hm)

/-- **Pro-étale Weil sheaves relative to `k₀` and relative to `k'`**: the first piece
`(K, φ) ↦ (θ^* K, ψ)` of the cyclic decomposition. -/
def constantFieldFunctor : ProEtaleWeilSheaf k₀ l V ⥤ ProEtaleWeilSheaf k' l V :=
  (cyclicDecomposition l hc hm).functor

instance : (constantFieldFunctor l hc hm).IsEquivalence :=
  IsoAlgebra.CyclicDecomposition.functor_isEquivalence _

end ProEtaleWeilSheaf

end AlgebraicGeometry
