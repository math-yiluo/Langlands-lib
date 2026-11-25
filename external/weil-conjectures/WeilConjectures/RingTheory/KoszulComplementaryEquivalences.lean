/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulDualComplex
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Signed complementary Koszul equivalences

Source: Stacks Project, Tag 0BQZ, proof of lemma-regular-immersion-ext,
complementary contraction on the ordered top wedge.
(blueprint: lem-sc-koszul-complementary-equivalences).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- The coefficient of the ordered top wedge in the standard exterior-algebra basis.
Source: Stacks Project, Tag 0BQZ, complementary contraction calculation. -/
private noncomputable def koszulTopCoefficient (A : Type u) [CommRing A] (r : ℕ) :
    ExteriorAlgebra A (Fin r →₀ A) →ₗ[A] A :=
  (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).ExteriorAlgebra.coord
    Finset.univ

/-- Pair a complementary wedge with a degree-`j` wedge by taking the coefficient of
its product on the ordered top wedge. This is a concrete construction, independent
of the sequence and of any assertion of invertibility.
Source: Stacks Project, Tag 0BQZ, complementary contraction calculation. -/
private noncomputable def koszulComplementaryPairing (A : Type u) [CommRing A] (r j : ℕ)
    (_f : Fin r → A) :
    (⋀[A]^(r - j) (Fin r →₀ A)) →ₗ[A]
      (ModuleCat.of A (⋀[A]^j (Fin r →₀ A)) ⟶ ModuleCat.of A A) where
  toFun y := ModuleCat.ofHom
    { toFun := fun x ↦ koszulTopCoefficient A r
        ((x : ExteriorAlgebra A (Fin r →₀ A)) * (y : ExteriorAlgebra A (Fin r →₀ A)))
      map_add' := by intros; simp [add_mul]
      map_smul' := by intros; simp }
  map_add' := by
    intro y z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change koszulTopCoefficient A r (_ * (↑y + ↑z)) =
      koszulTopCoefficient A r (_ * ↑y) + koszulTopCoefficient A r (_ * ↑z)
    simp [mul_add]
  map_smul' := by
    intro a y
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change koszulTopCoefficient A r (_ * (a • ↑y)) =
      a • koszulTopCoefficient A r (_ * ↑y)
    simp

/-- The complementary top-wedge pairing is perfect in every degree up to `r`.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, complementary
contraction on the ordered top wedge.

Proof: Use the exterior-power bases of the standard basis of `A^r`. The pairing
of basis wedges indexed by `S` and `T` is zero unless `T` is the complement of
`S`: overlapping factors give zero, and disjoint sets of cardinalities `j` and
`r-j` have union all of `Fin r`. In the complementary case the coefficient is
the sign of the shuffle ordering `S` followed by its complement, hence is a
unit whose square is one. The pairing matrix is therefore an invertible signed
permutation matrix. Equivalently, send the coordinate functional at `S` to
that sign times the basis wedge of the complement. Basis expansion verifies
both inverse identities. For `r=0` the pairing is multiplication in `A`, and
for the zero ring the same inverse identities hold. No regularity is used. -/
private theorem koszulComplementaryPairing_bijective (A : Type u) [CommRing A] (r j : ℕ)
    (f : Fin r → A) (hj : j ≤ r) :
    Function.Bijective (koszulComplementaryPairing A r j f) := by
  classical
  let b : Module.Basis (Fin r) A (Fin r →₀ A) := Finsupp.basisSingleOne
  let c : Set.powersetCard (Fin r) (r - j) ≃ Set.powersetCard (Fin r) j :=
    Set.powersetCard.compl (by simp; omega)
  have hdisj (s : Set.powersetCard (Fin r) (r - j)) : Disjoint (c s).val s.val := by
    change Disjoint s.valᶜ s.val
    exact disjoint_compl_left
  let a (s : Set.powersetCard (Fin r) (r - j)) : Aˣ :=
    Units.map (Int.castRingHom A).toMonoidHom
      (Set.powersetCard.permOfDisjoint (hdisj s)).sign
  let bd := (b.exteriorPower j).dualBasis.map
    (ModuleCat.homLinearEquiv (S := A)
      (M := ModuleCat.of A (⋀[A]^j (Fin r →₀ A))) (N := ModuleCat.of A A)).symm
  let bs := (bd.reindex c.symm).unitsSMul a
  let e := (b.exteriorPower (r - j)).equiv bs (Equiv.refl _)
  have hb (s : Set.powersetCard (Fin r) (r - j)) :
      koszulComplementaryPairing A r j f (b.exteriorPower (r - j) s) =
        bs s := by
    apply ModuleCat.hom_ext
    apply (b.exteriorPower j).ext
    intro t
    change koszulTopCoefficient A r
      ((b.exteriorPower j t : ExteriorAlgebra A (Fin r →₀ A)) *
        (b.exteriorPower (r - j) s : ExteriorAlgebra A (Fin r →₀ A))) = _
    simp only [bs, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
      Equiv.symm_symm, bd, Module.Basis.map_apply, ModuleCat.hom_smul,
      LinearMap.smul_apply]
    change koszulTopCoefficient A r
      ((b.exteriorPower j t : ExteriorAlgebra A (Fin r →₀ A)) *
        (b.exteriorPower (r - j) s : ExteriorAlgebra A (Fin r →₀ A))) =
      (a s : A) • (b.exteriorPower j).dualBasis (c s) (b.exteriorPower j t)
    rw [Module.Basis.dualBasis_apply_self]
    rw [← basis_eq_coe_basis b t, ← basis_eq_coe_basis b s]
    by_cases h : t = c s
    · subst t
      rw [ite_eq_left rfl, smul_eq_mul, mul_one,
        basis_mul_of_disjoint b (c s) s (hdisj s)]
      have hu : (Set.powersetCard.disjUnion (hdisj s)).val = Finset.univ := by
        change (c s).val.disjUnion s.val (hdisj s) = Finset.univ
        rw [Finset.disjUnion_eq_union]
        change s.valᶜ ∪ s.val = Finset.univ
        exact compl_sup_eq_top
      rw [Units.smul_def, map_zsmul, hu]
      simp [koszulTopCoefficient, b, a]
    · have hnot : ¬Disjoint t.val s.val := by
        intro hdis
        have ht : t.val ⊆ s.valᶜ := by
          intro i hi
          exact Finset.mem_compl.mpr (fun his ↦ Finset.disjoint_left.mp hdis hi his)
        have heq : t.val = s.valᶜ := Finset.eq_of_subset_of_card_le ht (by
          rw [Finset.card_compl, Set.powersetCard.card_eq s,
            Set.powersetCard.card_eq t, Fintype.card_fin]
          omega)
        exact h (Subtype.ext heq)
      rw [ite_eq_right h, smul_zero, basis_mul_of_not_disjoint b t s hnot, map_zero]
  have he : (koszulComplementaryPairing A r j f) = e.toLinearMap := by
    apply (b.exteriorPower (r - j)).ext
    intro s
    rw [hb]
    change bs s = (b.exteriorPower (r - j)).equiv bs (Equiv.refl _) _
    simp only [Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [he]
  exact e.bijective

private theorem exterior_above_rank_zero
    (A : Type u) [CommRing A] (r n : ℕ) (hn : r < n)
    (x : ⋀[A]^n (Fin r →₀ A)) : x = 0 := by
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n
  have : IsEmpty (Set.powersetCard (Fin r) n) := ⟨fun s ↦ by
    have h := Finset.card_le_card (Finset.subset_univ s.val)
    rw [s.property, Finset.card_univ, Fintype.card_fin] at h
    omega⟩
  have : Subsingleton (⋀[A]^n (Fin r →₀ A)) := b.repr.injective.subsingleton
  exact Subsingleton.elim _ _

private theorem koszul_d_coe
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (a b : ℕ) (h : a = b + 1) (y : ⋀[A]^a (Fin r →₀ A)) :
    (show ⋀[A]^b (Fin r →₀ A) from (koszulComplex A r f).d a b y).val =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
        (Finsupp.linearCombination A f) ↑y := by
  subst a
  simp only [koszulComplex, ChainComplex.of_d]
  rfl

private theorem complementary_pairing_differential
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (j : ℕ) (hj : j < r) (y : (koszulComplex A r f).X (r - j)) :
    (koszulDualComplex A r f).d j (j + 1) (koszulComplementaryPairing A r j f y) =
      -koszulComplementaryPairing A r (j + 1) f
        ((koszulComplex A r f).d (r - j) (r - (j + 1)) y) := by
  obtain ⟨D, _, _, huniq, _, _, _, _, hleib, _⟩ :=
    koszul_differential A (Fin r →₀ A) (Finsupp.linearCombination A f)
  have hcontract : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A)))
      (Finsupp.linearCombination A f) = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro v z
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm A (Fin r →₀ A)))
          (Finsupp.linearCombination A f) v z
  simp only [koszulDualComplex, CochainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ⋀[A]^(j + 1) (Fin r →₀ A) at x
  change ⋀[A]^(r - j) (Fin r →₀ A) at y
  have hprod : (x : ExteriorAlgebra A (Fin r →₀ A)) *
      (y : ExteriorAlgebra A (Fin r →₀ A)) = 0 := by
    have hm : (x : ExteriorAlgebra A (Fin r →₀ A)) *
        (y : ExteriorAlgebra A (Fin r →₀ A)) ∈
        ⋀[A]^(j + 1 + (r - j)) (Fin r →₀ A) :=
      SetLike.mul_mem_graded x.property y.property
    have hz := exterior_above_rank_zero A r (j + 1 + (r - j)) (by omega) ⟨_, hm⟩
    exact congrArg Subtype.val hz
  have hl := hleib (j + 1) x (y : ExteriorAlgebra A (Fin r →₀ A))
  rw [hprod, map_zero] at hl
  have hc := congrArg (koszulTopCoefficient A r) hl
  simp only [map_zero, map_add, ← Algebra.smul_def, map_smul, smul_mul_assoc] at hc
  have hind : r - j = (r - (j + 1)) + 1 := by omega
  change ((koszulDualBoundary A r j f) (koszulComplementaryPairing A r j f y)).hom x = _
  simp only [koszulDualBoundary, LinearMap.smul_apply, ModuleCat.hom_smul,
    Linear.leftComp, LinearMap.coe_mk, AddHom.coe_mk,
    ModuleCat.hom_neg, LinearMap.neg_apply]
  simp only [koszulComplementaryPairing, ModuleCat.hom_ofHom, LinearMap.coe_mk,
    AddHom.coe_mk]
  simp only [koszulComplex, ChainComplex.of_d, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  have hdy : (show ⋀[A]^(r - (j + 1)) (Fin r →₀ A) from
      (koszulComplex A r f).d (r - j) (r - (j + 1)) y).val = D y := by
    exact (koszul_d_coe A r f _ _ hind y).trans (LinearMap.congr_fun hcontract ↑y)
  change (-1 : A) ^ (j + 1) • koszulTopCoefficient A r
      ((CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
        (Finsupp.linearCombination A f) ↑x) * ↑y) = _
  rw [hcontract]
  simp only [koszulComplex] at hdy
  -- The complex and exterior-power presentations carry definitionally equal instances.
  erw [hdy]
  have hs : ((-1 : A) ^ (j + 1)) * ((-1 : A) ^ (j + 1)) = 1 := by
    rw [← mul_pow]
    simp
  have hc' := congrArg (fun z : A ↦ (-1 : A) ^ (j + 1) • z) hc
  simpa only [smul_zero, smul_add, smul_smul, hs, one_smul, eq_neg_iff_add_eq_zero]
    using hc'.symm

/-- The signed complementary-wedge equivalences commute with the Koszul differentials.
No regularity is assumed.
Source: Stacks Project, Tag 0BQZ, proof of lemma-regular-immersion-ext, the map
sending a dual contraction monomial to its value on the ordered top wedge.
(blueprint: lem-sc-koszul-complementary-equivalences).

Proof: Let E = A^r with ordered basis e_i and top wedge w. For 0 <= j <= r,
let P_j(x,y) be the coefficient of w in x wedge y, with x in wedge^j E and
y in wedge^(r-j) E. The finite exterior-power bases show that P_j is perfect:
the dual of e_S maps to sign(S,S-complement) times e_(S-complement). Call
this isomorphism T'_j. Contraction d is a graded derivation. For x of degree
j+1 and y of degree r-j, x wedge y vanishes in degree r+1, so
P_j(d x,y) = (-1)^j P_(j+1)(x,d y). The signed dual differential is
delta_j(phi) = (-1)^(j+1) phi composed with d. Consequently
T'_(j+1) delta_j = -d T'_j. Set T_j = (-1)^j T'_j; then
T_(j+1) delta_j = d T_j. Multiplication by the unit (-1)^j preserves
invertibility. These T_j give e and the displayed differential identity,
with natural-number subtraction justified by j < r. When r = 0 the only
map is Hom_A(A,A) to A by evaluation at 1 and there are no differential
identities to check. Over the zero ring every term is zero and the same
basis construction and signs apply. -/
theorem exists_koszul_complementary_equivalences
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) :
    ∃ e : ∀ (j : ℕ), j ≤ r →
        (koszulDualComplex A r f).X j ≃ₗ[A] (koszulComplex A r f).X (r - j),
      ∀ (j : ℕ) (hj : j < r) (x : (koszulDualComplex A r f).X j),
        e (j + 1) (by omega) ((koszulDualComplex A r f).d j (j + 1) x) =
          (koszulComplex A r f).d (r - j) (r - (j + 1))
            (e j (Nat.le_of_lt hj) x) := by
  let t (j : ℕ) (hj : j ≤ r) :
      (koszulComplex A r f).X (r - j) ≃ₗ[A] (koszulDualComplex A r f).X j :=
    LinearEquiv.ofBijective (koszulComplementaryPairing A r j f)
      (koszulComplementaryPairing_bijective A r j f hj)
  let e (j : ℕ) (hj : j ≤ r) :
      (koszulDualComplex A r f).X j ≃ₗ[A] (koszulComplex A r f).X (r - j) :=
    (t j hj).symm.trans (LinearEquiv.smulOfUnit ((-1 : Aˣ) ^ j))
  have he (j : ℕ) (hj : j ≤ r) (x : (koszulDualComplex A r f).X j) :
      e j hj x = (-1 : A) ^ j • (t j hj).symm x := rfl
  refine ⟨e, ?_⟩
  intro j hj x
  let y := (t j (Nat.le_of_lt hj)).symm x
  have hxy : t j (Nat.le_of_lt hj) y = x := LinearEquiv.apply_symm_apply _ _
  have hd := complementary_pairing_differential A r f j hj y
  change (koszulDualComplex A r f).d j (j + 1) (t j (Nat.le_of_lt hj) y) =
    -t (j + 1) (by omega) ((koszulComplex A r f).d (r - j) (r - (j + 1)) y) at hd
  rw [hxy] at hd
  have ht : (t (j + 1) (by omega)).symm
      ((koszulDualComplex A r f).d j (j + 1) x) =
      -(koszulComplex A r f).d (r - j) (r - (j + 1)) y := by
    rw [hd, map_neg, LinearEquiv.symm_apply_apply]
  rw [he (j + 1) (by omega), he j (Nat.le_of_lt hj), ht]
  simp only [pow_succ, mul_neg_one, neg_smul, smul_neg, neg_neg]
  exact ((koszulComplex A r f).d (r - j) (r - (j + 1))).hom.map_smul _ _ |>.symm

end ExteriorAlgebra
