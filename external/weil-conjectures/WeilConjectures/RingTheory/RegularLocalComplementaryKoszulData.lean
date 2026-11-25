/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import WeilConjectures.RingTheory.RegularLocalComplementaryTensorHomology
import WeilConjectures.RingTheory.RegularLocalComplementaryTensorAugmentation

/-! Auxiliary parameter and Koszul data for complementary regular quotients.
Source: Stacks Project, `intersection.tex`, Tag 0B1I.
(blueprint: new-d3-regular-local-complementary-koszul-data)
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace RingTheory

private theorem prefix_length_eq
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (r s : ℕ) (hdim : ringKrullDim A = ((r + s : ℕ) : WithBot ℕ∞))
    (I : Ideal A) (xs : List A) (c : ℕ) (hc : c ≤ r + s)
    (hparams : IsLocalRing.IsRegularSystemOfParameters xs)
    (hI : I = Ideal.ofList (xs.take c))
    [IsRegularLocalRing (A ⧸ I)]
    (hIdim : ringKrullDim (A ⧸ I) = (s : WithBot ℕ∞)) : c = r := by
  have hreg := IsRegularLocalRing.isRegular_and_quotients_of_generators
    A (r + s) hdim xs hparams
  have hq := (hreg.2.1 c hc).2
  rw [hI] at hIdim
  have hn : r + s - c = s := by
    exact_mod_cast hq.symm.trans hIdim
  omega

private theorem koszulBoundary_zero_formula_local
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (x : ⋀[A]^1 (Fin r →₀ A)) :
    exteriorPower.zeroEquiv A (Fin r →₀ A) (ExteriorAlgebra.koszulBoundary A r f 0 x) =
      Finsupp.linearCombination A f (exteriorPower.oneEquiv A (Fin r →₀ A) x) := by
  have he : (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
      (ExteriorAlgebra.koszulBoundary A r f 0) = (Finsupp.linearCombination A f).comp
        (exteriorPower.oneEquiv A (Fin r →₀ A)).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    have hg : ExteriorAlgebra.koszulBoundary A r f 0 (exteriorPower.ιMulti A 1 v) =
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm
          (Finsupp.linearCombination A f (v 0)) := by
      apply Subtype.ext
      simp [ExteriorAlgebra.koszulBoundary, exteriorPower.zeroEquiv_symm_apply,
        ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
        Algebra.algebraMap_eq_smul_one]
    simp [hg]
  exact LinearMap.congr_fun he x

private theorem exists_chain_quotient_augmentation
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f)
    (hf : Ideal.span (Set.range f) = I) :
    ∃ ε : ExteriorAlgebra.koszulComplex A r f ⟶
        (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ I)),
      QuasiIso ε ∧
      ∀ x : ⋀[A]^0 (Fin r →₀ A),
        ε.f 0 x = Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x) := by
  let K := ExteriorAlgebra.koszulComplex A r f
  let q : K.X 0 ⟶ ModuleCat.of A (A ⧸ I) :=
    ModuleCat.ofHom (I.mkQ.comp (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)
  have hq (x : K.X 0) : q x =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x) := rfl
  have hmem (v : Fin r →₀ A) : Finsupp.linearCombination A f v ∈ I := by
    rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ _
  have hz : K.d 1 0 ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change I.mkQ (exteriorPower.zeroEquiv A (Fin r →₀ A)
      (ExteriorAlgebra.koszulBoundary A r f 0 x)) = 0
    rw [koszulBoundary_zero_formula_local]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (hmem _)
  let ε₀ := (ChainComplex.toSingle₀Equiv K (ModuleCat.of A (A ⧸ I))).symm ⟨q, hz⟩
  have hε₀ : ε₀.f 0 = q := ChainComplex.toSingle₀Equiv_symm_apply_f_zero q hz
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨(exteriorPower.zeroEquiv A (Fin r →₀ A)).symm a, by simp [hq, ha]⟩
  have hex : (ShortComplex.mk (K.d 1 0) q hz).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hxI : exteriorPower.zeroEquiv A (Fin r →₀ A) x ∈ I :=
      (Submodule.Quotient.mk_eq_zero I).mp hx
    rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination] at hxI
    obtain ⟨v, hv⟩ := hxI
    refine ⟨(exteriorPower.oneEquiv A (Fin r →₀ A)).symm v, ?_⟩
    apply (exteriorPower.zeroEquiv A (Fin r →₀ A)).injective
    change exteriorPower.zeroEquiv A (Fin r →₀ A)
      (ExteriorAlgebra.koszulBoundary A r f 0 _) = _
    rw [koszulBoundary_zero_formula_local, LinearEquiv.apply_symm_apply, hv]
  have hqi : QuasiIso ε₀ := by
    constructor
    intro n
    by_cases hn : n = 0
    · subst n
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_isIso_descOpcycles _ (by simp) (by simp) (by simp)]
      let S := K.sc' 1 0 0
      have : Epi q := (ModuleCat.epi_iff_surjective q).mpr hsurj
      let ei := S.isoOpcyclesOfIsColimit hex.gIsCokernel
      have heq : S.descOpcycles
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat A)
            (ComplexShape.down ℕ) 1 0 0).map ε₀).τ₂
          (by change K.d 1 0 ≫ ε₀.f 0 = 0; rw [hε₀]; exact hz) = ei.inv := by
        apply (cancel_epi S.pOpcycles).mp
        simp only [ShortComplex.p_descOpcycles,
          ShortComplex.pOpcycles_π_isoOpcyclesOfIsColimit_inv, ei]
        exact hε₀
      rw [heq]
      infer_instance
    · rw [quasiIsoAt_iff_exactAt]
      · exact HomologicalComplex.exactAt_single_obj _ _ _ _ hn
      · exact (HomologicalComplex.exactAt_iff_isZero_homology K n).mpr (hreg n hn)
  refine ⟨ε₀, hqi, ?_⟩
  intro x
  exact hq x

/-- The parameter-selection and Koszul part of the transverse quotient argument.
The derived Tor and length calculation is isolated in
`regularLocal_complementary_tor_length_data`.
Source: Stacks Project, `intersection.tex`, Tag 0B1I.
(blueprint: new-d3-regular-local-complementary-koszul-data)

Proof:
1. `lem-weil-pbc-regular-local-quotient-kernel-parameters` applied to `A, I` gives a
   regular system of parameters `x₁,…,x_{r+s}` and `c ≤ r+s` with `I = (x₁,…,x_c)`.
   By `lem-weil-pbc-regular-local-generators-regular-sequence`,
   `dim A/(x₁,…,x_c) = r+s-c`; comparing with `dim A/I = s` gives `c = r`
   (`prefix_length_eq`). Put `f i = x_i` and `g` its first `r` entries. The same
   lemma makes the full list regular; its prefix `g` is regular, since its
   successive injectivities are among those of the full list and its quotient
   surjects onto the nonzero residue field.
2. In `B = A/J` the maximal ideal is `m/J`; since `I + J = m` it is generated by the
   images of `g`. As `B` is regular local of dimension `r`,
   `lem-weil-pbc-regular-local-generators-regular-sequence` makes these images a
   `B`-regular sequence (also for `r = 0`).
3. The terms `⋀^n (A^r)` of `def-weil-pbc-koszul-complex` are finite free by the
   exterior-power basis and zero for `n > r`. By
   `lem-weil-pbc-regular-sequence-koszul-regular` with `M = A`, positive homology
   vanishes; `K₀ = A` and `d₁(e_i) = g_i`, so `H₀ = A/I` and the quotient map
   `K₀ = A → A/I` is a quasi-isomorphism `ε` with the stated degree-zero formula.
4. On the `A`-module `B` the sequence `g` is regular: each successive quotient is
   `B/(ḡ₁,…,ḡ_{i-1})B` and `g_i` acts as `ḡ_i` (step 2). The module form of
   `lem-weil-pbc-regular-sequence-koszul-regular` kills positive homology of
   `K ⊗ B`; in degree zero `d₁ ⊗ B` has image `IB`, so `H₀ = B/IB = A/(I+J)` and
   `x ⊗ (a+J) ↦ x·a + (I+J)` is a quasi-isomorphism `δ`.
5. Since `I ⊔ J = m`, `A/(I ⊔ J)` is the residue field, and `e` is the identity of
   quotients `A/(I⊔J) = A/m`, sending `a + (I⊔J)` to `residue a`.
-/
theorem regularLocal_complementary_koszul_data
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (r s : ℕ) (hdim : ringKrullDim A = ((r + s : ℕ) : WithBot ℕ∞))
    (I J : Ideal A) (hI : I ≠ ⊤) (_hJ : J ≠ ⊤)
    [IsRegularLocalRing (A ⧸ I)] [IsRegularLocalRing (A ⧸ J)]
    (hIdim : ringKrullDim (A ⧸ I) = (s : WithBot ℕ∞))
    (hJdim : ringKrullDim (A ⧸ J) = (r : WithBot ℕ∞))
    (htrans : I ⊔ J = IsLocalRing.maximalIdeal A) :
    ∃ (f : Fin (r + s) → A) (g : Fin r → A),
      g = (fun i ↦ f (Fin.castAdd s i)) ∧
      IsLocalRing.IsRegularSystemOfParameters (List.ofFn f) ∧
      I = Ideal.span (Set.range g) ∧
      RingTheory.Sequence.IsRegular A (List.ofFn g) ∧
      RingTheory.Sequence.IsRegular (A ⧸ J)
        (List.ofFn (fun i ↦ Ideal.Quotient.mk J (g i))) ∧
      (∀ n : ℕ, Module.Free A ((ExteriorAlgebra.koszulComplex A r g).X n) ∧
        Module.Finite A ((ExteriorAlgebra.koszulComplex A r g).X n)) ∧
      (∀ n : ℕ, r < n → IsZero ((ExteriorAlgebra.koszulComplex A r g).X n)) ∧
      (∃ ε : ExteriorAlgebra.koszulComplex A r g ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ I)),
        QuasiIso ε ∧ ∀ x : ⋀[A]^0 (Fin r →₀ A),
          ε.f 0 x = Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) ∧
      (∀ n : ℕ, 0 < n →
        IsZero ((ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J)).homology n)) ∧
      (∃ δ : ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J) ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ (I ⊔ J))),
        QuasiIso δ ∧ ∀ (x : ⋀[A]^0 (Fin r →₀ A)) (a : A),
          δ.f 0 (x ⊗ₜ[A] Ideal.Quotient.mk J a) =
            Ideal.Quotient.mk (I ⊔ J)
              (exteriorPower.zeroEquiv A (Fin r →₀ A) x * a)) ∧
      (∃ e : ModuleCat.of A (A ⧸ (I ⊔ J)) ≅
          ModuleCat.of A (IsLocalRing.ResidueField A),
        ∀ a : A, e.hom (Ideal.Quotient.mk (I ⊔ J) a) = IsLocalRing.residue A a) := by
  classical
  obtain ⟨xs, c, hc, hparams, hIxs⟩ :=
    exists_parameters_regularLocalQuotient A (r + s) hdim I hI
  have hc' : c = r := prefix_length_eq A r s hdim I xs c hc hparams hIxs hIdim
  subst c
  have hlen : xs.length = r + s := by
    exact_mod_cast hparams.2.trans hdim
  let f : Fin (r + s) → A := fun i ↦ xs.get (Fin.cast hlen.symm i)
  let g : Fin r → A := fun i ↦ f (Fin.castAdd s i)
  have hfxs : List.ofFn f = xs := by
    apply List.ext_get
    · simp [hlen]
    · intro i hi1 hi2
      simp [List.getElem_ofFn, f]
  have htake : xs.take r = List.ofFn g := by
    rw [← hfxs]
    simp only [f, g]
    apply List.ext_get
    · simp
    · intro i hi1 hi2
      simp [List.getElem_ofFn, List.getElem_take]
  have hIspan : I = Ideal.span (Set.range g) := by
    rw [hIxs, htake]
    rw [Ideal.ofList]
    congr 1
    ext x
    simp
  have hregall := IsRegularLocalRing.isRegular_and_quotients_of_generators
    A (r + s) hdim xs hparams
  have hregA : RingTheory.Sequence.IsRegular A (List.ofFn g) := by
    have hparamsf : IsLocalRing.IsRegularSystemOfParameters (List.ofFn f) := by
      simpa [hfxs] using hparams
    apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (M := A) (fun x hx ↦ by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        apply hparamsf.1 ▸ Ideal.subset_span
        change g i ∈ List.ofFn f
        rw [List.mem_ofFn]
        exact ⟨Fin.castAdd s i, rfl⟩)).mpr
    constructor
    intro i hi
    have hir : i < r := by simpa using hi
    have hi' : i < xs.length := by
      rw [hlen]
      omega
    have hh := hregall.1.toIsWeaklyRegular.regular_mod_prev i hi'
    have htake_i : (List.ofFn g).take i = xs.take i := by
      rw [← htake, List.take_take]
      rw [Nat.min_eq_left (Nat.le_of_lt hir)]
    rw [htake_i]
    simpa [g, f, List.getElem_ofFn] using hh
  have hspanB : Ideal.span (Set.range (fun i : Fin r ↦ Ideal.Quotient.mk J (g i))) =
      IsLocalRing.maximalIdeal (A ⧸ J) := by
    let q : A →+* A ⧸ J := Ideal.Quotient.mk J
    calc
      Ideal.span (Set.range (fun i : Fin r ↦ q (g i))) =
          Ideal.map q (Ideal.span (Set.range g)) := by
        rw [Ideal.map_span]
        congr 1
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨g i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
      _ = Ideal.map q I := by rw [hIspan.symm]
      _ = Ideal.map q (I ⊔ J) := by
        rw [Ideal.map_sup]
        have hqJ : Ideal.map q J = (⊥ : Ideal (A ⧸ J)) := by
          apply le_antisymm
          · rw [Ideal.map_le_iff_le_comap]
            intro x hx
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
          · exact bot_le
        rw [hqJ, sup_bot_eq]
      _ = IsLocalRing.maximalIdeal (A ⧸ J) := by
        rw [htrans]
        exact IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
  have hparamsB : IsLocalRing.IsRegularSystemOfParameters
      (List.ofFn (fun i : Fin r ↦ Ideal.Quotient.mk J (g i))) := by
    refine ⟨?_, ?_⟩
    · have hset : {x | x ∈ List.ofFn (fun i : Fin r ↦ Ideal.Quotient.mk J (g i))} =
          Set.range (fun i : Fin r ↦ Ideal.Quotient.mk J (g i)) := by
          ext x
          simp
      rw [hset]
      exact hspanB
    · simpa [List.length_ofFn] using hJdim.symm
  have hregB : RingTheory.Sequence.IsRegular (A ⧸ J)
      (List.ofFn (fun i ↦ Ideal.Quotient.mk J (g i))) :=
    (IsRegularLocalRing.isRegular_and_quotients_of_generators
      (A ⧸ J) r hJdim _ hparamsB).1
  have hparamsf : IsLocalRing.IsRegularSystemOfParameters (List.ofFn f) := by
    simpa [hfxs] using hparams
  refine ⟨f, g, ?_, hparamsf, hIspan, hregA, hregB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro n
    change Module.Free A (⋀[A]^n (Fin r →₀ A)) ∧
      Module.Finite A (⋀[A]^n (Fin r →₀ A))
    exact ⟨inferInstance, inferInstance⟩
  · intro n hn
    let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A))
    letI : LinearOrder (Fin r) := inferInstance
    let B := b.exteriorPower n
    letI : IsEmpty (Set.powersetCard (Fin r) n) := ⟨fun S ↦ by
      have hc : (S : Finset (Fin r)).card ≤ r := by
        calc
          (S : Finset (Fin r)).card ≤ Fintype.card (Fin r) :=
            Finset.card_le_univ _
          _ = r := Fintype.card_fin r
      have hs : (S : Finset (Fin r)).card = n := S.prop
      omega⟩
    letI : Subsingleton (⋀[A]^n (Fin r →₀ A)) := ⟨fun x y ↦
      B.repr.injective (Subsingleton.elim _ _)⟩
    change IsZero (ModuleCat.of A (⋀[A]^n (Fin r →₀ A)))
    exact ModuleCat.isZero_of_subsingleton _
  · obtain ⟨ε, hε, hε0⟩ := exists_chain_quotient_augmentation A I r g
      hregA.isKoszulRegular hIspan.symm
    exact ⟨ε, hε, hε0⟩
  · exact regularLocal_complementary_tensor_homology_vanishing A r J g hregB
  · exact regularLocal_complementary_tensor_augmentation A r I J g hIspan
      (regularLocal_complementary_tensor_homology_vanishing A r J g hregB) htrans
  · let e : ModuleCat.of A (A ⧸ (I ⊔ J)) ≅
      ModuleCat.of A (IsLocalRing.ResidueField A) :=
      (Ideal.quotientEquivAlgOfEq A htrans).toLinearEquiv.toModuleIso
    refine ⟨e, ?_⟩
    intro a
    rfl

end RingTheory
