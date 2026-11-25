/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import WeilConjectures.FieldTheory.SeparablyGeneratedDifferentialsDimension

/-!
# Smoothness inputs of the Bertini argument

Infinitesimal facts about a smooth algebra `A` of finite type over an algebraically closed field
`k` used in the Bertini argument (blueprint `lemma-curve-preserving-finite-cover--1`): derivations
detect `m²` at maximal ideals, the transcendence degree is bounded by the rank of `Ω[A⁄k]`, and
minors of the first-order jet `derivationJet` of a linear system.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Algebra

section ClosedPoint

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Over an algebraically closed field, the residue field at a maximal ideal of a finite type
algebra is `k` itself. -/
noncomputable def residueFieldAlgEquiv (m : Ideal A) [m.IsMaximal] : k ≃ₐ[k] m.ResidueField :=
  have : Algebra.FiniteType k m.ResidueField :=
    FiniteType.of_surjective (IsScalarTower.toAlgHom k A _) m.algebraMap_residueField_surjective
  have : Module.Finite k m.ResidueField := finite_of_finite_type_of_isJacobsonRing k _
  AlgEquiv.ofBijective (Algebra.ofId k _) IsAlgClosed.algebraMap_bijective_of_isIntegral

lemma formallySmooth_residueField (m : Ideal A) [m.IsMaximal] :
    FormallySmooth k m.ResidueField :=
  FormallySmooth.of_equiv (residueFieldAlgEquiv m)

lemma kerCotangentToTensor_residueField_bijective [FormallySmooth k A] (m : Ideal A)
    [m.IsMaximal] :
    Function.Bijective (KaehlerDifferential.kerCotangentToTensor k A m.ResidueField) := by
  have := formallySmooth_residueField (k := k) m
  refine ⟨?_, fun x ↦ ?_⟩
  · rw [FormallySmooth.kerCotangentToTensor_injective_iff m.algebraMap_residueField_surjective]
    infer_instance
  · have : Subsingleton (KaehlerDifferential k m.ResidueField) :=
      KaehlerDifferential.subsingleton_of_surjective k _ (residueFieldAlgEquiv m).surjective
    exact (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k A _
      m.algebraMap_residueField_surjective x).mp (Subsingleton.elim _ _)

theorem exists_derivation_notMem_of_notMem_sq [FormallySmooth k A] (m : Ideal A) [m.IsMaximal]
    {g : A} (hg : g ∈ m) (hg2 : g ∉ m ^ 2) : ∃ D : Derivation k A A, D g ∉ m := by
  have hker : RingHom.ker (algebraMap A m.ResidueField) ^ 2 = m ^ 2 := by
    rw [Ideal.ker_algebraMap_residueField]
  have hgk : g ∈ RingHom.ker (algebraMap A m.ResidueField) :=
    RingHom.mem_ker.mpr (Ideal.algebraMap_residueField_eq_zero.mpr hg)
  have hne : (1 : m.ResidueField) ⊗ₜ[A] KaehlerDifferential.D k A g ≠ 0 := by
    rw [← KaehlerDifferential.kerCotangentToTensor_toCotangent k A _ ⟨g, hgk⟩, ne_eq,
      (kerCotangentToTensor_residueField_bijective m).1.eq_iff' (map_zero _),
      Ideal.toCotangent_eq_zero, hker]
    exact hg2
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero m.ResidueField hne
  let ψ : Ω[A⁄k] →ₗ[A] m.ResidueField :=
    (φ.restrictScalars A).comp (TensorProduct.mk A m.ResidueField Ω[A⁄k] 1)
  obtain ⟨ψ', hψ'⟩ := Module.projective_lifting_property (Algebra.linearMap A m.ResidueField) ψ
    m.algebraMap_residueField_surjective
  refine ⟨ψ'.compDer (KaehlerDifferential.D k A), fun h ↦ hφ ?_⟩
  have h' := Ideal.algebraMap_residueField_eq_zero.mpr h
  have := LinearMap.congr_fun hψ' (KaehlerDifferential.D k A g)
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply] at this
  replace h' : algebraMap A m.ResidueField (ψ' (KaehlerDifferential.D k A g)) = 0 := h'
  rw [h'] at this
  simpa [ψ] using this.symm

end ClosedPoint

end Algebra

namespace Algebra

section ClosedPoint2

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem exists_notMem_sq_independent [IsDomain A] [FormallySmooth k A] (m : Ideal A)
    [m.IsMaximal] :
    ∃ g : Fin (Module.finrank A Ω[A⁄k]) → A, (∀ l, g l ∈ m) ∧
      ∀ μ : Fin (Module.finrank A Ω[A⁄k]) → k, ∑ l, μ l • g l ∈ m ^ 2 → μ = 0 := by
  classical
  have hker : RingHom.ker (algebraMap A m.ResidueField) ^ 2 = m ^ 2 := by
    rw [Ideal.ker_algebraMap_residueField]
  let Φ := LinearEquiv.ofBijective _ (kerCotangentToTensor_residueField_bijective (k := k) m)
  have hrank : Module.finrank m.ResidueField (m.ResidueField ⊗[A] Ω[A⁄k]) =
      Module.finrank A Ω[A⁄k] :=
    m.finrank_fiber_eq_finrank
  let bκ := Module.finBasisOfFinrankEq m.ResidueField (m.ResidueField ⊗[A] Ω[A⁄k]) hrank
  choose g' hg' using fun l ↦ Ideal.toCotangent_surjective _ (Φ.symm (bκ l))
  have hg'm (l) : (g' l : A) ∈ m := Ideal.algebraMap_residueField_eq_zero.mp (g' l).2
  refine ⟨fun l ↦ (g' l : A), hg'm, fun μ hμ ↦ ?_⟩
  have h0 : ∑ l, algebraMap k A (μ l) • Φ.symm (bκ l) = 0 := by
    simp_rw [← hg', ← map_smul, ← map_sum, Ideal.toCotangent_eq_zero, hker]
    simpa [Algebra.smul_def] using hμ
  have h1 := congrArg Φ h0
  simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply, map_zero] at h1
  simp_rw [← algebraMap_smul m.ResidueField (algebraMap k A _),
    ← IsScalarTower.algebraMap_apply] at h1
  have := Fintype.linearIndependent_iff.mp bκ.linearIndependent _ h1
  funext l
  simpa using this l

variable (k A) in
theorem trdeg_le_finrank_kaehlerDifferential [IsDomain A] [FormallySmooth k A] :
    Algebra.trdeg k A ≤ Module.finrank A Ω[A⁄k] := by
  let K := FractionRing A
  have h1 : Algebra.trdeg k A ≤ Algebra.trdeg k K :=
    trdeg_le_of_injective (IsScalarTower.toAlgHom k A K) (IsFractionRing.injective A K)
  have : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have h2 : Module.finrank K Ω[K⁄k] = Module.finrank A Ω[A⁄k] := by
    rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A K).finrank_eq]
    exact (TensorProduct.isBaseChange A Ω[A⁄k] K).finrank_eq
  have hsep : Algebra.IsSeparableExtension k K := by
    intro F hF
    have : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
    obtain ⟨s, hs, hs'⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
    exact ⟨s, hs, hs'⟩
  obtain ⟨s, hs, hs'⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  let x : Fin s.card → K := fun i ↦ (s.equivFin.symm i : K)
  have hx : IsTranscendenceBasis k x := hs.comp_equiv s.equivFin.symm
  have hrange : Set.range x = (s : Set K) := by
    ext y
    simp only [Set.mem_range, Finset.mem_coe, x]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ (s.equivFin.symm i).2,
      fun hy ↦ ⟨s.equivFin ⟨y, hy⟩, by simp⟩⟩
  obtain ⟨-, -, h3⟩ :=
    KaehlerDifferential.exists_basis_differentials_of_separating_transcendenceBasis
    (IntermediateField.fg_top k K) hsep x hx (by rwa [hrange])
  rw [← h3, h2] at h1
  exact h1

end ClosedPoint2

end Algebra

theorem Matrix.exists_det_ne_zero_of_forall_sum_mul_eq_zero {K ι n : Type*} [Field K]
    [Fintype n] [DecidableEq n] (c : ι → n → K)
    (h : ∀ l : n → K, (∀ j, ∑ a, l a * c j a = 0) → l = 0) :
    ∃ J : n → ι, (Matrix.of fun a b ↦ c (J a) b).det ≠ 0 := by
  classical
  have hf_eq (f : Module.Dual K (n → K)) (x : n → K) :
      f x = ∑ a, f (fun j ↦ if a = j then 1 else 0) * x a := by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [mul_comm]
  have hspan : Submodule.span K (Set.range c) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have hl := h (fun a ↦ f (fun j ↦ if a = j then 1 else 0)) fun j ↦ by
      rw [← hf_eq]
      have := Submodule.mem_map_of_mem (f := f) (Submodule.subset_span (s := Set.range c) ⟨j, rfl⟩)
      rwa [hf, Submodule.mem_bot] at this
    refine hf0 (LinearMap.ext fun x ↦ ?_)
    rw [hf_eq, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun a _ ↦ by rw [congrFun hl a, Pi.zero_apply, zero_mul]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K c
  let b := Module.Basis.mk hli (by rw [hsp, hspan])
  have : Finite κ := Module.Finite.finite_basis b
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let e : n ≃ κ := (Fintype.equivOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent K (Matrix.of fun a' b' ↦ c ((a ∘ e) a') b').row :=
    hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp hli')).ne_zero

open Cardinal Matrix in
theorem Algebra.trdeg_add_card_le {k A D : Type u} [Field k] [CommRing A] [Algebra k A]
    [CommRing D] [IsDomain D] [Algebra k D] [Algebra A D] [IsScalarTower k A D]
    {M : ℕ} {n : Type*} [Fintype n] [DecidableEq n] (ξ : Fin M → D)
    (hgen : Algebra.adjoin A (Set.range ξ) = ⊤)
    (W : n → Fin M → A) (hW : ∀ a, ∑ i, algebraMap A D (W a i) * ξ i = 0)
    (I : n → Fin M) (hdet : algebraMap A D (Matrix.of fun a b ↦ W a (I b)).det ≠ 0) :
    Algebra.trdeg k D + Fintype.card n ≤
      Algebra.trdeg k (IsScalarTower.toAlgHom k A D).range + M := by
  classical
  set T := (IsScalarTower.toAlgHom k A D).range
  set N : Matrix n n A := Matrix.of fun a b ↦ W a (I b)
  have hI : Function.Injective I := by
    intro b b' hbb'
    by_contra hne
    exact hdet (by rw [Matrix.det_zero_of_column_eq hne fun a ↦ by simp [N, hbb'], map_zero])
  set U := Algebra.adjoin T (ξ '' (Set.range I)ᶜ)
  have hTU (a : A) : algebraMap A D a ∈ U :=
    Subalgebra.algebraMap_mem U (⟨algebraMap A D a, a, rfl⟩ : T)
  have hξU (i : Fin M) (hi : i ∉ Set.range I) : ξ i ∈ U := Algebra.subset_adjoin ⟨i, hi, rfl⟩
  have hcr (b : n) : algebraMap A D N.det * ξ (I b) ∈ U := by
    let r : n → D := fun a ↦ -∑ i ∈ (Finset.univ.image I)ᶜ, algebraMap A D (W a i) * ξ i
    have hr : ((algebraMap A D).mapMatrix N) *ᵥ (fun b ↦ ξ (I b)) = r := by
      funext a
      have := hW a
      rw [← Finset.sum_add_sum_compl (Finset.univ.image I),
        Finset.sum_image (fun x _ y _ h ↦ hI h)] at this
      simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, r, N,
        Matrix.of_apply]
      linear_combination this
    have := congrArg (fun v ↦ ((algebraMap A D).mapMatrix N).adjugate *ᵥ v) hr
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec] at this
    have hb := congrFun this b
    rw [Pi.smul_apply, smul_eq_mul, ← RingHom.map_det] at hb
    rw [hb, ← RingHom.map_adjugate]
    refine Subalgebra.sum_mem _ fun a _ ↦ mul_mem (hTU _) (neg_mem (Subalgebra.sum_mem _ ?_))
    intro i hi
    refine mul_mem (hTU _) (hξU i ?_)
    rintro ⟨b', rfl⟩
    simp at hi
  have halg : Algebra.IsAlgebraic U D := by
    have htop : Algebra.adjoin U (Set.range ξ) = ⊤ := by
      refine Algebra.eq_top_iff.mpr fun d ↦ ?_
      have hd : d ∈ Algebra.adjoin A (Set.range ξ) := hgen ▸ Algebra.mem_top
      induction hd using Algebra.adjoin_induction with
      | mem x hx => exact Algebra.subset_adjoin hx
      | algebraMap a => exact Subalgebra.algebraMap_mem _ (⟨_, hTU a⟩ : U)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
    have : (Algebra.adjoin U (Set.range ξ)).IsAlgebraic := by
      rw [Algebra.isAlgebraic_adjoin_iff]
      rintro _ ⟨i, rfl⟩
      by_cases hi : i ∈ Set.range I
      · obtain ⟨b, rfl⟩ := hi
        exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hdet)
          (isAlgebraic_algebraMap (⟨_, hTU _⟩ : U)) (isAlgebraic_algebraMap (⟨_, hcr b⟩ : U))
      · exact isAlgebraic_algebraMap (⟨_, hξU i hi⟩ : U)
    rw [htop] at this
    exact Algebra.isAlgebraic_iff.mpr this
  have h1 : Algebra.trdeg T D ≤ #(ξ '' (Set.range I)ᶜ) :=
    Algebra.IsAlgebraic.trdeg_le_cardinalMk T _
  have h2 : #(ξ '' (Set.range I)ᶜ) ≤ (M - Fintype.card n : ℕ) := by
    have := Cardinal.mk_image_le_lift (f := ξ) (s := (Set.range I)ᶜ)
    have hc : #((Set.range I)ᶜ : Set (Fin M)) = (M - Fintype.card n : ℕ) := by
      rw [Cardinal.mk_fintype, Fintype.card_compl_set, Fintype.card_fin,
        Set.card_range_of_injective hI]
    rwa [hc, Cardinal.lift_natCast, Cardinal.lift_uzero] at this
  have : FaithfulSMul k T := (faithfulSMul_iff_algebraMap_injective k T).mpr
    (algebraMap k T).injective
  have h3 := trdeg_add_eq k T (A := D)
  have hn : Fintype.card n ≤ M := by
    simpa using Fintype.card_le_of_injective I hI
  rw [← h3, add_assoc]
  gcongr
  calc Algebra.trdeg T D + Fintype.card n ≤ ((M - Fintype.card n : ℕ) : Cardinal) +
        Fintype.card n := by gcongr; exact h1.trans h2
    _ = M := by rw [← Nat.cast_add, Nat.sub_add_cancel hn]

theorem Derivation.apply_mem_of_mem_sq {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) {I : Ideal A} {x : A} (hx : x ∈ I ^ 2) : D x ∈ I := by
  rw [sq] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (I.mul_mem_right _ ha) (I.mul_mem_right _ hb)
  · rw [map_add]
    exact add_mem hy hz

theorem Ideal.exists_mem_notMem_sq {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {m : Ideal A} (hm : m ≠ ⊤) (hm0 : m ≠ ⊥) : ∃ g ∈ m, g ∉ m ^ 2 := by
  by_contra! h
  have hidem : IsIdempotentElem m :=
    le_antisymm Ideal.mul_le_left fun x hx ↦ by rw [← sq]; exact h x hx
  obtain ⟨e, he, rfl⟩ := (m.isIdempotentElem_iff_of_fg (IsNoetherian.noetherian m)).mp hidem
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with rfl | rfl
  · simp at hm0
  · simp at hm

theorem Ideal.exists_isMaximal_le_notMem {A : Type*} [CommRing A] [IsJacobsonRing A]
    (p : Ideal A) [p.IsPrime] (hp : ¬ p.IsMaximal) {S : Set (Ideal A)} (hS : S.Finite) :
    ∃ m, m.IsMaximal ∧ p ≤ m ∧ m ∉ S := by
  classical
  by_contra! h
  let F := hS.toFinset.filter fun m ↦ p ≤ m ∧ m.IsMaximal
  have hF : {J : Ideal A | p ≤ J ∧ J.IsMaximal} = ↑F := by
    ext J
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, F]
    exact ⟨fun hJ ↦ ⟨h J hJ.2 hJ.1, hJ⟩, fun hJ ↦ hJ.2⟩
  have hjac : p.jacobson = p := IsJacobsonRing.out' p (Ideal.IsPrime.isRadical inferInstance)
  have hle : F.inf id ≤ p := by
    rw [Finset.inf_id_eq_sInf, ← hF]
    exact hjac.le
  obtain ⟨m, hmF, hmp⟩ := (Ideal.IsPrime.inf_le' inferInstance).mp hle
  simp only [Finset.mem_filter, F] at hmF
  exact hp (le_antisymm hmF.2.1 hmp ▸ hmF.2.2)

namespace Algebra

theorem trdeg_quotient_eq_zero {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal] : Algebra.trdeg k (A ⧸ m) = 0 := by
  let := Ideal.Quotient.field m
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  exact trdeg_eq_zero

/-- The coefficients of `F = ∑ᵢ Xᵢ vᵢ` and of all its derivatives `D F = ∑ᵢ Xᵢ D(vᵢ)` along
`k`-derivations `D` of `A`: the first-order jet of the linear system spanned by the `vᵢ`.
The index `none` stands for `F` itself. -/
def derivationJet (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A] {M : ℕ}
    (v : Fin M → A) :
    Option (Derivation k A A) → Fin M → A :=
  fun j i ↦ j.elim (v i) fun D ↦ D (v i)

@[simp]
lemma derivationJet_none {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A] {M : ℕ}
    (v : Fin M → A)
    (i : Fin M) : derivationJet k v none i = v i := rfl

@[simp]
lemma derivationJet_some {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A] {M : ℕ}
    (v : Fin M → A)
    (D : Derivation k A A) (i : Fin M) : derivationJet k v (some D) i = D (v i) := rfl

end Algebra

namespace Algebra

section Minor

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

open Matrix in
theorem exists_det_derivationJet_notMem [IsDomain A] [FormallySmooth k A] {M : ℕ}
    (v : Fin M → A) (x : Ideal A) [x.IsMaximal]
    (hx : ∀ y : A, ∃ c : Fin M → k, y - ∑ i, c i • v i ∈ x ^ 2) :
    ∃ (I : Option (Fin (Module.finrank A Ω[A⁄k])) → Fin M)
      (J : Option (Fin (Module.finrank A Ω[A⁄k])) → Option (Derivation k A A)),
      (Matrix.of fun a b ↦ derivationJet k v (J a) (I b)).det ∉ x := by
  classical
  obtain ⟨g, hgx, hgind⟩ := exists_notMem_sq_independent (k := k) x
  choose c hc using hx
  let y : Option (Fin (Module.finrank A Ω[A⁄k])) → A := fun l ↦ l.elim 1 g
  let u : Option (Derivation k A A) → Option (Fin (Module.finrank A Ω[A⁄k])) →
      x.ResidueField :=
    fun j l ↦ algebraMap A _ (∑ i, c (y l) i • derivationJet k v j i)
  have key (lam : Option (Fin (Module.finrank A Ω[A⁄k])) → x.ResidueField)
      (hlam : ∀ j, ∑ l, lam l * u j l = 0) : lam = 0 := by
    let μ := fun l ↦ (residueFieldAlgEquiv (k := k) x).symm (lam l)
    have hμ (l) : lam l = algebraMap k _ (μ l) :=
      ((residueFieldAlgEquiv (k := k) x).apply_symm_apply (lam l)).symm
    let β : Fin M → k := fun i ↦ ∑ l, μ l * c (y l) i
    have hβ (j) : ∑ i, β i • derivationJet k v j i ∈ x := by
      rw [← Ideal.algebraMap_residueField_eq_zero]
      convert hlam j using 1
      simp only [u, hμ, β, map_sum, Finset.mul_sum, Finset.sum_mul,
        Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_assoc]
      exact Finset.sum_comm
    have hfY : ∑ i, β i • v i - ∑ l, μ l • y l ∈ x ^ 2 := by
      have : ∑ i, β i • v i - ∑ l, μ l • y l =
          ∑ l, μ l • (∑ i, c (y l) i • v i - y l) := by
        simp only [β, Finset.sum_smul, smul_sub, Finset.smul_sum, smul_smul,
          Finset.sum_sub_distrib]
        rw [Finset.sum_comm]
      rw [this]
      refine sum_mem fun l _ ↦ Submodule.smul_of_tower_mem _ _ ?_
      rw [← neg_sub]
      exact neg_mem (hc _)
    have hY : ∑ l, μ l • y l ∈ x := by
      have h1 : ∑ i, β i • v i ∈ x := hβ none
      have := sub_mem h1 (Ideal.pow_le_self two_ne_zero hfY)
      rwa [sub_sub_cancel] at this
    rw [Fintype.sum_option] at hY
    have hG : ∑ l, μ (some l) • g l ∈ x :=
      sum_mem fun l _ ↦ Submodule.smul_of_tower_mem _ _ (hgx l)
    have h0 : μ none = 0 := by
      have h1 : μ none • (1 : A) ∈ x := by simpa [y] using sub_mem hY hG
      by_contra hne
      rw [Algebra.smul_def, mul_one] at h1
      exact Ideal.IsMaximal.ne_top inferInstance
        (Ideal.eq_top_of_isUnit_mem _ h1 ((IsUnit.mk0 _ hne).map (algebraMap k A)))
    have hG2 : ∑ l, μ (some l) • g l ∈ x ^ 2 := by
      by_contra hG2
      obtain ⟨D, hD⟩ := exists_derivation_notMem_of_notMem_sq (k := k) x hG hG2
      have h1 : D (∑ i, β i • v i) ∈ x := by simpa [map_sum, D.map_smul] using hβ (some D)
      have hfG : ∑ i, β i • v i - ∑ l, μ (some l) • g l ∈ x ^ 2 := by
        simpa [Fintype.sum_option, h0, y] using hfY
      exact hD (by simpa using sub_mem h1 (D.apply_mem_of_mem_sq hfG))
    have hsome := hgind _ hG2
    funext l
    rw [hμ l]
    cases l with
    | none => simp [h0]
    | some l => simp [show μ (some l) = 0 from congrFun hsome l]
  obtain ⟨J, hJ⟩ := Matrix.exists_det_ne_zero_of_forall_sum_mul_eq_zero (fun j l ↦ u j l) key
  let Wt : Matrix (Option (Fin (Module.finrank A Ω[A⁄k]))) (Fin M) x.ResidueField :=
    Matrix.of fun a i ↦ algebraMap A _ (derivationJet k v (J a) i)
  let Bt : Matrix (Fin M) (Option (Fin (Module.finrank A Ω[A⁄k]))) x.ResidueField :=
    Matrix.of fun i l ↦ algebraMap k _ (c (y l) i)
  have hprod : (Matrix.of fun a l ↦ u (J a) l) = Wt * Bt := by
    ext a l
    simp only [Matrix.of_apply, Matrix.mul_apply, u, Wt, Bt, map_sum, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_comm]
  rw [hprod] at hJ
  obtain ⟨I, hI⟩ := Matrix.exists_det_ne_zero_of_forall_sum_mul_eq_zero (fun i a ↦ Wt a i)
    fun lam hlam ↦ by
      have h1 : lam ᵥ* Wt = 0 := funext fun i ↦ by simpa [Matrix.vecMul, dotProduct] using hlam i
      exact Matrix.eq_zero_of_vecMul_eq_zero hJ
        (by rw [← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul])
  refine ⟨I, J, fun hmem ↦ hI ?_⟩
  have h1 := Ideal.algebraMap_residueField_eq_zero.mpr hmem
  rw [RingHom.map_det, ← Matrix.det_transpose] at h1
  have hWt : (Matrix.of fun a b ↦ Wt b (I a)) = ((algebraMap A x.ResidueField).mapMatrix
      (Matrix.of fun a b ↦ derivationJet k v (J a) (I b)))ᵀ := by
    ext a b
    simp [Wt]
  rwa [hWt]

theorem exists_det_derivationJet_notMem_of_isPrime [IsDomain A] [FormallySmooth k A] {M : ℕ}
    (v : Fin M → A) (S : Set (Ideal A)) (hS : S.Finite)
    (hgen : ∀ m : Ideal A, m.IsMaximal → m ∉ S → ∀ x : A,
      ∃ c : Fin M → k, x - ∑ i, c i • v i ∈ m ^ 2)
    (hvS : ∀ m ∈ S, ∀ i, v i ∈ m)
    (hcot : ∀ m ∈ S, ∀ x ∈ m, ∃ c : Fin M → k, x - ∑ i, c i • v i ∈ m ^ 2) (hS0 : ⊥ ∉ S)
    (p : Ideal A) [p.IsPrime] :
    ∃ (n : Type) (_ : Fintype n) (_ : DecidableEq n) (I : n → Fin M)
      (J : n → Option (Derivation k A A)),
      (Matrix.of fun a b ↦ derivationJet k v (J a) (I b)).det ∉ p ∧
        Algebra.trdeg k (A ⧸ p) < Fintype.card n := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  by_cases hp : p.IsMaximal
  · obtain ⟨i, j, hij⟩ : ∃ i j, derivationJet k v j i ∉ p := by
      by_cases hpS : p ∈ S
      · obtain ⟨g, hg, hg2⟩ := Ideal.exists_mem_notMem_sq hp.ne_top fun h ↦ hS0 (h ▸ hpS)
        obtain ⟨c, hc⟩ := hcot p hpS g hg
        have hf : ∑ i, c i • v i ∈ p :=
          sum_mem fun i _ ↦ Submodule.smul_of_tower_mem _ _ (hvS p hpS i)
        have hf2 : ∑ i, c i • v i ∉ p ^ 2 := fun h ↦ hg2 (by simpa using add_mem hc h)
        obtain ⟨D, hD⟩ := exists_derivation_notMem_of_notMem_sq (k := k) p hf hf2
        by_contra! hall
        refine hD ?_
        rw [map_sum]
        refine sum_mem fun i _ ↦ ?_
        rw [D.map_smul]
        exact Submodule.smul_of_tower_mem _ _ (by simpa using hall i (some D))
      · obtain ⟨c, hc⟩ := hgen p hp hpS 1
        by_contra! hall
        have hf : ∑ i, c i • v i ∈ p :=
          sum_mem fun i _ ↦ Submodule.smul_of_tower_mem _ _ (by simpa using hall i none)
        exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr
          (by simpa using add_mem (Ideal.pow_le_self two_ne_zero hc) hf))
    refine ⟨Unit, inferInstance, inferInstance, fun _ ↦ i, fun _ ↦ j, ?_, ?_⟩
    · simpa [Matrix.det_unique] using hij
    · simp [trdeg_quotient_eq_zero p]
  · obtain ⟨x, hx, hpx, hxS⟩ := Ideal.exists_isMaximal_le_notMem p hp hS
    obtain ⟨I, J, hIJ⟩ := exists_det_derivationJet_notMem v x (hgen x hx hxS)
    refine ⟨_, inferInstance, inferInstance, I, J, fun h ↦ hIJ (hpx h), ?_⟩
    calc Algebra.trdeg k (A ⧸ p) ≤ Algebra.trdeg k A :=
          trdeg_le_of_surjective (Ideal.Quotient.mkₐ k p) (Ideal.Quotient.mkₐ_surjective k p)
      _ ≤ Module.finrank A Ω[A⁄k] := trdeg_le_finrank_kaehlerDifferential k A
      _ < _ := Nat.cast_lt.mpr (by simp)

end Minor

end Algebra
