/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGalois
public import WeilConjectures.FieldTheory.TameLaurentSeries
public import WeilConjectures.RepresentationTheory.ProPGroupPadicMatrix

/-!

# `P'` is pro-`p`

Let `K` be separably closed of characteristic exponent `p`. The group `P'` of generic
automorphisms, viewed inside the absolute Galois group of `Frac K⟦t⟧` acting on
`Ω_K = (Frac K⟦t⟧)^alg` (`NearbyCyclesModel.GenericAut.toAlgEquiv`), fixes the tame roots of
`t`, hence is pro-`p`. As `Ω_K` is normal but not separable over `Frac K⟦t⟧`, we first transfer
the Galois-theoretic statements along restriction to the separable closure, which identifies
`Gal(Ω / F)` with `Gal(Ω^sep / F)` as topological groups for any normal `Ω / F`.

## Main statements

- `separableClosure.algEquivEquiv`, `separableClosure.continuous_algEquivEquiv_symm`: for
  `Ω / F` normal, restriction `Gal(Ω / F) ≃* Gal(Ω^sep / F)` is bijective with continuous
  inverse.
- `separableClosure.compactSpace_algEquiv`: `Gal(Ω / F)` is compact for `Ω / F` normal.
- `PowerSeries.tendsto_pow_ringExpChar_pow_of_normal`: the tame quotient for normal `Ω`.
- `NearbyCyclesModel.GenericAut.tendsto_toAlgEquiv_pow`,
  `NearbyCyclesModel.GenericAut.tendsto_pow_of_mem_range`: `σ ^ (p ^ k) → 1` on `P'`.
- `NearbyCyclesModel.GenericAut.exists_finiteIndex_forall_eq_one`: a continuous `ℓ`-adic
  representation of `P'`, `ℓ ≠ p`, is trivial on a finite index subgroup.
-/

@[expose] public section

universe u

open IntermediateField

namespace separableClosure

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- In an algebraic extension `Ω / F`, every `x` has a power `x ^ (q ^ n)` in the separable
closure of `F` in `Ω`; an automorphism of `Ω / F` fixing it fixes `x`. -/
lemma exists_mem_forall_apply_eq [Algebra.IsAlgebraic F Ω] (x : Ω) :
    ∃ y ∈ separableClosure F Ω, ∀ τ : Gal(Ω/F), τ y = y → τ x = x := by
  have : ExpChar (separableClosure F Ω) (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F _).injective _
  have : ExpChar Ω (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F Ω).injective _
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure F Ω) (ringExpChar F) x
  refine ⟨_, y.2, fun τ hτ ↦ iterateFrobenius_inj Ω (ringExpChar F) n ?_⟩
  rw [iterateFrobenius_def, iterateFrobenius_def, ← map_pow, ← hy]
  exact hτ

/-- An automorphism of `Ω / F` fixing an `F`-basis of a subextension `E` fixes `E`. -/
lemma _root_.IntermediateField.mem_fixingSubgroup_of_basis {ι : Type*}
    {E : IntermediateField F Ω}
    (b : Module.Basis ι F E) {τ : Gal(Ω/F)} (h : ∀ i, τ (b i) = b i) :
    τ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have := b.ext (f₁ := τ.toLinearMap.comp E.val.toLinearMap) (f₂ := E.val.toLinearMap) h
  exact LinearMap.congr_fun this ⟨x, hx⟩

variable (F Ω) in
/-- For `Ω / F` normal, restriction to the separable closure is injective on automorphisms. -/
lemma restrictNormalHom_injective [Normal F Ω] :
    Function.Injective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) (separableClosure F Ω)) := by
  refine (injective_iff_map_eq_one _).2 fun τ hτ ↦ AlgEquiv.ext fun x ↦ ?_
  obtain ⟨y, hy, h⟩ := exists_mem_forall_apply_eq (F := F) x
  refine h τ ?_
  have := AlgEquiv.restrictNormalHom_apply (separableClosure F Ω) τ ⟨y, hy⟩
  rw [hτ, AlgEquiv.one_apply] at this
  exact this.symm

variable (F Ω) in
/-- For `Ω / F` normal, `Gal(Ω / F)` is isomorphic to the Galois group of the separable closure
of `F` in `Ω`, by restriction. -/
noncomputable def algEquivEquiv [Normal F Ω] :
    Gal(Ω/F) ≃* Gal(separableClosure F Ω/F) :=
  MulEquiv.ofBijective (AlgEquiv.restrictNormalHom (separableClosure F Ω))
    ⟨restrictNormalHom_injective F Ω, AlgEquiv.restrictNormalHom_surjective Ω⟩

lemma algEquivEquiv_apply [Normal F Ω] (σ : Gal(Ω/F)) :
    algEquivEquiv F Ω σ = AlgEquiv.restrictNormalHom (separableClosure F Ω) σ := rfl

variable (F Ω) in
/-- For `Ω / F` normal, the inverse of the restriction to the separable closure is continuous
for the Krull topologies. -/
lemma continuous_algEquivEquiv_symm [Normal F Ω] :
    Continuous (algEquivEquiv F Ω).symm := by
  refine continuous_of_continuousAt_one (algEquivEquiv F Ω).symm.toMonoidHom
    (continuousAt_def.2 fun s hs ↦ ?_)
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, _, hE⟩ := hs
  let b := Module.finBasis F E
  choose y hy hfix using fun i ↦ exists_mem_forall_apply_eq (F := F) (b i : Ω)
  have hV : (⋂ i, ((F⟮(⟨y i, hy i⟩ : separableClosure F Ω)⟯).fixingSubgroup :
      Set Gal(separableClosure F Ω/F))) ∈ nhds 1 := by
    refine Filter.iInter_mem.2 fun i ↦ ?_
    have : FiniteDimensional F F⟮(⟨y i, hy i⟩ : separableClosure F Ω)⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    exact (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  refine Filter.mem_of_superset hV fun g hg ↦ hE ?_
  obtain ⟨τ, rfl⟩ := (algEquivEquiv F Ω).surjective g
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  refine IntermediateField.mem_fixingSubgroup_of_basis b fun i ↦ hfix i τ ?_
  have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Set.mem_iInter.1 hg i) _
    (IntermediateField.mem_adjoin_simple_self F _)
  rw [algEquivEquiv_apply] at this
  rw [← AlgEquiv.restrictNormalHom_apply (separableClosure F Ω) τ ⟨y i, hy i⟩]
  exact congrArg Subtype.val this

/-- For `Ω / F` normal (not necessarily separable), the Galois group `Gal(Ω / F)` is compact
for the Krull topology: it is the continuous image of the Galois group of the separable closure
of `F` in `Ω`. -/
instance compactSpace_algEquiv [Normal F Ω] : CompactSpace Gal(Ω/F) :=
  (algEquivEquiv F Ω).symm.surjective.compactSpace (continuous_algEquivEquiv_symm F Ω)

end separableClosure

namespace PowerSeries

open scoped PowerSeries

variable {K : Type u} [Field K] {F : Type u} [Field F] [Algebra K⟦X⟧ F]
  [IsFractionRing K⟦X⟧ F]

/-- **The tame quotient, normal version.** Let `K` be separably closed of characteristic
exponent `q`, `F` the fraction field of `K⟦X⟧` and `Ω / F` a normal extension (e.g. an
algebraic closure). An automorphism `σ` of `Ω / F` fixing every `n`-th root of `X` in `Ω`, for
`n` invertible in `K`, satisfies `σ ^ (q ^ k) → 1` in the Krull topology. This reduces to the
Galois case (`PowerSeries.tendsto_pow_ringExpChar_pow`) on the separable closure of `F` in
`Ω`, whose Galois group is homeomorphic to `Gal(Ω / F)`. -/
theorem tendsto_pow_ringExpChar_pow_of_normal [IsSepClosed K] {Ω : Type u} [Field Ω]
    [Algebra F Ω] [Algebra K⟦X⟧ Ω] [IsScalarTower K⟦X⟧ F Ω] [Normal F Ω]
    (σ : Gal(Ω/F))
    (hσ : ∀ (n : ℕ) (z : Ω), (n : K) ≠ 0 →
      z ^ n = algebraMap K⟦X⟧ Ω PowerSeries.X → σ z = z) :
    Filter.Tendsto (fun k : ℕ ↦ σ ^ ringExpChar K ^ k) Filter.atTop (nhds 1) := by
  let e := separableClosure.algEquivEquiv F Ω
  have h := tendsto_pow_ringExpChar_pow (K := K) (e σ) fun n z hn hz ↦ Subtype.ext (by
    rw [separableClosure.algEquivEquiv_apply, AlgEquiv.restrictNormalHom_apply]
    refine hσ n z hn ?_
    rw [← IntermediateField.coe_pow, hz]
    rfl)
  have h' := ((separableClosure.continuous_algEquivEquiv_symm F Ω).tendsto 1).comp h
  rw [map_one] at h'
  refine h'.congr fun k ↦ ?_
  rw [Function.comp_apply, ← map_pow, MulEquiv.symm_apply_apply]

end PowerSeries

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- **`P'` is pro-`p`**: for `K` separably closed of characteristic exponent `p`, every generic
automorphism `σ` satisfies `σ ^ (p ^ k) → 1` in the Krull topology of the absolute Galois group
of `Frac K⟦t⟧`, as it fixes the tame roots of `t` (`toRingAut_eq_of_pow_eq_X`). -/
theorem tendsto_toAlgEquiv_pow [IsSepClosed K] (σ : GenericAut k' K) :
    Filter.Tendsto (fun k : ℕ ↦ toAlgEquiv σ ^ ringExpChar K ^ k) Filter.atTop (nhds 1) := by
  refine PowerSeries.tendsto_pow_ringExpChar_pow_of_normal (toAlgEquiv σ) fun n z hn hz ↦ ?_
  have hn' : (n : traitGenericField K) ≠ 0 := by
    rw [← map_natCast ((algebraMap (PowerSeries K) (traitGenericField K)).comp
      (PowerSeries.C (R := K)))]
    exact (map_ne_zero _).2 hn
  exact toRingAut_eq_of_pow_eq_X σ (Nat.pos_of_ne_zero fun h ↦ hn (by simp [h])) hn' hz

/-- **`P'` is pro-`p`**, in the subspace topology: every element `σ` of the range of
`toAlgEquiv` satisfies `σ ^ (p ^ k) → 1`. -/
theorem tendsto_pow_of_mem_range [IsSepClosed K] (σ : (toAlgEquiv (k' := k') (K := K)).range) :
    Filter.Tendsto (fun k : ℕ ↦ σ ^ ringExpChar K ^ k) Filter.atTop (nhds 1) := by
  obtain ⟨_, τ, rfl⟩ := σ
  rw [tendsto_subtype_rng]
  simpa using tendsto_toAlgEquiv_pow τ

/-- **`ℓ`-adic representations of `P'` are finite**: for `K` separably closed of characteristic
`p > 0` and `ℓ ≠ p`, a continuous homomorphism `ρ` from `P'` (the range of `toAlgEquiv`, with
the Krull topology) to `GL_n(ℤ_ℓ)` is trivial on a finite index subgroup. Indeed it is trivial
on an open subgroup (`exists_isOpen_forall_eq_one_of_tendsto_pow_prime_pow`), which has finite
index since `P'` is closed in the compact absolute Galois group of `Frac K⟦t⟧`. -/
theorem exists_finiteIndex_forall_eq_one [IsSepClosed K] [Fact (ringChar K).Prime] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : ringChar K ≠ ℓ) {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : (toAlgEquiv (k' := k') (K := K)).range →* (Matrix n n ℤ_[ℓ])ˣ)
    (hρ : Continuous fun g ↦ (ρ g : Matrix n n ℤ_[ℓ])) :
    ∃ U : Subgroup (toAlgEquiv (k' := k') (K := K)).range,
      U.FiniteIndex ∧ ∀ g ∈ U, ρ g = 1 := by
  have hp : ringExpChar K = ringChar K :=
    Nat.max_eq_left (Fact.out : (ringChar K).Prime).one_lt.le
  obtain ⟨U, hU, hρU⟩ := exists_isOpen_forall_eq_one_of_tendsto_pow_prime_pow Fact.out hℓ
    (fun σ ↦ hp ▸ tendsto_pow_of_mem_range σ) ρ hρ
  have : CompactSpace (toAlgEquiv (k' := k') (K := K)).range :=
    isCompact_iff_compactSpace.1 isClosed_range_toAlgEquiv.isCompact
  have := U.quotient_finite_of_isOpen hU
  exact ⟨U, Subgroup.finiteIndex_of_finite_quotient, hρU⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut
