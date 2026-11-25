/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!

# Generic automorphisms as field automorphisms

A generic automorphism `τ` of `Spec Ω_K` (`NearbyCyclesModel.GenericAut`) is `Spec` of a ring
automorphism of `Ω_K`. This gives an injective group homomorphism from the group of generic
automorphisms to the ring automorphisms of `Ω_K`
(`NearbyCyclesModel.GenericAut.toRingAut`), through which the group inherits the Krull topology
of the Galois group `Gal(Ω_K / Frac K⟦t⟧ · Ω)`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- The ring automorphism of `Ω_K` underlying a generic automorphism. -/
noncomputable def toRingEquiv (σ : GenericAut k' K) :
    traitGenericField K ≃+* traitGenericField K where
  toFun := (Spec.preimage σ.τ).hom
  invFun := (Spec.preimage (inv σ.τ)).hom
  left_inv x := by
    rw [← CommRingCat.comp_apply, ← Spec.preimage_comp, IsIso.inv_hom_id, Spec.preimage_id]
    rfl
  right_inv x := by
    rw [← CommRingCat.comp_apply, ← Spec.preimage_comp, IsIso.hom_inv_id, Spec.preimage_id]
    rfl
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
lemma toRingEquiv_apply (σ : GenericAut k' K) (x : traitGenericField K) :
    toRingEquiv σ x = (Spec.preimage σ.τ).hom x :=
  rfl

/-- Generic automorphisms act on `Ω_K` by ring automorphisms: a group homomorphism. -/
noncomputable def toRingAut : GenericAut k' K →* RingAut (traitGenericField K) where
  toFun := toRingEquiv
  map_one' := by
    ext x
    rw [toRingEquiv_apply, one_τ, Spec.preimage_id, CommRingCat.id_apply, RingAut.one_apply]
  map_mul' σ τ := by
    ext x
    rw [toRingEquiv_apply, mul_τ, Spec.preimage_comp, CommRingCat.comp_apply, RingAut.mul_apply,
      toRingEquiv_apply, toRingEquiv_apply]

/-- Generic automorphisms are determined by their action on `Ω_K`. -/
lemma toRingAut_injective : Function.Injective (toRingAut (k' := k') (K := K)) := by
  intro σ τ h
  refine ext ?_
  rw [← Spec.map_preimage σ.τ, ← Spec.map_preimage τ.τ]
  congr 1
  ext x
  exact RingEquiv.congr_fun h x

/-- A generic automorphism fixes the image of `K⟦t⟧` in `Ω_K`. -/
lemma toRingAut_algebraMap (σ : GenericAut k' K) (a : PowerSeries K) :
    toRingAut σ (algebraMap (PowerSeries K) (traitGenericField K) a) =
      algebraMap (PowerSeries K) (traitGenericField K) a := by
  have h := congrArg Spec.preimage σ.over_trait
  rw [traitGenericPoint, Spec.preimage_comp, Spec.preimage_map] at h
  exact congrArg (fun f ↦ f.hom a) h

/-- A generic automorphism fixes the image of `Ω` in `Ω_K`. -/
lemma toRingAut_traitGenericFieldMap (σ : GenericAut k' K) (y : traitGenericField k') :
    toRingAut σ (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y := by
  have h := congrArg Spec.preimage σ.over_base
  rw [traitGenericPointMap, Spec.preimage_comp, Spec.preimage_map] at h
  exact congrArg (fun f ↦ f.hom y) h

/-- A generic automorphism fixes the field of fractions `Frac K⟦t⟧` inside `Ω_K`. -/
lemma toRingAut_algebraMap_fractionRing (σ : GenericAut k' K)
    (a : FractionRing (PowerSeries K)) :
    toRingAut σ (algebraMap (FractionRing (PowerSeries K)) (traitGenericField K) a) =
      algebraMap (FractionRing (PowerSeries K)) (traitGenericField K) a :=
  DFunLike.congr_fun
    (IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries K))
      (j := ((toRingAut σ : traitGenericField K ≃+* _) : traitGenericField K →+* _).comp
        (algebraMap (FractionRing (PowerSeries K)) (traitGenericField K)))
      (k := algebraMap (FractionRing (PowerSeries K)) (traitGenericField K)) (by
        ext b
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        rw [← IsScalarTower.algebraMap_apply, toRingAut_algebraMap])) a

/-- A generic automorphism as an automorphism of `Ω_K` over `Frac K⟦t⟧`, an element of the
absolute Galois group of `Frac K⟦t⟧` (with its Krull topology). -/
noncomputable def toAlgEquiv : GenericAut k' K →*
    (traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := toRingAut σ) (toRingAut_algebraMap_fractionRing σ)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Generic automorphisms are determined by their action on `Ω_K`. -/
lemma toAlgEquiv_injective : Function.Injective (toAlgEquiv (k' := k') (K := K)) :=
  fun _ _ h ↦ toRingAut_injective (RingEquiv.ext fun x ↦ AlgEquiv.congr_fun h x)

/-- An automorphism of `Ω_K` over `Frac K⟦t⟧` fixing the image of `Ω` is a generic
automorphism. -/
noncomputable def ofAlgEquiv
    (e : traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K)
    (he : ∀ y, e (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y) :
    GenericAut k' K where
  τ := Spec.map (CommRingCat.ofHom (e : traitGenericField K →+* traitGenericField K))
  isIso := by
    have : IsIso (CommRingCat.ofHom (e : traitGenericField K →+* traitGenericField K)) :=
      ⟨CommRingCat.ofHom (e.symm : traitGenericField K →+* traitGenericField K),
        by ext; simp, by ext; simp⟩
    infer_instance
  over_trait := by
    rw [traitGenericPoint, ← Spec.map_comp]
    congr 1
    ext a
    rw [CommRingCat.comp_apply, CommRingCat.ofHom_apply, CommRingCat.ofHom_apply, RingHom.coe_coe,
      IsScalarTower.algebraMap_apply (PowerSeries K) (FractionRing (PowerSeries K)),
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  over_base := by
    rw [traitGenericPointMap, ← Spec.map_comp]
    congr 1
    ext y
    exact he y

lemma toAlgEquiv_ofAlgEquiv
    (e : traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K)
    (he : ∀ y, e (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y) :
    toAlgEquiv (ofAlgEquiv e he) = e := by
  refine AlgEquiv.ext fun x ↦ ?_
  have h : Spec.preimage (ofAlgEquiv e he).τ =
      CommRingCat.ofHom (e : traitGenericField K →+* traitGenericField K) :=
    Spec.preimage_map _
  exact congrArg (fun f ↦ f.hom x) h

/-- **The generic automorphisms are the Galois group `P' = Gal(Ω_K / Frac K⟦t⟧ · Ω)`**: the
range of `toAlgEquiv` is the subgroup of the absolute Galois group of `Frac K⟦t⟧` fixing the
image of `Ω`. -/
lemma mem_range_toAlgEquiv_iff
    (e : traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K) :
    e ∈ (toAlgEquiv (k' := k') (K := K)).range ↔
      ∀ y, e (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y := by
  refine ⟨?_, fun he ↦ ⟨ofAlgEquiv e he, toAlgEquiv_ofAlgEquiv e he⟩⟩
  rintro ⟨σ, rfl⟩ y
  exact toRingAut_traitGenericFieldMap σ y

/-- **Generic automorphisms fix the tame roots of the uniformizer**: every `n`-th root of `t` in
`Ω_K`, with `n` invertible in `Ω_K`, is fixed by every generic automorphism. These roots come
from `Ω` up to `n`-th roots of unity, which also come from `Ω`; so the generic automorphisms
act trivially on the tame extensions `K((t^{1/n}))` of `K((t))`, and `P'` lies in the wild
inertia. -/
lemma toRingAut_eq_of_pow_eq_X (σ : GenericAut k' K) {n : ℕ} (hn : 0 < n)
    (hn' : (n : traitGenericField K) ≠ 0) {z : traitGenericField K}
    (hz : z ^ n = algebraMap (PowerSeries K) (traitGenericField K) PowerSeries.X) :
    toRingAut σ z = z := by
  let φ := traitGenericFieldMap k' K
  have hφ : Function.Injective φ := φ.injective
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (PowerSeries k') (traitGenericField k') PowerSeries.X) hn
  have hz₀ : φ w ^ n = algebraMap (PowerSeries K) (traitGenericField K) PowerSeries.X := by
    rw [← map_pow, hw]
    have := congrArg (fun f ↦ f PowerSeries.X) (traitGenericFieldMap_comp_algebraMap k' K)
    simpa using this
  have hX : algebraMap (PowerSeries K) (traitGenericField K) PowerSeries.X ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap (PowerSeries K) (traitGenericField K)) := by
      rw [IsScalarTower.algebraMap_eq (PowerSeries K) (FractionRing (PowerSeries K))
        (traitGenericField K), RingHom.coe_comp]
      exact (algebraMap (FractionRing (PowerSeries K)) (traitGenericField K)).injective.comp
        (IsFractionRing.injective _ _)
    exact PowerSeries.X_ne_zero (hinj (h.trans (map_zero _).symm))
  have hw0 : φ w ≠ 0 := fun h ↦ hX (by rw [← hz₀, h, zero_pow hn.ne'])
  have hn'' : (n : traitGenericField k') ≠ 0 := fun h ↦ hn' (by rw [← map_natCast φ, h, map_zero])
  have : NeZero (n : traitGenericField k') := ⟨hn''⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (traitGenericField k') n
  have hξ' : IsPrimitiveRoot (φ ξ) n := hξ.map_of_injective hφ
  have hζ : (z / φ w) ^ n = 1 := by rw [div_pow, hz, ← hz₀, div_self (pow_ne_zero _ hw0)]
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ
  have hzw : z = φ ξ ^ i * φ w := by rw [hi, div_mul_cancel₀ _ hw0]
  rw [hzw, map_mul, map_pow, toRingAut_traitGenericFieldMap, toRingAut_traitGenericFieldMap]

/-- **`P'` is a closed subgroup** of the absolute Galois group of `Frac K⟦t⟧` (Krull topology):
it is the intersection of the stabilizers of the elements of the image of `Ω`, each the fixing
subgroup of a finite subextension. In particular `P'` is profinite. -/
lemma isClosed_range_toAlgEquiv :
    IsClosed ((toAlgEquiv (k' := k') (K := K)).range :
      Set (traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K)) := by
  have h : ((toAlgEquiv (k' := k') (K := K)).range :
      Set (traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K)) =
      ⋂ y : traitGenericField k', ((IntermediateField.adjoin (FractionRing (PowerSeries K))
        {traitGenericFieldMap k' K y}).fixingSubgroup : Set _) := by
    ext e
    simp only [SetLike.mem_coe, mem_range_toAlgEquiv_iff, Set.mem_iInter]
    refine forall_congr' fun y ↦
      ⟨fun hy ↦ ?_, fun hy ↦ hy ⟨_, IntermediateField.mem_adjoin_simple_self _ _⟩⟩
    have : Subgroup.zpowers e ≤ (IntermediateField.adjoin (FractionRing (PowerSeries K))
        {traitGenericFieldMap k' K y}).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff,
        Set.singleton_subset_iff, SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      clear hf
      have hy' : e⁻¹ (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y :=
        (AlgEquiv.symm_apply_eq e).2 hy.symm
      induction n using Int.induction_on with
      | zero => simp
      | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hy, ih]
      | pred n ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hy', ih]
    exact this (Subgroup.mem_zpowers e)
  rw [h]
  refine isClosed_iInter fun y ↦ ?_
  have : FiniteDimensional (FractionRing (PowerSeries K))
      (IntermediateField.adjoin (FractionRing (PowerSeries K))
        {traitGenericFieldMap k' K y}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  exact IntermediateField.fixingSubgroup_isClosed _

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut
