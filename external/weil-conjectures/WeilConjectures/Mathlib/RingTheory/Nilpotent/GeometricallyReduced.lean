/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Tensor products of reduced algebras over a perfect field

Over a perfect field every reduced algebra is geometrically reduced, so the tensor product of two
reduced algebras is reduced: a product of reduced varieties is reduced.

The proof reduces to fields. A reduced ring `A` embeds coordinatewise into the product of its
residue fields, so `A ⊗[k] B` is reduced once every `κ(p) ⊗[k] B` is
(`isReduced_tensorProduct_of_forall_residueField`); applied on both sides this leaves
`K ⊗[k] L` for fields `K, L`. Reducing `L` to its finitely generated subfields, `L` has a
separating transcendence basis over the perfect field `k`: `L` is separable algebraic over a
purely transcendental extension `E`. Then `K ⊗[k] E` is a localization of a polynomial ring over
`K`, and `K ⊗[k] L` is obtained from it by an unramified base change, so it is reduced.

## Main results

- `isReduced_tensorProduct_of_forall_residueField`
- `isReduced_tensorProduct_of_field`
- `isReduced_tensorProduct_of_perfectField`

## Blueprint

- `det-i-geometry`: products of reduced varieties over a perfect field are reduced.
-/

@[expose] public section

open TensorProduct

/-- If `A` is reduced and `κ(p) ⊗[k] B` is reduced for every prime `p` of `A`, then `A ⊗[k] B` is
reduced: a nilpotent element of `A ⊗[k] B` vanishes in every `κ(p) ⊗[k] B`, and these maps are
jointly injective since the primes of `A` intersect to `0`. -/
theorem isReduced_tensorProduct_of_forall_residueField {k A B : Type*} [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [IsReduced A]
    (h : ∀ p : PrimeSpectrum A, IsReduced (p.asIdeal.ResidueField ⊗[k] B)) :
    IsReduced (A ⊗[k] B) := by
  refine ⟨fun t ht ↦ TensorProduct.eq_zero_of_forall_rTensor_eq_zero
    (fun p : PrimeSpectrum A ↦ (IsScalarTower.toAlgHom k A p.asIdeal.ResidueField).toLinearMap)
    (fun a ha ↦ ?_) fun p ↦ ?_⟩
  · have : a ∈ nilradical A := by
      rw [nilradical_eq_sInf, Submodule.mem_sInf]
      intro q hq
      simpa [Ideal.algebraMap_residueField_eq_zero] using ha ⟨q, hq⟩
    rwa [nilradical_eq_zero, Submodule.zero_eq_bot, Ideal.mem_bot] at this
  · exact (h p).eq_zero _
      (ht.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A p.asIdeal.ResidueField)
        (AlgHom.id k B)))

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- Over a field `k`, the tensor product of a field `K` with a purely transcendental extension
`k(v)` is reduced: it is a localization of the polynomial ring `K ⊗[k] k[v] ≃ K[v]`. -/
theorem isReduced_tensorProduct_adjoin_of_algebraicIndependent {k K F ι : Type*} [Field k]
    [Field K] [Field F] [Algebra k K] [Algebra k F] {v : ι → F} (hv : AlgebraicIndependent k v) :
    IsReduced (K ⊗[k] IntermediateField.adjoin k (Set.range v)) := by
  have : IsReduced (K ⊗[k] Algebra.adjoin k (Set.range v)) := isReduced_of_injective
    ((Algebra.TensorProduct.congr AlgEquiv.refl hv.aevalEquiv.symm).trans
      (MvPolynomial.algebraTensorAlgEquiv k K)) (AlgEquiv.injective _)
  exact isReduced_tensorProduct_of_isLocalization
    (nonZeroDivisors (Algebra.adjoin k (Set.range v)))

/-- Let `k → E → F` be fields with `F` formally unramified and essentially of finite type over
`E`. If `E ⊗[k] K` is reduced, so is `K ⊗[k] F ≃ (E ⊗[k] K) ⊗[E] F`: by
`isReduced_tensorProduct_of_forall_residueField` it suffices that each `κ ⊗[E] F` is reduced, and
it is formally unramified and essentially of finite type over the field `κ`. -/
theorem isReduced_tensorProduct_of_formallyUnramified {k K E F : Type*} [Field k] [Field K]
    [Field E] [Field F] [Algebra k K] [Algebra k E] [Algebra k F] [Algebra E F]
    [IsScalarTower k E F] [Algebra.FormallyUnramified E F] [Algebra.EssFiniteType E F]
    (hE : IsReduced (E ⊗[k] K)) : IsReduced (K ⊗[k] F) := by
  have : IsReduced ((E ⊗[k] K) ⊗[E] F) := isReduced_tensorProduct_of_forall_residueField
    fun p ↦ Algebra.FormallyUnramified.isReduced_of_field p.asIdeal.ResidueField _
  let e : K ⊗[k] F ≃+* (E ⊗[k] K) ⊗[E] F :=
    (Algebra.TensorProduct.comm k K F).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange k E E F K).symm.toRingEquiv.trans
        (Algebra.TensorProduct.comm E F (E ⊗[k] K)).toRingEquiv)
  exact isReduced_of_injective e e.injective

/-- Over a perfect field `k`, the tensor product of a field `K` with a field `F` essentially of
finite type over `k` is reduced: `F` is separable algebraic over a purely transcendental extension
of `k`. -/
theorem isReduced_tensorProduct_of_essFiniteType (k K F : Type*) [Field k] [PerfectField k]
    [Field K] [Field F] [Algebra k K] [Algebra k F] [Algebra.EssFiniteType k F] :
    IsReduced (K ⊗[k] F) := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  set E := IntermediateField.adjoin k (s : Set F)
  have hE : IsReduced (K ⊗[k] E) := by
    have := isReduced_tensorProduct_adjoin_of_algebraicIndependent (K := K) hs.1
    rw [Subtype.range_coe_subtype] at this
    exact this
  have : Algebra.FormallyEtale E F := Algebra.FormallyEtale.of_isSeparable E F
  have : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp k E F
  exact isReduced_tensorProduct_of_formallyUnramified (E := E)
    (isReduced_of_injective (Algebra.TensorProduct.comm k E K) (AlgEquiv.injective _))
/-- Over a perfect field `k`, the tensor product of two field extensions is reduced. -/
theorem isReduced_tensorProduct_of_field (k K L : Type*) [Field k] [PerfectField k]
    [Field K] [Field L] [Algebra k K] [Algebra k L] : IsReduced (K ⊗[k] L) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun D hD ↦ ?_
  have : Algebra.FiniteType k D := (Subalgebra.fg_iff_finiteType D).mp hD
  have : Algebra.EssFiniteType k (FractionRing D) :=
    Algebra.EssFiniteType.comp k D (FractionRing D)
  have := isReduced_tensorProduct_of_essFiniteType k K (FractionRing D)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k D (FractionRing D)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective D _))
/-- Over a perfect field `k`, the tensor product of two reduced `k`-algebras is reduced.
(blueprint: `det-i-geometry`)

By `isReduced_tensorProduct_of_forall_residueField`, applied in both factors, this reduces to the
tensor product of two field extensions, `isReduced_tensorProduct_of_field`. -/
theorem isReduced_tensorProduct_of_perfectField (k A B : Type*) [Field k] [PerfectField k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [IsReduced A] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  refine isReduced_tensorProduct_of_forall_residueField fun p ↦ ?_
  have : IsReduced (B ⊗[k] p.asIdeal.ResidueField) :=
    isReduced_tensorProduct_of_forall_residueField fun q ↦ isReduced_tensorProduct_of_field k _ _
  exact isReduced_of_injective (Algebra.TensorProduct.comm k _ _) (AlgEquiv.injective _)
