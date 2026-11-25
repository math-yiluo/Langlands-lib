/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Finiteness
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.FormallySmoothAdicClosedFiber
import WeilConjectures.RingTheory.FormallySmoothAdicBaseChange
import WeilConjectures.RingTheory.FsAdicLiftOverFiniteCoefficientMap
import WeilConjectures.RingTheory.FormallySmoothRegularCompleteFiniteFieldRegular

/-!
# Geometric regularity of the generic fibre of a complete local domain

Source: Stacks Project, More on Algebra, Proposition 07PM, proof of (4) to (1).
(blueprint: lem-weil-pbc-formally-smooth-complete-local-generic-fiber)
-/

@[expose] public section

universe u v

namespace Algebra

private theorem formallySmoothAdic_of_algEquiv
    {R : Type u} {S : Type (max u v)} {T : Type v}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (n : Ideal S) (e : S ≃ₐ[R] T)
    (hfs : FormallySmoothAdic R S n) :
    FormallySmoothAdic R T (n.map e.toRingHom) := by
  intro D _ _ J hJ g hg
  let g' := g.comp e.toAlgHom
  obtain ⟨k, hk, hgk⟩ := hg
  have hg' : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g' x = 0 := by
    refine ⟨k, hk, ?_⟩
    intro x hx
    apply hgk
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem e.toRingHom hx
  obtain ⟨f, hf⟩ := hfs J hJ g' hg'
  refine ⟨f.comp e.symm.toAlgHom, ?_⟩
  ext x
  have hx := DFunLike.congr_fun hf (e.symm x)
  simpa [g'] using hx

/-- The generic fibre of an adically formally smooth map out of a complete local domain
is geometrically regular.
Source: Stacks Project, More on Algebra, Proposition 07PM, proof of (4) to (1),
after replacing the base by its quotient at a prime.
(blueprint: lem-weil-pbc-formally-smooth-complete-local-generic-fiber)

Proof: Choose a complete regular coefficient subring A₀ of A, finite with the same residue
field, by Algebra 032D. Lift the formally smooth closed fibre to a formally smooth complete
local A₀-algebra C using Remark 07NS, obtaining B = C tensor over A₀ with A. The fraction
field K of A is finite over K₀ = Frac(A₀), so tensor associativity and Algebra 0381 reduce
geometric regularity to C tensor over A₀ with K₀. Flatness and regularity of the closed
fibre (07NQ), regular local ascent (031E), and localization make this ring regular.
In characteristic zero this suffices. In characteristic p, induct on the degree of a finite
purely inseparable extension L/K₀. Choose its last degree-p step M[z]/(z^p-f) by Fields
09HI. A finite A₀-subalgebra A' of M with fraction field M is obtained by multiplying a
basis by denominators so the basis elements become integral. If f = c/e, replace f by
e^p f = e^(p-1)c and its root by e times that root, so f lies in A'. Lemma 07PH gives a
derivation of A' nonzero on f. Base change 07EG preserves formal smoothness; finite-module
completeness 00MA and 07PL extend this derivation to C tensor A', and localization extends
it to C tensor M. Its value on f is a unit because its nonzero value in A' becomes
invertible in M. Lemma 07PG proves regularity of the degree-p extension. Tensor
associativity identifies this extension with C tensor L, completing the induction.
Geometric regularity over K₀ now gives it over the finite extension K, using 0381 for
all finite field extensions of K. Noetherianity follows from localization of B.
-/
theorem isGeometricallyRegular_genericFiber_of_formallySmoothAdic
    {A : Type u} {B : Type v} {K : Type u}
    [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    [IsDomain A] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] [IsFractionRing A K]
    (hfs : FormallySmoothAdic A B (IsLocalRing.maximalIdeal B)) :
    IsGeometricallyRegular K (TensorProduct A K B) := by
  obtain ⟨A₀, hreg, hcomplete, hfinite, hmax, eres, heres, _hmodel⟩ :=
    IsLocalRing.complete_local_domain_finite_over_regular A
  let : IsRegularLocalRing A₀ := hreg
  have : IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀ := hcomplete
  have : Module.Finite A₀ A := hfinite
  have hlocal : IsLocalHom A₀.subtype := by
    apply ((IsLocalRing.local_hom_TFAE _).out 4 1).mp
    rw [hmax]
  have := hlocal
  have hres : Function.Bijective (IsLocalRing.ResidueField.map A₀.subtype) := by
    have heq : IsLocalRing.ResidueField.map A₀.subtype = eres.toRingHom := by
      apply Ideal.Quotient.ringHom_ext
      ext x
      exact (heres x).symm
    rw [heq]
    exact eres.bijective
  have halg : (algebraMap A B).toAlgebra = (inferInstance : Algebra A B) :=
    toAlgebra_algebraMap
  have hfs' : letI : Algebra A B := (algebraMap A B).toAlgebra
      FormallySmoothAdic A B (IsLocalRing.maximalIdeal B) := by
    exact halg.symm ▸ hfs
  have hflat := (RingHom.flat_and_isGeometricallyRegular_closedFiber_of_formallySmoothAdic
    (algebraMap A B) hfs').1
  let p := IsLocalRing.maximalIdeal A
  let I := p.map (algebraMap A B)
  let : Algebra (A ⧸ p) (B ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : Algebra (A ⧸ p) (TensorProduct A B (A ⧸ p)) :=
    Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A (A ⧸ p) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let eqt : (B ⧸ I) ≃ₐ[A ⧸ p] TensorProduct A B (A ⧸ p) :=
    AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).restrictScalars A)
  have heqt : eqt.symm.toRingHom.comp
      (algebraMap B (TensorProduct A B (A ⧸ p))) = Ideal.Quotient.mk I := by
    ext b
    exact eqt.symm_apply_apply (Ideal.Quotient.mk I b)
  have hqfs := formallySmoothAdic_of_algEquiv
    ((IsLocalRing.maximalIdeal B).map
      (algebraMap B (TensorProduct A B (A ⧸ p)))) eqt.symm
    (formallySmoothAdic_tensorProduct A B (A ⧸ p) (IsLocalRing.maximalIdeal B) hfs)
  rw [Ideal.map_map, heqt] at hqfs
  obtain ⟨C, hC, hClocal, hCalg, hCnoeth, hCcomplete, γ, hγ, hγlocal, hγfs,
      ψ, hψlocal, hψ, F, hF, hFtmul⟩ :=
    RingHom.exists_fs_adic_lift_over_finite_coefficient_map A₀.subtype rfl hres
      (algebraMap A B) rfl hflat hqfs
  let := hC
  let := hClocal
  let := hCalg
  have := hCnoeth
  have := hCcomplete
  have : IsLocalHom (algebraMap A₀ C) := hγ ▸ hγlocal
  let : Algebra A₀ K := ((algebraMap A K).comp A₀.subtype).toAlgebra
  have : IsScalarTower A₀ A K := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul A₀ K :=
    (faithfulSMul_iff_algebraMap_injective A₀ K).mpr
      ((IsFractionRing.injective A K).comp Subtype.val_injective)
  let K₀ := FractionRing A₀
  let : Algebra K₀ K := FractionRing.liftAlgebra A₀ K
  have : IsScalarTower A₀ K₀ K := FractionRing.isScalarTower_liftAlgebra A₀ K
  have : Module.Finite K₀ K := Module.Finite.of_isLocalization A₀ A (nonZeroDivisors A₀)
  let D := TensorProduct A₀ C A
  let : Algebra A D := Algebra.TensorProduct.rightAlgebra
  let e : D ≃ₐ[A] B :=
    { RingEquiv.ofBijective F hF with
      commutes' := fun a ↦ by
        change F (TensorProduct.tmul A₀ 1 a) = algebraMap A B a
        rw [hFtmul, map_one, one_mul] }
  refine ⟨?_, ?_⟩
  · let : Algebra B (TensorProduct A B K) := Algebra.TensorProduct.leftAlgebra
    have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
        (TensorProduct A B K) := IsLocalization.tensor (S := B) (A := K) _
    have := IsLocalization.isNoetherianRing
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (TensorProduct A B K)
      (inferInstance : IsNoetherianRing B)
    exact isNoetherianRing_of_ringEquiv (TensorProduct A B K)
      (Algebra.TensorProduct.comm A B K).toRingEquiv
  · intro L _ _ _ _
    let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra K₀ L := ((algebraMap K L).comp (algebraMap K₀ K)).toAlgebra
    have : IsScalarTower K₀ K L := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A₀ L := ((algebraMap K₀ L).comp (algebraMap A₀ K₀)).toAlgebra
    have : IsScalarTower A₀ K₀ L := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower A₀ A L := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change algebraMap K L (algebraMap K₀ K (algebraMap A₀ K₀ x)) =
        algebraMap K L (algebraMap A K x.val)
      rw [← IsScalarTower.algebraMap_apply A₀ K₀ K]
      rfl
    have : Module.Finite K₀ L := Module.Finite.trans K L
    have : IsRegularRing (TensorProduct A₀ L C) :=
      isRegularRing_tensorProduct_of_formallySmoothAdic_regular_complete
        A₀ C K₀ L hγfs
    let e₁ := Algebra.TensorProduct.cancelBaseChange A K L L B
    let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e.symm
    let e₃ := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
      (Algebra.TensorProduct.commRight A₀ A C).symm
    let e₄ := Algebra.TensorProduct.cancelBaseChange A₀ A L L C
    exact IsRegularRing.of_ringEquiv (e₁.trans (e₂.trans (e₃.trans e₄))).symm.toRingEquiv

end Algebra
