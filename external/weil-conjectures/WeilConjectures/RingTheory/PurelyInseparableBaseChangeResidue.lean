/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.Flat.Basic
@[expose] public section
set_option autoImplicit false
universe u v w
open scoped TensorProduct
namespace Algebra.TensorProduct
/-- Locality, residue, and closed-fibre properties of purely inseparable tensor base change.
Source: Stacks Project, More on Algebra, proof of Proposition Tag 07E5, (3) => (1),
where locality and finite flatness are used without proof; expanded argument below.
(blueprint: lem-weil-pbc-purely-inseparable-base-change-residue)

Proof: Write m for the maximal ideal of A, K = A/m, and d = [k':k]. A k-basis of k'
extends to a finite A-basis of A' = A tensor k', so A' is finite over A. The tensor
quotient isomorphism, the swap, and cancellation of base change identify C = A'/mA'
with B = K tensor k'; on pure tensors the map is [a tensor x] to residue(a) tensor x.
A scalar-extended k-basis of k' is a K-basis of B of size d. Transporting that basis
through the isomorphism, with precisely the K-action induced by its inverse as in the
statement, proves the displayed finrank equality. Since k' is a nonzero field, d is
positive, and this basis also shows B is nonzero.

Every z in B has a positive power in the image of K, by
`IsPurelyInseparable.exists_pow_mem_range_tensorProduct`. If that scalar is zero then
z is nilpotent; otherwise that power, hence z, is a unit. Thus the nilradical N of B
is proper and every element outside it is a unit. Every proper ideal lies in N, so
N is maximal. Every prime contains all nilpotents, hence N is the only prime of B.
Pull N back along A' to C to B to obtain m'. Its quotient is B/N, a field, and prime
correspondence shows m' is the only prime containing mA'. Every maximal ideal of A'
contracts to a maximal ideal of A, since the finite algebra A' is integral over A.
That contraction is m, so every maximal ideal contains mA' and equals m'. Thus A'
is local. The map A to A'/m' kills m and descends to the required ring map f from K;
its formula on residue classes gives the stated compatibility. Finally C surjects
onto A'/m' because mA' is contained in m'. This map is K-linear for f, so images
of the d basis vectors span A'/m' over K, proving its finiteness. -/
theorem purelyInseparable_baseChange_residue
    (k : Type u) (k' : Type v) (A : Type w)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A]
    [IsPurelyInseparable k k'] [Module.Finite k k']
    [IsLocalRing A] [IsNoetherianRing A] :
    IsLocalRing (A ⊗[k] k') ∧
      (∃ m' : Ideal (A ⊗[k] k'),
        m'.IsMaximal ∧
        (∀ P : Ideal (A ⊗[k] k'), P.IsPrime →
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A) ≤ P ↔ P = m')) ∧
        (∃ f : IsLocalRing.ResidueField A →+* ((A ⊗[k] k') ⧸ m'),
          (∀ a : A, f (IsLocalRing.residue A a) =
            Ideal.Quotient.mk m' (algebraMap A (A ⊗[k] k') a)) ∧
          @Module.Finite (IsLocalRing.ResidueField A) ((A ⊗[k] k') ⧸ m')
            _ _ (@Algebra.toModule _ _ _ _ f.toAlgebra))) ∧
      (∃ e : ((A ⊗[k] k') ⧸
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A))) ≃+*
          ((IsLocalRing.ResidueField A) ⊗[k] k'),
        (∀ (a : A) (x : k'), e (Ideal.Quotient.mk
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A))
          (a ⊗ₜ[k] x)) = (IsLocalRing.residue A a) ⊗ₜ[k] x) ∧
        @Module.finrank (IsLocalRing.ResidueField A)
          ((A ⊗[k] k') ⧸
            (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A)))
          _ _ (@Algebra.toModule _ _ _ _
            (e.symm.toRingHom.comp (algebraMap (IsLocalRing.ResidueField A)
              ((IsLocalRing.ResidueField A) ⊗[k] k'))).toAlgebra) =
            Module.finrank k k') := by
  classical
  let B := A ⊗[k] k'
  let K := IsLocalRing.ResidueField A
  let m := IsLocalRing.maximalIdeal A
  have : Module.Finite A B := inferInstance
  have hspec := (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k k' A).bijective
  have : Nontrivial B := (includeLeft_injective (S := A) (algebraMap k k').injective).nontrivial
  have hmax : ∀ n : Ideal B, n.IsMaximal → n.comap (algebraMap A B) = m := by
    intro n hn
    have : n.IsMaximal := hn
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) n)
  obtain ⟨n, hn⟩ := Ideal.exists_maximal B
  have hlocal : IsLocalRing B := IsLocalRing.of_unique_max_ideal ⟨n, hn, by
    intro q hq
    have he : (⟨q, hq.isPrime⟩ : PrimeSpectrum B) = ⟨n, hn.isPrime⟩ :=
      hspec.injective (PrimeSpectrum.ext ((hmax q hq).trans (hmax n hn).symm))
    exact congrArg PrimeSpectrum.asIdeal he⟩
  have hmn : Ideal.map (algebraMap A B) m ≤ n :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq (hmax n hn).symm)
  have hunique : ∀ P : Ideal B, P.IsPrime →
      (Ideal.map (algebraMap A B) m ≤ P ↔ P = n) := by
    intro P hP
    constructor
    · intro h
      have hp : P.comap (algebraMap A B) = m := by
        apply le_antisymm
        · exact IsLocalRing.le_maximalIdeal (hP.comap (algebraMap A B)).ne_top
        · exact Ideal.map_le_iff_le_comap.mp h
      have he : (⟨P, hP⟩ : PrimeSpectrum B) = ⟨n, hn.isPrime⟩ :=
        hspec.injective (PrimeSpectrum.ext (hp.trans (hmax n hn).symm))
      exact congrArg PrimeSpectrum.asIdeal he
    · rintro rfl
      exact hmn
  let e : (B ⧸ Ideal.map (algebraMap A B) m) ≃+* (K ⊗[k] k') :=
    (quotientTensorEquiv (R := k) k k' A m).symm.toRingEquiv
  refine ⟨hlocal, ⟨n, hn, hunique, ?_⟩, ⟨e, ?_, ?_⟩⟩
  · let f : K →+* (B ⧸ n) := Ideal.Quotient.lift m
      ((Ideal.Quotient.mk n).comp (algebraMap A B)) (by
        intro a ha
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmn (Ideal.mem_map_of_mem _ ha)))
    have hf : ∀ a : A, f (IsLocalRing.residue A a) =
        Ideal.Quotient.mk n (algebraMap A B a) := fun _ ↦ rfl
    refine ⟨f, hf, ?_⟩
    let := f.toAlgebra
    have : IsScalarTower A K (B ⧸ n) := IsScalarTower.of_algebraMap_eq fun a ↦ (hf a).symm
    have : Module.Finite A (B ⧸ n) := inferInstance
    exact Module.Finite.of_restrictScalars_finite A K (B ⧸ n)
  · intro a x
    exact quotientTensorEquiv_symm_apply_tmul (R := k) k k' A m a x
  · let := (e.symm.toRingHom.comp (algebraMap K (K ⊗[k] k'))).toAlgebra
    let el : (B ⧸ Ideal.map (algebraMap A B) m) ≃ₗ[K] K ⊗[k] k' :=
      { e.toAddEquiv with
        map_smul' := by
          intro r x
          change e (e.symm (algebraMap K (K ⊗[k] k') r) * x) = r • e x
          rw [map_mul, e.apply_symm_apply, Algebra.smul_def] }
    exact el.finrank_eq.trans (Module.finrank_baseChange (S := k) (R := K) (M' := k'))
end Algebra.TensorProduct
