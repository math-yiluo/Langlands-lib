/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

@[expose] public section

universe u
open scoped TensorProduct
namespace Algebra

/--
Source: Stacks Project, Smoothing Ring Maps, Lemmas 07CG and 07CH.
(blueprint: new-smooth-quotient-fibre-finrank-add-le)
The split conormal sequence embeds a rank-c summand in the rank-n polynomial
differential module, hence c ≤ n.
-/
theorem smooth_quotient_fibre_finrank_add_le
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (p : Ideal R) [p.IsPrime]
    (q : PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) :
    c ≤ n := by
  classical
  let I := Ideal.span (Set.range f)
  let A := MvPolynomial (Fin n) R ⧸ I
  let qA : PrimeSpectrum A :=
    PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q
  have : Nontrivial A := nontrivial_of_ne (0 : A) 1 fun h ↦
    qA.isPrime.one_notMem (h ▸ qA.asIdeal.zero_mem)
  let α := Ideal.Quotient.mkₐ R I
  have hα₀ : MvPolynomial.aeval (α ∘ MvPolynomial.X) = α := by
    ext i
    simp
  let P : Generators R A (Fin n) :=
    { Generators.ofAlgHom α (Ideal.Quotient.mkₐ_surjective R I) with
      algebra := inferInstance
      algebraMap_eq := by
        change (Ideal.Quotient.mk I) = _
        exact congrArg AlgHom.toRingHom hα₀.symm }
  have hα : MvPolynomial.aeval (P.val) = Ideal.Quotient.mkₐ R I := by
    ext i
    simp [P, α, Generators.ofAlgHom, Generators.ofSurjective]
    rfl
  have hp : P.ker = I := by
    rw [Generators.ker_eq_ker_aeval_val, hα]
    exact Ideal.Quotient.mkₐ_ker R I
  let e : P.toExtension.Cotangent ≃ₗ[MvPolynomial (Fin n) R] I.Cotangent := by
    let e₀ := Extension.cotangentEquivCotangentKer (P := P.toExtension)
    let e₁ := Ideal.Cotangent.equivOfEq P.toExtension.ker I hp
    exact e₀ ≪≫ₗ e₁
  let eA : P.toExtension.Cotangent ≃ₗ[A] I.Cotangent :=
    e.extendScalarsOfSurjective P.algebraMap_surjective
  have hi : Function.Injective P.toExtension.cotangentComplex := by
    have : FormallySmooth R P.toExtension.Ring :=
      inferInstanceAs (FormallySmooth R (MvPolynomial _ R))
    exact P.toExtension.cotangentComplex_injective_iff.mpr inferInstance
  let φ : (Fin c → A) →ₗ[A] (Fin n → A) :=
    P.cotangentSpaceBasis.equivFun.toLinearMap.comp
      (P.toExtension.cotangentComplex.comp
        (eA.symm.toLinearMap.comp b.equivFun.symm.toLinearMap))
  have hφ : Function.Injective φ := P.cotangentSpaceBasis.equivFun.injective.comp
    (hi.comp (eA.symm.injective.comp b.equivFun.symm.injective))
  simpa only [Fintype.card_fin] using card_le_of_injective A φ hφ

end Algebra
