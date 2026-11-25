/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Extension.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.CotangentComplexSymmetricAlgebra

/-! # The conormal module of a split symmetric-algebra presentation

Source: Stacks Project, More on Algebra, Tag 07EV, restricted to a projective quotient;
Smoothing Ring Maps, proof of Tag 07CE.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Algebra

/-- Source: Stacks Project, More on Algebra, proof of Tag 07EV, and Smoothing Ring Maps,
proof of Tag 07CE, lines 393–414.
(blueprint: lem-weil-pbc-projective-symmetric-presentation-conormal-equiv)

Proof. The general symmetric-algebra conormal theorem (Stacks 07EV, restricted to
its true surjectivity assertion) constructs a surjective linear map `lam` with the
specified formula. Projectivity splits `q`, giving a retraction of `ker q ↪ A^m`.
Tensoring that retraction with `C = Sym_A(M)` proves injectivity of the base-changed
inclusion. The differential formula in the general theorem, expressed in the
polynomial Kähler basis `dy_j`, identifies the composite `δ ∘ lam` with that inclusion:
its coordinates on `c ⊗ k` are `c k_j`. Both coordinate identifications are the
base-changed basis equivalences. Thus `lam` is injective, and its existing surjectivity
upgrades it to a linear equivalence. The generator formula is unchanged. This argument
also works for the zero ring and for an empty family of generators. -/
theorem projective_symmetric_presentation_conormal_equiv
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Projective A M] (m : ℕ)
    (q : (Fin m → A) →ₗ[A] M) (hq : Function.Surjective q)
    (α : MvPolynomial (Fin m) A →ₐ[A] SymmetricAlgebra A M)
    (hαX : ∀ j, α (MvPolynomial.X j) = SymmetricAlgebra.ι A M (q (Pi.single j 1)))
    (hα : Function.Surjective α) :
    ∃ lam : SymmetricAlgebra A M ⊗[A] LinearMap.ker q
        ≃ₗ[SymmetricAlgebra A M] (Extension.ofSurjective α hα).Cotangent,
      ∀ (c : SymmetricAlgebra A M) (k : LinearMap.ker q)
        (y : (Extension.ofSurjective α hα).ker),
        y.1 = ∑ j, MvPolynomial.C (k.1 j) * MvPolynomial.X j →
          lam (c ⊗ₜ k) = c • Extension.Cotangent.mk y := by
  classical
  have hαeq : α = MvPolynomial.aeval
      (fun j ↦ SymmetricAlgebra.ι A M (q (Pi.single j 1))) := by
    ext j
    rw [MvPolynomial.aeval_X]
    exact hαX j
  subst α
  obtain ⟨⟨hsurj, hker, lam, hlam, hsurjlam, hdlam, hrange⟩, ediff⟩ :=
    AlgebraicGeometry.cotangentComplex_symmetricAlgebra (LinearMap.ker q) q hq rfl
  let C := SymmetricAlgebra A M
  let G := Generators.ofSurjective
    (fun j ↦ SymmetricAlgebra.ι A M (q (Pi.single j 1))) hsurj
  let : Algebra (MvPolynomial (Fin m) A) C := G.toExtension.algebra₂
  let : IsScalarTower A (MvPolynomial (Fin m) A) C := G.toExtension.isScalarTower
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  let e := ((LinearMap.exact_subtype_ker_map q).splitSurjectiveEquiv
    (Submodule.injective_subtype _) ⟨s, hs⟩).1
  let t := (LinearMap.fst A (LinearMap.ker q) M).comp e.toLinearMap
  have ht : t.comp (LinearMap.ker q).subtype = LinearMap.id := by
    rw [show (LinearMap.ker q).subtype =
      e.symm.toLinearMap.comp (LinearMap.inl A (LinearMap.ker q) M) from
      ((LinearMap.exact_subtype_ker_map q).splitSurjectiveEquiv
        (Submodule.injective_subtype _) ⟨s, hs⟩).2.1]
    ext k
    simp [t]
  let inc := (LinearMap.ker q).subtype.baseChange C
  have hinc : Function.Injective inc := by
    apply Function.LeftInverse.injective (g := t.baseChange C)
    intro x
    change ((t.baseChange C).comp inc) x = x
    rw [← LinearMap.baseChange_comp, ht, LinearMap.baseChange_id]
    rfl
  let b := KaehlerDifferential.mvPolynomialBasis A (Fin m)
  let d := (b.baseChange C).equivFun
  let v := ((Pi.basisFun A (Fin m)).baseChange C).equivFun
  have hd : d.toLinearMap.comp (G.toExtension.cotangentComplex.comp lam) =
      v.toLinearMap.comp inc := by
    ext k j
    change d (G.toExtension.cotangentComplex (lam (1 ⊗ₜ k))) j = v (inc (1 ⊗ₜ k)) j
    rw [hdlam]
    simp only [one_mul]
    change d (∑ l, algebraMap A C (k.1 l) •
      ((1 : C) ⊗ₜ[MvPolynomial (Fin m) A]
        KaehlerDifferential.D A (MvPolynomial (Fin m) A) (MvPolynomial.X l))) j = _
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    simp [d, v, inc, b, Module.Basis.equivFun_apply, Finsupp.single_apply, Algebra.smul_def]
  have hlaminj : Function.Injective lam := by
    intro x y hxy
    apply hinc
    apply v.injective
    change (v.toLinearMap.comp inc) x = (v.toLinearMap.comp inc) y
    rw [← hd]
    change d (G.toExtension.cotangentComplex (lam x)) =
      d (G.toExtension.cotangentComplex (lam y))
    rw [hxy]
  refine ⟨LinearEquiv.ofBijective lam ⟨hlaminj, hsurjlam⟩, ?_⟩
  exact hlam

end Algebra
