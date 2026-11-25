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
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.Dimension.Finite
import WeilConjectures.RingTheory.PurelyInseparableBaseChangeStructural
import WeilConjectures.RingTheory.PurelyInseparableBaseChangeResidue

/-! # Purely inseparable base change of a Noetherian local algebra

Source: Stacks Project, More on Algebra, proof of Proposition Tag 07E5, (3) => (1)
(blueprint: lem-weil-pbc-purely-inseparable-base-change-local-ring).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Base change of a Noetherian local algebra along a finite purely inseparable extension is
finite free, flat, Noetherian and local, with the stated closed fibre and finite residue extension.
Source: Stacks Project, More on Algebra, proof of Proposition Tag 07E5, (3) => (1)
(blueprint: lem-weil-pbc-purely-inseparable-base-change-local-ring).

Proof (the six steps recorded in the node, expanding facts used without proof in Stacks):
1. Choose a k-basis of k' with d elements. Apply lem-weil-pbc-free-base-change-tower
   and swap tensor factors to obtain an A-basis of A' with d elements. This proves
   finite generation and freeness. Use lem-weil-pbc-projective-module-flat for flatness
   and lem-weil-pbc-finite-algebra-noetherian for Noetherianity. Since A is nonzero and
   d is positive, A' is nonzero.
2. Apply lem-weil-pbc-tensor-quotient-base-change at the maximal ideal m, swap factors
   and use lem-weil-pbc-tensor-cancel-base-change. The resulting closed-fibre isomorphism
   sends the class of a tensor x to the residue of a tensor x, so it commutes with the
   maps from A. Scalar extension of the k-basis gives a K-basis of K tensor k' with d
   elements (def-weil-vector-space-scalar-extension), hence its dimension is d.
3. Every element of K tensor k' is a unit or nilpotent. In characteristic zero pure
   inseparability makes k' = k. In characteristic p, write an element as a finite sum
   of pure tensors and choose a common p-power putting all its k'-coordinates in k.
   Frobenius (def-weil-ring-frobenius) turns that power into c tensor 1. If c vanishes
   the element is nilpotent; otherwise it is a unit.
4. The nilpotent elements form a proper ideal N. By step 3 every proper ideal lies in
   N, so N is maximal. Every prime contains N, and hence N is the unique prime.
5. Transport N through the closed-fibre isomorphism and take its inverse image m' in
   A'. The prime correspondence shows that m' is the only prime containing mA', and
   its quotient is a field. Every maximal ideal of A' contains mA', by
   lem-weil-pbc-finite-algebra-local-radical, hence equals m'. Thus A' is local.
6. The residue field A'/m' is a quotient of the d-dimensional closed fibre, so its
   canonical K-vector space is finite dimensional. The map K to this residue field is
   injective because both are fields. This gives the finite field extension. -/
theorem purelyInseparable_baseChange_localRing
    (k : Type u) (k' : Type v) (A : Type w)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A]
    [IsPurelyInseparable k k'] [Module.Finite k k']
    [IsLocalRing A] [IsNoetherianRing A] :
    Nonempty (Module.Basis (Fin (Module.finrank k k')) A (A ⊗[k] k')) ∧
      Module.Free A (A ⊗[k] k') ∧
      Module.Finite A (A ⊗[k] k') ∧
      RingHom.Flat (algebraMap A (A ⊗[k] k')) ∧
      IsNoetherianRing (A ⊗[k] k') ∧
      IsLocalRing (A ⊗[k] k') ∧
      (∃ m' : Ideal (A ⊗[k] k'),
        m'.IsMaximal ∧
        (∀ P : Ideal (A ⊗[k] k'), P.IsPrime →
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A) ≤ P ↔
            P = m')) ∧
        (∃ f : IsLocalRing.ResidueField A →+* ((A ⊗[k] k') ⧸ m'),
          (∀ a : A, f (IsLocalRing.residue A a) =
            Ideal.Quotient.mk m' (algebraMap A (A ⊗[k] k') a)) ∧
          @Module.Finite (IsLocalRing.ResidueField A) ((A ⊗[k] k') ⧸ m')
            _ _ (@Algebra.toModule _ _ _ _ f.toAlgebra))) ∧
      (∃ e : ((A ⊗[k] k') ⧸
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A))) ≃+*
          ((IsLocalRing.ResidueField A) ⊗[k] k'),
        (∀ (a : A) (x : k'),
          e (Ideal.Quotient.mk
            (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A))
            (a ⊗ₜ[k] x)) = (IsLocalRing.residue A a) ⊗ₜ[k] x) ∧
        @Module.finrank (IsLocalRing.ResidueField A)
          ((A ⊗[k] k') ⧸
            (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A)))
          _ _ (@Algebra.toModule _ _ _ _
            (e.symm.toRingHom.comp
              (algebraMap (IsLocalRing.ResidueField A)
                ((IsLocalRing.ResidueField A) ⊗[k] k'))).toAlgebra) =
            Module.finrank k k') := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ :=
    purelyInseparable_baseChange_structural k k' A
  obtain ⟨h₆, h₇, h₈⟩ :=
    purelyInseparable_baseChange_residue k k' A
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

end Algebra.TensorProduct
