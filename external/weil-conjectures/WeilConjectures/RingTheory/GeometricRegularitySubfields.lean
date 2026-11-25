/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.FieldTheory.IntermediateField.Basic
import WeilConjectures.FieldTheory.FinitePurelyInseparableScalarDescent
import WeilConjectures.FieldTheory.FinitePresentationSubfieldModel

/-!
# Geometric regularity over a directed union of subfields

Source: Stacks Project, Algebra, Lemma 07QG (blueprint:
lem-weil-pbc-geometrically-regular-over-subfields).
-/

@[expose] public section

universe u v w

/-- Geometric regularity over a directed union of subfields. Source: Stacks Project,
Algebra, Lemma 07QG (blueprint: lem-weil-pbc-geometrically-regular-over-subfields).

Proof:
1. By theorem-finite-etale-covers-proper-henselian--2, fix a finite purely inseparable field
extension k'/k. Choose a
   finite k-basis of k', giving a surjection from a polynomial algebra to k'. The field k
   is Noetherian (def-weil-pbc-noetherian-ring), and the polynomial algebra is Noetherian
   by lem-weil-pbc-finite-type-algebra-noetherian. Its kernel is finitely generated, so k'
   has a finite presentation by polynomial generators and relations.
2. The relations have finitely many coefficients. By hUnion and hdir, they all lie in
   one K i; use Nonempty I if there are no coefficients. Let k_i' be the quotient of the
   polynomial algebra over K i by these relations.
3. The lemmas lem-weil-pbc-tensor-cancel-base-change,
   lem-weil-pbc-polynomial-scalar-extension, and lem-weil-pbc-tensor-quotient-base-change
   identify k tensor over K i with k_i' with k' as k-algebras. In Stacks' printed identity
   the left side k_i is a misprint for k'.
4. By theorem-finite-etale-covers-proper-henselian--2, k_i' is a field and is finite
   purely inseparable over K i (def-weil-pbc-finite-purely-inseparable-extension).
5. By lem-weil-pbc-tensor-cancel-base-change and symmetry of tensor products, the rings
   k' tensor over k with A and k_i' tensor over K i with A are isomorphic. The latter is
   regular by hgeom and theorem-finite-etale-covers-proper-henselian--2. Regularity is preserved by
   ring isomorphisms. Since k'/k was arbitrary and A is Noetherian, A is geometrically regular over
   k.
-/
theorem geometricallyRegular_of_directed_subfields
    (k : Type u) [Field k]
    (I : Type v) [Nonempty I]
    (K : I → Subfield k)
    (hdir : ∀ i j : I, ∃ l : I, K i ≤ K l ∧ K j ≤ K l)
    (hUnion : ∀ x : k, ∃ i : I, x ∈ K i)
    (A : Type w) [CommRing A] [Algebra k A]
    (hA : IsNoetherianRing A)
    (hgeom : ∀ i : I, Algebra.IsGeometricallyRegular (K i) A) :
    Algebra.IsGeometricallyRegular k A := by
  classical
  refine ⟨hA, ?_⟩
  intro E _ _ _ _
  have : Algebra.FinitePresentation k E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨i, B, hB, aB, ⟨e⟩⟩ := Algebra.exists_subfield_model k I K hdir hUnion E
  let := hB
  let := aB
  have : Module.Finite k (TensorProduct (K i) k B) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have : IsPurelyInseparable k (TensorProduct (K i) k B) :=
    e.symm.isPurelyInseparable
  have ht : IsField (TensorProduct (K i) k B) := by
    exact MulEquiv.isField (Field.toIsField E) e.toMulEquiv
  obtain ⟨hf, hm, hp, _⟩ :=
    Algebra.TensorProduct.finite_purelyInseparable_of_tensorProduct (K i) k B ht
  let : Field B := hf.toField
  have := hm
  have := hp
  have : IsRegularRing (TensorProduct (K i) B A) := (hgeom i).2 B
  let t := (Algebra.TensorProduct.comm (K i) B A).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange (K i) k k A B).toRingEquiv.symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) e).toRingEquiv.trans
        (Algebra.TensorProduct.comm k A E).toRingEquiv))
  exact IsRegularRing.of_ringEquiv t
