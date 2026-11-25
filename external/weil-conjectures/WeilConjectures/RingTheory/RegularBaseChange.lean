/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Regular maps and finite type base change

Source: Stacks Project, More on Algebra, Lemma Tag 07C1 (blueprint:
lem-weil-pbc-regular-base-change).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace RingHom

/-- A regular ring map remains regular after base change along a finite type ring map.

This is the statement of Stacks Project, More on Algebra, Lemma Tag 07C1:
if `φ : R → Λ` is regular and `R → R'` is of finite type, then the map
`R' → Λ ⊗_R R'` induced by the second tensor factor is regular.
(blueprint: lem-weil-pbc-regular-base-change)

Proof (the six steps of the node, following Stacks 07C1):
1. Flat base change makes the second-factor map flat. Use
   lem-weil-pbc-flat-module-base-change, tensor symmetry, and def-weil-pbc-flat-ring-map.
2. For a prime p' of R', its inverse image p is prime. The induced residue-field map
   κ(p) → κ(p') commutes with the structure maps (def-weil-pbc-localization-at-prime).
   Finite type of R → R' makes this field extension finitely generated, by
   lem-weil-pbc-finite-type-residue-field-extension-finitely-generated.
3. Put A = κ(p) ⊗[R] Λ. Tensor symmetry and two applications of
   lem-weil-pbc-tensor-cancel-base-change identify the new fibre with κ(p') ⊗[κ(p)] A.
   The two R-algebra structures on κ(p') agree by step 2.
4. Regularity of φ makes A Noetherian and geometrically regular
(theorem-finite-etale-covers-proper-henselian--2).
   Apply lem-weil-pbc-geometrically-regular-finitely-generated-extensions to κ(p')/κ(p).
   The fibre is Noetherian by step 3 and def-weil-pbc-noetherian-ring.
5. For any finite purely inseparable extension k''/κ(p')
   (def-weil-pbc-finite-purely-inseparable-extension), tensor cancellation identifies
   its base-changed fibre with k'' ⊗[κ(p)] A. This extension of κ(p) is finitely generated:
   compose the essentially finite type residue-field extension with the finite extension.
   Apply lem-weil-pbc-geometrically-regular-finitely-generated-extensions again.
   Ring isomorphisms preserve regularity (def-weil-regular-scheme), so the new fibre
   is geometrically regular by theorem-finite-etale-covers-proper-henselian--2.
6. Flatness and the Noetherian, geometrically regular fibres give regularity of the
   second-factor map by theorem-finite-etale-covers-proper-henselian--2.
-/
theorem regular_base_change
    {R : Type u} {Λ : Type v} {R' : Type w}
    [CommRing R] [CommRing Λ] [CommRing R'] [Algebra R Λ] [Algebra R R']
    [Algebra.FiniteType R R'] (hφ : (algebraMap R Λ).IsRegular) :
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] Λ ⊗[R] R').toRingHom.IsRegular := by
  classical
  let : Algebra R' (Λ ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  change (algebraMap R' (Λ ⊗[R] R')).IsRegular
  rw [IsRegular, toAlgebra_algebraMap] at hφ ⊢
  have : Module.Flat R Λ := flat_algebraMap_iff.mp hφ.1
  refine ⟨?_, ?_⟩
  · apply flat_algebraMap_iff.mpr
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight R R' Λ).symm.toLinearEquiv
  · intro q hq
    let p : Ideal R := q.comap (algebraMap R R')
    have : p.IsPrime := Ideal.comap_isPrime _ q
    have : q.LiesOver p := ⟨rfl⟩
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
    have hp := hφ.2 p
    let e : q.Fiber (Λ ⊗[R] R') ≃ₐ[q.ResidueField]
        q.ResidueField ⊗[p.ResidueField] p.Fiber Λ :=
      (Algebra.TensorProduct.congr (.refl : q.ResidueField ≃ₐ[q.ResidueField] q.ResidueField)
        (Algebra.TensorProduct.commRight R R' Λ).symm).trans
        ((Algebra.TensorProduct.cancelBaseChange R R' q.ResidueField q.ResidueField Λ).trans
          (Algebra.TensorProduct.cancelBaseChange R p.ResidueField
            q.ResidueField q.ResidueField Λ).symm)
    have hfg := IntermediateField.fg_top p.ResidueField q.ResidueField
    have : IsRegularRing (q.ResidueField ⊗[p.ResidueField] p.Fiber Λ) :=
      Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular hp q.ResidueField hfg
    have : IsRegularRing (q.Fiber (Λ ⊗[R] R')) :=
      IsRegularRing.of_ringEquiv e.symm.toRingEquiv
    refine ⟨inferInstance, ?_⟩
    intro K _ _ _ _
    let : Algebra p.ResidueField K :=
      (algebraMap q.ResidueField K).comp (algebraMap p.ResidueField q.ResidueField)
        |>.toAlgebra
    have : IsScalarTower p.ResidueField q.ResidueField K :=
      IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    have : Algebra.EssFiniteType p.ResidueField q.ResidueField := inferInstance
    have : Algebra.EssFiniteType p.ResidueField K :=
      Algebra.EssFiniteType.comp p.ResidueField q.ResidueField K
    have : IsRegularRing (K ⊗[p.ResidueField] p.Fiber Λ) :=
      Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular hp K
        (IntermediateField.fg_top p.ResidueField K)
    exact IsRegularRing.of_ringEquiv
      ((Algebra.TensorProduct.congr (.refl : K ≃ₐ[K] K) e).trans
        (Algebra.TensorProduct.cancelBaseChange p.ResidueField q.ResidueField
          K K (p.Fiber Λ))).symm.toRingEquiv

end RingHom
