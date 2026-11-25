/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.FieldTheory.Separable
import WeilConjectures.FieldTheory.SeparableTensorPurelyInseparable
import WeilConjectures.RingTheory.GeometricRegularitySubfields
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import WeilConjectures.RingTheory.GeometricallyRegularSmoothAscent
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import WeilConjectures.Mathlib.RingTheory.Etale.Field

@[expose] public section

universe u v w

namespace Algebra

private theorem finite_separable_ascent
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [Module.Finite k k']
    (hR : IsGeometricallyRegular k R) : IsGeometricallyRegular k' R := by
  have : IsRegularRing (TensorProduct k k' R) :=
    isRegularRing_tensorProduct_of_isGeometricallyRegular hR k'
      (IntermediateField.fg_top k k')
  have hB : IsGeometricallyRegular k' (TensorProduct k k' R) := by
    refine ⟨inferInstance, ?_⟩
    intro L _ _ _ _
    let : Algebra k L := ((algebraMap k' L).comp (algebraMap k k')).toAlgebra
    have : IsScalarTower k k' L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : Module.Finite k L := Module.Finite.trans k' L
    have : IsRegularRing (TensorProduct k L R) :=
      isRegularRing_tensorProduct_of_isGeometricallyRegular hR L
        (IntermediateField.fg_top k L)
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange k k' k' L R).symm.toRingEquiv
  let φ : (TensorProduct k k' R) →ₐ[k'] R :=
    Algebra.TensorProduct.lift (Algebra.ofId k' R) (AlgHom.id k R)
      (fun _ _ ↦ Commute.all _ _)
  let : Algebra R (TensorProduct k k' R) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (TensorProduct k k' R) R := φ.toRingHom.toAlgebra
  have : IsScalarTower R (TensorProduct k k' R) R :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change r = φ (TensorProduct.tmul k 1 r)
      simp [φ]
  have : Algebra.Etale k k' := Algebra.Etale.of_finite_of_isSeparable
  have : Algebra.Etale R (TensorProduct k k' R) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight k R k')
  have : Algebra.Etale (TensorProduct k k' R) R :=
    Algebra.Etale.of_restrictScalars R (TensorProduct k k' R) R
  exact (isGeometricallyRegular_of_smooth φ inferInstance hB.1 hB).2

/-- Forward ascent along a separable algebraic extension. The proof follows the finite
intermediate-field reduction, smooth multiplication base change, and smooth ascent in
Stacks Project, Lemma 07QH.
(blueprint: lem-weil-pbc-geometric-regularity-separable-extension-forward) -/
theorem isGeometricallyRegular_of_isSeparable
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [IsNoetherianRing R] :
    IsGeometricallyRegular k R → IsGeometricallyRegular k' R := by
  intro hR
  let I := {E : IntermediateField k k' // Module.Finite k E}
  have : Nonempty I := ⟨⟨⊥, inferInstance⟩⟩
  let K : I → Subfield k' := fun E ↦ E.val.toSubfield
  apply geometricallyRegular_of_directed_subfields k' I K ?_ ?_ R inferInstance
  · intro E
    have : Module.Finite k E.val := E.property
    exact finite_separable_ascent k E.val R hR
  · intro E F
    have : Module.Finite k E.val := E.property
    have : Module.Finite k F.val := F.property
    refine ⟨⟨E.val ⊔ F.val, inferInstance⟩, ?_, ?_⟩
    · change E.val ≤ E.val ⊔ F.val
      exact le_sup_left
    · change F.val ≤ E.val ⊔ F.val
      exact le_sup_right
  · intro x
    have : Module.Finite k (IntermediateField.adjoin k {x}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral k x)
    exact ⟨⟨IntermediateField.adjoin k {x}, inferInstance⟩,
      IntermediateField.subset_adjoin k {x} (by simp)⟩

/-- Descent along a separable algebraic extension. The proof tensors finite purely inseparable
extensions with the separable extension and uses cancellation, as in Stacks Project,
Lemma 07QH. (blueprint: lem-weil-pbc-geometric-regularity-separable-extension-backward) -/
theorem isGeometricallyRegular_of_isSeparable_rev
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [IsNoetherianRing R] :
    IsGeometricallyRegular k' R → IsGeometricallyRegular k R := by
  intro hR
  refine ⟨inferInstance, ?_⟩
  intro L _ _ _ _
  obtain ⟨hfield, _, hfinite, _⟩ := separableTensor_purelyInseparable_isField k k' L
  let : Field (TensorProduct k k' L) := hfield.toField
  have : Module.Finite k' (TensorProduct k k' L) := hfinite
  have : IsRegularRing (TensorProduct k' (TensorProduct k k' L) R) :=
    isRegularRing_tensorProduct_of_isGeometricallyRegular hR (TensorProduct k k' L)
      (IntermediateField.fg_top k' (TensorProduct k k' L))
  let e := (Algebra.TensorProduct.comm k' (TensorProduct k k' L) R).trans
    (Algebra.TensorProduct.cancelBaseChange k k' k' R L)
  exact IsRegularRing.of_ringEquiv
    (e.toRingEquiv.trans (Algebra.TensorProduct.comm k R L).toRingEquiv)

/-- Geometric regularity of a Noetherian algebra is unchanged when its base field is replaced
by a separable algebraic extension over which the algebra is already defined.
Source: Stacks Project, Algebra, Lemma 07QH and Definition 0382
(blueprint: lem-weil-pbc-geometric-regularity-separable-extension).
-/
theorem isGeometricallyRegular_iff_of_isSeparable
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [IsNoetherianRing R] :
    IsGeometricallyRegular k R ↔ IsGeometricallyRegular k' R := by
  constructor
  · exact isGeometricallyRegular_of_isSeparable k k' R
  · exact isGeometricallyRegular_of_isSeparable_rev k k' R


end Algebra
