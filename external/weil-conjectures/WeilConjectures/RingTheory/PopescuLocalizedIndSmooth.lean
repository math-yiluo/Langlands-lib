/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.Algebra
import WeilConjectures.RingTheory.TotalFractionFiberDecomposition
import WeilConjectures.RingTheory.IndSmoothFiniteProductTransport

/-! # Ind-smoothness over a total fraction ring
Source: Stacks Project, Smoothing Ring Maps, Tag 07F5, third paragraph.
-/

@[expose] public section
open CategoryTheory
open scoped nonZeroDivisors
universe u v

-- Over a field the only fibre is the original algebra, up to its canonical isomorphism.
private theorem regular_of_geometricallyRegular
    (k : Type u) (A : Type (max u v)) [Field k] [CommRing A] [Algebra k A]
    (hA : Algebra.IsGeometricallyRegular k A) :
    RingHom.IsRegular (algebraMap k A) := by
  rw [RingHom.IsRegular, toAlgebra_algebraMap]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, ?_⟩
  intro p hp
  let K := p.ResidueField
  let e : k ≃ₐ[k] K := p.algEquivResidueFieldOfField
  let eA : A ≃ₐ[k] p.Fiber A :=
    (Algebra.TensorProduct.lid k A).symm.trans
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[k] A))
  let : IsNoetherianRing A := hA.1
  refine ⟨isNoetherianRing_of_ringEquiv A eA.toRingEquiv, ?_⟩
  intro L _ _ _ _
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite k K :=
    Module.Finite.of_surjective (Algebra.linearMap k K) e.surjective
  have : Module.Finite k L := Module.Finite.trans K L
  have : IsPurelyInseparable k K := e.isPurelyInseparable
  have : IsPurelyInseparable k L := IsPurelyInseparable.trans k K L
  have : IsRegularRing (TensorProduct k L A) := hA.2 L
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange k K L L A).symm.toRingEquiv

/-- The total-fraction localization inherits an ind-smooth presentation from the field case.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F5, third paragraph.
(blueprint: lem-weil-pbc-popescu-standard-nonzerodivisor-aux-localized-ind).

Proof: A reduced Noetherian ring has finitely many minimal primes. Its total fraction
ring is canonically the product of the localizations at these primes, which are fields
and canonically their residue fields, by reduced_noetherian_total_ring_fractions.
Tensoring this compatible product decomposition with Λ identifies its localization
with the product of the corresponding fibre rings. Localization is base change and
tensor products distribute over finite products. Regularity makes each fibre
Noetherian and geometrically regular. A map from its residue field to the fibre is
flat, and its only fibre is the same algebra, so it is regular. Apply the assumed
field case to each factor. Induct on the number of factors using ind_smooth_prod,
then transport the resulting colimit presentation along the two compatible ring
isomorphisms. Nontriviality ensures there is a minimal prime, so the finite product
is nonempty. The fields have universe u, the fibres and all diagram terms have
universe max u v, and the transported presentation retains this universe. -/
theorem localized_target_is_ind_smooth
    (h : ∀ (k : Type u) (Λ : Type (max u v)) [Field k] [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap k Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} k ↦ Algebra.Smooth k B)
          (CommAlgCat.of k Λ))
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] [Nontrivial R] [IsReduced R]
    (hreg : RingHom.IsRegular (algebraMap R Λ)) :
    ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} (Localization R⁰) ↦
        Algebra.Smooth (Localization R⁰) B)
      (CommAlgCat.of (Localization R⁰)
        (Localization (Algebra.algebraMapSubmonoid Λ R⁰))) := by
  obtain ⟨n, q, e, f, hcompat⟩ := total_fraction_fiber_decomposition R Λ
  apply Algebra.ind_smooth_of_finite_product (Localization R⁰)
    (Localization (Algebra.algebraMapSubmonoid Λ R⁰)) n
    (fun i ↦ (q i).val.asIdeal.ResidueField) (fun i ↦ (q i).val.asIdeal.Fiber Λ)
    e f hcompat
  intro i
  let p := (q i).val.asIdeal
  have hgeom : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber Λ) := by
    rw [RingHom.IsRegular, toAlgebra_algebraMap] at hreg
    exact hreg.2 p
  let : IsNoetherianRing (p.Fiber Λ) := hgeom.1
  exact h p.ResidueField (p.Fiber Λ)
    (regular_of_geometricallyRegular p.ResidueField (p.Fiber Λ) hgeom)
