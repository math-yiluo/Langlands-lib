/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.Ring.Colimits

import WeilConjectures.RingTheory.TensorModelAlgebraDescent
import WeilConjectures.RingTheory.CompatibleModuleModelDescent

/-! # Comparing a finite-presentation module model with prescribed stages

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph.
(blueprint: lem-pc-fp-module-tensor-model-comparison)
-/

@[expose] public section

universe v w x

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finitely presented algebra and module model agrees with all sufficiently late stages.
No flatness of the model or of the limit is assumed.

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph; Tags 00QO, 05N9 and 05N7.
(blueprint: lem-pc-fp-module-tensor-model-comparison)

Proof:
1. Restrict to the cofinal tail above i. If needed, pass to its poset reflection:
   indices mutually below each other have inverse transition maps, so the diagram
   descends up to these canonical isomorphisms, with the same colimit. A stage in
   the reflection is represented by an original index; transport its comparisons
   back and extend them to all later original indices. Tensor products commute
   with the ring colimit, giving the A, B and compatible module colimits.
2. Finite presentation of P over the integers factors its map into the limit A algebra
   through one A stage. Above that stage regard all A stages as P-algebras.
3. The right inclusion followed by e gives a P-algebra map Q into the limit B algebra.
   Finite presentation of Q factors it through a B stage. Tensoring gives the comparison
   A_j tensor_P Q to B_j, compatible with the A_j-action by the left-inclusion identity.
4. The comparison is an isomorphism at the limit. Both algebras are finitely presented
   over A_j. Descend its inverse by Tag 05N9 (2) and descend both inverse identities
   by Tag 05N9 (3), taking a common later stage. Every later comparison is an isomorphism.
5. At that stage the model L and the prescribed M give two finitely presented modules
   over B_j. The specified limit linear equivalence identifies their limit base changes.
   Descend it and its inverse by Tag 05N7, then descend both inverse identities on finite
   generators. At a common later stage the descended maps are mutually inverse.
6. Extend these isomorphisms to every later stage. Tensor associativity and the algebra
   comparison identify B_j tensor_Q L with A_j tensor_P L and the prescribed base-change
   module with A_j tensor_A M. Restrict scalars to A_j to obtain the displayed equivalence.
   No flatness enters any step. Zero modules, zero rings, and empty presentations are
   allowed; a common upper bound is used for every finite collection of indices.
-/
theorem exists_eventually_tensor_model_equiv
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    {i : I} {A B M : Type w}
    [CommRing A] [CommRing B] [AddCommMonoid M]
    [Algebra (F.obj i : Type v) A] [Algebra (F.obj i : Type v) B]
    [Algebra.FinitePresentation (F.obj i : Type v) A]
    [Algebra.FinitePresentation (F.obj i : Type v) B]
    [Module B M] [Module.FinitePresentation B M] (f : A →ₐ[F.obj i] B)
    (P Q L : Type x) [CommRing P] [CommRing Q] [Algebra P Q]
    [AddCommMonoid L] [Module Q L]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    [Module.FinitePresentation Q L]
    (aP : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      Algebra P ((c.pt : Type v) ⊗[F.obj i] A))
    (e : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      ((c.pt : Type v) ⊗[F.obj i] A) ⊗[P] Q ≃+* (c.pt : Type v) ⊗[F.obj i] B)
    (he : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
        (Algebra.TensorProduct.map (Algebra.ofId (c.pt : Type v) (c.pt : Type v))
          f).toRingHom)
    (eM : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      letI : Algebra Q ((c.pt : Type v) ⊗[F.obj i] B) :=
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
      letI : Algebra B ((c.pt : Type v) ⊗[F.obj i] B) :=
        Algebra.TensorProduct.rightAlgebra
      Nonempty (((c.pt : Type v) ⊗[F.obj i] B) ⊗[Q] L ≃ₗ[
        (c.pt : Type v) ⊗[F.obj i] B] ((c.pt : Type v) ⊗[F.obj i] B) ⊗[B] M)) :
    letI : Module A M := Module.compHom M f.toRingHom
    letI : Module P L := Module.compHom L (algebraMap P Q)
    ∃ j₀ : I, i ≤ j₀ ∧ ∀ (j : I) (h₀ : i ≤ j₀) (h₁ : j₀ ≤ j),
      letI := (F.map (homOfLE (h₀.trans h₁))).hom.toAlgebra
      letI : Algebra A ((F.obj j : Type v) ⊗[F.obj i] A) :=
        Algebra.TensorProduct.rightAlgebra
      ∃ aPj : Algebra P ((F.obj j : Type v) ⊗[F.obj i] A),
        letI := aPj
        Nonempty (((F.obj j : Type v) ⊗[F.obj i] A) ⊗[P] L ≃ₗ[
          (F.obj j : Type v) ⊗[F.obj i] A] ((F.obj j : Type v) ⊗[F.obj i] A) ⊗[A] M) := by
  classical
  let : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
  let : Algebra P ((c.pt : Type v) ⊗[F.obj i] A) := aP
  obtain ⟨k, hik, q, hqC, hq, aPk, -, hmodel⟩ :=
    exists_tensor_model_algebra_tail F c hc f P Q aP e he
  obtain ⟨j₀, hkj₀, hmodules⟩ :=
    exists_eventually_compatible_module_equiv F c hc Q L
      (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
      eM k hik q hqC hq
  let : Module A M := Module.compHom M f.toRingHom
  let : Module P L := Module.compHom L (algebraMap P Q)
  refine ⟨j₀, hik.trans hkj₀, ?_⟩
  intro j h₀ h₁
  let hkj : k ≤ j := hkj₀.trans h₁
  let : Algebra (F.obj i : Type v) (F.obj j : Type v) :=
    (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
  let D := (F.obj j : Type v) ⊗[F.obj i] A
  let E := (F.obj j : Type v) ⊗[F.obj i] B
  let d : D →+* E :=
    (Algebra.TensorProduct.map (AlgHom.id (F.obj j) (F.obj j)) f).toRingHom
  let : Algebra D E := d.toAlgebra
  let : Algebra Q E := (q j hkj).toAlgebra
  obtain ⟨hPQ, hpush⟩ := hmodel j hkj
  let : Algebra (F.obj i : Type v) (F.obj k : Type v) := (F.map (homOfLE hik)).hom.toAlgebra
  let tkj : F.obj k →ₐ[F.obj i] F.obj j :=
    { (F.map (homOfLE hkj)).hom with
      commutes' := fun s ↦ (ConcreteCategory.congr_hom
        (F.map_comp (homOfLE hik) (homOfLE hkj)) s).symm }
  let aPj : Algebra P D :=
    ((Algebra.TensorProduct.map tkj (AlgHom.id (F.obj i) A)).toRingHom.comp
      (@algebraMap P ((F.obj k : Type v) ⊗[F.obj i] A) _ _ aPk)).toAlgebra
  let : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
  let : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower P Q E := hPQ
  let : Algebra.IsPushout P D Q E := hpush
  let : Algebra A D := Algebra.TensorProduct.rightAlgebra
  refine ⟨aPj, ?_⟩
  obtain ⟨u⟩ := hmodules j hkj₀ h₁
  let : IsScalarTower P Q L := IsScalarTower.of_compHom P Q L
  let : Algebra B E := Algebra.TensorProduct.rightAlgebra
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra A E :=
    (Algebra.TensorProduct.includeRight.toRingHom.comp f.toRingHom).toAlgebra
  let : IsScalarTower A B E := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  let : IsScalarTower A D E := .of_algebraMap_eq fun a ↦ by
    change (1 : F.obj j) ⊗ₜ[F.obj i] f a = _
    rfl
  let : IsScalarTower (F.obj i) A B :=
    .of_algebraMap_eq fun s ↦ (f.commutes s).symm
  let : IsScalarTower (F.obj j) D E := .of_algebraMap_eq fun a ↦ by
    change a ⊗ₜ[F.obj i] (1 : B) = a ⊗ₜ[F.obj i] f 1
    rw [map_one]
  let : IsScalarTower (F.obj i) D E := .of_algebraMap_eq fun a ↦ by
    change (algebraMap (F.obj i) (F.obj j) a) ⊗ₜ[F.obj i] (1 : B) =
      (algebraMap (F.obj i) (F.obj j) a) ⊗ₜ[F.obj i] f 1
    rw [map_one]
  let : Algebra.IsPushout (F.obj i) A (F.obj j) D := inferInstance
  let : Algebra.IsPushout (F.obj i) B (F.obj j) E := inferInstance
  have hAB : Algebra.IsPushout A B D E :=
    (Algebra.IsPushout.comp_iff (F.obj i) A (F.obj j) D (T := B) (T' := E)).mp
      inferInstance
  let : Algebra.IsPushout A D B E := hAB.symm
  let : AddCommGroup L := Module.addCommMonoidToAddCommGroup Q
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup B
  exact ⟨(Algebra.IsPushout.cancelBaseChange P D Q E L).symm.trans
    ((u.restrictScalars D).trans (Algebra.IsPushout.cancelBaseChange A D B E M))⟩

end AlgebraicGeometry
