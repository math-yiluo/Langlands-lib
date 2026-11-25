/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolutionAlgebraic
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! The sectionwise realization of an ordinary finite point resolution. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A specified ordinary resolution realizes as a short exact point-module resolution.

Source: the sectionwise finite-discrete quotient argument in the scalar-six direct-image proof
(blueprint: lem-s3-integral-finite-point-resolution-continuous).

The maps are applied to continuous sections. Injectivity and middle exactness lift through the
continuous inverse on the image of the matrix map, while surjectivity uses the finite discrete
fibres of the target. The resulting module objects are identified with finite biproducts of
regular modules and with the actual restricted regular target. -/
theorem integralFinitePointResolution_continuous
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (A : Type u) [CommRing A] [Finite A]
    (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
      ⟨cartesianFinitePointRing A⟩) :
    letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : IsTopologicalRing A := inferInstance
    ∀ (φ : PadicAlgCl.integers ell E.1 →+* A),
      @Continuous _ _ inferInstance ⊥ φ →
      (∀ (P : Profinite.{u})
        (s : ULift.{u + 1} C(P, PadicAlgCl.integers ell E.1)) (x : P),
        ((a.hom.hom.hom.app (op P)) s).down x = φ (s.down x)) →
      letI : Module (PadicAlgCl.integers ell E.1) A := Module.compHom A φ
      let φ' : PadicAlgCl.integers ell E.1 →+* ULift.{u + 1} A :=
        ULift.ringEquiv.symm.toRingHom.comp φ
      letI : Module (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A) :=
        Module.compHom (ULift.{u + 1} A) φ'
      ∀ (r : ℕ)
        (f : ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (Fin r →
          ULift.{u + 1} (PadicAlgCl.integers ell E.1)) ⟶
          ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (Fin r →
            ULift.{u + 1} (PadicAlgCl.integers ell E.1)))
        (g : ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (Fin r →
          ULift.{u + 1} (PadicAlgCl.integers ell E.1)) ⟶
          ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A)),
        Function.Injective f.hom → Function.Exact f.hom g.hom →
          Function.Surjective g.hom →
          ∃ (P : ShortComplex (IntegralFiniteScalar.PointModules
              (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}))),
            P.ShortExact ∧
            Nonempty (P.X₁ ≅ biproduct
              (fun _ : Fin r ↦ Mod.regular (Profinite.padicIntegersRingObj ell E.1))) ∧
            Nonempty (P.X₂ ≅ biproduct
              (fun _ : Fin r ↦ Mod.regular (Profinite.padicIntegersRingObj ell E.1))) ∧
            Nonempty (P.X₃ ≅ (Mod.comap a.hom.hom).obj
              (Mod.regular (cartesianFinitePointRing A))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
