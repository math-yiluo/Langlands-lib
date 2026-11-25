/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import all WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism

/-! # Finite scalar realization from the étale site

Source: blueprint scalar-six-ctf (1), finite coefficient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- Exact étale inverse image, the existing constant-ring realization, and restriction
along the given condensed coefficient isomorphism. All three functors are specified
constructions; no constructible preimage is chosen in this definition.
Source: blueprint scalar-six-ctf (1), finite discrete comparison and transport along e. -/
abbrev finiteScalarRealization (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1} A) T ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X T) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory ⋙
    (finiteComparisonRealization A T eR).mapDerivedCategory ⋙
      shriekCoefficientTransport e.symm T

end AlgebraicGeometry.ProEtale.CondensedRing
