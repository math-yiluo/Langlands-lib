/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.TraceFormula.Specialization.Defect
public import WeilConjectures.TraceFormula.Specialization.DeformationModelFactor
public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.TraitModelInstances

/-!

# The defect of a bounded constructible complex is bounded constructible

The defect `C_{X,Z}(L)` of `ProEtale.CondensedRing.specializationDefect` is a cone of the
zero-section map `ε_{X,Z}(L) : Le^* Sp_{X,Z}(L) ⟶ Ψ_{Z × S}(Li^* L)`. Both sides are bounded
constructible when `L` is, by Deligne's finiteness theorem for nearby cycles, so the defect is
bounded constructible (`ProEtale.CondensedRing.boundedConstructible_specializationDefect`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (I : X.left.IdealSheafData)

/-- The defect `C_{X,Z}(L)` of a bounded constructible complex `L` is bounded constructible. -/
theorem boundedConstructible_specializationDefect
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (deformationSpecialFibre (centre X I) ⊥ k').left)
      (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  set Λ := Profinite.padicAlgClRingObj ℓ
  obtain ⟨g, h, hT⟩ := exists_distTriang_specializationDefect X I k' Λ L.obj
  have h₁ := boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ
    (zeroSectionSpecialFibreMap X I k').left
    _ ((deformationModel X I k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X I k') (deformationModel_exists_comp_ε X I k')
      L.obj L.property)
  have h₂ := (deformationModel (centre X I) ⊥ k').preservesBoundedConstructible_of_isTraitModel
    (isTraitModel_deformationModel (centre X I) ⊥ k')
    (deformationModel_exists_comp_ε (centre X I) ⊥ k') _
    (boundedConstructible_leftDerivedUpperStar_obj Λ ℓ (centreι X I) L)
  have : TopologicalSpace.NoetherianSpace (deformationSpecialFibre (centre X I) ⊥ k').left :=
    inferInstance
  exact (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT h₁ h₂

end AlgebraicGeometry.ProEtale.CondensedRing
