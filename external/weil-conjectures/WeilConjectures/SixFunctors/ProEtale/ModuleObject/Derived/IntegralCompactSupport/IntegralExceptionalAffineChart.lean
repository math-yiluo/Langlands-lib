/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralExceptionalAffineFactorization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralRestrictionLine
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralRestrictionClosed

/-!
# Constructibility on one affine chart of the integral Brown adjoint

Source: blueprint main-20261015, sk-thm-int-restriction, General f paragraph,
and sk-thm-int-restriction-glue.proof.md, paragraph (2).
(blueprint: lem-sfb-integral-exceptional-affine-chart).
-/

@[expose] public section
set_option linter.privateModule false

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable {X Y : Scheme.{u}}

private theorem finiteConstantLocalModel_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ T M) :
    HasFiniteConstantLocalModel Λ T N := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC a
  exact ⟨P, hP, ⟨((upperStar Λ (C.f a)).mapIso e).symm ≪≫ eP⟩⟩

private theorem finiteConstantStratified_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ T M) :
    IsFiniteConstantStratified Λ T N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_iso Λ (S.domain a)
    ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private theorem constantModelConstructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ T M) :
    IsConstantModelConstructible Λ T N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hT
  · exact finiteConstantStratified_of_iso Λ T e hM
  · intro U hU
    exact finiteConstantStratified_of_iso Λ U.toScheme
      ((upperStar Λ U.ι).mapIso e) (hM U hU)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
