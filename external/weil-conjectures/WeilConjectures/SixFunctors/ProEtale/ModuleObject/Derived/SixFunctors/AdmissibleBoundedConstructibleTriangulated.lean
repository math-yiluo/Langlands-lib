/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import Mathlib.AlgebraicGeometry.Noetherian

set_option linter.privateModule false

/-! # Triangulated bounded constructibility

Source: current blueprint, internal-Hom stability proof, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj ZeroObject
namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace AdmissibleTriangulated

private instance pointMod_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : ((upperStarFromPoint X).mapMod Λ).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts ((upperStarFromPoint X).mapMod Λ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

-- Zero is represented by the rank-zero presentation on the identity cover.
private theorem localModel_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

private theorem constructible_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : IsConstantModelConstructible Λ X (0 : Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  have hstrat (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
      (hM : IsZero M) : IsFiniteConstantStratified Λ T M := by
    refine ⟨Scheme.Stratification.trivial T, fun a ↦ ?_⟩
    exact localModel_zero Λ _ _ ((upperStar Λ _).map_isZero hM)
  classical
  unfold IsConstantModelConstructible
  split
  · exact hstrat X _ (isZero_zero _)
  · exact fun U _ ↦ hstrat _ _ ((upperStar Λ U.ι).map_isZero (isZero_zero _))

-- Apply the weak Serre cohomology theorem to this precise constructibility predicate.
private theorem triangulated_of_serre
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (hk : ∀ M N, ∀ f : M ⟶ N, IsConstantModelConstructible Λ X M →
      IsConstantModelConstructible Λ X N →
      IsConstantModelConstructible Λ X (kernel f) ∧
      IsConstantModelConstructible Λ X (cokernel f))
    (he : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)), S.ShortExact → IsConstantModelConstructible Λ X S.X₁ →
      IsConstantModelConstructible Λ X S.X₃ → IsConstantModelConstructible Λ X S.X₂) :
    (constantModelBoundedConstructible Λ X).IsTriangulated := by
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  have : P.ContainsZero := ⟨0, isZero_zero _, constructible_zero Λ X⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hlim, hFG⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hlim)
      (hk _ _ f hFG.1 hFG.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hlim, hFG⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hlim)
      (hk _ _ f hFG.1 hFG.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun hS h1 h3 ↦ he _ hS h1 h3⟩
  have : (DerivedCategory.homologyProperty P).IsTriangulated :=
    (cohomology_in_weak_serre_subcategory P).1
  change (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
    ).IsTriangulated
  infer_instance

-- Cover index universes are the only difference between these fixed-scalar predicates.
/-- Lifting a finite discrete coefficient carrier preserves its condensed ring object. -/
private theorem finiteCoefficientLiftIso (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A))) := by
  let ei : A ≃+* ULift.{u} A := ULift.ringEquiv.symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨Mon.mkIso ea⟩

end AdmissibleTriangulated

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
