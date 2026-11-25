/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PoincareDuality.ModuleObjectProjectionMorphism
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import all WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperHeartUniformBound

set_option linter.privateModule false

/-! Proper direct-image input to the exceptional projection formula. -/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

set_option Elab.async false

universe u

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

attribute [local irreducible] upperStarFromPoint moduleObjectProjectionMap derivedTensor
  DerivedCategory HasDerivedCategory.standard

private theorem field_realization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} E) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} F)) := by
  obtain ⟨F, σ, hσ⟩ := field_model ℓ E
  have hσi : Isometry σ.symm := fun x y ↦ by
    simpa only [σ.apply_symm_apply] using (hσ (σ.symm x) (σ.symm y)).symm
  exact ⟨F, ⟨continuousIso σ.toRingEquiv hσ.continuous hσi.continuous⟩⟩

private structure BoundedProjectionFormula
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  property : ∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))),
    boundedConstructible (condensedRingObj R X) K →
    boundedConstructible (condensedRingObj R Y) M →
    IsIso (moduleObjectProjectionMap R f K M)

private def HasProjectionModel
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1},
    ∃ mS : MonObj S, letI := mS
      ∃ hS : IsCommMonObj S, letI := hS
        Nonempty (Mon.mk R ≅ Mon.mk S) ∧ BoundedProjectionFormula S f

private theorem projection_from_model
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) (hm : HasProjectionModel R p.left)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj R X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj R Y.left)))
    (hK : boundedConstructible (condensedRingObj R X.left) K)
    (hM : boundedConstructible (condensedRingObj R Y.left) M) :
    IsIso (moduleObjectProjectionMap R p.left K M) := by
  obtain ⟨S, mS, hS, ⟨e⟩, hf⟩ := hm
  let := mS
  let := hS
  have hK' := bounded_scalar e X.left K hK
  have hM' := bounded_scalar e Y.left M hM
  have hi := hf.property ((internalScalarExtension e.hom.hom X.left).obj K)
    ((internalScalarExtension e.hom.hom Y.left).obj M) hK' hM'
  exact projection_isIso_of_coefficientIso (R := R) (S := S)
    e.hom.hom ℓ k p K M hi

private theorem model_transport
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] {X Y : Scheme.{u}} {p : X ⟶ Y}
    (e : Mon.mk R ≅ Mon.mk S) (h : HasProjectionModel S p) :
    HasProjectionModel R p := by
  obtain ⟨T, mT, hT, ⟨eT⟩, hf⟩ := h
  exact ⟨T, mT, hT, ⟨e ≪≫ eT⟩, hf⟩

private theorem integral_formula
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (hPX : ∀ K, boundedConstructible
      (condensedRingObj (DerivedNakayama.integerRing ℓ E) X) K →
        constantModelBoundedConstructible (DerivedNakayama.integerRing ℓ E) X K)
    (hPY : ∀ K, boundedConstructible
      (condensedRingObj (DerivedNakayama.integerRing ℓ E) Y) K →
        constantModelBoundedConstructible (DerivedNakayama.integerRing ℓ E) Y K) :
    HasProjectionModel (DerivedNakayama.integerRing ℓ E) p := by
  refine ⟨DerivedNakayama.integerRing ℓ E, (by infer_instance), (by infer_instance),
    ⟨Iso.refl _⟩, ?_⟩
  constructor
  intro A B hA hB
  exact (integralProperDirectImageAndFormulas ℓ E k p).2.2.2 A B
    (hPX A hA) (hPY B hB)

private theorem unitBall_model
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    HasProjectionModel (Profinite.continuousMapRingObj.{u} O) p.left := by
  obtain ⟨F, ⟨e⟩⟩ := unitBall_realization.{u} ℓ E O hO
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : p.left.IsOver (Spec (.of k)) := ⟨Over.w p⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    (inferInstance : LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (.of k)) := (inferInstance : QuasiCompact X.hom)
  let : IsSeparated (X.left ↘ Spec (.of k)) := (inferInstance : IsSeparated X.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    (inferInstance : LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := (inferInstance : QuasiCompact Y.hom)
  let : IsSeparated (Y.left ↘ Spec (.of k)) := (inferInstance : IsSeparated Y.hom)
  exact model_transport (e ≪≫ integerIso ℓ F)
    (integral_formula ℓ (ULift.{u} F.val) k p.left
      (integer_predicate ℓ F X.left) (integer_predicate ℓ F Y.left))

private theorem integral_model
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    HasProjectionModel (Profinite.padicIntegersRingObj.{u} ℓ E) p.left := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E := ⟨fun a x ↦ by
    change ‖algebraMap E (PadicAlgCl ℓ) (a • x)‖ ≤
      ‖a‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
      PadicAlgCl.norm_extends]⟩
  have hO (x : E) : x ∈ PadicAlgCl.integers ℓ E ↔ ‖x‖ ≤ 1 := by
    rw [PadicAlgCl.mem_integers_iff]
    change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
  exact unitBall_model ℓ E (PadicAlgCl.integers ℓ E).toSubring hO k p

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

include k in
private theorem projection_bounded (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (p : X ⟶ Y) [IsProper p.left]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) Y.left)))
    (hA : boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X.left) A)
    (hM : boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) Y.left) M) :
    IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj.{u} ℓ E) p.left A M) := by
  exact projection_from_model ℓ k p (integral_model ℓ E k p) A M hA hM

namespace ContinuousMapRingObj

end ContinuousMapRingObj

namespace PadicIntegersRingObj

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
