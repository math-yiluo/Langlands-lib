/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.IntegralPointThickening
public import WeilConjectures.TraceFormula.Specialization.ComponentClass
public import WeilConjectures.TraceFormula.Specialization.SpecialFixedLocus
public import WeilConjectures.TraceFormula.Specialization.TraitSpecializationFaithful

/-!

# The trace specialization of the deformation to the normal cone

Let `c = (c₁, c₂) : C ⟶ X × X` be contracting at the `k`-point `y` of its support, with
`x = c₁(y) = c₂(y)`, let `k'` be a separably closed extension of `k`, and let `c'` be the
specialized correspondence on the normal cones over `k'`, with fixed locus `F'`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specialCorrespondence`). Given
compact-support exchanges
```
ν_c : Rc'_! Ψ_C ⟶ Ψ_{X×X} Rc_!,     ν_X : Ra_{X'!} Ψ_X ⟶ Ψ_s Ra_{X!}
```
of the nearby cycles of the deformations to the normal cones (blueprint `prose-E-15`),
the specialization data of blueprint `proposition-specialization-trace-class`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.deformationTraceSpecialization`) has the
nearby cycles of the deformations as specialization functors, the specialization unit of the
support, the proper exchange `χ_Δ` of the diagonal, the exceptional exchange `β_c`, the mate of
`ν_c`, and the dualizing map `θ_X` of `ν_X`; the data of the fixed locus are determined by these
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofSupportExchange`).

Let `B` be an open and closed subscheme of the fixed locus `F`, proper over `k`, with underlying set
`{y}`. If the exchange `ν_F` of the fixed locus maps the specialization of the unit class of the
(proper, one-point) fixed locus `F'` to the class of `B`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.SpecializesComponentClass`), then the
specialization of Borel–Moore sections is injective on `B`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.restrict_eq_zero_of_sp_eq_zero`): the
integral over `F'` of `sp(z)` is the specialization of the integral of `z` over `B`, the
specialization is injective on `End(ℚ̄_ℓ)` and the integral is injective on the thickened point `B`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] isIso_traitSpecializationUnit

namespace Correspondence

namespace IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

variable (ℓ) (X) in
/-- The proper exchange `χ_Δ : Ψ_{X×X} RΔ_* ⟶ RΔ'_* Ψ_X` of the diagonal of the deformation to the
normal cone of a rational point `x`. -/
noncomputable def diagPushforwardExchange (x : RationalPoint X) :
    boundedConstructibleLowerStar ℓ (diag X) ⋙
        specializationProd k' x ⟶
      specialization k' x ⋙ boundedConstructibleLowerStar ℓ
        (diag (deformationSpecialFibre X x.left.ker k')) :=
  (deformationDiagModelHom X x.left.ker k').boundedConstructiblePushforwardExchange ℓ
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k'))
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))

/-- The specialization unit `σ_C : ℚ̄_ℓ ⟶ Ψ_C ℚ̄_ℓ` of the deformation of the support to the normal
cone of `y`. -/
noncomputable def supportSpecializationUnit :
    𝟙_ _ ⟶ (specialization (ℓ := ℓ) k' y).obj (𝟙_ _) :=
  NearbyCyclesModel.boundedConstructibleUnit ℓ
    ((deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel c.C y.left.ker k')
      (deformationModel_exists_comp_ε c.C y.left.ker k'))

/-- A compact-support exchange `ν_c : Rc'_! Ψ_C ⟶ Ψ_{X×X} Rc_!` for the support maps of `c` and of
the specialized correspondence. -/
abbrev SupportCompactSupportExchange :=
  specialization (ℓ := ℓ) k' y ⋙
      boundedConstructibleLowerShriek ℓ
        (hc.specialCorrespondence k').support ⟶
    boundedConstructibleLowerShriek ℓ c.support ⋙
      specializationProd k' (y ≫ c.c₁)

variable (X) in
/-- A compact-support exchange `ν_X : Ra_{X'!} Ψ_X ⟶ Ψ_s Ra_{X!}` for the structure maps of `X` and
of the special fibre `X'` of its deformation to the normal cone of a rational point `x`. -/
abbrev PointCompactSupportExchange (x : RationalPoint X) :=
  specialization (ℓ := ℓ) k' x ⋙
      boundedConstructibleLowerShriek ℓ
        (toPoint (deformationSpecialFibre X x.left.ker k')) ⟶
    boundedConstructibleLowerShriek ℓ (toPoint X) ⋙
      traitSpecialization k k'

variable (νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k')
  (νX : PointCompactSupportExchange (ℓ := ℓ) X k' (y ≫ c.c₁)) (F : c.FixedLocus)

/-- **The trace specialization of the deformation to the normal cone** (blueprint
`proposition-specialization-trace-class`): the specialization data from `c` to the specialized
correspondence `c'` with the nearby cycles of the deformations to the normal cones
`Ψ_C = specialization k' y`, `Ψ_X = specialization k' x`, `Ψ_{X×X} = specializationProd k' x`, the
specialization unit of the support, the proper exchange of the diagonal, the exceptional exchange
`β_c` of `ν_c` and the dualizing map `θ_X` of `ν_X`
(`TraceSpecialization.ofSupportExchange`). -/
noncomputable def deformationTraceSpecialization :
    c.TraceSpecialization F (hc.specialCorrespondence k') (hc.specialFixedLocus k') :=
  TraceSpecialization.ofSupportExchange (specialization (ℓ := ℓ) k' y)
    (specialization (ℓ := ℓ) k' (y ≫ c.c₁))
    (specializationProd (ℓ := ℓ) k' (y ≫ c.c₁)) (diagPushforwardExchange ℓ X k' (y ≫ c.c₁))
    (exceptionalExchange ℓ c.support (hc.specialCorrespondence k').support νc)
    (supportSpecializationUnit k')
    (dualizingExchange ℓ (traitSpecializationUnit k k') νX)

lemma deformationTraceSpecialization_ΨXX :
    (hc.deformationTraceSpecialization k' νc νX F).ΨXX = specializationProd k' (y ≫ c.c₁) :=
  rfl

/-- The compact-support exchange `ν_F : Ra_{F'!} Ψ_F ⟶ Ψ_s Ra_{F!}` of the fixed loci determined by
`ν_c` and `ν_X` (`TraceSpecialization.fixedLocusToPointCompactSupportExchange`). -/
noncomputable abbrev fixedLocusExchange :=
  TraceSpecialization.fixedLocusToPointCompactSupportExchange (F := F)
    (F' := hc.specialFixedLocus k') (specialization (ℓ := ℓ) k' y)
    (specialization (ℓ := ℓ) k' (y ≫ c.c₁))
    (specializationProd (ℓ := ℓ) k' (y ≫ c.c₁)) (diagPushforwardExchange ℓ X k' (y ≫ c.c₁))
    (exceptionalExchange ℓ c.support (hc.specialCorrespondence k').support νc) νX

/-- The compact-support exchanges `ν_c`, `ν_X` *specialize the class of the component* `B` of the
fixed locus: the exchange `ν_F` of the fixed loci maps the specialization `Ra_{F'!}(σ_F) [F']` of
the unit class of the (proper) special fixed locus `F'` to the specialization of the class of `B`
in `Ra_{F!} ℚ̄_ℓ` (`BorelMooreSection.componentClass`), through the specialization unit `σ_s` of
the point. -/
abbrev SpecializesComponentClass {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom]
    (j : B ⟶ F.F) [IsOpenImmersion j.left] : Prop :=
  (hc.deformationTraceSpecialization k' νc νX F).SpecializesComponentClass
    (traitSpecializationUnit k k') (hc.fixedLocusExchange k' νc νX F) j


variable {νc νX F}


/-- **The specialization is injective on the component `B`**: if `ν_c` and `ν_X` specialize the
class of the component `B ∋ y` of the fixed locus, then a Borel–Moore section `z` of the fixed
locus whose specialization `sp(z)` vanishes restricts to zero on `B`. Indeed
`∫_{F'} sp(z) = σ_s⁻¹ Ψ_s(∫_B z|_B) σ_s` (`TraceSpecialization.integral_sp_eq`,
`TraceSpecialization.θF_ofSupportExchange`, `BorelMooreSection.integral_restrict`), `Ψ_s` is
injective on `End(ℚ̄_ℓ)` (`traitSpecialization_map_eq_zero_iff`) and integration over the
thickened point `B` is injective (`BorelMooreSection.integral_injective`). -/
theorem restrict_eq_zero_of_sp_eq_zero {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))})
    (hS : hc.SpecializesComponentClass k' νc νX F j) (z : BorelMooreSection ℓ F.F)
    (hz : (hc.deformationTraceSpecialization k' νc νX F).sp z = 0) :
    z.restrict j = 0 := by
  have h' := TraceSpecialization.map_integral_restrict_eq_zero_of_sp_eq_zero
    (hc.deformationTraceSpecialization k' νc νX F)
    (traitSpecializationUnit k k') (hc.fixedLocusExchange k' νc νX F)
    (TraceSpecialization.θF_ofSupportExchange (F := F) (F' := hc.specialFixedLocus k')
      (traitSpecializationUnit k k') (specialization (ℓ := ℓ) k' y)
      (specialization (ℓ := ℓ) k' (y ≫ c.c₁)) (specializationProd (ℓ := ℓ) k' (y ≫ c.c₁))
      (diagPushforwardExchange ℓ X k' (y ≫ c.c₁))
      (exceptionalExchange ℓ c.support (hc.specialCorrespondence k').support νc)
      (supportSpecializationUnit k') νX) j hS z hz
  obtain ⟨b, -, hb⟩ := RationalPoint.exists_lift_of_range_eq_singleton j _ hB
  apply BorelMooreSection.integral_injective b hb
  apply End.ext
  exact ((traitSpecialization_map_eq_zero_iff k k' _).mp h').trans
    (congrArg End.asHom (BorelMooreSection.integral_zero (ℓ := ℓ) (X := B))).symm

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
