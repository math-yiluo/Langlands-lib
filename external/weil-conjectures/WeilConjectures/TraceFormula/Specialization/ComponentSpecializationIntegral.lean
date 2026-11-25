/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentClass
public import WeilConjectures.TraceFormula.Specialization.DeformationTraceSpecialization

/-!
# Specialization on a point component is the identity

Let `T` be specialization data from a correspondence `c` with fixed locus `F` to `c'` with proper
fixed locus `F'`, whose dualizing map `θ_F` is the dualizing map of a compact-support exchange
`ν_F`, and let `B` be a proper open subscheme of `F` whose class is specialized by `ν_F`
(`TraceSpecialization.SpecializesComponentClass`). Then the integral of the specialization of a
Borel–Moore section `z` is the specialization of the integral of `z` over `B`:
```
∫_{F'} sp_F(z) = σ_s⁻¹ ∘ Ψ_s(∫_B z|_B) ∘ σ_s
```
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.integral_sp_eq_map_integral_restrict`).

For the deformation to the normal cone of a contracting point `y`, where `F_red` is the constant
family of the point `{y}` (blueprint `corollary-specialization-when-fixed-point-scheme`),
integration identifies Borel–Moore sections of the thickened point `B` and of the one-point
special fixed locus `F'` with `End(ℚ̄_ℓ)`, and under these identifications `sp_F` is the
trait specialization `Ψ_s` conjugated by the unit `σ_s`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.integral_sp_eq_map_integral_restrict`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence.TraceSpecialization

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}
  (T : c.TraceSpecialization F c' F')
  {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

/-- **Specialization on a component is the specialization of integrals** (blueprint
`corollary-specialization-when-fixed-point-scheme`): if `θ_F` is the dualizing map of `ν_F` and
`ν_F` specializes the class of the proper open subscheme `j : B ⟶ F`, then
`∫_{F'} sp_F(z) = σ_s⁻¹ ∘ Ψ_s(∫_B z|_B) ∘ σ_s` for every Borel–Moore section `z` of `F`. -/
theorem integral_sp_eq_map_integral_restrict [IsProper F'.F.hom]
    (νF : T.ΨF ⋙ boundedConstructibleLowerShriek ℓ
        (toPoint F'.F) ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F.F) ⋙ Ψpt)
    (hθ : T.θF = dualizingExchange ℓ σpt νF) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hS : T.SpecializesComponentClass σpt νF j) (z : BorelMooreSection ℓ F.F) :
    (T.sp z).integral.asHom = σpt ≫ Ψpt.map (z.restrict j).integral.asHom ≫ inv σpt := by
  have hS' : BorelMooreSection.unitClass ℓ F'.F ≫
      (boundedConstructibleLowerShriek ℓ (toPoint F'.F)).map T.σF ≫ νF.app (𝟙_ _) =
        σpt ≫ Ψpt.map (BorelMooreSection.componentClass ℓ j) := hS
  rw [T.integral_sp_eq σpt νF hθ z, BorelMooreSection.integral_restrict, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hS']

end Correspondence.TraceSpecialization

namespace Correspondence.IsContractingAt

attribute [local instance] isIso_traitSpecializationUnit

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k'}
  {νX : PointCompactSupportExchange (ℓ := ℓ) X k' (y ≫ c.c₁)} {F : c.FixedLocus}

/-- **Specialization when the fixed point scheme is a constant family** (blueprint
`corollary-specialization-when-fixed-point-scheme`, the case `F_red = {y} × S`): for the trace
specialization of the deformation to the normal cone of a contracting point `y`, and a component
`B ∋ y` of the fixed locus, open, closed, proper and with underlying set `{y}`, whose class is
specialized by `ν_c`, `ν_X`, the specialization `sp_F` is the identity under the identifications
of Borel–Moore sections of `B` and of the special fixed locus with `End(ℚ̄_ℓ)` given by
integration: `∫ sp_F(z) = σ_s⁻¹ ∘ Ψ_s(∫_B z|_B) ∘ σ_s`, and `Ψ_s` is injective on `End(ℚ̄_ℓ)`
(`traitSpecialization_map_eq_zero_iff`). -/
theorem integral_sp_eq_map_integral_restrict {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hS : hc.SpecializesComponentClass k' νc νX F j) (z : BorelMooreSection ℓ F.F) :
    ((hc.deformationTraceSpecialization k' νc νX F).sp z).integral.asHom =
      traitSpecializationUnit k k' ≫ (traitSpecialization k k').map (z.restrict j).integral.asHom ≫
        inv (traitSpecializationUnit k k') :=
  TraceSpecialization.integral_sp_eq_map_integral_restrict
    (hc.deformationTraceSpecialization k' νc νX F)
    (traitSpecializationUnit k k') (hc.fixedLocusExchange k' νc νX F)
    (TraceSpecialization.θF_ofSupportExchange (F := F) (F' := hc.specialFixedLocus k')
      (traitSpecializationUnit k k') (specialization (ℓ := ℓ) k' y)
      (specialization (ℓ := ℓ) k' (y ≫ c.c₁)) (specializationProd (ℓ := ℓ) k' (y ≫ c.c₁))
      (diagPushforwardExchange ℓ X k' (y ≫ c.c₁))
      (exceptionalExchange ℓ c.support (hc.specialCorrespondence k').support νc)
      (supportSpecializationUnit k') νX) j hS z

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
