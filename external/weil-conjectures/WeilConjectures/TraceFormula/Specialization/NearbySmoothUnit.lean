/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SmoothBaseChangePadicAlgCl
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeLocal
public import WeilConjectures.TraceFormula.Specialization.ResidueConstantSmoothExchange
public import WeilConjectures.TraceFormula.Specialization.TraitChangeTrait
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange

/-!

# The specialization unit of a smooth model over the trait

Let `M` be a nearby-cycles model of finite type over the strictly henselian trait
`S = Spec k'⟦t⟧` along `q : 𝒳 ⟶ S` (`NearbyCyclesModel.IsTraitModelOver`). If `q` is smooth, the
specialization unit `σ_M : ℚ̄_ℓ ⟶ Ψ_M(ℚ̄_ℓ)` is an isomorphism
(`NearbyCyclesModel.IsTraitModelOver.isIso_unit_of_smooth`; blueprint
`prose-E-03` (1), smooth case, at the unit). The same holds for trait models
over a generic base (`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_unit_of_smooth`).

## Proof

* The structure morphisms `q`, `g` are a morphism from the model `M.toGeneric` of the geometric
  generic fibre to the trait `S` as a model of its geometric generic point
  (`NearbyCyclesModel.IsTraitModelOver.toTraitGeneric`). By smooth base change along the inclusion
  `j : Spec Ω ⟶ S` (`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_smooth`, reduced to the
  projections `𝔸ⁿ_S ⟶ S` and to integral coefficients,
  `NearbyCyclesModel.isIso_baseChangeMap_affineSpace_traitGenericModel_app`), its pullback
  exchange is invertible at the unit.
* The specialization unit of the trait is invertible
  (`NearbyCyclesModel.isIso_unit_traitGenericModel`), so by the unit law of the pullback exchange
  so is that of `M.toGeneric` (`NearbyCyclesModel.Hom.isIso_unit_of_isIso_pullbackExchange_app`).
* The specialization units of `M` and `M.toGeneric` agree up to `L(𝟙)^*`
  (`NearbyCyclesModel.isIso_unit_of_isIso_unit_toGeneric`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-! ### Specialization units and the unit law -/

namespace NearbyCyclesModel

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- If the target of a morphism of models `φ : M ⟶ N` has invertible specialization unit and the
pullback exchange of `φ` is invertible at the unit, then the specialization unit of `M` is
invertible, by the unit law of the pullback exchange. -/
lemma Hom.isIso_unit_of_isIso_pullbackExchange_app (φ : M.Hom N f f') [IsIso (N.unit Λ)]
    [IsIso ((φ.pullbackExchange Λ).app (𝟙_ _))] : IsIso (M.unit Λ) := by
  have : IsIso ((leftDerivedUpperStarUnitIso Λ f').hom ≫ M.unit Λ ≫
      (M.nearbyCycles Λ).map (leftDerivedUpperStarUnitIso Λ f).inv) := by
    rw [← φ.map_unit_comp_pullbackExchange_app Λ]
    infer_instance
  have : IsIso (M.unit Λ ≫ (M.nearbyCycles Λ).map (leftDerivedUpperStarUnitIso Λ f).inv) :=
    IsIso.of_isIso_comp_left (leftDerivedUpperStarUnitIso Λ f').hom _
  exact IsIso.of_isIso_comp_right _ ((M.nearbyCycles Λ).map (leftDerivedUpperStarUnitIso Λ f).inv)

/-- The specialization unit of a model is invertible if that of the model of its geometric generic
fibre (`NearbyCyclesModel.toGeneric`) is: the two agree up to the invertible pullback exchange of
`NearbyCyclesModel.toGenericSelfHom`. -/
lemma isIso_unit_of_isIso_unit_toGeneric (M : NearbyCyclesModel X X')
    [IsIso (M.toGeneric.unit Λ)] : IsIso (M.unit Λ) := by
  have h := (toGenericSelfHom M).map_unit_comp_pullbackExchange_app Λ
  have : IsIso (L((𝟙 X')^*⟦Λ⟧).map (M.unit Λ) ≫
      ((toGenericSelfHom M).pullbackExchange Λ).app (𝟙_ _)) := by
    rw [h]
    infer_instance
  have : IsIso (L((𝟙 X')^*⟦Λ⟧).map (M.unit Λ)) :=
    IsIso.of_isIso_comp_right _ (((toGenericSelfHom M).pullbackExchange Λ).app (𝟙_ _))
  exact isIso_of_isIso_map_leftDerivedUpperStar Λ (𝟙 X') _ this

end Unit

end NearbyCyclesModel

/-! ### Smooth base change for the geometric generic point of the trait -/

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [Fact (ringChar k' ≠ ℓ)]

namespace NearbyCyclesModel

variable {k'} {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

variable (k') in
/-- **Smooth base change along affine spaces for the geometric generic point of the trait**: for
the trait `S` as a model of its geometric generic point, the base change morphism
`Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` of the cartesian square of `j : Spec Ω ⟶ S` along `π : 𝔸ⁿ_S ⟶ S` is
invertible at `Lε^* K` for every bounded constructible `ℚ̄_ℓ`-complex `K` on `Spec Ω`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_smooth`). -/
theorem isIso_baseChangeMap_affineSpace_traitGenericModel_app [Fact (ringChar k').Prime]
    (n : ℕ)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (Spec (.of (traitGenericField k')))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of (traitGenericField k')))))}
    (hK : boundedConstructible _ K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ)
      (IsPullback.of_hasPullback (traitGenericModel k').j
        (𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) ↘
          (traitGenericModel k').total)).toCommSq).app
      ((L(((traitGenericModel k').ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  have : QuasiCompact (traitGenericModel k').j := by
    unfold traitGenericModel traitGenericPoint
    infer_instance
  have : QuasiSeparated (traitGenericModel k').j := by
    unfold traitGenericModel traitGenericPoint
    infer_instance
  have : IsNoetherian (traitGenericModel k').generic :=
    inferInstanceAs (IsNoetherian (Spec (.of (traitGenericField k'))))
  have : CompactSpace (traitGenericModel k').total :=
    inferInstanceAs (CompactSpace (trait k'))
  have : QuasiSeparatedSpace (traitGenericModel k').total :=
    inferInstanceAs (QuasiSeparatedSpace (trait k'))
  have : Smooth (𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) ↘
      (traitGenericModel k').total) :=
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin n))) _
  have : CompactSpace 𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) :=
    QuasiCompact.compactSpace_of_compactSpace
      (𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) ↘ (traitGenericModel k').total)
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) :=
    quasiSeparatedSpace_of_quasiSeparated
      (𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) ↘ (traitGenericModel k').total)
  have : CompactSpace ↥(pullback (traitGenericModel k').j
      (𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) ↘ (traitGenericModel k').total)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)
  have : QuasiSeparatedSpace ↥(pullback (traitGenericModel k').j
      (𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) ↘ (traitGenericModel k').total)) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  exact isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_smooth ℓ
    (𝔸(ULift.{u} (Fin n); (traitGenericModel k').total) ↘ (traitGenericModel k').total)
    (IsPullback.of_hasPullback (traitGenericModel k').j _) (isUnit_natCast_trait k') _ hK

/-- **The smooth exchange at the unit**: for a model of finite type over the trait along a smooth
`q`, the pullback exchange of `q` (from the model of the geometric generic fibre to the trait) is
invertible at the unit, by smooth base change along the geometric generic point of the trait. -/
theorem IsTraitModelOver.isIso_pullbackExchange_toTraitGeneric_app_unit
    [Fact (ringChar k').Prime] (hM : M.IsTraitModelOver q g) [Smooth q] :
    IsIso ((hM.toTraitGeneric.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app (𝟙_ _)) := by
  have := hM.quasiCompact
  have := hM.isSeparated
  have : CompactSpace M.total := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace M.total := quasiSeparatedSpace_of_quasiSeparated q
  have hA (n : ℕ) := isIso_baseChangeMap_affineSpace_traitGenericModel_app (ℓ := ℓ) k' n
    (boundedConstructible_tensorUnit _ _)
  have hj : IsPullback hM.toTraitGeneric.generic M.toGeneric.j (traitGenericModel k').j
      hM.toTraitGeneric.total :=
    hM.isPullback_j.flip
  have : Smooth hM.toTraitGeneric.total := inferInstanceAs (Smooth q)
  have h₂ := isIso_baseChangeMap_app_of_smooth (Profinite.padicAlgClRingObj ℓ) hj _ hA
  rw [Subsingleton.elim hj.toCommSq hM.toTraitGeneric.commSq_j] at h₂
  have h₁ := hM.toTraitGeneric.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app
    (Profinite.padicAlgClRingObj ℓ) (𝟙_ _)
  revert h₁ h₂
  normalize_precoherent
  intro h₂ h₁
  exact h₁ h₂

/-- **The specialization unit of a smooth model over the trait is invertible** (blueprint
`prose-E-03` (1), smooth case, at the unit): if `M` is of finite type over
the strictly henselian trait `S` along a smooth `q`, then `σ_M : ℚ̄_ℓ ⟶ Ψ_M(ℚ̄_ℓ)` is an
isomorphism. -/
theorem IsTraitModelOver.isIso_unit_of_smooth [IsSepClosed k'] [Fact (ringChar k').Prime]
    (hM : M.IsTraitModelOver q g) [Smooth q] : IsIso (M.unit (Profinite.padicAlgClRingObj ℓ)) := by
  have := isIso_unit_traitGenericModel (Profinite.padicAlgClRingObj ℓ) k'
  have := hM.isIso_pullbackExchange_toTraitGeneric_app_unit (ℓ := ℓ)
  have := hM.toTraitGeneric.isIso_unit_of_isIso_pullbackExchange_app
    (Profinite.padicAlgClRingObj ℓ)
  exact isIso_unit_of_isIso_unit_toGeneric _ M

/-- **The specialization unit of a smooth trait model over a generic base is invertible**. -/
theorem IsTraitModelOfGenericBase.isIso_unit_of_smooth [IsSepClosed k'] [Fact (ringChar k').Prime]
    {F : Type u} [Field F] {X₁ : Over (Spec (.of F))}
    {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [Smooth q] :
    IsIso (M.unit (Profinite.padicAlgClRingObj ℓ)) :=
  h.isTraitModelOver.isIso_unit_of_smooth

/-- **The specialization unit of a smooth model over the trait is invertible**, on bounded
constructible complexes (`NearbyCyclesModel.boundedConstructibleUnit`). -/
theorem IsTraitModelOver.isIso_boundedConstructibleUnit_of_smooth {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g) [Smooth q]
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    IsIso (boundedConstructibleUnit ℓ hP) := by
  have : IsIso ((boundedConstructible _).ι.map (boundedConstructibleUnit ℓ hP)) :=
    hM.isIso_unit_of_smooth
  exact isIso_of_fully_faithful (boundedConstructible _).ι _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
