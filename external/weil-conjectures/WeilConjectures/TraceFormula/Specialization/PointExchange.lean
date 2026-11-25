/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.TraceFormula.Specialization.CompactifiedModel
public import WeilConjectures.TraceFormula.Specialization.DeformationTraceSpecialization
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.Specialization.OpenExchange

/-!

# The compact-support exchange of the structure map of a proper scheme

For a proper `k`-scheme `X` with rational point `x`, the compact-support exchange
`ν_X : Ra_{X'!} Ψ_X ⟶ Ψ_s Ra_{X!}` of blueprint `prose-E-15` (3)
(`ProEtale.CondensedRing.pointCompactSupportExchange`), for the compactification
`X' ⊂ P_s ⟶ Spec k'` of the special fibre given by the compactified deformation model:
`ν_X = χ_p⁻¹ ∘ Rp'_*(ν_h)` read through `Ra'_! ≅ Rp'_! h'_! ≅ Rp'_* h'_!` and `Ra_* ≅ Ra_!`, with
`ν_h : h'_! Ψ_X ⟶ Ψ_P` the adjoint of the inverse of the open exchange `α_h` and `χ_p` the
(invertible) proper exchange of `𝒫 ⟶ S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- A transformation `χ : F ⟶ G` is invertible on the objects of the subcategory `ι`. -/
def IsIsoOn {C D E : Type*} [Category C] [Category D] [Category E] (ι : C ⥤ D) {F G : D ⥤ E}
    (χ : F ⟶ G) : Prop :=
  ∀ K, IsIso (χ.app (ι.obj K))

/-- The inverse on a subcategory `ι` of a transformation invertible on the objects of `ι`. -/
noncomputable def invOnSubcategory {C D E : Type*} [Category C] [Category D] [Category E]
    (ι : C ⥤ D) {F G : D ⥤ E} (χ : F ⟶ G) (h : IsIsoOn ι χ) : ι ⋙ G ⟶ ι ⋙ F :=
  have : IsIso (Functor.whiskerLeft ι χ) := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ h
  inv (Functor.whiskerLeft ι χ)

/-- The shape of `ν_X`: `Sp ⋙ LSa' ≅ Sp ⋙ OLS ⋙ LStp`, then (through the inclusions `ι`) `ν_h`
followed by `χinv` (the inverse of `χ`), then `LSta ≅ LSa`. -/
noncomputable def pointExchangeAux {CX CX' CP Cs Cs' DX DX' DP Ds Ds' : Type*} [Category CX]
    [Category CX'] [Category CP] [Category Cs] [Category Cs'] [Category DX] [Category DX']
    [Category DP] [Category Ds] [Category Ds'] {Sp : CX ⥤ CX'} {LSa' : CX' ⥤ Cs'}
    {LSh OLS : CX' ⥤ CP} {LSp LStp : CP ⥤ Cs'} {LSa LSta : CX ⥤ Cs} {Ts : Cs ⥤ Cs'}
    {ιX : CX ⥤ DX} {ιX' : CX' ⥤ DX'} {ιP : CP ⥤ DP} {ιs : Cs ⥤ Ds} {ιs' : Cs' ⥤ Ds'}
    (hι : ιs'.FullyFaithful) {ΨX : DX ⥤ DX'} {ΨP : DX ⥤ DP} {Ψs : Ds ⥤ Ds'} {Dh : DX' ⥤ DP}
    {Lh : DP ⥤ DX'} {L1 : DX ⥤ DX} {Rp : DP ⥤ Ds'} {Ra : DX ⥤ Ds}
    (i1 : LSa' ≅ LSh ⋙ LSp) (i2 : LSh ≅ OLS) (i3 : LSp ≅ LStp) (i4 : LSa ≅ LSta)
    (cSp : Sp ⋙ ιX' ≅ ιX ⋙ ΨX) (cO : OLS ⋙ ιP ≅ ιX' ⋙ Dh) (cR : LStp ⋙ ιs' ≅ ιP ⋙ Rp)
    (cA : LSta ⋙ ιs ≅ ιX ⋙ Ra) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs) (adj : Dh ⊣ Lh) (e : 𝟭 DX ≅ L1)
    (α : ΨP ⋙ Lh ⟶ L1 ⋙ ΨX) (hα : IsIso α)
    (χinv : ιX ⋙ ΨP ⋙ Rp ⟶ ιX ⋙ Ra ⋙ Ψs) : Sp ⋙ LSa' ⟶ LSa ⋙ Ts :=
  Functor.whiskerLeft Sp (i1.hom ≫ Functor.whiskerRight i2.hom LSp ≫
      Functor.whiskerLeft OLS i3.hom) ≫
    (hι.whiskeringRight CX).preimage (X := Sp ⋙ OLS ⋙ LStp) (Y := LSta ⋙ Ts)
      (Functor.whiskerLeft Sp (Functor.whiskerLeft OLS cR.hom ≫ Functor.whiskerRight cO.hom Rp) ≫
        Functor.whiskerRight cSp.hom (Dh ⋙ Rp) ≫
        Functor.whiskerLeft ιX (Functor.whiskerRight (Functor.whiskerRight
          ((Functor.leftUnitor ΨX).inv ≫ Functor.whiskerRight e.hom ΨX ≫ inv α) Dh ≫
            Functor.whiskerLeft ΨP adj.counit ≫ (Functor.rightUnitor ΨP).hom) Rp) ≫
        χinv ≫ Functor.whiskerRight cA.inv Ψs ≫
        Functor.whiskerLeft LSta cT.inv) ≫
    Functor.whiskerRight i4.inv Ts

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom] (x : RationalPoint X)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The square of geometric generic fibres of `𝒳 ⟶ 𝒫` is cartesian. -/
lemma isPullback_deformationGenericToCompactified :
    IsPullback (deformationGenericToCompactified X x k') (deformationGenericToTotal X x.left.ker k')
      (compactifiedGenericToTotal X x k') (deformationTotalToCompactified X x k') :=
  IsPullback.of_right (by
      rw [deformationGenericToCompactified_toPoint, deformationTotalToCompactified_toTrait]
      exact (IsPullback.of_hasPullback _ _).flip)
    (deformationGenericToCompactified_toTotal X x k') (isPullback_compactifiedGeneric X x k').flip

/-- The geometric generic fibre of `𝒫` is `X ×_k Spec Ω`. -/
lemma isPullback_compactifiedGenericToBase :
    IsPullback (compactifiedGenericToBase X x k') (compactifiedGenericToPoint X x k') X.hom
      (traitModel k k').ε := by
  have h₁ : IsPullback (compactifiedGenericToPunctured X x k') (compactifiedGenericToPoint X x k')
      (pullback.snd _ _) (traitGenericPointToPuncturedLine k k') := by
    refine IsPullback.of_right ?_ (compactifiedGenericToPunctured_snd X x k')
      (isPullback_deformationCompactificationOf X x)
    rw [compactifiedGenericToPunctured_generic, traitGenericPointToPuncturedLine_ι]
    exact (isPullback_compactifiedGeneric X x k').paste_horiz (isPullback_compactifiedTotal X x k')
  have e : traitGenericPointToPuncturedLine k k' ≫ (Scheme.Hom.puncturedLine _).ι ≫
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) = (traitModel k k').ε := by
    rw [← traitModel_j_traitToBase, traitGenericPointToPuncturedLine_ι_assoc,
      traitToAffineLine_over]
    rfl
  exact e ▸ h₁.paste_horiz (IsPullback.of_hasPullback X.hom _)

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [IsSepClosed k'] [Fact (ringChar k).Prime] [Fact (ringChar k').Prime]
  [Fact (ringChar k ≠ ℓ)] [Fact (ringChar k' ≠ ℓ)] in
lemma isIso_deformationToCompactifiedModelHom_pullbackExchange :
    IsIso ((deformationToCompactifiedModelHom X x k').pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)) :=
  (deformationToCompactifiedModelHom X x k').isIso_pullbackExchange_of_isOpenImmersion _
    (isPullback_deformationGenericToCompactified X x k')

/-- `compactifiedToTraitModelHom` over the structure map `toPoint` of the special fibre. -/
noncomputable def compactifiedToPointModelHom :
    (compactifiedDeformationModel X x k').Hom (traitModel k k') (toPoint X).left
      (toPoint (compactifiedSpecialFibre X x k')).left where
  total := compactifiedTotalToTrait X x k'
  generic := compactifiedGenericToPoint X x k'
  comm_j := (isPullback_compactifiedGeneric X x k').w.symm
  comm_i := by rw [toPoint_left]; exact (isPullback_compactifiedSpecialFibre X x k').w.symm
  comm_ε := by rw [toPoint_left]; exact (compactifiedGenericToBase_hom X x k').symm

omit [IsSepClosed k'] [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] in
lemma isIsoOn_compactifiedToPointModelHom_pushforwardExchange :
    IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
      ((compactifiedToPointModelHom X x k').pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) :=
  fun K ↦
  have : IsProper (toPoint X).left := by rw [toPoint_left]; infer_instance
  have : IsProper (compactifiedToPointModelHom X x k').total :=
    inferInstanceAs (IsProper (compactifiedTotalToTrait X x k'))
  have : IsNoetherian (point k).left := inferInstanceAs (IsNoetherian (Spec (.of k)))
  (compactifiedToPointModelHom X x k').isIso_pushforwardExchange_app_of_isProper
    (point k).hom
    (isTraitModel_compactifiedDeformationModel X x k').exists_over
    (isTraitModel_traitModel k k').exists_over
    (by
      have h := isPullback_compactifiedSpecialFibre X x k'
      rw [← toPoint_left (compactifiedSpecialFibre X x k')] at h
      exact h)
    (by
      have h := isPullback_compactifiedGenericToBase X x k'
      rw [← toPoint_left X] at h
      exact h) K.property

/-- **The compact-support exchange `ν_X` of a proper `X`** (blueprint `prose-E-15`
(3)): `ν_X = χ_p⁻¹ ∘ Rp'_*(ν_h)`, through `Ra'_! ≅ Rp'_! h'_! ≅ Rp'_* h'_!` and `Ra_* ≅ Ra_!`. -/
noncomputable def pointCompactSupportExchange :
    Correspondence.IsContractingAt.PointCompactSupportExchange (ℓ := ℓ) X k' x :=
  have : IsProper (toPoint X).left := by rw [toPoint_left]; infer_instance
  have : IsProper (toPoint (compactifiedSpecialFibre X x k')).left := by
    rw [toPoint_left]; infer_instance
  pointExchangeAux (ObjectProperty.fullyFaithfulι _)
    (lowerShriekCompOfEq ℓ (deformationSpecialFibreToCompactified X x k') (toPoint _)
      (comp_toPoint _))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ _)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ _)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X))
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
    (boundedConstructibleLowerStarCompatibility ℓ _)
    (boundedConstructibleLowerStarCompatibility ℓ _)
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility _)
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction _
      (deformationSpecialFibreToCompactified X x k').left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _ _).symm)
    (leftDerivedUpperStarId _ X.left).symm
    ((deformationToCompactifiedModelHom X x k').pullbackExchange _)
    (isIso_deformationToCompactifiedModelHom_pullbackExchange X x k')
    (invOnSubcategory _ _ (isIsoOn_compactifiedToPointModelHom_pushforwardExchange X x k'))

end AlgebraicGeometry.ProEtale.CondensedRing
