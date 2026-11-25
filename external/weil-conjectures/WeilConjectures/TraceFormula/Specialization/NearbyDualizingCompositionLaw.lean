/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineOver
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingClosedImmersionGenericBase
public import WeilConjectures.TraceFormula.Specialization.ProperUnitClass

/-!

# The composition law of the dualizing maps along a proper morphism of models

For a morphism `φ : N ⟶ M` of proper trait models with full geometric generic fibres over a
common generic base, over proper `i₁ : Y₁ ⟶ X₁` and `i₂ : Y' ⟶ X'`, the squares of special fibres
and of identifications `ε` of `φ` are cartesian, so the proper exchange `χ_φ` is invertible
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`). Its inverse, read through
`Ri_! ≅ Ri_*`, is a compact-support exchange `ν_φ`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.properCompactSupportExchange`), and the closed
immersion law `NearbyCyclesModel.NearbyDualizingDataOfGenericBase.closedImmersion_law` for `ν_φ`
is the unconditional composition law
`θ_N ∘ Ψ_N(ρ) = ρ' ∘ Ri₂^!(θ_M) ∘ β_φ(ω_{X₁})`
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_comp_law`).

For a coordinate, the projective line `ℙ¹_S` over the trait is a trait model of `ℙ¹_η` over the
generic base `(η, ℙ¹_η, 𝟙)` (`NearbyCyclesModel.projectiveLineModel`,
`NearbyCyclesModel.isTraitModelOfGenericBase_projectiveLineModel`), and the dualizing map of a
model with a proper morphism of models to `ℙ¹_S` is determined by that of `ℙ¹_S`
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_of_projectiveLine`).

The invertibility of the proper exchange rests on
`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper` (proper base change for nearby
cycles).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {Cs Cs' CB CB' : Type*} [Category Cs] [Category Cs'] [Category CB] [Category CB']
  {Ra LSa : CB ⥤ Cs} {Ra' LSa' : CB' ⥤ Cs'} {Ψs : Cs ⥤ Cs'} {ΨM : CB ⥤ CB'}

/-- The inverse exchange inverts the exchange under the identifications `LSa ≅ Ra`,
`LSa' ≅ Ra'`. -/
lemma app_comp_invExchange_app (is : LSa ≅ Ra) (is' : LSa' ≅ Ra') (χ : Ra ⋙ Ψs ⟶ ΨM ⋙ Ra')
    [IsIso χ] (K : CB) :
    χ.app K ≫ is'.inv.app (ΨM.obj K) ≫ (invExchange is is' χ).app K = Ψs.map (is.inv.app K) := by
  have hinv : (inv χ).app K = inv (χ.app K) := NatIso.isIso_inv_app χ K
  simp only [invExchange, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    hinv, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]

end Abstract

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {ℓ : ℕ} {F : Type u} [Field F] {X₁ Y₁ : Over (Spec (.of F))}
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {X' Y' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {N : NearbyCyclesModel Y₁.left Y'.left} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

namespace IsTraitModelOfGenericBase

/-- The square of special fibres of a morphism of trait models over the trait is cartesian. -/
lemma isPullback_i_of_hom (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN) {i₁ : Y₁.left ⟶ X₁.left} (i₂ : Y' ⟶ X')
    (φ : N.Hom M i₁ i₂.left) (hq : qN = φ.total ≫ q) :
    IsPullback N.i i₂.left φ.total M.i := by
  refine IsPullback.of_bot ?_ φ.comm_i.symm hM.isTraitModelOver.isPullback_i
  rw [Over.w i₂, ← hq]
  exact hN.isTraitModelOver.isPullback_i

/-- The square of identifications `ε` of a morphism of models with full geometric generic fibres
over a generic base is cartesian. -/
lemma isPullback_ε_of_hom (i₁ : Y₁ ⟶ X₁) {i₂ : Y'.left ⟶ X'.left} (φ : N.Hom M i₁.left i₂)
    (hg : gN = φ.generic ≫ g)
    (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hNgen : IsPullback N.ε gN Y₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    IsPullback N.ε φ.generic i₁.left M.ε := by
  refine IsPullback.of_bot ?_ φ.comm_ε.symm hMgen
  rw [Over.w i₁, ← hg]
  exact hNgen

variable (ℓ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (hM : M.IsTraitModelOfGenericBase X₁ ι q g) (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
  [IsProper qN]
  (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
  (hNgen : IsPullback N.ε gN Y₁.hom (traitGenericPointToSpec k' ≫ ι))
  (i₁ : Y₁ ⟶ X₁) [IsProper i₁.left] (i₂ : Y' ⟶ X')
  (φ : N.Hom M i₁.left i₂.left) (hq : qN = φ.total ≫ q) (hg : gN = φ.generic ≫ g)

include hq hMgen hNgen hg in
/-- **The proper exchange of a morphism of proper trait models over a generic base** is
invertible on bounded constructible complexes (blueprint `prose-E-03` (2)):
the morphism of total spaces is proper since `qN = φ.total ≫ q` is proper and `q` separated, and
the squares of special fibres and of identifications are cartesian. -/
lemma isIso_boundedConstructiblePushforwardExchange :
    IsIso (φ.boundedConstructiblePushforwardExchange ℓ
      (hN.preservesBoundedConstructible (ℓ := ℓ)) (hM.preservesBoundedConstructible (ℓ := ℓ))) := by
  have : IsSeparated q := hM.isTraitModelOver.isSeparated
  have : IsProper (φ.total ≫ q) := hq ▸ inferInstance
  have : IsProper φ.total := IsProper.of_comp φ.total q
  have : IsNoetherian X₁.left := isNoetherian_of_locallyOfFiniteType X₁.hom
  rw [Hom.boundedConstructiblePushforwardExchange_eq_liftExchange]
  exact isIso_liftExchange_of_isIso_app _ _ _ _ _
    fun K ↦ φ.isIso_pushforwardExchange_app_of_isProper X₁.hom
      hN.isTraitModelOver.isTraitModel.exists_over hM.isTraitModelOver.isTraitModel.exists_over
      (isPullback_i_of_hom hM hN i₂ φ hq) (isPullback_ε_of_hom i₁ φ hg hMgen hNgen) K.property

variable [IsProper i₂.left]

/-- **The compact-support exchange of a morphism of proper trait models over a generic base**:
the inverse of the invertible proper exchange `χ_φ`, read through `Ri₁_! ≅ Ri₁_*` and
`Ri₂_! ≅ Ri₂_*`. -/
noncomputable def properCompactSupportExchange :
    boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        boundedConstructibleLowerShriek ℓ i₂ ⟶
      boundedConstructibleLowerShriek ℓ i₁ ⋙
        boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ)) :=
  have := isIso_boundedConstructiblePushforwardExchange ℓ hM hN hMgen hNgen i₁ i₂ φ hq hg
  invExchange (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂)
    (φ.boundedConstructiblePushforwardExchange ℓ
      (hN.preservesBoundedConstructible (ℓ := ℓ)) (hM.preservesBoundedConstructible (ℓ := ℓ)))

/-- The compact-support exchange `ν_φ` inverts the proper exchange `χ_φ` under `Ri_! ≅ Ri_*`. -/
lemma pushforwardExchange_app_comp_properCompactSupportExchange_app (K) :
    (φ.boundedConstructiblePushforwardExchange ℓ
        (hN.preservesBoundedConstructible (ℓ := ℓ))
        (hM.preservesBoundedConstructible (ℓ := ℓ))).app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
        ((boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).obj K) ≫
      (properCompactSupportExchange ℓ hM hN hMgen hNgen i₁ i₂ φ hq hg).app K =
        (boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app K) :=
  have := isIso_boundedConstructiblePushforwardExchange ℓ hM hN hMgen hNgen i₁ i₂ φ hq hg
  app_comp_invExchange_app _ _ _ K

end IsTraitModelOfGenericBase

namespace NearbyDualizingDataOfGenericBase

variable [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- **The composition law of the dualizing maps along a proper morphism of models** (blueprint
`sec-Base-change-for-nearby-cycles` (4)): for a morphism `φ : N ⟶ M` of proper trait models with
full geometric generic fibres over a common generic base, over proper `i₁ : Y₁ ⟶ X₁` and
`i₂ : Y' ⟶ X'`, `θ_N ∘ Ψ_N(ρ) = ρ' ∘ Ri₂^!(θ_M) ∘ β_φ(ω_{X₁})`, where `β_φ` is the exceptional
exchange of the compact-support exchange `ν_φ` inverse to the proper exchange `χ_φ`. This is
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.closedImmersion_law` for `ν_φ`. -/
theorem θ_comp_law (D : NearbyDualizingDataOfGenericBase k' ℓ)
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint Y₁).left]
    [IsProper (CondensedRing.toPoint X').left] [IsProper (CondensedRing.toPoint Y').left]
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g) (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
    [IsProper q] [IsProper qN]
    (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hNgen : IsPullback N.ε gN Y₁.hom (traitGenericPointToSpec k' ≫ ι))
    (i₁ : Y₁ ⟶ X₁) [IsProper i₁.left] (i₂ : Y' ⟶ X') [IsProper i₂.left]
    (φ : N.Hom M i₁.left i₂.left) (hq : qN = φ.total ≫ q) (hg : gN = φ.generic ≫ g) :
    (boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).map
        (upperShriekDualizingComplexIso ℓ i₁).hom ≫ D.θ hN =
      (exceptionalExchange ℓ i₁ i₂
          (hM.properCompactSupportExchange ℓ hN hMgen hNgen i₁ i₂ φ hq hg)).app
          (dualizingComplex ℓ X₁) ≫
        (boundedConstructibleUpperShriek ℓ i₂).map (D.θ hM) ≫
        (upperShriekDualizingComplexIso ℓ i₂).hom :=
  D.closedImmersion_law hM hN hMgen hNgen i₁ i₂ φ hq hg _
    (IsTraitModelOfGenericBase.pushforwardExchange_app_comp_properCompactSupportExchange_app ℓ
      hM hN hMgen hNgen i₁ i₂ φ hq hg)

end NearbyDualizingDataOfGenericBase

section ProjectiveLine

open ProjectiveSpace

variable (k' : Type u) [Field k']

/-- The projective line `ℙ¹_S` over the trait `S = Spec k'⟦t⟧`, as a model of `ℙ¹_η` with
special fibre `ℙ¹_{k'}`: the geometric generic fibre `ℙ¹_Ω`, with the base changes
`j : ℙ¹_Ω ⟶ ℙ¹_S`, `i : ℙ¹_{k'} ⟶ ℙ¹_S` and `ε : ℙ¹_Ω ⟶ ℙ¹_η` of the geometric generic point,
the closed point and `Spec Ω ⟶ η`. -/
noncomputable def projectiveLineModel :
    NearbyCyclesModel (overProjectiveLine (point (FractionRing (PowerSeries k')))).left
      (overProjectiveLine (point k')).left where
  total := ProjectiveLine (trait k')
  generic := ProjectiveLine (Spec (.of (traitGenericField k')))
  j := ProjectiveSpace.map _ (traitGenericPoint k')
  i := ProjectiveSpace.map _ (traitClosedPoint k')
  ε := ProjectiveSpace.map _ (traitGenericPointToSpec k')

/-- The structure morphism of `ℙ¹_K` over `Spec K` is proper. -/
instance isProper_toPoint_overProjectiveLine_point (K : Type u) [Field K] :
    IsProper (toPoint (overProjectiveLine (point K))).left := by
  rw [toPoint_left]
  change IsProper (ProjectiveLine (Spec (.of K)) ↘ Spec (.of K) ≫ 𝟙 _)
  infer_instance

/-- The projective line `ℙ¹_S` over the trait is a trait model of `ℙ¹_η` over the generic base
`(η, ℙ¹_η, 𝟙)`: all its fibres are base changes of `ℙ¹_S`, and its generic fibre is `ℙ¹_η`. -/
theorem isTraitModelOfGenericBase_projectiveLineModel :
    (projectiveLineModel k').IsTraitModelOfGenericBase
      (overProjectiveLine (point (FractionRing (PowerSeries k')))) (𝟙 _)
      (ProjectiveLine (trait k') ↘ trait k')
      (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘
        Spec (.of (traitGenericField k'))) := by
  have hi := isPullback_map (ULift.{u} (Fin 2)) (traitClosedPoint k')
  rw [← Category.comp_id (ProjectiveLine (Spec (.of k')) ↘ Spec (.of k'))] at hi
  refine ⟨⟨inferInstance, inferInstance, inferInstance,
    isPullback_map (ULift.{u} (Fin 2)) (traitGenericPoint k'), hi⟩, ?_⟩
  have hP := isPullback_map (ULift.{u} (Fin 2)) (traitGenericSpec k')
  let e := hP.isoPullback.inv
  let w : pullback (ProjectiveLine (trait k') ↘ trait k') (traitGenericSpec k') ⟶
      pullback (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom (𝟙 _) :=
    pullback.lift e (pullback.snd _ _) (by
      refine (congrArg (e ≫ ·) (Category.comp_id _)).trans ?_
      exact hP.isoPullback_inv_snd.trans (Category.comp_id _).symm)
  have hwfst : w ≫ pullback.fst _ _ = e := pullback.lift_fst _ _ _
  have : IsIso (w ≫ pullback.fst _ _) := by
    rw [hwfst]
    infer_instance
  have : IsIso w := IsIso.of_isIso_comp_right w (pullback.fst _ _)
  refine ⟨w, inferInstance, pullback.lift_snd _ _ _, ?_⟩
  rw [hwfst]
  refine hP.hom_ext ?_ ?_
  · rw [Category.assoc, hP.isoPullback_inv_fst, genericFibreInclusion_fst]
    change _ = ProjectiveSpace.map (ULift.{u} (Fin 2)) (traitGenericPointToSpec k') ≫
      ProjectiveSpace.map (ULift.{u} (Fin 2)) (traitGenericSpec k')
    rw [← map_comp, traitGenericPointToSpec_traitGenericSpec]
    rfl
  · rw [Category.assoc, hP.isoPullback_inv_snd, genericFibreInclusion_snd]
    exact (map_over _ _).symm

/-- The geometric generic fibre of `ℙ¹_S` is the full base change `ℙ¹_Ω` of `ℙ¹_η`. -/
lemma isPullback_projectiveLineModel_ε :
    IsPullback (projectiveLineModel k').ε
      (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k')))
      (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom
      (traitGenericPointToSpec k' ≫ 𝟙 _) := by
  have h := isPullback_map (ULift.{u} (Fin 2)) (traitGenericPointToSpec k')
  rw [← Category.comp_id (ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) ↘
    Spec (.of (FractionRing (PowerSeries k')))), ← Category.comp_id (traitGenericPointToSpec k')]
    at h
  exact h

variable {k'} {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)]

/-- **The dualizing map of a model with a proper coordinate to `ℙ¹_S`** (blueprint
`sec-Base-change-for-nearby-cycles` (4) for a coordinate): for a proper trait model `M` of `X₁`
over the generic base `(η, X₁, 𝟙)` with full geometric generic fibre, and a morphism of models
`b : M ⟶ ℙ¹_S` over proper `b_η : X₁ ⟶ ℙ¹_η` and `b_s : X' ⟶ ℙ¹_{k'}`,
`θ_M = Ψ_M(ρ)⁻¹ ∘ β_b(ω_{ℙ¹_η}) ∘ Rb_s^!(θ_{ℙ¹_S}) ∘ ρ'`, for the exceptional exchange `β_b` of the
inverse `ν_b` of the proper exchange `χ_b`. -/
theorem NearbyDualizingDataOfGenericBase.θ_eq_of_projectiveLine
    (D : NearbyDualizingDataOfGenericBase k' ℓ)
    {X₁ : Over (Spec (.of (FractionRing (PowerSeries k'))))} [LocallyOfFiniteType X₁.hom]
    [QuasiCompact X₁.hom] [IsSeparated X₁.hom] {X' : Over (Spec (.of k'))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint X').left]
    {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (hM : M.IsTraitModelOfGenericBase X₁ (𝟙 _) q g) [IsProper q]
    (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ 𝟙 _))
    (b₁ : X₁ ⟶ overProjectiveLine (point (FractionRing (PowerSeries k')))) [IsProper b₁.left]
    (b₂ : X' ⟶ overProjectiveLine (point k')) [IsProper b₂.left]
    (b : M.Hom (projectiveLineModel k') b₁.left b₂.left)
    (hq : q = b.total ≫ (ProjectiveLine (trait k') ↘ trait k'))
    (hg : g = b.generic ≫
      (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k')))) :
    D.θ hM =
      ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).mapIso
          (upperShriekDualizingComplexIso ℓ b₁)).inv ≫
        (exceptionalExchange ℓ b₁ b₂
          ((isTraitModelOfGenericBase_projectiveLineModel k').properCompactSupportExchange ℓ hM
            (isPullback_projectiveLineModel_ε k') hMgen b₁ b₂ b hq hg)).app
          (dualizingComplex ℓ (overProjectiveLine (point (FractionRing (PowerSeries k'))))) ≫
        (boundedConstructibleUpperShriek ℓ b₂).map
          (D.θ (isTraitModelOfGenericBase_projectiveLineModel k')) ≫
        (upperShriekDualizingComplexIso ℓ b₂).hom := by
  rw [Iso.eq_inv_comp]
  exact D.θ_comp_law (isTraitModelOfGenericBase_projectiveLineModel k') hM
    (isPullback_projectiveLineModel_ε k') hMgen b₁ b₂ b hq hg

end ProjectiveLine

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
