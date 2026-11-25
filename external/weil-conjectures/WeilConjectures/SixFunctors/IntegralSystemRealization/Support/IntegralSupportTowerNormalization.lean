/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralBasicRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenMateNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.Support.IntegralSupportStrictTowerComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Support.IntegralSupportProjectionTransport

import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization

/-! # Whole compact-support tower normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem scalarProjection_comp
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A B Q Q' : C} {V : D}
    (a : A ⟶ B) (b : B ⟶ Q) (τ : Q ⟶ Q')
    (r : F.obj Q' ⟶ V) (c : F.obj Q ⟶ V)
    (p : A ⟶ G.obj V) (hτ : F.map τ ≫ r = c)
    (ha : a ≫ b ≫ adj.homEquiv _ _ c = p) :
    F.map (a ≫ b ≫ τ) ≫ r = (adj.homEquiv _ _).symm p := by
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Functor.map_comp, Category.assoc,
    Adjunction.homEquiv_naturality_left]
  rw [Functor.map_comp, Category.assoc, hτ, Adjunction.homEquiv_naturality_left]
  exact ha

/-- The fixed compactification composite has the recorded strict tower and the
projection-normalized integral compact-support comparison.
Source: Stacks 0941 and 0D6E; primitive realization Step 5 and the normalized
compact-support realization
(blueprint: lem-sf-integral-support-tower-normalization).

Proof: identify o.extension and o.direct with the canonical simultaneous open and
proper functors through their unit-normalized ordinary adjunctions. Compose these
whole-system comparisons with the fixed reduction calculus. The construction of the
recorded compact-support tower then gives the strict derived-tower comparison.
Its finite evaluations are the open/proper evaluation factors, followed by the
reduction evaluation, exactly as displayed. The coefficient-restriction cocycle gives
all pairs of quotient transitions. Apply total limit to the whole comparison, retaining
its projections. Insert the inverse actual unit of the completed open extension.
The normalized compact-support realization identifies the resulting integral image
with the recorded constructible functor. Its defining scalar-adjoint projection
identity gives the last equation. No equality of derived arrows is inferred merely
from their finite evaluations. The same construction works for zero inputs and empty
opens. -/
theorem integralSupportTowerNormalization (D : FiniteFieldDatum.{u})
    (o : Operations l E) (model : RealizationModel l E o) :
∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hl : IsUnit (l : D.k)) (c : Compactification f),
    ∃ (T : Integral l E X ⥤ coefficientSequenceRestrictedDerived l E Y)
      (e : ∀ n : ℕ,
        T ⋙ coefficientConstantTowerEvaluation l E Y n ≅ compactSupportRestrictedLevel l E c n),
      T = Classical.choose (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E D.k X Y f hl c))).2.2 ∧
      HEq e (Classical.choose (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
          (exists_compactSupportReductionTower l E D.k X Y f hl c))).2.2).2).2) ∧
      (∀ (m n : ℕ) (h : n ≤ m)
        (K : (basicSupportDomain l E o c).FullSubcategory),
        (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
            (T.obj K.obj) ≫ (e n).hom.app K.obj =
          (e m).hom.app K.obj ≫ compactSupportRestrictedTransition l E c m n h K.obj) ∧
      ∃ (tower : (basicSupportDomain l E o c).ι ⋙ (calculus l E X).reduction ⋙
          Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ⋙
            coefficientSequenceDerivedRestriction l E Y ≅ (basicSupportDomain l E o c).ι ⋙ T)
        (d : (basicSupportDomain l E o c).ι ⋙ (calculus l E X).reduction ⋙
          Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ⋙
            coefficientSequenceLimit l E Y ≅
          basicSupportInput l E o c ⋙ sfCompactSupportFiniteIntegralFunctor l D.k hl c E ⋙
            (sfIntegralConstructible l E Y).ι),
        ∃ hunit : ∀ K : (basicSupportDomain l E o c).FullSubcategory,
          IsIso ((calculus l E c.Z).adjunction.unit.app ((ringedOpen l E c.i).obj K.obj)),
        (∀ K : (basicSupportDomain l E o c).FullSubcategory,
          d.hom.app K =
            (model.push l E c.g).hom.app
              ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K.obj)) ≫
            (ringedPush l E c.g).map
              ((coefficientSequenceLimit l E c.Z).map
                  ((model.openReduction l E c.i).app K.obj) ≫
                @inv _ _ _ _ ((calculus l E c.Z).adjunction.unit.app
                  ((ringedOpen l E c.i).obj K.obj)) (hunit K)) ≫
            (sfQcqsCompactSupportRealization l E D.k hl c).hom.app
              ((basicSupportInput l E o c).obj K)) ∧
        (∀ (K : (basicSupportDomain l E o c).FullSubcategory) (n : ℕ),
          (coefficientConstantTowerEvaluation l E Y n).map (tower.hom.app K) ≫
            (e n).hom.app K.obj =
          (coefficientRestrictedEvaluationIso l E Y n).hom.app
              ((Operations.push l E o c.g).obj
                ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K.obj))) ≫
            (scalarReductionDerivedRestriction l E Y n).map
              ((supportEvaluation l E o c n).hom.app ((calculus l E X).reduction.obj K.obj) ≫
                (sfAmbientCompactSupportCandidate
                  (Padic.coefficientExtensionRing l E (n + 1)) c).map
                  (((calculus l E X).reductionEvaluation n).hom.app K.obj))) ∧
        (∀ (K : (basicSupportDomain l E o c).FullSubcategory) (n : ℕ),
          (scalarReductionDerivedExtension l E Y n).map (d.hom.app K) ≫
            (sfCompactSupportFiniteReductionIso l D.k hl c E
              ((basicSupportInput l E o c).obj K) n).hom =
          ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
            ((coefficientSequenceProjection l E Y n).app
                ((Operations.push l E o c.g).obj
                  ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K.obj))) ≫
              (scalarReductionDerivedRestriction l E Y n).map
                ((supportEvaluation l E o c n).hom.app ((calculus l E X).reduction.obj K.obj) ≫
                  (sfAmbientCompactSupportCandidate
                    (Padic.coefficientExtensionRing l E (n + 1)) c).map
                    (((calculus l E X).reductionEvaluation n).hom.app K.obj)))) := by
  classical
  intro X Y f _ _ _ _ _ _ _ _ _ _ hl c
  let H := exists_compactSupportReductionTower l E D.k X Y f hl c
  let HT := H.choose_spec.choose_spec.2.2
  let T : Integral l E X ⥤ coefficientSequenceRestrictedDerived l E Y := HT.choose
  let He := HT.choose_spec.2.choose_spec.2
  let e : ∀ n : ℕ,
      T ⋙ coefficientConstantTowerEvaluation l E Y n ≅ compactSupportRestrictedLevel l E c n :=
    He.choose
  have htransition := He.choose_spec.1
  have hT : T = Classical.choose (Classical.choose_spec (Classical.choose_spec
      (exists_compactSupportReductionTower l E D.k X Y f hl c))).2.2 := rfl
  have he : HEq e (Classical.choose (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E D.k X Y f hl c))).2.2).2).2) := HEq.rfl
  have hw := integralSupportStrictTowerComparison l E D.k o f hl c T e hT he
  obtain ⟨wholeTower, hwholeTower⟩ := hw
  let tower := Functor.isoWhiskerLeft (basicSupportDomain l E o c).ι wholeTower
  let : QuasiCompact c.i := compactOpenQuasiCompact c inferInstance
  have hx : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hl.map
      ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop).hom
  have hz : IsUnit (l : Γ(c.Z, ⊤)) := by
    simpa only [map_natCast] using hl.map
      ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (c.g ≫ (Y ↘ Spec (.of D.k))).appTop).hom
  have hopen (K : (basicSupportDomain l E o c).FullSubcategory) :=
    integralOpenMateNormalization l E o model c.i hx hz K.obj
      K.property.1.1 K.property.1.2.1 K.property.2
  let hunit := fun K ↦ (hopen K).1
  let P := basicSupportDomain l E o c
  let r := Functor.whiskerLeft P.ι (model.openReduction l E c.i)
  have : ∀ K, IsIso (r.app K) := fun K ↦ (hopen K).2
  let η := Functor.whiskerLeft (P.ι ⋙ ringedOpen l E c.i)
    (calculus l E c.Z).adjunction.unit
  have : ∀ K, IsIso (η.app K) := hunit
  let openIso := Functor.isoWhiskerRight
    (NatIso.ofComponents (fun K ↦ asIso (r.app K)) (fun v ↦ r.naturality v))
    (coefficientSequenceLimit l E c.Z) ≪≫
      (NatIso.ofComponents (fun K ↦ asIso (η.app K)) (fun v ↦ η.naturality v)).symm
  let d := Functor.isoWhiskerLeft
      (P.ι ⋙ (calculus l E X).reduction ⋙ Operations.shriek l E o c.i)
      (model.push l E c.g) ≪≫
    Functor.isoWhiskerRight openIso (ringedPush l E c.g) ≪≫
    Functor.isoWhiskerLeft (basicSupportInput l E o c)
      (sfQcqsCompactSupportRealization l E D.k hl c)
  have hd (K : P.FullSubcategory) :
      d.hom.app K =
        (model.push l E c.g).hom.app
          ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K.obj)) ≫
        (ringedPush l E c.g).map
          ((coefficientSequenceLimit l E c.Z).map
              ((model.openReduction l E c.i).app K.obj) ≫
            @inv _ _ _ _ ((calculus l E c.Z).adjunction.unit.app
              ((ringedOpen l E c.i).obj K.obj)) (hunit K)) ≫
        (sfQcqsCompactSupportRealization l E D.k hl c).hom.app
          ((basicSupportInput l E o c).obj K) := by
    simp only [d, openIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Iso.symm_hom, NatIso.ofComponents_hom_app,
      NatIso.ofComponents_inv_app, asIso_hom, asIso_inv]
    rfl
  refine ⟨T, e, rfl, heq_of_eq rfl, ?_, tower, d, hunit, hd, ?_, ?_⟩
  · intro m n h K
    exact htransition m n h K.obj
  · intro K n
    exact hwholeTower K.obj n
  · intro K n
    let a := (model.push l E c.g).hom.app
      ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K.obj))
    let b := (ringedPush l E c.g).map
      ((coefficientSequenceLimit l E c.Z).map ((model.openReduction l E c.i).app K.obj) ≫
        @inv _ _ _ _ ((calculus l E c.Z).adjunction.unit.app
          ((ringedOpen l E c.i).obj K.obj)) (hunit K))
    let τ := (sfQcqsCompactSupportRealization l E D.k hl c).hom.app
      ((basicSupportInput l E o c).obj K)
    have ha : d.hom.app K = a ≫ b ≫ τ := hd K
    refine (congrArg
      (fun v ↦ (scalarReductionDerivedExtension l E Y n).map v ≫
        (sfCompactSupportFiniteReductionIso l D.k hl c E
          ((basicSupportInput l E o c).obj K) n).hom) ha).trans ?_
    refine scalarProjection_comp
      (derivedScalarExtensionRestrictionAdjunction l E Y n).choose a b τ _ _ _
      ((sfQcqsCompactSupportRealization_spec l E D.k hl c)
        ((basicSupportInput l E o c).obj K) n) ?_
    exact integralSupportProjectionTransport l E o model c K.obj (hunit K) n

end WeilConjectures.IntegralSystemRealization
