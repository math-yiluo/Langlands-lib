/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import all WeilConjectures.SmoothPurity.Supporting.NativeConstantRestrictionAcyclicity
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardSites
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionEvaluationAcyclic
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Acyclicity after restriction of strict coefficient systems

Source: Stacks Project, Cohomology on Sites, Tag 0D6E, on sequence ringed topoi.
(blueprint: lem-pur-completed-coefficient-system-restriction-acyclic).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
universe t u s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward

open SheafOfModules

private instance coefficientSiteSmall (W : Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf.{u, t, t + 1} _

private instance sequenceSmall (W : Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} (ℕ × W.ProEt) := essentiallySmallSelf _

private instance sequenceAbSheafify (W : Scheme.{t}) :
    HasSheafify (coefficientSequenceTopology (ProEt.topology W))
      AddCommGrpCat.{max u (t + 1)} := hasSheafifyEssentiallySmallSite _ _

private instance sequenceAbLocallyBijective (W : Scheme.{t}) :
    (coefficientSequenceTopology (ProEt.topology W)).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finiteIso_canonical (W : Scheme.{t}) (source : SystemRestrictionData l E W)
    (n : ℕ) : source.finiteIso n = finiteCoefficientIso l E W n := by
  let V := sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let a := V.preimage (source.finiteIso n).hom
  let b := V.preimage (finiteCoefficientIso l E W n).hom
  have hab : a = b := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology W) _ _
      (integralCoefficientCommRingSheaf l E W n).property
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha := source.finiteIso_generator n U x
    have hb := finiteCoefficientIso_generator l E W n U x
    have hma := V.map_preimage (source.finiteIso n).hom
    have hmb := V.map_preimage (finiteCoefficientIso l E W n).hom
    have h := ha.trans hb.symm
    rw [← hma, ← hmb] at h
    exact h
  apply Iso.ext
  have h := congrArg V.map hab
  simpa only [a, b, Functor.map_preimage] using h

private theorem identity_sections_comm
    {A B A' B' : Type s} [Zero A] [Zero B]
    (e : A → A') (d : B → B') (f : A → B) (g : A' → B')
    (he : ∀ x, HEq (e x) x) (hd : ∀ x, HEq (d x) x) (hf : HEq f g) (x : A) :
    g (e x) = d (f x) := by
  have hA : A' = A := type_eq_of_heq (he 0)
  have hB : B' = B := type_eq_of_heq (hd 0)
  subst A' B'
  have he' : e x = x := eq_of_heq (he x)
  have hd' : d (f x) = f x := eq_of_heq (hd (f x))
  rw [he', hd', ← eq_of_heq hf]

private def towerFunctorIso {A B : Type*} [Category* A] [Category* B]
    {F G : A ⥤ ℕᵒᵖ ⥤ B}
    (ε : ∀ M n, (F.obj M).obj (op n) ≅ (G.obj M).obj (op n))
    (hs : ∀ M n, (F.obj M).map (homOfLE (Nat.le_succ n)).op ≫ (ε M n).hom =
      (ε M (n + 1)).hom ≫ (G.obj M).map (homOfLE (Nat.le_succ n)).op)
    (hn : ∀ {M N} (f : M ⟶ N) n, (F.map f).app (op n) ≫ (ε N n).hom =
      (ε M n).hom ≫ (G.map f).app (op n)) : F ≅ G :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun n ↦ ε M n.unop)
    (fun {_ _} f ↦ (NatTrans.ofOpSequence (fun n ↦ (ε M n).hom) (hs M)).naturality f)) (by
      intro M N f
      ext n
      exact hn f n.unop)

section AbstractCoefficientSections
universe a v w
variable {C : Type a} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Type w} [CommRing O] {ell : O}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J CommRingCat.{w}]

private theorem iterated_successor_sections
    (M : CoefficientSystem (J := J) O ell) (n : ℕ) (U : Cᵒᵖ)
    (x : (M.level (n + 1)).val.obj U) :
    (coefficientIteratedTransition M (Nat.le_succ n)).val.app U x =
      (M.transition n).val.app U x :=
  congrArg (fun q ↦ q.val.app U x) (coefficientIterated_succ M n)

end AbstractCoefficientSections

private def modelRings (W : Scheme.{t}) :=
  coefficientRings.{t + 1, t, max u (t + 1)} (J := ProEt.topology W)
    (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E)

private def sourceLeg (W : Scheme.{t}) (source : SystemRestrictionData l E W) (n : ℕ) :
    R l E W ⟶ modelRing l E W n :=
  projection l E W n ≫ (source.finiteIso n).inv

private theorem sourceLeg_transition (W : Scheme.{t}) (source : SystemRestrictionData l E W)
    (n : ℕ) : sourceLeg l E W source (n + 1) ≫ modelTransition l E W n =
      sourceLeg l E W source n := by
  dsimp only [sourceLeg]
  rw [finiteIso_canonical l E W source n, finiteIso_canonical l E W source (n + 1)]
  exact systemLeg_transition l E W n

-- Retain the abstract ring sheaves during module-functor unification.
attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap
  integralCoefficientSheaf completedIntegralCoefficientSheafUnrestricted

private def completedModelCone (W : Scheme.{t}) (source : SystemRestrictionData l E W) :
    (Functor.const ℕᵒᵖ).obj (R l E W) ⟶
      modelRings l E W ⋙ sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) :=
  NatTrans.ofOpSequence (fun n ↦ sourceLeg l E W source n) (by
    intro n
    exact (sourceLeg_transition l E W source n).symm)

private def sequenceScalarMap (W : Scheme.{t}) (source : SystemRestrictionData l E W) :
    NativeConstantModel.sequenceRing (ProEt.topology W) (R l E W) ⟶
      (sheafCompose (coefficientSequenceTopology (ProEt.topology W))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (systemSequenceRing.{t + 1, t, max u (t + 1)} (modelRings l E W)) where
  hom :=
    { app U := ((completedModelCone l E W source).app (op U.unop.1)).hom.app (op U.unop.2)
      naturality := by
        intro U V f
        have hn := congrArg (fun k ↦ k.hom.app (op U.unop.2))
          ((completedModelCone l E W source).naturality f.unop.1.op)
        change ((completedModelCone l E W source).app (op V.unop.1)).hom.app (op U.unop.2) =
          ((completedModelCone l E W source).app (op U.unop.1)).hom.app (op U.unop.2) ≫
            ((modelRings l E W ⋙ sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat RingCat)).map f.unop.1.op).hom.app (op U.unop.2) at hn
        change (R l E W).obj.map f.unop.2.op ≫
            ((completedModelCone l E W source).app (op V.unop.1)).hom.app (op V.unop.2) =
          ((completedModelCone l E W source).app (op U.unop.1)).hom.app (op U.unop.2) ≫
            (((modelRings l E W ⋙ sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat RingCat)).map f.unop.1.op).hom.app (op U.unop.2) ≫
              ((modelRings l E W ⋙ sheafCompose (ProEt.topology W)
                (forget₂ CommRingCat RingCat)).obj (op V.unop.1)).obj.map f.unop.2.op)
        rw [← Category.assoc, ← hn]
        exact ((completedModelCone l E W source).app (op V.unop.1)).hom.naturality f.unop.2.op }

private def sourceSequenceEquivalence (W : Scheme.{t}) :
    Systems l E W ≌ systemSequenceModules.{t + 1, t, max u (t + 1)} (modelRings l E W) :=
  (coefficientSystemEquivalence (J := ProEt.topology W)
    (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E)).trans
      (strictSystemSequenceEquivalence.{t + 1, t, max u (t + 1)} (modelRings l E W))

private def restrictionLevelIso (W : Scheme.{t}) (source : SystemRestrictionData l E W)
    (n : ℕ) : source.systemRestriction ⋙ (CategoryTheory.evaluation ℕᵒᵖ _).obj (op n) ≅
      coefficientEvaluation (J := ProEt.topology W)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
          SheafOfModules.restrictScalars (sourceLeg l E W source n) :=
  source.systemEvaluation n ≪≫ Functor.isoWhiskerLeft _
    (normalizedDVRRestrictionCompIso (projection l E W n) (source.finiteIso n).inv)

private theorem restrictionLevelIso_sections (W : Scheme.{t})
    (source : SystemRestrictionData l E W) (n : ℕ) (M : Systems l E W)
    (U : W.ProEtᵒᵖ) (x : ((source.systemRestriction.obj M).obj (op n)).val.obj U) :
    HEq (((restrictionLevelIso l E W source n).hom.app M).val.app U x) x :=
  source.systemEvaluation_identity n M U x

private def sequenceLevelIso (W : Scheme.{t}) (source : SystemRestrictionData l E W)
    (M : Systems l E W) (n : ℕ) :
    ((((sourceSequenceEquivalence l E W).functor ⋙
      SheafOfModules.restrictScalars (sequenceScalarMap l E W source) ⋙
        NativeConstantModel.sequenceCurry (ProEt.topology W) (R l E W)).obj M).obj
          (op n)) ≅
      (coefficientEvaluation (J := ProEt.topology W)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
          SheafOfModules.restrictScalars (sourceLeg l E W source n)).obj M :=
  NativeConstantModel.sequenceIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
      intro U V f
      ext x
      change (M.level n).val.map f
        (((coefficientToStrictObj M).transition (le_refl n)).val.app U x) =
          (M.level n).val.map f x
      rw [(coefficientToStrictObj M).identity n U x]))

private def restrictionTowerFunctor (W : Scheme.{t})
    (source : SystemRestrictionData l E W) : Systems l E W ⥤ ℕᵒᵖ ⥤ Mod W (R l E W) :=
  (sourceSequenceEquivalence l E W).functor ⋙
    SheafOfModules.restrictScalars (sequenceScalarMap l E W source) ⋙
      NativeConstantModel.sequenceCurry (ProEt.topology W) (R l E W)

private def restrictionTowerComponentIso (W : Scheme.{t})
    (source : SystemRestrictionData l E W) (M : Systems l E W) (n : ℕ) :
    (source.systemRestriction.obj M).obj (op n) ≅
      ((restrictionTowerFunctor l E W source).obj M).obj (op n) :=
  (restrictionLevelIso l E W source n).app M ≪≫ (sequenceLevelIso l E W source M n).symm

private theorem restrictionTowerComponentIso_sections (W : Scheme.{t})
    (source : SystemRestrictionData l E W) (M : Systems l E W) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : ((source.systemRestriction.obj M).obj (op n)).val.obj U) :
    HEq ((restrictionTowerComponentIso l E W source M n).hom.val.app U x) x :=
  restrictionLevelIso_sections l E W source n M U x

attribute [local irreducible] restrictionTowerComponentIso

private theorem restrictionTowerFunctor_successor (W : Scheme.{t})
    (source : SystemRestrictionData l E W) (M : Systems l E W) (n : ℕ)
    (U : W.ProEtᵒᵖ) :
    HEq (fun y ↦ ((((restrictionTowerFunctor l E W source).obj M).map
      (homOfLE (Nat.le_succ n)).op).val.app U) y)
      (fun y ↦ ((M.transition n).val.app U) y) := by
  apply heq_of_eq
  funext y
  change (M.level n).val.map (𝟙 U)
    ((coefficientIteratedTransition M (Nat.le_succ n)).val.app U y) =
      (M.transition n).val.app U y
  have hs := iterated_successor_sections M n U y
  exact (congrArg (fun z : (M.level n).val.obj U ↦
    (M.level n).val.map (𝟙 U) z) hs).trans
      (ConcreteCategory.congr_hom ((M.level n).val.presheaf.map_id U) _)

private theorem restrictionTowerFunctor_map (W : Scheme.{t})
    (source : SystemRestrictionData l E W) (M N : Systems l E W) (f : M ⟶ N) (n : ℕ)
    (U : W.ProEtᵒᵖ) :
    HEq (fun y ↦ ((((restrictionTowerFunctor l E W source).map f).app (op n)).val.app U) y)
      (fun y ↦ ((f.app n).val.app U) y) := HEq.rfl

attribute [local irreducible] restrictionTowerFunctor

private def restrictionTowerIso (W : Scheme.{t}) (source : SystemRestrictionData l E W) :
    source.systemRestriction ≅ restrictionTowerFunctor l E W source := by
  let ε := restrictionTowerComponentIso l E W source
  have he := restrictionTowerComponentIso_sections l E W source
  refine towerFunctorIso (F := source.systemRestriction)
    (G := restrictionTowerFunctor l E W source) ε ?_ ?_
  · intro M n
    ext U x
    exact (identity_sections_comm _ _ _ _ (he M (n + 1) U) (he M n U)
      ((source.systemTransition M n U).trans
        (restrictionTowerFunctor_successor l E W source M n U).symm) x).symm
  · intro M N f n
    ext U x
    exact (identity_sections_comm _ _ _ _ (he M n U) (he N n U)
      ((source.systemMap M N f n U).trans
        (restrictionTowerFunctor_map l E W source M N f n U).symm) x).symm

private def restrictionSequenceIso (W : Scheme.{t})
    (source : SystemRestrictionData l E W) :
    (sourceSequenceEquivalence l E W).functor ⋙
        SheafOfModules.restrictScalars (sequenceScalarMap l E W source) ≅
      source.systemRestriction ⋙
        (NativeConstantModel.sequenceEquivalence (ProEt.topology W) (R l E W)).inverse := by
  let e := NativeConstantModel.sequenceEquivalence (ProEt.topology W) (R l E W)
  let F := (sourceSequenceEquivalence l E W).functor ⋙
    SheafOfModules.restrictScalars (sequenceScalarMap l E W source)
  let d : F ⋙ e.functor ≅ source.systemRestriction := by
    have h := (restrictionTowerIso l E W source).symm
    unfold restrictionTowerFunctor at h
    exact h
  exact F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F e.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight d e.inverse

private theorem restricted_system_sections_quasiIso (W : Scheme.{t})
    (source : SystemRestrictionData l E W)
    (I : CochainComplex (Systems l E W) ℤ) [I.IsKInjective]
    (K : CochainComplex (ℕᵒᵖ ⥤ Mod W (R l E W)) ℤ) [K.IsKInjective]
    (j : (source.systemRestriction.mapHomologicalComplex (.up ℤ)).obj I ⟶ K) [QuasiIso j]
    (n : ℕ) (U : W.ProEt) :
    QuasiIso (((SheafOfModules.toSheaf (R l E W) ⋙
      sheafToPresheaf (ProEt.topology W) AddCommGrpCat.{max u (t + 1)} ⋙
      (CategoryTheory.evaluation _ _).obj (op U)).mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j).app (op n))) := by
  let eS := sourceSequenceEquivalence l E W
  let eR := NativeConstantModel.sequenceEquivalence (ProEt.topology W) (R l E W)
  let ES := eS.functor
  let ER := eR.inverse
  let r := SheafOfModules.restrictScalars (sequenceScalarMap l E W source)
  have : ES.Additive := Functor.additive_of_preserves_binary_products ES
  have : ER.Additive := Functor.additive_of_preserves_binary_products ER
  have : ES.IsEquivalence := inferInstanceAs eS.functor.IsEquivalence
  have : ER.IsEquivalence := inferInstanceAs eR.inverse.IsEquivalence
  let α := restrictionSequenceIso l E W source
  let αc := Functor.mapHomologicalComplexCompIso (F := ES) (G := r) α (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (source.systemRestriction ⋙ ER)) (.up ℤ)).symm
  let I' := (ES.mapHomologicalComplex (.up ℤ)).obj I
  let K' := (ER.mapHomologicalComplex (.up ℤ)).obj K
  let j' : (r.mapHomologicalComplex (.up ℤ)).obj I' ⟶ K' :=
    αc.hom.app I ≫ (ER.mapHomologicalComplex (.up ℤ)).map j
  have : CochainComplex.IsKInjective I' := inferInstance
  have : CochainComplex.IsKInjective K' := inferInstance
  have : QuasiIso j' := by dsimp only [j']; infer_instance
  let T := coefficientSequenceTopology (ProEt.topology W)
  let B := NativeConstantModel.sequenceRing (ProEt.topology W) (R l E W)
  let D := (sheafCompose T (forget₂ CommRingCat.{max u (t + 1)}
    RingCat.{max u (t + 1)})).obj
      (systemSequenceRing.{t + 1, t, max u (t + 1)} (modelRings l E W))
  have hB (V : (ℕ × W.ProEt)ᵒᵖ) (x y : B.obj.obj V) : x * y = y * x := by
    exact completedIntegralCoefficient_mul_commUnrestricted l E W (op V.unop.2) x y
  have hD (V : (ℕ × W.ProEt)ᵒᵖ) (x y : D.obj.obj V) : x * y = y * x := by
    exact mul_comm (show (systemSequenceRing.{t + 1, t, max u (t + 1)}
      (modelRings l E W)).obj.obj V from x) y
  let ev := SheafOfModules.toSheaf
      (NativeConstantModel.sequenceRing (ProEt.topology W) (R l E W)) ⋙
    sheafToPresheaf T AddCommGrpCat.{max u (t + 1)} ⋙
      (CategoryTheory.evaluation _ _).obj (op (n, U))
  have hq : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map j') :=
    coefficientRestrictionSectionsEvaluation_quasiIso.{t + 1, t, u} B D hB hD
      (sequenceScalarMap l E W source) I' K' j' (n, U)
  have hq' : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map
      ((ER.mapHomologicalComplex (.up ℤ)).map j)) := by
    dsimp only [j'] at hq
    rw [Functor.map_comp] at hq
    exact quasiIso_of_comp_left
      ((ev.mapHomologicalComplex (.up ℤ)).map (αc.hom.app I))
      ((ev.mapHomologicalComplex (.up ℤ)).map ((ER.mapHomologicalComplex (.up ℤ)).map j))
  exact hq'

/-- Restricting a K-injective system gives an acyclic input for tower direct image.
This concerns a fixed derived unit, and constructs no system direct-image functor.
Source: Stacks Project, Tag 0D6E, lemma-derived-pushforward-composition, applied to
restriction along the completed projection diagram followed by direct image
(blueprint: lem-pur-completed-coefficient-system-restriction-acyclic).

Proof: Present strict systems as module sheaves over the quotient-ring diagram on
the sequence site. The completed projections give a map from the constant completed
ring diagram to the quotient-ring diagram. The generator normalization of finiteIso,
together with systemEvaluation_identity, systemTransition and systemMap, identifies
source.systemRestriction with scalar restriction along this map. This identification
retains every transition, rather than just identifying the separate evaluations.
Transport to an equivalent small site in the coefficient universe. Apply the normalized
ringed-topos derived composition theorem to this scalar-restriction morphism followed
by the completed-module tower direct image. At a K-injective system I, the unit for
the composite is invertible. The restriction is exact, so its unit is invertible on
all complexes. In the composition-unit equation, cancel this latter unit and the
composition isomorphism. The tower-image unit at the restricted I is consequently
invertible. Finally the unique isomorphism between normalized right derived models
intertwines this unit with towerImage.unit; transport back to the original sites.
This uses acyclicity, and does not assert that restriction preserves K-injectives. -/
theorem systemRestriction_push_acyclic {X Y : Scheme.{t}} (f : X ⟶ Y)
    (source : SystemRestrictionData l E X)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    [(push f c).Additive]
    (towerImage : RightImage
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)))
    (I : CochainComplex (Systems l E X) ℤ) (hI : I.IsKInjective) :
    IsIso (towerImage.unit.app
      ((source.systemRestriction.mapHomologicalComplex (.up ℤ)).obj I)) := by
  classical
  have := hI
  let L := (source.systemRestriction.mapHomologicalComplex (.up ℤ)).obj I
  obtain ⟨K, hK, j, hj, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective L
  have := hK
  have := hq
  have hpush : QuasiIso
      ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).mapHomologicalComplex
        (.up ℤ)).map j) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
    intro n
    apply quasiIso_of_sectionsOfUniverses.{t + 1, t, u}
    intro U
    exact restricted_system_sections_quasiIso l E X source I K j n.unop
      ((proEtaleBaseChange f).obj U)
  have := towerImage.computes K hK
  have hn := towerImage.unit.naturality j
  dsimp only [Functor.comp_map] at hn
  have hi : IsIso (towerImage.unit.app L ≫
      towerImage.functor.map (DerivedCategory.Q.map j)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (towerImage.functor.map (DerivedCategory.Q.map j))

end WeilConjectures.CompletedCoefficientPushforward
