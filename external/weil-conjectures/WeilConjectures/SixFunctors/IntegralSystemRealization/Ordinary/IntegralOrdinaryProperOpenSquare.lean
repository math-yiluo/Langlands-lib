/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryCanonicalIsoSquare
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryProperOpenCalculus

/-! # Ordinary coefficient squares for proper/open interchange

Source: blueprint fix-prop-coherence, the coefficient comparisons of individual maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
attribute [local implicit_reducible] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  integralOperationsCommHasDerivedCategory
attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleCanonicalTensorComparison ringedPullComp
  ringedRestrictFactor restrictFactor properOpenLambda ringedProperOpenLambda
  ringedOpenComp Compositors.openComp openCongr ringedOpenCongr ordinaryPushReduction
  RingedOpenComparisons.unit OpenComparisons.unit

attribute [local implicit_reducible] PurCompactSupport.completed
  coefficientSequenceHasDerived scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralCompletedRingHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev functorSource {A B : Type*} [Category A] [Category B] (_ : A ⥤ B) := A
private abbrev functorTarget {A B : Type*} [Category A] [Category B] (_ : A ⥤ B) := B

private abbrev nativeIntegral (W : Scheme.{u}) :=
  functorSource ((calculus l E W).reduction)
private abbrev nativeSystem (W : Scheme.{u}) :=
  functorTarget ((calculus l E W).reduction)

-- Fix the category's own quiver when stating normalized component boundaries.
private abbrev systemHom (W : Scheme.{u}) (A B : System l E W) :=
  @Quiver.Hom _ (inferInstance : Category (System l E W)).toQuiver A B

private theorem cartesian_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {V W Z : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i]
    (L : Integral l E V) :
    (a.realizationModel.reductionPull i).hom.app ((ringedPush l E p).obj L) ≫
        (pull l E i).map ((ordinaryPushReduction l E o a.realizationModel p).app L) ≫
        (cartesianConjugate l E o a.compositors a.openComparisons p i).hom.app
          ((calculus l E V).reduction.obj L) =
      (calculus l E W).reduction.map
          ((ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel (pullback.snd p i)).app
          ((ringedPull l E (pullback.fst p i)).obj L) ≫
        (Operations.push l E o (pullback.snd p i)).map
          ((a.realizationModel.reductionPull (pullback.fst p i)).hom.app L) := by
  let q := pullback.snd p i
  let b := pullback.fst p i
  let χ₁ := TwoSquare.vComp (a.realizationModel.openReduction l E i)
    (a.realizationModel.reductionPull p).inv
  let χ₂ := TwoSquare.vComp (a.realizationModel.reductionPull q).inv
    (a.realizationModel.openReduction l E b)
  let α := (a.ringedOpenComparisons.beta q b i p
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip).inv
  let β := (a.openComparisons.beta q b i p
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip).inv
  have h : χ₁.whiskerRight β = χ₂.whiskerLeft α := by
    apply NatTrans.ext
    funext M
    have hi : IsIso ((a.realizationModel.openReduction l E i).app M) :=
      GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel i M
    have hi' : IsIso (((mateEquiv (ringedOpenAdj l E i) (o.extension i).adj).symm
        (a.realizationModel.reductionPull i).hom).app M) := hi
    have hb : IsIso ((a.realizationModel.openReduction l E b).app
        ((ringedPull l E q).obj M)) :=
      GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel b _
    have hb' : IsIso (((mateEquiv (ringedOpenAdj l E b) (o.extension b).adj).symm
        (a.realizationModel.reductionPull b).hom).app
          ((ringedPull l E q).obj M)) := hb
    let ζ₁ := (a.realizationModel.reductionPull p).hom.app ((ringedOpen l E i).obj M) ≫
      (pull l E p).map (inv ((a.realizationModel.openReduction l E i).app M))
    let ζ₂ := inv ((a.realizationModel.openReduction l E b).app
        ((ringedPull l E q).obj M)) ≫
      (Operations.shriek l E o b).map ((a.realizationModel.reductionPull q).hom.app M)
    have hu := GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E i)
      (o.extension i).adj (a.realizationModel.reductionPull i).hom
      (𝟙 ((calculus l E W).reduction.obj M))
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hu
    have hs := open_beta_inverse_square l E o a q b i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip M
      ((calculus l E W).reduction.obj M) (𝟙 _)
      (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E i).app M))
      (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id,
        RealizationModel.openReduction, ringedOpenAdj,
        Operations.shriek, Category.comp_id] using! hu)
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hs
    erw [GeneratorReduction.inverseOrZero_eq_inv] at hs
    have hs' : ζ₂ ≫ β.app ((calculus l E W).reduction.obj M) =
        (calculus l E V).reduction.map (α.app M) ≫ ζ₁ := by
      simpa only [ζ₁, ζ₂, α, β, ringedOpenAdj, RealizationModel.openReduction,
        Operations.shriek,
        GeneratorReduction.inverseOrZero_eq_inv, CategoryTheory.Functor.map_id,
        Category.comp_id, Category.assoc] using! hs
    have hx := GeneratorReduction.inverse_square
      ((calculus l E V).reduction.map (α.app M))
      (β.app ((calculus l E W).reduction.obj M)) ζ₂ ζ₁ hs'.symm
    simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
      TwoSquare.mk, χ₁, χ₂, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, ζ₁, ζ₂, GeneratorReduction.inverseOrZero_eq_inv,
      IsIso.inv_comp, ← CategoryTheory.Functor.map_inv, NatIso.inv_hom_app, IsIso.inv_inv,
      Category.id_comp, Category.comp_id, Functor.comp_obj, Category.assoc] using! hx
  have hm := ordinaryProperOpenConjugateSquare
    ((ringedOpenAdj l E i).comp (ringedAdj l E p))
    ((ringedAdj l E q).comp (ringedOpenAdj l E b))
    ((o.extension i).adj.comp (o.direct p).adj)
    ((o.direct q).adj.comp (o.extension b).adj) χ₁ χ₂ α β h L
  simp only [χ₁, χ₂, composite_mate_app] at hm
  simpa only [cartesianConjugate, ringedCartesianConjugate, conjugateIsoEquiv,
    ordinaryPushReduction, RealizationModel.openReduction, Equiv.apply_symm_apply,
    ringedOpenAdj, α, β, q, b, Category.assoc] using! hm

attribute [local irreducible] ringedCartesianConjugate ringedPushComp cartesianConjugate
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  Functor.leftAdjoint

attribute [local irreducible] getLimitCone limit.cone getColimitCocone colimit.cocone
  sheafificationAdjunction presheafToSheaf eqToIso eqToHom

@[irreducible] private def lambdaIso
    {A B C D E' : Type*} [Category A] [Category B] [Category C] [Category D] [Category E']
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ E') (Q : E' ⥤ D)
    (S T : A ⥤ E') (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G) : (K ⋙ P) ⋙ I ≅ G :=
  Functor.associator K P I ≪≫ Functor.isoWhiskerLeft K c ≪≫
    (Functor.associator K J Q).symm ≪≫ Functor.isoWhiskerRight r Q ≪≫
    Functor.isoWhiskerRight d Q ≪≫ p ≪≫ e

private theorem lambda_components
    {A B C D E' : Type*} [Category A] [Category B] [Category C] [Category D] [Category E']
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ E') (Q : E' ⥤ D)
    (S T : A ⥤ E') (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G) (X : A) :
    (lambdaIso K P I J Q S T F G c r d p e).hom.app X =
      c.hom.app (K.obj X) ≫ Q.map (r.hom.app X) ≫ Q.map (d.hom.app X) ≫
        p.hom.app X ≫ e.hom.app X := by
  unfold lambdaIso
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp]

private theorem lambda_components_of_eq
    {A B C D E' : Type*} [Category A] [Category B] [Category C] [Category D] [Category E']
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ E') (Q : E' ⥤ D)
    (S T : A ⥤ E') (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G) (e₀ : (K ⋙ P) ⋙ I ≅ G)
    (he : e₀ = lambdaIso K P I J Q S T F G c r d p e) (X : A) :
    e₀.hom.app X =
      c.hom.app (K.obj X) ≫ Q.map (r.hom.app X) ≫ Q.map (d.hom.app X) ≫
        p.hom.app X ≫ e.hom.app X := by
  rw [he]
  exact lambda_components K P I J Q S T F G c r d p e X

private theorem lambda_square
    {A B C D H A' B' C' D' H' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category H]
    [Category A'] [Category B'] [Category C'] [Category D'] [Category H']
    (R : D ⥤ D') (T₀ : A ⥤ A')
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ H) (Q : H ⥤ D)
    (S T : A ⥤ H) (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G)
    (K' : A' ⥤ B') (P' : B' ⥤ C') (I' : C' ⥤ D') (J' : B' ⥤ H')
    (Q' : H' ⥤ D') (S' T' : A' ⥤ H') (F' G' : A' ⥤ D')
    (c' : P' ⋙ I' ≅ J' ⋙ Q') (r' : K' ⋙ J' ≅ S') (d' : S' ≅ T')
    (p' : T' ⋙ Q' ≅ F') (e' : F' ≅ G')
    (lamR : (K ⋙ P) ⋙ I ≅ G) (lamS : (K' ⋙ P') ⋙ I' ≅ G')
    (hr : lamR = lambdaIso K P I J Q S T F G c r d p e)
    (hs : lamS = lambdaIso K' P' I' J' Q' S' T' F' G' c' r' d' p' e')
    (X : A)
    (q₀ : R.obj (I.obj (P.obj (K.obj X))) ⟶ I'.obj (P'.obj (K'.obj (T₀.obj X))))
    (q₅ : R.obj (G.obj X) ⟶ G'.obj (T₀.obj X))
    (h : q₀ ≫ c'.hom.app (K'.obj (T₀.obj X)) ≫ Q'.map (r'.hom.app (T₀.obj X)) ≫
          Q'.map (d'.hom.app (T₀.obj X)) ≫ p'.hom.app (T₀.obj X) ≫
          e'.hom.app (T₀.obj X) =
        R.map (c.hom.app (K.obj X) ≫ Q.map (r.hom.app X) ≫ Q.map (d.hom.app X) ≫
          p.hom.app X ≫ e.hom.app X) ≫ q₅) :
    q₀ ≫ lamS.hom.app (T₀.obj X) = R.map (lamR.hom.app X) ≫ q₅ := by
  have hsys := lambda_components_of_eq K' P' I' J' Q' S' T' F' G'
    c' r' d' p' e' lamS hs (T₀.obj X)
  have hring := lambda_components_of_eq K P I J Q S T F G c r d p e lamR hr X
  rw [hsys, hring]
  exact h

private theorem ringed_lambda_iso
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
        ringedProperOpenLambda l E a.ringedModels a.ringedOpenComparisons k r p i h =
          lambdaIso (ringedOpen l E k) (ringedPush l E p) (ringedPull l E i)
      (ringedPull l E (pullback.fst p i)) (ringedPush l E (pullback.snd p i))
      (ringedOpen l E (ProEtale.StrictTower.squareLift k r p i h))
      (ringedPush l E (ProEtale.StrictTower.squareLift k r p i h))
      (ringedPush l E ((ProEtale.StrictTower.squareLift k r p i h) ≫ pullback.snd p i))
      (ringedPush l E r)
      (ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i)
      (ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h)
      (a.ringedOpenComparisons.clopen (ProEtale.StrictTower.squareLift k r p i h))
      (ringedPushComp l E (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i))
      (eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h)))
    := by
  unfold ringedProperOpenLambda lambdaIso
  rfl

@[irreducible] private def initialCoefficient
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] (L : Integral l E U) : systemHom l E W
        ((calculus l E W).reduction.obj
          ((ringedPull l E i).obj ((ringedPush l E p).obj ((ringedOpen l E k).obj L))))
        ((pull l E i).obj ((Operations.push l E o p).obj
          ((Operations.shriek l E o k).obj ((calculus l E U).reduction.obj L)))) :=
      ((a.realizationModel.reductionPull i).hom.app
          ((ringedPush l E p).obj ((ringedOpen l E k).obj L)) ≫
        (pull l E i).map
          ((ordinaryPushReduction l E o a.realizationModel p).app ((ringedOpen l E k).obj L) ≫
            (Operations.push l E o p).map ((openR l E o a.realizationModel k).app L)))

@[irreducible] private def finalCoefficient
    (o : Operations l E) (m : RealizationModel l E o)
    {U W : Scheme.{u}} (r : U ⟶ W) (L : Integral l E U) : systemHom l E W
        ((calculus l E W).reduction.obj ((ringedPush l E r).obj L))
        ((Operations.push l E o r).obj ((calculus l E U).reduction.obj L)) :=
      (ordinaryPushReduction l E o m r).app L

private theorem raw_lambda_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (L : Integral l E U) :
    let s := ProEtale.StrictTower.squareLift k r p i h
    let q := pullback.snd p i
    let δ₀ := initialCoefficient l E o a k p i L
    let δ₅ := finalCoefficient l E o a.realizationModel r L
    δ₀ ≫
        ((cartesianConjugate l E o a.compositors a.openComparisons p i).hom.app
            ((Operations.shriek l E o k).obj ((calculus l E U).reduction.obj L)) ≫
          (Operations.push l E o q).map
            ((restrictFactor l E o a.compositors a.openComparisons k r p i h).hom.app
              ((calculus l E U).reduction.obj L)) ≫
          (Operations.push l E o q).map
            ((a.openComparisons.clopen s).hom.app ((calculus l E U).reduction.obj L)) ≫
          (a.compositors.pushComp l E s q).hom.app ((calculus l E U).reduction.obj L) ≫
          (eqToIso (congrArg (Operations.push l E o) (pullback.lift_snd k r h))).hom.app
            ((calculus l E U).reduction.obj L)) =
      (calculus l E W).reduction.map
          ((ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i).hom.app
            ((ringedOpen l E k).obj L) ≫
          (ringedPush l E q).map
            ((ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h).hom.app
              L) ≫
          (ringedPush l E q).map ((a.ringedOpenComparisons.clopen s).hom.app L) ≫
          (ringedPushComp l E s q).hom.app L ≫
          (eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h))).hom.app L
          ) ≫
        δ₅ := by
  let s := ProEtale.StrictTower.squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  let δ₀ := (a.realizationModel.reductionPull i).hom.app
      ((ringedPush l E p).obj ((ringedOpen l E k).obj L)) ≫
    (pull l E i).map
      ((ordinaryPushReduction l E o a.realizationModel p).app ((ringedOpen l E k).obj L) ≫
        (Operations.push l E o p).map ((openR l E o a.realizationModel k).app L))
  let δ₁ := (ordinaryPushReduction l E o a.realizationModel q).app
      ((ringedPull l E b).obj ((ringedOpen l E k).obj L)) ≫
    (Operations.push l E o q).map
      ((a.realizationModel.reductionPull b).hom.app ((ringedOpen l E k).obj L) ≫
        (pull l E b).map ((openR l E o a.realizationModel k).app L))
  let δ₂ := (ordinaryPushReduction l E o a.realizationModel q).app
      ((ringedOpen l E s).obj L) ≫
    (Operations.push l E o q).map ((openR l E o a.realizationModel s).app L)
  let δ₃ := (ordinaryPushReduction l E o a.realizationModel q).app
      ((ringedPush l E s).obj L) ≫
    (Operations.push l E o q).map
      ((ordinaryPushReduction l E o a.realizationModel s).app L)
  let δ₄ := (ordinaryPushReduction l E o a.realizationModel (s ≫ q)).app L
  let δ₅ := (ordinaryPushReduction l E o a.realizationModel r).app L
  have h₀ : δ₀ ≫ (cartesianConjugate l E o a.compositors a.openComparisons p i).hom.app
        ((Operations.shriek l E o k).obj ((calculus l E U).reduction.obj L)) =
      (calculus l E W).reduction.map
          ((ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i).hom.app
            ((ringedOpen l E k).obj L)) ≫ δ₁ := by
    have hc := cartesian_coefficient_square l E o a p i ((ringedOpen l E k).obj L)
    have hn := (cartesianConjugate l E o a.compositors a.openComparisons p i).hom.naturality
      ((openR l E o a.realizationModel k).app L)
    dsimp only [Functor.comp_map] at hn
    simp only [δ₀, δ₁, CategoryTheory.Functor.map_comp, Category.assoc]
    erw [hn, reassoc_of% hc]
  have h₁ := map_coefficient_square
    (ordinaryPushReduction l E o a.realizationModel q)
    ((a.realizationModel.reductionPull b).hom.app ((ringedOpen l E k).obj L) ≫
      (pull l E b).map ((openR l E o a.realizationModel k).app L))
    ((openR l E o a.realizationModel s).app L)
    ((ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h).hom.app L)
    ((restrictFactor l E o a.compositors a.openComparisons k r p i h).hom.app
      ((calculus l E U).reduction.obj L))
    (by
      have hr := open_restriction_coefficient_square l E o a s b k
        (pullback.lift_fst k r h) L
      have hs : restrictFactor l E o a.compositors a.openComparisons k r p i h =
          restrictionIso (F := Operations.shriek l E o s)
            (J := Operations.shriek l E o b) (K := Operations.shriek l E o k)
            (pull l E b) (a.compositors.openComp l E s b ≪≫ openCongr l E o
              (pullback.lift_fst k r h)) (a.openComparisons.unit l E o a.compositors b) := by
        unfold restrictFactor restrictionIso
        rfl
      have ht : ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h =
          restrictionIso (F := ringedOpen l E s) (J := ringedOpen l E b)
            (K := ringedOpen l E k) (ringedPull l E b)
            (ringedOpenComp l E s b ≪≫ ringedOpenCongr l E (pullback.lift_fst k r h))
            (a.ringedOpenComparisons.unit l E a.ringedModels b) := by
        unfold ringedRestrictFactor restrictionIso
        rfl
      erw [hs, ht]
      exact (Category.assoc _ _ _).trans hr)
  have h₂ := map_coefficient_square
    (ordinaryPushReduction l E o a.realizationModel q)
    ((openR l E o a.realizationModel s).app L)
    ((ordinaryPushReduction l E o a.realizationModel s).app L)
    ((a.ringedOpenComparisons.clopen s).hom.app L)
    ((a.openComparisons.clopen s).hom.app ((calculus l E U).reduction.obj L))
    (clopen_coefficient_square l E o a s L)
  have h₃ := push_comp_coefficient_square l E o a s q L
  have h₄ := push_congr_coefficient_square l E o a (pullback.lift_snd k r h) L
  have ht := paste_five (calculus l E W).reduction δ₀ δ₁ δ₂ δ₃ δ₄ δ₅
    ((ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i).hom.app
      ((ringedOpen l E k).obj L))
    ((ringedPush l E q).map
      ((ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h).hom.app L))
    ((ringedPush l E q).map ((a.ringedOpenComparisons.clopen s).hom.app L))
    ((ringedPushComp l E s q).hom.app L)
    ((eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h))).hom.app L)
    ((cartesianConjugate l E o a.compositors a.openComparisons p i).hom.app
      ((Operations.shriek l E o k).obj ((calculus l E U).reduction.obj L)))
    ((Operations.push l E o q).map
      ((restrictFactor l E o a.compositors a.openComparisons k r p i h).hom.app
        ((calculus l E U).reduction.obj L)))
    ((Operations.push l E o q).map
      ((a.openComparisons.clopen s).hom.app ((calculus l E U).reduction.obj L)))
    ((a.compositors.pushComp l E s q).hom.app ((calculus l E U).reduction.obj L))
    ((eqToIso (congrArg (Operations.push l E o) (pullback.lift_snd k r h))).hom.app
      ((calculus l E U).reduction.obj L)) h₀
    (by simpa only [δ₁, δ₂, Category.assoc] using! h₁)
    (by simpa only [δ₂, δ₃, Category.assoc] using! h₂)
    (by simpa only [δ₃, δ₄, Category.assoc] using! h₃) h₄
  simpa only [initialCoefficient, finalCoefficient] using! ht

-- Infer the dependent function type from the abstract application. An explicit
-- normalized type would force conversion of entire chosen derived categories.
set_option linter.defProp false in
@[irreducible] private def lambda_from_raw
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (L : Integral l E U) :=
  let s := ProEtale.StrictTower.squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  let hs : properOpenLambda l E o a.compositors a.openComparisons k r p i h =
      lambdaIso (Operations.shriek l E o k) (Operations.push l E o p)
        (pull l E i) (pull l E b) (Operations.push l E o q)
        (Operations.shriek l E o s) (Operations.push l E o s)
        (Operations.push l E o (s ≫ q)) (Operations.push l E o r)
        (cartesianConjugate l E o a.compositors a.openComparisons p i)
        (restrictFactor l E o a.compositors a.openComparisons k r p i h)
        (a.openComparisons.clopen s) (a.compositors.pushComp l E s q)
        (eqToIso (congrArg (Operations.push l E o) (pullback.lift_snd k r h))) := by
    unfold properOpenLambda lambdaIso
    rfl
  lambda_square
    (A := nativeIntegral l E U) (B := nativeIntegral l E V)
    (C := nativeIntegral l E Z) (D := nativeIntegral l E W)
    (H := nativeIntegral l E (pullback p i))
    (A' := nativeSystem l E U) (B' := nativeSystem l E V)
    (C' := nativeSystem l E Z) (D' := nativeSystem l E W)
    (H' := nativeSystem l E (pullback p i))
    (calculus l E W).reduction (calculus l E U).reduction
    (ringedOpen l E k) (ringedPush l E p) (ringedPull l E i)
    (ringedPull l E b) (ringedPush l E q) (ringedOpen l E s) (ringedPush l E s)
    (ringedPush l E (s ≫ q)) (ringedPush l E r)
    (ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i)
    (ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h)
    (a.ringedOpenComparisons.clopen s) (ringedPushComp l E s q)
    (eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h)))
    (Operations.shriek l E o k) (Operations.push l E o p) (pull l E i)
    (pull l E b) (Operations.push l E o q)
    (Operations.shriek l E o s) (Operations.push l E o s)
    (Operations.push l E o (s ≫ q)) (Operations.push l E o r)
    (cartesianConjugate l E o a.compositors a.openComparisons p i)
    (restrictFactor l E o a.compositors a.openComparisons k r p i h)
    (a.openComparisons.clopen s) (a.compositors.pushComp l E s q)
    (eqToIso (congrArg (Operations.push l E o) (pullback.lift_snd k r h)))
    (ringedProperOpenLambda l E a.ringedModels a.ringedOpenComparisons k r p i h)
    (properOpenLambda l E o a.compositors a.openComparisons k r p i h)
    (ringed_lambda_iso l E o a k r p i h) hs
    L
    (initialCoefficient l E o a k p i L)
    (finalCoefficient l E o a.realizationModel r L)

private theorem evaluate_push_obj
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] (d : Interpretation C)
    {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left) (e : Expression B I X U)
    (M : ∀ i, C (X i).left) :
    ((Expression.push f hf e).evaluate d).obj M =
      (d.push f.left).obj ((e.evaluate d).obj M) := rfl

private theorem evaluate_shriek_obj
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] (d : Interpretation C)
    {U V : Over B} (f : U ⟶ V) (hf : IsOpenImmersion f.left)
    (hq : QuasiCompact f.left) (e : Expression B I X U) (M : ∀ i, C (X i).left) :
    ((Expression.shriek f hf hq e).evaluate d).obj M =
      (by letI := hf; exact (d.shriek f.left).obj ((e.evaluate d).obj M)) := rfl

-- Normalize object evaluation by proved equations, retaining the equality proof.
-- Doing this before congruence avoids comparing the sources of different functors.
private meta def compProjection (x : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let args := x.getAppArgs
  if x.isAppOf ``Functor.obj && args.size ≥ 2 then
    let f := args[args.size - 2]!
    if f.isAppOf ``Expression.evaluate then
      let fs := f.getAppArgs
      let e := fs.back!
      let es := e.getAppArgs
      let d := fs[fs.size - 3]!
      if e.isAppOf ``Expression.push then
        let h ← Lean.Meta.mkAppM ``evaluate_push_obj
          #[d, es[es.size - 3]!, es[es.size - 2]!, es.back!, args.back!]
        return some ((← Lean.Meta.inferType h).getAppArgs.back!,
          ← Lean.Meta.mkHEqOfEq h)
      if e.isAppOf ``Expression.shriek then
        let h ← Lean.Meta.mkAppM ``evaluate_shriek_obj
          #[d, es[es.size - 4]!, es[es.size - 3]!, es[es.size - 2]!, es.back!, args.back!]
        return some ((← Lean.Meta.inferType h).getAppArgs.back!,
          ← Lean.Meta.mkHEqOfEq h)
    if f.isAppOf ``Functor.comp then
      let fs := f.getAppArgs
      let h ← Lean.Meta.mkAppM ``Functor.comp_obj
        #[fs[fs.size - 2]!, fs[fs.size - 1]!, args[args.size - 1]!]
      let rhs := (← Lean.Meta.inferType h).getAppArgs.back!
      return some (rhs, ← Lean.Meta.mkHEqOfEq h)
  return none

-- Reify congruence between definitionally equal presentations into explicit HEq proofs.
-- This keeps the kernel from unfolding chosen derived categories while comparing
-- compound functor expressions. The reflexivity leaves and the resulting casts are
-- all checked by the kernel; this procedure adds no mathematical assumption.
private meta partial def typeCongruence (x y : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if x == y then return ← Lean.Meta.mkHEqRefl x
  if let some (x', h) ← compProjection x then
    return ← Lean.Meta.mkAppM ``HEq.trans #[h, ← typeCongruence x' y]
  if let some (y', h) ← compProjection y then
    return ← Lean.Meta.mkAppM ``HEq.trans
      #[← typeCongruence x y', ← Lean.Meta.mkAppM ``HEq.symm #[h]]
  if (← Lean.Meta.isProof x) && (← Lean.Meta.isProof y) then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[x, y]
  if x.getAppFn == y.getAppFn && x.isApp && x.getAppNumArgs == y.getAppNumArgs then
    let xs := x.getAppArgs
    let ys := y.getAppArgs
    let thm ← Lean.Meta.mkHCongrWithArity x.getAppFn xs.size
    let mut args := #[]
    for a in xs, b in ys, kind in thm.argKinds do
      let h ← typeCongruence a b
      match kind with
      | .eq =>
        let h ← Lean.Meta.mkEqOfHEq h
        args := args ++ #[a, b, h]
      | .heq => args := args ++ #[a, b, h]
      | _ => throwError "Unexpected congruence argument"
    let h := Lean.mkAppN thm.proof args
    if (← Lean.Meta.inferType h).isHEq then return h
    return ← Lean.Meta.mkHEqOfEq h
  return ← Lean.Meta.mkHEqRefl x

private theorem lambda_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (L : Integral l E U) :
    let δ₀ := initialCoefficient l E o a k p i L
    let δ₅ := finalCoefficient l E o a.realizationModel r L
    δ₀ ≫
        (properOpenLambda l E o a.compositors a.openComparisons k r p i h).hom.app
          ((calculus l E U).reduction.obj L) =
      (calculus l E W).reduction.map
          ((ringedProperOpenLambda l E a.ringedModels a.ringedOpenComparisons
            k r p i h).hom.app L) ≫
        δ₅ := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let args ← #[`l, `E, `o, `a, `k, `r, `p, `i, `h, `L].mapM fun n ↦
      Lean.Elab.Term.elabTerm (Lean.mkIdent n) none
    let f ← Lean.Meta.mkAppM ``lambda_from_raw args
    let raw ← Lean.Meta.mkAppM ``raw_lambda_coefficient_square args
    let ft ← Lean.Meta.whnf (← Lean.Meta.inferType f)
    let rt ← Lean.Meta.whnf (← Lean.Meta.inferType raw)
    let e ← Lean.Meta.mkEqOfHEq (← typeCongruence rt ft.bindingDomain!)
    let raw' ← Lean.Meta.mkAppM ``Eq.mp #[e, raw]
    let result := Lean.mkApp f raw'
    let out ← Lean.Meta.whnf (← Lean.Meta.inferType result)
    let goal ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
    let e ← Lean.Meta.mkEqOfHEq (← typeCongruence out goal)
    let result ← Lean.Meta.mkAppM ``Eq.mp #[e, result]
    Lean.Elab.Tactic.closeMainGoal `exact result

private theorem gamma_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (L : Integral l E U) :
    (openR l E o a.realizationModel i).app ((ringedPush l E r).obj L) ≫
        (Operations.shriek l E o i).map
          ((ordinaryPushReduction l E o a.realizationModel r).app L) ≫
        (a.properOpen.gamma k r p i h).app ((calculus l E U).reduction.obj L) =
      (calculus l E Z).reduction.map ((a.ringedProperOpen.gamma k r p i h).app L) ≫
        (ordinaryPushReduction l E o a.realizationModel p).app ((ringedOpen l E k).obj L) ≫
        (Operations.push l E o p).map ((openR l E o a.realizationModel k).app L) := by
  have hi : IsIso (((mateEquiv (ringedOpenAdj l E i) (o.extension i).adj).symm
      (a.realizationModel.reductionPull i).hom).app
        ((ringedPush l E r).obj L)) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel i _
  have hlam := lambda_coefficient_square l E o a k r p i h L
  have hlam₀ := hlam
  simp only [initialCoefficient, finalCoefficient] at hlam₀
  have hlam' := inverse_square (calculus l E W).reduction
    ((ringedProperOpenLambda l E a.ringedModels a.ringedOpenComparisons k r p i h).app L)
    ((properOpenLambda l E o a.compositors a.openComparisons k r p i h).app
      ((calculus l E U).reduction.obj L))
    ((a.realizationModel.reductionPull i).hom.app
        ((ringedPush l E p).obj ((ringedOpen l E k).obj L)) ≫
      (pull l E i).map
        ((ordinaryPushReduction l E o a.realizationModel p).app ((ringedOpen l E k).obj L) ≫
          (Operations.push l E o p).map ((openR l E o a.realizationModel k).app L)))
    ((ordinaryPushReduction l E o a.realizationModel r).app L) hlam₀
  have hm := inverse_mate_square (ringedOpenAdj l E i) (o.extension i).adj
    (a.realizationModel.reductionPull i).hom
    ((ordinaryPushReduction l E o a.realizationModel r).app L)
    ((ordinaryPushReduction l E o a.realizationModel p).app ((ringedOpen l E k).obj L) ≫
      (Operations.push l E o p).map ((openR l E o a.realizationModel k).app L))
    ((a.ringedProperOpen.gamma k r p i h).app L)
    ((a.properOpen.gamma k r p i h).app ((calculus l E U).reduction.obj L)) (by
      erw [a.ringedProperOpen.adjunct k r p i h L,
        a.properOpen.adjunct k r p i h ((calculus l E U).reduction.obj L)]
      simpa only [Iso.app_inv, Category.assoc] using! hlam')
  have hi' := GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel i
    ((ringedPush l E r).obj L)
  rw [openR_app]
  erw [GeneratorReduction.inverseOrZero_eq_inv]
  simpa only [RealizationModel.openReduction, ringedOpenAdj,
    Category.assoc] using! hm

/-- The ordinary coefficient square for the proper/open interchange.
Source: blueprint fix-prop-coherence, the canonical proper/open lambda adjunct.
(blueprint: lem-sf-integral-ordinary-proper-open-square).

Proof: expand gamma as the open adjunct of inverse lambda. The canonical bridge
identifies the system lambda with the cartesian open-base-change, clopen lift and
proper-composition factors. The ringed lambda has exactly the independent ringed
factors. Their coefficient squares follow from pull-composition, open base change,
clopen adjunction normalization and proper composition. Paste, invert the resulting
lambda square, and transpose under the actual open adjunction using its counit
square. Naturality inserts the coefficient map of e. The computation is in whole
systems and ordinary ringed categories; no completion or expression comparison is used. -/
theorem ordinaryProperOpenSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V W Z : Over B} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [hk : IsOpenImmersion k.left] [hi : IsOpenImmersion i.left]
    [qk : QuasiCompact k.left] [qi : QuasiCompact i.left]
    [hr : IsProper r.left] [hp : IsProper p.left]
    (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X U) :
    (Expression.shriek i hi qi (.push r hr e)).ordinaryReduction l E o a K ≫
      (a.properOpen.gamma k.left r.left p.left i.left w).app
        (e.systemObj l E o ((inputReduction l E X).obj K)) =
    (calculus l E Z.left).reduction.map
        ((a.ringedProperOpen.gamma k.left r.left p.left i.left w).app
          (e.ringedObj l E a.ringedModels K)) ≫
      (Expression.push p hp (.shriek k hk qk e)).ordinaryReduction l E o a K := by
  have hg := gamma_coefficient_square l E o a k.left r.left p.left i.left w
    (e.ringedObj l E a.ringedModels K)
  have hn := (a.properOpen.gamma k.left r.left p.left i.left w).naturality
    (e.ordinaryReduction l E o a K)
  dsimp only [Functor.comp_map] at hn
  have hc := congrArg (fun f ↦ f ≫ (Operations.push l E o p.left).map
    ((Operations.shriek l E o k.left).map (e.ordinaryReduction l E o a K))) hg
  simp only [Category.assoc] at hc
  rw [← hn] at hc
  rw [← Functor.map_comp_assoc, ← Functor.map_comp] at hc
  rw [← Category.assoc] at hc
  rw [openR_app, openR_app] at hc
  simp only [Expression.ordinaryReduction]
  run_tac Lean.Elab.Tactic.withMainContext do
    let pr ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hc) none
    let source ← Lean.Meta.whnf (← Lean.Meta.inferType pr)
    let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
    let e ← Lean.Meta.mkEqOfHEq (← typeCongruence source target)
    let pr ← Lean.Meta.mkAppM ``Eq.mp #[e, pr]
    Lean.Elab.Tactic.closeMainGoal `exact pr

end WeilConjectures.IntegralSystemRealization
