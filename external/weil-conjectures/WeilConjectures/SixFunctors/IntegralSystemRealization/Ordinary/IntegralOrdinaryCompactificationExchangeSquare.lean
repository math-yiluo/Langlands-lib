/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryCanonicalIsoSquare
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares

/-! # Ordinary coefficient compatibility for compactification exchange

Source: blueprint fix-prop-coherence, the coefficient comparisons of individual maps.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible]
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  integralOperationsCommHasDerivedCategory
  PurCompactSupport.completed coefficientSequenceHasDerived scalarReductionSourceDerived
  integralTowerHasDerivedCategory integralCompletedRingHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleCanonicalTensorComparison ringedPullComp ringedSquare Compositors.square
  mateEquiv ringedAdj Direct.adj

private abbrev functorSource {A B : Type*} [Category A] [Category B] (_ : A ⥤ B) := A
private abbrev functorTarget {A B : Type*} [Category A] [Category B] (_ : A ⥤ B) := B
private abbrev nativeIntegral (W : Scheme.{u}) :=
  functorSource ((calculus l E W).reduction)
private abbrev nativeSystem (W : Scheme.{u}) :=
  functorTarget ((calculus l E W).reduction)

private theorem matePastingSquare
    {AZ AV AW AU BZ BV BW BU : Type*}
    [Category AZ] [Category AV] [Category AW] [Category AU]
    [Category BZ] [Category BV] [Category BW] [Category BU]
    {P : AZ ⥤ AV} {Q : AV ⥤ AZ} {P' : AW ⥤ AU} {Q' : AU ⥤ AW}
    {F : BZ ⥤ BV} {G : BV ⥤ BZ} {F' : BW ⥤ BU} {G' : BU ⥤ BW}
    {RZ : AZ ⥤ BZ} {RV : AV ⥤ BV} {RW : AW ⥤ BW} {RU : AU ⥤ BU}
    {I : AZ ⥤ AW} {K : AV ⥤ AU} {J : BZ ⥤ BW} {H : BV ⥤ BU}
    (a : P ⊣ Q) (b : P' ⊣ Q') (c : F ⊣ G) (d : F' ⊣ G')
    (δp : P ⋙ RV ≅ RZ ⋙ F) (δr : P' ⋙ RU ≅ RW ⋙ F')
    (δi : I ⋙ RW ⟶ RZ ⋙ J) (δk : K ⋙ RU ⟶ RV ⋙ H)
    (θr : TwoSquare I P P' K) (θs : TwoSquare J F F' H)
    (h : (Functor.whiskerLeft I δr.hom ≫ Functor.whiskerRight δi F') ≫
        Functor.whiskerLeft RZ θs =
      Functor.whiskerRight θr RU ≫
        (Functor.whiskerLeft P δk ≫ Functor.whiskerRight δp.hom H))
    (L : AV) :
    δi.app (Q.obj L) ≫ J.map ((mateEquiv a c δp.inv).app L) ≫
        (mateEquiv c d θs).app (RV.obj L) =
      RW.map ((mateEquiv a b θr).app L) ≫
        (mateEquiv b d δr.inv).app (K.obj L) ≫ G'.map (δk.app L) := by
  apply (d.homEquiv _ _).symm.injective
  change F'.map _ ≫ d.counit.app _ = F'.map _ ≫ d.counit.app _
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hε := d.counit.naturality (δk.app L)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hε
  erw [hε, mateEquiv_counit c d θs (RV.obj L)]
  have hn := θs.naturality ((mateEquiv a c δp.inv).app L)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← H.map_comp, mateEquiv_counit a c δp.inv L]
  erw [reassoc_of% (mateEquiv_counit b d δr.inv (K.obj L))]
  have hn' := δr.inv.naturality ((mateEquiv a b θr).app L)
  dsimp only [Functor.comp_map] at hn'
  erw [reassoc_of% hn', ← RU.map_comp_assoc, mateEquiv_counit a b θr L]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn'' := δk.naturality (a.counit.app L)
  dsimp only [Functor.comp_map] at hn''
  erw [hn'']
  apply (cancel_epi (δr.hom.app (I.obj (Q.obj L)))).1
  simp only [Iso.hom_inv_id_app_assoc]
  have h₀ := whisker_square_app δi δr.hom δp.hom δk θr θs h
    (Q.obj L)
  erw [reassoc_of% h₀]
  simp only [← H.map_comp_assoc, Iso.hom_inv_id_app]
  erw [H.map_id, Category.id_comp]
  rfl

private theorem matePastingNaturalSquare
    {AZ AV AW AU BZ BV BW BU : Type*}
    [Category AZ] [Category AV] [Category AW] [Category AU]
    [Category BZ] [Category BV] [Category BW] [Category BU]
    {P : AZ ⥤ AV} {Q : AV ⥤ AZ} {P' : AW ⥤ AU} {Q' : AU ⥤ AW}
    {F : BZ ⥤ BV} {G : BV ⥤ BZ} {F' : BW ⥤ BU} {G' : BU ⥤ BW}
    {RZ : AZ ⥤ BZ} {RV : AV ⥤ BV} {RW : AW ⥤ BW} {RU : AU ⥤ BU}
    {I : AZ ⥤ AW} {K : AV ⥤ AU} {J : BZ ⥤ BW} {H : BV ⥤ BU}
    (a : P ⊣ Q) (b : P' ⊣ Q') (c : F ⊣ G) (d : F' ⊣ G')
    (δp : P ⋙ RV ≅ RZ ⋙ F) (δr : P' ⋙ RU ≅ RW ⋙ F')
    (δi : I ⋙ RW ⟶ RZ ⋙ J) (δk : K ⋙ RU ⟶ RV ⋙ H)
    (θr : TwoSquare I P P' K) (θs : TwoSquare J F F' H)
    (h : (Functor.whiskerLeft I δr.hom ≫ Functor.whiskerRight δi F') ≫
        Functor.whiskerLeft RZ θs =
      Functor.whiskerRight θr RU ≫
        (Functor.whiskerLeft P δk ≫ Functor.whiskerRight δp.hom H))
    (L : AV) {M : BV} (q : RV.obj L ⟶ M) :
    (δi.app (Q.obj L) ≫
        J.map ((mateEquiv a c δp.inv).app L ≫ G.map q)) ≫
        (mateEquiv c d θs).app M =
      RW.map ((mateEquiv a b θr).app L) ≫
        (mateEquiv b d δr.inv).app (K.obj L) ≫
        G'.map (δk.app L ≫ H.map q) := by
  have hn := (mateEquiv c d θs).naturality q
  dsimp only [Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ G'.map (H.map q))
    (matePastingSquare a b c d δp δr δi δk θr θs h L)

private theorem pasteCoefficientSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {R : A ⥤ B} {T : C ⥤ D} {F : C ⥤ A} {G : D ⥤ B}
    (η : F ⋙ R ⟶ T ⋙ G)
    {Z : A} {Y : B} {L L' : C} {M N : D}
    {s : R.obj Z ⟶ Y} {exS : Y ⟶ G.obj M} {exR : Z ⟶ F.obj L}
    {betaS : M ⟶ N} {betaR : L ⟶ L'}
    {q₀ : T.obj L ⟶ M} {q₁ : T.obj L' ⟶ N}
    (hp : s ≫ exS = R.map exR ≫ η.app L ≫ G.map q₀)
    (ho : q₀ ≫ betaS = T.map betaR ≫ q₁) :
    s ≫ (exS ≫ G.map betaS) =
      R.map (exR ≫ F.map betaR) ≫ (η.app L' ≫ G.map q₁) := by
  rw [← Category.assoc, hp]
  simp only [Category.assoc, ← G.map_comp]
  rw [ho]
  simp only [Functor.map_comp, ← Category.assoc]
  have hn := η.naturality betaR
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn]

private theorem properPullCoeff
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (w : k ≫ p = r ≫ i) :
    (Functor.whiskerLeft (ringedPull l E i) (a.realizationModel.reductionPull r).hom ≫
        Functor.whiskerRight (a.realizationModel.reductionPull i).hom (pull l E r)) ≫
        Functor.whiskerLeft (calculus l E Z).reduction
          (a.compositors.square l E k r p i w).hom =
      Functor.whiskerRight (ringedSquare l E k r p i w).hom
          (calculus l E U).reduction ≫
        (Functor.whiskerLeft (ringedPull l E p) (a.realizationModel.reductionPull k).hom ≫
          Functor.whiskerRight (a.realizationModel.reductionPull p).hom (pull l E k)) := by
  have h := pull_square_nat l E o a.realizationModel a.compositors r k i p w.symm
  have hR : (ringedSquare l E r k i p w.symm).inv =
      (ringedSquare l E k r p i w).hom := by
    simp only [ringedSquare, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
      Category.assoc]
    rfl
  have hS : (a.compositors.square l E r k i p w.symm).inv =
      (a.compositors.square l E k r p i w).hom := by
    simp only [Compositors.square, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
      Category.assoc]
    rfl
  rw [hR, hS] at h
  exact h

private theorem open_beta_coeff
    (o : Operations l E) (a : AmbientModels l E o)
    {U' U V' V : Scheme.{u}} (v : U' ⟶ U) (j' : U' ⟶ V') (j : U ⟶ V) (g : V' ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (w : v ≫ j = j' ≫ g) (sq : IsPullback v j' j g)
    (L : Integral l E U) (M : System l E U)
    (q : (calculus l E U).reduction.obj L ⟶ M) :
    (a.realizationModel.reductionPull g).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E g).map
          (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
            (Operations.shriek l E o j).map q) ≫
        (a.openComparisons.beta v j' j g w sq).hom.app M =
      (calculus l E V').reduction.map ((a.ringedOpenComparisons.beta v j' j g w sq).hom.app L) ≫
        GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j').app
          ((ringedPull l E v).obj L)) ≫
        (Operations.shriek l E o j').map
          ((a.realizationModel.reductionPull v).hom.app L ≫ (pull l E v).map q) := by
  let qJ := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E j).app L) ≫
      (Operations.shriek l E o j).map q
  have hj : IsIso ((a.realizationModel.openReduction l E j).app L) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j L
  have hj' : IsIso ((a.realizationModel.openReduction l E j').app
    ((ringedPull l E v).obj L)) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j' _
  have hj₀ := hj
  have hj'₀ := hj'
  change IsIso (((mateEquiv (ringedOpenAdj l E j) (o.extension j).adj).symm
    (a.realizationModel.reductionPull j).hom).app L) at hj
  change IsIso (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
    (a.realizationModel.reductionPull j').hom).app
      ((ringedPull l E v).obj L)) at hj'
  have hu : q ≫ (o.extension j).adj.unit.app M =
      (calculus l E _).reduction.map ((ringedOpenAdj l E j).unit.app L) ≫
        (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map qJ := by
    simpa only [qJ, RealizationModel.openReduction, ringedOpenAdj, Operations.shriek] using!
      GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E j)
        (o.extension j).adj (a.realizationModel.reductionPull j).hom q
  have hs := open_beta_inverse_square l E o a v j' j g w sq L M q qJ hu
  have hi := inverse_square (calculus l E V').reduction
    ((a.ringedOpenComparisons.beta v j' j g w sq).app L).symm
    ((a.openComparisons.beta v j' j g w sq).app M).symm
    (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j').app
        ((ringedPull l E v).obj L)) ≫
      (Operations.shriek l E o j').map
        ((a.realizationModel.reductionPull v).hom.app L ≫ (pull l E v).map q))
    ((a.realizationModel.reductionPull g).hom.app ((ringedOpen l E j).obj L) ≫
      (pull l E g).map qJ)
    (by
      rw [GeneratorReduction.inverseOrZero_eq_inv]
      simpa only [Iso.symm_hom, Iso.app_inv, RealizationModel.openReduction,
        ringedOpenAdj, Operations.shriek, Category.assoc] using! hs)
  simpa only [Iso.symm_inv, Iso.app_hom, qJ, Category.assoc] using! hi

private def compactComposite
    {DX DB DY DX' DB' DY' : Type*}
    [Category DX] [Category DB] [Category DY]
    [Category DX'] [Category DB'] [Category DY']
    (J : DX ⥤ DB) (J' : DX' ⥤ DB') (R : DB ⥤ DY) (R' : DB' ⥤ DY')
    (G : DY ⥤ DY') (H : DX ⥤ DX') (B : DB ⥤ DB')
    (ex : R ⋙ G ⟶ B ⋙ R') (β : J ⋙ B ≅ H ⋙ J') :
    (J ⋙ R) ⋙ G ⟶ H ⋙ (J' ⋙ R') :=
  (Functor.associator J R G).hom ≫ Functor.whiskerLeft J ex ≫
    (Functor.associator J B R').inv ≫ Functor.whiskerRight β.hom R' ≫
    (Functor.associator H J' R').hom

private theorem compactCompositeSquare
    {AX AB AY AX' AB' AY' BX BB BY BX' BB' BY' : Type*}
    [Category AX] [Category AB] [Category AY]
    [Category AX'] [Category AB'] [Category AY']
    [Category BX] [Category BB] [Category BY]
    [Category BX'] [Category BB'] [Category BY']
    {J : AX ⥤ AB} {J' : AX' ⥤ AB'} {P : AB ⥤ AY} {P' : AB' ⥤ AY'}
    {G : AY ⥤ AY'} {H : AX ⥤ AX'} {B : AB ⥤ AB'}
    {K : BX ⥤ BB} {K' : BX' ⥤ BB'} {Q : BB ⥤ BY} {Q' : BB' ⥤ BY'}
    {G' : BY ⥤ BY'} {H' : BX ⥤ BX'} {B' : BB ⥤ BB'}
    {R : AY' ⥤ BY'} {T : AB' ⥤ BB'} (η : P' ⋙ R ⟶ T ⋙ Q')
    {exR : P ⋙ G ⟶ B ⋙ P'} {exS : Q ⋙ G' ⟶ B' ⋙ Q'}
    {βR : J ⋙ B ≅ H ⋙ J'} {βS : K ⋙ B' ≅ H' ⋙ K'}
    {ξR : (J ⋙ P) ⋙ G ⟶ H ⋙ (J' ⋙ P')}
    {ξS : (K ⋙ Q) ⋙ G' ⟶ H' ⋙ (K' ⋙ Q')}
    {L : AX} {M : BX}
    {s : R.obj (G.obj (P.obj (J.obj L))) ⟶ G'.obj (Q.obj (K.obj M))}
    {q₀ : T.obj (B.obj (J.obj L)) ⟶ B'.obj (K.obj M)}
    {q₁ : T.obj (J'.obj (H.obj L)) ⟶ K'.obj (H'.obj M)}
    (hr : ξR = compactComposite J J' P P' G H B exR βR)
    (hs : ξS = compactComposite K K' Q Q' G' H' B' exS βS)
    (hp : s ≫ exS.app (K.obj M) =
      R.map (exR.app (J.obj L)) ≫ η.app (B.obj (J.obj L)) ≫ Q'.map q₀)
    (ho : q₀ ≫ βS.hom.app M = T.map (βR.hom.app L) ≫ q₁) :
    s ≫ ξS.app M =
      R.map (ξR.app L) ≫ (η.app (J'.obj (H.obj L)) ≫ Q'.map q₁) := by
  rw [hr, hs]
  simpa only [compactComposite, Functor.comp_obj, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using pasteCoefficientSquare η hp ho

private theorem compactificationMap
    (o : Operations l E) (a : AmbientModels l E o)
    {U V U' V' : Scheme.{u}} {f : U ⟶ V} {f' : U' ⟶ V'}
    (cf : Compactification f) (cf' : Compactification f')
    (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y)
    (hi : IsPullback x cf'.i cf.i z) :
    compactificationExchange l E o a.compositors a.openComparisons
      cf cf' x y z wi wp hi =
    compactComposite (Operations.shriek l E o cf.i) (Operations.shriek l E o cf'.i)
      (Operations.push l E o cf.g) (Operations.push l E o cf'.g)
      (pull l E y) (pull l E x) (pull l E z)
      (properExchange l E o a.compositors z cf'.g cf.g y wp)
      (a.openComparisons.beta x cf'.i cf.i z wi hi) := by
  rfl

private theorem ringedCompactificationMap
    (o : Operations l E) (a : AmbientModels l E o)
    {U V U' V' : Scheme.{u}} {f : U ⟶ V} {f' : U' ⟶ V'}
    (cf : Compactification f) (cf' : Compactification f')
    (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y)
    (hi : IsPullback x cf'.i cf.i z) :
    ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
      cf cf' x y z wi wp hi =
    compactComposite (ringedOpen l E cf.i) (ringedOpen l E cf'.i)
      (ringedPush l E cf.g) (ringedPush l E cf'.g)
      (ringedPull l E y) (ringedPull l E x) (ringedPull l E z)
      (mateEquiv (ringedAdj l E cf.g) (ringedAdj l E cf'.g)
        (TwoSquare.mk _ _ _ _ (ringedSquare l E z cf'.g cf.g y wp).hom))
      (a.ringedOpenComparisons.beta x cf'.i cf.i z wi hi) := by
  rfl

-- Infer this proposition from the categorical application. An explicit normalized
-- type forces conversion through the chosen derived categories.
set_option linter.defProp false in
@[irreducible] private def compactificationProperRaw
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {U V U' V' : Over B}
    (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
    (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (_wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
    (_hi : IsPullback x.left cf'.i cf.i z)
    (L : Integral l E U.left) (M : System l E U.left)
    (q : (calculus l E U.left).reduction.obj L ⟶ M) :=
  let qJ := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E cf.i).app L) ≫
      (Operations.shriek l E o cf.i).map q
  matePastingNaturalSquare
    (ringedAdj l E cf.g) (ringedAdj l E cf'.g)
    (o.direct cf.g).adj (o.direct cf'.g).adj
    (a.realizationModel.reductionPull cf.g) (a.realizationModel.reductionPull cf'.g)
    (a.realizationModel.reductionPull y.left).hom
    (a.realizationModel.reductionPull z).hom
    (TwoSquare.mk _ _ _ _ (ringedSquare l E z cf'.g cf.g y.left wp).hom)
    (TwoSquare.mk _ _ _ _ (a.compositors.square l E z cf'.g cf.g y.left wp).hom)
    (properPullCoeff l E o a z cf'.g cf.g y.left wp)
    ((ringedOpen l E cf.i).obj L) qJ

set_option linter.defProp false in
@[irreducible] private def compactificationRaw
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {U V U' V' : Over B}
    (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
    (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
    (hi : IsPullback x.left cf'.i cf.i z)
    (L : Integral l E U.left) (M : System l E U.left)
    (q : (calculus l E U.left).reduction.obj L ⟶ M) :=
  let qJ := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E cf.i).app L) ≫
      (Operations.shriek l E o cf.i).map q
  compactCompositeSquare
    (AX := nativeIntegral l E U.left) (AB := nativeIntegral l E cf.Z)
    (AY := nativeIntegral l E V.left) (AX' := nativeIntegral l E U'.left)
    (AB' := nativeIntegral l E cf'.Z) (AY' := nativeIntegral l E V'.left)
    (BX := nativeSystem l E U.left) (BB := nativeSystem l E cf.Z)
    (BY := nativeSystem l E V.left) (BX' := nativeSystem l E U'.left)
    (BB' := nativeSystem l E cf'.Z) (BY' := nativeSystem l E V'.left)
    (s := (a.realizationModel.reductionPull y.left).hom.app
      ((ringedPush l E cf.g).obj ((ringedOpen l E cf.i).obj L)) ≫
      (pull l E y.left).map
        ((ordinaryPushReduction l E o a.realizationModel cf.g).app
          ((ringedOpen l E cf.i).obj L) ≫ (Operations.push l E o cf.g).map qJ))
    (q₀ := (a.realizationModel.reductionPull z).hom.app ((ringedOpen l E cf.i).obj L) ≫
      (pull l E z).map qJ)
    (q₁ := GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E cf'.i).app
      ((ringedPull l E x.left).obj L)) ≫ (Operations.shriek l E o cf'.i).map
        ((a.realizationModel.reductionPull x.left).hom.app L ≫ (pull l E x.left).map q))
    (L := L) (M := M)
    (ordinaryPushReduction l E o a.realizationModel cf'.g)
    (ringedCompactificationMap l E o a cf cf' x.left y.left z wi wp hi)
    (compactificationMap l E o a cf cf' x.left y.left z wi wp hi)

private meta def ordinaryCompProjection (x : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let args := x.getAppArgs
  if x.isAppOf ``Functor.obj && args.size ≥ 2 then
    let f := args[args.size - 2]!
    if f.isAppOf ``Functor.comp then
      let fs := f.getAppArgs
      let h ← Lean.Meta.mkAppM ``Functor.comp_obj
        #[fs[fs.size - 2]!, fs[fs.size - 1]!, args[args.size - 1]!]
      let rhs := (← Lean.Meta.inferType h).getAppArgs.back!
      return some (rhs, ← Lean.Meta.mkHEqOfEq h)
  return none

-- Reuse the congruence method of IntegralOrdinaryProperOpenSquare locally.
-- Reify definitionally equal presentations into explicit HEq proofs.
-- This keeps the kernel from unfolding chosen derived categories while comparing
-- compound functor expressions. The reflexivity leaves and the resulting casts are
-- all checked by the kernel; this procedure adds no mathematical assumption.
private meta partial def ordinaryTypeCongruence (x y : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if x == y then return ← Lean.Meta.mkHEqRefl x
  if let some (x', h) ← ordinaryCompProjection x then
    return ← Lean.Meta.mkAppM ``HEq.trans #[h, ← ordinaryTypeCongruence x' y]
  if let some (y', h) ← ordinaryCompProjection y then
    return ← Lean.Meta.mkAppM ``HEq.trans
      #[← ordinaryTypeCongruence x y', ← Lean.Meta.mkAppM ``HEq.symm #[h]]
  if (← Lean.Meta.isProof x) && (← Lean.Meta.isProof y) then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[x, y]
  if x.getAppFn == y.getAppFn && x.isApp && x.getAppNumArgs == y.getAppNumArgs then
    let xs := x.getAppArgs
    let ys := y.getAppArgs
    let thm ← Lean.Meta.mkHCongrWithArity x.getAppFn xs.size
    let mut args := #[]
    for a in xs, b in ys, kind in thm.argKinds do
      let h ← ordinaryTypeCongruence a b
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

private theorem compactificationCoefficientOnObjects
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {U V U' V' : Over B}
    (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
    (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
    (hi : IsPullback x.left cf'.i cf.i z)
    (L : Integral l E U.left) (M : System l E U.left)
    (q : (calculus l E U.left).reduction.obj L ⟶ M) :
    ((a.realizationModel.reductionPull y.left).hom.app
          ((ringedPush l E cf.g).obj ((ringedOpen l E cf.i).obj L)) ≫
        (pull l E y.left).map
          ((ordinaryPushReduction l E o a.realizationModel cf.g).app
              ((ringedOpen l E cf.i).obj L) ≫
            (Operations.push l E o cf.g).map
              (GeneratorReduction.inverseOrZero
                  ((a.realizationModel.openReduction l E cf.i).app L) ≫
                (Operations.shriek l E o cf.i).map q))) ≫
        (compactificationExchange l E o a.compositors a.openComparisons
          cf cf' x.left y.left z wi wp hi).app M =
      (calculus l E V'.left).reduction.map
          ((ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
            cf cf' x.left y.left z wi wp hi).app L) ≫
        ((ordinaryPushReduction l E o a.realizationModel cf'.g).app
            ((ringedOpen l E cf'.i).obj ((ringedPull l E x.left).obj L)) ≫
          (Operations.push l E o cf'.g).map
            (GeneratorReduction.inverseOrZero
                ((a.realizationModel.openReduction l E cf'.i).app
                  ((ringedPull l E x.left).obj L)) ≫
              (Operations.shriek l E o cf'.i).map
                ((a.realizationModel.reductionPull x.left).hom.app L ≫
                  (pull l E x.left).map q))) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let args ← #[`l, `E, `o, `a, `f, `f', `cf, `cf', `x, `y, `z,
      `wi, `wp, `hi, `L, `M, `q].mapM fun n ↦
        Lean.Elab.Term.elabTerm (Lean.mkIdent n) none
    let f ← Lean.Meta.mkAppM ``compactificationRaw args
    let hp ← Lean.Meta.mkAppM ``compactificationProperRaw args
    let ho ← Lean.Elab.Term.elabTerm (← Lean.ofExcept
      (Lean.Parser.runParserCategory (← Lean.getEnv) `term
        "open_beta_coeff l E o a x.left cf'.i cf.i z wi hi L M q")) none
    let hot ← Lean.Meta.whnf (← Lean.Meta.inferType ho)
    let lhs := hot.getAppArgs[1]!
    let parts := lhs.getAppArgs
    let tail := parts.back!.getAppArgs
    let assoc ← Lean.Meta.mkAppM ``Category.assoc
      #[parts[parts.size - 2]!, tail[tail.size - 2]!, tail.back!]
    let ho ← Lean.Meta.mkAppM ``Eq.trans #[assoc, ho]
    let ft ← Lean.Meta.whnf (← Lean.Meta.inferType f)
    let pt ← Lean.Meta.whnf (← Lean.Meta.inferType hp)
    let ep ← Lean.Meta.mkEqOfHEq (← ordinaryTypeCongruence pt ft.bindingDomain!)
    let hp ← Lean.Meta.mkAppM ``Eq.mp #[ep, hp]
    let fp := Lean.mkApp f hp
    let fpt ← Lean.Meta.whnf (← Lean.Meta.inferType fp)
    let ot ← Lean.Meta.whnf (← Lean.Meta.inferType ho)
    let eo ← Lean.Meta.mkEqOfHEq (← ordinaryTypeCongruence ot fpt.bindingDomain!)
    let ho ← Lean.Meta.mkAppM ``Eq.mp #[eo, ho]
    let result := Lean.mkApp fp ho
    let out ← Lean.Meta.whnf (← Lean.Meta.inferType result)
    let goal ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
    let e ← Lean.Meta.mkEqOfHEq (← ordinaryTypeCongruence out goal)
    let result ← Lean.Meta.mkAppM ``Eq.mp #[e, result]
    Lean.Elab.Tactic.closeMainGoal `exact result

/-- Ordinary coefficient compatibility with the fixed compactification exchange.
Source: blueprint fix-prop-coherence, the prescribed proper/open exchange composite.
(blueprint: lem-sf-integral-ordinary-compactification-exchange-square).

Proof: write L for the ringed interpretation of e, M for its system interpretation,
and q : R(L) ⟶ M for its ordinary coefficient map. The coefficient of the open
image is the inverse open-reduction component followed by open extension of q.
The helper properPullCoeff supplies the pullback coefficient boundary; applying
matePastingSquare with the actual ringed and system direct-image adjunctions
transposes it to the proper-exchange coefficient square on the open image.
Naturality of properExchange inserts the open-image coefficient. The helper
open_beta_coeff supplies the open base-change square for the same q, obtained
from the inverse-open mate unit equation and open_beta_inverse_square by inverse
cancellation. It applies to every compactification open, without quasi-compactness.
Apply ordinaryPushReduction.naturality to the ringed open base-change component.
Functoriality now pastes these three equalities: proper exchange, proper image
of open base change, and transport of the open coefficient. Expanding the
prescribed compactificationExchangeFromData and ringedCompactificationExchange
identifies precisely the two fixed composites in this statement. Reassociate and
use map_comp to obtain the displayed equality. No completion comparison is used.

The final pasting uses a generic categorical helper and whole-transformation
normalizations. Infer its dependent function type, then transport the proved
proper and open coefficient squares and its conclusion using explicit congruence.
The congruence algorithm follows the private utility in IntegralOrdinaryProperOpenSquare;
its generated equality proofs are checked by the kernel.
-/
theorem ordinaryCompactificationExchangeSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V U' V' : Over B}
    (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
    (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
    (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U) :
    (Expression.pull y (.compactSupport f cf e)).ordinaryReduction l E o a K ≫
        (compactificationExchange l E o a.compositors a.openComparisons
          cf cf' x.left y.left z wi wp hi).app
            (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V'.left).reduction.map
          ((ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
            cf cf' x.left y.left z wi wp hi).app (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f' cf' (.pull x e)).ordinaryReduction l E o a K := by
  exact compactificationCoefficientOnObjects l E o a f f' cf cf' x y z wi wp hi
    (e.ringedObj l E a.ringedModels K)
    (e.systemObj l E o ((inputReduction l E X).obj K)) (e.ordinaryReduction l E o a K)

end WeilConjectures.IntegralSystemRealization
