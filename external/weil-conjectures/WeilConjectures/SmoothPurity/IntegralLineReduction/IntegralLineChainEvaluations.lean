/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence

/-! # Chain cancellation for signed integral lines

Source: latest blueprint, Tate-twist local freeness, proof (3), final two sentences.
(blueprint: lem-pur-integral-line-chain-evaluations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
universe u uC vC r
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Total tensor by the degree-zero signed line, before localization.
Source: Stacks 06YU (blueprint: lem-pur-integral-line-chain-evaluations). -/
def chainTensor (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    Cx.{u, u} l E X none ⥤ Cx.{u, u} l E X none :=
  Prod.sectL (Cx.{u, u} l E X none)
      ((integralLineSingle.{u, u} l E X).obj (power l E X L m)) ⋙
    coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)

/-- The ordinary cancellation formula on every total-complex generator.
Source: Stacks 06YU (blueprint: lem-pur-integral-line-chain-evaluations). -/
def ChainEvaluationFormula (L : scalarReductionSource.{u, u} l E X) (m k : ℤ)
    (e : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (power l E X L k)).obj
        (power l E X L m) ≅ SheafOfModules.unit _)
    (a : chainTensor l E X L m ⋙ chainTensor l E X L k ≅ 𝟭 (Cx.{u, u} l E X none)) : Prop :=
  ∀ P : Cx.{u, u} l E X none,
    (∀ (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U)
          (y : (power l E X L m).val.obj U) (z : (power l E X L k).val.obj U),
        ((a.hom.app P).f i).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
            (integralLineComplex.{u, u} l E X P (power l E X L m))
            ((integralLineSingle.{u, u} l E X).obj (power l E X L k)) i 0 i (add_zero i) U
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P
              ((integralLineSingle.{u, u} l E X).obj (power l E X L m))
              i 0 i (add_zero i) U x y) z) =
          (e.hom.val.app U
            (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
              (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U y z)) • x)

open MonoidalCategory
open Functor
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted

private abbrev chainCoeffRing := completedIntegralCommRingSheafUnrestricted.{u, u} l E X

section OrdinarySite

variable {D : Type uC} [Category.{vC} D] {J : GrothendieckTopology D}
  [EssentiallySmall.{max uC vC r} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC r}]
  (R : Sheaf J CommRingCat.{max uC vC r})

open SheafOfModules.LineEvaluation
set_option quotPrecheck false in
set_option hygiene false in
local notation "Mdl" => SheafOfModules.LineEvaluation.Modules.{uC, vC, r} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "𝒪" => SheafOfModules.unit
  ((sheafCompose J
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R)

private abbrev SiteEvaluation (P Q : Mdl) :=
  (SheafOfModules.siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} (A := R) Q).obj P ≅ 𝒪

private def tensorSiteIso (P Q : Mdl) :
    P ⊗ Q ≅ (SheafOfModules.siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r}
      (A := R) Q).obj P :=
  SheafOfModules.tensorObjIsoSheafification.{vC, uC, max uC vC r} (R := R) P Q ≪≫
    (PresheafOfModules.sheafification.{max uC vC r} (𝟙
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).mapIso
        ((SheafOfModules.siteTensorRightIso.{uC, vC, max uC vC r} R Q.val).app P.val).symm

private theorem tensorSiteIso_pure (P Q : Mdl) (U : Dᵒᵖ)
    (x : P.val.obj U) (y : Q.val.obj U) :
    (tensorSiteIso.{uC, vC, r} R P Q).hom.val.app U
      (pureTensor.{uC, vC, r} R P Q U x y) =
      SheafOfModules.siteSheafTensorTmul.{uC, vC, max uC vC r, max uC vC r} (A := R) P Q U x y := by
  let adj := PresheafOfModules.sheafificationAdjunction.{max uC vC r} (𝟙
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let q := ((SheafOfModules.siteTensorRightIso.{uC, vC, max uC vC r}
    R Q.val).app P.val).inv
  have hi : (SheafOfModules.tensorObjIsoSheafification (R := R) P Q).inv ≫
      (tensorSiteIso.{uC, vC, r} R P Q).hom =
      (PresheafOfModules.sheafification.{max uC vC r} (𝟙
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map q := by
    unfold tensorSiteIso
    simp only [Iso.trans_hom, Iso.inv_hom_id_assoc,
      Functor.mapIso_hom, Iso.symm_hom, q]
  have hi' := congrArg (fun f ↦ f.val.app U
    ((adj.unit.app (P.val ⊗ Q.val)).app U (x ⊗ₜ[R.obj.obj U] y))) hi
  have hn := adj.unit.naturality q
  have hn' := congrArg (fun f ↦ f.app U (x ⊗ₜ[R.obj.obj U] y)) hn
  exact hi'.trans hn'.symm

attribute [local irreducible] tensorSiteIso
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  SheafOfModules.LineEvaluation.cancellation Localization.Monoidal.tensorBifunctor

private def sitePairing (P Q : Mdl) (e : SiteEvaluation.{uC, vC, r} R P Q) :
    P ⊗ Q ≅ 𝒪 := tensorSiteIso.{uC, vC, r} R P Q ≪≫ e

private def siteCancellation (P Q : Mdl) (e : SiteEvaluation.{uC, vC, r} R P Q) :
    tensorRight P ⋙ tensorRight Q ≅ 𝟭 Mdl :=
  cancellation.{uC, vC, r} R P Q (sitePairing.{uC, vC, r} R P Q e)

private theorem siteCancellation_pure (P Q M : Mdl)
    (e : SiteEvaluation.{uC, vC, r} R P Q) (U : Dᵒᵖ)
    (x : M.val.obj U) (y : P.val.obj U) (z : Q.val.obj U) :
    ((siteCancellation.{uC, vC, r} R P Q e).hom.app M).val.app U
      (pureTensor.{uC, vC, r} R _ _ U (pureTensor.{uC, vC, r} R _ _ U x y) z) =
      e.hom.val.app U (SheafOfModules.siteSheafTensorTmul
        (A := R) P Q U y z) • x := by
  unfold siteCancellation sitePairing
  have h := cancellation_pure.{uC, vC, r} R P Q M
    (tensorSiteIso.{uC, vC, r} R P Q ≪≫ e) U x y z
  exact h.trans (congrArg (fun t ↦ e.hom.val.app U t • x)
    (tensorSiteIso_pure.{uC, vC, r} R P Q U y z))

attribute [local irreducible] siteCancellation sitePairing

end OrdinarySite

private theorem chainSiteSmall : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance 3000] chainSiteSmall

private theorem chainWeakSheafify :
    HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := by
  infer_instance

attribute [local instance 3000] chainWeakSheafify

private theorem chainLocallyBijective :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  infer_instance

attribute [local instance 3000] chainLocallyBijective

attribute [local irreducible] tensorSiteIso sitePairing siteCancellation
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  SheafOfModules.LineEvaluation.cancellation Localization.Monoidal.tensorBifunctor

private abbrev termTensor (P : scalarReductionSource.{u, u} l E X) :=
  (tensorRight P).mapHomologicalComplex (.up ℤ)

private def chainCollapse (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    chainTensor l E X L m ≅ termTensor l E X (power l E X L m) := by
  let T := (curriedTensor (scalarReductionSource l E X)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)
  let Q := (CochainComplex.singleFunctor (scalarReductionSource l E X) 0).obj
    (power l E X L m)
  let h : chainTensor l E X L m ≅ T.flip.obj Q :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P P' f
      change ((T.map f).app Q ≫ (T.obj P').map (𝟙 Q)) ≫ 𝟙 _ =
        𝟙 _ ≫ (T.map f).app Q
      erw [(T.obj P').map_id Q]
      simp only [Category.comp_id, Category.id_comp])
  exact h ≪≫ CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (curriedTensor _) (power l E X L m)

private def liftCancellation
    (L : scalarReductionSource.{u, u} l E X) (m k : ℤ)
    (a : tensorRight (power l E X L m) ⋙ tensorRight (power l E X L k) ≅ 𝟭 _) :
    chainTensor l E X L m ⋙ chainTensor l E X L k ≅ 𝟭 _ :=
  isoWhiskerLeft (chainTensor l E X L m) (chainCollapse l E X L k) ≪≫
    isoWhiskerRight (chainCollapse l E X L m) (termTensor l E X (power l E X L k)) ≪≫
    Functor.mapHomologicalComplexCompIso a (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)

private theorem line_cover (P : scalarReductionSource.{u, u} l E X)
    [P.IsFiniteLocallyFreeOfRank 1] :
    ∀ U : X.ProEt, ∃ s : Sieve U, s ∈ ProEt.topology X U ∧
      ∀ (V : X.ProEt) (f : V ⟶ U), s f → Nonempty
        (P.over V ≅ SheafOfModules.unit
          (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (chainCoeffRing l E X)).over V)) := by
  classical
  obtain ⟨I, V, hV, h⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := P) (r := 1)).mp inferInstance
  intro U
  refine ⟨Sieve.ofObjects V U, hV U, ?_⟩
  rintro Z f ⟨i, ⟨g⟩⟩
  let ei := (h i).some ≪≫ SheafOfModules.freeUniqueIso (ULift (Fin 1))
  exact ⟨((SheafOfModules.overFunctorMap _ g).app P).symm ≪≫
    (SheafOfModules.overMap _ g).mapIso ei ≪≫ SheafOfModules.overMapUnitIso g⟩

private def moduleCancellation (L : scalarReductionSource.{u, u} l E X) (m k : ℤ)
    (e : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := chainCoeffRing l E X)
      (power l E X L k)).obj (power l E X L m) ≅ SheafOfModules.unit _) :
    tensorRight (power l E X L m) ⋙ tensorRight (power l E X L k) ≅ 𝟭 _ :=
  siteCancellation.{u + 1, u, u + 1} (chainCoeffRing l E X)
    (power l E X L m) (power l E X L k) e

attribute [local irreducible] moduleCancellation

private theorem moduleCancellation_pure
    (L : scalarReductionSource.{u, u} l E X) (m k : ℤ)
    (e : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := chainCoeffRing l E X)
      (power l E X L k)).obj (power l E X L m) ≅ SheafOfModules.unit _)
    (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) (y : (power l E X L m).val.obj U)
    (z : (power l E X L k).val.obj U) :
    ((moduleCancellation l E X L m k e).hom.app M).val.app U
      (SheafOfModules.LineEvaluation.pureTensor.{u + 1, u, u + 1} (chainCoeffRing l E X) _ _ U
        (SheafOfModules.LineEvaluation.pureTensor.{u + 1, u, u + 1}
          (chainCoeffRing l E X) _ _ U x y) z) =
      e.hom.val.app U (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := chainCoeffRing l E X) _ _ U y z) • x := by
  unfold moduleCancellation
  exact siteCancellation_pure.{u + 1, u, u + 1} (chainCoeffRing l E X)
    (power l E X L m) (power l E X L k) M e U x y z

set_option backward.defeqAttrib.useBackward true in
private theorem collapse_ι_generic
    {M : Type*} [Category* M] [Preadditive M] [HasZeroObject M]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (L : M) (P : CochainComplex M ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor P ((CochainComplex.singleFunctor _ 0).obj L)
        T (.up ℤ) i 0 i (add_zero i) ≫
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso T L).hom.app P).f i =
        (T.obj (P.X i)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom := by
  dsimp [CochainComplex.map₂HomologicalComplexFlipObjSingleIso,
    CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    HomologicalComplex.Hom.isoOfComponents]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  simp [CochainComplex.mapBifunctorSingle₁XIso, HomologicalComplex.singleObjXSelf]

private theorem chainCollapse_ι
    (L : scalarReductionSource.{u, u} l E X) (m : ℤ)
    (P : Cx.{u, u} l E X none) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor P
        ((integralLineSingle l E X).obj (power l E X L m))
        (curriedTensor (scalarReductionSource l E X)) (.up ℤ) i 0 i (add_zero i) ≫
      ((chainCollapse l E X L m).hom.app P).f i = 𝟙 (P.X i ⊗ power l E X L m) := by
  have h := collapse_ι_generic (curriedTensor (scalarReductionSource l E X))
    (power l E X L m) P i
  have hi : ((curriedTensor (scalarReductionSource l E X)).obj (P.X i)).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (power l E X L m)).hom = 𝟙 _ := by
    change (P.X i) ◁ (𝟙 (power l E X L m)) = _
    exact whiskerLeft_id _ _
  dsimp only [chainCollapse, Iso.trans_hom, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp]
  exact h.trans hi

private theorem chainCollapse_generator
    (L : scalarReductionSource.{u, u} l E X) (m : ℤ)
    (P : Cx.{u, u} l E X none) (i : ℤ) (U : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) (y : (power l E X L m).val.obj U) :
    (((chainCollapse l E X L m).hom.app P).f i).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) (chainCoeffRing l E X) P
        ((integralLineSingle l E X).obj (power l E X L m)) i 0 i (add_zero i) U x y) =
      SheafOfModules.LineEvaluation.pureTensor.{u + 1, u, u + 1}
        (chainCoeffRing l E X) _ _ U x y := by
  exact congrArg (fun f ↦ f.val.app U
    (SheafOfModules.LineEvaluation.pureTensor.{u + 1, u, u + 1}
      (chainCoeffRing l E X) _ _ U x y)) (chainCollapse_ι l E X L m P i)

private def unitCancellation {C : Type*} [Category* C] [MonoidalCategory C] :
    tensorRight (𝟙_ C) ⋙ tensorRight (𝟙_ C) ≅ 𝟭 C :=
  (tensorRightTensor (𝟙_ C) (𝟙_ C)).symm ≪≫
    (tensoringRight C).mapIso (ρ_ (𝟙_ C)) ≪≫ rightUnitorNatIso C

private theorem unitCancellation_triangle {C : Type*} [Category* C] [MonoidalCategory C]
    (M : C) :
    (tensorRight (𝟙_ C)).map (unitCancellation.inv.app M) ≫
      unitCancellation.hom.app (M ⊗ 𝟙_ C) = 𝟙 _ := by
  dsimp only [unitCancellation, tensorRightTensor, tensoringRight, rightUnitorNatIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    CategoryTheory.Functor.flip_map_app]
  dsimp only [tensorRight, curriedTensor, CategoryTheory.Functor.flip]
  monoidal_coherence

private theorem reverseCancellation_triangle
    {C : Type*} [Category* C] (F G : C ⥤ C)
    (a : F ⋙ G ≅ 𝟭 C) (b : G ⋙ F ≅ 𝟭 C)
    (h : ∀ M, F.map (a.inv.app M) ≫ b.hom.app (F.obj M) = 𝟙 _) :
    ∀ M, G.map (b.inv.app M) ≫ a.hom.app (G.obj M) = 𝟙 _ := by
  let eqv : C ≌ C := ⟨F, G, a.symm, b, h⟩
  exact eqv.symm.functor_unit_comp

private theorem sheafLineCancellation_triangles
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{max uC vC r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    (R : Sheaf J CommRingCat.{max uC vC r})
    (P : SheafOfModules.LineEvaluation.Modules.{uC, vC, r} R)
    (hP : ∀ U : C, ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), s f → Nonempty
        (P.over V ≅ SheafOfModules.unit
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
    (e : P ⊗ SheafOfModules.LineEvaluation.unitDual.{uC, vC, r} R P ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (e' : SheafOfModules.LineEvaluation.unitDual.{uC, vC, r} R P ⊗ P ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (he : e.hom = SheafOfModules.LineEvaluation.evaluation.{uC, vC, r} R P)
    (he' : e' = (β_ (SheafOfModules.LineEvaluation.unitDual.{uC, vC, r} R P) P) ≪≫ e) :
    let Q := SheafOfModules.LineEvaluation.unitDual.{uC, vC, r} R P
    let a := SheafOfModules.LineEvaluation.cancellation.{uC, vC, r} R P Q e
    let b := SheafOfModules.LineEvaluation.cancellation.{uC, vC, r} R Q P e'
    (∀ M, (tensorRight P).map (a.inv.app M) ≫ b.hom.app (M ⊗ P) = 𝟙 _) ∧
    (∀ M, (tensorRight Q).map (b.inv.app M) ≫ a.hom.app (M ⊗ Q) = 𝟙 _) := by
  dsimp only
  subst e'
  have h := SheafOfModules.LineEvaluation.tensor_triangles.{uC, vC, r} R P hP e he
  exact ⟨h.1, reverseCancellation_triangle _ _ _ _ h.1⟩

private def sheafUnitUnitor
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{max uC vC r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    (R : Sheaf J CommRingCat.{max uC vC r}) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⊗
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  ρ_ _

private theorem sheafUnitUnitor_pure
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{max uC vC r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    (R : Sheaf J CommRingCat.{max uC vC r})
    (U : Cᵒᵖ) (x y : R.obj.obj U) :
    (sheafUnitUnitor.{uC, vC, r} R).hom.val.app U
      (SheafOfModules.LineEvaluation.pureTensor.{uC, vC, r} R _ _ U x y) = y * x := by
  exact SheafOfModules.LineEvaluation.pure_right_unitor.{uC, vC, r} R
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) U x y

private theorem sheafUnitCancellation_triangle
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{max uC vC r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    (R : Sheaf J CommRingCat.{max uC vC r})
    (e : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⊗
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (he : e = sheafUnitUnitor.{uC, vC, r} R)
    (M : SheafOfModules.LineEvaluation.Modules.{uC, vC, r} R) :
    let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    let a := SheafOfModules.LineEvaluation.cancellation.{uC, vC, r} R U U e
    (tensorRight U).map (a.inv.app M) ≫ a.hom.app (M ⊗ U) = 𝟙 _ := by
  subst e
  unfold SheafOfModules.LineEvaluation.cancellation sheafUnitUnitor
  have h := unitCancellation_triangle
    (C := SheafOfModules.LineEvaluation.Modules.{uC, vC, r} R) M
  unfold unitCancellation at h
  exact h

section OrdinarySiteTriangles

attribute [-instance] chainSiteSmall chainWeakSheafify chainLocallyBijective

variable {D : Type uC} [Category.{vC} D] {J : GrothendieckTopology D}
  [EssentiallySmall.{max uC vC r} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC r}]
  (R : Sheaf J CommRingCat.{max uC vC r})

open SheafOfModules.LineEvaluation
set_option quotPrecheck false in
set_option hygiene false in
local notation "Mdl" => SheafOfModules.LineEvaluation.Modules.{uC, vC, r} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "𝒪" => SheafOfModules.unit
  ((sheafCompose J
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R)

private theorem siteLineCancellation_triangles (P : Mdl)
    (hP : ∀ U : D, ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : D) (f : V ⟶ U), s f → Nonempty
        (P.over V ≅ SheafOfModules.unit
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
    (e : SiteEvaluation.{uC, vC, r} R P (unitDual.{uC, vC, r} R P))
    (e' : SiteEvaluation.{uC, vC, r} R (unitDual.{uC, vC, r} R P) P)
    (he : ∀ (U : Dᵒᵖ) (x : P.val.obj U)
      (phi : (unitDual.{uC, vC, r} R P).val.obj U),
      e.hom.val.app U (SheafOfModules.siteSheafTensorTmul.{uC, vC, max uC vC r, max uC vC r}
        (A := R) _ _ U x phi) =
        phi.app (op (Over.mk (𝟙 U.unop))) x)
    (he' : ∀ (U : Dᵒᵖ) (x : P.val.obj U)
      (phi : (unitDual.{uC, vC, r} R P).val.obj U),
      e'.hom.val.app U (SheafOfModules.siteSheafTensorTmul.{uC, vC, max uC vC r, max uC vC r}
        (A := R) _ _ U phi x) =
        phi.app (op (Over.mk (𝟙 U.unop))) x) :
    let Q := unitDual.{uC, vC, r} R P
    let a := siteCancellation.{uC, vC, r} R P Q e
    let b := siteCancellation.{uC, vC, r} R Q P e'
    (∀ M, (tensorRight P).map (a.inv.app M) ≫ b.hom.app (M ⊗ P) = 𝟙 _) ∧
    (∀ M, (tensorRight Q).map (b.inv.app M) ≫ a.hom.app (M ⊗ Q) = 𝟙 _) := by
  let Q := unitDual.{uC, vC, r} R P
  have hp : (sitePairing.{uC, vC, r} R P Q e).hom =
      SheafOfModules.LineEvaluation.evaluation.{uC, vC, r} R P := by
    unfold sitePairing
    apply pure_hom_ext.{uC, vC, r} R
    intro U x phi
    exact (congrArg (fun t ↦ e.hom.val.app U t)
      (tensorSiteIso_pure.{uC, vC, r} R P Q U x phi)).trans
        ((he U x phi).trans (evaluation_pure.{uC, vC, r} R P U x phi).symm)
  have hn : sitePairing.{uC, vC, r} R Q P e' =
      (β_ Q P) ≪≫ sitePairing.{uC, vC, r} R P Q e := by
    unfold sitePairing
    apply Iso.ext
    apply pure_hom_ext.{uC, vC, r} R
    intro U phi x
    have hb := pure_braiding.{uC, vC, r} R Q P U phi x
    have hl := tensorSiteIso_pure.{uC, vC, r} R Q P U phi x
    have hr := tensorSiteIso_pure.{uC, vC, r} R P Q U x phi
    exact (congrArg (fun t ↦ e'.hom.val.app U t) hl).trans
      ((he' U x phi).trans ((he U x phi).symm.trans
        (congrArg (fun t ↦ e.hom.val.app U t)
          ((congrArg (fun t ↦ (tensorSiteIso.{uC, vC, r} R P Q).hom.val.app U t)
            hb).trans hr).symm)))
  dsimp only
  unfold siteCancellation
  exact sheafLineCancellation_triangles.{uC, vC, r} R P hP _ _ hp hn

private theorem siteUnitCancellation_triangle
    (e : SiteEvaluation.{uC, vC, r} R 𝒪 𝒪)
    (he : ∀ (U : Dᵒᵖ) (x y : R.obj.obj U),
      e.hom.val.app U (SheafOfModules.siteSheafTensorTmul.{uC, vC, max uC vC r, max uC vC r}
        (A := R) _ _ U x y) = x * y) :
    let a := siteCancellation.{uC, vC, r} R 𝒪 𝒪 e
    ∀ M, (tensorRight 𝒪).map (a.inv.app M) ≫ a.hom.app (M ⊗ 𝒪) = 𝟙 _ := by
  have hz : sitePairing.{uC, vC, r} R 𝒪 𝒪 e = sheafUnitUnitor.{uC, vC, r} R := by
    unfold sitePairing
    apply Iso.ext
    apply pure_hom_ext.{uC, vC, r} R
    intro U x y
    exact (congrArg (fun t ↦ e.hom.val.app U t)
      (tensorSiteIso_pure.{uC, vC, r} R _ _ U x y)).trans
        ((he U x y).trans ((mul_comm (G := R.obj.obj U) x y).trans
          (sheafUnitUnitor_pure.{uC, vC, r} R U x y).symm))
  dsimp only
  unfold siteCancellation
  exact sheafUnitCancellation_triangle.{uC, vC, r} R _ hz

private def siteSignedPower (L : Mdl) : ℤ → Mdl
  | .ofNat n => SheafOfModules.scalarTensorPower.{uC, vC, max uC vC r} R L n
  | .negSucc n => unitDual.{uC, vC, r} R
      (SheafOfModules.scalarTensorPower.{uC, vC, max uC vC r} R L (n + 1))

private abbrev SiteEvaluations (L : Mdl) :=
  ∀ m : ℤ, SiteEvaluation.{uC, vC, r} R
    (siteSignedPower.{uC, vC, r} R L m) (siteSignedPower.{uC, vC, r} R L (-m))

private def siteReverseEvaluation (L : Mdl) (e : SiteEvaluations.{uC, vC, r} R L) (m : ℤ) :
    SiteEvaluation.{uC, vC, r} R
      (siteSignedPower.{uC, vC, r} R L (-m)) (siteSignedPower.{uC, vC, r} R L m) :=
  eqToIso (congrArg
    (fun T ↦ (SheafOfModules.siteSheafTensorRight
      (A := R) T).obj (siteSignedPower.{uC, vC, r} R L (-m)))
    (congrArg (siteSignedPower.{uC, vC, r} R L) (neg_neg m)).symm) ≪≫ e (-m)

private theorem siteSignedCancellation_triangle (L : Mdl)
    (hL : ∀ (n : ℕ) (U : D), ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : D) (f : V ⟶ U), s f → Nonempty
        ((siteSignedPower.{uC, vC, r} R L (Int.ofNat (n + 1))).over V ≅
          SheafOfModules.unit
            (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
    (e : SiteEvaluations.{uC, vC, r} R L)
    (hzero : ∀ (U : Dᵒᵖ) (x y : R.obj.obj U),
      (e 0).hom.val.app U (SheafOfModules.siteSheafTensorTmul
        (A := R) _ _ U x y) = x * y)
    (hpos : ∀ (n : ℕ) (U : Dᵒᵖ)
      (x : (siteSignedPower.{uC, vC, r} R L (Int.ofNat (n + 1))).val.obj U)
      (phi : (siteSignedPower.{uC, vC, r} R L (Int.negSucc n)).val.obj U),
      (e (Int.ofNat (n + 1))).hom.val.app U (SheafOfModules.siteSheafTensorTmul
        (A := R) _ _ U x phi) = phi.app (op (Over.mk (𝟙 U.unop))) x)
    (hneg : ∀ (n : ℕ) (U : Dᵒᵖ)
      (x : (siteSignedPower.{uC, vC, r} R L (Int.ofNat (n + 1))).val.obj U)
      (phi : (siteSignedPower.{uC, vC, r} R L (Int.negSucc n)).val.obj U),
      (e (Int.negSucc n)).hom.val.app U (SheafOfModules.siteSheafTensorTmul
        (A := R) _ _ U phi x) = phi.app (op (Over.mk (𝟙 U.unop))) x)
    (m : ℤ) :
    ∀ M : Mdl, (tensorRight (siteSignedPower.{uC, vC, r} R L m)).map
      ((siteCancellation.{uC, vC, r} R _ _ (e m)).inv.app M) ≫
      (siteCancellation.{uC, vC, r} R _ _
        (siteReverseEvaluation.{uC, vC, r} R L e m)).hom.app
          (M ⊗ siteSignedPower.{uC, vC, r} R L m) = 𝟙 _ := by
  have ht (n : ℕ) := siteLineCancellation_triangles.{uC, vC, r} R
    (siteSignedPower.{uC, vC, r} R L (Int.ofNat (n + 1))) (hL n)
    (e (Int.ofNat (n + 1))) (e (Int.negSucc n)) (hpos n) (hneg n)
  cases m with
  | ofNat n =>
    cases n with
    | zero => exact siteUnitCancellation_triangle.{uC, vC, r} R (e 0) hzero
    | succ n => exact (ht n).1
  | negSucc n => exact (ht n).2

end OrdinarySiteTriangles

attribute [local instance 3000] chainSiteSmall chainWeakSheafify chainLocallyBijective

attribute [local irreducible] sheafUnitUnitor

private theorem module_triangle
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (e : Evaluations l E X L) (he : EvaluationFormula l E X L e) (m : ℤ) :
    ∀ M : scalarReductionSource.{u, u} l E X,
      (tensorRight (power l E X L m)).map
          ((moduleCancellation l E X L m (-m) (e m)).inv.app M) ≫
        (moduleCancellation l E X L (-m) m
          (reverseEvaluation l E X L e m)).hom.app (M ⊗ power l E X L m) = 𝟙 _ := by
  have hL (n : ℕ) := by
    have : (power l E X L (Int.ofNat (n + 1))).IsFiniteLocallyFreeOfRank 1 := by
      rw [power_eq_coefficient]
      exact lineSignedRank X (chainCoeffRing l E X) L (Int.ofNat (n + 1))
    exact line_cover l E X (power l E X L (Int.ofNat (n + 1)))
  unfold moduleCancellation
  exact siteSignedCancellation_triangle.{u + 1, u, u + 1}
    (chainCoeffRing l E X) L hL e he.1 he.2.1 he.2.2 m

private theorem liftCancellation_triangle_generic
    {C : Type*} [Category* C] [Preadditive C]
    (F G : C ⥤ C) [F.Additive] [G.Additive]
    (F' G' : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (f : F' ≅ F.mapHomologicalComplex (.up ℤ))
    (g : G' ≅ G.mapHomologicalComplex (.up ℤ))
    (a : F ⋙ G ≅ 𝟭 C) (b : G ⋙ F ≅ 𝟭 C)
    (h : ∀ M : C, F.map (a.inv.app M) ≫ b.hom.app (F.obj M) = 𝟙 _) :
    let a' := isoWhiskerLeft F' g ≪≫
      isoWhiskerRight f (G.mapHomologicalComplex (.up ℤ)) ≪≫
      Functor.mapHomologicalComplexCompIso a (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso C (.up ℤ)
    let b' := isoWhiskerLeft G' f ≪≫
      isoWhiskerRight g (F.mapHomologicalComplex (.up ℤ)) ≪≫
      Functor.mapHomologicalComplexCompIso b (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso C (.up ℤ)
    ∀ P, F'.map (a'.inv.app P) ≫ b'.hom.app (F'.obj P) = 𝟙 _ := by
  let e0 : C ≌ C := ⟨F, G, a.symm, b, h⟩
  let ec := ((e0.mapHomologicalComplex (.up ℤ)).changeFunctor f.symm).changeInverse g.symm
  have ha : (isoWhiskerLeft F' g ≪≫
      isoWhiskerRight f (G.mapHomologicalComplex (.up ℤ)) ≪≫
      Functor.mapHomologicalComplexCompIso a (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso C (.up ℤ)) = ec.unitIso.symm := by
    apply Iso.ext
    ext P i
    simp [ec, e0, Equivalence.changeFunctor, Equivalence.changeInverse,
      Equivalence.mapHomologicalComplex]
  have hb : (isoWhiskerLeft G' f ≪≫
      isoWhiskerRight g (F.mapHomologicalComplex (.up ℤ)) ≪≫
      Functor.mapHomologicalComplexCompIso b (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso C (.up ℤ)) = ec.counitIso := by
    apply Iso.ext
    apply NatTrans.ext
    funext P
    dsimp [ec, e0, Equivalence.changeFunctor, Equivalence.changeInverse,
      Equivalence.mapHomologicalComplex]
    rw [← f.hom.naturality_assoc]
    rfl
  dsimp only
  intro P
  rw [ha, hb]
  exact ec.functor_unit_comp P

private theorem liftCancellation_triangle
    (L : scalarReductionSource.{u, u} l E X) (m k : ℤ)
    (a : tensorRight (power l E X L m) ⋙ tensorRight (power l E X L k) ≅ 𝟭 _)
    (b : tensorRight (power l E X L k) ⋙ tensorRight (power l E X L m) ≅ 𝟭 _)
    (h : ∀ M : scalarReductionSource.{u, u} l E X,
      (tensorRight (power l E X L m)).map (a.inv.app M) ≫
        b.hom.app (M ⊗ power l E X L m) = 𝟙 _) :
    ∀ P : Cx.{u, u} l E X none,
      (chainTensor l E X L m).map ((liftCancellation l E X L m k a).inv.app P) ≫
        (liftCancellation l E X L k m b).hom.app ((chainTensor l E X L m).obj P) = 𝟙 _ := by
  exact liftCancellation_triangle_generic
    (tensorRight (power l E X L m)) (tensorRight (power l E X L k))
    (chainTensor l E X L m) (chainTensor l E X L k)
    (chainCollapse l E X L m) (chainCollapse l E X L k) a b h

private theorem liftCancellation_formula
    (L : scalarReductionSource.{u, u} l E X) (m k : ℤ)
    (e : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := chainCoeffRing l E X)
      (power l E X L k)).obj (power l E X L m) ≅ SheafOfModules.unit _) :
    ChainEvaluationFormula l E X L m k e
      (liftCancellation l E X L m k (moduleCancellation l E X L m k e)) := by
  intro P i U x y z
  let Pm := (chainTensor l E X L m).obj P
  let ym := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
    (chainCoeffRing l E X) P ((integralLineSingle l E X).obj (power l E X L m))
      i 0 i (add_zero i) U x y
  change ((moduleCancellation l E X L m k e).hom.app (P.X i)).val.app U
    (((((termTensor l E X (power l E X L k)).map
      ((chainCollapse l E X L m).hom.app P)).f i).val.app U)
        ((((chainCollapse l E X L k).hom.app Pm).f i).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (chainCoeffRing l E X) Pm ((integralLineSingle l E X).obj (power l E X L k))
              i 0 i (add_zero i) U ym z))) = _
  rw [chainCollapse_generator]
  have hm := SheafOfModules.LineEvaluation.pure_map.{u + 1, u, u + 1} (chainCoeffRing l E X)
    (((chainCollapse l E X L m).hom.app P).f i) (𝟙 (power l E X L k)) U ym z
  rw [tensorHom_id] at hm
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hm
  change ((moduleCancellation l E X L m k e).hom.app (P.X i)).val.app U
    (((((chainCollapse l E X L m).hom.app P).f i) ▷ power l E X L k).val.app U _) = _
  erw [hm]
  dsimp only [ym]
  erw [chainCollapse_generator l E X L m P i U x y]
  exact moduleCancellation_pure l E X L m k e (P.X i) U x y z

/-- Opposite signed-line tensors cancel already on unbounded complexes.

Source: latest blueprint, `sk-def-sp-tate-twist-locally-free.proof.md`, (3),
final two sentences; Stacks Project, Tags 0B8N, 0B8Q, and 06YU.
(blueprint: lem-pur-integral-line-chain-evaluations).

Proof: collapse tensor with each degree-zero line to termwise tensor. Reassociate
and apply e(m), respectively the reversed evaluation, followed by the right unit
constraint; transport these termwise isomorphisms back through the collapses.
This defines natural chain isomorphisms: the collapse and termwise constraints
commute with the differentials. Their value on a total generator is e(y,z) times x,
since the two line degrees are zero, so every sign is one. On a covering where
the positive power is free with basis p, its dual has the basis phi with phi(p)=1.
EvaluationFormula identifies both given pairings with functional evaluation.
The inverse cancellation inserts p and phi, in the indicated order. The first
triangle on x tensor cp inserts p,phi then evaluates phi(cp)=c, giving the same
tensor by balancing. Pure tensors generate after sheafification and equality is
local, so the triangle holds globally in each degree. For m=0 the same calculation
is multiplication in the coefficient ring, and for a negative m the two orders
are exchanged. The transport -(-m)=m in reverseEvaluation changes no generator.
The computations hold also on empty covering members, where all sections agree. -/
theorem integral_line_chain_evaluations
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (e : Evaluations l E X L) (he : EvaluationFormula l E X L e) (m : ℤ) :
    ∃ (a : chainTensor l E X L m ⋙ chainTensor l E X L (-m) ≅ 𝟭 (Cx.{u, u} l E X none))
      (b : chainTensor l E X L (-m) ⋙ chainTensor l E X L m ≅ 𝟭 (Cx.{u, u} l E X none)),
      ChainEvaluationFormula l E X L m (-m) (e m) a ∧
      ChainEvaluationFormula l E X L (-m) m (reverseEvaluation l E X L e m) b ∧
      ∀ P : Cx.{u, u} l E X none,
        (chainTensor l E X L m).map (a.inv.app P) ≫
          b.hom.app ((chainTensor l E X L m).obj P) = 𝟙 _ := by
  let a := moduleCancellation l E X L m (-m) (e m)
  let b := moduleCancellation l E X L (-m) m (reverseEvaluation l E X L e m)
  exact ⟨liftCancellation l E X L m (-m) a,
    liftCancellation l E X L (-m) m b,
    liftCancellation_formula l E X L m (-m) (e m),
    liftCancellation_formula l E X L (-m) m (reverseEvaluation l E X L e m),
    liftCancellation_triangle l E X L m (-m) a b (module_triangle l E X L e he m)⟩

end WeilConjectures.IntegralLineReduction
