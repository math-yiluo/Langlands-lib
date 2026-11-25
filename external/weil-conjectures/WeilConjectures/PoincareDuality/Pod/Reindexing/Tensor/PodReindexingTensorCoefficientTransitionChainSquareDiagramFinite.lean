/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorDescentDiagram
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelTower
import all WeilConjectures.SmoothPurity.Supporting.AdditiveRoosHorizontal

/-! # Finite level square for scalar/reindexing tensor transitions

Auxiliary module for `PodReindexingTensorCoefficientTransitionChainSquareDiagramAux`: the private
finite level square `finiteSquare`, used there through `import all`. It is a separate module so
that its kernel check runs in parallel with the Roos comparisons.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-tensor-chain-square-diagram).
-/

-- Only private declarations: they are used through `import all`.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] podTensorReindexAdditive podTensorScalarZero podTensorMixedLeftZero
  podTensorMixedRightZero
  podTensorReindexLimits podTensorReindexColimits
attribute [local irreducible] integralCompletedTensor integralOrdinaryScalar
  scalarTensorChain scalarTensorOrdinary
  integralOperationsRoos completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor SheafOfModules.monoidalCategory
attribute [local implicit_reducible] podOrdinaryReindex podGoodReindex
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor integralOperationsTensorOnGood
  scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralOperationsCommHasDerivedCategory
  podTensorScalarGoodFunctor podTensorScalarGoodComparison podTensorReindexGoodComparison
  podTensorGoodConstructibleLocalization
  podTensorGoodConstructible podTensorMixedTensorIso podTensorGoodCoefficientTransition
  podTensorTensorReindexDerivedChain
  podTensorTensorScalarDerivedChain podTensorTensorMixedDerivedChain

attribute [local irreducible] integralOrdinaryTensorSection
  integralCompletedScalarMap scalarAdjunction
attribute [local implicit_reducible] integralOperationsTensorLevel
  integralOperationsTensorComposite integralOperationsRestrict
  integralOperationsTensorTowerFunctor
  Functor.ofOpSequence Functor.ofSequence isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
attribute [local instance 2001] integralOperationsFiniteHasMap

private theorem quotientUnitSection
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((D.quotient P hP n).hom.f i).val.app (op U))
        (unrestrictedIntegralTensorSection l E Y n (P.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) 1 x) =
      unrestrictedIntegralTensorSection l E X n
        (((isoReductionIntegralComplex l E g).obj P).X i) (op U) 1 x := by
  have h := hD.2.2.2.2.2.2.1 P hP n i U 1 x
  have ho : ((isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
      (ULift.{u+1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U)) 1 = 1 :=
    (RingCat.Hom.hom _).map_one
  exact h.trans (congrArg (fun c ↦ unrestrictedIntegralTensorSection l E X n
    (((isoReductionIntegralComplex l E g).obj P).X i) (op U) c x) ho)

-- Transposing and evaluating the total tensor maps needs extra elaboration time.
private theorem finiteSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        ((T.tower P Q).hom.app (op n)) ≫
      (scalarTensorLevel l E L ι X n).app
        (((podGoodReindex l E g D).obj P).obj, ((podGoodReindex l E g D).obj Q).obj) ≫
      (integralOperationsTensorLevel l L X n).map (Prod.mkHom
        ((S.complex l E g L ι D D').hom.app P.obj)
        ((S.complex l E g L ι D D').hom.app Q.obj)) =
    (S.complex l E g L ι D D').hom.app
        ((integralOperationsTensorLevel l E Y n).obj (P.obj, Q.obj)) ≫
      (isoReductionIntegralComplex l L g).map
        ((scalarTensorLevel l E L ι Y n).app (P.obj, Q.obj)) ≫
      (T'.tower ((podTensorScalarGoodFunctor l E L ι Y).obj P)
        ((podTensorScalarGoodFunctor l E L ι Y).obj Q)).hom.app (op n) := by
  let G := (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)
  let PX := (podGoodReindex l E g D).obj P
  let QX := (podGoodReindex l E g D).obj Q
  -- After cancelling reindexing, the scalar adjunction tests unit tensor generators.
  apply (cancel_epi (G.map ((T.tower P Q).inv.app (op n)))).mp
  dsimp only [G]
  rw [← Functor.map_comp_assoc]
  rw [← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply HomologicalComplex.hom_ext
  intro k
  apply ((scalarAdjunction l E L ι X).homEquiv _ _).injective
  apply finite_tensor_ext l E X n PX.obj QX.obj k
  intro p q hpq U x y
  subst k
  change (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) at x
  change (Q.obj.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) at y
  let zY : (((integralOperationsTensorLevel l E Y n).obj (P.obj, Q.obj)).X
      (p + q)).val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) :=
    integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
    (op ((proEtaleIsoPostcompose g).obj U.unop))
    (unrestrictedIntegralTensorSection l E Y n _
      (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x)
    (unrestrictedIntegralTensorSection l E Y n _
      (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 y)
  let zX : (((integralOperationsTensorLevel l E X n).obj (PX.obj, QX.obj)).X
      (p + q)).val.obj U := integralOperationsTotalTensorSection l E X n PX.obj QX.obj p q U
    (unrestrictedIntegralTensorSection l E X n _ U 1 x)
    (unrestrictedIntegralTensorSection l E X n _ U 1 y)
  have ht : ((((T.tower P Q).hom.app (op n)).f (p + q)).val.app U) zY = zX := by
    dsimp only [zY, zX, PX, QX]
    rw [hT.1]
    rw [quotientUnitSection l E g D hD, quotientUnitSection l E g D hD]
    rfl
  have hinv : ((((T.tower P Q).inv.app (op n)).f (p + q)).val.app U) zX = zY := by
    have hi := congrArg (fun f ↦ (((f.app (op n)).f (p + q)).val.app U) zY)
      (T.tower P Q).hom_inv_id
    have hh := congrArg
      (fun z ↦ ((((T.tower P Q).inv.app (op n)).f (p + q)).val.app U) z) ht
    with_unfolding_all simp only [NatTrans.id_app, HomologicalComplex.id_f,
      SheafOfModules.id_val, PresheafOfModules.id_app] at hi
    exact hh.symm.trans hi
  have hX := (scalarTensorLevel_existsUnique l E L ι X n).exists.choose_spec
  have hY := (scalarTensorLevel_existsUnique l E L ι Y n).exists.choose_spec
  change scalarTensorLevelNormalization l E L ι X n (scalarTensorLevel l E L ι X n) at hX
  change scalarTensorLevelNormalization l E L ι Y n (scalarTensorLevel l E L ι Y n) at hY
  change (((integralOperationsTensorLevel l L X n).map (Prod.mkHom
      ((S.complex l E g L ι D D').hom.app P.obj)
      ((S.complex l E g L ι D D').hom.app Q.obj))).f (p + q)).val.app U
      ((((scalarTensorLevel l E L ι X n).app (PX.obj, QX.obj)).f (p + q)).val.app U
        (((scalarAdjunction l E L ι X).unit.app
          (((integralOperationsTensorLevel l E X n).obj (PX.obj, QX.obj)).X (p + q))).val.app
          U zX)) =
    ((((T'.tower ((podTensorScalarGoodFunctor l E L ι Y).obj P)
      ((podTensorScalarGoodFunctor l E L ι Y).obj Q)).hom.app (op n)).f (p + q)).val.app U)
      (((((scalarTensorLevel l E L ι Y n).app (P.obj, Q.obj)).f (p + q)).val.app
        (op ((proEtaleIsoPostcompose g).obj U.unop)))
        (((S.ordinary.hom.app _).val.app U)
          ((((integralOrdinaryScalar l E L ι X).map
            (((T.tower P Q).inv.app (op n)).f (p + q))).val.app U)
            (((scalarAdjunction l E L ι X).unit.app
              (((integralOperationsTensorLevel l E X n).obj (PX.obj, QX.obj)).X
                (p + q))).val.app U zX))))
  have hu := scalarAdjunction_unit l E L ι X
    (((integralOperationsTensorLevel l E X n).obj (PX.obj, QX.obj)).X (p + q)) U zX
  simp only [hu]
  erw [scalar_map_tensor]
  erw [hinv]
  have hs (M : scalarReductionSource l E Y)
      (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop))) :
      (S.ordinary.hom.app M).val.app U
        (integralOrdinaryTensorSection l E L ι X
          ((isoReductionIntegralInverse l E g).obj M) U 1 x) =
      integralOrdinaryTensorSection l E L ι Y M
        (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x := by
    have h := hcore.1 M U.unop x 1
    have h1 : (isoReductionCompletedMap l L g).hom.hom.app U 1 = 1 := map_one _
    erw [h1] at h
    with_unfolding_all exact h
  erw [hs]
  dsimp only [zX, zY]
  erw [hX, hY, finite_tensor_map_section]
  erw [finite_reduction_map_section, finite_reduction_map_section]
  erw [hT'.1 ((podTensorScalarGoodFunctor l E L ι Y).obj P)
    ((podTensorScalarGoodFunctor l E L ι Y).obj Q) n p q U.unop]
  erw [quotientUnitSection l L g D' hD' _ _ n p U.unop,
    quotientUnitSection l L g D' hD' _ _ n q U.unop]
  dsimp only [PodReindexCoefficientTransition.complex,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex]
  erw [hs, hs]
  rfl

end WeilConjectures
