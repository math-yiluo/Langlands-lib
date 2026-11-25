/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreData
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares

/-! Constructing the normalized finite comparison from raw derived data.

The raw record leaves its finite comparison unconstrained. Replace that field by
the derived scalar-extension square normalized by its universal counit. Tensor
generators identify the prescribed strict quotient with the ordinary square,
which proves the finite-model law without constraining any other field.
(blueprint: lem-pod-reindexing-derived-core-finite-model) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

private def finiteCounit (W : Scheme.{t}) (n : ℕ) :=
  CategoryTheory.derivedCochainCounit (scalarReductionExtension l E W n)
    (coefficientFiniteDerivedExtension l E W n) (scalarReductionCounit l E W n)

private theorem finiteCounit_model (W : Scheme.{t})
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P) (n : ℕ) :
    (finiteCounit l E W n).app P =
      (coefficientFiniteReductionModel l E W P hP.1 n).hom := by
  rw [finiteCounit, CategoryTheory.cochainCounit_app_eq]
  simp only [coefficientFiniteReductionModel, coefficientLocalizedCounitModel,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, asIso_hom]
  change _ = (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫ _ ≫ 𝟙 _
  simp only [Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem finiteSquare (n : ℕ)
    (e : scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n) :
    ∃ φ : coefficientFiniteDerivedExtension l E Y n ⋙
        isoReductionFiniteDerived l E g n ≅
      podOrdinaryReindex l E g ⋙ coefficientFiniteDerivedExtension l E X n,
      ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : integralOperationsGoodComplex l E Y P)
        (hFP : integralOperationsGoodComplex l E X
          ((isoReductionIntegralComplex l E g).obj P)),
        (isoReductionFiniteDerived l E g n).map
            (coefficientFiniteReductionModel l E Y P hP.1 n).hom ≫
            (isoReductionFiniteInverse l E g n).mapDerivedCategoryFactors.hom.app
              (unrestrictedTowerFiniteComplex l E Y n P) ≫
            DerivedCategory.Q.map ((isoReduction_complexSquare l E g n e).app P).hom =
          φ.hom.app (DerivedCategory.Q.obj P) ≫
            (coefficientFiniteDerivedExtension l E X n).map
              ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P) ≫
            (coefficientFiniteReductionModel l E X _ hFP.1 n).hom := by
  let F := isoReductionIntegralInverse l E g
  let G := isoReductionFiniteInverse l E g n
  have : F.IsEquivalence := isoReduction_equivalence g (isoReductionCompletedMap l E g).hom
  have : G.IsEquivalence := isoReduction_equivalence g
    (isoSectionwiseConstantMap g (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
  have hder (W : Scheme.{t}) :
      (coefficientFiniteDerivedExtension l E W n).IsLeftDerivedFunctor
        (scalarReductionCounit l E W n)
        (HomotopyCategory.quasiIso (scalarReductionSource l E W) (.up ℤ)) :=
    (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.1
  have hkan (W : Scheme.{t}) :
      (coefficientFiniteDerivedExtension l E W n).IsRightKanExtension
        (finiteCounit l E W n) := by
    have := hder W
    exact CategoryTheory.cochainCounit_universal _ _ _
  have := hkan Y
  have := hkan X
  have : F.asEquivalence.functor.Additive := inferInstanceAs F.Additive
  have : G.asEquivalence.functor.Additive := inferInstanceAs G.Additive
  obtain ⟨φ, hφ⟩ := CategoryTheory.leftDerivedSquare F.asEquivalence G.asEquivalence
    (scalarReductionExtension l E Y n) (scalarReductionExtension l E X n)
    (coefficientFiniteDerivedExtension l E Y n) (coefficientFiniteDerivedExtension l E X n)
    (finiteCounit l E Y n) (finiteCounit l E X n) e
  refine ⟨φ, ?_⟩
  intro P hP hFP
  have h := hφ P
  change φ.hom.app (DerivedCategory.Q.obj P) ≫
      (coefficientFiniteDerivedExtension l E X n).map
        ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P) ≫
      (finiteCounit l E X n).app ((isoReductionIntegralComplex l E g).obj P) = _ at h
  rw [finiteCounit_model l E Y P hP n, finiteCounit_model l E X _ hFP n] at h
  have hc : ((isoReduction_complexSquare l E g n e).app P).hom =
      (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P := by
    apply HomologicalComplex.Hom.ext
    funext i
    change e.hom.app (P.X i) ≫ 𝟙 _ = e.hom.app (P.X i)
    exact Category.comp_id _
  erw [hc]
  exact h.symm

/-- The finite scalar comparison can be chosen with the prescribed quotient normalization.

STATEMENT-DISPUTED (old version): the raw record permits independently changing
`Q.finite`, so it cannot assert this equality for every such choice.  The corrected
statement chooses that field and retains all the other fields of Q.

Source: blueprint Steps 1 and 5.  Derive the ordinary scalar-extension square,
whose unit fixes its pure-tensor formula.  Tensor generation identifies the supplied
quotient map with this square degreewise.  The universal derived counit then gives
the finite-model equality on good representatives.
(blueprint: lem-pod-reindexing-derived-core-finite-model) -/
theorem podReindexingDerivedCoreData_finiteModel
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (_hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (_htransition : podReindexingCoreQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g) :
    ∃ φ : ∀ n : ℕ, coefficientFiniteDerivedExtension l E Y n ⋙
        isoReductionFiniteDerived l E g n ≅
      podOrdinaryReindex l E g ⋙ coefficientFiniteDerivedExtension l E X n,
    PodCompletionReindex.FiniteModel l E g
      (({ Q with finite := φ } : PodReindexingDerivedCoreData l E g).assemble
        l E g SY SX S β CY CX) := by
  classical
  let e := fun n ↦ (isoReduction_tensorSquare l E g n).choose
  choose φ hφ using fun n ↦ finiteSquare l E g n (e n)
  refine ⟨φ, ?_⟩
  intro P hP n
  have hb : (β P hP n).hom = ((isoReduction_complexSquare l E g n (e n)).app P).hom := by
    apply HomologicalComplex.Hom.ext
    funext i
    rw [Iso.app_hom, isoReduction_complexSquare_component]
    let a := (e n).app (P.X i)
    apply (cancel_epi a.inv).1
    change a.inv ≫ (β P hP n).hom.f i = a.inv ≫ a.hom
    rw [a.inv_hom_id]
    let R := scalarReductionRestriction l E X n
    have : R.Faithful := by
      constructor
      intro M N f h hf
      ext U x
      exact congrArg (fun k ↦ k.val.app U x) hf
    apply R.map_injective
    apply SheafOfModules.UnrestrictedTowerProof.identified_hom_ext
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      ((isoReductionIntegralInverse l E g).obj (P.X i))
      (scalarReductionExtension l E X n) (isoReduction_extension_obj l E X n) _
    intro V b x
    have hs := isoReduction_tensorSection_eq l E X n
      ((isoReductionIntegralInverse l E g).obj (P.X i)) V b x
    apply (congrArg ((R.map (a.inv ≫ (β P hP n).hom.f i)).val.app V) hs).trans
    apply Eq.trans _ (congrArg ((R.map (𝟙 _)).val.app V) hs).symm
    let d := isoSectionwiseConstantMap g (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    let b' := (inv d).hom.app V b
    have hb' : d.hom.app V b' = b :=
      congrArg (fun f ↦ f.hom.app V b) (IsIso.inv_hom_id d)
    have ht := isoReduction_tensorFormula l E g n (e n)
      (isoReduction_tensorUnit l E g n (e n) (isoReduction_tensorSquare l E g n).choose_spec)
      (P.X i) V b' x
    have hbt := hβ P hP n i V.unop b' x
    rw [hb'] at ht hbt
    change (a.hom.val.app V) _ = _ at ht
    change ((β P hP n).hom.f i).val.app V _ = _ at hbt
    change ((β P hP n).hom.f i).val.app V (a.inv.val.app V _) = _
    rw [← ht]
    have ha : a.inv.val.app V (a.hom.val.app V
        (unrestrictedTowerTensorSection l E Y n (P.X i)
          ((proEtaleIsoPostcompose g).op.obj V) b' x)) =
      unrestrictedTowerTensorSection l E Y n (P.X i)
        ((proEtaleIsoPostcompose g).op.obj V) b' x := by
      exact ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.val.app V) a.hom_inv_id) _
    rw [ha]
    exact hbt.trans ht.symm
  dsimp only [PodReindexingDerivedCoreData.assemble]
  rw [hb]
  exact hφ n P hP (S.good l E g P hP)

end WeilConjectures
