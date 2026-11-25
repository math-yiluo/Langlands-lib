/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all WeilConjectures.SixFunctors.Completed.CompletedFreeCellOrdinaryLimit
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.MilnorTower
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.AffineScheme
import all Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import all WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.RingTheory.ProEtale.WContractible
import all Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all Mathlib.RingTheory.RingHom.FaithfullyFlat
import all WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # The normalized completion unit of the completed coefficient sheaf

Source: Bhatt--Scholze, Propositions 3.1.9--3.1.10 and Lemma 6.5.5;
Stacks Project, Tags 099I and 0941.
(blueprint: lem-sf-completed-coefficient-unit-complete)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.IntegralOnSlice.abSheafify
  WeilConjectures.IntegralOnSlice.abLocallyBijective
universe t u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace WeilConjectures
open IntegralOnSlice

section
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (T : AlgebraicGeometry.Scheme.{t})

private theorem coefficientUnit_good :
    Good l E T none ((CochainComplex.singleFunctor (Mod l E T none) 0).obj
      (SheafOfModules.unit (rings l E T none))) := by
  let R := ring l E T none
  let P := (CochainComplex.singleFunctor (Mod l E T none) 0).obj
    (SheafOfModules.unit (rings l E T none))
  let : EssentiallySmall.{max u (t + 1)} (Site T none) := essentiallySmallSelf _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  have hflat (i : ℤ) :
      SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := topology T none) (R := R) (P.X i) := by
    have h : ObjectProperty.flat (P.X i) := by
      by_cases hi : i = 0
      · subst i
        exact ObjectProperty.flat_of_tensorIso
          (leftUnitor (𝟙_ (Mod l E T none)))
      · exact ObjectProperty.flat_of_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2
  have : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i (by omega)
  exact ⟨SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R P 0 hflat, hflat⟩

private theorem globalAugmentation_unit (P : Cx l E T none) (n : ℕ) :
    ((augmentation l E T none).app P).app (op n) =
      (NatTrans.mapHomologicalComplex
        (scalarReductionExtension_adjunction l E T n).choose.unit (.up ℤ)).app P := by
  ext i V x
  exact ((augmentation_existsUnique l E T none).exists.choose_spec P n i V x).trans
    ((scalarReductionExtension_adjunction l E T n).choose_spec (P.X i) V x).symm

private theorem coefficientUnit_normalized (n : ℕ) :
    let B := SheafOfModules.unit (rings l E T none)
    let P := (HomologicalComplex.single (scalarReductionSource l E T) (.up ℤ) 0).obj B
    ∃ e : ((tower l E T none).obj P).obj (op n) ≅
        (HomologicalComplex.single (scalarReductionSource l E T) (.up ℤ) 0).obj
          ((coefficientDiagram l E T).obj (op n)),
      ((augmentation l E T none).app P).app (op n) ≫ e.hom =
        (HomologicalComplex.single (scalarReductionSource l E T) (.up ℤ) 0).map
          (coefficientUnitProjection l E T n) := by
  let B := SheafOfModules.unit (rings l E T none)
  let F := scalarReductionExtension l E T n ⋙ scalarReductionRestriction l E T n
  let S := HomologicalComplex.single (scalarReductionSource l E T) (.up ℤ) 0
  obtain ⟨e, he⟩ := extensionUnit_normalized l E T n
  let e' := (scalarReductionRestriction l E T n).mapIso e
  let eC := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app B ≪≫
    S.mapIso e'
  refine ⟨eC, ?_⟩
  rw [globalAugmentation_unit]
  exact normalizedUnit_single F
    (scalarReductionExtension_adjunction l E T n).choose.unit _ _ e' _ he 0

private theorem coefficientUnit_tower :
    let P := (CochainComplex.singleFunctor (Mod l E T none) 0).obj
      (SheafOfModules.unit (rings l E T none))
    Nonempty (IsLimit (show Cone ((tower l E T none).obj P) from
      { pt := P, π := (augmentation l E T none).app P })) ∧
      ∀ (n : ℕ) (i : ℤ),
        Epi ((integralOperationsTowerStep ((tower l E T none).obj P) n).f i) := by
  classical
  let S := HomologicalComplex.single (scalarReductionSource l E T) (.up ℤ) 0
  let B := SheafOfModules.unit (rings l E T none)
  let P := S.obj B
  let T₁ := (tower l E T none).obj P
  let T₂ := coefficientDiagram l E T ⋙ S
  let c₁ : Cone T₁ := { pt := P, π := (augmentation l E T none).app P }
  let c₂ := S.mapCone (coefficientCone l E T)
  choose e he using coefficientUnit_normalized l E T
  have he' (n : ℕ) : c₁.π.app (op n) ≫ (e n).hom =
      S.map (coefficientUnitProjection l E T n) := he n
  have hunit_epi (n : ℕ) : Epi (c₁.π.app (op n)) := by
    have := coefficientUnitProjection_epi l E T n
    have h : c₁.π.app (op n) ≫ (e n).hom =
        S.map (coefficientUnitProjection l E T n) := he' n
    have : Epi (c₁.π.app (op n) ≫ (e n).hom) := h.symm ▸ inferInstance
    exact (epi_comp_iff_of_isIso _ (e n).hom).1 inferInstance
  let α : T₁ ⟶ T₂ := NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
    intro n
    apply (cancel_epi (c₁.π.app (op (n + 1)))).1
    rw [← Category.assoc, c₁.w (homOfLE n.le_succ).op]
    change c₁.π.app (op n) ≫ (e n).hom =
      (c₁.π.app (op (n + 1)) ≫ (e (n + 1)).hom) ≫ _
    rw [he' n, he' (n + 1)]
    change S.map (coefficientUnitProjection l E T n) =
      S.map (coefficientUnitProjection l E T (n + 1)) ≫
        S.map ((coefficientDiagram l E T).map (homOfLE n.le_succ).op)
    rw [← S.map_comp]
    exact congrArg S.map (by
      simpa only [coefficientCone, NatTrans.ofOpSequence_app,
        Functor.const_obj_map, Category.id_comp] using
        ((coefficientCone l E T).w (homOfLE n.le_succ).op).symm))
  have (n : ℕᵒᵖ) : IsIso (α.app n) := inferInstanceAs (IsIso (e n.unop).hom)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have hc₂ : IsLimit c₂ :=
    isLimitOfPreserves S (coefficientCone_isLimit l E T).some
  have hcone : (Cone.postcompose α).obj c₁ ≅ c₂ := Cone.ext (Iso.refl _) (by
    intro n
    change c₁.π.app n ≫ (e n.unop).hom =
      𝟙 _ ≫ S.map (coefficientUnitProjection l E T n.unop)
    simpa only [Category.id_comp] using he' n.unop)
  refine ⟨⟨(IsLimit.postcomposeHomEquiv (asIso α) _).toFun
    (hc₂.ofIsoLimit hcone.symm)⟩, ?_⟩
  intro n i
  have := coefficientStep_epi l E T n
  have ht : Epi ((T₂.map (homOfLE n.le_succ).op).f i) := by
    simp only [T₂, Functor.comp_map, coefficientDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance
  have h := congrArg (fun f ↦ f.f i) (α.naturality (homOfLE n.le_succ).op)
  simp only [HomologicalComplex.comp_f] at h
  have hc : Epi ((T₁.map (homOfLE n.le_succ).op).f i ≫ (α.app (op n)).f i) := by
    rw [h]
    infer_instance
  exact (epi_comp_iff_of_isIso _ ((α.app (op n)).f i)).1 hc

private theorem coefficientUnit_roos_quasiIso :
    let P := (CochainComplex.singleFunctor (Mod l E T none) 0).obj
      (SheafOfModules.unit (rings l E T none))
    QuasiIso (roosUnit l E T none P) := by
  classical
  let P := (CochainComplex.singleFunctor (Mod l E T none) 0).obj
    (SheafOfModules.unit (rings l E T none))
  let F := (tower l E T none).obj P
  let c : Cone F := { pt := P, π := (augmentation l E T none).app P }
  obtain ⟨hc, ht⟩ := coefficientUnit_tower l E T
  let δ := towerTransitionEndomorphism (K := fun n : ℕ ↦ F.obj (op n))
    (integralOperationsTowerStep F)
  have hδ : Epi δ := by
    apply HomologicalComplex.epi_of_epi_f
    intro i
    let ev := HomologicalComplex.eval (Mod l E T none) (.up ℤ) i
    have hstep (n : ℕ) : Epi ((F ⋙ ev).map (homOfLE n.le_succ).op) := ht n i
    have h : Epi (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ev.obj (F.obj (op n)))
        (fun n ↦ ev.map (integralOperationsTowerStep F n))) := by
      exact AlgebraicGeometry.ProEtale.sheaf_tower_epi T (rings l E T none)
        (F ⋙ ev) hstep
    have hh := AlgebraicGeometry.ProEtale.map_transition ev
      (fun n ↦ F.obj (op n)) (integralOperationsTowerStep F)
    have hcomp : Epi (ev.map δ ≫ piComparison ev (fun n ↦ F.obj (op n))) := by
      rw [hh]
      infer_instance
    exact (epi_comp_iff_of_isIso (ev.map δ) (piComparison ev _)).1 hcomp
  obtain ⟨hz, hk⟩ := AlgebraicGeometry.ProEtale.tower_kernel F c hc.some
    (Fan.mk _ (Pi.π (fun n ↦ F.obj (op n))))
    (productIsProduct _) (productAugmentation l E T none P) δ
    (fun n ↦ Pi.lift_comp_π _ n) (fun n ↦ by
      simp [δ, towerTransitionEndomorphism, towerProductShift,
        integralOperationsTowerStep])
  let S := ShortComplex.mk (productAugmentation l E T none P) δ hz
  have hS : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel hk.some
      mono_f := mono_of_isLimit_fork hk.some
      epi_g := hδ }
  exact AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S hS
    (roosUnit_condition l E T none P)

end

/-- The actual quotient augmentation of the coefficient unit in degree zero
is an isomorphism after passing to the derived category.

Source: Bhatt--Scholze, Propositions 3.1.9--3.1.10, pp. 17--18, and
Lemma 6.5.5, pp. 49--50; Stacks Project, Tags 099I and 0941
(blueprint: lem-sf-completed-coefficient-unit-complete).

Proof: the coefficient sheaf B is the inverse limit of the finite quotient
coefficient sheaves. Tensoring B with each quotient and then restricting scalars
identifies its ordinary reduction with that quotient, by multiplication; the
quotient unit becomes the actual inverse-limit projection. These identifications
commute with the specified successor transitions. The completed-free-cell
ordinary-limit theorem at rank one and degree zero supplies this augmented
limit cone and epimorphic transitions. Its finite-field datum can be chosen
with any prime characteristic different from l and imposes no condition on T.
The pro-etale surjective-tower theorem makes one minus shift on the countable
product epimorphic. The kernel of this map is the ordinary inverse limit, with
its specified projections. Thus the short exact sequence from B[0] into the
product and then one minus shift identifies B[0] quasi-isomorphically with the
product mapping fibre, by the lift having zero shifted-product coordinate.
The coefficient unit is flat and its single complex is K-flat by the bounded
flat theorem, so it is a good representative. completionComparison computes
completion on this representative. The normalization in
completionUnit_existsUnique identifies the quasi-isomorphism just constructed
with completionUnit followed by this comparison. Cancel the comparison to
obtain the assertion. The rank-one product-to-unit isomorphism preserves the
augmentation by naturality. -/
theorem completedCoefficientUnit_completionUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : AlgebraicGeometry.Scheme.{t}) [CompactSpace T] [QuasiSeparatedSpace T]
    (_hl : ∀ x : T, IsUnit (l : T.residueField x)) :
    IsIso ((completionUnit l E T none).app
      ((DerivedCategory.singleFunctor (Mod l E T none) 0).obj
        (SheafOfModules.unit (rings l E T none)))) := by
  let P : (Good l E T none).FullSubcategory :=
    ⟨(CochainComplex.singleFunctor (Mod l E T none) 0).obj
      (SheafOfModules.unit (rings l E T none)), coefficientUnit_good l E T⟩
  have hnorm : (completionUnit l E T none).app (DerivedCategory.Q.obj P.obj) ≫
      (completionComparison l E T none).hom.app P =
        DerivedCategory.Q.map (roosUnit l E T none P.obj) := by
    exact (completionUnit_existsUnique l E T none).exists.choose_spec P
  have : QuasiIso (roosUnit l E T none P.obj) := coefficientUnit_roos_quasiIso l E T
  have : IsIso ((completionUnit l E T none).app (DerivedCategory.Q.obj P.obj) ≫
      (completionComparison l E T none).hom.app P) := by
    rw [hnorm]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((completionUnit l E T none).app (DerivedCategory.Q.obj P.obj))
    ((completionComparison l E T none).hom.app P)

end WeilConjectures
