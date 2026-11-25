/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import WeilConjectures.SmoothPurity.Integral.IntegralPrincipalConeQuotientComparison
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Invertibility of the canonical strict reduction augmentation

Source: Stacks algebraization.tex Tag 0A0E; Bhatt--Scholze Definition 3.5.2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section LimitComparison
variable {B : Type*} [Category* B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
  [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]

private def limitModelCone (C : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : Cone C.asFunctor where
  pt := ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj C
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app C
      naturality := by
        intro n m f
        ext i
        change 𝟙 (limit (C.X i)) ≫ limit.π (C.X i) m =
          limit.π (C.X i) n ≫ (C.X i).map f
        rw [Category.id_comp, limit.w] }

private def limitModelLimit (C : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    IsLimit (limitModelCone C) := by
  apply HomologicalComplex.isLimitOfEval
  intro i
  exact limit.isLimit (C.X i)

private def limitModelPointIso (C : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj C ≅ limit C.asFunctor :=
  (limitModelLimit C).conePointUniqueUpToIso (limit.isLimit C.asFunctor)

private lemma limitModelPointIso_hom_π (C : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (n : ℕᵒᵖ) :
    (limitModelPointIso C).hom ≫ limit.π C.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app C :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limitModelLimit C) (limit.isLimit C.asFunctor) n

private def limitModelIso :
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor :=
  NatIso.ofComponents limitModelPointIso (by
    intro C D f
    dsimp only [roosLimitFunctor, Functor.comp_map,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    apply limit.hom_ext
    intro n
    change (((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).map f ≫
        (limitModelPointIso D).hom) ≫ limit.π D.asFunctor n =
      ((limitModelPointIso C).hom ≫
        lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)) ≫
          limit.π D.asFunctor n
    simp only [Category.assoc]
    rw [limitModelPointIso_hom_π, lim_map]
    erw [limMap_π]
    rw [← Category.assoc, limitModelPointIso_hom_π]
    exact (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).naturality f)

private lemma limitModel_hom_π (C : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (n : ℕᵒᵖ) :
    limitModelIso.hom.app C ≫ limit.π C.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app C :=
  limitModelPointIso_hom_π C n

end LimitComparison

private theorem complete_roosUnit (W : Scheme.{t})
    (K : IntegralOnSlice.D l E W none)
    (P : IntegralOnSlice.Cx l E W none)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := IntegralOnSlice.ring l E W none) P)
    (r : DerivedCategory.Q.obj P ≅ K)
    (hK : IsDerivedCompleteUnrestricted l E W K) :
    IsIso (r.inv ≫ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E W none P)) := by
  classical
  let : HasExactLimitsOfShape (Discrete ℕ) (IntegralOnSlice.Mod l E W none) :=
    IntegralOnSlice.sliceProductsExact l E W none
  let : HasFiniteBiproducts (IntegralOnSlice.Mod l E W none) :=
    Abelian.hasFiniteBiproducts
  let : CountableAB4Star (IntegralOnSlice.Mod l E W none) :=
    CountableAB4Star.of_hasExactLimitsOfShape_nat (IntegralOnSlice.Mod l E W none)
  let : HasCountableProducts (IntegralOnSlice.D l E W none) :=
    derivedCategory_hasCountableProducts (IntegralOnSlice.Mod l E W none)
  have hloc : IntegralPrincipalCone.locallyComplete l E W
      (integralCompletionScalarValue l E W) K := by
    rcases hK with ⟨D, hl, P₀, G, q, hq, e₀, hprod, δ, hδ⟩
    let := hprod
    let C : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E W none :=
      Functor.ofOpSequence (X := fun n ↦ integralTowerComplex l E W D hl n P₀)
        (fun n ↦ integralTowerTransition l E W D hl P₀ n)
    obtain ⟨ε, hε⟩ := integralStrictRoosTriangle (A := IntegralOnSlice.Mod l E W none) C
    simp only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ] at hδ
    have hε' := hε
    simp only [integralOperationsTowerStep, C,
      Functor.ofOpSequence_map_homOfLE_succ] at hε'
    set_option backward.isDefEq.respectTransparency true in
    obtain ⟨i⟩ := integralRoosIso _ _ _ δ ε hδ hε'
    have hc₀ := integralQuotientLocallyComplete l E W P₀ hq.2
    have hC : (IntegralOnSlice.tower l E W none).obj P₀ = C := by
      rw [integralGlobalTower]
      simp only [C, integralTowerTransition_eq, integralTowerComplex]
      rfl
    have hc₁ := (congrArg (fun B : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E W none ↦
      IntegralPrincipalCone.locallyComplete l E W (integralCompletionScalarValue l E W)
        (DerivedCategory.Q.obj (integralOperationsRoos B))) hC).mp hc₀
    exact integralLocallyComplete_iso l E W (integralCompletionScalarValue l E W) i.symm hc₁
  have hμ := (integralKoszulScalar_existsUnique l E W P).exists.choose_spec
  have hu := (IntegralPrincipalCone.localCriterion l E W
    (integralCompletionScalarValue l E W) (integralScalar_natural l E W)
    P (integralKoszulScalar l E W P) hμ K r).2.mp hloc
  obtain ⟨c, hc⟩ := integralPrincipalConeQuotientComparison l E W P hP
    (integralKoszulScalar l E W P) hμ
  rw [← hc, ← Category.assoc]
  exact IsIso.comp_isIso' hu c.isIso_hom

/-- Completeness makes the specified chain-level reduction augmentation invertible
in any normalized total derived inverse-limit model.

Source: Stacks algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
Bhatt--Scholze Definition 3.5.2; Stacks sites-cohomology.tex, Tag 0941
(blueprint: lem-pur-completed-reduction-augmentation-iso).
Proof:
1. Use the chosen flat-term K-flat P to compute derived reduction at each positive
power of the uniformizer. The finite free two-term resolution of each quotient
identifies its derived tensor with the corresponding Koszul reduction. The maps of
these resolutions induce the given quotient transitions. The tensor units agree
on every section with x mapped to 1 tensor x.
2. Exact countable products of pro-etale module sheaves identify the explicit signed
Koszul fiber with the Roos model of this strict quotient tower. Its unit is the
zero-homotopy lift of the compatible tensor units. The Roos/intrinsic completeness
equivalence makes this particular unit invertible when K is complete. This uses the
normalized explicit unit, rather than an unspecified triangle isomorphism.
3. The strict Roos derivation computes total inverse limit. Its universal property
compares it with source.limit, preserving the comparison on every complex. The
augmentation a has precisely the tensor-unit formula, so under this comparison its
localized composite with source.limit.unit is the explicit unit from step 2.
Precomposing with r.inv gives the displayed map, and hence it is invertible.
Changing the exact or total derived models conjugates by isomorphisms and does not
change invertibility. No claim that a reduced inverse system is constant is used;
empty schemes give the identity map of a zero object. -/
theorem reductionAugmentation_isIso (p : ℕ) [Fact p.Prime] (hlp : l ≠ p)
    (W : Scheme.{t}) (source : SiteLimitData l E W)
    (K : DerivedCategory (Mod W (R l E W)))
    (P : CochainComplex (Mod W (R l E W)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hflat : ∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      W.ProEt inferInstance (ProEt.topology W)
      inferInstance (integralCoefficientAbLocallyBijective.{t, u} W)
      (integralCoefficientAbSheafify.{t, u} W).isRightAdjoint
      (completedIntegralCommRingSheafUnrestricted l E W) (P.X i))
    (r : DerivedCategory.Q.obj P ≅ K)
    (C : CochainComplex (ℕᵒᵖ ⥤ Mod W (R l E W)) ℤ)
    (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E W P)
    (a : P ⟶ ((ordinaryTowerLimit l E W).mapHomologicalComplex (.up ℤ)).obj C)
    (ha : IsReductionAugmentation l E W P C e a)
    (hK : IsDerivedCompleteUnrestricted l E W K) :
    IsIso (r.inv ≫ DerivedCategory.Q.map a ≫ source.limit.unit.app C) := by
  classical
  have _hchar := hlp
  have _hterms := hflat
  let B := Mod W (R l E W)
  let : (ordinaryTowerLimit l E W).Additive := source.limitAdditive
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} W
  let : HasExactLimitsOfShape (Discrete ℕ) B :=
    ProEt.products_exact.{t, u, 0} W (R l E W) ℕ
  obtain ⟨RF, κ, hRF, _⟩ := strictRoosDerivation.{t + 1, t, u}
    (ProEt.topology W) (R l E W) (fun U x y ↦
      @mul_comm ((completedIntegralCommRingSheafUnrestricted l E W).obj.obj U)
        inferInstance x y)
  let := hRF
  let limIso := limitModelIso (B := B)
  let α := (Functor.isoWhiskerRight limIso.symm DerivedCategory.Q).hom ≫ source.limit.unit
  let T := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ)
  have : source.limit.functor.IsRightDerivedFunctor α T := by
    rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
    have := source.limit.universal
    exact (Functor.isLeftKanExtension_iff_of_iso₂ α source.limit.unit
      (Functor.isoWhiskerRight limIso.symm DerivedCategory.Q) (Iso.refl _)
      (by simp [α])).mpr
        (Functor.IsRightDerivedFunctor.isLeftKanExtension
          source.limit.functor source.limit.unit T)
  let ρ := RF.rightDerivedUnique source.limit.functor (roosDerivedUnit κ) α T
  have hn : DerivedCategory.Q.map (roosι C) ≫ κ.hom.app C ≫
      ρ.hom.app (DerivedCategory.Q.obj C) = α.app C := by
    have h := RF.rightDerivedNatTrans_app source.limit.functor (roosDerivedUnit κ)
      α T (𝟙 _) C
    simpa only [ρ, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, roosDerivedUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      roosInclusion, roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj,
      Category.assoc, NatTrans.id_app, Category.id_comp] using h
  have hunit : DerivedCategory.Q.map (limIso.hom.app C ≫ roosι C) ≫
      κ.hom.app C ≫ ρ.hom.app (DerivedCategory.Q.obj C) = source.limit.unit.app C := by
    simp only [Functor.map_comp, Category.assoc, hn]
    dsimp only [α, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Iso.symm_hom]
    rw [← Category.assoc, ← Functor.map_comp, limIso.hom_inv_id_app,
      DerivedCategory.Q.map_id, Category.id_comp]
  have htower : (IntegralOnSlice.tower l E W none).obj P =
      unrestrictedIntegralComplexTower l E W P := by
    rw [integralGlobalTower]
    rfl
  let e' := e ≪≫ (eqToIso htower).symm
  have haug (n : ℕ) : a ≫ limIso.hom.app C ≫ limit.π C.asFunctor (op n) ≫
      e'.hom.app (op n) = ((IntegralOnSlice.augmentation l E W none).app P).app (op n) := by
    dsimp only [limIso]
    rw [← Category.assoc (limitModelIso.hom.app C),
      limitModel_hom_π]
    simp only [e', Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.inv,
      eqToHom_app, eqToHom_refl, Category.comp_id]
    ext i U x
    exact (ha n i U x).trans
      ((IntegralOnSlice.augmentation_existsUnique l E W none).exists.choose_spec
        P n i U x).symm
  have hchain : a ≫ limIso.hom.app C ≫ roosι C =
      IntegralOnSlice.roosUnit l E W none P ≫ integralOperationsRoosMap e'.inv := by
    let u := Pi.lift (fun n : ℕ ↦ limit.π C.asFunctor (op n))
    let v := IntegralOnSlice.productAugmentation l E W none P
    let m := Limits.Pi.map (fun n : ℕ ↦ e'.inv.app (op n))
    have hu : u ≫ roosU C = 0 := by
      apply Pi.hom_ext
      intro n
      simp [u, roosU, towerTransitionEndomorphism, towerProductShift,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, limit.w]
    have hv : v ≫ towerTransitionEndomorphism
        (integralOperationsTowerStep ((IntegralOnSlice.tower l E W none).obj P)) = 0 := by
      apply CochainComplex.HomComplex.Cochain.ofHom_injective
      simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
        CochainComplex.HomComplex.Cochain.ofHom_zero] using
        IntegralOnSlice.roosUnit_condition l E W none P
    have hprod : (a ≫ limIso.hom.app C) ≫ u = v ≫ m := by
      apply Pi.hom_ext
      intro n
      simp only [u, v, m, Category.assoc, Pi.map_π, Pi.lift_comp_π,
        Pi.lift_comp_π_assoc, IntegralOnSlice.productAugmentation]
      apply (cancel_mono (e'.hom.app (op n))).1
      simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using haug n
    unfold integralOperationsRoosMap
    rw [arrowConeMap, ← Category.assoc a]
    exact completedCoconeLift_natural B _ _ m m (integralOperationsRoos_square e'.inv)
      (a ≫ limIso.hom.app C) v u hv hu hprod
  have hroos := complete_roosUnit l E W K P hP r hK
  have hmap : IsIso (DerivedCategory.Q.map (integralOperationsRoosMap e'.inv)) := by
    change IsIso (DerivedCategory.Q.map (integralOperationsRoosFunctor.map e'.inv))
    infer_instance
  have haugIso : IsIso (r.inv ≫ DerivedCategory.Q.map a ≫
      DerivedCategory.Q.map (limIso.hom.app C ≫ roosι C)) := by
    let := hroos
    let := hmap
    rw [← Functor.map_comp, hchain, Functor.map_comp]
    simpa only [Category.assoc] using
      (inferInstance : IsIso ((r.inv ≫ DerivedCategory.Q.map
        (IntegralOnSlice.roosUnit l E W none P)) ≫
          DerivedCategory.Q.map (integralOperationsRoosMap e'.inv)))
  rw [← hunit]
  let := haugIso
  simpa only [Category.assoc] using
    (inferInstance : IsIso ((r.inv ≫ DerivedCategory.Q.map a ≫
      DerivedCategory.Q.map (limIso.hom.app C ≫ roosι C)) ≫ κ.hom.app C ≫
        ρ.hom.app (DerivedCategory.Q.obj C)))

end WeilConjectures.CompletedCoefficientPushforward
