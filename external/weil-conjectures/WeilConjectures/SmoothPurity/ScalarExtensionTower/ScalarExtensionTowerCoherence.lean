/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionTensorUnit
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionQuotientAssociation

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComposition
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionQuotientSectionExt
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerPullbackLimitSquare
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitSquare
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTensorModelNormalization
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence
import WeilConjectures.SmoothPurity.Integral.IntegralOperationRoosEffectivity
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData

/-! # Scalar extension on strict quotient models

Source: main-20261015 blueprint, prose-03-02, integral operations;
Stacks Tags 03EL and 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence).

## Main definitions

* `Comparisons`: the pure-tensor-normalized comparisons on whole quotient systems.
* `TensorModel`: the representative-normalized completed tensor realization.

## Main statements

* `square`, `unit`, `composition`: strict tower coherence before localization.
* `quotientModels`: the actual quotient representatives and their association formula.
* `scalarExtensionTowerCoherence`: their identification with the canonical integral maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.coefficientTotalTensor
  SheafOfModules.monoidalCategory
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.integralComparisonSequenceScalarModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] scalar_adj comparisons
  integralComparisonSequenceTensorSection integralComparisonSequenceScalarUnit

-- Check all three normalized maps on homogeneous tensor generators.
/-- Equality before localization, hence for both directions and all quotient transitions.
Source: blueprint integral operations; Stacks 03EL, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: expand the specified scalar association and the two tensor comparisons on
b tensor (x tensor y). Both composites give (b tensor x) tensor (1 tensor y).
The coefficient square commutes on constant sections, hence after sheafification.
Balancing extends the equality to arbitrary scalars in either factor. Homogeneous
tensors generate each summand and the direct sum total, proving equality of chain
maps. Their inverses are equal because the two maps are isomorphisms. Every map
is a sequence-site module map, so this equality and its inverse retain every
horizontal quotient transition, as well as vertical restrictions. -/
theorem square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    leftRoute l E L ι f = rightRoute l E L ι f := by
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ((scalar_adj l E L ι X).homEquiv _ _).injective
  apply ((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).homEquiv _ _).injective
  apply WeilConjectures.total_tensor_sections_ext l E Y P Q n
  intro p q hpq V
  rcases V with ⟨m, U⟩
  intro x y
  subst n
  change
    (((scalar_adj l E L ι X).homEquiv _ _)
      (((leftRoute l E L ι f).hom.app (P, Q)).f (p + q))).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y)) =
    (((scalar_adj l E L ι X).homEquiv _ _)
      (((rightRoute l E L ι f).hom.app (P, Q)).f (p + q))).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y))
  refine (scalar_transpose_section l E L ι X
    ((integralComparisonSequencePullback.{u, u} l E f).obj
      (((tensor l E Y).obj (P, Q)).X (p + q))) _ _
    (op (m, (Scheme.proEtaleBaseChange f).obj U))
    (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y))).trans ?_
  refine Eq.trans ?_ (scalar_transpose_section l E L ι X
    ((integralComparisonSequencePullback.{u, u} l E f).obj
      (((tensor l E Y).obj (P, Q)).X (p + q))) _ _
    (op (m, (Scheme.proEtaleBaseChange f).obj U))
    (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y))).symm
  simp only [leftRoute, rightRoute, leftRouteCore, rightRouteCore, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f,
    SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalar_pull_section l E L ι f
    (((tensor l E Y).obj (P, Q)).X (p + q)) m U
    (generator l E Y P Q p q (op (m, U)) x y)]
  erw [pull_section_naturality l L f
    ((((comparisons l).sigma E L ι Y).hom.app (P, Q)).f (p + q))]
  erw [(comparisons l).sigma_formula E L ι Y P Q p q (op (m, U)) 1 x y]
  erw [pull_tensor_section l L f ((scalar l E L ι Y).obj P)
    ((scalar l E L ι Y).obj Q) p q m U]
  erw [scalar_section_naturality l E L ι X
    ((((comparisons l).c E f).hom.app (P, Q)).f (p + q))]
  erw [pull_tensor_section l E f P Q p q m U x y]
  erw [(comparisons l).sigma_formula E L ι X
    ((pull l E f).obj P) ((pull l E f).obj Q) p q
    (op (m, (Scheme.proEtaleBaseChange f).obj U)) 1
    (pullSection l E f (P.X p) m U x) (pullSection l E f (Q.X q) m U y)]
  erw [WeilConjectures.generator_map]
  erw [scalar_pull_section l E L ι f (P.X p) m U x,
    scalar_pull_section l E L ι f (Q.X q) m U y]
  rfl

/-- Identity extension is the identity under the actual scalar action unitors.
Source: node proof step 7; Stacks 03EL
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: at identity coefficients the scalar-association map multiplies the inserted
coefficient, exactly the action unitor. On x tensor y the tensor comparison inserts
one in the second factor. Applying the two action unitors gives x tensor y again.
These formulas commute with every quotient and restriction, giving the displayed
identities as strict-system equations. -/
theorem unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UnitSquare (pull l E f) (scalar l E E (AlgHom.id ℚ_[l] E) Y)
      (scalar l E E (AlgHom.id ℚ_[l] E) X) (kappa l E E (AlgHom.id ℚ_[l] E) f)
      (scalarUnit l E Y) (scalarUnit l E X) ∧
    TensorUnitSquare (tensor l E Y) (scalar l E E (AlgHom.id ℚ_[l] E) Y)
      ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y) (scalarUnit l E Y) := by
  unfold UnitSquare TensorUnitSquare
  constructor
  · exact map_unit_square _ _ _ _ _ _ (scalar_pull_unit l E f)
  · exact scalarExtensionTensorUnit l E Y
      ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y)
      (fun P Q p q V x y ↦
        (comparisons l).sigma_formula E E (AlgHom.id ℚ_[l] E) Y P Q p q V 1 x y)

attribute [local irreducible] integralCompletedTensor integralDerivedPullback
  integralComparisonDerivedSequenceScalar integralComparisonDerivedSequencePullback
  pullbackReduction scalarReduction tensorReduction derivedSigma

/-- The normalized realization models exist for the named completed tensor and scalar functors.
Source: node proof step 8; Stacks 06YS, 07A4, 0941
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: form the strict quotients of one good representative. For tensor take their
signed total tensor; for scalar use the actual quotient inclusions. K-flat change
of rings and closure under total tensor identify these ordinary complexes with
the derived systems. The coefficient-extension reduction model supplies its
normalized coherent counit. Completed-operation substitution identifies the tensor
limit; scalar extension is its defining strict Roos limit. The K-injective-normalized
Roos bridge identifies these with total derived limit. The generator formulas fix
all tower identifications. Universal localization gives the displayed realizations
and their normalization on every whole-system coherent simultaneous presentation.
The residue-field unit assumption is the invertibility hypothesis of the source. -/
theorem realizationModels (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W) (ML : CompletedOperations.Models.{u, u} l L W)
    (hl : ∀ (a : Bool) (x : W a), IsUnit (l : (W a).residueField x)) :
    ∀ a : Bool, Nonempty (TensorModel l E (W a) (ME.calculus a) (ME.roos a)) ∧
      Nonempty (IntegralComparisonScalarModel.{u, u} l E L ι (W a)
        (ME.calculus a) (ML.roos a)) := by
  intro a
  refine ⟨⟨⟨tensorModelRealization l E (W a) (ME.calculus a),
    tensorModelRealization_normalized l E (W a) (ME.calculus a) (ME.roos a)⟩⟩, ?_⟩
  exact primitiveQuotientScalarModelExistence l E L ι (W a) (hl a)
    (ME.calculus a) (ML.roos a)

private theorem reduction_of_limit_square
    {C D : Type*} [Category C] [Category D] {R : C ⥤ D} {G : D ⥤ C}
    (adj : R ⊣ G) {A B : C} {X Y T : D}
    (a : A ⟶ B) (x : B ⟶ G.obj X) (y : A ⟶ G.obj Y)
    (t : X ⟶ T) (s : Y ⟶ T)
    (h : a ≫ x ≫ G.map t = y ≫ G.map s) :
    R.map a ≫ (R.map x ≫ adj.counit.app X) ≫ t =
      (R.map y ≫ adj.counit.app Y) ≫ s := by
  calc
    _ = R.map (a ≫ x ≫ G.map t) ≫ adj.counit.app T := by
      simp only [R.map_comp, Category.assoc]
      rw [adj.counit_naturality t]
    _ = R.map (y ≫ G.map s) ≫ adj.counit.app T := by rw [h]
    _ = _ := by
      simp only [R.map_comp, Category.assoc]
      rw [adj.counit_naturality s]

/-- The coherent quotient representatives of the canonical completed comparisons.
Together with square, unit, composition and the normalized cochain definitions, this
identifies the actual strict quotient maps and their derived limits, including ramification.
The displayed equations are in the derived category of whole quotient systems;
applying total derived limit gives exactly the two stated integral comparisons.
Source: main-20261015 blueprint, prose-03-02, integral clause;
Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence).
Proof:
1. Use flat-term K-flat representatives P,Q and K-flat change of rings to form
   P_m,Q_m and their scalar extensions. Total tensor and finite pullback preserve
   this representative class; no flatness of A_m to B_m is used.
2. The balanced association (x tensor a) tensor b maps to x tensor iota(a)*b.
   Its inverse inserts one. The coefficient-extension reduction model identifies
   these simultaneously with P tensor B_m,Q tensor B_m, including every transition,
   and makes their coherent systems normalized.
3. Scalar association defines kappa. Tensor balancing gives its inverse; the
   constant coefficient square commutes on constant sections and on sheafification.
4. The signed total tensor comparison defines sigma and c. They preserve each
   bidegree, so preserve the factor (-1)^p in the second differential summand.
5. Both routes on b tensor (x tensor y) give (b tensor x) tensor (1 tensor y).
   Tensor generators, sheafification and direct sums prove the strict square.
6. Reduction preserves multiplication and one. Thus every map and inverse respects
   every quotient transition, and these are equations of strict systems.
7. For identity coefficients multiplication is the action unitor. For E to L to F,
   the direct coefficient map is the composite. Both successive and direct formulas
   multiply d*j(b), so the unit and transitivity equations hold strictly.
8. Apply coefficient-extension reduction and completed-operation tower substitution
   to these normalized systems. Their defining realizations and the canonical
   coherent counits are precisely pullbackReduction, scalarReduction and
   tensorReduction below. The cochain-normalized derivedSigma and the recorded
   derived kappa are the localizations of the same strict chain maps. Their coherent
   counit squares give the two equations, with the specified completed comparisons.
9. Apply total derived limit. Functoriality preserves the square, inverse, units
   and successive-extension equations. The normalized realizations identify the
   limit maps with the canonical scalarPullbackCompleted and scalarTensorCompleted;
   no interchange with arbitrary inverse limits or uniqueness of arbitrary isos is used.
-/
theorem scalarExtensionTowerCoherence (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W) (ML : CompletedOperations.Models.{u, u} l L W)
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true) (ME.calculus true) (ML.roos true))
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι (W false)
      (ME.calculus false) (ML.roos false))
    (TE : TensorModel l E (W false) (ME.calculus false) (ME.roos false))
    (TL : TensorModel l L (W false) (ML.calculus false) (ML.roos false))
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (M N : sfIntegralConstructibleCategory l E (W false)) :
    ∃ (hF : IsSfDerivedComplete l E (W true) ((integralDerivedPullback.{u, u} l E f).obj M.obj))
      (hT : IsSfDerivedComplete l E (W false)
        ((integralCompletedTensor.{u, u} l E (W false)).obj (M.obj, N.obj))),
    ((ML.calculus true).reduction.map
        (scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
      pullbackReduction l L W ML f ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj) ≫
      (integralComparisonDerivedSequencePullback.{u, u} l L f).map
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY M.obj) =
      scalarReduction l E L ι (W true) (ME.calculus true) (ML.calculus true)
          (ML.roos true) SX ((integralDerivedPullback.{u, u} l E f).obj M.obj) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f M.obj) ≫
        (integralComparisonSystemScalarPullback.{u, u} l E L ι f).hom.app
          ((ME.calculus false).reduction.obj M.obj)) ∧
    ((ML.calculus false).reduction.map
        (scalarTensorCompleted l E L ι (W false) M.obj N.obj M.property.1 N.property.1 hT).hom ≫
      tensorReduction l L (W false) (ML.calculus false) (ML.roos false) TL
        ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj)
        ((integralScalarExtension.{u} l E L ι (W false)).obj N.obj) ≫
      (ML.calculus false).systemClosed.tensor.map (Prod.mkHom
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY M.obj)
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY N.obj)) =
      scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY ((integralCompletedTensor.{u, u} l E (W false)).obj (M.obj, N.obj)) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W false)).map
          (tensorReduction l E (W false) (ME.calculus false) (ME.roos false) TE M.obj N.obj) ≫
        (derivedSigma l E L ι (W false) (ME.calculus false) (ML.calculus false)).hom.app
          ((ME.calculus false).reduction.obj M.obj, (ME.calculus false).reduction.obj N.obj)) := by
  let qGood := integralOperationsGoodLocalization.{u, u} l E (W false)
  let weak :=
    (HomologicalComplex.quasiIso (integralTowerModules l E (W false)) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E (W false)).ι
  have : qGood.IsLocalization weak :=
    integralOperationsGoodLocalization_isLocalization l E (W false)
  have : qGood.EssSurj := Localization.essSurj qGood weak
  let PM := qGood.objPreimage M.obj
  let PN := qGood.objPreimage N.obj
  let eM : DerivedCategory.Q.obj PM.obj ≅ M.obj := qGood.objObjPreimageIso M.obj
  let eN : DerivedCategory.Q.obj PN.obj ≅ N.obj := qGood.objObjPreimageIso N.obj
  have hF := ((integralOperationRoos_effectivity l E).1 f PM _
    ((integralDerivedPullback l E f).mapIso eM.symm ≪≫
      (integralDerivedPullbackComparison l E f).app PM)).1
  have hT := ((integralOperationRoos_effectivity l E).2 (W false) PM PN _
    ((integralCompletedTensor l E (W false)).mapIso (Iso.prod eM.symm eN.symm) ≪≫
      (integralCompletedTensorComparison l E (W false)).app (PM, PN))).1
  refine ⟨hF, hT, ?_, ?_⟩
  · have h := scalarTowerPullbackLimitSquare l E L ι W ME ML SX SY f _hX _hY M hF
    simpa only [pullbackReduction, scalarReduction, Category.assoc] using
      reduction_of_limit_square (ML.calculus true).adjunction
        (scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom
        ((ML.pullback f).realization.hom.app
          ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj))
        (SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj M.obj))
        _ _ h
  · have h := scalarTowerTensorLimitSquare l E L ι (W false)
      (ME.calculus false) (ML.calculus false) (ME.roos false) (ML.roos false)
      SY TE TL _hY M N hT
    simpa only [tensorReduction, scalarReduction, Category.assoc] using
      reduction_of_limit_square (ML.calculus false).adjunction
        (scalarTensorCompleted l E L ι (W false) M.obj N.obj
          M.property.1 N.property.1 hT).hom
        (TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj,
            (integralScalarExtension.{u} l E L ι (W false)).obj N.obj))
        (SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E (W false)).obj (M.obj, N.obj))) _ _ h

attribute [local semireducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

/-- Scalar extension of the actual E quotient complex is the actual B quotient complex,
with the balanced association formula and all quotient transitions retained.
Source: node proof steps 1--2, 5--6; Stacks 03EL, 0G7E
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: the coefficient-extension reduction model supplies d and d0. Their finite
values are P tensor B_m and P tensor A_m with the actual quotient transitions.
Associate (x tensor a) tensor b to x tensor iota(a)*b; the inverse inserts one.
Balancing proves inverse identities and naturality. These formulas are chain maps
and commute with every quotient transition because coefficient reduction is a ring
map. They therefore glue to the displayed unique strict-system iso. K-flat change
of rings and closure under total tensor justify every derived interpretation.
Apply square to these E quotient representatives. The resulting iso equality is
exactly the stated scalar-extension square, on the actual models, in both directions.
No flatness of A_m to B_m is required, including in ramified extensions. -/
theorem quotientModels {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (A : CoefficientExtensionSystems.{u, u} l E L ι Y)
    (A0 : CoefficientExtensionSystems.{u, u} l E E (AlgHom.id ℚ_[l] E) Y)
    (M N : sfIntegralConstructibleCategory l E Y)
    (P Q : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (_eP : DerivedCategory.Q.obj P.obj ≅ M.obj) (_eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj) :
    ∃ (d : CoefficientExtensionReductionData.{u, u} l E L ι Y SE SL A)
      (d0 : CoefficientExtensionReductionData.{u, u} l E E (AlgHom.id ℚ_[l] E) Y SE SE A0),
    (∀ K : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory,
      ∃! δ : (scalar l E L ι Y).obj (d0.direct.obj K) ≅ d.direct.obj K,
        ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ)
          (b : (coefficientSequenceCommRingSheaf l L Y).obj.obj (op (n, U.unop)))
          (a : (coefficientSequenceCommRingSheaf l E Y).obj.obj (op (n, U.unop)))
          (x : (K.obj.X i).val.obj U),
          (δ.hom.f i).val.app (op (n, U.unop))
            (integralComparisonSequenceTensorSection l E L ι Y ((d0.direct.obj K).X i)
              (op (n, U.unop)) b
              (modelSection l E E (AlgHom.id ℚ_[l] E) Y SE SE A0 d0 K n i U a x)) =
          modelSection l E L ι Y SE SL A d K n i U
            (((integralComparisonSequenceScalarMap.{u, u} l E L ι Y).hom.app
              (op (n, U.unop))) a * b) x) ∧
    (leftRoute l E L ι f).app (d0.direct.obj P, d0.direct.obj Q) =
      (rightRoute l E L ι f).app (d0.direct.obj P, d0.direct.obj Q) := by
  obtain ⟨d⟩ := coefficientExtensionReductionModel l E L ι Y SE SL A _hY
  obtain ⟨d0⟩ := coefficientExtensionReductionModel l E E (AlgHom.id ℚ_[l] E) Y
    SE SE A0 _hY
  refine ⟨d, d0, ?_, ?_⟩
  · intro K
    obtain ⟨δ, hδ⟩ := quotientAssociation_exists l E L ι Y SE SL A A0 d d0 K
    refine ⟨δ, hδ, ?_⟩
    intro δ' hδ'
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro i
    apply ((scalar_adj l E L ι Y).homEquiv _ _).injective
    apply quotientModelSection_hom_ext l E E (AlgHom.id ℚ_[l] E) Y SE SE A0 d0 K i
    intro n U a x
    rw [scalar_transpose_section, scalar_transpose_section]
    exact (hδ' n i U 1 a x).trans (hδ n i U 1 a x).symm
  · exact congrArg (fun e ↦ e.app (d0.direct.obj P, d0.direct.obj Q)) (square l E L ι f)

end WeilConjectures.ScalarExtensionTower
