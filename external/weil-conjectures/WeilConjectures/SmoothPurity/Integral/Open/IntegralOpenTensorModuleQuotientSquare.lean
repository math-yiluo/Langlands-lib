/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenScalarTransitionCompatibility
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSystemUnitSections
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationQuotientUnits
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor

/-! # The ordinary open tensor quotient square on modules

Source: Stacks 0E8I, 03DI and 03CY; Step 3 of the open tensor quotient-model argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian

universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local irreducible] scalarReductionExtension scalarReductionExistence
  completedIntegralCoefficientSheafUnrestricted
  coefficientOrdinaryQuotient coefficientOrdinaryQuotientComponent
  coefficientOrdinaryQuotientNaturalTransformation coefficientQuotientNatTrans
  coefficientIntegralScalarUnitSection coefficientOrdinaryScalarAdjunction
  CoefficientExtensionAssociation.quotientAdjunction
  CategoryTheory.Functor.leftAdjoint CategoryTheory.constantSheaf
  CategoryTheory.presheafToSheaf

-- Prove the mate calculation generically to keep completed coefficient data out of reduction.
private theorem quotient_sections
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (he : SheafOfModules.restrictScalars.{r} g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars h)
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars f)
    {F' : SheafOfModules.{r} R ⥤ SheafOfModules.{r} T}
    (adj' : F' ⊣ SheafOfModules.restrictScalars h)
    (q : F ⟶ F' ⋙ SheafOfModules.restrictScalars g)
    (hq : CoefficientExtensionAssociation.QuotientMateLaw adj adj'
      (SheafOfModules.restrictScalars g) (eqToIso he) q)
    (M : SheafOfModules.{r} R) (W : Cᵒᵖ) (x : M.val.obj W) :
    HEq ((q.app M).val.app W
      (CoefficientExtensionAssociation.normalizedUnitSection f adj M W x))
      (CoefficientExtensionAssociation.normalizedUnitSection h adj' M W x) := by
  have hx := congrArg (fun k ↦ k.val.app W
    (CoefficientExtensionAssociation.normalizedUnitSection f adj M W x)) (hq.app_eq M)
  exact (heq_of_eq hx).trans
    ((CoefficientExtensionAssociation.quotientSectionUnitLaw f g h he adj adj').unit M W x)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X V : Scheme.{t}} (j : X ⟶ V) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

private theorem native_unit_heq (T : Scheme.{t}) (n : ℕ)
    (M : scalarReductionSource l E T) (W : T.ProEtᵒᵖ) (x : M.val.obj W) :
    HEq (CoefficientExtensionAssociation.normalizedUnitSection
      (CoefficientExtensionAssociation.coefficientProjection l E T n)
      (CoefficientExtensionAssociation.quotientAdjunction l E T n) M W x)
      (coefficientIntegralScalarUnitSection l E T n M W x) := by
  have h := OpenSemilinearTensor.nativeUnit_eq l E T M n W x
  unfold CoefficientExtensionAssociation.finiteUnitSection at h
  exact heq_of_eq h

private theorem quotient_native_unit (T : Scheme.{t}) (n : ℕ)
    (M : scalarReductionSource l E T) (W : T.ProEtᵒᵖ) (x : M.val.obj W) :
    HEq (((coefficientOrdinaryQuotient l E T (Nat.le_succ n)).app M).val.app W
      (CoefficientExtensionAssociation.normalizedUnitSection
        (CoefficientExtensionAssociation.coefficientProjection l E T (n + 1))
        (CoefficientExtensionAssociation.quotientAdjunction l E T (n + 1)) M W x))
      (CoefficientExtensionAssociation.normalizedUnitSection
        (CoefficientExtensionAssociation.coefficientProjection l E T n)
        (CoefficientExtensionAssociation.quotientAdjunction l E T n) M W x) := by
  exact quotient_sections
    (CoefficientExtensionAssociation.coefficientProjection l E T (n + 1))
    (normalizedDVRQuotient l E T (Nat.le_succ n))
    (CoefficientExtensionAssociation.coefficientProjection l E T n)
    (coefficientRestrictionComp l E T (Nat.le_succ n))
    (CoefficientExtensionAssociation.quotientAdjunction l E T (n + 1))
    (CoefficientExtensionAssociation.quotientAdjunction l E T n)
    (coefficientOrdinaryQuotient l E T (Nat.le_succ n))
    (CoefficientExtensionAssociation.quotient_mate_law l E T (Nat.le_succ n)) M W x

private theorem quotient_unit_section (T : Scheme.{t}) (n : ℕ)
    (M : scalarReductionSource l E T) (W : T.ProEtᵒᵖ) (x : M.val.obj W) :
    HEq (((coefficientOrdinaryQuotient l E T (Nat.le_succ n)).app M).val.app W
      (coefficientIntegralScalarUnitSection l E T (n + 1) M W x))
      (coefficientIntegralScalarUnitSection l E T n M W x) := by
  have hu := eq_of_heq (native_unit_heq l E T (n + 1) M W x)
  have hm := congrArg
    (fun z ↦ ((coefficientOrdinaryQuotient l E T (Nat.le_succ n)).app M).val.app W z) hu
  exact (heq_of_eq hm).symm.trans
    ((quotient_native_unit l E T n M W x).trans (native_unit_heq l E T n M W x))

private theorem unit_map_section
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars φ)
    {M : SheafOfModules.{r} R} {N : SheafOfModules.{r} S}
    (f : F.obj M ⟶ N) (W : Cᵒᵖ) (x : M.val.obj W) :
    HEq ((adj.unit.app M ≫ (SheafOfModules.restrictScalars φ).map f).val.app W x)
      (f.val.app W (CoefficientExtensionAssociation.normalizedUnitSection φ adj M W x)) := by
  unfold CoefficientExtensionAssociation.normalizedUnitSection
  rfl

private theorem section_apply_heq {A B C : Type r} {f : A → B} {g : C → B}
    {x : A} {y : C} (hf : HEq f g) (hx : HEq x y) : HEq (f x) (g y) :=
  heq_of_eq (congr_heq hf hx)

-- Transpose once, then test on the original open-extension generators.
private theorem scalar_open_generator_ext (n : ℕ) (M : scalarReductionSource l E X)
    (N : normalizedDVRModules l E V n)
    (f g : (scalarReductionExtension l E V n).obj
      ((IntegralOpenReduction.extension l E j o).obj M) ⟶ N)
    (h : ∀ (W : V.ProEt) (a : W ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      f.val.app (op W) (coefficientIntegralScalarUnitSection l E V n
        ((IntegralOpenReduction.extension l E j o).obj M) (op W)
        (IntegralOpenReduction.extensionSection l E j o M W a x)) =
      g.val.app (op W) (coefficientIntegralScalarUnitSection l E V n
        ((IntegralOpenReduction.extension l E j o).obj M) (op W)
        (IntegralOpenReduction.extensionSection l E j o M W a x))) : f = g := by
  apply ((CoefficientExtensionAssociation.quotientAdjunction l E V n).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply OpenSemilinearTensor.extensionSection_ext l E j o M _
  intro W a x
  have hf := unit_map_section (CoefficientExtensionAssociation.coefficientProjection l E V n)
    (CoefficientExtensionAssociation.quotientAdjunction l E V n) f (op W)
    (IntegralOpenReduction.extensionSection l E j o M W a x)
  have hg := unit_map_section (CoefficientExtensionAssociation.coefficientProjection l E V n)
    (CoefficientExtensionAssociation.quotientAdjunction l E V n) g (op W)
    (IntegralOpenReduction.extensionSection l E j o M W a x)
  have hu := OpenSemilinearTensor.nativeUnit_eq l E V
    ((IntegralOpenReduction.extension l E j o).obj M) n (op W)
    (IntegralOpenReduction.extensionSection l E j o M W a x)
  unfold CoefficientExtensionAssociation.finiteUnitSection at hu
  rw [hu] at hf hg
  exact eq_of_heq (hf.trans ((heq_of_eq (h W a x)).trans hg.symm))

/-- Generator normalization makes the ordinary tensor comparison respect quotients.
Source: Stacks 0E8I, 03DI and 03CY; parent Step 3, before passing to complexes.
(blueprint: lem-sf-integral-open-tensor-module-quotient-square).

Proof: work first with a single module M. Transpose the two maps under the scalar
extension/restriction adjunction for the larger quotient. The ordinary quotient's
mate formula makes its transpose the smaller scalar unit followed by the inverse
successive-restriction comparison. The tensor comparison's generator formula and
hgen identify both transposes on every extension summand: both send x to the
smaller scalar-unit image of x in that same summand. Apply the extension/restriction
Hom bijection for the localized site and the sheafification Hom bijection; equality
on direct-sum generators gives equality of the maps. Transposing back gives the
ordinary quotient square. The argument is entirely on modules, before any
complex or localization is used. No flatness, boundedness, completeness or strict
reduction calculus is involved. Empty sums, zero terms and n=0 obey the same formulas. -/
theorem integralOpenTensorModuleQuotientSquare
    (tensor : IntegralOpenReduction.TensorComparison l E j o) (n : ℕ)
    (ordinary : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
          IntegralOpenReduction.finiteExtension l E j o (n + 1) ≅
        IntegralOpenReduction.finiteExtension l E j o n ⋙
          normalizedDVRModuleRes l E V (Nat.le_succ n))
    (hgen : ∀ (M : normalizedDVRModules l E X n) (W : V.ProEt)
        (a : W ⟶ IntegralOpenReduction.openObject j),
        HEq (fun x : ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M).val.obj
            (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
          (ordinary.hom.app M).val.app (op W)
            (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1)
              ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x))
          (fun x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
            IntegralOpenReduction.finiteExtensionSection l E j o n M W a x))
    (M : scalarReductionSource l E X) :
    (coefficientOrdinaryQuotient l E V (Nat.le_succ n)).app
        ((IntegralOpenReduction.extension l E j o).obj M) ≫
      (normalizedDVRModuleRes l E V (Nat.le_succ n)).map
        ((tensor.ordinary n).hom.app M) =
    (tensor.ordinary (n + 1)).hom.app M ≫
      (IntegralOpenReduction.finiteExtension l E j o (n + 1)).map
        ((coefficientOrdinaryQuotient l E X (Nat.le_succ n)).app M) ≫
      ordinary.hom.app ((scalarReductionExtension l E X n).obj M) := by
  apply scalar_open_generator_ext l E j o (n + 1) M _
  intro W a x
  change (((normalizedDVRModuleRes l E V (Nat.le_succ n)).map
      ((tensor.ordinary n).hom.app M)).val.app (op W))
      (((coefficientOrdinaryQuotient l E V (Nat.le_succ n)).app
        ((IntegralOpenReduction.extension l E j o).obj M)).val.app (op W)
          (coefficientIntegralScalarUnitSection l E V (n + 1)
            ((IntegralOpenReduction.extension l E j o).obj M) (op W)
            (IntegralOpenReduction.extensionSection l E j o M W a x))) =
    (ordinary.hom.app ((scalarReductionExtension l E X n).obj M)).val.app (op W)
      (((IntegralOpenReduction.finiteExtension l E j o (n + 1)).map
        ((coefficientOrdinaryQuotient l E X (Nat.le_succ n)).app M)).val.app (op W)
          (((tensor.ordinary (n + 1)).hom.app M).val.app (op W)
            (coefficientIntegralScalarUnitSection l E V (n + 1)
              ((IntegralOpenReduction.extension l E j o).obj M) (op W)
              (IntegralOpenReduction.extensionSection l E j o M W a x))))
  have hleft := restrict_apply_heq
    (normalizedDVRQuotient l E V (Nat.le_succ n)) ((tensor.ordinary n).hom.app M)
    (op W) _ _ (quotient_unit_section l E V n
      ((IntegralOpenReduction.extension l E j o).obj M) (op W)
      (IntegralOpenReduction.extensionSection l E j o M W a x))
  have hleft' := hleft.trans (heq_of_eq (tensor.generators n M W a x))
  rw [tensor.generators, OpenSemilinearTensor.finiteSection_map]
  have hright := section_apply_heq
    (hgen ((scalarReductionExtension l E X n).obj M) W a)
    (quotient_unit_section l E X n M
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
  exact eq_of_heq (hleft'.trans hright.symm)

end WeilConjectures
