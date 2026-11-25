/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroRepresentativeData
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleClosed
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Scalar extension of the unit class and of the left unitor

The finite scalar adjunction unit sends the global unit class of the completed
coefficients to the global unit class of a finite level, and finite scalar extension
of K-flat representatives is compatible with the left unitors of the total tensor.

Source: Stacks Project, Tags 03CZ, 079P, 07A4 and 08JA.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

/-- Localization of a termwise adjunction unit agrees in the two quotient coordinates.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
theorem localizedUnit_eq
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F : A ⥤ B} {R : B ⥤ A} [F.Additive] [R.Additive] (a : F ⊣ R)
    (Q : CochainComplex A ℤ) :
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      (DerivedCategory.quotientCompQhIso A).hom.app Q ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        (DerivedCategory.quotientCompQhIso A).inv.app
          ((F.mapHomologicalComplex (.up ℤ) ⋙ R.mapHomologicalComplex (.up ℤ)).obj Q) := by
  have hq : (DerivedCategory.quotientCompQhIso A).hom.app Q = 𝟙 _ := rfl
  have hqi (K : CochainComplex A ℤ) :
      (DerivedCategory.quotientCompQhIso A).inv.app K = 𝟙 _ := rfl
  rw [hq, hqi, Category.id_comp, Category.comp_id,
    Adjunction.mapHomotopyCategory_unit_app_quotient]
  rfl

/-- The finite derived scalar unit on a K-flat complex in cochain coordinates.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
theorem coefficientFiniteAdjunction_unit_reductionModel
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          (coefficientFiniteReductionModel l E W Q hQ n).hom ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) =
      DerivedCategory.Q.map
        (((coefficientOrdinaryScalarAdjunction l E W n).mapHomologicalComplex
          (.up ℤ)).unit.app Q) := by
  have h := (derivedScalarExtensionRestrictionAdjunction l E W n).choose_spec Q hQ
  have hfac := (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh_hom_app
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
  have hfac' : (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) := by
    erw [hfac]
    change (scalarReductionDerivedRestriction l E W n).map (𝟙 _) ≫ _ ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [(scalarReductionRestriction l E W n).mapDerivedCategory.map_id,
      DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]
  have hunit : DerivedCategory.Qh.map
      ((((scalarReductionExtension_adjunction l E W n).choose).mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) := by
    exact congrArg DerivedCategory.Qh.map
      (Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
        (scalarReductionExtension_adjunction l E W n).choose Q)
  have hmodel : (coefficientFiniteReductionModel l E W Q hQ n).hom =
      (scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) := by
    dsimp only [coefficientFiniteReductionModel, coefficientLocalizedCounitModel,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app, asIso_hom]
    change (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
    erw [(coefficientFiniteDerivedExtension l E W n).map_id, Category.id_comp]
  refine (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (coefficientFiniteDerivedRestriction l E W n).map f ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))
          hmodel).trans ?_
  exact (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (scalarReductionDerivedRestriction l E W n).map
        ((scalarReductionCounit l E W n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) ≫ f) hfac'.symm).trans
      (h.trans hunit)

/-- The finite reduction model is the universal counit on the quotient.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
theorem coefficientFiniteReductionModel_hom
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) :
    (coefficientFiniteReductionModel l E W Q hQ n).hom =
      (coefficientFiniteDerivedExtension l E W n).map
          ((DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app Q) ≫
        (scalarReductionCounit l E W n).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) ≫
        (DerivedCategory.quotientCompQhIso (scalarReductionTarget l E W n)).hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) := by
  have hqi : (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app Q =
      𝟙 _ := rfl
  have hq (K : CochainComplex (scalarReductionTarget l E W n) ℤ) :
      (DerivedCategory.quotientCompQhIso (scalarReductionTarget l E W n)).hom.app K = 𝟙 _ := rfl
  erw [hqi, hq, Category.comp_id]
  erw [(coefficientFiniteDerivedExtension l E W n).map_id, Category.id_comp]
  dsimp only [coefficientFiniteReductionModel, coefficientLocalizedCounitModel,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app, asIso_hom]
  change (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
  simp only [Category.comp_id]
  erw [(coefficientFiniteDerivedExtension l E W n).map_id, Category.id_comp]

/-- The finite reduction models are natural in chain maps of K-flat complexes.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
theorem coefficientFiniteReductionModel_naturality
    {X Y : CochainComplex (scalarReductionSource l E W) ℤ}
    (hX : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) X)
    (hY : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Y)
    (n : ℕ) (g : X ⟶ Y) :
    (coefficientFiniteDerivedExtension l E W n).map (DerivedCategory.Q.map g) ≫
        (coefficientFiniteReductionModel l E W Y hY n).hom =
      (coefficientFiniteReductionModel l E W X hX n).hom ≫
        DerivedCategory.Q.map (((scalarReductionExtension l E W n).mapHomologicalComplex
          (.up ℤ)).map g) := by
  have hmodel (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q) :
      (coefficientFiniteReductionModel l E W Q hQ n).hom =
        (scalarReductionCounit l E W n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) := by
    dsimp only [coefficientFiniteReductionModel, coefficientLocalizedCounitModel,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app, asIso_hom]
    change (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
    erw [(coefficientFiniteDerivedExtension l E W n).map_id, Category.id_comp]
  rw [hmodel Y hY, hmodel X hX]
  exact (scalarReductionCounit l E W n).naturality ((HomotopyCategory.quotient _ (.up ℤ)).map g)

/-- Maps out of an ordinary finite scalar extension are determined on unit sections.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
theorem scalarReductionExtension_hom_ext (n : ℕ) {M : scalarReductionSource l E W}
    {N : scalarReductionTarget l E W n}
    (f g : (scalarReductionExtension l E W n).obj M ⟶ N)
    (h : ∀ (U : (Scheme.ProEt W)ᵒᵖ) (x : M.val.obj U),
      f.val.app U (((coefficientOrdinaryScalarAdjunction l E W n).unit.app M).val.app U x) =
        g.val.app U (((coefficientOrdinaryScalarAdjunction l E W n).unit.app M).val.app U x)) :
    f = g := by
  apply ((coefficientOrdinaryScalarAdjunction l E W n).homEquiv M N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U x
  exact h U x

/-- Ordinary scalar extension maps unit sections to unit sections.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
theorem scalarReductionExtension_map_unit (n : ℕ) {M M' : scalarReductionSource l E W}
    (g : M ⟶ M') (U : (Scheme.ProEt W)ᵒᵖ) (x : M.val.obj U) :
    ((scalarReductionExtension l E W n).map g).val.app U
        (((coefficientOrdinaryScalarAdjunction l E W n).unit.app M).val.app U x) =
      ((coefficientOrdinaryScalarAdjunction l E W n).unit.app M').val.app U (g.val.app U x) := by
  have hn := (coefficientOrdinaryScalarAdjunction l E W n).unit.naturality g
  exact (congrArg (fun k ↦ k.val.app U x) hn).symm

/-- The completed coefficient ring placed in degree zero.
Source: Stacks 0FPT (auxiliary; not a blueprint node). -/
noncomputable abbrev coefficientIntegralUnitComplex :
    CochainComplex (scalarReductionSource l E W) ℤ :=
  coefficientUnitComplex.{u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

/-- The finite coefficient ring placed in degree zero.
Source: Stacks 0FPT (auxiliary; not a blueprint node). -/
noncomputable abbrev coefficientFiniteUnitComplex (n : ℕ) :
    CochainComplex (normalizedDVRModules l E W n) ℤ :=
  coefficientUnitComplex.{u} (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)

/-- The ordinary scalar unit of the completed unit complex.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
noncomputable abbrev coefficientIntegralUnitComplexUnit (n : ℕ) :=
  ((coefficientOrdinaryScalarAdjunction l E W n).mapHomologicalComplex (.up ℤ)).unit.app
    (coefficientIntegralUnitComplex l E W)

/-- The global section of the finite reduction of the unit complex obtained by
transporting the scalar unit along the ordinary scalar-sections comparison.
Source: Stacks 03CZ, 08JA (auxiliary; not a blueprint node). -/
noncomputable def coefficientFiniteUnitSection (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ) :
    SheafOfModules.unit _ ⟶ (((scalarReductionExtension l E W n).mapHomologicalComplex
      (.up ℤ)).obj (coefficientIntegralUnitComplex l E W)).X 0 :=
  (D.ordinaryScalarSections n).hom.app
    ((((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
      (coefficientIntegralUnitComplex l E W)).X 0)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) _).inv ≫
      (coefficientIntegralUnitComplexUnit l E W n).f 0)

/-- The map from the finite unit complex to the finite reduction of the completed unit
complex given by the transported scalar unit.
Source: Stacks 03CZ, 08JA (auxiliary; not a blueprint node). -/
noncomputable def coefficientFiniteUnitComparison
    (D : CoefficientDerivedSystemScalarCoherence l E W) (n : ℕ) :
    coefficientFiniteUnitComplex l E W n ⟶
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
        (coefficientIntegralUnitComplex l E W) :=
  HomologicalComplex.mkHomFromSingle (coefficientFiniteUnitSection l E W D n) (by
    intro k _
    simp only [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.single_obj_d]
    have := coefficientFiniteExtensionAdditive l E W n
    erw [Functor.map_zero, comp_zero])

/-- The ordinary scalar-sections comparison applied termwise to a complex.
Source: Stacks 03CZ, 08JA (auxiliary; not a blueprint node). -/
noncomputable def coefficientScalarSectionsChainMap
    (D : CoefficientDerivedSystemScalarCoherence l E W) (n : ℕ)
    (I : CochainComplex (scalarReductionTarget l E W n) ℤ) :
    ((coefficientOrdinarySections.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((scalarReductionRestriction l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
    ((coefficientOrdinarySections.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I :=
  (NatTrans.mapHomologicalComplex (D.ordinaryScalarSections n).hom (.up ℤ)).app I

/-- The scalar-sections comparison on complexes, unfolded from the model equation.
Source: Stacks 079P, 08JA (auxiliary; not a blueprint node). -/
theorem coefficientScalarSections_model_eq (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ) (I : CochainComplex (scalarReductionTarget l E W n) ℤ) :
    coefficientSiteSectionsComparison.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        (((scalarReductionRestriction l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      (coefficientIntegralSections l E W).map
          ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I) ≫
      (D.scalarSections n).hom.app (DerivedCategory.Q.obj I) =
    (@DerivedCategory.Q AddCommGrpCat.{max u (t + 1)} _ _ (HasDerivedCategory.standard _)).map
      (coefficientScalarSectionsChainMap l E W D n I) ≫
      coefficientSiteSectionsComparison.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) I := by
  exact D.scalarSections_model n I

/-- The finite unit comparison sends the unit section to the transported scalar unit.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
theorem coefficientFiniteUnitComparison_unit (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ) :
    (((coefficientOrdinarySections.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (coefficientFiniteUnitComparison l E W D n)).f 0
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            (integralCoefficientCommRingSheaf l E W n)))).inv =
      coefficientFiniteUnitSection l E W D n := by
  rw [Functor.mapHomologicalComplex_map_f]
  refine (congrArg (fun g ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (integralCoefficientCommRingSheaf l E W n)))).inv ≫ g)
    (HomologicalComplex.mkHomFromSingle_f _ _)).trans ?_
  exact Iso.inv_hom_id_assoc _ _

/-- The termwise scalar-sections comparison sends the scalar unit to the transported unit.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
theorem coefficientScalarSectionsChainMap_unit (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ) :
    (coefficientScalarSectionsChainMap l E W D n
      (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
        (coefficientIntegralUnitComplex l E W))).f 0
      ((((coefficientOrdinarySections.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (coefficientIntegralUnitComplexUnit l E W n)).f 0
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
              (completedIntegralCommRingSheafUnrestricted l E W)))).inv) =
      coefficientFiniteUnitSection l E W D n :=
  rfl

private theorem cyclesMap_comp_apply_eq_of_components
    {X Y Z X' : CochainComplex AddCommGrpCat.{u} ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X' ⟶ Z)
    (x : X.cycles 0) (y : X'.cycles 0)
    (x₀ : X.X 0) (y₀ : X'.X 0)
    (hx : X.iCycles 0 x = x₀) (hy : X'.iCycles 0 y = y₀)
    (hf : g.f 0 (f.f 0 x₀) = h.f 0 y₀) :
    HomologicalComplex.cyclesMap g 0 (HomologicalComplex.cyclesMap f 0 x) =
      HomologicalComplex.cyclesMap h 0 y := by
  apply (AddCommGrpCat.mono_iff_injective (Z.iCycles 0)).1 inferInstance
  have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i g 0)
    (HomologicalComplex.cyclesMap f 0 x)
  have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f 0) x
  have h3 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i h 0) y
  simp only [ConcreteCategory.comp_apply] at h1 h2 h3
  rw [h1, h3, h2, hx, hy]
  exact hf

/-- The global cycles of the transported scalar unit and of the finite unit agree.
Source: Stacks 03CZ, 08JA (auxiliary; not a blueprint node). -/
theorem coefficientFiniteUnitComparison_cycles (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ) :
    HomologicalComplex.cyclesMap
        (coefficientScalarSectionsChainMap l E W D n
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
            (coefficientIntegralUnitComplex l E W))) 0
        (HomologicalComplex.cyclesMap
          (((coefficientOrdinarySections.{u, t + 1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (coefficientIntegralUnitComplexUnit l E W n)) 0
          (coefficientUnitCycle.{u} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W))) =
      HomologicalComplex.cyclesMap
        (((coefficientOrdinarySections.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (coefficientFiniteUnitComparison l E W D n)) 0
        (coefficientUnitCycle.{u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)) := by
  refine cyclesMap_comp_apply_eq_of_components _ _ _ _ _ _ _
    (coefficientUnitCycle_iCycles.{u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W))
    (coefficientUnitCycle_iCycles.{u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)) ?_
  exact (coefficientScalarSectionsChainMap_unit l E W D n).trans
    (coefficientFiniteUnitComparison_unit l E W D n).symm

private theorem homologyClass_map_eq_of_cyclesMap_eq
    {X Y : CochainComplex AddCommGrpCat.{u} ℤ} (φ : X ⟶ Y)
    (x : X.cycles 0) (y : Y.cycles 0) (h : HomologicalComplex.cyclesMap φ 0 x = y) :
    (@DerivedCategory.homologyFunctor AddCommGrpCat.{u} _ _
      (HasDerivedCategory.standard _) 0).map
        ((@DerivedCategory.Q AddCommGrpCat.{u} _ _ (HasDerivedCategory.standard _)).map φ)
        ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} _ _
          (HasDerivedCategory.standard _) 0).inv.app X (X.homologyπ 0 x)) =
      (@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} _ _
        (HasDerivedCategory.standard _) 0).inv.app Y (Y.homologyπ 0 y) := by
  subst y
  exact homologyFunctorFactors_inv_homologyπ_naturality φ x

private theorem unitClass_eq_of_scalar_model
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F : A ⥤ C) (G : B ⥤ C) (R : B ⥤ A) (H : C ⥤ AddCommGrpCat.{u})
    (α : R ⋙ F ⟶ G) {X K : A} {Y I V : B} {P Q : C}
    (η : X ⟶ R.obj Y) (p : Y ≅ I) (v : X ⟶ K) (r : K ⟶ R.obj I) (w : V ⟶ I)
    (a : P ⟶ F.obj K) (b : Q ⟶ G.obj I) (f : P ⟶ Q)
    (x : H.obj (F.obj X)) (y : H.obj (G.obj V)) (z : H.obj P) (z' : H.obj Q)
    (hu : η ≫ R.map p.hom = v ≫ r)
    (hm : a ≫ F.map r ≫ α.app I = f ≫ b)
    (ha : H.map (F.map v) x = H.map a z)
    (hb : H.map (G.map w) y = H.map b z')
    (hz : H.map f z = z') :
    H.map (F.map η ≫ α.app Y) x = H.map (G.map (w ≫ p.inv)) y := by
  have key : H.map (G.map p.hom) (H.map (F.map η ≫ α.app Y) x) =
      H.map (G.map w) y := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Category.assoc,
      ← α.naturality, Functor.comp_map, ← Category.assoc, ← F.map_comp, hu,
      F.map_comp, Category.assoc, Functor.map_comp, ConcreteCategory.comp_apply, ha, hb]
    have hm' := ConcreteCategory.congr_hom (congrArg H.map hm) z
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hm' ⊢
    exact hm'.trans (congrArg (H.map b) hz)
  have e1 := ((G ⋙ H).mapIso p).hom_inv_id_apply
  rw [G.map_comp, H.map_comp (G.map w), ConcreteCategory.comp_apply, ← key]
  exact (e1 _).symm

/-- The finite scalar adjunction unit followed by the scalar-sections comparison sends
the completed unit class to the finite unit class, along the transported scalar unit.
Source: Stacks 03CZ, 079P, 08JA (auxiliary; not a blueprint node).
Proof: after the finite reduction model, the derived unit is the localized ordinary
unit. The scalar-sections model turns the global class of its unit cycle into the
global class of the transported cycle, which is the unit cycle of the finite unit
complex mapped along the transported scalar unit. -/
theorem coefficientFiniteAdjunction_unit_unitClass
    (D : CoefficientDerivedSystemScalarCoherence l E W) (n : ℕ) :
    (@DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} _ _
      (HasDerivedCategory.standard _) 0).map
        ((coefficientIntegralSections l E W).map
            ((coefficientFiniteAdjunction l E W n).unit.app
              (DerivedCategory.Q.obj (coefficientIntegralUnitComplex l E W))) ≫
          (D.scalarSections n).hom.app ((coefficientFiniteDerivedExtension l E W n).obj
            (DerivedCategory.Q.obj (coefficientIntegralUnitComplex l E W))))
        (coefficientUnitClass.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)) =
      (@DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} _ _
        (HasDerivedCategory.standard _) 0).map
        ((coefficientFiniteSections l E W n).map
          (DerivedCategory.Q.map (coefficientFiniteUnitComparison l E W D n) ≫
            (coefficientFiniteReductionModel l E W _
              (coefficientUnitComplex_isKFlat.{u} _ _) n).inv))
        (coefficientUnitClass.{u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)) := by
  let UA := coefficientIntegralUnitComplex l E W
  let hUA := coefficientUnitComplex_isKFlat.{u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let I := ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj UA
  let pU := coefficientFiniteReductionModel l E W UA hUA n
  have hu := coefficientFiniteAdjunction_unit_reductionModel l E W UA hUA n
  have hu' : (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj UA) ≫
      (coefficientFiniteDerivedRestriction l E W n).map pU.hom =
      DerivedCategory.Q.map (coefficientIntegralUnitComplexUnit l E W n) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I := by
    exact (Iso.eq_comp_inv
      ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.app I)).2
        ((Category.assoc _ _ _).trans hu)
  have hm := coefficientScalarSections_model_eq l E W D n I
  have hA := coefficientUnitClass_map.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj I)
    (coefficientIntegralUnitComplexUnit l E W n)
  have hB := coefficientUnitClass_map.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n) I (coefficientFiniteUnitComparison l E W D n)
  have hnat := homologyClass_map_eq_of_cyclesMap_eq
    (coefficientScalarSectionsChainMap l E W D n I)
    (HomologicalComplex.cyclesMap
      (((coefficientOrdinarySections.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (coefficientIntegralUnitComplexUnit l E W n)) 0
      (coefficientUnitCycle.{u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)))
    _ (coefficientFiniteUnitComparison_cycles l E W D n)
  exact unitClass_eq_of_scalar_model
    (coefficientIntegralSections l E W) (coefficientFiniteSections l E W n)
    (coefficientFiniteDerivedRestriction l E W n)
    (@DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} _ _
      (HasDerivedCategory.standard _) 0)
    (D.scalarSections n).hom
    ((coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj UA)) pU
    (DerivedCategory.Q.map (coefficientIntegralUnitComplexUnit l E W n))
    ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I)
    (DerivedCategory.Q.map (coefficientFiniteUnitComparison l E W D n))
    _ _ _ _ _ _ _ hu' hm hA hB hnat

end WeilConjectures
