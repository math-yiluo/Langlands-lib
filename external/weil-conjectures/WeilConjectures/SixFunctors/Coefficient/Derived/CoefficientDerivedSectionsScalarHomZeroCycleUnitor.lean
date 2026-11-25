/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleScalar

/-! # Finite scalar extension of the left unitor

On a K-flat complex, the finite tensor comparison carries the scalar extension of the
left unitor of the total tensor to the left unitor at the finite level, along the
transported scalar unit of the unit complex.

Source: Stacks Project, Tags 03CZ, 03EK, 07A4 and 06YY.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The K-flat tensor model comparison is natural in chain maps of K-flat complexes.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
theorem CoefficientTensorModels.iso_naturality
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    {P P' L L' : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ}
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := A) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := A) P')
    (hL : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := A) L)
    (hL' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := A) L')
    (f : P ⟶ P') (g : L ⟶ L') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J A).map (Prod.mkHom f g)) ≫
        (CoefficientTensorModels.iso.{u, c, v, w} J A S T P' L' hP' hL').hom =
      (CoefficientTensorModels.iso.{u, c, v, w} J A S T P L hP hL).hom ≫
        S.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) :=
  by
  have h := T.comparison.hom.naturality (X := (⟨P, hP⟩, ⟨L, hL⟩)) (Y := (⟨P', hP'⟩, ⟨L', hL'⟩))
    (Prod.mkHom (ObjectProperty.homMk f) (ObjectProperty.homMk g))
  simp only [coefficientKFlatInclusion, Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
    ObjectProperty.homMk_hom] at h
  exact h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence


/-- The finite unit comparison sends `1` to the scalar unit section of `1`.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
theorem coefficientFiniteUnitComparison_apply_one
    (D : CoefficientDerivedSystemScalarCoherence l E W) (n : ℕ) (V : (Scheme.ProEt W)ᵒᵖ) :
    ((coefficientFiniteUnitComparison l E W D n).f 0).val.app V
        (coefficientUnitComplexSection.{u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) V 1) =
      ((coefficientOrdinaryScalarAdjunction l E W n).unit.app
        ((coefficientIntegralUnitComplex l E W).X 0)).val.app V
        (coefficientUnitComplexSection.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) V 1) := by
  have h1 : (coefficientFiniteUnitComparison l E W D n).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) _).hom ≫
        coefficientFiniteUnitSection l E W D n :=
    HomologicalComplex.mkHomFromSingle_f _ _
  have h2 := D.ordinaryScalarSections_formula n
    ((((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
      (coefficientIntegralUnitComplex l E W)).X 0)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) _).inv ≫
      (coefficientIntegralUnitComplexUnit l E W n).f 0) V 1
  have h3 := congrArg (fun k ↦ k.val.app V (1 : (integralCoefficientSheaf l E W n).obj.obj V))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
      (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (integralCoefficientCommRingSheaf l E W n)))).inv_hom_id
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply] at h3
  rw [h1]
  refine (congrArg (fun y ↦ (coefficientFiniteUnitSection l E W D n).val.app V y) h3).trans ?_
  refine h2.trans ?_
  exact one_smul _ _

/-- The finite unit comparison sends `1` to the scalar unit section of `1`, as a
section of the scalar extension.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
theorem coefficientFiniteUnitComparison_apply_one_unitSection
    (D : CoefficientDerivedSystemScalarCoherence l E W) (n : ℕ) (V : (Scheme.ProEt W)ᵒᵖ) :
    ((coefficientFiniteUnitComparison l E W D n).f 0).val.app V
        (coefficientUnitComplexSection.{u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) V 1) =
      coefficientIntegralScalarUnitSection l E W n ((coefficientIntegralUnitComplex l E W).X 0) V
        (coefficientUnitComplexSection.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) V 1) :=
  coefficientFiniteUnitComparison_apply_one l E W D n V

/-- Ordinary scalar extension maps scalar unit sections to scalar unit sections.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
theorem scalarReductionExtension_map_unitSection (n : ℕ) {M M' : scalarReductionSource l E W}
    (g : M ⟶ M') (U : (Scheme.ProEt W)ᵒᵖ) (x : M.val.obj U) :
    ((scalarReductionExtension l E W n).map g).val.app U
        (coefficientIntegralScalarUnitSection l E W n M U x) =
      coefficientIntegralScalarUnitSection l E W n M' U (g.val.app U x) :=
  scalarReductionExtension_map_unit l E W n g U x

/-- Maps out of an ordinary finite scalar extension are determined on scalar unit sections.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
theorem scalarReductionExtension_hom_ext_unitSection (n : ℕ) {M : scalarReductionSource l E W}
    {N : scalarReductionTarget l E W n}
    (f g : (scalarReductionExtension l E W n).obj M ⟶ N)
    (h : ∀ (U : (Scheme.ProEt W)ᵒᵖ) (x : M.val.obj U),
      f.val.app U (coefficientIntegralScalarUnitSection l E W n M U x) =
        g.val.app U (coefficientIntegralScalarUnitSection l E W n M U x)) :
    f = g :=
  scalarReductionExtension_hom_ext l E W n f g h

/-- The finite tensor comparison carries the scalar extension of the inverse left unitor
to the inverse left unitor at the finite level, along the transported scalar unit.
Source: Stacks 03EK, 07A4 (auxiliary; not a blueprint node).
Proof: both chain maps are determined by their values on scalar unit sections, which
both send `x` to the generator of the scalar unit sections of `1` and `x`. -/
theorem coefficientUnitLeftUnitor_inv_scalarExtension
    (D : CoefficientDerivedSystemScalarCoherence l E W) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
      (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom (coefficientFiniteUnitComparison l E W D n) (𝟙 _)) =
    ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).map
        (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P).inv ≫
      (coefficientScalarTensorIso l E W n (coefficientIntegralUnitComplex l E W) P).hom := by
  ext q : 1
  apply scalarReductionExtension_hom_ext_unitSection l E W n
  intro V x
  have hsti := (coefficientScalarTensorIso_exists l E W n (coefficientIntegralUnitComplex l E W)
    P).choose_spec.1 0 q q (zero_add q) V
      (coefficientUnitComplexSection.{u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) V 1) x
  have s1 : ((coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)).inv.f q).val.app
          V (coefficientIntegralScalarUnitSection l E W n (P.X q) V x) =
      coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (coefficientUnitComplex.{u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n))
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) 0 q q
        (zero_add q) V (coefficientUnitComplexSection.{u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) V 1)
        (coefficientIntegralScalarUnitSection l E W n (P.X q) V x) :=
    coefficientUnitLeftUnitor_inv_apply.{u} _ _ _ q V _
  have key : (((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom (coefficientFiniteUnitComparison l E W D n) (𝟙 _))).f q).val.app V
      (((coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)).inv.f q).val.app
          V (coefficientIntegralScalarUnitSection l E W n (P.X q) V x)) =
    ((coefficientScalarTensorIso l E W n (coefficientIntegralUnitComplex l E W)
      P).hom.f q).val.app V
      (((scalarReductionExtension l E W n).map ((coefficientUnitLeftUnitor.{u}
        (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)
          P).inv.f q)).val.app V (coefficientIntegralScalarUnitSection l E W n (P.X q) V x)) := by
    rw [s1, coefficientTotalTensor_map_tensorGenerator]
    erw [coefficientFiniteUnitComparison_apply_one_unitSection]
    rw [scalarReductionExtension_map_unitSection, coefficientUnitLeftUnitor_inv_apply]
    exact hsti.symm
  exact key

/-- The finite tensor comparison carries the scalar extension of the derived inverse left
unitor on a K-flat complex to the finite derived inverse left unitor, along the
transported scalar unit and the finite reduction models.
Source: Stacks 07A4, 06YY (auxiliary; not a blueprint node).
Proof: after the finite reduction models of the two factors, the normalized finite tensor
comparison is the localized ordinary scalar tensor comparison. Naturality of the reduction
models and of the K-flat tensor models reduces the claim to the chain-level identity
`coefficientUnitLeftUnitor_inv_scalarExtension`. -/
theorem coefficientFiniteTensor_unitLeftUnitor
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSystemScalarCoherence l E W) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    (coefficientFiniteReductionModel l E W P hP n).hom ≫
      DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
      (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (R.finiteClosed n) (R.finiteTensorModel n)
        (coefficientFiniteUnitComplex l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
        (coefficientUnitComplex_isKFlat.{u} _ _)
        ((coefficientTensorModelPreservation l E W).1 P hP n)).hom ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map (coefficientFiniteUnitComparison l E W D n) ≫
          (coefficientFiniteReductionModel l E W _ (coefficientUnitComplex_isKFlat.{u} _ _) n).inv)
          (coefficientFiniteReductionModel l E W P hP n).inv) ≫
      (R.finiteTensor n).inv.app
        (DerivedCategory.Q.obj (coefficientIntegralUnitComplex l E W), DerivedCategory.Q.obj P) =
    (coefficientFiniteDerivedExtension l E W n).map
      (DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P).inv ≫
        (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) R.integralClosed
          R.integralTensorModel (coefficientIntegralUnitComplex l E W) P
          (coefficientUnitComplex_isKFlat.{u} _ _) hP).hom) := by
  have hUA := coefficientUnitComplex_isKFlat.{u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  have hsq := hF n (coefficientIntegralUnitComplex l E W) P hUA hP
  unfold CoefficientTensorComparisonSquare coefficientIntegralTensorModelIso
    coefficientFiniteTensorModelIso at hsq
  have hnat : (coefficientFiniteDerivedExtension l E W n).map
      (DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P).inv) ≫
      (coefficientFiniteReductionModel l E W
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj
            (coefficientIntegralUnitComplex l E W, P))
        (coefficientTotalTensor_isKFlat.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)
          (coefficientIntegralUnitComplex l E W) P hUA hP) n).hom =
      (coefficientFiniteReductionModel l E W P hP n).hom ≫
        DerivedCategory.Q.map (((scalarReductionExtension l E W n).mapHomologicalComplex
          (.up ℤ)).map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P).inv) :=
    coefficientFiniteReductionModel_naturality l E W hP _ n _
  have hW := coefficientUnitLeftUnitor_inv_scalarExtension l E W D n P
  have hiso := CoefficientTensorModels.iso_naturality.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n) (R.finiteClosed n) (R.finiteTensorModel n)
    (coefficientUnitComplex_isKFlat.{u} _ _)
    ((coefficientTensorModelPreservation l E W).1 _ hUA n)
    ((coefficientTensorModelPreservation l E W).1 P hP n)
    ((coefficientTensorModelPreservation l E W).1 P hP n)
    (coefficientFiniteUnitComparison l E W D n) (𝟙 _)
  have e1 : (R.finiteClosed n).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map (coefficientFiniteUnitComparison l E W D n) ≫
          (coefficientFiniteReductionModel l E W _ hUA n).inv)
          (coefficientFiniteReductionModel l E W P hP n).inv) ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom (coefficientFiniteReductionModel l E W _ hUA n).hom
          (coefficientFiniteReductionModel l E W P hP n).hom) =
      (R.finiteClosed n).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map (coefficientFiniteUnitComparison l E W D n))
          (DerivedCategory.Q.map (𝟙 _))) := by
    rw [← Functor.map_comp]
    congr 1
    ext <;> simp
  have key : (coefficientFiniteReductionModel l E W P hP n).hom ≫
      DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
      (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (R.finiteClosed n) (R.finiteTensorModel n)
        (coefficientFiniteUnitComplex l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
        (coefficientUnitComplex_isKFlat.{u} _ _)
        ((coefficientTensorModelPreservation l E W).1 P hP n)).hom ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map (coefficientFiniteUnitComparison l E W D n) ≫
          (coefficientFiniteReductionModel l E W _ hUA n).inv)
          (coefficientFiniteReductionModel l E W P hP n).inv) ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom (coefficientFiniteReductionModel l E W _ hUA n).hom
          (coefficientFiniteReductionModel l E W P hP n).hom) =
      (coefficientFiniteDerivedExtension l E W n).map
        (DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P).inv ≫
        (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) R.integralClosed
          R.integralTensorModel (coefficientIntegralUnitComplex l E W) P hUA hP).hom) ≫
      (R.finiteTensor n).hom.app
        (DerivedCategory.Q.obj (coefficientIntegralUnitComplex l E W), DerivedCategory.Q.obj P) ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom (coefficientFiniteReductionModel l E W _ hUA n).hom
          (coefficientFiniteReductionModel l E W P hP n).hom) := by
    rw [e1, ← hiso, ← Functor.map_comp_assoc, hW, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, hsq, reassoc_of% hnat]
  have hpi : IsIso (Prod.mkHom (coefficientFiniteReductionModel l E W _ hUA n).hom
      (coefficientFiniteReductionModel l E W P hP n).hom) :=
    ⟨⟨Prod.mkHom (coefficientFiniteReductionModel l E W _ hUA n).inv
      (coefficientFiniteReductionModel l E W P hP n).inv, by ext <;> simp, by ext <;> simp⟩⟩
  have key' : (coefficientFiniteReductionModel l E W P hP n).hom ≫
      DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
      (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (R.finiteClosed n) (R.finiteTensorModel n)
        (coefficientFiniteUnitComplex l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
        (coefficientUnitComplex_isKFlat.{u} _ _)
        ((coefficientTensorModelPreservation l E W).1 P hP n)).hom ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map (coefficientFiniteUnitComparison l E W D n) ≫
          (coefficientFiniteReductionModel l E W _ hUA n).inv)
          (coefficientFiniteReductionModel l E W P hP n).inv) =
      (coefficientFiniteDerivedExtension l E W n).map
        (DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P).inv ≫
        (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) R.integralClosed
          R.integralTensorModel (coefficientIntegralUnitComplex l E W) P hUA hP).hom) ≫
      (R.finiteTensor n).hom.app
        (DerivedCategory.Q.obj (coefficientIntegralUnitComplex l E W),
          DerivedCategory.Q.obj P) := by
    rw [← cancel_mono ((R.finiteClosed n).tensor.map
      (Prod.mkHom (coefficientFiniteReductionModel l E W _ hUA n).hom
        (coefficientFiniteReductionModel l E W P hP n).hom))]
    simpa only [Category.assoc] using key
  have hfin := congrArg (· ≫ (R.finiteTensor n).inv.app
    (DerivedCategory.Q.obj (coefficientIntegralUnitComplex l E W), DerivedCategory.Q.obj P)) key'
  simp only [Category.assoc, Iso.hom_inv_id_app] at hfin
  exact hfin.trans (Category.comp_id _)

end WeilConjectures
