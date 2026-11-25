/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModel
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Zero cycles of the fixed Hom complex as maps from the unit complex

A degree-zero cycle of the global sections of the fixed representative Hom complex
`Hom(L, I(M))` is the same as a chain map from the coefficient ring placed in degree
zero. This file records this dictionary, the resulting description of the class of a
cycle through the global unit class, and the evaluation of `coefficientHomZeroEquiv` on
the global class of a tensor-Hom transpose.

Source: Stacks Project, Tags 08JA, 0A8X and 08J9.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

/-- The coefficient ring placed in degree zero.
Source: Stacks 0FPT (auxiliary; not a blueprint node). -/
noncomputable abbrev coefficientUnitComplex :
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))

/-- The degree-zero section of the unit complex given by a local coefficient.
Source: Stacks 0FPT (auxiliary; not a blueprint node). -/
noncomputable def coefficientUnitComplexSection (U : Cᵒᵖ) (a : A.obj.obj U) :
    ((coefficientUnitComplex.{u} J A).X 0).val.obj U :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))).inv.val.app U) a

/-- The unit complex is K-flat.
Source: Stacks 06YN (auxiliary; not a blueprint node).
Proof: tensoring with the unit complex is isomorphic to the identity by the right
unitor, which preserves acyclicity. -/
theorem coefficientUnitComplex_isKFlat :
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
      (J := J) (R := A) (coefficientUnitComplex.{u} J A) := by
  intro F hF i
  let := SheafOfModules.cochainModulesMonoidal A
  change (F ⊗ (𝟙_ (CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ))).ExactAt i
  exact (exactAt_iff_of_quasiIsoAt (ρ_ F).hom i).2 (hF i)

/-- The left unitor of the total tensor product with the unit complex.
Source: Stacks 0FPQ (auxiliary; not a blueprint node). -/
noncomputable def coefficientUnitLeftUnitor
    (P : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    (coefficientTotalTensor.{u, c, v} J A).obj (coefficientUnitComplex.{u} J A, P) ≅ P :=
  letI := SheafOfModules.cochainModulesMonoidal A
  λ_ P

/-- The left unitor sends the generator `1 ⊗ x` to `x`.
Source: Stacks 0FPQ (auxiliary; not a blueprint node). -/
theorem coefficientUnitLeftUnitor_generator
    (P : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (x : (P.X n).val.obj U) :
    ((coefficientUnitLeftUnitor.{u} J A P).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J A (coefficientUnitComplex.{u} J A) P 0 n n
        (zero_add n) U (coefficientUnitComplexSection.{u} J A U 1) x) = x :=
  ((RingedDerivedNative.complexConstraints.{c, v, u} J A).leftUnitor P n (zero_add n) U 1
    x).trans (one_smul (((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).obj.obj U) x)

/-- The inverse left unitor sends `x` to the generator `1 ⊗ x`.
Source: Stacks 0FPQ (auxiliary; not a blueprint node). -/
theorem coefficientUnitLeftUnitor_inv_apply
    (P : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (x : (P.X n).val.obj U) :
    ((coefficientUnitLeftUnitor.{u} J A P).inv.f n).val.app U x =
      coefficientTensorGenerator.{u, c, v} J A (coefficientUnitComplex.{u} J A) P 0 n n
        (zero_add n) U (coefficientUnitComplexSection.{u} J A U 1) x := by
  conv_lhs => rw [← coefficientUnitLeftUnitor_generator.{u} J A P n U x]
  have h := congrArg (fun f ↦ (f.f n).val.app U
    (coefficientTensorGenerator.{u, c, v} J A (coefficientUnitComplex.{u} J A) P 0 n n
        (zero_add n) U (coefficientUnitComplexSection.{u} J A U 1) x))
    (coefficientUnitLeftUnitor.{u} J A P).hom_inv_id
  simpa only [HomologicalComplex.comp_f, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply, HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ConcreteCategory.id_apply] using h


/-- The canonical global section of the unit complex, as a degree-zero cycle.
Source: Stacks 08JA (auxiliary; not a blueprint node). -/
noncomputable def coefficientUnitCycle :
    (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (coefficientUnitComplex.{u} J A)).cycles 0 :=
  HomologicalComplex.liftCycles _
    (AddCommGrpCat.ofHom ((zmultiplesHom _
      (show SheafOfModules.unit _ ⟶ (coefficientUnitComplex.{u} J A).X 0 from
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) _).inv)).comp
          (AddEquiv.ulift.{0, max c v u} (α := ℤ)).toAddMonoidHom)) 1 (by simp)
    (by simp) (ULift.up (1 : ℤ))

/-- The unit cycle is the inclusion of the coefficient ring in degree zero.
Source: Stacks 08JA (auxiliary; not a blueprint node). -/
theorem coefficientUnitCycle_iCycles :
    (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (coefficientUnitComplex.{u} J A)).iCycles 0
        (coefficientUnitCycle.{u} J A) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))).inv := by
  rw [coefficientUnitCycle, ← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  exact one_zsmul _

/-- The degree-zero cycle of the fixed Hom complex determined by a map from the unit complex.
Source: Stacks 08JA, 0A8X (auxiliary; not a blueprint node). -/
noncomputable def coefficientHomCycleOfUnitMap
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (σ : coefficientUnitComplex.{u} J A ⟶
      homComplex.{c, v, max c v u, max c v u} (R := A) L
        ((coefficientHomResolution.{u, c, v} J A).obj M)) :
    (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0 :=
  HomologicalComplex.cyclesMap
    (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
      (ComplexShape.up ℤ)).map σ) 0 (coefficientUnitCycle.{u} J A)

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The cycle of a map from the unit complex is its degree-zero component.
Source: Stacks 08JA (auxiliary; not a blueprint node). -/
theorem coefficientHomCycleOfUnitMap_iCycles
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (σ : coefficientUnitComplex.{u} J A ⟶
      homComplex.{c, v, max c v u, max c v u} (R := A) L
        ((coefficientHomResolution.{u, c, v} J A).obj M)) :
    (coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0
        (coefficientHomCycleOfUnitMap.{u, c, v, w} J A L M σ) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))).inv ≫ σ.f 0 := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (ComplexShape.up ℤ)).map
      σ) 0) (coefficientUnitCycle.{u} J A)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, coefficientUnitCycle_iCycles] at h
  exact h

/-- The map from the unit complex determined by a degree-zero cycle.
Source: Stacks 08JA, 0A8X (auxiliary; not a blueprint node). -/
noncomputable def coefficientHomUnitMapOfCycle
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0) :
    coefficientUnitComplex.{u} J A ⟶
      homComplex.{c, v, max c v u, max c v u} (R := A) L
        ((coefficientHomResolution.{u, c, v} J A).obj M) :=
  HomologicalComplex.mkHomFromSingle
    (show SheafOfModules.unit _ ⟶ _ from
      (coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0 z) (by
      intro k _
      have h := ConcreteCategory.congr_hom
        ((coefficientHomSectionComplex.{u, c, v} J A L M).iCycles_d 0 k) z
      exact h)

/-- Every degree-zero cycle comes from its map out of the unit complex.
Source: Stacks 08JA (auxiliary; not a blueprint node). -/
theorem coefficientHomCycleOfUnitMap_unitMapOfCycle
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0) :
    coefficientHomCycleOfUnitMap.{u, c, v, w} J A L M
      (coefficientHomUnitMapOfCycle.{u, c, v} J A L M z) = z := by
  apply (AddCommGrpCat.mono_iff_injective
    ((coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0)).1 inferInstance
  rw [coefficientHomCycleOfUnitMap_iCycles, coefficientHomUnitMapOfCycle,
    HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]

/-- Evaluating the cycle of a map from the unit complex is evaluating the map at `1`.
Source: Stacks 08JA, 0A8X (auxiliary; not a blueprint node). -/
theorem coefficientHomZeroEvaluation_cycleOfUnitMap
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (σ : coefficientUnitComplex.{u} J A ⟶
      homComplex.{c, v, max c v u, max c v u} (R := A) L
        ((coefficientHomResolution.{u, c, v} J A).obj M))
    (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
    coefficientHomZeroEvaluation.{u, c, v} J A L M
        (coefficientHomCycleOfUnitMap.{u, c, v, w} J A L M σ) p U y =
      coefficientHomSectionEvaluation.{u, c, v} J A (coefficientUnitComplex.{u} J A) L M σ
        0 p p (add_zero p) U (coefficientUnitComplexSection.{u} J A U 1) y := by
  unfold coefficientHomZeroEvaluation
  rw [coefficientHomCycleOfUnitMap_iCycles]
  rfl

/-- Naturality of the canonical global-sections comparison on complexes.
Source: Stacks 079P (auxiliary; not a blueprint node). -/
theorem coefficientSiteSectionsComparison_naturality
    {K L : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ}
    (f : K ⟶ L) :
    (@DerivedCategory.Q AddCommGrpCat.{max c v u} _ _ (HasDerivedCategory.standard _)).map
        (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) ≫
      coefficientSiteSectionsComparison.{u, c, v, w} J A L =
    coefficientSiteSectionsComparison.{u, c, v, w} J A K ≫
      (coefficientGlobalSections.{u, c, v, w} J A).map (DerivedCategory.Q.map f) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  let : IsGrothendieckAbelian.{max c v u} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  exact (coefficientOrdinarySections.{u, c, v} J A).rightDerivedFunctorUnitQ_naturality f

/-- The global class of the unit section of the coefficient ring.
Source: Stacks 08JA (auxiliary; not a blueprint node). -/
noncomputable def coefficientUnitClass :
    (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).obj
        ((coefficientGlobalSections.{u, c, v, w} J A).obj
          (DerivedCategory.Q.obj (coefficientUnitComplex.{u} J A))) :=
  (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).map
    (coefficientSiteSectionsComparison.{u, c, v, w} J A (coefficientUnitComplex.{u} J A))
    ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).inv.app _
      (((((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (coefficientUnitComplex.{u} J A)).homologyπ 0)
          (coefficientUnitCycle.{u} J A)))

/-- The class of the cycle of a map from the unit complex is the image of the unit class.
Source: Stacks 08JA, 079P (auxiliary; not a blueprint node).
Proof: naturality of the homology projection, of the homology factorization and of the
global-sections comparison carry the unit cycle along the map. -/
theorem coefficientHomZeroClass_cycleOfUnitMap
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (σ : coefficientUnitComplex.{u} J A ⟶
      homComplex.{c, v, max c v u, max c v u} (R := A) L
        ((coefficientHomResolution.{u, c, v} J A).obj M)) :
    coefficientHomZeroClass.{u, c, v, w} J A L M
        (coefficientHomCycleOfUnitMap.{u, c, v, w} J A L M σ) =
      (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
        (HasDerivedCategory.standard _) 0).map
        ((coefficientGlobalSections.{u, c, v, w} J A).map
          (DerivedCategory.Q.map σ ≫ (coefficientHomResolutionIso.{u, c, v, w} J A L M).inv))
        (coefficientUnitClass.{u, c, v, w} J A) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  let φ := ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
    (ComplexShape.up ℤ)).map σ
  let ΓU := ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (coefficientUnitComplex.{u} J A)
  let ΓK := ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (homComplex.{c, v, max c v u, max c v u} (R := A) L
      ((coefficientHomResolution.{u, c, v} J A).obj M))
  let fac := DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} 0
  have key : fac.inv.app ΓK (ΓK.homologyπ 0
      (HomologicalComplex.cyclesMap φ 0 (coefficientUnitCycle.{u} J A))) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} 0).map
        (DerivedCategory.Q.map φ) (fac.inv.app ΓU (ΓU.homologyπ 0
          (coefficientUnitCycle.{u} J A))) := by
    have h1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ 0)
      (coefficientUnitCycle.{u} J A)
    have h2 := ConcreteCategory.congr_hom (fac.inv.naturality φ)
      (ΓU.homologyπ 0 (coefficientUnitCycle.{u} J A))
    simp only [ConcreteCategory.comp_apply] at h1
    rw [← h1]
    exact h2
  have h3 := coefficientSiteSectionsComparison_naturality.{u, c, v, w} J A σ
  unfold coefficientHomZeroClass coefficientUnitClass coefficientHomCycleOfUnitMap
  erw [key]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rw [reassoc_of% h3]
  simp only [Functor.map_comp]
  rfl

/-- Every derived morphism into a K-injective complex is the localization of a chain map.
Source: Stacks 070Y (auxiliary; not a blueprint node). -/
theorem derivedCategoryQ_map_surjective_of_isKInjective
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (X K : CochainComplex D ℤ) [K.IsKInjective]
    (g : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj K) :
    ∃ s : X ⟶ K, DerivedCategory.Q.map s = g := by
  let σ := DerivedCategory.quotientCompQhIso D
  obtain ⟨h, hh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj X) K).2
      (σ.hom.app X ≫ g ≫ σ.inv.app K)
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map_surjective h
  refine ⟨s, ?_⟩
  have hn := σ.hom.naturality s
  dsimp only [Functor.comp_map] at hn
  rw [hh] at hn
  simpa using hn.symm

/-- The class of a tensor-Hom transpose from the unit is computed by the left unitor.
Source: Stacks 08JA, 08J9 (auxiliary; not a blueprint node).
Proof: the transpose is the localization of a chain map `σ` into the K-injective Hom
complex. Its class is the class of the cycle of `σ`, which the recorded H-zero
equivalence sends to the chain map whose components evaluate `σ` at `1`. The uncurry
normalization identifies this chain map with the left unitor followed by the uncurried
map, which represents `X` on the K-flat tensor model. -/
theorem coefficientHomZeroEquiv_unitClass_transpose
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (P M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
      (J := J) (R := A) P)
    (X : S.tensor.obj (DerivedCategory.Q.obj (coefficientUnitComplex.{u} J A),
      DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj M) :
    coefficientHomZeroEquiv.{u, c, v, w} J A (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M)
        ((@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _) 0).map
          ((coefficientGlobalSections.{u, c, v, w} J A).map
            (S.transpose _ _ _ X)) (coefficientUnitClass.{u, c, v, w} J A)) =
      DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} J A P).inv ≫
        (CoefficientTensorModels.iso.{u, c, v, w} J A S T _ P
          (coefficientUnitComplex_isKFlat.{u} J A) hP).hom ≫ X := by
  let : IsGrothendieckAbelian.{max c v u} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  let : ((coefficientHomResolution.{u, c, v} J A).obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ M
  let : (homComplex.{c, v, max c v u, max c v u} (R := A) P
      ((coefficientHomResolution.{u, c, v} J A).obj M)).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, c, v} P _ hP
  obtain ⟨σ, hσ⟩ := derivedCategoryQ_map_surjective_of_isKInjective _ _
    (S.transpose _ _ _ X ≫ (coefficientHomResolutionIso.{u, c, v, w} J A P M).hom)
  have ht : S.transpose _ _ _ X =
      DerivedCategory.Q.map σ ≫ (coefficientHomResolutionIso.{u, c, v, w} J A P M).inv := by
    rw [hσ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hu := T.uncurry_model
    ⟨coefficientUnitComplex.{u} J A, coefficientUnitComplex_isKFlat.{u} J A⟩ ⟨P, hP⟩ M σ
  let ψ := hu.choose
  have hψ := hu.choose_spec.1
  have hn := hu.choose_spec.2
  have hc := (congrArg (fun g ↦ (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).map
        ((coefficientGlobalSections.{u, c, v, w} J A).map g)
          (coefficientUnitClass.{u, c, v, w} J A))
      ht).trans (coefficientHomZeroClass_cycleOfUnitMap.{u, c, v, w} J A P M σ).symm
  have he : ∀ (p : ℤ) (U : Cᵒᵖ) (y : (P.X p).val.obj U),
      coefficientHomZeroEvaluation.{u, c, v} J A P M
        (coefficientHomCycleOfUnitMap.{u, c, v, w} J A P M σ) p U y =
      (((coefficientUnitLeftUnitor.{u} J A P).inv ≫ ψ).f p).val.app U y := by
    intro p U y
    have h1 := congrArg ((ψ.f p).val.app U) (coefficientUnitLeftUnitor_inv_apply.{u} J A P p U y)
    exact (coefficientHomZeroEvaluation_cycleOfUnitMap.{u, c, v, w} J A P M σ p U y).trans
      ((hψ 0 p p (zero_add p) (add_zero p) U (coefficientUnitComplexSection.{u} J A U 1)
        y).symm.trans h1.symm)
  have hz := (coefficientHomZeroEquiv_exists.{u, c, v, w} J A).choose_spec.1.2 P M hP
    ((coefficientUnitLeftUnitor.{u} J A P).inv ≫ ψ) _ he
  refine (congrArg (coefficientHomZeroEquiv.{u, c, v, w} J A (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj M)) hc).trans (hz.trans ?_)
  have hX : X = (S.transpose _ _ _).symm
      (DerivedCategory.Q.map σ ≫ (coefficientHomResolutionIso.{u, c, v, w} J A P M).inv) := by
    exact ((S.transpose _ _ _).symm_apply_apply X).symm.trans
      (congrArg (S.transpose _ _ _).symm ht)
  have hn' : (CoefficientTensorModels.iso.{u, c, v, w} J A S T _ P
      (coefficientUnitComplex_isKFlat.{u} J A) hP).hom ≫ X =
      DerivedCategory.Q.map ψ ≫ coefficientHomResolutionInverse.{u, c, v, w} J A M := by
    rw [hX]
    exact hn
  have hm : DerivedCategory.Q.map ((coefficientUnitLeftUnitor.{u} J A P).inv ≫ ψ) =
      DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} J A P).inv ≫ DerivedCategory.Q.map ψ :=
    DerivedCategory.Q.map_comp _ _
  exact (congrArg (fun g ↦ g ≫ coefficientHomResolutionInverse.{u, c, v, w} J A M) hm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun g ↦ DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} J A P).inv ≫ g)
        hn'.symm))

end WeilConjectures
