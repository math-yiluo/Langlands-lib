/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralReductionTensorStrength
import Mathlib.CategoryTheory.Monoidal.Functor
import all WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteTensorMonoidal
import all WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Associativity of the normalized reduction tensor strength

Source: Stacks 06YY, 07A4 and 0FPT; integral Hom reduction, paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe d t u
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory

private theorem reduction_iso_inv_section_of_hom_section
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {P Q : CochainComplex (SheafOfModules.{u} R) ℤ} (e : P ≅ Q)
    (k : ℤ) (U : Cᵒᵖ) (x : (P.X k).val.obj U) (y : (Q.X k).val.obj U)
    (h : (e.hom.f k).val.app U x = y) : (e.inv.f k).val.app U y = x := by
  rw [← h]
  exact congrArg (fun f ↦ (f.f k).val.app U x) e.hom_inv_id

-- Establish the diagram identities before specializing to the derived coefficient models.
private theorem reduction_map_inverse_cancel
    {C : Type*} [Category C] {X Y : C} {e : X ≅ Y} {f : Y ≅ X}
    (h : e.symm = f) {D : Type*} [Category D] (F : C ⥤ D) :
    F.map e.hom ≫ F.map f.hom = 𝟙 (F.obj X) := by
  rw [← h, Iso.symm_hom, ← F.map_comp, e.hom_inv_id, F.map_id]

private theorem reduction_normalized_comparison
    {C : Type*} [Category C] {A B D E P Q T : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {r : P ⟶ E} {ri : E ⟶ P}
    {v : P ⟶ Q} {w : Q ⟶ P} {ε : A ⟶ Q} {t : E ⟶ T} {s : P ⟶ T}
    (hs : s = r ≫ t) (h : a ≫ b ≫ c ≫ ri ≫ v = ε)
    (hv : v ≫ w = 𝟙 P) (hr : ri ≫ r = 𝟙 E) :
    (a ≫ b ≫ c) ≫ t = ε ≫ w ≫ s := by
  calc
    (a ≫ b ≫ c) ≫ t = (a ≫ b ≫ c) ≫ ri ≫ s := by
      rw [hs]
      simp only [reassoc_of% hr]
    _ = ε ≫ w ≫ s := by
      have hh := congrArg (fun z ↦ z ≫ w ≫ s) h
      simpa only [Category.assoc, reassoc_of% hv, Category.id_comp] using hh

private theorem reduction_tensorComparison_transport
    {C D : Type*} [Category C] [Category D]
    {T T' : C × C ⥤ C} {S S' : D × D ⥤ D} (F : C ⥤ D)
    (e : T ≅ T') (f : S ≅ S') (mu : T ⋙ F ≅ F.prod F ⋙ S)
    {A X Z : C} {P Q : D} (r : A ⟶ T.obj (X, Z))
    {r' : A ⟶ T'.obj (X, Z)} (hr : r' = r ≫ e.hom.app (X, Z))
    (x : F.obj X ⟶ P) (y : F.obj Z ⟶ Q) :
    F.map r' ≫
        (Functor.isoWhiskerRight e.symm F ≪≫ mu ≪≫
          Functor.isoWhiskerLeft (F.prod F) f).hom.app (X, Z) ≫
        S'.map (Prod.mkHom x y) =
      (F.map r ≫ mu.hom.app (X, Z) ≫ S.map (Prod.mkHom x y)) ≫
        f.hom.app (P, Q) := by
  rw [hr]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.prod_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [← f.hom.naturality]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp]

private theorem nativeScalarTensorStrength_transpose
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    (T : C × C ⥤ C) (S : D × D ⥤ D) {F : C ⥤ D} {U : D ⥤ C}
    (adj : F ⊣ U) (mu : T ⋙ F ≅ F.prod F ⋙ S) (e : T ≅ tensor C) (X Z : C) :
    F.map ((nativeScalarTensorStrength T S adj mu e).app (X, Z)) ≫
        adj.counit.app (F.obj (X ⊗ Z)) =
      F.map (e.inv.app (X, U.obj (F.obj Z))) ≫
        mu.hom.app (X, U.obj (F.obj Z)) ≫
        S.map (Prod.mkHom (𝟙 (F.obj X)) (adj.counit.app (F.obj Z))) ≫
        mu.inv.app (X, Z) ≫ F.map (e.hom.app (X, Z)) := by
  have h : (nativeScalarTensorStrength T S adj mu e).app (X, Z) =
      adj.homEquiv _ _
        (F.map (e.inv.app (X, U.obj (F.obj Z))) ≫
          mu.hom.app (X, U.obj (F.obj Z)) ≫
          S.map (Prod.mkHom (𝟙 (F.obj X)) (adj.counit.app (F.obj Z))) ≫
          mu.inv.app (X, Z) ≫ F.map (e.hom.app (X, Z))) := by
    dsimp only [nativeScalarTensorStrength, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.prod_obj, Functor.id_obj, Functor.comp_obj]
    rw [scalarTensorStrength_app]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
      ← adj.unit_naturality_assoc]
  rw [h]
  exact (adj.homEquiv _ _).symm_apply_apply _

private theorem tensorMate_assoc {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] {F : C ⥤ D} {U : D ⥤ C}
    [F.Monoidal] (adj : F ⊣ U)
    (p : ∀ X Z : C, X ⊗ U.obj (F.obj Z) ⟶ U.obj (F.obj (X ⊗ Z)))
    (hp : ∀ X Z : C, F.map (p X Z) ≫ adj.counit.app (F.obj (X ⊗ Z)) =
      Functor.OplaxMonoidal.δ F X (U.obj (F.obj Z)) ≫
        F.obj X ◁ adj.counit.app (F.obj Z) ≫ Functor.LaxMonoidal.μ F X Z)
    (X V Z : C) :
    (α_ X V (U.obj (F.obj Z))).hom ≫ X ◁ p V Z ≫ p X (V ⊗ Z) =
      p (X ⊗ V) Z ≫ U.map (F.map (α_ X V Z).hom) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [adj.counit_naturality, hp X (V ⊗ Z),
    reassoc_of% hp (X ⊗ V) Z]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, hp]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.associativity_assoc]
  rw [← associator_naturality_right_assoc]
  simp only [Functor.id_obj]
  rw [← Functor.LaxMonoidal.associativity]
  rw [← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Functor.Monoidal.δ_μ,
    id_whiskerRight, Category.id_comp]

private theorem transportedTensorMate_assoc
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (T : C × C ⥤ C) (S : D × D ⥤ D) {F : C ⥤ D} {U : D ⥤ C}
    (adj : F ⊣ U) (mu : T ⋙ F ≅ F.prod F ⋙ S)
    (e : T ≅ tensor C) (f : S ≅ tensor D) (core : F.CoreMonoidal)
    (hm : ∀ X Z, (core.μIso X Z).inv = F.map (e.inv.app (X, Z)) ≫
      mu.hom.app (X, Z) ≫ f.hom.app (F.obj X, F.obj Z)) (X V Z : C) :
    let p := nativeScalarTensorStrength T S adj mu e
    X ◁ p.app (V, Z) ≫ p.app (X, V ⊗ Z) ≫ (F ⋙ U).map (α_ X V Z).inv =
      (α_ X V ((F ⋙ U).obj Z)).inv ≫ p.app (X ⊗ V, Z) := by
  let := core.toMonoidal
  let mun : tensor C ⋙ F ≅ F.prod F ⋙ tensor D :=
    Functor.isoWhiskerRight e.symm F ≪≫ mu ≪≫ Functor.isoWhiskerLeft (F.prod F) f
  have hiso (A B : C) : (core.μIso A B).symm = mun.app (A, B) := Iso.ext (hm A B)
  have hδ (A B : C) : Functor.OplaxMonoidal.δ F A B =
      F.map (e.inv.app (A, B)) ≫ mu.hom.app (A, B) ≫
        f.hom.app (F.obj A, F.obj B) := hm A B
  have hμ (A B : C) : Functor.LaxMonoidal.μ F A B =
      f.inv.app (F.obj A, F.obj B) ≫ mu.inv.app (A, B) ≫ F.map (e.hom.app (A, B)) := by
    change (core.μIso A B).hom = _
    simpa only [mun, Iso.app_inv, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Functor.prod_obj, Category.assoc] using
      congrArg Iso.inv (hiso A B)
  let p := nativeScalarTensorStrength T S adj mu e
  have hp (A B : C) : F.map (p.app (A, B)) ≫ adj.counit.app (F.obj (A ⊗ B)) =
      Functor.OplaxMonoidal.δ F A (U.obj (F.obj B)) ≫
        F.obj A ◁ adj.counit.app (F.obj B) ≫ Functor.LaxMonoidal.μ F A B := by
    rw [nativeScalarTensorStrength_transpose, hδ, hμ]
    have hn := (f.hom.naturality
      (Prod.mkHom (𝟙 (F.obj A)) (adj.counit.app (F.obj B)))).symm
    dsimp only [tensor_map] at hn
    simp only [id_tensorHom] at hn
    simp only [Category.assoc]
    rw [reassoc_of% hn]
    simp only [Iso.hom_inv_id_app_assoc]
  have h := tensorMate_assoc adj (fun A B ↦ p.app (A, B)) hp X V Z
  change X ◁ p.app (V, Z) ≫ p.app (X, V ⊗ Z) ≫ U.map (F.map (α_ X V Z).inv) =
    (α_ X V (U.obj (F.obj Z))).inv ≫ p.app (X ⊗ V, Z)
  apply (cancel_epi (α_ X V (U.obj (F.obj Z))).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% h]
  simp only [← U.map_comp, ← F.map_comp, Iso.hom_inv_id,
    Functor.map_id, Category.comp_id]

end CategoryTheory

namespace WeilConjectures.IntegralHom

attribute [local implicit_reducible] completedIntegralCoefficientSheaf
  completedIntegralCommRingSheafUnrestricted totalTensor coefficientTotalTensor
  completedIntegralCommRingSheaf integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralDerivedReduction scalarReductionSourceDerived scalarReductionTargetDerived
  integralReductionSourceHasDerivedCategory integralReductionTargetHasDerivedCategory
  coefficientFiniteHasDerived coefficientFiniteDerivedExtension derivedCategory
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

-- Comparing the fixed localization models requires many definitional equalities.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem nativeIso_representative
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : TensorPresentation.{t, u} Y R)
    (P Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat Y R P) (hQ : flat Y R Q) :
    a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        (tensorPresentationNativeIso Y R a).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (RingedDerivedNative.comparison.{t + 1, t, u, max u (t + 1) + 1}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let i := coefficientKFlatInclusion.{u, t + 1, t} J R
  let L := i ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).inverseImage i
  let := tensorPresentationKFlatLocalization Y R
  let ff := Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W)
    (Derived.{t, u} Y R)
  have he := congrArg (fun z ↦ z.app (⟨P, hP⟩, ⟨Q, hQ⟩))
    (ff.map_preimage (a.representative.symm ≪≫
      RingedDerivedNative.comparison.{t + 1, t, u, max u (t + 1) + 1} J R).hom)
  change (tensorPresentationNativeIso Y R a).hom.app
    (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) = _ at he
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.hom_inv_id_app_assoc]
  all_goals rfl

private theorem nativeReductionPair_eq_generator
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)}]
    [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)}]
    (P Q : CochainComplex (Modules.{t, u} Y R) ℤ) (i j : ℤ)
    (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    totalPair.{t, u} Y R P Q i j U x y = coefficientTensorGenerator.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j (i + j) rfl U x y := by
  simp only [totalPair, pair, ordinaryTensor, coefficientTensorGenerator,
    CochainComplex.ιMapBifunctor, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

private theorem reductionExtension_eq_scalarExtension (n : ℕ) :
    integralReductionChangeOfRings l E Y D hl n = scalarReductionExtension l E Y n := rfl

-- Comparing the fixed localization models requires many definitional equalities.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem normalizedBeta_eq (n : ℕ)
    (P Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (beta : ((totalTensor.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
      (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)).obj
      (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      ((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj
        (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q))
    [IsIso beta]
    (hbeta : ∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (beta.f (i + j)).val.app U
        (totalPair Y (integralCoefficientCommRingSheaf l E Y n)
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q)
          i j U ((reductionUnit l E Y D hl n (P.X i)).val.app U x)
            ((reductionUnit l E Y D hl n (Q.X j)).val.app U y)) =
      (reductionUnit l E Y D hl n
        ((((totalTensor Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q).X
          (i + j))).val.app U
        (totalPair Y (completedIntegralCommRingSheaf l E Y D hl) P Q i j U x y)) :
    (asIso beta).symm = coefficientScalarTensorIso l E Y n P Q := by
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  dsimp only [reductionExtension_eq_scalarExtension] at beta hbeta ⊢
  dsimp only [coefficientTotalTensor, totalTensor, ordinaryTensor] at beta hbeta ⊢
  apply (coefficientScalarTensorIso_exists l E Y n P Q).unique
  · intro i j k hij U x y
    subst k
    have hh := reduction_iso_inv_section_of_hom_section (asIso beta) (i + j) U _ _
      (hbeta i j U x y)
    simp only [nativeReductionPair_eq_generator] at hh
    dsimp only [coefficientIntegralScalarUnitSection, coefficientRestrictionSection,
      coefficientOrdinaryScalarAdjunction, reductionUnit] at hh ⊢
    dsimp only [coefficientTotalTensor, totalTensor, ordinaryTensor] at hh ⊢
    exact hh
  · unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
    exact (coefficientScalarTensorIso_exists l E Y n P Q).choose_spec.1

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem finiteCochainModel_reductionCounit (n : ℕ)
    (A : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hA : A.IsKFlatIndependentCoefficients) :
    (finiteCochainModel l E Y n).ε.app A = reductionCounit l E Y D hl n A := by
  rw [finiteCochainModel_counit l E Y n A hA]
  unfold coefficientFiniteReductionModel coefficientLocalizedCounitModel reductionCounit
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
  change _ = _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  with_unfolding_all rfl

-- Comparing the fixed localization models requires many definitional equalities.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem nativeReductionMonoidal
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n) :
    let J := AlgebraicGeometry.Scheme.ProEt.topology Y
    let R := completedIntegralCommRingSheafUnrestricted l E Y
    let S := integralCoefficientCommRingSheaf l E Y n
    let : MonoidalCategory (Derived.{t, u} Y R) :=
      RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J R
    let : MonoidalCategory (Derived.{t, u} Y S) :=
      RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J S
    let F : Derived.{t, u} Y R ⥤ Derived.{t, u} Y S := by
      with_unfolding_all exact integralDerivedReduction l E Y D hl n
    let e := tensorPresentationNativeIso Y R a
    let f := tensorPresentationNativeIso Y S m.target
    ∃ core : F.CoreMonoidal, ∀ X Z,
      (core.μIso X Z).inv = F.map (e.inv.app (X, Z)) ≫
        m.mu.hom.app (X, Z) ≫ f.hom.app (F.obj X, F.obj Z) := by
  classical
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let S := integralCoefficientCommRingSheaf l E Y n
  let : MonoidalCategory (Derived.{t, u} Y S) :=
    RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J S
  let : MonoidalCategory (Derived.{t, u} Y R) :=
    RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J R
  obtain ⟨⟨monR, adjR, evR⟩, hmonR, TR, βR, hR, _, hTR⟩ :=
    ringedDerived_closed_symmetric_monoidal_native.{t + 1, t, u, max u (t + 1) + 1} J R
  dsimp only [CoefficientClosedStructure.monoidal] at hmonR
  subst monR
  obtain ⟨⟨monS, adjS, evS⟩, hmonS, TS, βS, hS, _, hTS⟩ :=
    ringedDerived_closed_symmetric_monoidal_native.{t + 1, t, u, max u (t + 1) + 1} J S
  dsimp only [CoefficientClosedStructure.monoidal] at hmonS
  subst monS
  let AR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{t + 1, t, u} J R) :=
    ⟨RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J R, adjR, evR⟩
  let AS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{t + 1, t, u} J S) :=
    ⟨RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J S, adjS, evS⟩
  let D' := finiteCochainModel l E Y n
  let F : Derived.{t, u} Y R ⥤ Derived.{t, u} Y S := by
    with_unfolding_all exact integralDerivedReduction l E Y D hl n
  let e := tensorPresentationNativeIso Y R a
  let f := tensorPresentationNativeIso Y S m.target
  let mu : AR.tensor ⋙ F ≅ F.prod F ⋙ AS.tensor :=
    Functor.isoWhiskerRight e.symm F ≪≫ m.mu ≪≫ Functor.isoWhiskerLeft (F.prod F) f
  let φ := completedIntegralCommRingProjectionUnrestricted l E Y n
  obtain ⟨κ, hκ, _⟩ := ringedFiniteFreeHomBaseChange_complex.{t + 1, t, u,
    max u (t + 1) + 1} J φ D'
  have hc (P Q : CochainComplex (scalarReductionSource l E Y) ℤ) :
      κ.app (P, Q) = coefficientScalarTensorIso l E Y n P Q := by
    apply (coefficientScalarTensorIso_exists l E Y n P Q).unique
    · intro p q k hpq U x y
      subst k
      have h := hκ P Q p q U x y
      dsimp only [D', finiteCochainModel] at h
      dsimp only [J, φ] at h
      simp only [coefficientFiniteScalarSection] at h
      exact h
    · unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
      exact (coefficientScalarTensorIso_exists l E Y n P Q).choose_spec.1
  obtain ⟨core, hcore⟩ := ringedScalarTensorMonoidal.{t + 1, t, u,
    max u (t + 1) + 1} J φ D' AR AS TR TS βR βS hR hS κ mu hκ (by
      intro P Q hP hQ
      obtain ⟨hEP, hEQ, beta, hbeta, hgen, hnorm⟩ := m.normalization P Q hP hQ
      let := hbeta
      have hb := normalizedBeta_eq l E Y D hl n P Q beta hgen
      have hcPQ := hc P Q
      -- Use the same tensor and scalar-extension expressions in both uniqueness equalities.
      dsimp only [reductionExtension_eq_scalarExtension, coefficientTotalTensor,
        totalTensor, ordinaryTensor] at hb
      dsimp only [D', finiteCochainModel, coefficientTotalTensor,
        totalTensor, ordinaryTensor] at hcPQ
      have hbκ := hb.trans hcPQ.symm
      refine ⟨hEP, hEQ, ?_⟩
      have hrepR := nativeIso_representative Y R a P Q hP hQ
      have hrepS := nativeIso_representative Y S m.target _ _ hEP hEQ
      have hTR' := eq_of_heq (hTR P Q hP hQ)
      have hTS' := eq_of_heq (hTS _ _ hEP hEQ)
      change (TR.iso J R AR P Q hP hQ) = _ at hTR'
      change (TS.iso J S AS _ _ hEP hEQ) = _ at hTS'
      change _ = (RingedDerivedNative.tensorIso J R P Q (Or.inl hP)).hom at hrepR
      have hcr := (congrArg Iso.hom hTR').trans hrepR.symm
      have heps (A : CochainComplex (scalarReductionSource l E Y) ℤ)
          (hA : A.IsKFlatIndependentCoefficients) :
          D'.ε.app A = reductionCounit l E Y D hl n A :=
        finiteCochainModel_reductionCounit l E Y D hl n A hA
      have hepsPQ := heps _ (coefficientTotalTensor_isKFlat J R P Q hP hQ)
      simp only [heps P hP, heps Q hQ]
      dsimp only [coefficientTotalTensor, totalTensor, ordinaryTensor,
        CategoryTheory.Functor.uncurry_obj_obj, Modules, J, R] at hepsPQ ⊢
      -- Rewrite just the counit, without testing the other natural-transformation components.
      conv_rhs =>
        arg 1
        rw [hepsPQ]
      let εP := reductionCounit l E Y D hl n P
      let εQ := reductionCounit l E Y D hl n Q
      have hcs := (congrArg Iso.hom hTS').trans hrepS.symm
      have hcan := reduction_map_inverse_cancel hbκ DerivedCategory.Q
      have hr := m.target.representative.inv_hom_id_app (⟨_, hEP⟩, ⟨_, hEQ⟩)
      dsimp only [D', finiteCochainModel, reductionExtension_eq_scalarExtension,
        J, R, S, completedIntegralCommRingSheaf, coefficientTotalTensor, totalTensor,
        ordinaryTensor, CategoryTheory.Functor.uncurry_obj_obj] at hnorm hcan hcs hr
      have hn := by
        with_unfolding_all
          exact reduction_normalized_comparison hcs hnorm hcan hr
      have ht := reduction_tensorComparison_transport F e f m.mu
        (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) hcr εP εQ
      dsimp only [D', finiteCochainModel, coefficientFiniteDerivedExtension,
        F, integralDerivedReduction, reductionExtension_eq_scalarExtension, e, f, mu,
        AS, CoefficientClosedStructure.tensor, εP, εQ,
        J, R, S, completedIntegralCommRingSheaf, totalTensor, coefficientTotalTensor,
        Modules, Derived,
        ordinaryTensor, CategoryTheory.Functor.uncurry_obj_obj,
        CategoryTheory.Functor.prod_obj, Functor.comp_obj, ObjectProperty.ι_obj] at ht hn ⊢
      have hsquare := ht.trans hn
      with_unfolding_all
        exact hsquare)
  refine ⟨core, ?_⟩
  intro X Z
  have hi : core.μIso X Z = (mu.app (X, Z)).symm := Iso.ext (hcore X Z)
  have hi := congrArg Iso.inv hi
  with_unfolding_all
    simpa only [D', finiteCochainModel, coefficientFiniteDerivedExtension,
      F, integralDerivedReduction, e, f, CategoryTheory.Functor.prod_obj,
      Iso.symm_inv, Iso.app_hom, mu, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app] using hi

-- Comparing the fixed localization models requires many definitional equalities.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A native tensor comparison transports the normalized scalar tensor mate to
an associative tensor strength. No invertibility of that mate is asserted here.

Source: Stacks 06YY, 07A4 and 0FPT; integral Hom reduction, paragraphs 1--2.
Proof: choose the unique tensor comparison whose pullback to the product of
K-flat localization functors is a.representative inverse followed by the native
comparison. On three K-flat complexes the normalization field of m identifies
mu with the balanced scalar tensor map. Its associativity is tested on a local
homogeneous generator ((x tensor y) tensor z): both routes insert the same scalar
unit and multiply the two coefficient factors. Sheafification and coproduct
summands detect equality. The native associator square identifies the localized
chain reassociation with the derived associator. Transposing by the normalized
scalar adjunction gives the displayed strength associativity. Resolve the
restricted scalar extension in its occurrence as a tensor input, cancel the
quasi-isomorphisms by K-flatness, and descend the equality through the product
localization. Naturality then extends the equation to arbitrary derived inputs.
All coefficient and site universes remain independent; zero rings and empty
sites satisfy the same generator equations.
(blueprint: lem-sf-reduction-tensor-strength-associativity). -/
theorem reductionTensorStrength_associativity
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    letI : MonoidalCategory (completedIntegralDerivedCategory l E Y D hl) := by
      with_unfolding_all exact RingedDerivedNative.monoidal.{t + 1, t, u,
        max u (t + 1) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y) R
    let e : a.tensor ≅ tensor (completedIntegralDerivedCategory l E Y D hl) := by
      with_unfolding_all exact tensorPresentationNativeIso Y R a
    let B := integralDerivedReduction l E Y D hl n ⋙ scalarReductionDerivedRestriction l E Y n
    let p := nativeScalarTensorStrength
      (C := completedIntegralDerivedCategory l E Y D hl) a.tensor m.target.tensor
      (derivedScalarExtensionRestrictionAdjunction l E Y n).choose m.mu e
    ∀ X V Z : completedIntegralDerivedCategory l E Y D hl,
      X ◁ p.app (V, Z) ≫ p.app (X, V ⊗ Z) ≫ B.map (α_ X V Z).inv =
        (α_ X V (B.obj Z)).inv ≫ p.app (X ⊗ V, Z) := by
  intro R e B p X V Z
  let : MonoidalCategory (completedIntegralDerivedCategory l E Y D hl) :=
    RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R
  let S := integralCoefficientCommRingSheaf l E Y n
  let : MonoidalCategory
      (DerivedCategory (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n))) := by
    with_unfolding_all exact RingedDerivedNative.monoidal.{t + 1, t, u,
      max u (t + 1) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y) S
  let f := tensorPresentationNativeIso Y S m.target
  obtain ⟨core, hcore⟩ := nativeReductionMonoidal l E Y D hl a n m
  exact (CategoryTheory.transportedTensorMate_assoc
    (C := completedIntegralDerivedCategory l E Y D hl)
    (D := DerivedCategory (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)))
    a.tensor m.target.tensor
    (derivedScalarExtensionRestrictionAdjunction l E Y n).choose m.mu e f core hcore X V Z)

end WeilConjectures.IntegralHom
