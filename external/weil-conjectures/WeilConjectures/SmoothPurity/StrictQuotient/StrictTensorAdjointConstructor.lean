/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.SmoothPurity.StrictQuotient.StrictTensorOrdinaryAdjunct
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # Constructor laws for ordinary strict quotient adjuncts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian

universe t u c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence coefficientFiniteQuotientModel
  coefficientFiniteQuotientExtension coefficientFiniteQuotientUnitSection
  SheafOfModules.monoidalCategory scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension coefficientFiniteQuotientDerived HasDerivedCategory.standard
  CoefficientClosedStructure.tensor coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology constantSheaf coefficientSequenceEvaluation

private theorem presheaf_map_apply {C : Type c} [Category.{v} C]
    {R : Cᵒᵖ ⥤ RingCat.{r}} (M : PresheafOfModules.{r} R)
    {A B : Cᵒᵖ} (f : A ⟶ B) (x : M.obj A) :
    M.presheaf.map f x = M.map f x := rfl

private theorem generator_presheaf_restrict {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P Q : CochainComplex (CategoryTheory.RingedTensorModules.{c, v, r} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) {A B : Cᵒᵖ} (f : A ⟶ B)
    (x : (P.X p).val.obj A) (y : (Q.X q).val.obj A) :
    (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X k).val.presheaf.map f
      (coefficientTensorGenerator.{r, c, v} J R P Q p q k h A x y) =
    coefficientTensorGenerator.{r, c, v} J R P Q p q k h B
      ((P.X p).val.presheaf.map f x) ((Q.X q).val.presheaf.map f y) := by
  simp only [presheaf_map_apply]
  exact CategoryTheory.ringedSiteTensorGenerator_restrict.{c, v, r} J R P Q p q k h f x y

private theorem tensorTransitions {W : Scheme.{t}} (P Q : Complex l E W) :
    TensorTransitions l E P Q := by
  intro m n hmn p q k hpq U x y
  exact generator_presheaf_restrict.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) P Q p q k hpq
    (Prod.mkHom (homOfLE hmn) (𝟙 U)).op x y

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

private abbrev finiteTensor (W : Scheme.{t}) (n : ℕ) :=
  coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)

private theorem transpose_from_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E : A ⥤ B} {U : B ⥤ A} (am : E ⊣ U)
    (I : A ⥤ C) (J : B ⥤ D) {F : C ⥤ D} {R : D ⥤ C} (ad : F ⊣ R)
    (ρ : J ⋙ R ≅ U ⋙ I) (P : A) (ε : F.obj (I.obj P) ⟶ J.obj (E.obj P))
    (hu : ad.unit.app (I.obj P) ≫ R.map ε ≫ ρ.hom.app (E.obj P) =
      I.map (am.unit.app P)) (H : B) (g : P ⟶ U.obj H) :
    (ad.homEquiv _ _).symm (I.map g ≫ ρ.inv.app H) =
      ε ≫ J.map ((am.homEquiv _ _).symm g) := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, ad.homEquiv_unit, R.map_comp, ← Category.assoc]
  have hu' : ad.unit.app (I.obj P) ≫ R.map ε =
      I.map (am.unit.app P) ≫ ρ.inv.app (E.obj P) := by
    apply (cancel_mono (ρ.hom.app (E.obj P))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact hu.trans (Category.comp_id _).symm
  rw [hu', Category.assoc]
  have hn := ρ.inv.naturality ((am.homEquiv P H).symm g)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← I.map_comp]
  have hg : am.unit.app P ≫ U.map ((am.homEquiv P H).symm g) = g := by
    exact (am.homEquiv_unit P H ((am.homEquiv P H).symm g)).symm.trans
      ((am.homEquiv P H).apply_symm_apply g)
  rw [hg]

private theorem alpha_model {W : Scheme.{t}} (P : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) (level l E P m)) :
    alpha l E P S D hmn =
      (coefficientFiniteQuotientModel l E W hmn (level l E P m) hP).hom ≫
        DerivedCategory.Q.map (ordinaryAlpha l E P S D hmn) := by
  exact transpose_from_unit
    ((D.ordinaryAdjunction hmn).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q (D.adjunction hmn)
    (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors
    (level l E P m)
    (coefficientFiniteQuotientModel l E W hmn (level l E P m) hP).hom
    (D.unit_model hmn (level l E P m) hP) (level l E P n)
    (transition l E P hmn)

private theorem quotient_map_eq_Qmap {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] {P Q : CochainComplex B ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality f
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
  simpa only [Category.comp_id, Category.id_comp] using h

private theorem cochain_comparison_eq {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ T ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ)
    [IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))] :
    ((T.mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
        (DerivedCategory.quotientCompQhIso _).app _).hom) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  change T.map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
  erw [T.map_id]
  simp only [Category.id_comp, Category.comp_id, asIso_hom]

private theorem scalar_model_naturality {W : Scheme.{t}} {m n : ℕ} (hmn : n ≤ m)
    {P Q : CochainComplex (normalizedDVRModules l E W m) ℤ}
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) Q) (f : P ⟶ Q) :
    (coefficientFiniteQuotientDerived l E W hmn).map (DerivedCategory.Q.map f) ≫
        (coefficientFiniteQuotientModel l E W hmn Q hQ).hom =
      (coefficientFiniteQuotientModel l E W hmn P hP).hom ≫
        DerivedCategory.Q.map
          (((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).map f)
        := by
  have hp : (coefficientFiniteQuotientModel l E W hmn P hP).hom =
      (coefficientFiniteQuotientCounit l E W hmn).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    have := coefficientFiniteQuotientCounit_isIso l E W hmn P hP
    unfold coefficientFiniteQuotientModel
    exact cochain_comparison_eq (coefficientFiniteQuotientExtension l E W hmn)
      (coefficientFiniteQuotientDerived l E W hmn) (coefficientFiniteQuotientCounit l E W hmn) P
  have hq : (coefficientFiniteQuotientModel l E W hmn Q hQ).hom =
      (coefficientFiniteQuotientCounit l E W hmn).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) := by
    have := coefficientFiniteQuotientCounit_isIso l E W hmn Q hQ
    unfold coefficientFiniteQuotientModel
    exact cochain_comparison_eq (coefficientFiniteQuotientExtension l E W hmn)
      (coefficientFiniteQuotientDerived l E W hmn) (coefficientFiniteQuotientCounit l E W hmn) Q
  rw [hp, hq]
  have h := (coefficientFiniteQuotientCounit l E W hmn).naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map f)
  change (coefficientFiniteQuotientDerived l E W hmn).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f)) ≫ _ =
    _ ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      (((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).map f)) at h
  simpa only [quotient_map_eq_Qmap] using h

private theorem tensor_model_naturality {W : Scheme.{t}}
    (S : CoefficientDerivedSystemTensors l E W) (n : ℕ)
    (P P' Q Q' : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P')
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q)
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q') (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((finiteTensor l E W n).map (Prod.mkHom f g)) ≫
        ((S.finiteTensorModel n).iso _ _ _ P' Q' hP' hQ').hom =
      ((S.finiteTensorModel n).iso _ _ _ P Q hP hQ).hom ≫
        (S.finiteClosed n).tensor.map (Prod.mkHom (DerivedCategory.Q.map f)
          (DerivedCategory.Q.map g)) := by
  let ρ : ObjectProperty (CochainComplex (normalizedDVRModules l E W n) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
  let f' : (⟨P, hP⟩ : ρ.FullSubcategory) ⟶ ⟨P', hP'⟩ := ObjectProperty.homMk f
  let g' : (⟨Q, hQ⟩ : ρ.FullSubcategory) ⟶ ⟨Q', hQ'⟩ := ObjectProperty.homMk g
  exact (S.finiteTensorModel n).comparison.hom.naturality (Prod.mkHom f' g')

private theorem level_total_kflat {W : Scheme.{t}} (P Q : Complex l E W) (n : ℕ)
    (hP : Good l E P n) (hQ : Good l E Q n) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) (level l E (total l E P Q) n) := by
  let R := integralCoefficientCommRingSheaf l E W n
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have h := coefficientTotalTensor_isKFlat.{u, t + 1, t} (Scheme.ProEt.topology W) R
    (level l E P n) (level l E Q n) hP.1 hQ.1
  intro A hA
  let e := ((curriedTensor _).map₂CochainComplex.obj A).mapIso
    (coefficientEvaluationTensorIso l E W n P Q)
  exact fun k ↦ (h A hA k).of_iso e.symm

private theorem map_pair_comp {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ B) {a b c d e f : A}
    (u : a ⟶ b) (v : b ⟶ c) (x : d ⟶ e) (y : e ⟶ f) :
    T.map (Prod.mkHom (u ≫ v) (x ≫ y)) =
      T.map (Prod.mkHom u x) ≫ T.map (Prod.mkHom v y) :=
  T.map_comp (Prod.mkHom u x) (Prod.mkHom v y)

private theorem paste_tensor_comparisons {C : Type*} [Category C]
    {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ D₀ D₁ : C}
    (ev : A₀ ⟶ A₁) (tm : A₁ ⟶ A₂) (scalarTensor : A₂ ⟶ B₀)
    (scalarPair : B₀ ⟶ B₁) (factorPair : B₁ ⟶ B₂)
    (totalScalar : A₁ ⟶ C₀) (ordinaryComp : C₀ ⟶ C₁) (tensorAfter : C₁ ⟶ B₁)
    (tensorFactor : C₁ ⟶ C₂) (tensorEnd : C₂ ⟶ B₂)
    (scalarBefore : A₀ ⟶ D₀) (evalScalar : D₀ ⟶ C₀)
    (ordinaryAdj : D₀ ⟶ D₁) (evalEnd : D₁ ⟶ C₂)
    (hd : tm ≫ scalarTensor ≫ scalarPair = totalScalar ≫ ordinaryComp ≫ tensorAfter)
    (hn : tensorFactor ≫ tensorEnd = tensorAfter ≫ factorPair)
    (hs : ev ≫ totalScalar = scalarBefore ≫ evalScalar)
    (ho : evalScalar ≫ ordinaryComp ≫ tensorFactor = ordinaryAdj ≫ evalEnd) :
    ev ≫ (tm ≫ scalarTensor ≫ scalarPair) ≫ factorPair =
      (scalarBefore ≫ ordinaryAdj) ≫ evalEnd ≫ tensorEnd := by
  calc
    _ = ev ≫ totalScalar ≫ ordinaryComp ≫ tensorAfter ≫ factorPair := by
      rw [hd]
      simp only [Category.assoc]
    _ = ev ≫ totalScalar ≫ ordinaryComp ≫ tensorFactor ≫ tensorEnd := by rw [hn]
    _ = scalarBefore ≫ evalScalar ≫ ordinaryComp ≫ tensorFactor ≫ tensorEnd := by
      rw [← Category.assoc, hs]
      simp only [Category.assoc]
    _ = (scalarBefore ≫ ordinaryAdj) ≫ evalEnd ≫ tensorEnd := by
      simpa only [Category.assoc] using
        congrArg (fun h ↦ scalarBefore ≫ h ≫ tensorEnd) ho

/-- Tensoring strict systems has its actual tensor transition and respects ordinary
and derived quotient adjuncts on Good representatives.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 07A6, and
lem-pur-quotient-operation-adjoint-factorizations, tensor clauses.
(blueprint: lem-pur-strict-tensor-adjoint-constructor).

Proof: the sheafified pure-tensor inclusion into each total summand is natural in
the site object. Apply naturality to the horizontal arrow (n,U) to (m,U) to get
TensorTransitions. Evaluation identifies the total with the total of the evaluated
complexes. Under these identifications, extension of scalars has the balanced
comparison (u tensor v) tensor b maps to (u tensor b) tensor (v tensor 1),
whose inverse multiplies the two scalars. The adjunct of the tensor transition is
this comparison followed by the tensor of the two factor adjuncts: applying the
ordinary adjunction unit to a pure generator gives the transition on both sides.
The generator formulas extend through sheafification and direct sums and commute
with d(u tensor v) = du tensor v + (-1)^p u tensor dv. Thus invertible factor
adjuncts give an invertible tensor adjunct. Localize that same equality. The
unit_model clauses identify the three localized adjuncts; tensor_model identifies
the localized balanced comparison with D.tensor. Naturality of the finite K-flat
tensor model moves the two factor maps through its comparison. This gives exactly
TensorAdjointEquation with the specified tensorComparison at m and n. Zero inputs,
equal levels, odd degrees and unbounded direct-sum totals obey the same formulas;
no boundedness or flatness of the quotient map is used. -/
theorem strictTensorAdjointConstructor {W : Scheme.{t}} (U V : Complex l E W) :
    TensorTransitions l E U V ∧
    ∀ (S : CoefficientDerivedSystemTensors l E W)
      (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
      (hUm : Good l E U m) (hVm : Good l E V m)
      (hUn : Good l E U n) (hVn : Good l E V n),
      (IsIso (ordinaryAlpha l E U S D hmn) →
        IsIso (ordinaryAlpha l E V S D hmn) →
        IsIso (ordinaryAlpha l E (total l E U V) S D hmn)) ∧
      TensorAdjointEquation l E U V S D hmn hUm hVm hUn hVn := by
  refine ⟨tensorTransitions l E U V, ?_⟩
  intro S D m n hmn hUm hVm hUn hVn
  let F := (coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)
  let T := coefficientFiniteQuotientDerived l E W hmn
  let B := (S.finiteClosed n).tensor
  let em := coefficientEvaluationTensorIso l E W m U V
  let en := coefficientEvaluationTensorIso l E W n U V
  let f := ordinaryAlpha l E U S D hmn
  let g := ordinaryAlpha l E V S D hmn
  let z := ordinaryAlpha l E (total l E U V) S D hmn
  have hTot := level_total_kflat l E U V m hUm hVm
  have htm := coefficientTotalTensor_isKFlat.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W m) (level l E U m) (level l E V m) hUm.1 hVm.1
  obtain ⟨e, he, hd⟩ := D.tensor_model hmn (level l E U m) (level l E V m) hUm.1 hVm.1
  have ho := strictTensorOrdinaryAdjunct l E U V S D hmn e he
  constructor
  · intro hf hg
    have := hf
    have := hg
    have hi : IsIso (Prod.mkHom f g) := ((asIso f).prod (asIso g)).isIso_hom
    have hz : z = F.map em.hom ≫ e.hom ≫
        (finiteTensor l E W n).map (Prod.mkHom f g) ≫ en.inv := by
      apply (cancel_mono en.hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ho.symm
    change IsIso z
    rw [hz]
    infer_instance
  · let km := (S.finiteTensorModel m).iso _ _ _
      (level l E U m) (level l E V m) hUm.1 hVm.1
    let kn := (S.finiteTensorModel n).iso _ _ _
      (level l E U n) (level l E V n) hUn.1 hVn.1
    let ke := (S.finiteTensorModel n).iso _ _ _
      (F.obj (level l E U m)) (F.obj (level l E V m))
      (D.preservesKFlat hmn _ hUm.1) (D.preservesKFlat hmn _ hVm.1)
    let su := (coefficientFiniteQuotientModel l E W hmn (level l E U m) hUm.1).hom
    let sv := (coefficientFiniteQuotientModel l E W hmn (level l E V m) hVm.1).hom
    let st := (coefficientFiniteQuotientModel l E W hmn _ htm).hom
    let so := (coefficientFiniteQuotientModel l E W hmn _ hTot).hom
    let qf := DerivedCategory.Q.map f
    let qg := DerivedCategory.Q.map g
    let qt := DerivedCategory.Q.map ((finiteTensor l E W n).map (Prod.mkHom f g))
    have hn : qt ≫ kn.hom = ke.hom ≫ B.map (Prod.mkHom qf qg) :=
      tensor_model_naturality l E S n _ _ _ _
        (D.preservesKFlat hmn _ hUm.1) hUn.1
        (D.preservesKFlat hmn _ hVm.1) hVn.1 f g
    have hs : T.map (DerivedCategory.Q.map em.hom) ≫ st =
        so ≫ DerivedCategory.Q.map (F.map em.hom) :=
      scalar_model_naturality l E hmn hTot htm em.hom
    change T.map ((DerivedCategory.Q.map em.hom) ≫ km.hom) ≫
        (D.tensor hmn).hom.app _ ≫
        B.map (Prod.mkHom (alpha l E U S D hmn) (alpha l E V S D hmn)) =
      alpha l E (total l E U V) S D hmn ≫ DerivedCategory.Q.map en.hom ≫ kn.hom
    rw [alpha_model l E U S D hmn hUm.1, alpha_model l E V S D hmn hVm.1,
      alpha_model l E (total l E U V) S D hmn hTot]
    change T.map ((DerivedCategory.Q.map em.hom) ≫ km.hom) ≫
        (D.tensor hmn).hom.app _ ≫ B.map (Prod.mkHom (su ≫ qf) (sv ≫ qg)) =
      (so ≫ DerivedCategory.Q.map z) ≫ DerivedCategory.Q.map en.hom ≫ kn.hom
    rw [map_pair_comp, T.map_comp]
    have hq := congrArg (fun f ↦ DerivedCategory.Q.map f) ho
    simp only [Functor.map_comp] at hq
    simpa only [Category.assoc, qt] using
      paste_tensor_comparisons (T.map (DerivedCategory.Q.map em.hom)) (T.map km.hom)
        ((D.tensor hmn).hom.app _) (B.map (Prod.mkHom su sv))
        (B.map (Prod.mkHom qf qg)) st (DerivedCategory.Q.map e.hom) ke.hom qt kn.hom
        so (DerivedCategory.Q.map (F.map em.hom))
        (DerivedCategory.Q.map z) (DerivedCategory.Q.map en.hom) hd hn hs hq

end WeilConjectures.StrictQuotient
