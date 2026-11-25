/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import WeilConjectures.SixFunctors.Coefficient.CoefficientPrescribedPairTensorModels
import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarLineData
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorReductionTowerComparison
import WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility

/-! # Normalized derived comparisons for integral lines

(blueprint: lem-pur-integral-line-normalized-derived-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.IntegralOnSlice.abSheafify

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private local instance (priority := 10000) allRingDerived :
    ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 2} (SheafOfModules.scalarModules (ProEt.topology X) R) :=
  fun _ ↦ HasDerivedCategory.standard _

private local instance siteSmall : EssentiallySmall.{u + 1} X.ProEt :=
  scalarReductionSiteSmall.{u, u} X

attribute [-instance] WeilConjectures.integralOperationsFiniteMonoidal
attribute [local instance 30000] SheafOfModules.monoidalCategory

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  HasDerivedCategory.standard coefficientTotalTensor CoefficientClosedStructure.tensor
  CoefficientTensorModels.iso completedIntegralCoefficientSheafUnrestricted constantSheaf

-- Instantiate the prescribed two-variable tensor model with the actual scalar pair.
private theorem scalarTensorData (n : ℕ) :
    Nonempty (CategoryTheory.ScalarHomTensor.PairTensorComparison.{u + 1, u, u, u + 2}
      (J := ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
      (S := integralCoefficientCommRingSheaf.{u, u} l E X n)
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n)
      (coefficientActualScalarDerivedPair.{u, u} l E X n)
      (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (duality.{u, u} l E X none))
      (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (finiteModel l E X n))
      (RingedSiteDualityModel.models.{u + 1, u, u, u + 2} (duality.{u, u} l E X none))
      (RingedSiteDualityModel.models.{u + 1, u, u, u + 2} (finiteModel l E X n))) := by
  let := scalarReductionSiteSmall.{u, u} X
  let (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
      HasDerivedCategory.{u + 2} (SheafOfModules.scalarModules (ProEt.topology X) R) :=
    HasDerivedCategory.standard _
  exact coefficientPrescribedPairTensorComparison.{u + 1, u, u, u + 2}
    (J := ProEt.topology X)
    (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n)
    (coefficientActualScalarDerivedPair.{u, u} l E X n)
    (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (duality.{u, u} l E X none))
      (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (finiteModel l E X n))
    (RingedSiteDualityModel.models.{u + 1, u, u, u + 2} (duality.{u, u} l E X none))
      (RingedSiteDualityModel.models.{u + 1, u, u, u + 2} (finiteModel l E X n))

private theorem powerRank (L : scalarReductionSource.{u, u} l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (power l E X L m).IsFiniteLocallyFreeOfRank 1 := by
  let := scalarReductionSiteSmall.{u, u} X
  exact SheafOfModules.OrdinaryLineScalar.signed_power_rank.{u, u} L m

private theorem lineFlat (L : scalarReductionSource.{u, u} l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
      ((integralLineSingle.{u, u} l E X).obj (power l E X L m)) := by
  let := scalarReductionSiteSmall.{u, u} X
  let := powerRank l E X L m
  exact (SheafOfModules.LineUnbounded.line_unbounded_derived_tensor.{u, u} X
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (power l E X L m)).2.2.choose

private noncomputable def lineComplexIso
    (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L)
    (m : ℤ) (n : ℕ) :
    (reduceComplex l E X n).obj ((integralLineSingle.{u, u} l E X).obj (power l E X L m)) ≅
      (HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (scalarReductionExtension l E X n) (.up ℤ) 0).app (power l E X L m) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso (b m n)

private noncomputable def chainIso
    (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L)
    (m : ℤ) (n : ℕ) (P : Cx.{u, u} l E X none) :
    (reduceComplex l E X n).obj (integralLineComplex l E X P (power l E X L m)) ≅
      finiteTensorComplex l E X P L n m :=
  ((scalarTensorData l E X n).some.complexIso P
      ((integralLineSingle.{u, u} l E X).obj (power l E X L m))) ≪≫
    (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)).mapIso
        (Iso.prod (Iso.refl _) (lineComplexIso l E X L b m n))

private theorem pairUnit_eq (n : ℕ) (M : scalarReductionSource.{u, u} l E X)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    CategoryTheory.ScalarHomTensor.pairUnit.{u + 1, u, u, u + 2}
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n)
      (coefficientActualScalarDerivedPair.{u, u} l E X n) M U x =
        sfReductionTensor l E X n M U 1 x := by
  exact CategoryTheory.ScalarHomTensor.pairUnit_eq_tensorSection.{u + 1, u, u, u + 2}
    (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n)
    (coefficientActualScalarDerivedPair.{u, u} l E X n) M U x

-- Elaborate sheafification transports on the coefficient tensor sections.
private theorem scalar_generator_smul (n : ℕ)
    (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
    (c : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
    (x : M.val.obj U) :
    sfReductionTensor l E X n M U c x = c • sfReductionTensor l E X n M U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (completedIntegralCommRingProjectionUnrestricted l E X n) M)
  let g := (eqToHom ((scalarReductionExistence l E X n).choose_spec.choose M).symm).val.app U
  change g (η.app U (c ⊗ₜ[_, _] x)) = c • g (η.app U ((1 :
    (integralCoefficientCommRingSheaf l E X n).obj.obj U) ⊗ₜ[_, _] x))
  have ht := (ModuleCat.ExtendScalars.smul_tmul
    (f := ((completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U).hom)
    c 1 x).symm
  simp only [mul_one] at ht
  exact (congrArg (fun z ↦ g (η.app U z)) ht).trans
    ((congrArg g ((η.app U).hom.map_smul c _)).trans (g.hom.map_smul c _))

private theorem lineComplexIso_f (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (m : ℤ) (n : ℕ) :
    ((lineComplexIso l E X L b m n).hom.f 0) = (b m n).hom := by
  simp only [lineComplexIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Iso.app_hom, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Functor.mapIso_hom,
    HomologicalComplex.single_map_f_self]
  dsimp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact Category.id_comp _

-- Normalize both tensor generators through the specified chain isomorphisms.
private theorem chain_formula (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (m : ℤ) (n : ℕ) (P : Cx.{u, u} l E X none) :
    ChainFormula l E X P L b n m (chainIso l E X L b m n P) := by
  intro i U c x y
  have hg := (scalarTensorData l E X n).some.generators P
    ((integralLineSingle.{u, u} l E X).obj (power l E X L m)) i 0 i (add_zero i) U x y
  simp only [pairUnit_eq] at hg
  dsimp only [chainIso, Iso.trans_hom, HomologicalComplex.comp_f]
  change (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)).map
        (Prod.mkHom (𝟙 _) (lineComplexIso l E X L b m n).hom)).f i).val.app U
    (((scalarTensorData l E X n).some.complexIso P
      ((integralLineSingle.{u, u} l E X).obj (power l E X L m))).hom.f i |>.val.app U
        (sfReductionTensor l E X n _ U c
          (coefficientTensorGenerator.{u, u + 1, u} _ _ P
            ((integralLineSingle.{u, u} l E X).obj (power l E X L m))
            i 0 i (add_zero i) U x y))) = _
  rw [scalar_generator_smul, map_smul]
  erw [hg]
  rw [map_smul]
  erw [CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply, lineComplexIso_f]
  erw [scalar_generator_smul l E X n (P.X i) U c x]
  delta coefficientTotalTensor coefficientTensorGenerator
  simp only [← TensorProduct.smul_tmul', map_smul]
  rfl

private theorem reduceCounit_eq (n : ℕ) (P : Cx.{u, u} l E X none) :
    (reduceCounit l E X n).app P =
      SheafOfModules.scalarPairComplexComparison
        (coefficientActualScalarDerivedPair.{u, u} l E X n).extension
        (coefficientActualScalarDerivedPair.{u, u} l E X n).extension_additive
        (coefficientActualScalarDerivedPair.{u, u} l E X n).derived
        (coefficientActualScalarDerivedPair.{u, u} l E X n).counit P := by
  dsimp only [reduceCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp]
  change _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ = _
  rw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl

private noncomputable def derivedLineIso
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (b : PowerComparisons l E X L) (m : ℤ) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E X n).obj
        (DerivedCategory.Q.obj ((integralLineSingle l E X).obj (power l E X L m))) ≅
      (DerivedCategory.singleFunctor _ 0).obj (finitePower l E X L n m) := by
  have h : IsIso ((reduceCounit l E X n).app
      ((integralLineSingle l E X).obj (power l E X L m))) := by
    rw [reduceCounit_eq]
    exact (coefficientActualScalarDerivedPair.{u, u} l E X n).computes _
      (lineFlat l E X L m)
  exact asIso ((reduceCounit l E X n).app _) ≪≫
    DerivedCategory.Q.mapIso (lineComplexIso l E X L b m n)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private noncomputable def derivedIso
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (b : PowerComparisons l E X L) (m : ℤ) (n : ℕ) :
    ordinary l E X L m ⋙ scalarReductionDerivedExtension.{u, u} l E X n ≅
      scalarReductionDerivedExtension.{u, u} l E X n ⋙ finiteOrdinary l E X L n m :=
  NatIso.ofComponents (fun K ↦
    ((scalarTensorData l E X n).some.iso.app
      (K, DerivedCategory.Q.obj ((integralLineSingle l E X).obj (power l E X L m)))) ≪≫
    (finiteModel l E X n).closed.tensor.mapIso
      (Iso.prod (Iso.refl _) (derivedLineIso l E X L b m n))) (by
        intro K K' f
        have h := (scalarTensorData l E X n).some.iso.hom.naturality
          (Prod.mkHom f (𝟙 (DerivedCategory.Q.obj
            ((integralLineSingle l E X).obj (power l E X L m)))))
        dsimp only [Functor.comp_map, Functor.prod_map] at h
        simp only [CategoryTheory.Functor.map_id] at h
        simp only [ordinary, integralLineOrdinary, finiteOrdinary, Functor.comp_map,
          Functor.prod_map, Prod.sectL_map, Functor.id_map,
          Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
        erw [(integralLineSingle l E X).map_id, DerivedCategory.Q.map_id]
        change (scalarReductionDerivedExtension l E X n).map
            ((duality l E X none).closed.tensor.map
              (Prod.mkHom f (𝟙 _))) ≫
            (scalarTensorData l E X n).some.iso.hom.app _ ≫
            (finiteModel l E X n).closed.tensor.map
              (Prod.mkHom (𝟙 _) (derivedLineIso l E X L b m n).hom) =
          ((scalarTensorData l E X n).some.iso.hom.app _ ≫
            (finiteModel l E X n).closed.tensor.map
              (Prod.mkHom (𝟙 _) (derivedLineIso l E X L b m n).hom)) ≫
            (finiteModel l E X n).closed.tensor.map
              (Prod.mkHom ((scalarReductionDerivedExtension l E X n).map f) (𝟙 _))
        erw [← Category.assoc, h]
        simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
        congr 1
        apply congrArg (finiteModel l E X n).closed.tensor.map
        apply Prod.ext <;> simp
        rfl)

attribute [local semireducible] CoefficientTensorModels.iso

private theorem representative_pasting
    {B D : Type*} [Category B] [Category D] (T : B × B ⥤ D)
    {x x' y₀ y₁ y₂ : D} (r : x ≅ x')
    {p p' q q' q'' : B} (ep : p ≅ p') (eq : q ⟶ q') (e : q' ⟶ q'')
    (ε : x ⟶ y₀) (c : y₀ ⟶ y₁) (d : y₁ ⟶ y₂)
    (s : y₁ ⟶ T.obj (p', q')) (s' : y₂ ⟶ T.obj (p', q''))
    (z : x' ⟶ T.obj (p, q))
    (hn : ε ≫ c ≫ s = r.hom ≫ z ≫ T.map (Prod.mkHom ep.hom eq))
    (hnet : d ≫ s' = s ≫ T.map (Prod.mkHom (𝟙 p') e)) :
    r.inv ≫ ε ≫ (c ≫ d) ≫ (s' ≫ T.map (Prod.mkHom ep.inv (𝟙 q''))) =
      z ≫ T.map (Prod.mkHom (𝟙 p) (eq ≫ e)) := by
  simp only [Category.assoc]
  rw [reassoc_of% hnet, reassoc_of% hn]
  simp only [Iso.inv_hom_id_assoc, ← T.map_comp]
  congr 1
  apply congrArg T.map
  apply Prod.ext
  · change ep.hom ≫ 𝟙 _ ≫ ep.inv = 𝟙 _
    simp only [Category.id_comp, Iso.hom_inv_id]
  · change eq ≫ e ≫ 𝟙 _ = eq ≫ e
    simp only [Category.comp_id]

-- Normalize the specified scalar and tensor model transports in the representative square.
attribute [local irreducible] SheafOfModules.monoidalCategory in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem representative_formula
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (b : PowerComparisons l E X L) (m : ℤ)
    (P : (Good.{u, u} l E X none).FullSubcategory)
    (hL : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X)
      ((integralLineSingle l E X).obj (power l E X L m)))
    (n : ℕ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      ((reduceComplex l E X n).obj P.obj))
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m)))
    (hε : IsIso ((reduceCounit l E X n).app P.obj)) :
    (scalarReductionDerivedExtension l E X n).map
        (integralLineRepresentativeIso l E X P (power l E X L m) hL
          (DerivedCategory.Q.obj P.obj) (Iso.refl _)).inv ≫
      (reduceCounit l E X n).app (integralLineComplex l E X P.obj (power l E X L m)) ≫
      DerivedCategory.Q.map (chainIso l E X L b m n P.obj).hom ≫
      (finiteRepresentativeIso l E X P.obj L n m hP hQ hε).hom =
        (derivedIso l E X L b m n).hom.app (DerivedCategory.Q.obj P.obj) := by
  let t := (scalarTensorData l E X n).some
  let F := scalarReductionDerivedExtension l E X n
  let T := (finiteModel l E X n).closed.tensor
  let Q := (integralLineSingle l E X).obj (power l E X L m)
  let e := lineComplexIso l E X L b m n
  let r := CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (duality l E X none).closed (duality l E X none).models P.obj Q P.property.1 hL
  let rS := CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n) (finiteModel l E X n).closed
    (finiteModel l E X n).models _ _ (t.preservesKFlat P.obj P.property.1)
    (t.preservesKFlat Q hL)
  let rS' := CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n) (finiteModel l E X n).closed
    (finiteModel l E X n).models _ _ hP hQ
  have hnorm := t.normalization P.obj Q P.property.1 hL
  simp only [← reduceCounit_eq] at hnorm
  have hnat : DerivedCategory.Q.map
      ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).map (Prod.mkHom (𝟙 _) e.hom)) ≫
      rS'.hom = rS.hom ≫ T.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map e.hom)) := by
    have hh :=
      (finiteModel l E X n).models.comparison.hom.naturality
        (Prod.mkHom
          (ObjectProperty.homMk (X := ⟨_, t.preservesKFlat P.obj P.property.1⟩)
            (Y := ⟨_, hP⟩) (𝟙 _))
          (ObjectProperty.homMk (X := ⟨_, t.preservesKFlat Q hL⟩)
            (Y := ⟨_, hQ⟩) e.hom))
    dsimp only [Functor.comp_map, Functor.prod_map, coefficientKFlatInclusion,
      ObjectProperty.ι_map, ObjectProperty.homMk_hom] at hh
    exact hh.trans (congrArg
      (fun f ↦ rS.hom ≫ T.map (Prod.mkHom f (DerivedCategory.Q.map e.hom)))
      (DerivedCategory.Q.map_id _))
  have hrep : (integralLineRepresentativeIso l E X P (power l E X L m) hL
      (DerivedCategory.Q.obj P.obj) (Iso.refl _)).inv = r.inv := by
    change (duality l E X none).closed.tensor.map (𝟙 _) ≫ r.inv = r.inv
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hrep]
  change F.map r.inv ≫ (reduceCounit l E X n).app _ ≫
    DerivedCategory.Q.map ((t.complexIso P.obj Q).hom ≫
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).map (Prod.mkHom (𝟙 _) e.hom)) ≫
      (rS'.hom ≫ T.map (Prod.mkHom (asIso ((reduceCounit l E X n).app P.obj)).inv
        (𝟙 _))) = _
  have h := representative_pasting T (F.mapIso r)
    (asIso ((reduceCounit l E X n).app P.obj)) ((reduceCounit l E X n).app Q)
    (DerivedCategory.Q.map e.hom)
    ((reduceCounit l E X n).app (integralLineComplex l E X P.obj (power l E X L m)))
    (DerivedCategory.Q.map (t.complexIso P.obj Q).hom)
    (DerivedCategory.Q.map
      ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).map (Prod.mkHom (𝟙 _) e.hom)))
    rS.hom rS'.hom (t.iso.hom.app _) hnorm.symm hnat
  simp only [derivedIso, derivedLineIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.prod_hom, Iso.refl_hom, asIso_hom,
    DerivedCategory.Q.map_comp, Category.assoc] at h ⊢
  exact h

attribute [local semireducible] coefficientTotalTensor

private theorem totalSection_eq (n : ℕ) (P Q : Cx.{u, u} l E X none)
    (p q : ℤ) (U : X.ProEtᵒᵖ)
    (x : (((reduceComplex l E X n).obj P).X p).val.obj U)
    (y : (((reduceComplex l E X n).obj Q).X q).val.obj U) :
    integralOperationsTotalTensorSection l E X n P Q p q U x y =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        ((reduceComplex l E X n).obj P) ((reduceComplex l E X n).obj Q)
        p q (p + q) rfl U x y := by
  rfl

private theorem tensor_iso_eq (n : ℕ) (P Q : Cx.{u, u} l E X none) :
    (scalarTensorData l E X n).some.complexIso P Q =
      (finiteTensorComparison.{u, u} l E X n).choose.app (P, Q) := by
  symm
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext k
  apply ((coefficientActualScalarDerivedPair.{u, u} l E X n).ordinaryAdjunction.homEquiv
    _ _).injective
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u}
  intro p q hpq U x y
  change (((finiteTensorComparison.{u, u} l E X n).choose.app (P, Q)).hom.f k).val.app U
      (CategoryTheory.ScalarHomTensor.pairUnit.{u + 1, u, u, u + 2}
        (completedIntegralCommRingProjectionUnrestricted l E X n)
        (coefficientActualScalarDerivedPair l E X n) _ U
        (coefficientTensorGenerator.{u, u + 1, u} _ _ P Q p q k hpq U x y)) =
    (((scalarTensorData l E X n).some.complexIso P Q).hom.f k).val.app U
      (CategoryTheory.ScalarHomTensor.pairUnit.{u + 1, u, u, u + 2}
        (completedIntegralCommRingProjectionUnrestricted l E X n)
        (coefficientActualScalarDerivedPair l E X n) _ U
        (coefficientTensorGenerator.{u, u + 1, u} _ _ P Q p q k hpq U x y))
  rw [pairUnit_eq]
  subst k
  have h := (finiteTensorComparison.{u, u} l E X n).choose_spec P Q p q U x y
  rw [totalSection_eq] at h
  refine h.trans ?_
  simpa only [pairUnit_eq, unrestrictedIntegralTensorSection, sfReductionTensor,
    IntegralOnSlice.topology, IntegralOnSlice.ring, IntegralOnSlice.restrict, Functor.id_obj,
    SheafOfModules.scalarComplex, coefficientActualScalarDerivedPair_extension, reduceComplex] using
      ((scalarTensorData l E X n).some.generators P Q p q (p + q) rfl U x y).symm

private theorem transition_eq (n : ℕ) :
    unrestrictedIntegralTransition l E X n =
      NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ) := by
  apply (unrestrictedIntegralTransition_existsUnique l E X n).unique
    (unrestrictedIntegralTransition_existsUnique l E X n).exists.choose_spec
  intro P i U c x
  exact (sfReductionTransition_existsUnique l E X n).exists.choose_spec (P.X i) U c x

private def finiteLineTensorIso
    (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L)
    (m : ℤ) (n : ℕ) (P : Cx.{u, u} l E X none) :=
  (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n)).mapIso
      (Iso.prod (Iso.refl ((reduceComplex l E X n).obj P))
        (lineComplexIso l E X L b m n))

private def finiteTransition
    (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L)
    (m : ℤ) (n : ℕ) (P : Cx.{u, u} l E X none) :
    (restrictComplex l E X (n + 1)).obj (finiteTensorComplex l E X P L (n + 1) m) ⟶
      (restrictComplex l E X n).obj (finiteTensorComplex l E X P L n m) :=
  (restrictComplex l E X (n + 1)).map (finiteLineTensorIso l E X L b m (n + 1) P).inv ≫
    (integralOperationsTensorTransition l E X n).app
      (P, (integralLineSingle l E X).obj (power l E X L m)) ≫
    (restrictComplex l E X n).map (finiteLineTensorIso l E X L b m n P).hom

private theorem lineComplexIso_inv_f (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (m : ℤ) (n : ℕ) :
    (lineComplexIso l E X L b m n).inv.f 0 = (b m n).inv := by
  apply (cancel_mono (b m n).hom).mp
  rw [← lineComplexIso_f l E X L b m n, ← HomologicalComplex.comp_f,
    Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [lineComplexIso_f]
  exact (b m n).inv_hom_id.symm

-- Elaborate the finite-ring transports in the tensor generator formulas.
private theorem transition_formula (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (m : ℤ) (n : ℕ) (P : Cx.{u, u} l E X none) :
    TransitionFormula l E X P L b n m (finiteTransition l E X L b m n P) := by
  intro i U x y
  have ht := (integralOperationsTensorTransition_existsUnique l E X n).exists.choose_spec
    P ((integralLineSingle l E X).obj (power l E X L m)) i 0 U x
      (((lineComplexIso l E X L b m (n + 1)).inv.f 0).val.app U y)
  rw [totalSection_eq, totalSection_eq] at ht
  have htk (k : ℤ) (hk : i + 0 = k) : (((integralOperationsTensorTransition l E X n).app
      (P, (integralLineSingle l E X).obj (power l E X L m))).f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X (n + 1))
          ((reduceComplex l E X (n + 1)).obj P)
          ((reduceComplex l E X (n + 1)).obj
            ((integralLineSingle l E X).obj (power l E X L m))) i 0 k hk U x
          (((lineComplexIso l E X L b m (n + 1)).inv.f 0).val.app U y)) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        ((reduceComplex l E X n).obj P)
        ((reduceComplex l E X n).obj
          ((integralLineSingle l E X).obj (power l E X L m))) i 0 k hk U
        ((((unrestrictedIntegralTransition l E X n).app P).f i).val.app U x)
        ((((unrestrictedIntegralTransition l E X n).app
          ((integralLineSingle l E X).obj (power l E X L m))).f 0).val.app U
            (((lineComplexIso l E X L b m (n + 1)).inv.f 0).val.app U y)) := by
    cases hk
    exact ht
  have ht := htk i (add_zero i)
  change (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)).map
        (Prod.mkHom (𝟙 _) (lineComplexIso l E X L b m n).hom)).f i).val.app U
      ((((integralOperationsTensorTransition l E X n).app
        (P, (integralLineSingle l E X).obj (power l E X L m))).f i).val.app U
        ((((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X (n + 1))).map
            (Prod.mkHom (𝟙 _) (lineComplexIso l E X L b m (n + 1)).inv)).f i).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (integralCoefficientCommRingSheaf l E X (n + 1))
            ((reduceComplex l E X (n + 1)).obj P)
            ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L (n + 1) m))
            i 0 i (add_zero i) U x y))) = _
  have hinv := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X (n + 1))
    (𝟙 ((reduceComplex l E X (n + 1)).obj P))
    (lineComplexIso l E X L b m (n + 1)).inv i 0 i (add_zero i) U x y
  erw [hinv]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  erw [ht]
  erw [CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
    (𝟙 ((reduceComplex l E X n).obj P)) (lineComplexIso l E X L b m n).hom
    i 0 i (add_zero i)]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply, lineComplexIso_f, lineComplexIso_inv_f, transition_eq]
  rfl

private theorem conjugate_square
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ C) (G : B ⥤ C)
    {a₀ a₁ a₂ : A} {b₀ b₁ b₂ : B}
    (a : a₀ ≅ a₁) (e : a₁ ≅ a₂) (b : b₀ ≅ b₁) (d : b₁ ≅ b₂)
    (t : F.obj a₁ ⟶ G.obj b₁) (s : F.obj a₀ ⟶ G.obj b₀)
    (h : s ≫ G.map b.hom = F.map a.hom ≫ t) :
    F.map (a.hom ≫ e.hom) ≫ (F.map e.inv ≫ t ≫ G.map d.hom) =
      s ≫ G.map (b.hom ≫ d.hom) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [Iso.hom_inv_id_map_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ G.map d.hom) h.symm).trans (Category.assoc _ _ _))

private theorem replace_square
    {C : Type*} [Category C] {A B D E : C}
    {s s' : A ⟶ B} {a a' : B ⟶ D} {b b' : A ⟶ E} {t : E ⟶ D}
    (h : s ≫ a = b ≫ t) (hs : s = s') (ha : a = a') (hb : b = b') :
    s' ≫ a' = b' ≫ t := by
  exact (congrArg₂ (fun f g ↦ f ≫ g) hs.symm ha.symm).trans
    (h.trans (congrArg (fun f ↦ f ≫ t) hb))

private theorem whiskered_square_app
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    {L : A ⥤ B} {F₀ : B ⥤ C} {F₁ : B ⥤ D} {G₀ : C ⥤ E} {G₁ : D ⥤ E}
    {T₀ : A ⥤ C} {T₁ : A ⥤ D}
    {b₀ : L ⋙ F₀ ≅ T₀} {b₁ : L ⋙ F₁ ≅ T₁}
    {s : F₁ ⋙ G₁ ⟶ F₀ ⋙ G₀} {t : T₁ ⋙ G₁ ⟶ T₀ ⋙ G₀}
    (h : Functor.whiskerLeft L s ≫ (Functor.isoWhiskerRight b₀ G₀).hom =
      (Functor.isoWhiskerRight b₁ G₁).hom ≫ t) (P : A) :
    s.app (L.obj P) ≫ G₀.map (b₀.hom.app P) =
      G₁.map (b₁.hom.app P) ≫ t.app P := by
  exact NatTrans.congr_app h P

private theorem transition_postcompose (n : ℕ) (P : Cx.{u, u} l E X none)
    {Y : Cx.{u, u} l E X none}
    (f : (restrictComplex l E X n).obj ((reduceComplex l E X n).obj P) ⟶ Y) :
    (unrestrictedIntegralTransition l E X n).app P ≫ f =
      (NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app P ≫ f := by
  exact congrArg (fun t ↦ t ≫ f) (NatTrans.congr_app (transition_eq l E X n) P)

private theorem chosen_tensor_compatibility (n : ℕ) (P Q : Cx.{u, u} l E X none) :
    (unrestrictedIntegralTransition l E X n).app
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q)) ≫
      (restrictComplex l E X n).map
        ((finiteTensorComparison l E X n).choose.app (P, Q)).hom =
    (restrictComplex l E X (n + 1)).map
        ((finiteTensorComparison l E X (n + 1)).choose.app (P, Q)).hom ≫
      (integralOperationsTensorTransition l E X n).app (P, Q) := by
  exact whiskered_square_app (integralTensorTransitionCompatibility l E X
    (fun n ↦ (finiteTensorComparison l E X n).choose)
    (fun n ↦ (finiteTensorComparison l E X n).choose_spec) n) (P, Q)

private theorem scalar_tensor_compatibility (n : ℕ) (P Q : Cx.{u, u} l E X none) :
    (NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q)) ≫
      (restrictComplex l E X n).map ((scalarTensorData l E X n).some.complexIso P Q).hom =
    (restrictComplex l E X (n + 1)).map
        ((scalarTensorData l E X (n + 1)).some.complexIso P Q).hom ≫
      (integralOperationsTensorTransition l E X n).app (P, Q) := by
  have h := replace_square (chosen_tensor_compatibility l E X n P Q) rfl
    (congrArg (fun e ↦ (restrictComplex l E X n).map e.hom)
      (tensor_iso_eq l E X n P Q).symm)
    (congrArg (fun e ↦ (restrictComplex l E X (n + 1)).map e.hom)
      (tensor_iso_eq l E X (n + 1) P Q).symm)
  exact (transition_postcompose l E X n
    ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q))
    ((restrictComplex l E X n).map
      ((scalarTensorData l E X n).some.complexIso P Q).hom)).symm.trans h

-- Identify the strict tower and signed-line presentations before cancelling isomorphisms.
attribute [local irreducible] SheafOfModules.monoidalCategory in
private theorem transition_square (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (m : ℤ) (n : ℕ) (P : Cx.{u, u} l E X none) :
    (restrictComplex l E X (n + 1)).map (chainIso l E X L b m (n + 1) P).hom ≫
        finiteTransition l E X L b m n P =
      (NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app
        (integralLineComplex l E X P (power l E X L m)) ≫
          (restrictComplex l E X n).map (chainIso l E X L b m n P).hom := by
  exact conjugate_square (restrictComplex l E X (n + 1)) (restrictComplex l E X n)
    ((scalarTensorData l E X (n + 1)).some.complexIso P
      ((integralLineSingle l E X).obj (power l E X L m)))
    (finiteLineTensorIso l E X L b m (n + 1) P)
    ((scalarTensorData l E X n).some.complexIso P
      ((integralLineSingle l E X).obj (power l E X L m)))
    (finiteLineTensorIso l E X L b m n P) _ _
    (scalar_tensor_compatibility l E X n P
      ((integralLineSingle l E X).obj (power l E X L m)))

/-- The normalized derived comparison isomorphisms exist and satisfy the representative,
chain, transition, and naturality formulas in `DerivedFormula`.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A4; the signed-line
specialization in the blueprint proof of `lem-pur-integral-line-derived-comparisons`.
Proof: resolve both arguments by K-flat complexes with flat terms. Tensoring with the
single degree-zero signed line is exact and K-flat. The ringed-topos tensor pullback
comparison identifies reduction of the total tensor with the total tensor of the two
reductions. Compose this comparison with the specified ordinary power comparison `b`.
The balancing formula on pure tensors proves `ChainFormula`; conjugating the strict
quotient transition proves `TransitionFormula`. The representative equations and
naturality descend through the K-flat localization, yielding `DerivedFormula`.
(blueprint: lem-pur-integral-line-normalized-derived-comparisons).
-/
theorem integral_line_normalized_derived_comparisons
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (b : PowerComparisons l E X L) (hb : PowerFormula l E X L b) :
    ∃ d : DerivedComparisons l E X L, DerivedFormula l E X L b d := by
  rcases hb with ⟨_, _, _, _⟩
  refine ⟨derivedIso l E X L b, ?_⟩
  intro m P hL
  refine ⟨fun n ↦ chainIso l E X L b m n P.obj,
    fun n ↦ chain_formula l E X L b m n P.obj, ?_, ?_⟩
  · intro n hP hQ hε
    exact representative_formula l E X L b m P hL n hP hQ hε
  · intro n
    exact ⟨finiteTransition l E X L b m n P.obj,
      transition_formula l E X L b m n P.obj, transition_square l E X L b m n P.obj⟩

end WeilConjectures.IntegralLineReduction
