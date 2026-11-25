/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorChainGenerators
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatRepresentatives
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorChainMapFormula
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorRealizationFactors

/-! # Transport of the K-flat tensor square to intrinsic pullback

Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-kflat-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open MonoidalCategory TensorProduct
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex₂.total
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
  pullbackTensorCoefficientFinite
  SheafOfModules.monoidalCategory

attribute [local instance] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived FinitePullbackTensorRep.ordinary_additive
  FinitePullbackTensorRep.ordinary_limits FinitePullbackTensorRep.ordinary_colimits
attribute [local implicit_reducible] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived
attribute [local semireducible] FinitePullbackTensorRep.pull
attribute [local implicit_reducible] FinitePullbackTensorRep.pull
  coefficientFiniteInternalHom
attribute [local irreducible] finiteIntrinsicClosed finiteIntrinsicTensorModels
attribute [local implicit_reducible] finiteIntrinsicDerivedTensor coefficientTotalTensor
  FinitePullbackTensorRep.totalTensor

private theorem tensorSquareTransport {D₀ : Type*} [Category D₀]
    {A B C D D' E E' F F' : D₀}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {c' : C ⟶ D'}
    {d : A ⟶ E} {e : E ⟶ F} {s : F ⟶ D} {t : F ⟶ F'}
    {u : F' ⟶ D'} {v : D ⟶ D'} {w : A ⟶ E'} {r : E' ⟶ E} {k : E' ⟶ F'}
    (h : a ≫ b ≫ c = d ≫ e ≫ s) (hs : t ≫ u = s ≫ v)
    (ht : d = w ≫ r) (hd : c' = c ≫ v) (hk : k = r ≫ e ≫ t) :
    a ≫ b ≫ c' = w ≫ k ≫ u := by
  have hh := congrArg (fun z ↦ z ≫ v) h
  simp only [Category.assoc, ← hs, ht] at hh
  simpa only [hd, hk, Category.assoc] using hh

private theorem finiteTensor_kflat_iso {W : Scheme.{u}} (n : ℕ)
    {P Q : CochainComplex (normalizedDVRModules l E W n) ℤ}
    (e : P ≅ Q) (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q := by
  intro L hL
  exact (hP L hL).of_iso
    ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).mapIso ((Iso.refl L).prod e))

private theorem finiteTensor_model_naturality (W : Scheme.{u}) (n : ℕ)
    (P Q P' Q' : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q') (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom a b)) ≫
      ((finiteIntrinsicTensorModels l E W n).iso (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
        P' Q' hP' hQ').hom =
    ((finiteIntrinsicTensorModels l E W n).iso (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
      P Q hP hQ).hom ≫
      (finiteIntrinsicDerivedTensor l E W n).map
        (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) := by
  exact (finiteIntrinsicTensorModels l E W n).comparison.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨P', hP'⟩) a)
      (ObjectProperty.homMk (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) b))

/-- The ordinary K-flat representative square transported through the prescribed
finite realization. Source: Stacks 06YS and 07A4
(blueprint: lem-pur-finite-pullback-tensor-kflat-transport).
Proof: transfer K-flatness of the intrinsic pullbacks to the ordinary ones using
the degreewise realization isomorphism. Apply the ordinary K-flat square. Naturality
of the finite tensor model moves the two realization maps past the target model.
The derived realization factorization identity expresses the intrinsic factors as
the ordinary factors followed by the localized realization. Postcompose the ordinary
square with that pair of realization maps and reassociate. The remaining chain map
is precisely the conjugate defining finitePullbackTensorChainIso. -/
theorem finitePullbackTensor_intrinsic_kflat_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) Q)
    (hFP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj P))
    (hFQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj Q)) :
    (finiteDerivedPullback l E n f).map
        ((finiteIntrinsicTensorModels l E Y n).iso (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n) (finiteIntrinsicClosed l E Y n)
          P Q hP hQ).hom ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom
          ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
            f).mapDerivedCategoryFactors.hom.app P)
          ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
            f).mapDerivedCategoryFactors.hom.app Q)) =
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
      f).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (finitePullbackTensorChainIso l E f n P Q).hom ≫
      ((finiteIntrinsicTensorModels l E X n).iso (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n) (finiteIntrinsicClosed l E X n)
        _ _ hFP hFQ).hom := by
  let : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let R := integralCoefficientCommRingSheaf l E Y n
  let S := integralCoefficientCommRingSheaf l E X n
  let F := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let e := NatIso.mapHomologicalComplex (pullbackTensorFiniteRealization l E f n) (.up ℤ)
  let LP := (FinitePullbackTensorRep.pull l E f n).obj P
  let LQ := (FinitePullbackTensorRep.pull l E f n).obj Q
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let TY := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y) R
  let TX := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) S
  let DX := finiteIntrinsicDerivedTensor l E X n
  let hLP := finiteTensor_kflat_iso l E n (e.app P).symm hFP
  let hLQ := finiteTensor_kflat_iso l E n (e.app Q).symm hFQ
  let sO := (finiteIntrinsicTensorModels l E X n).iso (ProEt.topology X) S
    (finiteIntrinsicClosed l E X n) LP LQ hLP hLQ
  let sF := (finiteIntrinsicTensorModels l E X n).iso (ProEt.topology X) S
    (finiteIntrinsicClosed l E X n) FP FQ hFP hFQ
  let d := TX.map (Prod.mkHom (e.hom.app P) (e.hom.app Q))
  let de := DX.map (Prod.mkHom (DerivedCategory.Q.map (e.hom.app P))
    (DerivedCategory.Q.map (e.hom.app Q)))
  have hk : (finitePullbackTensorChainIso l E f n P Q).hom =
      e.inv.app (TY.obj (P, Q)) ≫ FinitePullbackTensorRep.comparison l E f n P Q ≫ d := by
    exact finitePullbackTensorChainIso_hom l E f n P Q
  have hs : DerivedCategory.Q.map d ≫ sF.hom = sO.hom ≫ de := by
    exact finiteTensor_model_naturality l E X n LP LQ FP FQ hLP hLQ hFP hFQ
      (e.hom.app P) (e.hom.app Q)
  have ht : (FinitePullbackTensorRep.factors l E f n).hom.app (TY.obj (P, Q)) =
      F.mapDerivedCategoryFactors.hom.app (TY.obj (P, Q)) ≫
        DerivedCategory.Q.map (e.inv.app (TY.obj (P, Q))) := by
    apply (cancel_mono (DerivedCategory.Q.map (e.hom.app (TY.obj (P, Q))))).1
    rw [finitePullbackTensor_realization_factors]
    rw [Category.assoc]
    erw [← DerivedCategory.Q.map_comp, e.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hd : DX.map (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
      (F.mapDerivedCategoryFactors.hom.app Q)) =
      DX.map (Prod.mkHom ((FinitePullbackTensorRep.factors l E f n).hom.app P)
        ((FinitePullbackTensorRep.factors l E f n).hom.app Q)) ≫ de := by
    rw [← finitePullbackTensor_realization_factors l E f n P,
      ← finitePullbackTensor_realization_factors l E f n Q]
    exact DX.map_comp
      (Prod.mkHom ((FinitePullbackTensorRep.factors l E f n).hom.app P)
        ((FinitePullbackTensorRep.factors l E f n).hom.app Q))
      (Prod.mkHom (DerivedCategory.Q.map (e.hom.app P))
        (DerivedCategory.Q.map (e.hom.app Q)))
  have h := finitePullbackTensor_ringed_kflat_square l E f n P Q hP hQ hLP hLQ
  have hkD := congrArg (fun z ↦ DerivedCategory.Q.map z) hk
  simp only [DerivedCategory.Q.map_comp] at hkD
  exact tensorSquareTransport h hs ht hd hkD

end WeilConjectures
