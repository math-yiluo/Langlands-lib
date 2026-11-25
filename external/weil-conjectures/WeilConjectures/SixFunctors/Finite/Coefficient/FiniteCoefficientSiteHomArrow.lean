/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteChainTensor

import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteTensorPresentation
/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node lemma-change-coefficients-internal-hom--1 (blueprint:
def-sf-finite-coefficient-site-hom-arrow). Indices n and m below denote exponents n + 1 and m + 1;
thus every positive exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Explicit K-flat witness type with the small pro-etale universe fixed.
Source: blueprint site-comparison proof (blueprint: def-sf-finite-coefficient-site-hom-arrow). -/
abbrev finiteHomKFlat (n : ℕ)
    (P : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) : Prop :=
  @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
    X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
    ((finiteHomNuComplex l E X n).obj P)

/-- Representative normalization with the category and tensor data shared.
Source: Stacks 07A4, site-comparison paragraph
(blueprint: def-sf-finite-coefficient-site-hom-arrow). -/
def FiniteHomNuTensorNormalizationAux
    {C : Type a} {D : Type b} {A : Type c} {B : Type d}
    [Category.{e} C] [Category.{f} D] [Category.{g} A] [Category.{w} B]
    (QA : C ⥤ A) (QB : D ⥤ B) (U : C ⥤ D) (V : A ⥤ B)
    (ρ : QA ⋙ V ≅ U ⋙ QB) (P : ObjectProperty C) (S : ObjectProperty D)
    (hU : ∀ x, P x → S (U.obj x))
    (t : C × C ⥤ C) (t' : D × D ⥤ D) (T : A × A ⥤ A) (T' : B × B ⥤ B)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ QB ≅ ((S.ι ⋙ QB).prod (S.ι ⋙ QB)) ⋙ T')
    {M : C → C → Type g} (η : ∀ x y, M x y)
    {F : C → C → Type f} (ε : ∀ x y, F x y)
    (μ : T ⋙ V ≅ V.prod V ⋙ T') : Prop :=
  ∀ x y (hx : P x) (hy : P y),
    ∃ (a : T.obj (QA.obj x, QA.obj y) ⟶ QA.obj (t.obj (x, y)))
      (e : U.obj (t.obj (x, y)) ≅ t'.obj (U.obj x, U.obj y)),
      HEq a (η x y) ∧ HEq e (ε x y) ∧
      μ.hom.app (QA.obj x, QA.obj y) ≫
          T'.map (Prod.mkHom (ρ.hom.app x) (ρ.hom.app y)) ≫
            r'.inv.app (⟨U.obj x, hU x hx⟩, ⟨U.obj y, hU y hy⟩) =
        V.map a ≫ ρ.hom.app (t.obj (x, y)) ≫ QB.map e.hom

private theorem tensorModelSquare_iff
    {C : Type a} {D : Type b} {A : Type c} {B : Type d}
    [Category.{e} C] [Category.{f} D] [Category.{g} A] [Category.{w} B]
    (QA : C ⥤ A) (QB : D ⥤ B) (U : C ⥤ D) (V : A ⥤ B)
    (ρ : QA ⋙ V ≅ U ⋙ QB) (TA : C → C → C) (TB : D → D → D)
    (SA : A × A ⥤ A) (SB : B × B ⥤ B)
    (μ : SA ⋙ V ≅ V.prod V ⋙ SB) (P Q : C)
    (ηA : SA.obj (QA.obj P, QA.obj Q) ⟶ QA.obj (TA P Q))
    (ε : U.obj (TA P Q) ≅ TB (U.obj P) (U.obj Q))
    (ηB : SB.obj (QB.obj (U.obj P), QB.obj (U.obj Q)) ≅
      QB.obj (TB (U.obj P) (U.obj Q)))
    (rA : QA.obj (TA P Q) ≅ SA.obj (QA.obj P, QA.obj Q))
    (hrA : rA.inv = ηA) :
    (μ.hom.app (QA.obj P, QA.obj Q) ≫
        SB.map (Prod.mkHom (ρ.hom.app P) (ρ.hom.app Q)) ≫ ηB.hom =
      V.map ηA ≫ ρ.hom.app (TA P Q) ≫ QB.map ε.hom) ↔
      V.map rA.hom ≫ μ.hom.app (QA.obj P, QA.obj Q) ≫
          SB.map (Prod.mkHom (ρ.hom.app P) (ρ.hom.app Q)) =
        ρ.hom.app (TA P Q) ≫ QB.map ε.hom ≫ ηB.inv := by
  constructor
  · intro h
    apply (cancel_mono ηB.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, ← V.map_comp_assoc, ← hrA, Iso.hom_inv_id, V.map_id, Category.id_comp]
  · intro h
    apply (cancel_epi (V.map rA.hom)).1
    rw [← V.map_comp_assoc, ← hrA, Iso.hom_inv_id, V.map_id, Category.id_comp]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k ↦ k ≫ ηB.hom) h

private theorem tensorModelSquareDescent
    {C : Type a} {D : Type b} {A : Type c} {B : Type d}
    [Category.{e} C] [Category.{f} D] [Category.{g} A] [Category.{w} B]
    (QA : C ⥤ A) (QB : D ⥤ B) (U : C ⥤ D) (V : A ⥤ B)
    (ρ : QA ⋙ V ≅ U ⋙ QB) (P : ObjectProperty C) (S : ObjectProperty D)
    (hU : ∀ x, P x → S (U.obj x))
    (ff : ((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (A × A) B).obj ((P.ι ⋙ QA).prod (P.ι ⋙ QA))).FullyFaithful)
    (t : C × C ⥤ C) (t' : D × D ⥤ D) (T : A × A ⥤ A) (T' : B × B ⥤ B)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ QA ≅ ((P.ι ⋙ QA).prod (P.ι ⋙ QA)) ⋙ T)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ QB ≅ ((S.ι ⋙ QB).prod (S.ι ⋙ QB)) ⋙ T')
    (b : t ⋙ U ≅ U.prod U ⋙ t')
    {M : C → C → Type g} (η : ∀ x y, M x y)
    {F : C → C → Type f} (ε : ∀ x y, F x y)
    (hr : ∀ x y (hx : P x) (hy : P y),
      HEq (r.inv.app (⟨x, hx⟩, ⟨y, hy⟩)) (η x y))
    (hb : ∀ x y, HEq (b.app (x, y)) (ε x y)) :
    ∃! μ, FiniteHomNuTensorNormalizationAux
      QA QB U V ρ P S hU t t' T T' r' η ε μ := by
  obtain ⟨μ, hμ, huniq⟩ :=
    tensorComparisonDescent QA QB U V ρ.hom P S hU ff t t' T T' r r' b
      (fun x _ ↦ (ρ.app x).isIso_hom)
      (fun x y _ _ ↦ (ρ.app (t.obj (x, y))).isIso_hom)
  unfold FiniteHomNuTensorNormalizationAux
  have hi (ν : T ⋙ V ≅ V.prod V ⋙ T') (x y : C) (hx : P x) (hy : P y) :=
    tensorModelSquare_iff QA QB U V ρ (fun x y ↦ t.obj (x, y))
      (fun x y ↦ t'.obj (x, y)) T T' ν x y
      (r.inv.app (⟨x, hx⟩, ⟨y, hy⟩)) (b.app (x, y))
      (r'.app (⟨U.obj x, hU x hx⟩, ⟨U.obj y, hU y hy⟩)).symm
      (r.app (⟨x, hx⟩, ⟨y, hy⟩)) rfl
  refine ⟨μ, ?_, ?_⟩
  · intro x y hx hy
    refine ⟨r.inv.app (⟨x, hx⟩, ⟨y, hy⟩), b.app (x, y), hr x y hx hy, hb x y, ?_⟩
    apply (hi μ x y hx hy).2
    simpa only [Iso.symm_inv, Iso.app_hom] using hμ x y hx hy
  · intro ν hν
    apply huniq ν
    intro x y hx hy
    obtain ⟨a, e, ha, he, h⟩ := hν x y hx hy
    have ha' : a = r.inv.app (⟨x, hx⟩, ⟨y, hy⟩) :=
      eq_of_heq (ha.trans (hr x y hx hy).symm)
    have he' : e = b.app (x, y) := eq_of_heq (he.trans (hb x y).symm)
    subst a e
    have h := (hi ν x y hx hy).1 h
    simpa only [Iso.symm_inv, Iso.app_hom] using h

private theorem tensorModelSquareDescentOfPresentation
    {C : Type a} {D : Type b} {A : Type c} {B : Type d}
    [Category.{e} C] [Category.{f} D] [Category.{g} A] [Category.{w} B]
    (QA : C ⥤ A) (QB : D ⥤ B) (U : C ⥤ D) (V : A ⥤ B)
    (ρ : QA ⋙ V ≅ U ⋙ QB) (P : ObjectProperty C) (S : ObjectProperty D)
    (hU : ∀ x, P x → S (U.obj x))
    (t : C × C ⥤ C) (t' : D × D ⥤ D) (T : A × A ⥤ A) (T' : B × B ⥤ B)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ QB ≅ ((S.ι ⋙ QB).prod (S.ι ⋙ QB)) ⋙ T')
    {M : C → C → Type g} (η : ∀ x y, M x y)
    {F : C → C → Type f} (ε : ∀ x y, F x y)
    (h : FiniteHomTensorPresentationAux B QA U t t' T P η ε) :
    ∃! μ, FiniteHomNuTensorNormalizationAux
      QA QB U V ρ P S hU t t' T T' r' η ε μ := by
  obtain ⟨⟨ff⟩, ⟨r, hr⟩, ⟨b, hb⟩⟩ := h
  exact tensorModelSquareDescent QA QB U V ρ P S hU ff t t' T T'
    r r' b η ε hr hb

/-- The specified tensorator is characterized on every pair of explicit K-flat
representatives by the ordinary pure-tensor chain comparison and the intrinsic
localization comparison. Source: Stacks 00YV, 06YN, 07A4 (blueprint:
def-sf-finite-coefficient-site-hom-arrow). -/
def FiniteHomNuTensorNormalization (n : ℕ)
    (μ : (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ≅
      (finiteHomNu l E X n).prod (finiteHomNu l E X n) ⋙
        (finiteIntrinsicClosed l E X n).tensor) : Prop :=
  let : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let : HasDerivedCategory.{u + 2} (normalizedDVRModules l E X n) :=
    HasDerivedCategory.standard _
  let K := CochainComplex (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1))))) ℤ
  let S : ObjectProperty (CochainComplex (normalizedDVRModules l E X n) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
  let P : ObjectProperty K := fun A ↦ S ((finiteHomNuComplex l E X n).obj A)
  FiniteHomNuTensorNormalizationAux
    (finiteHomEtaleQ l E X n) (finiteHomIntrinsicQ l E X n)
    (finiteHomNuComplex l E X n) (finiteHomNu l E X n) (finiteHomNuFactors l E X n)
    P S (fun _ h ↦ h) (finiteHomCochainTensorGeneral _)
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n))
    (finiteHomEtaleClosed l E X n).tensor (finiteIntrinsicClosed l E X n).tensor
    (finiteIntrinsicTensorModels l E X n).comparison
    (finiteHomEtaleTensorModel l E X n) (finiteHomNuChainTensor l E X n) μ

attribute [local irreducible] coefficientTotalTensor finiteHomNuComplex finiteHomNuChainTensor
  finiteHomEtaleTensorModel finiteHomNuFactors
  finiteIntrinsicTensorModels finiteIntrinsicClosed finiteHomNu
  finiteHomEtaleData

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse-image tensor comparison is uniquely fixed by the displayed
K-flat pure-tensor and localization equations. Source: blueprint site-comparison
proof (blueprint: def-sf-finite-coefficient-site-hom-arrow).
Proof: inverse image preserves the balanced pure-tensor chain map; localization
and the intrinsic tensor-model comparison identify its derived image. The
representative equation determines the natural isomorphism uniquely. -/
theorem finiteHomNuTensor_existsUnique (n : ℕ) :
    ∃! μ, FiniteHomNuTensorNormalization l E X n μ := by
  let : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let : HasDerivedCategory.{u + 2} (normalizedDVRModules l E X n) :=
    HasDerivedCategory.standard _
  let K := CochainComplex (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1))))) ℤ
  let t : K × K ⥤ K := finiteHomCochainTensorGeneral _
  let S : ObjectProperty (CochainComplex (normalizedDVRModules l E X n) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
  let P : ObjectProperty K := fun A ↦ S ((finiteHomNuComplex l E X n).obj A)
  unfold FiniteHomNuTensorNormalization
  exact tensorModelSquareDescentOfPresentation
    (finiteHomEtaleQ l E X n) (finiteHomIntrinsicQ l E X n)
    (finiteHomNuComplex l E X n) (finiteHomNu l E X n)
    (finiteHomNuFactors l E X n) P S (fun _ h ↦ h)
    t
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n))
    (finiteHomEtaleClosed l E X n).tensor (finiteIntrinsicClosed l E X n).tensor
    (finiteIntrinsicTensorModels l E X n).comparison
    (finiteHomEtaleTensorModel l E X n) (finiteHomNuChainTensor l E X n)
    (finiteHomNuTensorPresentation l E X n)

/-- The canonical normalized tensor comparison for nu_X^*.
Source: blueprint site-comparison proof (blueprint: def-sf-finite-coefficient-site-hom-arrow). -/
def finiteHomNuTensor (n : ℕ) :
    (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ≅
      (finiteHomNu l E X n).prod (finiteHomNu l E X n) ⋙
        (finiteIntrinsicClosed l E X n).tensor :=
  (finiteHomNuTensor_existsUnique l E X n).choose

/-- The site internal-Hom comparison, the transpose of inverse image of evaluation.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-hom-arrow). -/
def finiteHomSiteHom (n : ℕ) :=
  coefficientBaseChangeHom (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
    (finiteHomNu l E X n) (finiteHomNuTensor l E X n)

end WeilConjectures
