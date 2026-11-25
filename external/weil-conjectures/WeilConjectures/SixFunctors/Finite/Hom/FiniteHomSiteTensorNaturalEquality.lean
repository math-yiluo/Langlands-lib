/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteTensorRouteNormalization
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientKFlatRepresentatives
/-! # Equality of the two normalized finite site tensor routes -/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
private theorem models_eq
    {C : Type*} [Category C] {S A B T : C}
    (s : S ≅ A) (t : B ≅ T) {f g : A ⟶ B} {x y : S ⟶ T}
    (hf : s.hom ≫ f ≫ t.hom = x) (hg : s.hom ≫ g ≫ t.hom = y)
    (h : x = y) : f = g := by
  apply (cancel_epi s.hom).mp
  apply (cancel_mono t.hom).mp
  simpa only [Category.assoc] using hf.trans (h.trans hg.symm)

/-- Whiskering the intrinsic tensor comparison and then the two beta components.
Source: the categorical composition in the final site-comparison paragraph
(blueprint: lem-coef-finite-hom-site-tensor-natural-equality). -/
def finiteHomTensorBetaLeftOfComparisons
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (A : C₁ × C₁ ⥤ C₁) (B : D₁ × D₁ ⥤ D₁) (D : D₂ × D₂ ⥤ D₂)
    (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂) (U : C₁ ⥤ D₁) (V : C₂ ⥤ D₂)
    (α : A ⋙ U ⟶ U.prod U ⋙ B) (τ : B ⋙ G ⟶ G.prod G ⋙ D)
    (β : U ⋙ G ⟶ F ⋙ V) : A ⋙ U ⋙ G ⟶ (F ⋙ V).prod (F ⋙ V) ⋙ D :=
  Functor.whiskerRight α G ≫ Functor.whiskerLeft (U.prod U) τ ≫
    Functor.whiskerRight (NatTrans.prod β β) D

/-- Whiskering beta on the tensor before the etale tensor comparisons.
Source: the categorical composition in the final site-comparison paragraph
(blueprint: lem-coef-finite-hom-site-tensor-natural-equality). -/
def finiteHomTensorBetaRightOfComparisons
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (A : C₁ × C₁ ⥤ C₁) (C : C₂ × C₂ ⥤ C₂) (D : D₂ × D₂ ⥤ D₂)
    (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂) (U : C₁ ⥤ D₁) (V : C₂ ⥤ D₂)
    (δ : A ⋙ F ⟶ F.prod F ⋙ C) (γ : C ⋙ V ⟶ V.prod V ⋙ D)
    (β : U ⋙ G ⟶ F ⋙ V) : A ⋙ U ⋙ G ⟶ (F ⋙ V).prod (F ⋙ V) ⋙ D :=
  Functor.whiskerLeft A β ≫ Functor.whiskerRight δ V ≫
    Functor.whiskerLeft (F.prod F) γ

-- Comparing the chosen intrinsic closed structures requires a larger kernel budget.
/-- The route through the intrinsic scalar tensorator, in the direction of beta.
Source: blueprint lemma-change-coefficients-internal-hom--1, final site-comparison paragraph
(blueprint: lem-coef-finite-hom-site-tensor-natural-equality). -/
noncomputable def finiteHomSiteTensorBetaLeft
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n) :
    (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ⋙
      coefficientFiniteQuotientDerived l E X h ⟶
    (finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m).prod
      (finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m) ⋙
      (finiteIntrinsicClosed l E X m).tensor :=
  finiteHomTensorBetaLeftOfComparisons
    (finiteHomEtaleClosed l E X n).tensor
    (finiteIntrinsicClosed l E X n).tensor (finiteIntrinsicClosed l E X m).tensor
    (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
    (finiteHomNu l E X n) (finiteHomNu l E X m)
    (finiteHomNuTensor l E X n).hom (coefFiniteHomProTensor l E X h).hom
    (finiteHomSiteBeta l E X h)

-- Comparing the chosen etale closed structures requires a larger kernel budget.
/-- The route through the etale scalar tensorator, in the direction of beta.
Source: blueprint lemma-change-coefficients-internal-hom--1, final site-comparison paragraph
(blueprint: lem-coef-finite-hom-site-tensor-natural-equality). -/
noncomputable def finiteHomSiteTensorBetaRight
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n) :
    (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ⋙
      coefficientFiniteQuotientDerived l E X h ⟶
    (finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m).prod
      (finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m) ⋙
      (finiteIntrinsicClosed l E X m).tensor :=
  finiteHomTensorBetaRightOfComparisons
    (finiteHomEtaleClosed l E X n).tensor (finiteHomEtaleClosed l E X m).tensor
    (finiteIntrinsicClosed l E X m).tensor
    (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
    (finiteHomNu l E X n) (finiteHomNu l E X m)
    (finiteHomEtaleTensor l E X h).hom (finiteHomNuTensor l E X m).hom
    (finiteHomSiteBeta l E X h)

-- The chain-model formulas involve separately encoded localization functors.
private theorem beta_routes_on_representatives
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (hP : finiteHomKFlat l E X n P) (hQ : finiteHomKFlat l E X n Q) :
    (finiteHomSiteTensorBetaLeft l E X h).app
        ((finiteHomEtaleQ l E X n).obj P, (finiteHomEtaleQ l E X n).obj Q) =
      (finiteHomSiteTensorBetaRight l E X h).app
        ((finiteHomEtaleQ l E X n).obj P, (finiteHomEtaleQ l E X n).obj Q) := by
  obtain ⟨e, he, s, t, hs, ht⟩ :=
    finiteHomSiteTensorRouteNormalization l E X h P Q hP hQ
  exact models_eq s t hs ht
    (congrArg (finiteHomIntrinsicQ l E X m).map
      (finiteHomSiteTensorChainEquation l E X h P Q e he))

-- Fully faithful descent compares the recorded derived-category presentations.
/-- The beta oriented tensor transformations agree after K-flat localization.
Source: blueprint lemma-change-coefficients-internal-hom--1, final scalar/site comparison paragraph
(blueprint: lem-coef-finite-hom-site-tensor-natural-equality).
Proof: restrict the two natural transformations to pairs of K-flat representatives.
The route normalization theorem supplies comparison isomorphisms for each route;
the ordinary chain equation identifies their chain maps. Fully faithful restriction,
followed by cancellation of those comparison isomorphisms, yields equality. -/
theorem finiteHomSiteTensorNaturalEquality
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n) :
    finiteHomSiteTensorBetaLeft l E X h = finiteHomSiteTensorBetaRight l E X h := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  obtain ⟨ff⟩ := finiteCoefficientKFlatRepresentativesFullyFaithful
    (Padic.coefficientExtensionRing l E (n + 1)) X
    (hD := inferInstanceAs (HasDerivedCategory.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))))
    (normalizedDVRDerived l E X m)
  apply ff.map_injective
  apply NatTrans.ext
  funext pq
  obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := pq
  exact beta_routes_on_representatives l E X h P Q hP hQ
end WeilConjectures
