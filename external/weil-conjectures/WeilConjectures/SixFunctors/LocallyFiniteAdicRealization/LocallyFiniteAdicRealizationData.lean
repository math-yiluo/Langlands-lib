/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientBasicSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation

/-! # Native locally finite adic realization data

These are the existing realization presentations, unchanged and reexported by
`LocallyFiniteAdicConstructibleRealization`. Source: Bhatt--Scholze, Section 6.8,
Lemma 6.8.2 and Proposition 6.8.14
(blueprint: def-sf-locally-finite-adic-realization-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The native locally finite coefficient ring, read in abelian sheaves.
Source: Bhatt--Scholze, 6.8.1--6.8.2, native coefficient specialization
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
abbrev abRing :=
  (ProEtale.weilCoefficientsForgetAb l X).obj (ProEtale.adicConstantSheaf l X)

/-- The sectionwise ring of the native internal coefficient. Its underlying sections
are exactly the same locally finite continuous functions, with pointwise operations.
Source: Bhatt--Scholze, 6.8.1--6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def ringSheaf [IsCommMonObj (abRing l X)] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (ProEt.topology X) (abRing l X)

/-- The canonical section-module functor, retaining the native module action.
Source: internal-module convention of def-sf-native-weil-derived-framework and
Bhatt--Scholze, 6.8.1
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def sections [IsCommMonObj (abRing l X)] :=
  ProEtale.AdicSheaf.forgetAb l X ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) (abRing l X)).functor

/-- The specified finite-field inclusion, undoing only the published size transport.
Source: common finite-field convention and Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def embedding (E : Index l (PadicAlgCl l)) :
    Coefficient.{u} l (PadicAlgCl l) E →ₐ[Padic l] PadicAlgCl l :=
  E.val.val.comp (Shrink.algEquiv (Padic l) E.val).toAlgHom

/-- The inverse-limit and localization identifications used in one integral formula.
All ring maps are fixed pointwise, and all finite-quotient isomorphisms fix constants.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure CoefficientPresentation [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) where
  integral : AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
      E ≅
    completedIntegralCommRingSheafUnrestricted l E X
  finite : ∀ n : ℕ,
    integralCoefficientCommRingSheaf l E X n ≅
      finiteContinuousCoefficientSheaf l X E n
  finite_constants : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : finiteCoefficientRing l E n)
      (x : U.unop.left),
    finiteContinuousCoefficientValue l E X n U
      ((finite n).hom.hom.app U ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (finiteCoefficientRing l E n))).app U a)) x = a
  integral_residues : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
        E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X n U
      ((integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l
        E X n ≫ (finite n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E X U s x)
  localization : integralCoefficientLocalization l X E ≅
    rationalCoefficientSheaf l X E
  localization_normalized : integralCoefficientLocalizationNormalized l
    E X localization.hom
  integralInclusion : AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
      E ⟶
    rationalCoefficientSheaf l X E
  integralInclusion_normalized : integralRationalCoefficientNormalized l
    E X integralInclusion
  rationalInclusion : rationalCoefficientSheaf l X E ⟶
    ringSheaf l X
  rationalInclusion_normalized : ∀ (U : X.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X
        E).obj.obj U) (x : U.unop.left),
    (rationalInclusion.hom.app U s).down.1 x =
      i (rationalCoefficientValue l E X U s x)

/-- The actual structural ring map B_integral to B_native. It is the composite of the
normalized completion identification, integral inclusion and finite-field inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def CoefficientPresentation.integralMap [IsCommMonObj (abRing l X)]
    {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {i : E →ₐ[Padic l] PadicAlgCl l} (C : CoefficientPresentation l X E i) :
    completedIntegralCommRingSheafUnrestricted l
      E X ⟶ ringSheaf l X :=
  C.integral.inv ≫ C.integralInclusion ≫ C.rationalInclusion

/-- One ordinary realization, with its exact essential image and full derived Hom
bijections. The comparison to the universal derived tensor functor is natural on
integral arrows; functoriality then sends inverse uniformizer powers to their inverses.
The common-stage category already uses balanced extension and eventual equality of
representatives, so its arrows, including arrows between different finite stages, are
realized by the same functor. The `common_field` equation fixes its transition
isomorphisms by the canonical completion map and balanced derived tensor associator;
HEq retains the published literal-object transports instead of selecting new isomorphisms.
Source: Bhatt--Scholze, Proposition 6.8.14 and the native smallness addendum
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure RealizationCore where
  [commutative : IsCommMonObj (abRing l X)]
  [sectionsAdditive : (sections l X).Additive]
  [sectionsLimits : PreservesFiniteLimits (sections l X)]
  [sectionsColimits : PreservesFiniteColimits (sections l X)]
  coefficient : ∀ E : Index l (PadicAlgCl l),
    CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)
  coefficient_scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
      (coefficient L).integralMap l X = (coefficient E).integralMap l X
  J : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ⥤
    DerivedCategory (ProEtale.AdicSheaf l X)
  [additive : J.Additive]
  [shift : J.CommShift ℤ]
  triangulated : J.IsTriangulated
  fully_faithful : ∀ K L, Function.Bijective (J.map : (K ⟶ L) → (J.obj K ⟶ J.obj L))
  image : ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
    ∃ A, Nonempty (J.obj A ≅ K)
  integral : ∀ E : Index l (PadicAlgCl l),
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
        J ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend.{u} ((coefficient E).integralMap l X)
  sourceSmall : EssentiallySmall.{u + 1}
    (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
  targetSmall : EssentiallySmall.{u + 1}
    (ProEtale.DerivedCategory.boundedAdicConstructible l X).FullSubcategory

/-- The specific completion map, read through the canonical derived tensor presentation.
This is the published map characterized by its quotient-completion chain map and counit.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def completedTensorComparison
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) :
    pbcDerivedExtend.{u} (completedCoefficientMap l E L i X) ⟶
      integralScalarExtensionOfUniverses l E L i X :=
  completedScalarComparison l E L i X

/-- The common-field identification is the specified completion and balanced-tensor map.
Source: Bhatt--Scholze, Proposition 6.8.14, and the completion-map scalar comparison
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def commonField (R : RealizationCore l X) : Prop :=
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    HEq
      ((sections l X).mapDerivedCategory.map
          (R.J.map ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨E, (sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom)))
      ((R.integral E).hom.app K ≫
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((R.coefficient L).integralMap l X) ((R.coefficient E).integralMap l X)
          (R.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((R.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) ≫
        (R.integral L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
            E L h).obj K))

/-- A realization with its canonical common-field transition normalization.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure Realization extends RealizationCore l X where
  common_field : commonField l X toRealizationCore

end WeilConjectures.LocallyFiniteAdicRealization
