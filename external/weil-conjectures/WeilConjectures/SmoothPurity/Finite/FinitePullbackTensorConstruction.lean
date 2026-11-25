/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-! # Derived pullback and derived tensor comparison

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-construction).

## Main definitions

* `finitePullbackTensorConstruction` constructs the prescribed comparison.
* The helper declarations fix its representative normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped MonoidalCategory
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
attribute [local irreducible] finiteIntrinsicClosed finiteIntrinsicTensorModels

/-! The comparison families below are fixed by canonical constructions. The
compatibilities are stated as equations on those same comparison maps. -/
/-- Finite unbounded tensor/pullback isomorphism families.
Source: Stacks 07A4 and the blueprint coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-construction). -/
abbrev FinitePullbackTensorComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    [_hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  ∀ (M N : proEtaleDerivedCategory Y
      (finiteCoefficientRing l E (n + 1))),
    (finiteDerivedPullback l E n f).obj
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M, N)) ≅
      (finiteIntrinsicDerivedTensor l E X n).obj
        ((finiteDerivedPullback l E n f).obj M,
          (finiteDerivedPullback l E n f).obj N)

/-- Completed integral constructible tensor/pullback isomorphism families.
Source: Stacks 07A4 and the blueprint coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-construction). -/
abbrev IntegralPullbackTensorComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  ∀ (M N : sfIntegralConstructibleCategory l E Y),
    ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
        (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M, N)) ≅
      ((@constructibleIntegralTensor l _ E _ _ _ X hX)).obj
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M,
          ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)

/-- Rational constructible tensor/pullback isomorphism families.
Source: Stacks 07A4 and the blueprint coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-construction). -/
abbrev RationalPullbackTensorComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  ∀ (M N : sfRationalConstructibleCategory l E Y),
    ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj
        (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M, N)) ≅
      ((@rationalDerivedTensor l _ E _ _ _ X hX)).obj
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M,
          ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj N)

/-- Common-stage algebraically closed tensor/pullback isomorphism families.
Source: Stacks 07A4 and the blueprint coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-construction). -/
abbrev CommonStagePullbackTensorComparison
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
      [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
    ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj
        (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M, N)) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).obj
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M,
          ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)

/-- Essential smallness with the site morphism and object sizes retained.
Source: Stacks 00YW (blueprint: def-pur-finite-pullback-tensor-construction). -/
instance (priority := 3000) pullbackTensorSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

section FiniteCanonical

open CategoryTheory.Functor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finiteness of the existing positive coefficient quotient.
Source: Serre, Local Fields II.2 (blueprint: def-pur-finite-pullback-tensor-construction). -/
noncomputable instance pullbackTensorCoefficientFinite (n : ℕ) :
    Finite (finiteCoefficientRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- The canonical constant-ring identification, with coefficient exponent n + 1.
Source: Stacks 0H7J and 07A4 (blueprint: def-pur-finite-pullback-tensor-construction). -/
def pullbackTensorCoefficientIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  letI : Finite (finiteCoefficientRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  asIso (proEtaleCoefficientInverseImageMap f (finiteCoefficientRing l E (n + 1)))

/-- The two recorded K-flat interfaces agree at the small-site coefficient size.
Source: Stacks 06YN (blueprint: def-pur-finite-pullback-tensor-construction).
Proof: apply isKFlatIndependentCoefficients_iff_isKFlat at object size u + 1
and morphism size u. Its right side is the first flat-representative property. -/
theorem pullbackTensorIndependent (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (P : (proEtaleFlatRepresentatives W R).FullSubcategory) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      W.ProEt (inferInstance : Category.{u} W.ProEt) (essentiallySmallSelf.{0, u, u + 1} W.ProEt)
      (ProEt.topology W) R P.obj := by
  exact P.property.1

/-- Restriction of the recorded K-flat model is unique with its component equations.
Source: Stacks 06YS and 07A4 (blueprint: def-pur-finite-pullback-tensor-construction).
Proof: restrict the model's comparison along the inclusion of flat-term K-flat
representatives. Every component is prescribed in the displayed formula, so
natural-transformation extensionality proves uniqueness. -/
theorem pullbackTensorFiniteRepresentative_existsUnique (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (S : CoefficientClosedStructure
      (CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology W) R))
    (T : CoefficientTensorModels.{u, u + 1, u} (ProEt.topology W) R S) :
    ∃! a : ProEtaleTensorModel W R,
      a.tensor = S.tensor ∧
      ∀ P Q : (proEtaleFlatRepresentatives W R).FullSubcategory,
        HEq (a.representative.hom.app (P,Q))
          (T.comparison.hom.app
            (⟨P.obj, pullbackTensorIndependent W R P⟩,
             ⟨Q.obj, pullbackTensorIndependent W R Q⟩)) := by
  let i := ObjectProperty.ιOfLE
    (P := proEtaleFlatRepresentatives W R)
    (P' := CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology W) (R := R))
    (fun P hP ↦ pullbackTensorIndependent W R ⟨P, hP⟩)
  let e := Functor.isoWhiskerLeft (i.prod i)
    (CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} T)
  let a : ProEtaleTensorModel W R :=
    { tensor := S.tensor
      representative := e }
  refine ⟨a, ⟨rfl, ?_⟩, ?_⟩
  · intro P Q
    rfl
  · intro b hb
    rcases b with ⟨tensor, representative⟩
    rcases hb with ⟨ht, he⟩
    dsimp at ht
    subst tensor
    have hr : representative = a.representative := by
      apply Iso.ext
      apply NatTrans.ext
      funext P
      exact eq_of_heq (he P.1 P.2)
    exact congrArg (fun r ↦ ProEtaleTensorModel.mk S.tensor r) hr

/-- The unique restriction of the prescribed finite tensor model.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-construction). -/
def pullbackTensorFiniteModel (W : Scheme.{u}) (n : ℕ) :
    ProEtaleTensorModel W (integralCoefficientCommRingSheaf l E W n) :=
  (pullbackTensorFiniteRepresentative_existsUnique W
    (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
    (finiteIntrinsicTensorModels l E W n)).exists.choose

/-- The equality of tensor functors in the preceding normalized restriction.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-construction). -/
def pullbackTensorFiniteModelIso (W : Scheme.{u}) (n : ℕ) :
    (pullbackTensorFiniteModel l E W n).tensor ≅ finiteIntrinsicDerivedTensor l E W n :=
  eqToIso (pullbackTensorFiniteRepresentative_existsUnique W
    (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
    (finiteIntrinsicTensorModels l E W n)).exists.choose_spec.1

/-- The two finite module presentations have a unique comparison preserving the
actual adjunction-unit sections. Source: Stacks 00YV, 03D2 and 07A4
(blueprint: def-pur-finite-pullback-tensor-construction).
Proof: identify their right adjoints on sections using the constant-section ring
map. Conjugating this identification by the two normalized adjunctions gives the
comparison. The adjunction unit equation is the displayed section equation.
Taking adjuncts of any second comparison with that equation makes its components
identical on every section, so the comparison is unique. -/
theorem pullbackTensorFiniteRealization_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : proEtaleRingModulePullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n) ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f,
      ∀ (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
        (x : M.val.obj (Opposite.op U)),
        (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (((proEtaleRingModuleAdjunction f
            (integralCoefficientCommRingSheaf l E Y n)
            (integralCoefficientCommRingSheaf l E X n)
            (pullbackTensorCoefficientIso l E f n)).unit.app M).val.app (Opposite.op U) x) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (Opposite.op U) x := by
  exact openSquarePullbackModel_existsUnique (finiteCoefficientRing l E (n + 1)) f

/-- The uniquely unit-normalized finite module realization.
Source: Stacks 00YV, 03D2 (blueprint: def-pur-finite-pullback-tensor-construction). -/
def pullbackTensorFiniteRealization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorFiniteRealization_existsUnique l E f n).exists.choose

/-- The canonical finite tensor comparison, using the small-site specialization of
ringedTopoiCanonicalDerivedTensorComparison and the prescribed unit-normalized
realization. Its K-flat square is proEtaleCanonicalTensorPullback; the tensor
representative comparisons are exactly finiteIntrinsicTensorModels.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-construction). -/
def finitePullbackTensorConstruction {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@FinitePullbackTensorComparison l _ E _ _ _ X Y f n hX hY) := by
  letI : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  exact fun M N ↦
    ((Functor.mapDerivedCategoryNatIso
      (pullbackTensorFiniteRealization l E f n)).app
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M, N))).symm ≪≫
    (proEtaleRingDerivedPullback f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).mapIso
        ((pullbackTensorFiniteModelIso l E Y n).app (M,N)).symm ≪≫
    (proEtaleCanonicalTensorComparison f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
      (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E X n)).app (M, N) ≪≫
    (pullbackTensorFiniteModelIso l E X n).app
      ((proEtaleRingDerivedPullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).obj M,
      (proEtaleRingDerivedPullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).obj N) ≪≫
    (finiteIntrinsicDerivedTensor l E X n).mapIso
      (Iso.prod ((Functor.mapDerivedCategoryNatIso
        (pullbackTensorFiniteRealization l E f n)).app M)
        ((Functor.mapDerivedCategoryNatIso
          (pullbackTensorFiniteRealization l E f n)).app N))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Naturality of the constructed comparison in its two derived inputs.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-construction). -/
def finitePullbackTensorConstructionIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    [_hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    finiteIntrinsicDerivedTensor l E Y n ⋙ finiteDerivedPullback l E n f ≅
      ((finiteDerivedPullback l E n f).prod (finiteDerivedPullback l E n f)) ⋙
        finiteIntrinsicDerivedTensor l E X n := by
  letI := integralCoefficientAbSheafify.{u, u} Y
  letI := integralCoefficientAbSheafify.{u, u} X
  letI := integralCoefficientAbLocallyBijective.{u, u} Y
  letI := integralCoefficientAbLocallyBijective.{u, u} X
  letI : Abelian (normalizedDVRModules l E Y n) :=
    SheafOfModules.instAbelian (integralCoefficientSheaf l E Y n)
  letI : Abelian (normalizedDVRModules l E X n) :=
    SheafOfModules.instAbelian (integralCoefficientSheaf l E X n)
  let F := proEtaleRingDerivedPullback f
    (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
  let r : F ≅ finiteDerivedPullback l E n f :=
    @Functor.mapDerivedCategoryNatIso
      (normalizedDVRModules l E Y n) (normalizedDVRModules l E X n) _ _
      (SheafOfModules.instAbelian (integralCoefficientSheaf l E Y n))
      (SheafOfModules.instAbelian (integralCoefficientSheaf l E X n)) _ _
      (proEtaleRingModulePullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
      (proEtaleRingModulePullback_additive f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f)
      (proEtaleRingModulePullback_preservesFiniteLimits f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (proEtaleRingModulePullback_preservesFiniteColimits f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f)
      (sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f)
      (pullbackTensorFiniteRealization l E f n)
  exact Functor.isoWhiskerLeft (finiteIntrinsicDerivedTensor l E Y n) r.symm ≪≫
    Functor.isoWhiskerRight (pullbackTensorFiniteModelIso l E Y n).symm F ≪≫
    proEtaleCanonicalTensorComparison f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
      (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E X n) ≪≫
    Functor.isoWhiskerLeft (F.prod F) (pullbackTensorFiniteModelIso l E X n) ≪≫
    Functor.isoWhiskerRight (NatIso.prod r r) (finiteIntrinsicDerivedTensor l E X n)

end FiniteCanonical

end WeilConjectures
