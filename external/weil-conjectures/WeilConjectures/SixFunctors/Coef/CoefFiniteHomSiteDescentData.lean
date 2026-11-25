/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteHomArrow
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteScalarArrow
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteChainTensor
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude

/-! # Finite Hom scalar/site square and constructible descent

Source: blueprint `lemma-change-coefficients-internal-hom--1`, final paragraph and final
site-comparison sentence, expanded in the seven proof steps of lem-coef-finite-hom-site-descent
(blueprint: lem-coef-finite-hom-site-descent).

The indices n,m,r mean the positive exponents n+1,m+1,r+1. The canonical
scalar/site isomorphism is the inverse of the existing adjunction mate, and the
Hom comparisons are the existing evaluation transposes. No scalar-Hom
invertibility is asserted. Object and morphism universes of the small site remain distinct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u a b c d va vb vc vd
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Strong monoidality for a specified tensor comparison, including unit and associativity.
The unit is determined by this tensorator and the two unit axioms, so it is not extra
unconstrained comparison data. Source: blueprint final paragraph; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomStrong
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) :=
  letI := SA.monoidal
  letI := SB.monoidal
  {s : F.CoreMonoidal // ∀ P Q : A, s.μIso P Q = (μ.app (P, Q)).symm}

/-- The monoidal square equations for the fixed tensorators and their coherent units.
Source: blueprint final site-comparison sentence; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomMonoidalSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (h : F ⋙ V ≅ U ⋙ G) : Prop :=
  ∃ sF : CoefFiniteHomStrong SA SB F μF,
    ∃ sG : CoefFiniteHomStrong SC SD G μG,
      ∃ sU : CoefFiniteHomStrong SA SC U μU,
        ∃ sV : CoefFiniteHomStrong SB SD V μV,
          (∀ K M : A,
            h.hom.app (SA.tensor.obj (K, M)) ≫ G.map (μU.hom.app (K, M)) ≫
                μG.hom.app (U.obj K, U.obj M) =
              V.map (μF.hom.app (K, M)) ≫ μV.hom.app (F.obj K, F.obj M) ≫
                SD.tensor.map (Prod.mkHom (h.hom.app K) (h.hom.app M))) ∧
          h.hom.app SA.monoidal.tensorUnit ≫
              G.map (@Functor.CoreMonoidal.εIso _ _ SA.monoidal _ _ SC.monoidal U sU.val).inv ≫
              (@Functor.CoreMonoidal.εIso _ _ SC.monoidal _ _ SD.monoidal G sG.val).inv =
            V.map (@Functor.CoreMonoidal.εIso _ _ SA.monoidal _ _ SB.monoidal F sF.val).inv ≫
              (@Functor.CoreMonoidal.εIso _ _ SB.monoidal _ _ SD.monoidal V sV.val).inv

/-- Naturality, evaluation/transpose and internal composition at finite-Tor pairs.
This is the restriction of the existing coefficient evaluation equations to the stated
constructible domain. Source: blueprint final paragraph, equations transported by the square
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomLawsOn
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P : ObjectProperty A) : Prop :=
  (∀ K M K' M' : A, P K → P M → P K' → P M' →
    ∀ (f : K' ⟶ K) (g : M ⟶ M'),
      F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ K' M' =
        coefficientBaseChangeHom SA SB F μ K M ≫
          HB.map (Prod.mkHom (F.map f).op (F.map g))) ∧
  (∀ K M : A, P K → P M → ∀ (T : A) (f : SA.tensor.obj (T, K) ⟶ M),
    F.map (SA.transpose T K M f) ≫ coefficientBaseChangeHom SA SB F μ K M =
      SB.transpose (F.obj T) (F.obj K) (F.obj M) (μ.inv.app (T, K) ≫ F.map f)) ∧
  (∀ K L M : A, P K → P L → P M →
    F.map (SA.composition K L M) ≫ coefficientBaseChangeHom SA SB F μ K M =
      μ.hom.app (HA.obj (op L, M), HA.obj (op K, L)) ≫
        SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ L M)
          (coefficientBaseChangeHom SA SB F μ K L)) ≫
        SB.composition (F.obj K) (F.obj L) (F.obj M))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The specified coefficient/site isomorphism h, inverse to the scalar-restriction mate.
Source: blueprint final site-comparison sentence
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomSiteIso {n m : ℕ} (h : m ≤ n) :
    finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m ≅
      finiteHomNu l E X n ⋙ coefficientFiniteQuotientDerived l E X h :=
  (asIso (finiteHomSiteBeta l E X h)).symm

/-- Bounded constructibility in the existing positive-level etale category.
Source: blueprint constructible descent clause
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomEtaleConstructible (n : ℕ) : ObjectProperty (finiteHomEtale l E X n) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X

/-- Descent, reflection for every bounded constructible witness, and interval preservation.
Source: blueprint site-comparison sentence; proof step 1
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomDescent (n : ℕ) : Prop :=
  PreservesFiniteLimits (finiteHomNuOrdinary l E X n) ∧
  PreservesFiniteColimits (finiteHomNuOrdinary l E X n) ∧
  (∀ P : normalizedDVRDerived l E X n,
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X P →
    ∃ P' : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X P' ∧
      Nonempty ((finiteHomNu l E X n).obj P' ≅ P)) ∧
  (∀ (P : normalizedDVRDerived l E X n) (P' : finiteHomEtale l E X n),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X P →
    coefFiniteHomEtaleConstructible l E X n P' →
    Nonempty ((finiteHomNu l E X n).obj P' ≅ P) → ∀ a b : ℤ, a ≤ b →
      (Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X a b P' ↔
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) P a b)) ∧
  (∀ P' : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X P' →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
      ((finiteHomNu l E X n).obj P') ∧
    ∀ a b : ℤ, a ≤ b → Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X a b P' →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((finiteHomNu l E X n).obj P') a b)

/-- The actual canonical square, with the inverse h in the contravariant Hom input.
Source: blueprint final site-comparison sentence; proof step 6
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSquare {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ K M : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    IsIso (finiteHomSiteHom l E X n K M) ∧
    IsIso (finiteHomSiteHom l E X m
      ((finiteHomEtaleReduction l E X h).obj K)
      ((finiteHomEtaleReduction l E X h).obj M)) ∧
    (coefFiniteHomSiteIso l E X h).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ≫
      (coefficientFiniteQuotientDerived l E X h).map (finiteHomSiteHom l E X n K M) ≫
      proEtaleFiniteHomCanonical l E X h
        ((finiteHomNu l E X n).obj K) ((finiteHomNu l E X n).obj M) =
    (finiteHomNu l E X m).map (etaleFiniteHomCanonical l E X h K M) ≫
      finiteHomSiteHom l E X m
        ((finiteHomEtaleReduction l E X h).obj K)
        ((finiteHomEtaleReduction l E X h).obj M) ≫
      (coefficientFiniteInternalHom l E X m).map
        (Prod.mkHom ((coefFiniteHomSiteIso l E X h).inv.app K).op
          ((coefFiniteHomSiteIso l E X h).hom.app M))

/-- Coherence for the actual scalar/site isomorphisms under successive quotients.
Source: blueprint final paragraph; proof step 4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomQuotientCoherence {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ (r : ℕ) (k : r ≤ m) (T : finiteHomEtale l E X n),
    (finiteHomNu l E X r).map ((finiteHomEtaleAssoc l E X h k).hom.app T) ≫
      (coefFiniteHomSiteIso l E X (k.trans h)).hom.app T =
    (coefFiniteHomSiteIso l E X k).hom.app ((finiteHomEtaleReduction l E X h).obj T) ≫
      (coefficientFiniteQuotientDerived l E X k).map
        ((coefFiniteHomSiteIso l E X h).hom.app T) ≫
      (finiteHomIntrinsicAssoc l E X h k).hom.app ((finiteHomNu l E X n).obj T)

/-- The fixed intrinsic scalar tensorator, projected from the published quotient calculus.
Source: blueprint scalar tensor convention; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomProTensor {n m : ℕ} (h : m ≤ n) :=
  (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h

/-- Symmetry of a specified tensor comparison, using the supplied canonical symmetries.
Source: blueprint monoidal clause; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSymmetry
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (βA : @SymmetricCategory A _ SA.monoidal)
    (βB : @SymmetricCategory B _ SB.monoidal)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q : A,
    F.map (βA.toBraidedCategory.braiding P Q).hom ≫ μ.hom.app (Q, P) =
      μ.hom.app (P, Q) ≫ (βB.toBraidedCategory.braiding (F.obj P) (F.obj Q)).hom

/-- The canonical identity-quotient scalar associator, adjoint to identity restriction.
Source: blueprint identity quotient convention
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomProUnit (n : ℕ) :
    coefficientFiniteQuotientDerived l E X (Nat.le_refl n) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (Nat.le_refl n)) (normalizedDVRResUnit l E X n)

/-- Transport of successive quotient and identity equations from the etale transposes
to the intrinsic transposes, on finite-Tor constructible pairs.
Source: blueprint final paragraph; proof step 7
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSuccessive {n m : ℕ} (h : m ≤ n) : Prop :=
  ((∀ (r : ℕ) (k : r ≤ m) (K M : finiteHomEtale l E X n),
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    (finiteHomEtaleAssoc l E X h k).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ≫
      etaleFiniteHomCanonical l E X (k.trans h) K M =
    (finiteHomEtaleReduction l E X k).map
        (etaleFiniteHomCanonical l E X h K M) ≫
      etaleFiniteHomCanonical l E X k
        ((finiteHomEtaleReduction l E X h).obj K)
        ((finiteHomEtaleReduction l E X h).obj M) ≫
      (finiteHomEtaleInternalHom l E X r).map
        (Prod.mkHom ((finiteHomEtaleAssoc l E X h k).inv.app K).op
          ((finiteHomEtaleAssoc l E X h k).hom.app M))) ∧
  (∀ K M : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    etaleFiniteHomCanonical l E X (Nat.le_refl n) K M ≫
      (finiteHomEtaleInternalHom l E X n).map
        (Prod.mkHom
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
            (finiteHomQuotient l E (Nat.le_refl n))
            (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
              (S := Padic.coefficientExtensionIdeal l E (n + 1))))).inv.app K).op
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
            (finiteHomQuotient l E (Nat.le_refl n))
            (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
              (S := Padic.coefficientExtensionIdeal l E (n + 1))))).hom.app M)) =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
        (finiteHomQuotient l E (Nat.le_refl n))
        (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
          (S := Padic.coefficientExtensionIdeal l E (n + 1))))).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)))) →
  (∀ (r : ℕ) (k : r ≤ m) (K M : normalizedDVRDerived l E X n),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
    (finiteHomIntrinsicAssoc l E X h k).hom.app
        ((coefficientFiniteInternalHom l E X n).obj (op K, M)) ≫
      proEtaleFiniteHomCanonical l E X (k.trans h) K M =
    (coefficientFiniteQuotientDerived l E X k).map
        (proEtaleFiniteHomCanonical l E X h K M) ≫
      proEtaleFiniteHomCanonical l E X k
        ((coefficientFiniteQuotientDerived l E X h).obj K)
        ((coefficientFiniteQuotientDerived l E X h).obj M) ≫
      (coefficientFiniteInternalHom l E X r).map
        (Prod.mkHom ((finiteHomIntrinsicAssoc l E X h k).inv.app K).op
          ((finiteHomIntrinsicAssoc l E X h k).hom.app M))) ∧
  (∀ K M : normalizedDVRDerived l E X n,
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
    proEtaleFiniteHomCanonical l E X (Nat.le_refl n) K M ≫
      (coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom ((coefFiniteHomProUnit l E X n).inv.app K).op
          ((coefFiniteHomProUnit l E X n).hom.app M)) =
      (coefFiniteHomProUnit l E X n).hom.app
        ((coefficientFiniteInternalHom l E X n).obj (op K, M)))

end WeilConjectures
