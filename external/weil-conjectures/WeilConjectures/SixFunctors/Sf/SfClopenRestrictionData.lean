/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
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
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final

/-! # Interfaces for normalized complete restriction to a clopen

Source: Stacks Project, proetale.tex, Tags 09C3 and 098F; sites-cohomology.tex,
Tag 0946; derived.tex, Tag 08TC (blueprint: lem-sf-clopen-lisse-complete-localization).

The coefficient comparisons below are fixed by constant sections and the actual
inverse-limit projections. Restriction is sectionwise precomposition, descended
termwise to unbounded derived categories. Index n denotes the positive exponent n+1.

## Main declarations

- `SfClopenCoefficientRestriction`: the normalized coefficient and exact restriction data.
- `SfClopenCompleteRestriction`: canonical reduction, augmented tower and Tor compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The site inclusion for an open subscheme, by composition of weakly etale maps.
Source: Stacks 00XZ and 09AE (blueprint: lem-sf-clopen-lisse-complete-localization). -/
abbrev sfClopenSiteInclusion {T : Scheme.{t}} (U : T.Opens) :
    U.toScheme.ProEt ⥤ T.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale U.ι)

/-- The continuous site inclusion used for ordinary restriction.
Source: Stacks 09AE (blueprint: lem-sf-clopen-lisse-complete-localization). -/
instance sfClopenSiteInclusionContinuous {T : Scheme.{t}} (U : T.Opens) :
    (sfClopenSiteInclusion U).IsContinuous (Scheme.ProEt.topology U.toScheme)
      (Scheme.ProEt.topology T) :=
  Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale U.ι)

/-- Restriction of a ring sheaf by precomposition, with unchanged section rings.
Source: Stacks 00Y0 (blueprint: lem-sf-clopen-lisse-complete-localization). -/
abbrev sfClopenRingRestriction {T : Scheme.{t}} (U : T.Opens)
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{v}) :=
  ((sfClopenSiteInclusion U).sheafPushforwardContinuous
    RingCat.{v} (Scheme.ProEt.topology U.toScheme) (Scheme.ProEt.topology T)).obj R

/-- Sectionwise restriction with scalars identified by the specified ring comparison.
Source: Stacks 03DH (blueprint: lem-sf-clopen-lisse-complete-localization). -/
abbrev sfClopenModuleRestriction {T : Scheme.{t}} (U : T.Opens)
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{v})
    (S : Sheaf (Scheme.ProEt.topology U.toScheme) RingCat.{v})
    (c : S ≅ sfClopenRingRestriction U R) : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S :=
  SheafOfModules.pushforward (F := sfClopenSiteInclusion U) (𝟙 _) ⋙
    SheafOfModules.restrictScalars c.hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Canonical coefficient identifications and exact ordinary restriction on a component.
The constant-section normalization fixes the finite comparisons; the projection squares
fix the completed comparison uniquely. Exactness is evidence, not extra hypotheses on T.
Source: Stacks 00Y0, 09C3, 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
structure SfClopenCoefficientRestriction (T : Scheme.{t}) (U : T.Opens) where
  /-- Finite coefficients, oriented from local coefficients to restricted coefficients. -/
  finite : ∀ n : ℕ, integralCoefficientSheaf l E U.toScheme n ≅
    sfClopenRingRestriction U (integralCoefficientSheaf l E T n)
  /-- Constant sections are fixed, on every site object. -/
  finite_constant : ∀ (n : ℕ) (V : U.toScheme.ProEt)
      (x : ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))),
    (finite n).hom.hom.app (op V)
      ((toSheafify (Scheme.ProEt.topology U.toScheme)
        ((Functor.const U.toScheme.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
            (op V) x) =
    (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op ((sfClopenSiteInclusion U).obj V)) x
  /-- The completion comparison is the inverse-limit comparison. -/
  completion : completedIntegralCoefficientSheafUnrestricted l E U.toScheme ≅
    sfClopenRingRestriction U (completedIntegralCoefficientSheafUnrestricted l E T)
  /-- The completion comparison commutes with every quotient projection. -/
  projection : ∀ n : ℕ,
    completion.hom ≫
      ((sfClopenSiteInclusion U).sheafPushforwardContinuous _ _ _).map
        (limit.π (integralCoefficientSheafSystem l E T) (op n)) =
    limit.π (integralCoefficientSheafSystem l E U.toScheme) (op n) ≫ (finite n).hom
  /-- The finite identifications preserve the quotient transition maps. -/
  transition : ∀ n : ℕ,
    (finite (n + 1)).hom ≫
      ((sfClopenSiteInclusion U).sheafPushforwardContinuous _ _ _).map
        (integralCoefficientSheafTransition l E T n) =
    integralCoefficientSheafTransition l E U.toScheme n ≫ (finite n).hom
  /-- Ordinary completed-coefficient restriction is additive. -/
  [additive : (sfClopenModuleRestriction U _ _ completion).Additive]
  /-- It preserves kernels. -/
  [limits : PreservesFiniteLimits (sfClopenModuleRestriction U _ _ completion)]
  /-- It preserves cokernels. -/
  [colimits : PreservesFiniteColimits (sfClopenModuleRestriction U _ _ completion)]
  /-- Ordinary finite-coefficient restriction is additive. -/
  [finite_additive : ∀ n : ℕ, (sfClopenModuleRestriction U _ _ (finite n)).Additive]
  /-- Ordinary finite-coefficient restriction preserves kernels. -/
  [finite_limits : ∀ n : ℕ,
    PreservesFiniteLimits (sfClopenModuleRestriction U _ _ (finite n))]
  /-- Ordinary finite-coefficient restriction preserves cokernels. -/
  [finite_colimits : ∀ n : ℕ,
    PreservesFiniteColimits (sfClopenModuleRestriction U _ _ (finite n))]

/-- Standard localization on every localized ringed site used in the Tor test.
Source: Stacks 05RU (blueprint: lem-sf-clopen-lisse-complete-localization). -/
instance sfClopenSliceHasDerived (T : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{v}) (V : T.ProEt)
    [HasSheafify ((Scheme.ProEt.topology T).over V) AddCommGrpCat.{v}]
    [((Scheme.ProEt.topology T).over V).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    HasDerivedCategory (ringedSiteModules.{v} (R.over V)) :=
  HasDerivedCategory.standard _

attribute [instance] SfClopenCoefficientRestriction.additive
  SfClopenCoefficientRestriction.limits SfClopenCoefficientRestriction.colimits
  SfClopenCoefficientRestriction.finite_additive SfClopenCoefficientRestriction.finite_limits
  SfClopenCoefficientRestriction.finite_colimits

variable {l E}

/-- Ordinary restriction on the unbounded completed-coefficient derived category.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenDerivedRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) :
    DerivedCategory (scalarReductionSource l E T) ⥤
      DerivedCategory (scalarReductionSource l E U.toScheme) :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  letI := integralCoefficientAbSheafify.{t, u} U.toScheme
  letI := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    (sfClopenModuleRestriction.{t, max u (t + 1)} U
      (completedIntegralCoefficientSheafUnrestricted l E T)
      (completedIntegralCoefficientSheafUnrestricted l E U.toScheme) d.completion)
    d.additive d.limits d.colimits

/-- The same ordinary restriction on a finite quotient, including exponent one.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenFiniteDerivedRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ) :
    DerivedCategory (scalarReductionTarget l E T n) ⥤
      DerivedCategory (scalarReductionTarget l E U.toScheme n) :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  letI := integralCoefficientAbSheafify.{t, u} U.toScheme
  letI := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    (sfClopenModuleRestriction.{t, max u (t + 1)} U
      (integralCoefficientSheaf l E T n)
      (integralCoefficientSheaf l E U.toScheme n) (d.finite n))
    (d.finite_additive n) (d.finite_limits n) (d.finite_colimits n)

/-- Restrict cochain complexes degreewise, with the same scalar action as module restriction.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenComplexRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) :
    CochainComplex (scalarReductionSource l E T) ℤ ⥤
      CochainComplex (scalarReductionSource l E U.toScheme) ℤ :=
  letI := d.additive
  (sfClopenModuleRestriction U _ _ d.completion).mapHomologicalComplex (.up ℤ)

/-- The canonical comparison of termwise restriction with unbounded localization.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenLocalizationIso {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) :
    (sfClopenDerivedRestriction d).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((sfClopenComplexRestriction d).obj P) :=
  letI := d.additive
  letI := d.limits
  letI := d.colimits
  ((sfClopenModuleRestriction U _ _ d.completion).mapDerivedCategoryFactors).app P

/-- Finite-coefficient restriction on actual complexes.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenFiniteComplexRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ) :=
  letI := d.finite_additive n
  (sfClopenModuleRestriction U _ _ (d.finite n)).mapHomologicalComplex (.up ℤ)

/-- The canonical localization comparison for finite-coefficient restriction.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenFiniteLocalizationIso {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ)
    (P : CochainComplex (scalarReductionTarget l E T n) ℤ) :
    (sfClopenFiniteDerivedRestriction d n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((sfClopenFiniteComplexRestriction d n).obj P) :=
  letI := d.finite_additive n
  letI := d.finite_limits n
  letI := d.finite_colimits n
  ((sfClopenModuleRestriction U _ _ (d.finite n)).mapDerivedCategoryFactors).app P

/-- The existing derived scalar-extension counit, transported from homotopy objects
by the canonical quotient comparisons. On K-flat complexes it computes reduction.
Source: Stacks 06YY (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenReductionCounit (T : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) :
    (scalarReductionDerivedExtension l E T n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E T n P) :=
  (scalarReductionDerivedExtension l E T n).map
      ((DerivedCategory.quotientCompQhIso _).app P).inv ≫
    (scalarReductionCounit l E T n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((scalarReductionExtension l E T n).mapHomotopyCategoryFactors (.up ℤ)).app P).hom ≫
    ((DerivedCategory.quotientCompQhIso _).app
      (unrestrictedTowerFiniteComplex l E T n P)).hom

/-- Test the same Tor interval after ordinary localization at every site object.
Source: Stacks 08FZ, 00Y0 (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def SfResidueTorAmplitudeOnEveryObject (T : Scheme.{t})
    (K : DerivedCategory (scalarReductionTarget l E T 0)) (a b : ℤ) : Prop :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  ∀ V : T.ProEt,
    letI : HasDerivedCategory (ringedSiteModules.{max u (t + 1)}
        ((sheafCompose ((Scheme.ProEt.topology T).over V)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((integralCoefficientCommRingSheaf l E T 0).over V))) :=
      HasDerivedCategory.standard _
    HasRingedSiteTorAmplitudeOfUniverses.{t + 1, t, max u (t + 1)}
      ((integralCoefficientCommRingSheaf l E T 0).over V)
      ((ringedDerivedRestrictionGeneral.{t + 1, t, max u (t + 1), max u (t + 1)}
        (integralCoefficientSheaf l E T 0) V).obj K) a b

/-- The complete restriction assertions, with normalized comparisons on actual tensors.
All fields are conclusions of the main existence theorem, not assumptions on the input.
Source: Stacks 09C3, 06YY and 08TC
(blueprint: lem-sf-clopen-lisse-complete-localization). -/
structure SfClopenCompleteRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) where
  /-- The natural derived reduction comparison at every positive exponent. -/
  reduction : ∀ n : ℕ,
    scalarReductionDerivedExtension l E T n ⋙ sfClopenFiniteDerivedRestriction d n ≅
      sfClopenDerivedRestriction d ⋙ scalarReductionDerivedExtension l E U.toScheme n
  /-- The finite-coefficient termwise tensor comparison. -/
  finite_quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenFiniteComplexRestriction d n).obj (unrestrictedTowerFiniteComplex l E T n P) ≅
      unrestrictedTowerFiniteComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P)
  /-- Its normalization on sheafified pure tensors fixes this comparison. -/
  finite_quotient_tensor : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
      (n : ℕ) (q : ℤ) (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V))),
    (((finite_quotient P n).hom.f q).val.app (op V))
      (unrestrictedTowerTensorSection l E T n (P.X q)
        (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
    unrestrictedTowerTensorSection l E U.toScheme n
      (((sfClopenComplexRestriction d).obj P).X q) (op V) s x
  /-- The derived reduction is the comparison induced by these tensors and the counits. -/
  reduction_counit : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenFiniteDerivedRestriction d n).map (sfClopenReductionCounit T n P) ≫
        (sfClopenFiniteLocalizationIso d n (unrestrictedTowerFiniteComplex l E T n P)).hom ≫
        DerivedCategory.Q.map (finite_quotient P n).hom =
      (reduction n).hom.app (DerivedCategory.Q.obj P) ≫
        (scalarReductionDerivedExtension l E U.toScheme n).map
          (sfClopenLocalizationIso d P).hom ≫
        sfClopenReductionCounit U.toScheme n ((sfClopenComplexRestriction d).obj P)
  /-- Restriction of the actual termwise quotients, with their restricted scalar actions. -/
  quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenComplexRestriction d).obj (unrestrictedTowerComplex l E T n P) ≅
      unrestrictedTowerComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P)
  /-- The quotient comparison is the sectionwise pure-tensor comparison. -/
  quotient_tensor : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
      (n : ℕ) (q : ℤ) (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V))),
    (((quotient P n).hom.f q).val.app (op V))
      (unrestrictedTowerTensorSection l E T n (P.X q)
        (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
    unrestrictedTowerTensorSection l E U.toScheme n
      (((sfClopenComplexRestriction d).obj P).X q) (op V) s x
  /-- One isomorphism of towers retains every quotient transition. -/
  tower : ∀ P : CochainComplex (scalarReductionSource l E T) ℤ,
    canonicalIntegralReductionTower l E T P ⋙ sfClopenDerivedRestriction d ≅
      canonicalIntegralReductionTower l E U.toScheme ((sfClopenComplexRestriction d).obj P)
  /-- The tower comparison is induced by the preceding actual quotient comparisons. -/
  tower_quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (tower P).hom.app (op n) =
      (sfClopenLocalizationIso d (unrestrictedTowerComplex l E T n P)).hom ≫
        DerivedCategory.Q.map (quotient P n).hom
  /-- The canonical quotient projections agree under this tower isomorphism. -/
  tower_unit : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenDerivedRestriction d).map
        (DerivedCategory.Q.map (unrestrictedTowerUnit l E T P n)) ≫
      (tower P).hom.app (op n) =
    (sfClopenLocalizationIso d P).hom ≫
      DerivedCategory.Q.map
        (unrestrictedTowerUnit l E U.toScheme ((sfClopenComplexRestriction d).obj P) n)
  /-- Ordinary restriction preserves the canonically augmented Roos completeness condition. -/
  complete : ∀ M : DerivedCategory (scalarReductionSource l E T),
    IsDerivedCompleteUnrestricted l E T M →
      IsDerivedCompleteUnrestricted l E U.toScheme ((sfClopenDerivedRestriction d).obj M)
  /-- The bounds remain the same on every object of the component site. -/
  tor : ∀ (M : DerivedCategory (scalarReductionSource l E T)) (a b : ℤ),
    SfResidueTorAmplitudeOnEveryObject (l := l) (E := E) T
      ((scalarReductionDerivedExtension l E T 0).obj M) a b →
    SfResidueTorAmplitudeOnEveryObject (l := l) (E := E) U.toScheme
      ((scalarReductionDerivedExtension l E U.toScheme 0).obj
        ((sfClopenDerivedRestriction d).obj M)) a b

end WeilConjectures
