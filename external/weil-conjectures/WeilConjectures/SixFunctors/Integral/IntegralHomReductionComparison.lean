/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
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
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.SixFunctors.ScalarTensorTransport.ScalarTensorComparisonTransport
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization

/-! # The evaluation-defined integral Hom reduction comparison

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
`proposition-six-operations-change-coefficients--7`, order 2134; Stacks Project, Tags 08J7, 06YY and
0A90 (blueprint: def-sf-integral-hom-reduction-comparison).

Tensor models below are normalized on K-flat representatives. Their Hom adjunctions
are normalized by the actual Hom-complex evaluation. Thus the mate is the canonical
comparison, independently of the equivalent choices of models.

## Main definitions

- `HomReductionTensorModel`: tensor-Hom adjunction normalized on representatives.
- `IntegralHomReductionTensorData`: scalar tensor comparison with its counit square.
- `integralHomReductionComparison`: the transpose of reduced evaluation.

## Main statements

- `integralHomReductionTensorData_exists`: existence of the normalized models.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u d c v w r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace WeilConjectures

open SheafOfModules

/-- Locally bijective maps describe this same sheafification.
Source: Stacks 03DA (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable instance (priority := 2000) homReductionLocallyBijective
    (X : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

/-- The site is essentially small at this coefficient size.
Source: Stacks 098K (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable instance (priority := 2000) homReductionSmall
    (X : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} (AlgebraicGeometry.Scheme.ProEt X) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Module sheaves for a commutative coefficient sheaf on the small pro-etale site.
Source: Stacks 03DA (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable abbrev homReductionModules {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard localization of these module complexes.
Source: Stacks 05RU (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable instance homReductionDerived {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory (homReductionModules R) := HasDerivedCategory.standard _

/-- The recorded K-injective internal Hom, with the actual two site universes.
Source: Stacks 08J7 (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable abbrev homReductionHom {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  derivedInternalHomOfUniverses.{u + 1, u, u, u + 2} (AlgebraicGeometry.Scheme.ProEt.topology X) R

/-- The signed direct-sum total tensor on complexes; the tensor is the existing sheaf tensor.
Source: Stacks 0A90 (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable def homReductionTotal {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (homReductionModules R) ℤ) :
    CochainComplex (homReductionModules R) ℤ :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  CochainComplex.mapBifunctor P Q (curriedTensor _)

/-- The canonical map from the Hom complex to its derived internal Hom.
It is the Hom of the K-injective augmentation followed by the localization factorization.
Source: Stacks 08J7 (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable def homReductionHomUnit {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P I : CochainComplex (homReductionModules R) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := R) P I) ⟶
      (homReductionHom R).obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) :=
  letI : IsGrothendieckAbelian.{u + 1} (homReductionModules R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
      (AlgebraicGeometry.Scheme.ProEt.topology X) R).1
  let F : (CochainComplex (homReductionModules R) ℤ)ᵒᵖ ×
      CochainComplex (homReductionModules R) ℤ ⥤ DerivedCategory (homReductionModules R) :=
    (𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{u + 1} _) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        DerivedCategory.Q (C := homReductionModules R)
  let Qpair : (CochainComplex (homReductionModules R) ℤ)ᵒᵖ ×
      CochainComplex (homReductionModules R) ℤ ⥤
      (DerivedCategory (homReductionModules R))ᵒᵖ × DerivedCategory (homReductionModules R) :=
    (DerivedCategory.Q (C := homReductionModules R)).op.prod
      (DerivedCategory.Q (C := homReductionModules R))
  DerivedCategory.Q.map ((homComplexFunctor (R := R)).obj (op P) |>.map
    ((CochainComplex.toKInjectiveResolution.{u + 1} _).app I)) ≫
    (Localization.fac F
      (derivedInternalHomOfUniverses_inverts.{u + 1, u, u, u + 2} _ R _
        (CochainComplex.toKInjectiveResolution.{u + 1} _)
        (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1}
          _ M).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u + 1}
            _ M⟩)) Qpair).inv.app (op P, I)

/-- Inclusion of a pure tensor into the signed total tensor complex.
Source: Stacks 0A90 (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable def homReductionTensorElement {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (homReductionModules R) ℤ) (a b : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
    (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U) :
    ((homReductionTotal R P Q).X (a + b)).val.obj U :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  (CochainComplex.ιMapBifunctor P Q (curriedTensor _) a b (a + b) rfl).val.app U
    ((SheafOfModules.tensorObjIsoSheafification (R := R) (P.X a) (Q.X b)).inv.val.app U
      ((CategoryTheory.toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
        ((P.X a).val ⊗ (Q.X b).val).presheaf).app U (x ⊗ₜ[R.obj.obj U] y)))

/-- The recorded projection family, selected before specializing the site.
Source: Stacks 0A8X (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable def homReductionHomProjection
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) :=
  (CategoryTheory.homComplex_projections_exists.{c, v, w, r} (R := R)).choose

/-- The product projection of the recorded Hom complex.
Source: Stacks 0A8X (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable def homReductionProjection {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P I : CochainComplex (homReductionModules R) ℤ) (a b c : ℤ) (h : b + a = c) :
    (homComplex (R := R) P I).X a ⟶ SheafOfModules.homObj (R := R) (P.X b) (I.X c) :=
  homReductionHomProjection R P I a b c h

/-- Currying means the literal evaluation equation on every localized section and summand.
Source: Stacks 0A90 (blueprint: def-sf-integral-hom-reduction-comparison). -/
def IsHomReductionCurry {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P Q I : CochainComplex (homReductionModules R) ℤ)
    (f : homReductionTotal R P Q ⟶ I) (c : P ⟶ homComplex (R := R) Q I) : Prop :=
  ∀ (a b : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
    (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U),
    (f.f (a + b)).val.app U (homReductionTensorElement R P Q a b U x y) =
      ((homReductionProjection R Q I a b (a + b) (add_comm b a)).val.app U
        ((c.f a).val.app U x)).app (op (Over.mk (𝟙 U.unop))) y

/-- A model of derived tensor and its *normalized* adjunction to the recorded internal Hom.
The representative comparisons and the sectionwise currying equation determine all data
up to the unique compatible isomorphism; no arbitrary tensor or adjunction is admitted.
Source: Stacks 06YS, 0A90 and 08J7
(blueprint: def-sf-integral-hom-reduction-comparison). -/
structure HomReductionTensorModel {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}) where
  tensor : DerivedCategory (homReductionModules R) ×
    DerivedCategory (homReductionModules R) ⥤ DerivedCategory (homReductionModules R)
  compute : ∀ (P Q : CochainComplex (homReductionModules R) ℤ),
    CochainComplex.IsAcyclicTensorKFlat (R := R) P →
      CochainComplex.IsAcyclicTensorKFlat (R := R) Q →
    (DerivedCategory.Q.obj (homReductionTotal R P Q) ≅
      tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
  curry : ∀ K L M : DerivedCategory (homReductionModules R),
    (K ⟶ (homReductionHom R).obj (op L, M)) ≃ (tensor.obj (K, L) ⟶ M)
  natural : ∀ (K K' L L' M M' : DerivedCategory (homReductionModules R))
    (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
    (f : K ⟶ (homReductionHom R).obj (op L, M)),
    curry K' L' M' (a ≫ f ≫ (homReductionHom R).map (b.op, c)) =
      tensor.map (a, b) ≫ curry K L M f ≫ c
  cochain_curry : ∀ (P Q I : CochainComplex (homReductionModules R) ℤ)
    (f : homReductionTotal R P Q ⟶ I),
    ∃! c : P ⟶ homComplex (R := R) Q I, IsHomReductionCurry R P Q I f c
  normalize : ∀ (P Q I : CochainComplex (homReductionModules R) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P)
    (hQ : CochainComplex.IsAcyclicTensorKFlat (R := R) Q), I.IsKInjective →
    ∀ (f : homReductionTotal R P Q ⟶ I) (c : P ⟶ homComplex (R := R) Q I),
    IsHomReductionCurry R P Q I f c →
    curry (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
      (DerivedCategory.Q.map c ≫ homReductionHomUnit R Q I) =
        (compute P Q hP hQ).inv ≫ DerivedCategory.Q.map f

namespace HomReductionProof
set_option backward.isDefEq.respectTransparency.types false

private theorem closed_curry_natural {A : Type c} [Category.{v} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H)
    (K K' L L' M M' : A) (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
    (f : K ⟶ H.obj (op L, M)) :
    (S.transpose K' L' M').symm (a ≫ f ≫ H.map (b.op, c)) =
      S.tensor.map (a, b) ≫ (S.transpose K L M).symm f ≫ c := by
  let := S.monoidal
  have hh : H.map (b.op, c) =
      H.map (X := (op L, M)) (Y := (op L', M)) (b.op, 𝟙 M) ≫
        H.map (X := (op L', M)) (Y := (op L', M')) (𝟙 (op L'), c) := by
    rw [← H.map_comp]
    simp
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor]
  rw [hh]
  erw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (S.adjunction L').counit.naturality c
  change (tensorRight L').map (H.map (X := (op L', M)) (Y := (op L', M')) (𝟙 (op L'), c)) ≫
    (S.adjunction L').counit.app M' = (S.adjunction L').counit.app M ≫ c at hn
  erw [hn]
  erw [reassoc_of% (S.evaluation_naturality L L' M b)]
  change (a ▷ L') ≫ (f ▷ L') ≫ (H.obj (op L, M) ◁ b) ≫
    (S.adjunction L).counit.app M ≫ c =
      (a ⊗ₘ b) ≫ (f ▷ L) ≫ (S.adjunction L).counit.app M ≫ c
  simp only [← tensorHom_id, ← id_tensorHom, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem projection_eq {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (homReductionModules R) ℤ)
    (a b k : ℤ) (h : b + a = k) :
    homReductionProjection R P Q a b k h =
      coefficientHomComponent.{u, u + 1, u} _ R P Q a b k h := rfl

attribute [local irreducible] homComplexFunctor

private theorem generator_eq {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (homReductionModules R) ℤ)
    (a b : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
    (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U) :
    homReductionTensorElement R P Q a b U x y =
      coefficientTensorGenerator.{u, u + 1, u} _ R P Q a b (a + b) rfl U x y := rfl

private theorem curry_iff {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P Q I : CochainComplex (homReductionModules R) ℤ)
    (f : homReductionTotal R P Q ⟶ I) (g : P ⟶ homComplex (R := R) Q I) :
    IsHomReductionCurry R P Q I f g ↔
      IsCoefficientTensorCurry.{u, u + 1, u} _ R P Q I f g := by
  simp only [IsHomReductionCurry, IsCoefficientTensorCurry, coefficientHomSectionApply,
    generator_eq, projection_eq]
  with_unfolding_all rfl

private theorem unit_eq {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (Q I : CochainComplex (homReductionModules R) ℤ) :
    homReductionHomUnit R Q I =
      DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op Q)).map
          ((coefficientHomAugmentation.{u, u + 1, u} _ R).app I)) ≫
        (coefficientHomResolutionIso.{u, u + 1, u, u + 2} _ R Q I).inv := rfl

attribute [local irreducible] homReductionHomUnit homReductionProjection
  homReductionTensorElement

private noncomputable def model {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (S : CoefficientClosedStructure (homReductionHom R))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (AlgebraicGeometry.Scheme.ProEt.topology X) R S) : HomReductionTensorModel R where
  tensor := S.tensor
  compute P Q hP hQ := CoefficientTensorModels.iso.{u, u + 1, u, u + 2} _ R S T P Q hP hQ
  curry K L M := (S.transpose K L M).symm
  natural := closed_curry_natural S
  cochain_curry P Q I f := by
    obtain ⟨g, hg, hu⟩ :=
      coefficientCochainTensorCurry_exists.{u} _ R P Q I f
    exact ⟨g, (curry_iff R P Q I f g).2 hg,
      fun g' hg' ↦ hu g' ((curry_iff R P Q I f g').1 hg')⟩
  normalize P Q I hP hQ _ f g hg := by
    change (S.transpose _ _ _).symm (DerivedCategory.Q.map g ≫ _) = _
    rw [unit_eq]
    have h := coefficientTensorCurry_normalize.{u, u + 1, u, u + 2} _ R S T P Q I hP hQ f g
      ((curry_iff R P Q I f g).1 hg)
    erw [Functor.map_comp, Category.assoc] at h
    with_unfolding_all exact h

private theorem section_transport_cancel {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {P Q : SheafOfModules.{w} R} (h : P = Q) (U : Cᵒᵖ) (x : P.val.obj U) :
    (eqToHom h.symm).val.app U ((eqToHom h).val.app U x) = x := by
  cases h
  rfl

end HomReductionProof

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)

/-- Additivity at the fixed common coefficient size.
Source: Stacks 06YY (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable instance (priority := 2000) homReductionExtensionAdditive :
    (integralReductionChangeOfRings l E X D hl n).Additive :=
  integralReductionChangeOfRingsAdditive.{d, u, u} l E X D hl n

/-- The same scalar extension preserves zero morphisms.
Source: Stacks 06YY (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable instance (priority := 2000) homReductionExtensionZero :
    (integralReductionChangeOfRings l E X D hl n).PreservesZeroMorphisms :=
  inferInstance

/-- The left-derived counit transported from homotopy complexes to the complex localization.
Source: Stacks 06YY (blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable def homReductionComplexComparison
    (P : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ) :
    (integralDerivedReduction l E X D hl n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (integralDerivedReduction l E X D hl n).map
      ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (integralDerivedReductionCounit l E X D hl n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((integralReductionChangeOfRings l E X D hl n).mapHomotopyCategoryFactors (.up ℤ)).hom.app
        P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)

/-- Normalized tensor-Hom models and scalar tensor comparison for the actual projection.
The unit is `m ↦ 1 ⊗ m`. The total comparison is specified on these generating sections.
Its derived comparison is specified on all pairs of K-flat representatives by the counit
square. The source and target currying are specified by literal Hom-complex evaluation.
Source: Stacks 03EK, 06YY, 0A90, 08J7; blueprint order 2134
(blueprint: def-sf-integral-hom-reduction-comparison). -/
structure IntegralHomReductionTensorData where
  source : HomReductionTensorModel (completedIntegralCommRingSheaf l E X D hl)
  target : HomReductionTensorModel (integralCoefficientCommRingSheaf l E X n)
  scalarUnit : 𝟭 (completedIntegralModuleSheaves l E X D hl) ⟶
    integralReductionChangeOfRings l E X D hl n ⋙ completedIntegralRestrictScalars l E X D hl n
  scalarUnit_normalize : ∀ (M : completedIntegralModuleSheaves l E X D hl)
    (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ) (x : M.val.obj U),
    (scalarUnit.app M).val.app U x =
      integralTowerTensorSection l E X D hl n M U 1 x
  total : ∀ P Q : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ,
    ((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj
      (homReductionTotal (completedIntegralCommRingSheaf l E X D hl) P Q) ⟶
    homReductionTotal (integralCoefficientCommRingSheaf l E X n)
      (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)
      (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj Q)
  total_normalize : ∀ (P Q : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
    (a b : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
    (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U),
    ((total P Q).f (a + b)).val.app U
      ((scalarUnit.app
        ((homReductionTotal (completedIntegralCommRingSheaf l E X D hl) P Q).X (a + b))).val.app U
          (homReductionTensorElement (completedIntegralCommRingSheaf l E X D hl) P Q a b U x y)) =
      homReductionTensorElement (integralCoefficientCommRingSheaf l E X n)
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj Q)
        a b U ((scalarUnit.app (P.X a)).val.app U x) ((scalarUnit.app (Q.X b)).val.app U y)
  extension_flat : ∀ P : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (R := completedIntegralCommRingSheaf l E X D hl) P →
      CochainComplex.IsAcyclicTensorKFlat (R := integralCoefficientCommRingSheaf l E X n)
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)
  tensor : source.tensor ⋙ integralDerivedReduction l E X D hl n ≅
    ((integralDerivedReduction l E X D hl n).prod
      (integralDerivedReduction l E X D hl n)) ⋙ target.tensor
  normalize : ∀ (P Q : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedIntegralCommRingSheaf l E X D hl) P)
    (hQ : CochainComplex.IsAcyclicTensorKFlat (R := completedIntegralCommRingSheaf l E X D hl) Q),
    (integralDerivedReduction l E X D hl n).map (source.compute P Q hP hQ).hom ≫
        tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          target.tensor.map
            (X := ((integralDerivedReduction l E X D hl n).obj (DerivedCategory.Q.obj P),
              (integralDerivedReduction l E X D hl n).obj (DerivedCategory.Q.obj Q)))
            (Y := (DerivedCategory.Q.obj
              (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P),
              DerivedCategory.Q.obj
              (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex
                (.up ℤ)).obj Q)))
            (homReductionComplexComparison D l hl E X n P,
              homReductionComplexComparison D l hl E X n Q) =
      homReductionComplexComparison D l hl E X n
        (homReductionTotal (completedIntegralCommRingSheaf l E X D hl) P Q) ≫
        DerivedCategory.Q.map (total P Q) ≫
          (target.compute
            (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)
            (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj Q)
            (extension_flat P hP) (extension_flat Q hQ)).hom

attribute [local irreducible] CoefficientClosedStructure.tensor CoefficientTensorModels.iso

private theorem homReductionComplexComparison_eq_scalar
    (P : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ) :
    homReductionComplexComparison D l hl E X n P =
      scalarPairComplexComparison.{u + 1, u, u + 1, u + 2}
        (J := AlgebraicGeometry.Scheme.ProEt.topology X)
        (R := completedIntegralCommRingSheaf l E X D hl)
        (S := integralCoefficientCommRingSheaf l E X n)
        (integralReductionChangeOfRings l E X D hl n)
        (homReductionExtensionAdditive D l hl E X n)
        (integralDerivedReduction l E X D hl n)
        (integralDerivedReductionCounit l E X D hl n) P := by
  simp only [homReductionComplexComparison, scalarPairComplexComparison,
    Functor.mapHomotopyCategoryFactors, CategoryTheory.Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id
    (DerivedCategory.Qh (C := SheafOfModules.{u + 1} (integralCoefficientSheaf l E X n))),
    Category.id_comp]
  all_goals with_unfolding_all rfl

/-- Existence of the normalized universal models defining the comparison.
This does not assert invertibility of the Hom comparison. The tensor, its representative
comparisons, currying, scalar unit, total comparison and derived tensor comparison are
fixed up to their unique compatible isomorphisms by the displayed universal properties
and normalization equations, so selecting this witness does not select an arbitrary map.
Source: Stacks 06YS, 06YY, 0A90, 08J7; blueprint order 2134
(blueprint: def-sf-integral-hom-reduction-comparison).
Proof:
1. Resolve both tensor factors by K-flat complexes. Tensoring quasi-isomorphisms between
K-flat complexes preserves quasi-isomorphisms, by applying K-flatness to their acyclic
cones. Localize this total tensor bifunctor, retaining its representative comparisons.
2. Resolve the Hom target by a K-injective complex. Sectionwise currying on every slice
is exactly the displayed evaluation equation. It respects the total and Hom differentials;
localization gives the adjunction and its normalization. K-flat resolutions and K-injective
resolutions show that these normalized data are unique up to compatible isomorphism.
3. Ordinary scalar extension has unit 1 tensor m. Its tensor comparison sends the image
of x tensor y to the tensor of their two unit images. These generating-section formulas
respect restrictions, balancing and differentials, so sheafification and totalization
supply scalarUnit and total. The balanced tensor associativity proves extension_flat.
4. Apply the universal property of the left-derived reduction in both K-flat variables.
The counit square in normalize defines the resulting tensor comparison uniquely.
The ordinary tensor comparison and its inverse are isomorphisms, so their descended
comparisons are inverse. This proves existence of the stated normalized models. -/
theorem integralHomReductionTensorData_exists :
    Nonempty (IntegralHomReductionTensorData D l hl E X n) := by
  classical
  let J := AlgebraicGeometry.Scheme.ProEt.topology X
  let a := completedIntegralCommRingProjection l E X D hl n
  let : ∀ R : Sheaf J CommRingCat.{u + 1},
      HasDerivedCategory.{u + 2} (SheafOfModules.scalarModules J R) :=
    fun R ↦ homReductionDerived R
  obtain ⟨M, μ, _⟩ := scalarInternalHomAdjunction_exists.{u + 1, u, u, u + 2} (J := J)
  let hobj := (integralReductionExistence l E X D hl n).choose_spec.choose
  have he := ScalarTensorTransport.extension_eq.{u + 1, u, u, u + 2} J a
    (M.scalar a) (integralReductionChangeOfRings l E X D hl n) hobj
    (integralReductionExistence l E X D hl n).choose_spec.choose_spec.choose
  obtain ⟨t⟩ := ScalarTensorTransport.fixedScalarTensorComparison_exists.{u + 1, u, u, u + 2}
    J a M (μ a) (integralReductionChangeOfRings l E X D hl n)
    (homReductionExtensionAdditive D l hl E X n) hobj he
    (integralDerivedReduction l E X D hl n) (integralDerivedReductionCounit l E X D hl n)
    (by with_unfolding_all exact integralDerivedReductionUniversal l E X D hl n)
  refine ⟨{
    source := HomReductionProof.model _ (M.closed _) (M.model _)
    target := HomReductionProof.model _ (M.closed _) (M.model _)
    scalarUnit := t.unit
    scalarUnit_normalize := ?_
    total := fun P Q ↦ (t.complexIso P Q).hom
    total_normalize := ?_
    extension_flat := t.preservesKFlat
    tensor := t.iso
    normalize := ?_ }⟩
  · intro P U x
    have h := t.unit_normalize P U x
    apply_fun (fun z ↦ (eqToHom (hobj P).symm).val.app U z) at h
    have hc := HomReductionProof.section_transport_cancel (hobj P) U
      ((t.unit.app P).val.app U x)
    with_unfolding_all exact hc.symm.trans h
  · intro P Q a b U x y
    exact t.generators P Q a b (a + b) rfl U x y
  · intro P Q hp hq
    simp only [homReductionComplexComparison_eq_scalar]
    have h := t.normalization P Q hp hq
    with_unfolding_all exact h

/-- The canonical comparison is the transpose of reduced evaluation, using the inverse
canonical tensor comparison. The defining model is fixed by its universal properties
and its sectionwise and K-flat normalizations, not by an unconstrained isomorphism.
Source: blueprint order 2134; Stacks 08J7 and 06YY
(blueprint: def-sf-integral-hom-reduction-comparison). -/
noncomputable def integralHomReductionComparison
    (K L : completedIntegralDerivedCategory l E X D hl) :
    (integralDerivedReduction l E X D hl n).obj
        ((homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)) ⟶
      (homReductionHom (integralCoefficientCommRingSheaf l E X n)).obj
        (op ((integralDerivedReduction l E X D hl n).obj K),
          (integralDerivedReduction l E X D hl n).obj L) :=
  let m := (integralHomReductionTensorData_exists D l hl E X n).some
  (m.target.curry
    ((integralDerivedReduction l E X D hl n).obj
      ((homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)))
    ((integralDerivedReduction l E X D hl n).obj K)
    ((integralDerivedReduction l E X D hl n).obj L)).symm
    (m.tensor.inv.app
        ((homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L), K) ≫
      (integralDerivedReduction l E X D hl n).map
        (m.source.curry
          ((homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L))
          K L (𝟙 _)))

end WeilConjectures
