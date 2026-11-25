/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
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
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
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
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import Mathlib.Data.List.TFAE
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
import WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import WeilConjectures.SmoothPurity.Integral.IntegralPrincipalConeQuotientComparison
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence

/-! # Roos and intrinsic completeness for completed local-field coefficients

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul,
and Tag 099B, lemma-derived-completion
(blueprint: lem-pur-roos-intrinsic-completeness-equivalence).

All five conditions concern the completed integral ring on the actual small pro-etale
site. A section on U is equivalently a global section on the slice over U. Membership
in the ideal sheaf tR is expressed by local divisibility on a covering sieve; thus the
second condition tests every section of the sheaf ideal, not only the constant t.
The representative is K-flat with flat terms. The three displayed units retain their
specified quotient, degree-zero Koszul, and explicit (u,0) normalizations.
The integral one-generator chain models and their normalized units are defined here;
the proof uses these concrete integral models throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

section IntegralKoszulModels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})

/-- The uniformizer section, through the actual constant-to-limit map.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralCompletionScalarValue (U : T.ProEtᵒᵖ) :
    (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U :=
  (integralConstantToCompletionOfUniverses l E T).hom.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
          (ULift.up (Padic.coefficientExtensionUniformizer l E)))

/-- Multiplication by the actual uniformizer determines a unique chain endomorphism.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: the constant-to-limit map is natural, so its uniformizer sections restrict
compatibly. Scalar multiplication is linear over the commutative coefficient ring,
commutes with restrictions, and commutes with the linear differential. These formulas
define a chain map; equality on every section in every degree proves uniqueness. -/
theorem integralKoszulScalar_existsUnique (P : IntegralOnSlice.Cx l E T none) :
    ∃! f : P ⟶ P, ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (f.f q).val.app U x = integralCompletionScalarValue l E T U • x := by
  have hs {U V : T.ProEtᵒᵖ} (g : U ⟶ V) :
      (completedIntegralCoefficientSheafUnrestricted l E T).obj.map g
          (integralCompletionScalarValue l E T U) =
        integralCompletionScalarValue l E T V := by
    let α := Functor.whiskerRight
      (toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))))
      (forget₂ CommRingCat RingCat) ≫
      (integralConstantToCompletionOfUniverses l E T).hom
    exact (CategoryTheory.congr_fun (α.naturality g)
      (ULift.up (Padic.coefficientExtensionUniformizer l E))).symm
  let f : P ⟶ P :=
    { f := fun q ↦
        { val :=
            { app := fun U ↦ ModuleCat.ofHom
                { toFun := fun x ↦ integralCompletionScalarValue l E T U • x
                  map_add' := fun x y ↦ smul_add _ x y
                  map_smul' := fun a x ↦ by
                    let : CommRing ((IntegralOnSlice.rings l E T none).obj.obj U) :=
                      inferInstanceAs (CommRing ((IntegralOnSlice.ring l E T none).obj.obj U))
                    change (integralCompletionScalarValue l E T U :
                      (IntegralOnSlice.rings l E T none).obj.obj U) • (a • x) =
                        a • ((integralCompletionScalarValue l E T U :
                          (IntegralOnSlice.rings l E T none).obj.obj U) • x)
                    let z : (IntegralOnSlice.rings l E T none).obj.obj U :=
                      integralCompletionScalarValue l E T U
                    change z • (a • x) = a • (z • x)
                    rw [← mul_smul, ← mul_smul, mul_comm z a] }
              naturality := by
                intro U V g
                ext x
                change integralCompletionScalarValue l E T V • (P.X q).val.map g x =
                  (P.X q).val.map g (integralCompletionScalarValue l E T U • x)
                rw [PresheafOfModules.map_smul]
                rw [show (IntegralOnSlice.rings l E T none).obj.map g
                    (integralCompletionScalarValue l E T U) =
                    integralCompletionScalarValue l E T V from hs g] } }
      comm' := by
        intro i j _hij
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        ext x
        exact ((P.d i j).val.app U).hom.map_smul
          (integralCompletionScalarValue l E T U) x }
  refine ⟨f, ?_, ?_⟩
  · intro q U x
    rfl
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro q
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact hg q U x

/-- The uniquely section-normalized scalar chain map.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulScalar (P : IntegralOnSlice.Cx l E T none) : End P :=
  .of (integralKoszulScalar_existsUnique l E T P).exists.choose

/-- P tensor [R --t^(n+1)--> R], in the standard total-cone coordinates.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulLevel (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :=
  CochainComplex.mappingCone (integralKoszulScalar l E T P ^ (n + 1)).asHom

/-- The square defining the (t,1) transition commutes.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: compose the indicated powers of the same endomorphism. Both sides are its
(n+2)-nd power, by the power recursion and the identity composition law. -/
theorem integralKoszulStep_square (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :
    (integralKoszulScalar l E T P ^ (n + 1 + 1)).asHom ≫ 𝟙 P =
      (integralKoszulScalar l E T P).asHom ≫ (integralKoszulScalar l E T P ^ (n + 1)).asHom := by
  exact CochainComplex.PrincipalCone.square (integralKoszulScalar l E T P) n

/-- The specified transition, multiplication by t in degree -1 and identity in degree 0.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulStep (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :
    integralKoszulLevel l E T P (n + 1) ⟶ integralKoszulLevel l E T P n :=
  CochainComplex.mappingCone.map _ _ (integralKoszulScalar l E T P).asHom (𝟙 P)
    (integralKoszulStep_square l E T P n)

/-- The strict positive-power Koszul tensor tower on this single representative.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulTower (P : IntegralOnSlice.Cx l E T none) :
    ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E T none :=
  Functor.ofOpSequence (integralKoszulStep l E T P)

/-- The product of the degree-zero inclusions.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulProductUnit (P : IntegralOnSlice.Cx l E T none) :
    P ⟶ ∏ᶜ (fun n : ℕ ↦ (integralKoszulTower l E T P).obj (op n)) :=
  Pi.lift (fun n ↦ CochainComplex.mappingCone.inr
    (integralKoszulScalar l E T P ^ (n + 1)).asHom)

/-- The specified one-minus-transition map on the termwise product.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulOneSubShift (P : IntegralOnSlice.Cx l E T none) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ (integralKoszulTower l E T P).obj (op n))
    (integralKoszulStep l E T P)

private theorem integralKoszulProductUnit_comp (P : IntegralOnSlice.Cx l E T none) :
    integralKoszulProductUnit l E T P ≫ integralKoszulOneSubShift l E T P = 0 := by
  exact CochainComplex.PrincipalCone.productUnit_comp (integralKoszulScalar l E T P)

/-- The explicit fiber has differential (dx,(1-s)x-dy), as in the owning node.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulIntrinsicFiber (P : IntegralOnSlice.Cx l E T none) :=
  CochainComplex.mappingCocone (-integralKoszulOneSubShift l E T P)

/-- Zero is the specified second cochain in the intrinsic augmentation.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: each component of u(1-s) is the difference of consecutive compatible cone
inclusions, so is zero. The differential of the zero cochain is zero. -/
theorem integralKoszulIntrinsicUnit_condition (P : IntegralOnSlice.Cx l E T none) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ (integralKoszulTower l E T P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (integralKoszulProductUnit l E T P ≫ (-integralKoszulOneSubShift l E T P)) = 0 := by
  simp [Preadditive.comp_neg, integralKoszulProductUnit_comp]

/-- The actual (u,0) chain map into the signed intrinsic fiber.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulIntrinsicUnitComplex (P : IntegralOnSlice.Cx l E T none) :
    P ⟶ integralKoszulIntrinsicFiber l E T P :=
  CochainComplex.mappingCocone.lift _ (integralKoszulProductUnit l E T P) 0
    (integralKoszulIntrinsicUnit_condition l E T P)

/-- The intrinsic unit on K, realized using the specified representative isomorphism.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulIntrinsicUnit (K : IntegralOnSlice.D l E T none)
    (P : IntegralOnSlice.Cx l E T none) (e : DerivedCategory.Q.obj P ≅ K) :
    K ⟶ DerivedCategory.Q.obj (integralKoszulIntrinsicFiber l E T P) :=
  e.inv ≫ DerivedCategory.Q.map (integralKoszulIntrinsicUnitComplex l E T P)

/-- The total derived inverse limit of the Koszul tensor tower, in the exact-products model.
Source: Stacks 0A0E and 0941 (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulLimit (P : IntegralOnSlice.Cx l E T none) :=
  CochainComplex.mappingCocone (integralKoszulOneSubShift l E T P)

/-- The zero cochain gives the strict Koszul augmentation into the Roos fiber.
Source: Stacks 0A0E and 0941 (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: evaluate u(1-s) at every product projection. It is the difference of the
two cone inclusions identified by integralKoszulUnit_compatible. Thus it vanishes;
the differential of the zero cochain also vanishes. -/
theorem integralKoszulLimitUnit_condition (P : IntegralOnSlice.Cx l E T none) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ (integralKoszulTower l E T P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (integralKoszulProductUnit l E T P ≫ integralKoszulOneSubShift l E T P) = 0 := by
  simp [integralKoszulProductUnit_comp]

/-- The degree-zero Koszul unit into its total strict derived inverse limit.
Source: Stacks 0A0E and 0941 (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulLimitUnitComplex (P : IntegralOnSlice.Cx l E T none) :
    P ⟶ integralKoszulLimit l E T P :=
  CochainComplex.mappingCocone.lift _ (integralKoszulProductUnit l E T P) 0
    (integralKoszulLimitUnit_condition l E T P)

/-- The specified Koszul unit on the object represented by P.
Source: Stacks 0A0E and 0941 (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulLimitUnit (K : IntegralOnSlice.D l E T none)
    (P : IntegralOnSlice.Cx l E T none) (e : DerivedCategory.Q.obj P ≅ K) :
    K ⟶ DerivedCategory.Q.obj (integralKoszulLimit l E T P) :=
  e.inv ≫ DerivedCategory.Q.map (integralKoszulLimitUnitComplex l E T P)

end IntegralKoszulModels

/-- The local test object is exactly RHom(R_U[1/s], K restricted to U).
The slice sheafification and standard localization are the existing canonical ones;
they impose no equality between the site object, morphism and coefficient universes.
Source: Stacks 0999 and 0A0E
(blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
noncomputable def integralCompletionLocalTest
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : AlgebraicGeometry.Scheme.{t}) (K : IntegralOnSlice.D l E T none)
    (U : T.ProEt)
    (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections) :
    IntegralOnSlice.D l E T (some U) :=
  letI : HasSheafify (IntegralOnSlice.topology T (some U))
      CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  letI := HasDerivedCategory.standard
    (SheafOfModules.{max u (t + 1)} ((IntegralOnSlice.rings l E T none).over U))
  (IntegralOnSlice.hom l E T (some U)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalizationOfUniverses (IntegralOnSlice.ring l E T (some U)) s)),
      ringedSiteDerivedRestrictionOfUniverses (IntegralOnSlice.rings l E T none) U K)

section CompletionProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})

private def localizationRepresentativeIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory A} (e : K ≅ L) :
    DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K)) ≅
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage L)) :=
  (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
    F.mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso K ≪≫ e ≪≫
        (DerivedCategory.Q.objObjPreimageIso L).symm) ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage L)

attribute [local irreducible] localizationRepresentativeIso

private def integralCompletionLocalTest_iso
    {K L : IntegralOnSlice.D l E T none} (e : K ≅ L) (U : T.ProEt)
    (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections) :
    integralCompletionLocalTest l E T K U s ≅ integralCompletionLocalTest l E T L U s := by
  letI : HasSheafify (IntegralOnSlice.topology T (some U))
      CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  letI := HasDerivedCategory.standard
    (SheafOfModules.{max u (t + 1)} ((IntegralOnSlice.rings l E T none).over U))
  let F := SheafOfModules.overFunctor.{max u (t + 1)}
    (IntegralOnSlice.rings l E T none) U
  letI : F.Additive := inferInstance
  letI : PreservesFiniteLimits F :=
    (SheafOfModules.overFunctor_exact_ofUniverses (IntegralOnSlice.rings l E T none) U).1
  letI : PreservesFiniteColimits F :=
    (SheafOfModules.overFunctor_exact_ofUniverses (IntegralOnSlice.rings l E T none) U).2
  let er := localizationRepresentativeIso F e
  exact (IntegralOnSlice.hom l E T (some U)).mapIso (Iso.prod (Iso.refl _) er)

attribute [local irreducible] integralCompletionLocalTest_iso

private theorem integralLocallyComplete_iso
    (σ : ∀ U : T.ProEtᵒᵖ, (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    {K L : IntegralOnSlice.D l E T none} (e : K ≅ L)
    (h : IntegralPrincipalCone.locallyComplete l E T σ K) :
    IntegralPrincipalCone.locallyComplete l E T σ L := by
  intro U s hs
  exact (integralCompletionLocalTest_iso l E T e U s).isZero_iff.mp (h U s hs)

private theorem integralScalar_natural {U V : T.ProEtᵒᵖ} (g : U ⟶ V) :
    (completedIntegralCoefficientSheafUnrestricted l E T).obj.map g
        (integralCompletionScalarValue l E T U) = integralCompletionScalarValue l E T V := by
  let α := Functor.whiskerRight
    (toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))))
    (forget₂ CommRingCat RingCat) ≫ (integralConstantToCompletionOfUniverses l E T).hom
  exact (CategoryTheory.congr_fun (α.naturality g)
    (ULift.up (Padic.coefficientExtensionUniformizer l E))).symm

private theorem signedFiberUnit {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {P B : CochainComplex A ℤ} (f : B ⟶ B)
    (a : P ⟶ B) (ha : a ≫ f = 0)
    (hpos : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P B (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (a ≫ f) = 0)
    (hneg : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P B (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (a ≫ (-f)) = 0) :
    IsIso (DerivedCategory.Q.map (CochainComplex.mappingCocone.lift f a 0 hpos)) ↔
      IsIso (DerivedCategory.Q.map (CochainComplex.mappingCocone.lift (-f) a 0 hneg)) := by
  let c := CochainComplex.mappingCone.map (-f) f (𝟙 B) (-𝟙 B) (by simp)
  let c' := CochainComplex.mappingCone.map f (-f) (𝟙 B) (-𝟙 B) (by simp)
  have hc : c ≫ c' = 𝟙 _ := by
    dsimp only [c, c']
    rw [← CochainComplex.mappingCone.map_comp]
    simpa using CochainComplex.mappingCone.map_id (-f)
  have hc' : c' ≫ c = 𝟙 _ := by
    dsimp only [c, c']
    rw [← CochainComplex.mappingCone.map_comp]
    simpa using CochainComplex.mappingCone.map_id f
  let e : CochainComplex.mappingCocone (-f) ≅ CochainComplex.mappingCocone f :=
    (shiftFunctor _ (-1 : ℤ)).mapIso ⟨c, c', hc, hc'⟩
  have hu : CochainComplex.mappingCocone.lift (-f) a 0 hneg ≫ e.hom =
      CochainComplex.mappingCocone.lift f a 0 hpos := by
    simpa only [e, c, Functor.mapIso_hom, Category.id_comp, Category.comp_id] using
      (completedCoconeLift_natural A (-f) f (𝟙 B) (-𝟙 B) (by simp)
        (𝟙 P) a a (by simp [ha]) ha (by simp)).symm
  have huQ := congrArg DerivedCategory.Q.map hu
  rw [Functor.map_comp] at huQ
  rw [← huQ]
  exact ⟨fun h ↦ by
    have := h
    exact IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map e.hom), fun h ↦ by
      have := h
      infer_instance⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The strict mapping-cocone model has the actual localized projections.
Source: Stacks Tag 08TC. Exact products identify both product vertices; mapping the
mapping-cocone triangle and transporting those vertices gives the required triangle. -/
private theorem integralStrictRoosTriangle {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasCountableProducts A] [CountableAB4Star A]
    [HasCountableProducts (DerivedCategory A)]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    ∃ δ, IsDerivedLimitTriangle
      (K := fun n ↦ DerivedCategory.Q.obj (C.obj (op n)))
      (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
      (DerivedCategory.Q.obj (integralOperationsRoos C))
      (Pi.lift (fun n ↦ DerivedCategory.Q.map
        (CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
            (integralOperationsTowerStep C)) ≫
            Pi.π (fun n ↦ C.obj (op n)) n))) δ := by
  dsimp only [integralOperationsRoos]
  let Q := DerivedCategory.Q (C := A)
  let P := fun n ↦ C.obj (op n)
  let D := fun n ↦ Q.obj (P n)
  obtain ⟨_, hp, _⟩ := derivedCategory_countableProducts_core.{0} A
  obtain ⟨hlim⟩ := hp ℕ P
  let : PreservesLimit (Discrete.functor P) Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) hlim
  let e : Q.obj (∏ᶜ P) ≅ ∏ᶜ D := PreservesProduct.iso Q P
  have he (n : ℕ) : e.hom ≫ Pi.π D n = Q.map (Pi.π P n) := by
    exact piComparison_comp_π Q P n
  dsimp only [D] at he
  let t := towerTransitionEndomorphism (K := P) (integralOperationsTowerStep C)
  have hmid : Q.map t ≫ e.hom = e.hom ≫
      towerTransitionEndomorphism (K := D)
        (fun n ↦ Q.map (integralOperationsTowerStep C n)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he, ← Q.map_comp]
    rw [(towerTransitionEndomorphism_eq_iff (K := P) (integralOperationsTowerStep C) t).mp rfl n]
    simp only [Functor.map_sub, Functor.map_comp]
    rw [Category.assoc, (towerTransitionEndomorphism_eq_iff (K := D)
      (fun n ↦ Q.map (integralOperationsTowerStep C n)) _).mp rfl n]
    simp only [Preadditive.comp_sub, ← Category.assoc, D, he]
  let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle t)
  refine ⟨e.inv ≫ T.mor₃, ?_⟩
  apply Pretriangulated.isomorphic_distinguished T
    (DerivedCategory.mappingCocone_triangle_distinguished t)
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · change (Pi.lift (fun n ↦ Q.map
        (CochainComplex.mappingCocone.fst t ≫ Pi.π P n))) ≫ e.inv =
      𝟙 _ ≫ Q.map (CochainComplex.mappingCocone.fst t)
    rw [Category.id_comp]
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, Pi.lift_comp_π, Functor.map_comp]
  · change towerTransitionEndomorphism (fun n ↦ Q.map (integralOperationsTowerStep C n)) ≫
      e.inv = e.inv ≫ Q.map t
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hmid]
    simp only [Iso.inv_hom_id_assoc]
  · change (e.inv ≫ T.mor₃) ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = e.inv ≫ T.mor₃
    rw [(shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id T.obj₁, Category.comp_id]

private theorem integralRoosIso {C : Type*} [Category* C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {X : ℕ → C} [HasProduct X]
    (f : ∀ n, X (n + 1) ⟶ X n) {K L : C}
    (p : K ⟶ ∏ᶜ X) (q : L ⟶ ∏ᶜ X)
    (δ : ∏ᶜ X ⟶ K⟦(1 : ℤ)⟧) (ε : ∏ᶜ X ⟶ L⟦(1 : ℤ)⟧)
    (hp : IsDerivedLimitTriangle f K p δ) (hq : IsDerivedLimitTriangle f L q ε) :
    Nonempty (K ≅ L) := by
  let T := Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ
  let S := Pretriangulated.Triangle.mk q (towerTransitionEndomorphism f) ε
  let e := Pretriangulated.isoTriangleOfIso₁₂ T.rotate S.rotate
    ((Pretriangulated.rotate_distinguished_triangle _).mp hp)
    ((Pretriangulated.rotate_distinguished_triangle _).mp hq)
    (Iso.refl _) (Iso.refl _) (by simp [T, S])
  exact ⟨(shiftFunctor C (1 : ℤ)).preimageIso (Pretriangulated.Triangle.π₃.mapIso e)⟩

private theorem integralRoosTransport {C : Type*} [Category* C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {X : ℕ → C} [HasProduct X]
    (f : ∀ n, X (n + 1) ⟶ X n) {K L : C} (e : K ≅ L)
    (q : L ⟶ ∏ᶜ X) (δ : ∏ᶜ X ⟶ L⟦(1 : ℤ)⟧)
    (hq : IsDerivedLimitTriangle f L q δ) :
    IsDerivedLimitTriangle f K (e.hom ≫ q) (δ ≫ e.inv⟦(1 : ℤ)⟧') := by
  apply Pretriangulated.isomorphic_distinguished _ hq _
  refine Pretriangulated.Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp
  · simp
  · simp [← Functor.map_comp]

private theorem integralGlobalUnit (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :
    ((IntegralOnSlice.augmentation l E T none).app P).app (op n) =
      unrestrictedTowerUnit l E T P n := by
  ext i U x
  exact ((IntegralOnSlice.augmentation_existsUnique l E T none).exists.choose_spec
    P n i U x).trans (unrestrictedTowerUnit_condition l E T P n i U x).symm

private theorem integralQuotientLocallyComplete
    (P : IntegralOnSlice.Cx l E T none)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := IntegralOnSlice.ring l E T none) P) :
    IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T)
      (DerivedCategory.Q.obj
        (integralOperationsRoos ((IntegralOnSlice.tower l E T none).obj P))) := by
  have hμ := (integralKoszulScalar_existsUnique l E T P).exists.choose_spec
  have hlocal := (IntegralPrincipalCone.localCriterion l E T
    (integralCompletionScalarValue l E T) (integralScalar_natural l E T)
    P (integralKoszulScalar l E T P) hμ (DerivedCategory.Q.obj P) (Iso.refl _)).1
  obtain ⟨c, _⟩ := integralPrincipalConeQuotientComparison l E T P hP
    (integralKoszulScalar l E T P) hμ
  exact integralLocallyComplete_iso l E T _ c hlocal

private theorem evaluatedSequence {A B : Type*} [Category* A] [Category* B]
    (X : ℕ → A ⥤ B) (f : ∀ n, X (n + 1) ⟶ X n) (a : A) :
    (Functor.ofOpSequence f).flip.obj a =
      Functor.ofOpSequence (X := fun n ↦ (X n).obj a) (fun n ↦ (f n).app a) := by
  let F := (Functor.ofOpSequence f).flip.obj a
  let G := Functor.ofOpSequence (X := fun n ↦ (X n).obj a) (fun n ↦ (f n).app a)
  let α : F ⟶ G := NatTrans.ofOpSequence (fun n ↦ 𝟙 (G.obj (op n))) (by
    intro n
    change (((Functor.ofOpSequence f).map (homOfLE n.le_succ).op).app a) ≫ 𝟙 _ =
      𝟙 _ ≫ G.map (homOfLE n.le_succ).op
    simp only [Functor.ofOpSequence_map_homOfLE_succ, G,
      Category.id_comp, Category.comp_id])
  have (n : ℕᵒᵖ) : IsIso (α.app n) := by
    change IsIso (𝟙 _)
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact Functor.ext_of_iso (asIso α) (fun _ ↦ rfl) (fun _ ↦ rfl)

private theorem integralGlobalTower
    (P : IntegralOnSlice.Cx l E T none) :
    (IntegralOnSlice.tower l E T none).obj P =
      Functor.ofOpSequence (X := fun n ↦ unrestrictedTowerComplex l E T n P)
        (fun n ↦ unrestrictedTowerTransition l E T P n) := by
  rw [IntegralOnSlice.globalTower_eq]
  exact evaluatedSequence _ _ P

private def integralLegacyComplexTower
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (P : IntegralOnSlice.Cx l E T none) :
    ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E T none :=
  Functor.ofOpSequence (X := fun n ↦ integralTowerComplex l E T D hl n P)
    (fun n ↦ integralTowerTransition l E T D hl P n)

private theorem integralLegacyTower_eq
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (P : IntegralOnSlice.Cx l E T none) :
    (IntegralOnSlice.tower l E T none).obj P = integralLegacyComplexTower l E T D hl P := by
  rw [integralGlobalTower]
  simp only [integralLegacyComplexTower, integralTowerTransition_eq, integralTowerComplex]

private theorem integralAugmentation_cast
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :
    ((IntegralOnSlice.augmentation l E T none).app P).app (op n) ≫
        eqToHom (congrArg (fun B : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E T none ↦ B.obj (op n))
          (integralLegacyTower_eq l E T D hl P)) =
      integralTowerUnit l E T D hl P n := by
  rw [integralGlobalUnit, integralTowerUnit_eq]
  change unrestrictedTowerUnit l E T P n ≫
    eqToHom (show unrestrictedTowerComplex l E T n P =
      unrestrictedTowerComplex l E T n P from rfl) = _
  simp only [eqToHom_refl, Category.comp_id]

private theorem roosProjection_cast {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (h : C = D) (n : ℕ) :
    eqToHom (congrArg integralOperationsRoos h) ≫
        (CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism (K := fun k ↦ D.obj (op k))
            (integralOperationsTowerStep D)) ≫ Pi.π (fun k ↦ D.obj (op k)) n) =
      (CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism (K := fun k ↦ C.obj (op k))
            (integralOperationsTowerStep C)) ≫ Pi.π (fun k ↦ C.obj (op k)) n) ≫
        eqToHom (congrArg (fun B : ℕᵒᵖ ⥤ CochainComplex A ℤ ↦ B.obj (op n)) h) := by
  subst D
  simp

private theorem integralRoosUnit_projection
    (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :
    IntegralOnSlice.roosUnit l E T none P ≫
        (CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism
            (K := fun k ↦ ((IntegralOnSlice.tower l E T none).obj P).obj (op k))
            (integralOperationsTowerStep ((IntegralOnSlice.tower l E T none).obj P))) ≫
          Pi.π (fun k ↦ ((IntegralOnSlice.tower l E T none).obj P).obj (op k)) n) =
      ((IntegralOnSlice.augmentation l E T none).app P).app (op n) := by
  simp only [IntegralOnSlice.roosUnit, CochainComplex.mappingCocone.lift_fst_assoc,
    IntegralOnSlice.productAugmentation, Pi.lift_comp_π]

private theorem invMapId_comp {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (P : A) {X Y : B} (a : X ⟶ F.obj P) (b : F.obj P ⟶ Y) :
    a ≫ inv (F.map (𝟙 P)) ≫ b = a ≫ b := by
  simp only [CategoryTheory.Functor.map_id, IsIso.inv_id, Category.id_comp]

private theorem productLift_transport {A : Type*} [Category* A]
    {X Y : A} {Z : ℕ → A} [HasProduct Z]
    (κ : X ⟶ Y) (a : ∀ n, X ⟶ Z n) (b : ∀ n, Y ⟶ Z n)
    (h : ∀ n, a n = κ ≫ b n) : Pi.lift a = κ ≫ Pi.lift b := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.lift_comp_π]
  exact h n

private theorem integralLegacyIdentityLeg
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (P : IntegralOnSlice.Cx l E T none)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheaf l E T D hl) (𝟙 P))
    (K : IntegralOnSlice.D l E T none) (e : DerivedCategory.Q.obj P ≅ K) (n : ℕ) :
    ((integralReductionTowerCone l E T D hl (𝟙 P) hq).extend e.inv).π.app (op n) =
      e.inv ≫ DerivedCategory.Q.map (integralTowerUnit l E T D hl P n) := by
  change e.inv ≫ (inv (DerivedCategory.Q.map (𝟙 P)) ≫
    DerivedCategory.Q.map (integralTowerUnit l E T D hl P n)) = _
  exact invMapId_comp _ _ _ _

end CompletionProof

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  unrestrictedTowerUnit unrestrictedTowerTransition DerivedCategory.Q
  HasDerivedCategory.standard scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence IntegralOnSlice.reductionWitness

private noncomputable def integralAuxiliaryDatum (p : ℕ) [Fact p.Prime] :
    FiniteFieldDatum.{0} :=
  { p := p
    a := 1
    q := p
    prime := Fact.out
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The five completeness conditions for the specified canonical units are equivalent.
There is no geometric finiteness or cohomological boundedness assumption.

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul,
and Tag 099B, lemma-derived-completion
(blueprint: lem-pur-roos-intrinsic-completeness-equivalence).

Proof:
1. The independent-universe singleton cone criterion identifies local vanishing with
   invertibility of the specified cone-completion unit and makes its output complete.
2. The regular principal-quotient augmentation gives a levelwise quasi-isomorphism
   from the scalar cones to the actual quotient reductions, preserving transitions
   and augmentations. Exact products and the cone triangle give an isomorphism of
   their Roos objects preserving the entire zero-homotopy units. Naturality and
   representative normalization of the completion unit give (iii) iff (v).
3. The square (1,-1) identifies the signed and unsigned cone models. After shifting
   by minus one it preserves the product-component unit and its zero homotopy,
   proving (iii) iff (iv).
4. Localization preserves countable products because these products are exact.
   Transporting the mapping-cocone triangle through its product comparison gives
   the strict Roos triangle with the actual localized product projections.
5. For (i), normalize the legacy quotient transitions. Rotate the asserted triangle
   and the strict Roos triangle to start at the same arrow 1-s. The identity maps of
   its two vertices extend to a triangle isomorphism. Shift back and transport local
   vanishing from the quotient Roos object to K, proving (ii). No arbitrary TR3 map
   is identified with the prescribed completion unit.
6. For (v), transport the strict Roos triangle along the specified, invertible unit.
   Its product projections are the quotient augmentations. The identity resolution
   of the given K-flat representative and the auxiliary finite-field datum at p
   therefore witness exactly the published global Roos condition (i). -/
theorem roosIntrinsicCompletenessEquivalence
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (_hpl : p ≠ l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : AlgebraicGeometry.Scheme.{t})
    (d : AlgebraicGeometry.Scheme.AdicCoefficientDatum
      (Padic.coefficientExtensionIntegers l E))
    (_hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (K : IntegralOnSlice.D l E T none)
    (P : (IntegralOnSlice.Good l E T none).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) :
    List.TFAE [
      IntegralOnSlice.IsComplete l E T none K,
      (∀ (U : T.ProEt)
        (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections),
        (∃ S : Sieve U, S ∈ AlgebraicGeometry.Scheme.ProEt.topology T U ∧
          ∀ (V : T.ProEt) (f : V ⟶ U), S f →
            ∃ c : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V),
              s.val (op (Over.mk f)) = integralCompletionScalarValue l E T (op V) * c) →
        IsZero (integralCompletionLocalTest l E T K U s)),
      IsIso (integralKoszulLimitUnit l E T K P.obj e),
      IsIso (integralKoszulIntrinsicUnit l E T K P.obj e),
      IsIso ((IntegralOnSlice.completionUnit l E T none).app K)] := by
  classical
  let : HasExactLimitsOfShape (Discrete ℕ) (IntegralOnSlice.Mod l E T none) :=
    IntegralOnSlice.sliceProductsExact l E T none
  let : HasFiniteBiproducts (IntegralOnSlice.Mod l E T none) :=
    Abelian.hasFiniteBiproducts
  let : CountableAB4Star (IntegralOnSlice.Mod l E T none) :=
    CountableAB4Star.of_hasExactLimitsOfShape_nat (IntegralOnSlice.Mod l E T none)
  let : HasCountableProducts (IntegralOnSlice.D l E T none) :=
    derivedCategory_hasCountableProducts (IntegralOnSlice.Mod l E T none)
  have hμ := (integralKoszulScalar_existsUnique l E T P.obj).exists.choose_spec
  have hlocal := IntegralPrincipalCone.localCriterion l E T
    (integralCompletionScalarValue l E T) (integralScalar_natural l E T)
    P.obj (integralKoszulScalar l E T P.obj) hμ K e
  obtain ⟨c, hc⟩ := integralPrincipalConeQuotientComparison l E T P.obj P.property.1
    (integralKoszulScalar l E T P.obj) hμ
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  have h35 : IsIso (integralKoszulLimitUnit l E T K P.obj e) ↔
      IsIso ((IntegralOnSlice.completionUnit l E T none).app K) := by
    have hn := (IntegralOnSlice.completionUnit l E T none).naturality e.inv
    have hp : (IntegralOnSlice.completionUnit l E T none).app
        (DerivedCategory.Q.obj P.obj) ≫
          (IntegralOnSlice.completionComparison l E T none).hom.app P =
        DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P.obj) :=
      (IntegralOnSlice.completionUnit_existsUnique l E T none).exists.choose_spec P
    have hnorm : (IntegralOnSlice.completionUnit l E T none).app K ≫
        (IntegralOnSlice.completion l E T none).map e.inv ≫
          (IntegralOnSlice.completionComparison l E T none).hom.app P =
        e.inv ≫ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P.obj) := by
      rw [← Category.assoc, ← hn, Functor.id_map, Category.assoc, hp]
    rw [← isIso_comp_right_iff _
      ((IntegralOnSlice.completion l E T none).map e.inv ≫
        (IntegralOnSlice.completionComparison l E T none).hom.app P), hnorm]
    rw [← hc]
    change IsIso (e.inv ≫ DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit (integralKoszulScalar l E T P.obj))) ↔ _
    simp only [← Category.assoc, isIso_comp_right_iff]
  have h34 : IsIso (integralKoszulLimitUnit l E T K P.obj e) ↔
      IsIso (integralKoszulIntrinsicUnit l E T K P.obj e) := by
    simp only [integralKoszulLimitUnit, integralKoszulIntrinsicUnit, isIso_comp_left_iff]
    exact signedFiberUnit _ _ (integralKoszulProductUnit_comp l E T P.obj)
      (integralKoszulLimitUnit_condition l E T P.obj)
      (integralKoszulIntrinsicUnit_condition l E T P.obj)
  tfae_have 1 → 2 := by
    rintro ⟨D, hl, P₀, G, q, hq, e₀, hprod, δ, hδ⟩
    let := hprod
    let C : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E T none :=
      Functor.ofOpSequence (X := fun n ↦ integralTowerComplex l E T D hl n P₀)
        (fun n ↦ integralTowerTransition l E T D hl P₀ n)
    obtain ⟨ε, hε⟩ := integralStrictRoosTriangle (A := IntegralOnSlice.Mod l E T none) C
    simp only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ] at hδ
    have hε' := hε
    simp only [integralOperationsTowerStep, C,
      Functor.ofOpSequence_map_homOfLE_succ] at hε'
    set_option backward.isDefEq.respectTransparency true in
    obtain ⟨i⟩ := integralRoosIso _ _ _ δ ε hδ hε'
    have hc₀ := integralQuotientLocallyComplete l E T P₀ hq.2
    have hC : (IntegralOnSlice.tower l E T none).obj P₀ = C := by
      rw [integralGlobalTower]
      simp only [C, integralTowerTransition_eq, integralTowerComplex]
      rfl
    have hc₁ := (congrArg (fun B : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E T none ↦
      IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T)
        (DerivedCategory.Q.obj (integralOperationsRoos B))) hC).mp hc₀
    change IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T) K
    exact integralLocallyComplete_iso l E T (integralCompletionScalarValue l E T) i.symm hc₁
  tfae_have 2 ↔ 3 := hlocal.2
  tfae_have 3 ↔ 4 := h34
  tfae_have 3 ↔ 5 := h35
  tfae_have 5 → 1 := by
    intro hK
    let := hK
    let D := integralAuxiliaryDatum p
    have hl : l ≠ D.p := _hpl.symm
    let C := integralLegacyComplexTower l E T D hl P.obj
    let j := DerivedCategory.Q.mapIso (eqToIso (congrArg integralOperationsRoos
      (integralLegacyTower_eq l E T D hl P.obj)))
    let κ₀ := e.inv ≫ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P.obj)
    have hκ₀ : IsIso κ₀ := by
      dsimp only [κ₀]
      rw [← hc, ← Category.assoc]
      change IsIso (integralKoszulLimitUnit l E T K P.obj e ≫ c.hom)
      have := h35.mpr hK
      infer_instance
    let κ : K ⟶ DerivedCategory.Q.obj (integralOperationsRoos C) := κ₀ ≫ j.hom
    have hκ : IsIso κ := by dsimp only [κ]; infer_instance
    have hκπ (n : ℕ) :
        κ ≫ DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun k ↦ C.obj (op k))
              (integralOperationsTowerStep C)) ≫ Pi.π (fun k ↦ C.obj (op k)) n) =
          e.inv ≫ DerivedCategory.Q.map (integralTowerUnit l E T D hl P.obj n) := by
      simp only [κ, κ₀, j, Functor.mapIso_hom, eqToIso.hom,
        Category.assoc, ← Functor.map_comp]
      rw [roosProjection_cast _ _ (integralLegacyTower_eq l E T D hl P.obj) n,
        ← Category.assoc, integralRoosUnit_projection, integralAugmentation_cast]
    obtain ⟨δ, hδ⟩ := integralStrictRoosTriangle (A := IntegralOnSlice.Mod l E T none) C
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    have h := integralRoosTransport
      (C := IntegralOnSlice.D l E T none)
      (X := fun n : ℕ ↦
        (DerivedCategory.Q (C := IntegralOnSlice.Mod l E T none)).obj (C.obj (op n)))
      (fun (n : ℕ) ↦
        (DerivedCategory.Q (C := IntegralOnSlice.Mod l E T none)).map
          (integralOperationsTowerStep C n))
      (asIso κ) _ δ hδ
    let ε : (∏ᶜ fun n ↦ DerivedCategory.Q.obj (C.obj (op n))) ⟶
        (shiftFunctor (IntegralOnSlice.D l E T none) (1 : ℤ)).obj K :=
      δ ≫ (shiftFunctor (IntegralOnSlice.D l E T none) (1 : ℤ)).map (asIso κ).inv
    have hqid : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (R := IntegralOnSlice.ring l E T none) (𝟙 P.obj) :=
      ⟨inferInstance, P.property.1⟩
    let : HasCountableProducts (completedIntegralDerivedCategory l E T D hl) :=
      inferInstanceAs (HasCountableProducts (IntegralOnSlice.D l E T none))
    have hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheaf l E T D hl) (𝟙 P.obj) :=
      hqid
    change IsDerivedCompleteUnrestricted l E T K
    refine ⟨D, hl, ?_⟩
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    refine ⟨P.obj, P.obj, 𝟙 P.obj, hq, e, ?_⟩
    dsimp only
    refine ⟨inferInstance, ?_⟩
    have hstep (n : ℕ) :
        DerivedCategory.Q.map (integralOperationsTowerStep C n) =
          (integralReductionTower l E T D hl P.obj).map (homOfLE n.le_succ).op := by
      simp only [C, integralLegacyComplexTower, integralOperationsTowerStep,
        integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ]
      erw [Functor.ofOpSequence_map_homOfLE_succ]
      rfl
    refine ⟨ε, ?_⟩
    have hπ : (Pi.lift (fun n ↦
        ((integralReductionTowerCone l E T D hl (𝟙 P.obj) hq).extend e.inv).π.app (op n))) =
        κ ≫ Pi.lift (fun n ↦ DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun k ↦ C.obj (op k))
              (integralOperationsTowerStep C)) ≫ Pi.π (fun k ↦ C.obj (op k)) n)) := by
      exact productLift_transport κ _ _ (fun n ↦
        (integralLegacyIdentityLeg l E T D hl P.obj hq K e n).trans (hκπ n).symm)
    rw [funext hstep] at h
    rw [hπ]
    exact h
  tfae_finish

end WeilConjectures
