/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
import all WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Constant-scalar bilinearity of integral derived internal Hom

Source: Stacks Project, Section 08J7 and Lemma 0A95; the rational internal-Hom
paragraph of blueprint `prose-03-02`.
-/

@[expose] public section
set_option autoImplicit false

universe u a b
open CategoryTheory AlgebraicGeometry Opposite

namespace WeilConjectures

open CategoryTheory.MonoidalCategory

private theorem closedHom_bilinear
    {D : Type a} [Category.{b} D] [Preadditive D]
    (R : Type*) [CommRing R] [Linear R D]
    (H : Dᵒᵖ × D ⥤ D) (S : CoefficientClosedStructure H)
    (hadd : let := S.monoidal; MonoidalPreadditive D)
    (hlin : let := S.monoidal; let := hadd; MonoidalLinear R D)
    (M M' N N' : D) :
    ∃ b : (M' ⟶ M) →ₗ[R] (N ⟶ N') →ₗ[R]
        (H.obj (op M, N) ⟶ H.obj (op M', N')),
      ∀ f g, b f g = H.map (Prod.mkHom f.op g) := by
  let := S.monoidal
  let := hadd
  let := hlin
  let A : (M' ⟶ M) →ₗ[R] (H.obj (op M, N) ⟶ H.obj (op M', N)) :=
    { toFun := fun f ↦ H.map (Prod.mkHom f.op (𝟙 N))
      map_add' := fun f g ↦ by
        apply ((S.adjunction M').homEquiv _ N).symm.injective
        simp only [Adjunction.homEquiv_counit, Functor.map_add, Preadditive.add_comp]
        rw [S.evaluation_naturality, S.evaluation_naturality, S.evaluation_naturality]
        simp only [Functor.map_add, Preadditive.add_comp]
      map_smul' := fun r f ↦ by
        apply ((S.adjunction M').homEquiv _ N).symm.injective
        simp only [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp]
        rw [S.evaluation_naturality, S.evaluation_naturality]
        simp only [Functor.map_smul, Linear.smul_comp, RingHom.id_apply] }
  let B : (N ⟶ N') →ₗ[R] (H.obj (op M', N) ⟶ H.obj (op M', N')) :=
    { toFun := (Prod.sectR (op M') D ⋙ H).map
      map_add' := by
        let := (S.adjunction M').right_adjoint_additive
        exact fun x y ↦ (Prod.sectR (op M') D ⋙ H).map_add (f := x) (g := y)
      map_smul' := fun r f ↦ by
        apply ((S.adjunction M').homEquiv _ N').symm.injective
        simp only [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp]
        change (tensorRight M').map ((Prod.sectR (op M') D ⋙ H).map (r • f)) ≫
            (S.adjunction M').counit.app N' = _
        have hc (g : N ⟶ N') := (S.adjunction M').counit.naturality g
        dsimp only [Functor.comp_map, Functor.id_map] at hc ⊢
        rw [hc, hc]
        simp only [Linear.comp_smul, RingHom.id_apply] }
  refine ⟨
    { toFun := fun f ↦ (Linear.leftComp R _ (A f)).comp B
      map_add' := fun f g ↦ by
        ext k
        exact (congrArg (fun z ↦ z ≫ B k) (A.map_add f g)).trans
          (Preadditive.add_comp _ _ _ _ _ _)
      map_smul' := fun r f ↦ by
        ext k
        exact (congrArg (fun z ↦ z ≫ B k) (A.map_smul r f)).trans
          (Linear.smul_comp _ _ _ _ _ _) }, ?_⟩
  intro f g
  change H.map (Prod.mkHom f.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op M')) g) = _
  rw [← H.map_comp]
  congr 1
  ext <;> simp

/-- The ambient integral internal-Hom action is bilinear for the published constant
valuation-ring action. The first arrow is contravariant; the second is covariant.
Source: Stacks Project, Section 08J7 and Lemma 0A95; blueprint
`prose-03-02`, rational internal-Hom paragraph.
(blueprint: lem-sf-integral-derived-hom-bilinear).

Proof: compute the second input with a K-injective resolution. On the sheaf Hom
complex, precomposition and postcomposition are additive in their arrows. For a
constant valuation-ring scalar a, their sectionwise formulas are h ↦ h ∘ (a f)
and h ↦ (a g) ∘ h. Module-linearity of h and of the differentials identifies these
with a times the corresponding maps. These identities hold degreewise in the
products defining the Hom complex, hence also for its differential. Pass to the
derived category. An arbitrary first-variable derived arrow is a roof, and Hom
into a K-injective complex inverts its quasi-isomorphism leg by Lemma 0A95.
Arbitrary second-variable arrows are represented between K-injective complexes;
the equivalence between their homotopy category and the derived category preserves
addition and the constant scalar action. The Hom-complex equations therefore give
separate additivity and linearity for the two derived arrow maps. Conjugating by
the canonical replacement comparisons preserves these equations since composition
is linear for the published constant-section action. Package the simultaneous
arrow action in the two nested linear maps displayed below. No constructibility,
completeness, flatness or boundedness is assumed, and zero objects and torsion
inputs obey the same degreewise formulas. -/
theorem integralDerivedHom_bilinear (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u})
    (M M' N N' : DerivedCategory (integralTowerModules l E W)) :
    ∃ b : (M' ⟶ M) →ₗ[Padic.coefficientExtensionIntegers l E]
        (N ⟶ N') →ₗ[Padic.coefficientExtensionIntegers l E]
        ((integralDerivedInternalHom l E W).obj (op M, N) ⟶
          (integralDerivedInternalHom l E W).obj (op M', N')),
      ∀ a b', b a b' = (integralDerivedInternalHom l E W).map (Prod.mkHom a.op b') := by
  let := coefficientModuleLinear l E W
  let standard : Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E W)) :=
    Localization.linear _ DerivedCategory.Qh
      (HomotopyCategory.quasiIso (integralTowerModules l E W) (.up ℤ))
  have heq : integralCoefficientLinear l E W = standard := by
    apply coefficientLinear_ext
    intro K K' r f
    rw [(integralCoefficientLinear_existsUnique l E W).exists.choose_spec]
    let := standard
    have hc : integralScalarDerivedAction l E W r =
        (Linear.toCatCenter (Padic.coefficientExtensionIntegers l E)
          (DerivedCategory (integralTowerModules l E W)) r).asHom := by
      rw [coefficientDerived_eq]
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ))
      intro P
      change (CatCenter.localization _ DerivedCategory.Q _).app (DerivedCategory.Q.obj P) = _
      rw [CatCenter.localization_app]
      change DerivedCategory.Q.map (r • 𝟙 P) = r • 𝟙 (DerivedCategory.Q.obj P)
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [hc]
    change (r • 𝟙 K) ≫ f = r • f
    simp
  let : Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E W)) := integralCoefficientLinear l E W
  let C := completedIntegralCommRingSheafUnrestricted l E W
  let J := AlgebraicGeometry.Scheme.ProEt.topology W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := RingedDerivedNative.moduleMonoidal.{u + 1, u, u} J C
  let := RingedDerivedNative.moduleSymmetric.{u + 1, u, u} J C
  let := RingedDerivedNative.modulePreadditive.{u + 1, u, u} J C
  let := RingedDerivedNative.moduleClosed.{u + 1, u, u} J C
  let := RingedDerivedNative.moduleGrothendieck.{u + 1, u, u} J C
  let := RingedDerivedNative.moduleFlat.{u + 1, u, u} J C
  let : Linear (SheafOfModules.LineEvaluation.scalars.{u + 1, u, u} C)
      (integralTowerModules l E W) :=
    SheafOfModules.LineEvaluation.coefficientLinear.{u + 1, u, u} C
  let : MonoidalLinear (Padic.coefficientExtensionIntegers l E)
      (integralTowerModules l E W) := by
    have hright (P : integralTowerModules l E W) :
        (tensorRight P).Linear (Padic.coefficientExtensionIntegers l E) := by
      constructor
      intro M N f r
      have ht := @SheafOfModules.LineEvaluation.tensor_linear.{u + 1, u, u}
        W.ProEt inferInstance J
        (essentiallySmallSelf.{0, u, u + 1} W.ProEt)
        (inferInstance : J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) C P
      have hh := ht.map_smul f (coefficient_scalarSections l E W r)
      exact hh
    have hleft (P : integralTowerModules l E W) :
        (tensorLeft P).Linear (Padic.coefficientExtensionIntegers l E) := by
      let := hright P
      exact Functor.linear_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight P).symm
    exact
      { whiskerLeft_smul := fun X _ _ r f ↦ (hleft X).map_smul f r
        smul_whiskerRight := fun r _ _ f X ↦ (hright X).map_smul f r }
  obtain ⟨S, hS, _⟩ := RingedDerivedNative.closedAdjunction.{u + 1, u, u} J C
  have hSadd : let := S.monoidal;
      MonoidalPreadditive (DerivedCategory (integralTowerModules l E W)) := by
    rw [hS]
    exact DerivedCategory.monoidalPreadditive
  have hSlin : let := S.monoidal; let := hSadd;
      MonoidalLinear (Padic.coefficientExtensionIntegers l E)
        (DerivedCategory (integralTowerModules l E W)) := by
    change @MonoidalLinear (Padic.coefficientExtensionIntegers l E) _
      (DerivedCategory (integralTowerModules l E W)) _ _
      (integralCoefficientLinear l E W) S.monoidal hSadd
    rw [heq]
    revert hSadd
    rw [hS]
    intro hadd
    exact DerivedCategory.monoidalLinear _
  exact closedHom_bilinear _ _ S hSadd hSlin M M' N N'

end WeilConjectures
