/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedComplete
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
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
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation

-- Avoid successor-universe sheafification on coefficient-universe goals.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-! # Presentations for integral internal Hom and reduction

Source: blueprint, chap-The-six-operations-on-Dbctf, sk-prop-sf-biduality-general,
proposition-six-operations-change-coefficients--7, order 2134; Stacks Project, Tags 08J9, 07A6,
07A4 and 08TC (blueprint: def-sf-integral-hom-reduction-models).

The presentation records below specify ordinary, uncompleted derived tensor on
K-flat representatives. They normalize evaluation on local homogeneous sections,
and coefficient comparison on the ordinary scalar-extension units. Thus the
comparison is a specified transpose, rather than an unspecified isomorphism.
The theorem supplies all presentation data; none is an additional hypothesis.
Index n denotes the positive exponent n+1.

## Main definitions

* `IntegralHom.TensorPresentation`: canonical tensor and evaluation on representatives.
* `IntegralHom.ReductionPresentation`: normalized coefficient tensor comparison.
* `IntegralHom.comparison`: the transpose of reduced evaluation.

## Main statements

* `integralHomReduction`: reduction, pairing compatibility, and completeness.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open CategoryTheory.MonoidalCategory

namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

/-- Existing large-coefficient sheafification on the unchanged small site.
Source: Stacks 03DA (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance abSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} Y

/-- Existing locally bijective sheafification criterion at the coefficient universe.
Source: Stacks 03DA (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance abLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} Y

/-- The existing module category, retaining both site universes.
Source: Stacks 03DA (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable abbrev Modules := SheafOfModules.{max u (t + 1)}
  ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)

/-- Standard localization instance for the existing module category.
Source: Stacks 05RU (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance derivedCategory : HasDerivedCategory (Modules.{t, u} Y R) :=
  HasDerivedCategory.standard _

/-- The standard unbounded derived localization.
Source: Stacks 05RU (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable abbrev Derived := @DerivedCategory (Modules.{t, u} Y R) _ _
  (HasDerivedCategory.standard _)

/-- The existing ambient derived internal Hom, without a change of coefficients.
Source: Stacks 08J7 (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable abbrev hom : (Derived.{t, u} Y R)ᵒᵖ × Derived.{t, u} Y R ⥤ Derived.{t, u} Y R :=
  @derivedInternalHomOfUniverses.{t + 1, t, u}
    _ _ (AlgebraicGeometry.Scheme.ProEt.topology Y) _ _ R
      (HasDerivedCategory.standard _)

/-- The recorded monoidal localization structure for the independent coefficient universe.
Source: Stacks 03EK (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance tensorLocalization :
    ((AlgebraicGeometry.Scheme.ProEt.topology Y).W.inverseImage
      (PresheafOfModules.toPresheaf.{max u (t + 1)}
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat RingCat)).obj R).obj)).IsMonoidal :=
  SheafOfModules.isMonoidal_W_independentCoefficients R

/-- The existing sectionwise sheaf tensor bifunctor.
Source: Stacks 03EK (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable abbrev ordinaryTensor :=
  @MonoidalCategory.curriedTensor (Modules.{t, u} Y R) _ (SheafOfModules.monoidalCategory R)

/-- Zero preservation in the first tensor argument, from the existing tensor interface.
Source: Stacks 03EK (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance ordinaryTensorZero : (ordinaryTensor.{t, u} Y R).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R

/-- Zero preservation in the second tensor argument.
Source: Stacks 03EK (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance ordinaryTensorObjZero (M : Modules.{t, u} Y R) :
    ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R M

/-- Countable totalizations use the existing cocompleteness of module sheaves.
Source: Stacks 03DA (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance countableColimits :
    HasColimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  letI := integralCoefficientAbSheafify.{t, u} Y
  letI := integralCoefficientAbLocallyBijective.{t, u} Y
  letI : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1,t,u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).1
  hasColimitsOfSizeShrink.{0, 0, max u (t + 1), max u (t + 1),
    max u (t + 1), max u (t + 1) + 1} (Modules.{t, u} Y R)

/-- Signed total tensor of complexes, using Mathlib's existing totalization.
Source: Stacks 06YL (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def totalTensor :
    CochainComplex (Modules.{t, u} Y R) ℤ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ ⥤
      CochainComplex (Modules.{t, u} Y R) ℤ :=
  letI := countableColimits.{t, u} Y R
  letI := ordinaryTensorZero.{t, u} Y R
  letI : ∀ M : Modules.{t, u} Y R,
      ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} Y R M
  (ordinaryTensor.{t, u} Y R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)

/-- The recorded K-flat predicate, with independent coefficient universe.
Source: Stacks 06YN (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable abbrev flat : ObjectProperty (CochainComplex (Modules.{t, u} Y R) ℤ) :=
  CochainComplex.IsKFlatIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y) (R := R)

/-- Pure tensors mapped through the ordinary module-sheafification unit.
Source: Stacks 03EK (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def pair (M N : Modules.{t, u} Y R)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (((ordinaryTensor.{t, u} Y R).obj M).obj N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
      (𝟙 ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))

/-- A local homogeneous tensor inserted into the appropriate total summand.
Source: Stacks 06YL (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def totalPair (P Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    (((totalTensor.{t, u} Y R).obj P).obj Q).X (i + j) |>.val.obj U :=
  letI := countableColimits.{t, u} Y R
  letI := ordinaryTensorZero.{t, u} Y R
  letI : ∀ M : Modules.{t, u} Y R,
      ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} Y R M
  (CochainComplex.ιMapBifunctor P Q (ordinaryTensor.{t, u} Y R) i j (i + j) rfl).val.app U
    (pair.{t, u} Y R (P.X i) (Q.X j) U x y)

/-- The existing Hom-complex product projection, with its source type kept explicit.
Source: Stacks 0A8X (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def projection (P I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (j i : ℤ) :=
  homComplexπ.{t + 1, t, max u (t + 1), max u (t + 1)}
    (R := R) P I j i (i + j) rfl

/-- The product projection in the existing Hom complex, evaluated at the identity slice.
Source: Stacks 0A8X (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def evaluate (P I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (j i : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (f : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X j |>.val.obj U)
    (x : (P.X i).val.obj U) : (I.X (i + j)).val.obj U :=
  (((projection.{t, u} Y R P I j i).val.app U f).app (op (Over.mk (𝟙 U.unop)))).hom x

/-- Canonical localization comparison from a Hom complex to derived internal Hom.
It is the Hom map to the fixed K-injective replacement, followed by Localization.fac.
Source: Stacks 08J7 (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def homModelMap (P I : CochainComplex (Modules.{t, u} Y R) ℤ) :
    DerivedCategory.Q.obj (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) ⟶
      (hom.{t, u} Y R).obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) :=
  letI : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1,t,u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).1
  DerivedCategory.Q.map
    (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R)).obj (op P)).map
      ((CochainComplex.toKInjectiveResolution.{max u (t + 1)} _).app I)) ≫
    (coefficientHomResolutionIso.{u, t + 1, t, max u (t + 1) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R P I).inv

attribute [local irreducible] totalTensor totalPair pair projection evaluate homModelMap
  homComplexFunctor derivedInternalHomOfUniverses

/-- A presentation of the existing derived tensor and its evaluation adjunction.
The parameter adjunction retains naturality in the first derived argument.
The last field fixes evaluation on every K-flat test representative by the actual
Hom-complex evaluation, including the sign for the order P tensor Hom(P,I).
Source: Stacks 08J9, 06YU (blueprint: def-sf-integral-hom-reduction-models). -/
structure TensorPresentation where
  tensor : Derived.{t, u} Y R × Derived.{t, u} Y R ⥤ Derived.{t, u} Y R
  representative :
    ((flat.{t, u} Y R).ι.prod (flat.{t, u} Y R).ι) ⋙ Functor.uncurry.obj (totalTensor.{t, u} Y R) ⋙
      DerivedCategory.Q ≅
    (((flat.{t, u} Y R).ι ⋙ DerivedCategory.Q).prod
      ((flat.{t, u} Y R).ι ⋙ DerivedCategory.Q)) ⋙ tensor
  /-- Tensor-Hom currying, natural in its tensor parameter. -/
  parameterAdjunction : Functor.curry.obj tensor ⊣₂ Functor.curry.obj (hom.{t, u} Y R)
  evaluation : ∀ (P I S : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) (hS : flat.{t, u} Y R S), I.IsKInjective →
    ∀ q : S ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I,
      ∃ beta : ((totalTensor.{t, u} Y R).obj P).obj S ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S.X j).val.obj U),
          (beta.f (i + j)).val.app U (totalPair.{t, u} Y R P S i j U x s) =
            (i * j).negOnePow • evaluate.{t, u} Y R P I j i U ((q.f j).val.app U s) x) ∧
        representative.inv.app (⟨P, hP⟩, ⟨S, hS⟩) ≫ DerivedCategory.Q.map beta =
          tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I)) ≫
          (parameterAdjunction.adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I)

/-- The adjunction at a fixed first argument, retaining the existing presentation API.
Source: Stacks 08J9 (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def TensorPresentation.adjunction
    {Y : AlgebraicGeometry.Scheme.{t}}
    {R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}}
    (a : TensorPresentation.{t, u} Y R)
    (K : Derived.{t, u} Y R) :
    (Functor.curry.obj a.tensor).obj K ⊣ (Functor.curry.obj (hom.{t, u} Y R)).obj (op K) :=
  a.parameterAdjunction.adj K

end WeilConjectures.IntegralHom

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

namespace IntegralHom

/-- Additivity of the same ordinary scalar extension, from its recorded adjunction packet.
Source: Stacks 03CZ (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance reductionAdditive (n : ℕ) :
    (integralReductionChangeOfRings l E Y D hl n).Additive :=
  scalarReductionExtensionAdditive l E Y n

/-- Zero preservation supplied by additivity of coefficient extension.
Source: Stacks 03CZ (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable instance reductionZero (n : ℕ) :
    (integralReductionChangeOfRings l E Y D hl n).PreservesZeroMorphisms :=
  inferInstance

/-- The canonical derived-reduction counit on complexes, including quotient factors.
Source: Stacks 06YY (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def reductionCounit (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    (integralDerivedReduction l E Y D hl n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (integralDerivedReduction l E Y D hl n).map
      ((DerivedCategory.quotientCompQhIso _).app P).inv ≫
    (integralDerivedReductionCounit l E Y D hl n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategoryFactors
        (.up ℤ)).app P).hom ≫
    ((DerivedCategory.quotientCompQhIso _).app
      (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)).hom

/-- The ordinary extension unit, with its recorded normalization x maps to 1 tensor x.
Its choice is determined by the adjunction and the sectionwise normalization.
Source: Stacks 03CZ (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def reductionUnit (n : ℕ)
    (M : completedIntegralModuleSheaves l E Y D hl) :
    M ⟶ (completedIntegralRestrictScalars l E Y D hl n).obj
      ((integralReductionChangeOfRings l E Y D hl n).obj M) :=
  (Classical.choose (scalarReductionExtension_adjunction l E Y n)).unit.app M

attribute [local irreducible] reductionCounit reductionUnit integralDerivedReduction
  integralReductionChangeOfRings

/-- Canonical tensor comparison for reduction. Its normalization uses every K-flat
pair and the actual ordinary extension units on local sections. The chain comparison
is required to be invertible; its displayed unit formula uniquely determines it.
Thus neither the derived comparison nor the ordinary comparison is an arbitrary map.
Source: Stacks 07A4 and 06YY (blueprint: def-sf-integral-hom-reduction-models). -/
structure ReductionPresentation
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ) where
  target : TensorPresentation.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
  mu : a.tensor ⋙ integralDerivedReduction l E Y D hl n ≅
    ((integralDerivedReduction l E Y D hl n).prod
      (integralDerivedReduction l E Y D hl n)) ⋙ target.tensor
  normalization :
    ∀ (P Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
      (hp : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P)
      (hq : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q),
    ∃ (hp' : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P))
      (hq' : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q))
      (beta : ((totalTensor.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)).obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      ((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj
        (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q)),
      IsIso beta ∧
      (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        (beta.f (i + j)).val.app U
          (totalPair.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
            (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)
            (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q)
            i j U ((reductionUnit l E Y D hl n (P.X i)).val.app U x)
              ((reductionUnit l E Y D hl n (Q.X j)).val.app U y)) =
        (reductionUnit l E Y D hl n
          ((((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q).X
            (i + j))).val.app U
          (totalPair.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P Q i j U x y)) ∧
      (integralDerivedReduction l E Y D hl n).map
          (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        target.tensor.map (Prod.mkHom (reductionCounit l E Y D hl n P)
          (reductionCounit l E Y D hl n Q)) ≫
        target.representative.inv.app (⟨_, hp'⟩, ⟨_, hq'⟩) ≫ DerivedCategory.Q.map beta =
        reductionCounit l E Y D hl n
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q)

/-- The comparison is exactly the transpose of reduced evaluation, using the inverse
canonical tensor comparison. In particular it is a morphism over the finite quotient.
Source: blueprint order 2134, displayed comparison and pairing;
Stacks 07A6 and 08J9 (blueprint: def-sf-integral-hom-reduction-models). -/
noncomputable def comparison
    {a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)}
    {n : ℕ} (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    (integralDerivedReduction l E Y D hl n).obj
        ((hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)) ⟶
      (hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
        (op ((integralDerivedReduction l E Y D hl n).obj K),
          (integralDerivedReduction l E Y D hl n).obj L) :=
  (m.target.adjunction ((integralDerivedReduction l E Y D hl n).obj K)).homEquiv _ _
    (m.mu.inv.app (K, (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)) ≫
      (integralDerivedReduction l E Y D hl n).map ((a.adjunction K).counit.app L))

end IntegralHom

end WeilConjectures
