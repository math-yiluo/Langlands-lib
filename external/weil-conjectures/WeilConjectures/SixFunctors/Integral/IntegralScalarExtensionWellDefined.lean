/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Localization.Predicate
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift

/-! # Well-defined completed integral scalar extension

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 3.4.10,
Proposition 3.5.1(3), and Proposition 6.8.14(1); Stacks Tags 06YS, 06YT, 08TC, 04VG
(blueprint: lem-weil-integral-scalar-extension-well-defined).

The zero-based level n means exponent n+1. Coefficients, tensor generators,
transitions, and the diagonal Roos maps are fixed before localization. Scalar
multiplication is expressed intrinsically by the canonical constant-section
endomorphism, descended through Q; no auxiliary linear structure is chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped ChangeOfRings

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace SheafOfModules.IntegralScalarProof

universe a b r

-- A linear map over the finite target remains linear over the completed target
-- when the two projection maps form a commuting triangle.
private noncomputable def restrictTriangle
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (p : R ⟶ S) (q : S ⟶ T) (p' : R ⟶ T)
    (h : p ≫ q = p') (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)
    (k : M ⟶ (restrictScalars q).obj N) :
    (restrictScalars p).obj M ⟶ (restrictScalars p').obj N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((restrictScalars p).obj M).val.obj U)
        (Y := ((restrictScalars p').obj N).val.obj U)
        { toFun := k.val.app U
          map_add' := _root_.map_add _
          map_smul' := fun r x ↦ by
            change M.val.obj U at x
            change k.val.app U (p.hom.app U r • x) =
              p'.hom.app U r • (show N.val.obj U from k.val.app U x)
            rw [_root_.map_smul]
            have he := congrArg (fun f ↦ (f.hom.app U).hom r) h
            exact congrArg (fun a ↦ a • (show N.val.obj U from k.val.app U x)) he }
      naturality := by
        intro U V f
        ext x
        exact PresheafOfModules.naturality_apply k.val f x }

universe a' b' r'

variable {C : Type a'} [Category.{b'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r'} RingCat.{r'})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r'}] [HasWeakSheafify J AddCommGrpCat.{r'}]

-- Tensor balancing uses the source coefficient sheaf A; the restricted action
-- uses the independent target coefficient sheaf B.
private noncomputable def scalarStep {A B S T : Sheaf J CommRingCat.{r'}}
    (f : A ⟶ S) (g : A ⟶ T) (p : B ⟶ S) (q : S ⟶ T) (p' : B ⟶ T)
    (hf : f ≫ q = g) (hp : p ≫ q = p')
    (M : SheafOfModules.{r'} ((sheafCompose J (forget₂ CommRingCat.{r'} RingCat.{r'})).obj A)) :=
  restrictTriangle.{a', b', r'}
    ((sheafCompose J (forget₂ CommRingCat.{r'} RingCat.{r'})).map p)
    ((sheafCompose J (forget₂ CommRingCat.{r'} RingCat.{r'})).map q)
    ((sheafCompose J (forget₂ CommRingCat.{r'} RingCat.{r'})).map p')
    (by rw [← Functor.map_comp, hp])
    (SheafOfModules.changeOfRings.{b', a', r'} f M) (SheafOfModules.changeOfRings.{b', a', r'} g M)
    (SheafOfModules.UnrestrictedTowerProof.sheafMap f g q hf M)

end SheafOfModules.IntegralScalarProof

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The larger absolute value restricts to the specified absolute value on E.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: Compose the absolute value on L with the injective field inclusion. It extends the
p-adic absolute value. spectralNorm_unique_field_norm_ext identifies it with the
spectral absolute value on E (lem-weil-l-adic-extension-absolute-value). -/
theorem integralScalar_absoluteValue (x : E) :
    Padic.coefficientExtensionAbsoluteValue l L (ι x) =
      Padic.coefficientExtensionAbsoluteValue l E x := by
  let f : AbsoluteValue E ℝ :=
    (Padic.coefficientExtensionAbsoluteValue l L).comp ι.toRingHom.injective
  have hf : ∀ a : ℚ_[l], f (algebraMap (ℚ_[l]) E a) = ‖a‖ := by
    intro a
    change Padic.coefficientExtensionAbsoluteValue l L
      (ι (algebraMap (ℚ_[l]) E a)) = ‖a‖
    rw [ι.commutes]
    exact spectralNorm_extends a
  calc
    Padic.coefficientExtensionAbsoluteValue l L (ι x) = spectralNorm (ℚ_[l]) E x :=
      spectralNorm_unique_field_norm_ext hf x
    _ = Padic.coefficientExtensionAbsoluteValue l E x := rfl

/-- The field inclusion maps integers to integers, in independent site/coefficient sizes.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: By integralScalar_absoluteValue the two absolute values agree on x. The defining
DVR witnesses characterize membership in each integer ring by absolute value at most one.
Apply this characterization to hx and to ι x. -/
theorem integralScalar_integer_mem (x : E)
    (hx : x ∈ Padic.coefficientExtensionIntegers l E) :
    ι x ∈ Padic.coefficientExtensionIntegers l L := by
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.1 x
  have hL := (Padic.coefficientExtensionIntegers_dvr l L).choose_spec.1 (ι x)
  apply hL.mpr
  rw [integralScalar_absoluteValue l E L ι x]
  exact hE.mp hx

/-- The actual restriction of the field inclusion to the recorded valuation subrings.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarIntegerInclusion :
    Padic.coefficientExtensionIntegers l E →+* Padic.coefficientExtensionIntegers l L :=
  ((ι.toRingHom.comp (Padic.coefficientExtensionIntegers l E).subtype).codRestrict
    (Padic.coefficientExtensionIntegers l L)
    (fun x ↦ integralScalar_integer_mem l E L ι x x.property))

/-- The source uniformizer powers vanish in the same-index target quotient.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: The source uniformizer has absolute value less than one. By absolute-value
restriction it belongs to the target maximal ideal, generated by its uniformizer.
Taking (n+1)st powers gives the required ideal inclusion; quotienting kills its image. -/
theorem integralScalar_quotient_kernel (n : ℕ)
    (x : Padic.coefficientExtensionIntegers l E)
    (hx : x ∈ Padic.coefficientExtensionIdeal l E (n + 1)) :
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1)))
      (integralScalarIntegerInclusion l E L ι x) = 0 := by
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hL := (Padic.coefficientExtensionIntegers_dvr l L).choose_spec
  have hgenE : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenL : Ideal.span {Padic.coefficientExtensionUniformizer l L} =
      Padic.coefficientExtensionMaximalIdeal l L :=
    hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hπE : Padic.coefficientExtensionUniformizer l E ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    rw [← hgenE]
    exact Ideal.mem_span_singleton_self _
  have hπL : integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E) ∈
      Padic.coefficientExtensionMaximalIdeal l L := by
    apply (hL.2.1 _).mpr
    change Padic.coefficientExtensionAbsoluteValue l L
      (ι (Padic.coefficientExtensionUniformizer l E)) < 1
    rw [integralScalar_absoluteValue l E L ι]
    exact (hE.2.1 _).mp hπE
  rw [← hgenL, Ideal.mem_span_singleton] at hπL
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact (pow_dvd_pow_of_dvd hπL (n + 1)).trans (by
    simpa only [map_pow] using map_dvd (integralScalarIntegerInclusion l E L ι) hx)

/-- The canonical quotient map induced by inclusion of integer rings.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarQuotientMap (n : ℕ) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (n + 1) :=
  Ideal.Quotient.lift (Padic.coefficientExtensionIdeal l E (n + 1))
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))).comp
      (integralScalarIntegerInclusion l E L ι))
    (integralScalar_quotient_kernel l E L ι n)

/-- The quotient maps commute with the two canonical reductions.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: Both composites send a class represented by x to the class represented by ι x.
Quotient induction and ring-homomorphism extensionality give equality. -/
theorem integralScalarQuotientMap_transition (n : ℕ) :
    (Padic.coefficientExtensionTransition l L (n + 1)).comp
        (integralScalarQuotientMap l E L ι (n + 1)) =
      (integralScalarQuotientMap l E L ι n).comp
        (Padic.coefficientExtensionTransition l E (n + 1)) := by
  apply RingHom.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x => rfl

variable (Y : AlgebraicGeometry.Scheme.{t})

/-- The quotient inclusion after functorial constant sheafification.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarQuotientSheafMap (n : ℕ) :
    integralCoefficientCommRingSheaf l E Y n ⟶
      integralCoefficientCommRingSheaf l L Y n :=
  (constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((integralScalarQuotientMap l E L ι n).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

/-- The actual coefficient map ρ_n=(ι_n)_Y π_n, without auxiliary finite-field data.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarRho (n : ℕ) :
    completedIntegralCommRingSheafUnrestricted l E Y ⟶
      integralCoefficientCommRingSheaf l L Y n :=
  completedIntegralCommRingProjectionUnrestricted l E Y n ≫
    integralScalarQuotientSheafMap l E L ι Y n

attribute [local irreducible] integralScalarRho

set_option linter.defProp false in
/-- The recorded change-of-rings witness, fixing the ordinary functor on objects and maps.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarReductionWitness (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l L Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheafUnrestricted l E Y)
    (O' := integralCoefficientCommRingSheaf l L Y n)
    (integralScalarRho l E L ι Y n)

/-- Ordinary sheafified sectionwise extension along ρ_n, with its finite target action.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarReductionConcrete (n : ℕ) :
    integralTowerModules l E Y ⥤ integralOperationsFiniteModules l L Y n :=
  let φ := integralScalarRho l E L ι Y n
  let E₀ : SheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheafUnrestricted l E Y)) ⥤
      PresheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (integralCoefficientCommRingSheaf l L Y n)).obj :=
    { obj := SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ
      map := fun a ↦
        { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U)
          naturality := SheafOfModules.changeOfRingsHom_naturality.{t, t + 1, max u (t + 1)} φ _ a }
      map_id := by
        intro M
        apply PresheafOfModules.hom_ext
        intro U
        simp
        rfl
      map_comp := by
        intro M N P a b
        apply PresheafOfModules.hom_ext
        intro U
        simp }
  E₀ ⋙ PresheafOfModules.sheafification.{max u (t + 1)}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l L Y n)).obj)

/-- Additivity of ordinary sheafified coefficient change.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable instance integralScalarReductionConcrete_additive (n : ℕ) :
    (integralScalarReductionConcrete l E L ι Y n).Additive := by
  let φ := integralScalarRho l E L ι Y n
  have hscalar (U : Y.ProEtᵒᵖ) :
      (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  let S := PresheafOfModules.sheafification.{max u (t + 1)}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l L Y n)).obj)
  have : S.Additive :=
    (PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
      (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (integralCoefficientCommRingSheaf l L Y n)).obj)).left_adjoint_additive
  constructor
  intro M N a b
  change S.map _ = S.map _ + S.map _
  rw [← S.map_add]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  simpa only [SheafOfModules.add_val, PresheafOfModules.add_app] using
    (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
      (f := a.val.app U) (g := b.val.app U)

/-- The canonical ordinary tensor functor, with its implementation exposed by equality.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarReduction (n : ℕ) :
    integralTowerModules l E Y ⥤ integralOperationsFiniteModules l L Y n :=
  (existsUnique_eq (a' := integralScalarReductionConcrete l E L ι Y n)).exists.choose

/-- The ordinary tensor functor equals the explicit sectionwise construction.
Source: Stacks Tag 06YT (blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: Equality to that constructed functor is the defining singleton property. -/
theorem integralScalarReduction_eqConcrete (n : ℕ) :
    integralScalarReduction l E L ι Y n = integralScalarReductionConcrete l E L ι Y n :=
  (existsUnique_eq (a' := integralScalarReductionConcrete l E L ι Y n)).exists.choose_spec

/-- The canonical comparison with the constructed ordinary tensor functor.
Source: Stacks Tag 06YT (blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarReductionIso (n : ℕ) :
    integralScalarReduction l E L ι Y n ≅ integralScalarReductionConcrete l E L ι Y n :=
  eqToIso (integralScalarReduction_eqConcrete l E L ι Y n)

/-- Additivity of the canonical ordinary tensor functor.
Source: Stacks Tag 06YT (blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable instance integralScalarReduction_additive (n : ℕ) :
    (integralScalarReduction l E L ι Y n).Additive := by
  rw [integralScalarReduction_eqConcrete]
  infer_instance

/-- Termwise extension P_{L,n}, before restriction of scalars.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarFiniteComplex (n : ℕ) :=
  (integralScalarReduction l E L ι Y n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordinary module functor extending coefficients and restricting to the completion.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarOrdinaryLevel (n : ℕ) :
    integralTowerModules l E Y ⥤ integralTowerModules l L Y :=
  (integralScalarReduction l E L ι Y n ⋙
    SheafOfModules.restrictScalars.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n)))

/-- Additivity of ordinary extension followed by restriction.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-scalar-extension-well-defined). -/
instance integralScalarOrdinaryLevel_additive (n : ℕ) :
    (integralScalarOrdinaryLevel l E L ι Y n).Additive :=
  inferInstanceAs ((integralScalarReduction l E L ι Y n ⋙
    SheafOfModules.restrictScalars.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))).Additive)

/-- The complex Res^L_n(P_{L,n}) over the target completion.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarLevel (n : ℕ) :=
  (integralScalarOrdinaryLevel l E L ι Y n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The sheafified tensor generator s⊗x in the specified ordinary scalar extension.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarTensorSection (n : ℕ)
    (M : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    ((integralScalarReduction l E L ι Y n).obj M).val.obj U :=
  ((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (integralScalarRho l E L ι Y n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((integralScalarRho l E L ι Y n).hom.app U).hom] x))

section ScalarTransitions

private theorem integralScalarQuotientSheafMap_transition (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι Y (n + 1) ≫
        unrestrictedCoefficientStep l L Y n =
      unrestrictedCoefficientStep l E Y n ≫ integralScalarQuotientSheafMap l E L ι Y n := by
  unfold integralScalarQuotientSheafMap unrestrictedCoefficientStep
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  cases x with
  | up x =>
    induction x using Quotient.inductionOn' with
    | h x => rfl

private theorem integralScalarRho_transition (n : ℕ) :
    integralScalarRho l E L ι Y (n + 1) ≫ unrestrictedCoefficientStep l L Y n =
      integralScalarRho l E L ι Y n := by
  unfold integralScalarRho
  rw [Category.assoc, integralScalarQuotientSheafMap_transition,
    ← Category.assoc, unrestrictedCoefficientStep_comp]

attribute [local irreducible] limit integralScalarReductionWitness

private theorem integralScalarReduction_obj (n : ℕ) (M : integralTowerModules l E Y) :
    (integralScalarReduction l E L ι Y n).obj M =
      SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} (integralScalarRho l E L ι Y n) M :=
  congrArg (fun F ↦ F.obj M) (integralScalarReduction_eqConcrete l E L ι Y n)

private theorem scalarFunctor_map_transport {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) (h : F = G) {M N : A} (a : M ⟶ N) :
    F.map a = eqToHom (congrArg (fun F ↦ F.obj M) h) ≫ G.map a ≫
      eqToHom (congrArg (fun F ↦ F.obj N) h).symm := by
  subst G
  simp

private theorem integralScalarReduction_map (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N) :
    (integralScalarReduction l E L ι Y n).map a =
      eqToHom (integralScalarReduction_obj l E L ι Y n M) ≫
        SheafOfModules.changeOfRingsHom (integralScalarRho l E L ι Y n) M a ≫
          eqToHom (integralScalarReduction_obj l E L ι Y n N).symm :=
  scalarFunctor_map_transport _ _ (integralScalarReduction_eqConcrete l E L ι Y n) a

private noncomputable abbrev integralScalarRestrict (n : ℕ) :=
  SheafOfModules.restrictScalars.{max u (t + 1)}
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l L Y n))

attribute [local irreducible] SheafOfModules.UnrestrictedTowerProof.sectionMap
  SheafOfModules.UnrestrictedTowerProof.presheafMap SheafOfModules.UnrestrictedTowerProof.sheafMap

private noncomputable def integralScalarModuleStepRaw (n : ℕ)
    (M : integralTowerModules l E Y) :=
  SheafOfModules.IntegralScalarProof.scalarStep.{t + 1, t, max u (t + 1)}
    (A := completedIntegralCommRingSheafUnrestricted l E Y)
    (B := completedIntegralCommRingSheafUnrestricted l L Y)
    (S := integralCoefficientCommRingSheaf l L Y (n + 1))
    (T := integralCoefficientCommRingSheaf l L Y n)
    (integralScalarRho l E L ι Y (n + 1)) (integralScalarRho l E L ι Y n)
    (completedIntegralCommRingProjectionUnrestricted l L Y (n + 1))
    (unrestrictedCoefficientStep l L Y n)
    (completedIntegralCommRingProjectionUnrestricted l L Y n)
    (integralScalarRho_transition l E L ι Y n)
    (unrestrictedCoefficientStep_comp l L Y n) M

-- The restriction functors have definitionally equal underlying section types.
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def integralScalarModuleStep (n : ℕ)
    (M : integralTowerModules l E Y) :
    (integralScalarRestrict l L Y (n + 1)).obj
        ((integralScalarReduction l E L ι Y (n + 1)).obj M) ⟶
      (integralScalarRestrict l L Y n).obj
        ((integralScalarReduction l E L ι Y n).obj M) :=
  (integralScalarRestrict l L Y (n + 1)).map
      ((integralScalarReductionIso l E L ι Y (n + 1)).hom.app M) ≫
    integralScalarModuleStepRaw l E L ι Y n M ≫
    (integralScalarRestrict l L Y n).map
      ((integralScalarReductionIso l E L ι Y n).inv.app M)

private theorem integralScalarModuleStep_tmul (n : ℕ) (M : integralTowerModules l E Y)
    (U : Y.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj U)
    (x : M.val.obj U) :
    (integralScalarModuleStep l E L ι Y n M).val.app U
      (integralScalarTensorSection l E L ι Y (n + 1) M U s x) =
    integralScalarTensorSection l E L ι Y n M U
      ((integralCoefficientSheafTransition l L Y n).hom.app U s) x := by
  let e₁ := (integralScalarReductionIso l E L ι Y (n + 1)).app M
  let e₀ := (integralScalarReductionIso l E L ι Y n).app M
  let z := SheafOfModules.UnrestrictedTowerProof.tensorSection
    (integralScalarRho l E L ι Y (n + 1)) M U s x
  change (e₀.inv.val.app U)
      ((integralScalarModuleStepRaw l E L ι Y n M).val.app U
        ((e₁.hom.val.app U) ((e₁.inv.val.app U) z))) = _
  have he : (e₁.hom.val.app U) ((e₁.inv.val.app U) z) = z :=
    congrArg (fun f ↦ (f.val.app U) z) e₁.inv_hom_id
  rw [he]
  exact congrArg (fun z ↦ (e₀.inv.val.app U) z)
    (SheafOfModules.UnrestrictedTowerProof.sheafMap_tmul
      (integralScalarRho l E L ι Y (n + 1)) (integralScalarRho l E L ι Y n)
      (unrestrictedCoefficientStep l L Y n) (integralScalarRho_transition l E L ι Y n) M U s x)

private theorem integralScalarReduction_hom_ext (n : ℕ) (M : integralTowerModules l E Y)
    (N : integralTowerModules l L Y)
    (a b : (integralScalarRestrict l L Y n).obj
      ((integralScalarReduction l E L ι Y n).obj M) ⟶ N)
    (h : ∀ U s x, a.val.app U (integralScalarTensorSection l E L ι Y n M U s x) =
      b.val.app U (integralScalarTensorSection l E L ι Y n M U s x)) : a = b := by
  let e := (integralScalarRestrict l L Y n).mapIso
    ((integralScalarReductionIso l E L ι Y n).app M)
  apply (cancel_epi e.inv).mp
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ N.isSheaf
  ext U z
  induction z using TensorProduct.inductionOn with
  | tmul s x => exact h U s x
  | add z w hz hw => simpa only [_root_.map_add] using congrArg₂ (· + ·) hz hw

attribute [local irreducible] integralScalarModuleStepRaw integralScalarModuleStep

private theorem integralScalarReduction_map_tmul (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    ((integralScalarReduction l E L ι Y n).map a).val.app U
        (integralScalarTensorSection l E L ι Y n M U s x) =
      integralScalarTensorSection l E L ι Y n N U s (a.val.app U x) := by
  let e := integralScalarReductionIso l E L ι Y n
  let z := SheafOfModules.UnrestrictedTowerProof.tensorSection
    (integralScalarRho l E L ι Y n) M U s x
  have h := congrArg (fun f ↦ (f.val.app U) z) (e.inv.naturality a).symm
  exact h.trans (congrArg (fun z ↦ ((e.inv.app N).val.app U) z)
    (SheafOfModules.UnrestrictedTowerProof.map_tensorSection
      (integralScalarRho l E L ι Y n) M a U s x))

private theorem integralScalarModuleStep_naturality (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N) :
    (integralScalarRestrict l L Y (n + 1)).map
        ((integralScalarReduction l E L ι Y (n + 1)).map a) ≫
        integralScalarModuleStep l E L ι Y n N =
      integralScalarModuleStep l E L ι Y n M ≫
        (integralScalarRestrict l L Y n).map ((integralScalarReduction l E L ι Y n).map a) := by
  apply integralScalarReduction_hom_ext l E L ι Y (n + 1) M
  intro U s x
  have hm (k : ℕ) (t : (integralCoefficientCommRingSheaf l L Y k).obj.obj U) :
      ((integralScalarReduction l E L ι Y k).map a).val.app U
        (integralScalarTensorSection l E L ι Y k M U t x) =
      integralScalarTensorSection l E L ι Y k N U t (a.val.app U x) := by
    exact integralScalarReduction_map_tmul l E L ι Y k a U t x
  change (integralScalarModuleStep l E L ι Y n N).val.app U
      (((integralScalarReduction l E L ι Y (n + 1)).map a).val.app U _) =
    ((integralScalarReduction l E L ι Y n).map a).val.app U
      ((integralScalarModuleStep l E L ι Y n M).val.app U _)
  rw [hm, integralScalarModuleStep_tmul, integralScalarModuleStep_tmul, hm]

/-- The transition is the unique natural chain map sending s⊗x to red(s)⊗x.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: integralScalarQuotientMap_transition and functoriality of constant sheafification
make ρ_n equal to reduction after ρ_(n+1). The stated tensor formula is therefore
balanced. The target limit projections make it linear over the target completion.
It commutes with restrictions, differentials and maps in P; sheafification gives τ.
Pure tensors generate locally, so the formula determines τ uniquely. -/
theorem integralScalarTransition_existsUnique (n : ℕ) :
    ∃! τ : integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj U)
        (x : (P.X i).val.obj U),
        ((τ.app P).f i).val.app U
          (integralScalarTensorSection l E L ι Y (n + 1) (P.X i) U s x) =
        integralScalarTensorSection l E L ι Y n (P.X i) U
          ((integralCoefficientSheafTransition l L Y n).hom.app U s) x := by
  let τ : integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n :=
    { app := fun P ↦
        { f := fun i ↦ integralScalarModuleStep l E L ι Y n (P.X i)
          comm' := fun i j _ ↦ (integralScalarModuleStep_naturality l E L ι Y n
            (P.d i j)).symm }
      naturality := fun P Q a ↦ by
        apply HomologicalComplex.hom_ext
        intro i
        exact integralScalarModuleStep_naturality l E L ι Y n (a.f i) }
  refine ⟨τ, (fun P i U s x ↦ integralScalarModuleStep_tmul l E L ι Y n (P.X i) U s x), ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply integralScalarReduction_hom_ext l E L ι Y (n + 1) (P.X i)
  intro U s x
  exact (hτ' P i U s x).trans (integralScalarModuleStep_tmul l E L ι Y n (P.X i) U s x).symm

end ScalarTransitions

/-- The canonical transition, selected from a theorem that determines it uniquely.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarTransition (n : ℕ) :
    integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n :=
  (integralScalarTransition_existsUnique l E L ι Y n).exists.choose

/-- The strict tower, including its action on all chain maps.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarTowerFunctor :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l L Y) ℤ) :=
  (Functor.ofOpSequence (X := fun n ↦ integralScalarLevel l E L ι Y n)
    (integralScalarTransition l E L ι Y)).flip

/-- The fixed Cone(1-s)[-1] functor with termwise products and diagonal cone maps.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarComplexFunctor :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      CochainComplex (integralTowerModules l L Y) ℤ :=
  integralScalarTowerFunctor l E L ι Y ⋙ integralOperationsRoosFunctor

/-- The specified Roos construction on K-flat flat-term representatives, localized.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarOnGood :=
  (integralOperationsGoodComplex l E Y).ι ⋙
    integralScalarComplexFunctor l E L ι Y ⋙ DerivedCategory.Q

/-- The constant section of the finite ring sheaf represented by a modulo ϖ_E^(n+1).
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarFiniteConstant (n : ℕ) (U : Y.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (integralCoefficientSheaf l E Y n).obj.obj U :=
  ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U)
        (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a))

section ScalarConstants

universe cs vs rs is js

private theorem ringSheafLimit_ext
    {C : Type cs} [Category.{vs} C] {J : GrothendieckTopology C}
    {I : Type is} [Category.{js} I] (D : I ⥤ Sheaf J RingCat.{rs})
    [HasLimit D] [PreservesLimit D (sheafToPresheaf J RingCat)]
    (U : Cᵒᵖ)
    [PreservesLimit (D ⋙ sheafToPresheaf J RingCat) ((evaluation _ _).obj U)]
    [PreservesLimit ((D ⋙ sheafToPresheaf J RingCat) ⋙ (evaluation _ _).obj U)
      (forget RingCat)]
    (x y : (limit D).obj.obj U)
    (h : ∀ i, ((limit.π D i).hom.app U) x = ((limit.π D i).hom.app U) y) : x = y := by
  let h₁ := isLimitOfPreserves (sheafToPresheaf J RingCat) (limit.isLimit D)
  let h₂ := isLimitOfPreserves ((evaluation _ _).obj U) h₁
  exact Concrete.isLimit_ext _ h₂ x y h

attribute [local irreducible] limit

/-- The constant section of the completion is determined by all its finite residues.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: The displayed finite constant sections commute with reduction, because both
orders send a to its class. Limits of ring sheaves are sectionwise. Their universal
property supplies the compatible tuple, and the projections are jointly injective. -/
theorem integralScalarConstant_existsUnique (U : Y.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    ∃! s : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U,
      ∀ n : ℕ,
        ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U) s =
          integralScalarFiniteConstant l E Y n U a := by
  let b : (integralConstantRingOfUniverses l E Y).obj.obj U :=
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U)
      (ULift.up a)
  let s := (integralConstantToCompletionOfUniverses l E Y).hom.app U b
  have hs : ∀ n : ℕ,
      ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U) s =
        integralScalarFiniteConstant l E Y n U a := by
    intro n
    have hπ := congrArg (fun f ↦ f.hom.app U)
      (limit.lift_π (integralConstantConeOfUniverses l E Y) (op n))
    have hcomp :
        (integralConstantToCompletionOfUniverses l E Y).hom.app U ≫
            (limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U =
          ((integralConstantConeOfUniverses l E Y).π.app (op n)).hom.app U := by
      change (limit.lift (integralCoefficientSheafSystem l E Y)
          (integralConstantConeOfUniverses l E Y)).hom.app U ≫
          (limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U = _
      exact hπ
    have hb := congrArg (fun f ↦ f.hom b) hcomp
    change ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U).hom
      (((integralConstantToCompletionOfUniverses l E Y).hom.app U).hom b) = _ at hb
    change ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U).hom
      (((integralConstantToCompletionOfUniverses l E Y).hom.app U).hom b) = _
    refine hb.trans ?_
    let q := CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
    have hn := congrArg (fun f ↦ (f.app U).hom (ULift.up a))
      (toSheafify_naturality (AlgebraicGeometry.Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).map q))
    exact hn.symm
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  exact ringSheafLimit_ext (integralCoefficientSheafSystem l E Y) U s' s
    (fun n ↦ (hs' n.unop).trans (hs n.unop).symm)

/-- The unique constant global section, restricted to the site object U.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarConstant (U : Y.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  (integralScalarConstant_existsUnique l E Y U a).exists.choose

private theorem integralScalarConstant_naturality {U V : Y.ProEtᵒᵖ}
    (f : U ⟶ V) (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
      (integralScalarConstant l E Y U a) = integralScalarConstant l E Y V a := by
  apply ringSheafLimit_ext (integralCoefficientSheafSystem l E Y) V
  intro n
  change ((limit.π (integralCoefficientSheafSystem l E Y) n).hom.app V)
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
        (integralScalarConstant l E Y U a)) =
    ((limit.π (integralCoefficientSheafSystem l E Y) n).hom.app V)
      (integralScalarConstant l E Y V a)
  have hn := congrArg (fun k ↦ k.hom (integralScalarConstant l E Y U a))
    ((limit.π (integralCoefficientSheafSystem l E Y) n).hom.naturality f)
  change ((limit.π (integralCoefficientSheafSystem l E Y) n).hom.app V)
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
        (integralScalarConstant l E Y U a)) =
      (integralCoefficientSheaf l E Y n.unop).obj.map f
        (((limit.π (integralCoefficientSheafSystem l E Y) n).hom.app U)
          (integralScalarConstant l E Y U a)) at hn
  rw [hn]
  erw [(integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n.unop,
    (integralScalarConstant_existsUnique l E Y V a).exists.choose_spec n.unop]
  have h := congrArg
    (fun k ↦ k.hom
      (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))) a)))
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1)))))).naturality f)
  exact h.symm

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private noncomputable def integralScalarModuleAction
    (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (SheafOfModules.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E Y)) ⟶ 𝟭 (SheafOfModules.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E Y)) where
  app M :=
    { val :=
        { app := fun U ↦ by
            let := completedIntegralCoefficientCommRingUnrestricted l E Y U
            exact ModuleCat.ofHom
              { toFun := fun x ↦ integralScalarConstant l E Y U a • x
                map_add' := smul_add _
                map_smul' := fun r x ↦ smul_comm _ r x }
          naturality := by
            intro U V f
            ext x
            change integralScalarConstant l E Y V a • M.val.map f x =
              M.val.map f (integralScalarConstant l E Y U a • x)
            rw [M.val.map_smul, integralScalarConstant_naturality l E Y f a] } }
  naturality := by
    intro M N f
    ext U x
    exact ((f.val.app U).hom.map_smul (integralScalarConstant l E Y U a) x).symm

/-- Multiplication by the constant section is a uniquely specified natural chain map.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: The sections from integralScalarConstant are compatible with restrictions by
their uniqueness and their finite residue formulas. Multiplication is linear over
the completed commutative ring. It commutes with differentials and module maps,
giving σ. Equality on every degree and every section proves uniqueness. -/
theorem integralScalarChainAction_existsUnique (a : Padic.coefficientExtensionIntegers l E) :
    ∃! σ : 𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) ⟶
        𝟭 (CochainComplex (integralTowerModules l E Y) ℤ),
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (x : (P.X i).val.obj U),
        ((σ.app P).f i).val.app U x = integralScalarConstant l E Y U a • x := by
  let σ := (integralScalarModuleAction l E Y a).mapHomologicalComplex (.up ℤ)
  refine ⟨σ, ?_, ?_⟩
  · intro P i U x
    rfl
  · intro σ' hσ'
    apply NatTrans.ext
    funext P
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hσ' P i U x

/-- The actual constant-section scalar endomorphism of the identity on complexes.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarChainAction (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) ⟶
      𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) :=
  (integralScalarChainAction_existsUnique l E Y a).exists.choose

/-- The canonical scalar endomorphism after localization. Its composite with f is a f;
this is the constant-section action of lem-weil-linear-abelian-derived-category.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarDerivedAction (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (DerivedCategory (integralTowerModules l E Y)) ⟶
      𝟭 (DerivedCategory (integralTowerModules l E Y)) :=
  (existsUnique_eq (a' :=
    (Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (ComplexShape.up ℤ))
      (DerivedCategory (integralTowerModules l E Y))).preimage (X := 𝟭 _) (Y := 𝟭 _)
        (whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)
  )).exists.choose

-- Equality to the canonical fully faithful lift keeps its component API explicit.
private theorem integralScalarDerivedAction_eq_preimage
    (a : Padic.coefficientExtensionIntegers l E) :
    integralScalarDerivedAction l E Y a =
    (Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (ComplexShape.up ℤ))
      (DerivedCategory (integralTowerModules l E Y))).preimage (X := 𝟭 _) (Y := 𝟭 _)
        (whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q) := by
  exact (existsUnique_eq (a' :=
      (Localization.fullyFaithfulWhiskeringLeft
        (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
        (HomologicalComplex.quasiIso (integralTowerModules l E Y) (ComplexShape.up ℤ))
        (DerivedCategory (integralTowerModules l E Y))).preimage (X := 𝟭 _) (Y := 𝟭 _)
          (whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)
  )).exists.choose_spec

end ScalarConstants

namespace ScalarConeProof
open CochainComplex
universe v a b
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
variable {C : Type a} [Category.{b} C]
private noncomputable def squareIso {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L') (e : K ≅ K') (e' : L ≅ L')
    (h : f ≫ e'.hom = e.hom ≫ f') : mappingCone f ≅ mappingCone f' where
  hom := mappingCone.map f f' e.hom e'.hom h
  inv := mappingCone.map f' f e.inv e'.inv (by
    rw [← cancel_epi e.hom, ← cancel_mono e'.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc, h])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simpa only [Iso.hom_inv_id] using mappingCone.map_id f
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simpa only [Iso.inv_hom_id] using mappingCone.map_id f'
private noncomputable def coneFunctor {F G : C ⥤ CochainComplex A ℤ} (τ : F ⟶ G) :
    C ⥤ CochainComplex A ℤ where
  obj X := mappingCone (τ.app X)
  map f := mappingCone.map _ _ (F.map f) (G.map f) (τ.naturality f).symm
  map_id X := by
    ext i
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map]
  map_comp f g := by
    ext i
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map]
private local instance coneAdditive [Preadditive C] {F G : C ⥤ CochainComplex A ℤ}
    [F.Additive] [G.Additive] (τ : F ⟶ G) : (coneFunctor τ).Additive where
  map_add := by
    intro X Y f g
    ext i
    apply mappingCone.ext_from (τ.app X) (i + 1) i rfl
    all_goals simp [coneFunctor, mappingCone.map, Preadditive.comp_add,
      Preadditive.add_comp]
private noncomputable def coneFunctorIso {F G F' G' : C ⥤ CochainComplex A ℤ}
    {τ : F ⟶ G} {τ' : F' ⟶ G'} (e : F ≅ F') (d : G ≅ G')
    (h : τ ≫ d.hom = e.hom ≫ τ') : coneFunctor τ ≅ coneFunctor τ' := by
  refine NatIso.ofComponents (fun X ↦ squareIso _ _ (e.app X) (d.app X)
    (congrArg (fun k ↦ k.app X) h)) ?_
  intro X Y f
  dsimp only [coneFunctor, squareIso, NatIso.ofComponents]
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  congr 1
  · exact e.hom.naturality f
  · exact d.hom.naturality f
variable [HasShift C ℤ] {F G : C ⥤ CochainComplex A ℤ}
  [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
private noncomputable def coneShiftObj (X : C) (m : ℤ) :
    (coneFunctor τ).obj (X⟦m⟧) ≅ ((coneFunctor τ).obj X)⟦m⟧ :=
  squareIso (τ.app (X⟦m⟧)) ((τ.app X)⟦m⟧')
    ((F.commShiftIso m).app X) ((G.commShiftIso m).app X)
    (NatTrans.shift_app_comm τ m X).symm ≪≫ (mappingCone.shiftIso (τ.app X) m).symm
private theorem coneShift_naturality {X Y : C} (f : X ⟶ Y) (m : ℤ) :
    (coneFunctor τ).map (f⟦m⟧') ≫ (coneShiftObj τ Y m).hom =
      (coneShiftObj τ X m).hom ≫ ((coneFunctor τ).map f)⟦m⟧' := by
  ext i
  apply mappingCone.ext_from (τ.app (X⟦m⟧)) (i + 1) i rfl
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, shiftFunctor_obj_X', coneShiftObj,
      squareIso, Iso.app_hom, Iso.app_inv, mappingCone.shiftIso, Iso.symm_mk, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inl_v_desc_f_assoc,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v, Category.assoc,
      mappingCone.inl_v_desc_f, HomComplex.Cochain.units_smul_v, HomComplex.Cochain.shift_v',
      Linear.comp_units_smul, shiftFunctor_map_f', Linear.units_smul_comp, smul_left_cancel_iff]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simpa only [HomologicalComplex.comp_f, Functor.comp_map,
      CochainComplex.shiftFunctor_map_f'] using
      congrArg (fun g ↦ g.f (i + 1)) ((F.commShiftIso m).hom.naturality f)
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, shiftFunctor_obj_X', coneShiftObj,
      squareIso, Iso.app_hom, Iso.app_inv, mappingCone.shiftIso, Iso.symm_mk, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inr_f_desc_f_assoc, Category.assoc,
      mappingCone.inr_f_desc_f, shiftFunctor_map_f']
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simpa only [HomologicalComplex.comp_f, Functor.comp_map,
      CochainComplex.shiftFunctor_map_f'] using
      congrArg (fun g ↦ g.f i) ((G.commShiftIso m).hom.naturality f)
private noncomputable def coneShiftIso (m : ℤ) :
    CategoryTheory.shiftFunctor C m ⋙ coneFunctor τ ≅
      coneFunctor τ ⋙ CategoryTheory.shiftFunctor _ m :=
  NatIso.ofComponents (fun X ↦ coneShiftObj τ X m) (fun f ↦ coneShift_naturality τ f m)

omit [HasBinaryBiproducts A] in
private theorem cochain_cast {K L : CochainComplex A ℤ} {n : ℤ}
    (γ : HomComplex.Cochain K L n) {p p' q q' : ℤ} (hp : p = p') (hq : q = q')
    (h : p + n = q) (h' : p' + n = q') :
    (HomologicalComplex.XIsoOfEq K hp).inv ≫ γ.v p q h =
      γ.v p' q' h' ≫ (HomologicalComplex.XIsoOfEq L hq).inv := by
  subst hp
  subst hq
  simp
private theorem coneShiftIso_zero :
    coneShiftIso τ 0 = Functor.CommShift.isoZero (coneFunctor τ) ℤ := by
  ext X i
  apply mappingCone.ext_from (τ.app (X⟦(0 : ℤ)⟧)) (i + 1) i rfl
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, Functor.comp_obj,
      shiftFunctor_obj_X', coneShiftIso, coneShiftObj, squareIso, Functor.commShiftIso_zero,
      Iso.app_hom, Functor.CommShift.isoZero_hom_app, shiftFunctorZero_eq,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      Category.assoc, Iso.app_inv, Functor.CommShift.isoZero_inv_app, mappingCone.shiftIso,
      Int.negOnePow_zero, one_smul, Iso.symm_mk, NatIso.ofComponents_hom_app, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inl_v_desc_f_assoc,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v,
      shiftFunctorZero'_inv_app_f, mappingCone.inl_v_desc_f, HomComplex.Cochain.shift_v']
    rw [cochain_cast]
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, Functor.comp_obj,
      shiftFunctor_obj_X', coneShiftIso, coneShiftObj, squareIso, Functor.commShiftIso_zero,
      Iso.app_hom, Functor.CommShift.isoZero_hom_app, shiftFunctorZero_eq,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      Category.assoc, Iso.app_inv, Functor.CommShift.isoZero_inv_app, mappingCone.shiftIso,
      Int.negOnePow_zero, one_smul, Iso.symm_mk, NatIso.ofComponents_hom_app, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inr_f_desc_f_assoc, shiftFunctorZero'_inv_app_f,
      mappingCone.inr_f_desc_f, shiftFunctor_map_f']
    rw [← HomologicalComplex.XIsoOfEq_inv_naturality]

private theorem coneShiftIso_add (a b : ℤ) :
    coneShiftIso τ (a + b) = Functor.CommShift.isoAdd (coneShiftIso τ a) (coneShiftIso τ b) := by
  ext X i
  apply mappingCone.ext_from (τ.app (X⟦a + b⟧)) (i + 1) i rfl
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, Functor.comp_obj,
      shiftFunctor_obj_X', coneShiftIso, coneShiftObj, squareIso, Functor.commShiftIso_add,
      Iso.app_hom, Functor.CommShift.isoAdd_hom_app, shiftFunctorAdd_eq,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      Category.assoc, Iso.app_inv, Functor.CommShift.isoAdd_inv_app, mappingCone.shiftIso,
      add_comm a b, Iso.symm_mk, NatIso.ofComponents_hom_app, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inl_v_desc_f_assoc,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v, shiftFunctor_map_f',
      shiftFunctorAdd'_inv_app_f, mappingCone.inl_v_desc_f, HomComplex.Cochain.units_smul_v,
      HomComplex.Cochain.shift_v', Linear.comp_units_smul, Functor.map_comp,
      Linear.units_smul_comp, smul_smul, ← Int.negOnePow_add, smul_left_cancel_iff]
    rw [cochain_cast]
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, Functor.comp_obj,
      shiftFunctor_obj_X', coneShiftIso, coneShiftObj, squareIso, Functor.commShiftIso_add,
      Iso.app_hom, Functor.CommShift.isoAdd_hom_app, shiftFunctorAdd_eq,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      Category.assoc, Iso.app_inv, Functor.CommShift.isoAdd_inv_app, mappingCone.shiftIso,
      add_comm a b, Iso.symm_mk, NatIso.ofComponents_hom_app, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inr_f_desc_f_assoc, shiftFunctor_map_f',
      shiftFunctorAdd'_inv_app_f, mappingCone.inr_f_desc_f, Functor.map_comp]
    rw [← HomologicalComplex.XIsoOfEq_inv_naturality]

@[instance_reducible]
private noncomputable def coneCommShift : (coneFunctor τ).CommShift ℤ where
  commShiftIso := coneShiftIso τ
  commShiftIso_zero := coneShiftIso_zero τ
  commShiftIso_add := coneShiftIso_add τ

end ScalarConeProof

attribute [local irreducible] ScalarConeProof.coneCommShift

namespace ScalarModuleRoosProof
open CochainComplex
attribute [local instance] ScalarConeProof.coneAdditive
universe v a b
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type a} [Category.{b} B] [Preadditive B] [HasLimitsOfShape (Discrete ℕ) B]
private noncomputable def modulePi (F : ℕ → A ⥤ B) : A ⥤ B where
  obj X := ∏ᶜ (fun n ↦ (F n).obj X)
  map f := Limits.Pi.map (fun n ↦ (F n).map f)
  map_id X := by apply Pi.hom_ext; intro n; simp
  map_comp f g := by apply Pi.hom_ext; intro n; simp
private local instance (F : ℕ → A ⥤ B) [∀ n, (F n).Additive] : (modulePi F).Additive where
  map_add := by
    intros
    dsimp only [modulePi]
    apply Pi.hom_ext
    intro n
    simp [Preadditive.add_comp]
private noncomputable def modulePiProjection (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (P : CochainComplex A ℤ) (n : ℕ) :
    ((modulePi F).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((F n).mapHomologicalComplex (.up ℤ)).obj P where
  f i := Pi.π (fun n ↦ (F n).obj (P.X i)) n
  comm' i j hij := by simp [modulePi]
private noncomputable def modulePiFan (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (P : CochainComplex A ℤ) :
    Fan (fun n ↦ ((F n).mapHomologicalComplex (.up ℤ)).obj P) :=
  Fan.mk _ (modulePiProjection F P)
private noncomputable def modulePiIsLimit (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (P : CochainComplex A ℤ) : IsLimit (modulePiFan F P) := by
  apply HomologicalComplex.isLimitOfEval
  intro i
  refine { lift := fun s ↦ Pi.lift (fun n ↦ s.π.app ⟨n⟩)
           fac := ?_
           uniq := ?_ }
  · intro s n
    exact Pi.lift_comp_π _ n.as
  · intro s m hm
    apply Pi.hom_ext
    intro n
    simpa [Pi.lift_comp_π, modulePiFan, modulePiProjection, modulePi] using hm ⟨n⟩
private noncomputable def modulePiIso (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (P : CochainComplex A ℤ) :
    ((modulePi F).mapHomologicalComplex (.up ℤ)).obj P ≅
      ∏ᶜ (fun n ↦ ((F n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (modulePiIsLimit F P).conePointUniqueUpToIso (limit.isLimit _)
private noncomputable def complexPi (F : ℕ → A ⥤ B) [∀ n, (F n).Additive] :
    CochainComplex A ℤ ⥤ CochainComplex B ℤ where
  obj P := ∏ᶜ (fun n ↦ ((F n).mapHomologicalComplex (.up ℤ)).obj P)
  map f := Limits.Pi.map (fun n ↦ ((F n).mapHomologicalComplex (.up ℤ)).map f)
  map_id P := by apply Pi.hom_ext; intro n; simp
  map_comp f g := by apply Pi.hom_ext; intro n; simp
@[reassoc (attr := simp)]
private theorem modulePiIso_hom_π (F : ℕ → A ⥤ B) [∀ n, (F n).Additive]
    (P : CochainComplex A ℤ) (n : ℕ) :
    (modulePiIso F P).hom ≫ Pi.π _ n = modulePiProjection F P n :=
  (modulePiIsLimit F P).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨n⟩
private theorem modulePiIso_naturality (F : ℕ → A ⥤ B) [∀ n, (F n).Additive]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) :
    ((modulePi F).mapHomologicalComplex (.up ℤ)).map f ≫ (modulePiIso F Q).hom =
      (modulePiIso F P).hom ≫ (complexPi F).map f := by
  apply Pi.hom_ext
  intro n
  simp only [complexPi, Category.assoc, modulePiIso_hom_π, Pi.map_π,
    modulePiIso_hom_π_assoc]
  ext i
  simp [modulePiProjection, modulePi]

private noncomputable def modulePiComparison (F : ℕ → A ⥤ B) [∀ n, (F n).Additive] :
    (modulePi F).mapHomologicalComplex (.up ℤ) ≅ complexPi F :=
  NatIso.ofComponents (F := (modulePi F).mapHomologicalComplex (.up ℤ))
    (G := complexPi F) (modulePiIso F) (modulePiIso_naturality F)
private noncomputable def modulePiEndo (F : ℕ → A ⥤ B) (τ : ∀ n, F (n + 1) ⟶ F n) :
    modulePi F ⟶ modulePi F where
  app X := 𝟙 _ - Pi.lift (fun n ↦ Pi.π _ (n + 1) ≫ (τ n).app X)
  naturality := by
    intro X Y f
    apply Pi.hom_ext
    intro n
    simp [modulePi, Preadditive.comp_sub, Preadditive.sub_comp, (τ n).naturality]

private noncomputable def complexPiEndo (F : ℕ → A ⥤ B) [∀ n, (F n).Additive]
    (τ : ∀ n, F (n + 1) ⟶ F n) : complexPi F ⟶ complexPi F where
  app P := towerTransitionEndomorphism
    (fun n ↦ ((τ n).mapHomologicalComplex (.up ℤ)).app P)
  naturality := by
    intro X Y f
    exact towerTransitionEndomorphism_natural_backward
      (K := fun n ↦ ((F n).mapHomologicalComplex (.up ℤ)).obj X)
      (K' := fun n ↦ ((F n).mapHomologicalComplex (.up ℤ)).obj Y)
      (fun n ↦ ((τ n).mapHomologicalComplex (.up ℤ)).app X)
      (fun n ↦ ((τ n).mapHomologicalComplex (.up ℤ)).app Y)
      (fun n ↦ ((F n).mapHomologicalComplex (.up ℤ)).map f)
      (fun n ↦ ((τ n).mapHomologicalComplex (.up ℤ)).naturality f)
private theorem modulePiEndo_comparison (F : ℕ → A ⥤ B) [∀ n, (F n).Additive]
    (τ : ∀ n, F (n + 1) ⟶ F n) :
    (modulePiEndo F τ).mapHomologicalComplex (.up ℤ) ≫ (modulePiComparison F).hom =
      (modulePiComparison F).hom ≫ complexPiEndo F τ := by
  apply NatTrans.ext
  funext P
  dsimp only [modulePiComparison, complexPi, modulePi]
  apply Pi.hom_ext
  intro n
  simp only [NatTrans.comp_app, Category.assoc,
    NatIso.ofComponents_hom_app, modulePiIso_hom_π]
  simp only [complexPiEndo, towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp,
    Pi.lift_comp_π, modulePiIso_hom_π_assoc]
  ext i
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    HomologicalComplex.sub_f_apply]
  rw [HomologicalComplex.id_f, Category.id_comp,
    ← HomologicalComplex.comp_f, modulePiIso_hom_π]
  dsimp only [modulePiEndo, modulePiProjection]
  simp only [Preadditive.sub_comp, Pi.lift_comp_π]
  congr 1
  exact Category.id_comp (Pi.π (fun n ↦ (F n).obj (P.X i)) n)
private local instance termwiseNatTrans_commShift {F G : A ⥤ B} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : NatTrans.CommShift (τ.mapHomologicalComplex (.up ℤ)) ℤ where
  shift_comm n := by
    ext P i
    simp [CochainComplex.shiftFunctor_map_f']

private local instance complexPi_additive (F : ℕ → A ⥤ B) [∀ n, (F n).Additive] :
    (complexPi F).Additive :=
  Functor.additive_of_iso (modulePiComparison F)
private theorem complexCone_structure [HasBinaryBiproducts B]
    (F : ℕ → A ⥤ B) [∀ n, (F n).Additive] (τ : ∀ n, F (n + 1) ⟶ F n) :
    (ScalarConeProof.coneFunctor (complexPiEndo F τ) ⋙
      CategoryTheory.shiftFunctor _ (-1 : ℤ)).Additive ∧
    Nonempty ((ScalarConeProof.coneFunctor (complexPiEndo F τ) ⋙
      CategoryTheory.shiftFunctor _ (-1 : ℤ)).CommShift ℤ) := by
  let e := ScalarConeProof.coneFunctorIso (modulePiComparison F) (modulePiComparison F)
    (modulePiEndo_comparison F τ)
  let := ScalarConeProof.coneCommShift
    ((modulePiEndo F τ).mapHomologicalComplex (.up ℤ))
  let := Functor.CommShift.ofIso e ℤ
  exact ⟨inferInstance, ⟨inferInstance⟩⟩
end ScalarModuleRoosProof

attribute [local irreducible] ScalarModuleRoosProof.modulePiComparison

namespace RoosComparisonProof
open CochainComplex
universe v a b
open WeilConjectures
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type a} [Category.{b} B] [Abelian B] [HasCountableProducts B]
omit [HasCountableProducts B] in
private theorem coneEq_naturality {K K' : CochainComplex B ℤ}
    (s t : K ⟶ K) (s' t' : K' ⟶ K') (hs : s = t) (hs' : s' = t')
    (a : K ⟶ K') (h : s ≫ a = a ≫ s') (h' : t ≫ a = a ≫ t') :
    (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map (mappingCone.map s s' a a h) ≫
        eqToHom (congrArg (fun k : K' ⟶ K' ↦ mappingCocone k) hs') =
      eqToHom (congrArg (fun k : K ⟶ K ↦ mappingCocone k) hs) ≫
        (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map (mappingCone.map t t' a a h') := by
  subst hs
  subst hs'
  simp
private noncomputable def strictRoos (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (τ : ∀ n, F (n + 1) ⟶ F n) :=
  (Functor.ofOpSequence (X := fun n ↦ (F n).mapHomologicalComplex (.up ℤ))
    (fun n ↦ (τ n).mapHomologicalComplex (.up ℤ))).flip ⋙ integralOperationsRoosFunctor
private theorem strictRoos_of_termwise (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (τ : ∀ n, F (n + 1) ⟶ F n)
    (σ : ∀ n, (F (n + 1)).mapHomologicalComplex (.up ℤ) ⟶
      (F n).mapHomologicalComplex (.up ℤ))
    (h : σ = fun n ↦ (τ n).mapHomologicalComplex (.up ℤ)) :
    (Functor.ofOpSequence (X := fun n ↦ (F n).mapHomologicalComplex (.up ℤ)) σ).flip ⋙
      integralOperationsRoosFunctor = strictRoos F τ := by
  subst h
  rfl

private theorem endo_eq (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (τ : ∀ n, F (n + 1) ⟶ F n)
    (P : CochainComplex A ℤ) :
    towerTransitionEndomorphism
      (K := fun n ↦ ((F n).mapHomologicalComplex (.up ℤ)).obj P)
      (integralOperationsTowerStep
        ((Functor.ofOpSequence (X := fun n ↦ (F n).mapHomologicalComplex (.up ℤ))
          (fun n ↦ (τ n).mapHomologicalComplex (.up ℤ))).flip.obj P)) =
      (ScalarModuleRoosProof.complexPiEndo F τ).app P := by
  congr 1
  funext n
  simp only [integralOperationsTowerStep, Functor.flip_obj_map,
    Functor.ofOpSequence_map_homOfLE_succ]
private theorem strictRoosIso_naturality (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (τ : ∀ n, F (n + 1) ⟶ F n)
    {P P' : CochainComplex A ℤ} (f : P ⟶ P') :
    (strictRoos F τ).map f ≫
        (eqToIso (congrArg (fun k ↦ mappingCocone k) (endo_eq F τ P'))).hom =
      (eqToIso (congrArg (fun k ↦ mappingCocone k) (endo_eq F τ P))).hom ≫
        (ScalarConeProof.coneFunctor (ScalarModuleRoosProof.complexPiEndo F τ) ⋙
          CategoryTheory.shiftFunctor _ (-1 : ℤ)).map f := by
  simp only [eqToIso.hom]
  dsimp only [strictRoos, Functor.comp_map, integralOperationsRoosFunctor,
    ScalarConeProof.coneFunctor]
  unfold integralOperationsRoosMap
  rw [WeilConjectures.cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square _)]
  exact coneEq_naturality _ _ _ _ (endo_eq F τ P) (endo_eq F τ P') _ _ _

private noncomputable def strictRoosIso (F : ℕ → A ⥤ B)
    [∀ n, (F n).Additive] (τ : ∀ n, F (n + 1) ⟶ F n) :
    strictRoos F τ ≅ ScalarConeProof.coneFunctor
      (ScalarModuleRoosProof.complexPiEndo F τ) ⋙ CategoryTheory.shiftFunctor _ (-1 : ℤ) :=
  NatIso.ofComponents (F := strictRoos F τ)
    (G := ScalarConeProof.coneFunctor (ScalarModuleRoosProof.complexPiEndo F τ) ⋙
      CategoryTheory.shiftFunctor _ (-1 : ℤ))
    (fun P ↦ eqToIso (congrArg (fun k ↦ mappingCocone k) (endo_eq F τ P)))
    (strictRoosIso_naturality F τ)

private def complexAction {D : Type*} [Category D] [Preadditive D]
    (μ : 𝟭 D ⟶ 𝟭 D) : 𝟭 (CochainComplex D ℤ) ⟶ 𝟭 (CochainComplex D ℤ) :=
  μ.mapHomologicalComplex (.up ℤ)
omit [HasCountableProducts B] in
private theorem coneAction (μ : 𝟭 B ⟶ 𝟭 B) {K L : CochainComplex B ℤ}
    (f : K ⟶ L) :
    mappingCone.map f f ((complexAction μ).app K)
      ((complexAction μ).app L)
      ((complexAction μ).naturality f) =
    (complexAction μ).app (mappingCone f) := by
  ext i
  apply mappingCone.ext_from f (i + 1) i rfl
  · simp only [Int.reduceNeg, mappingCone.map, mappingCone.inl_v_desc_f,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v]
    exact (μ.naturality _).symm
  · simp only [mappingCone.map, Int.reduceNeg, mappingCone.inr_f_desc_f,
      HomologicalComplex.comp_f]
    exact (μ.naturality _).symm
private theorem productAction (F : ℕ → A ⥤ B) [∀ n, (F n).Additive]
    (μ : 𝟭 A ⟶ 𝟭 A) (ν : 𝟭 B ⟶ 𝟭 B)
    (h : ∀ n X, (F n).map (μ.app X) = ν.app ((F n).obj X))
    (P : CochainComplex A ℤ) :
    (ScalarModuleRoosProof.complexPi F).map
        ((complexAction μ).app P) =
      (complexAction ν).app
        ((ScalarModuleRoosProof.complexPi F).obj P) := by
  apply Pi.hom_ext
  intro n
  dsimp only [ScalarModuleRoosProof.complexPi]
  rw [Pi.map_π]
  have hn : ((F n).mapHomologicalComplex (.up ℤ)).map
      ((complexAction μ).app P) =
      (complexAction ν).app
        (((F n).mapHomologicalComplex (.up ℤ)).obj P) := by
    ext i
    exact h n (P.X i)
  rw [hn]
  exact (complexAction ν).naturality (Pi.π _ n)
omit [HasCountableProducts B] in
private theorem coneMap_diag_eq {K : CochainComplex B ℤ} (s : K ⟶ K)
    (a b : K ⟶ K) (ha : a = b) (h : s ≫ a = a ≫ s) (h' : s ≫ b = b ≫ s) :
    mappingCone.map s s a a h = mappingCone.map s s b b h' := by
  subst ha
  rfl
private theorem coneFunctorAction (F : ℕ → A ⥤ B) [∀ n, (F n).Additive]
    (τ : ∀ n, F (n + 1) ⟶ F n) (μ : 𝟭 A ⟶ 𝟭 A) (ν : 𝟭 B ⟶ 𝟭 B)
    (h : ∀ n X, (F n).map (μ.app X) = ν.app ((F n).obj X))
    (P : CochainComplex A ℤ) :
    (ScalarConeProof.coneFunctor (ScalarModuleRoosProof.complexPiEndo F τ) ⋙
      CategoryTheory.shiftFunctor _ (-1 : ℤ)).map
        ((complexAction μ).app P) =
      (complexAction ν).app
        ((ScalarConeProof.coneFunctor (ScalarModuleRoosProof.complexPiEndo F τ) ⋙
          CategoryTheory.shiftFunctor _ (-1 : ℤ)).obj P) := by
  let s := (ScalarModuleRoosProof.complexPiEndo F τ).app P
  let g := (ScalarModuleRoosProof.complexPi F).map ((complexAction μ).app P)
  have hg : s ≫ g = g ≫ s :=
    ((ScalarModuleRoosProof.complexPiEndo F τ).naturality ((complexAction μ).app P)).symm
  have hg' : s ≫ (complexAction ν).app ((ScalarModuleRoosProof.complexPi F).obj P) =
      (complexAction ν).app ((ScalarModuleRoosProof.complexPi F).obj P) ≫ s :=
    (complexAction ν).naturality s
  have hc := (coneMap_diag_eq s g _ (productAction F μ ν h P) hg hg').trans
    (coneAction ν s)
  exact congrArg ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map) hc

private theorem strictRoosAction (F : ℕ → A ⥤ B) [∀ n, (F n).Additive]
    (τ : ∀ n, F (n + 1) ⟶ F n) (μ : 𝟭 A ⟶ 𝟭 A) (ν : 𝟭 B ⟶ 𝟭 B)
    (h : ∀ n X, (F n).map (μ.app X) = ν.app ((F n).obj X))
    (P : CochainComplex A ℤ) :
    (strictRoos F τ).map ((complexAction μ).app P) =
      (complexAction ν).app ((strictRoos F τ).obj P) := by
  let e := strictRoosIso F τ
  apply (cancel_mono (e.hom.app P)).mp
  exact (e.hom.naturality ((complexAction μ).app P)).trans
    ((congrArg (fun k ↦ e.hom.app P ≫ k) (coneFunctorAction F τ μ ν h P)).trans
      ((complexAction ν).naturality (e.hom.app P)))

private theorem action_of_termwise (F : ℕ → A ⥤ B) [∀ n, (F n).Additive]
    (τ : ∀ n, F (n + 1) ⟶ F n)
    (T : CochainComplex A ℤ ⥤ CochainComplex B ℤ) (hT : T = strictRoos F τ)
    (μ : 𝟭 A ⟶ 𝟭 A) (ν : 𝟭 B ⟶ 𝟭 B)
    (α : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 (CochainComplex A ℤ))
    (β : 𝟭 (CochainComplex B ℤ) ⟶ 𝟭 (CochainComplex B ℤ))
    (hα : α = complexAction μ) (hβ : β = complexAction ν)
    (hF : ∀ n M, (F n).map (μ.app M) = ν.app ((F n).obj M))
    (P : CochainComplex A ℤ) : T.map (α.app P) = β.app (T.obj P) := by
  subst hT
  subst hα
  subst hβ
  exact strictRoosAction F τ μ ν hF P

end RoosComparisonProof

attribute [local irreducible] RoosComparisonProof.strictRoosIso

namespace IntegralScalarAux

universe w

set_option synthInstance.maxSize 2048
open MonoidalCategory

universe v r
section
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
private abbrev ScalarModules := SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
local notation "A" => ScalarModules R
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
private noncomputable local instance : MonoidalCategory A := SheafOfModules.monoidalCategory R
private noncomputable local instance : SymmetricCategory A := SheafOfModules.symmetricCategory R
private noncomputable local instance : MonoidalPreadditive A :=
  SheafOfModules.monoidalPreadditive_kfi R
private noncomputable local instance (M : A) :
    PreservesColimitsOfSize.{r, r} (tensorLeft M) :=
  SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
private noncomputable local instance (M : A) :
    PreservesColimitsOfSize.{r, r} (tensorRight M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
private noncomputable local instance (M : A) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  preservesColimitsOfSize_shrink (tensorLeft M)
private noncomputable local instance (M : A) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  preservesColimitsOfSize_shrink (tensorRight M)
private theorem siteFlat_iff_core (M : A) :
    SheafOfModules.IsFlatOnSite.{u, v, r, r} (J := J) (R := R) M ↔ ObjectProperty.flat M := by
  have e := SheafOfModules.siteSheafTensorRightIso R M
  constructor
  · intro h
    have hr := (exactFunctor _ _).prop_of_iso e h
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight M).symm hr, hr⟩
  · intro h
    exact (exactFunctor _ _).prop_of_iso e.symm h.2
private theorem goodClosed :
    ObjectProperty.IsClosedUnderBinaryProducts
      (fun K : CochainComplex A ℤ ↦
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) K ∧
        ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, v, r, r} (J := J) (R := R) (K.X i)) := by
  constructor
  rintro K ⟨p⟩
  constructor
  · intro Z hZ i
    let T := ((curriedTensor A).map₂CochainComplex.obj Z) ⋙
      HomologicalComplex.homologyFunctor A (.up ℤ) i
    have hzero : IsZero (p.diag ⋙ T) := by
      apply Functor.isZero
      intro j
      exact ((p.prop_diag_obj j).1 Z hZ i).isZero_homology
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      ((isLimitOfPreserves T p.isLimit).isZero_pt hzero)
  · intro i
    have hc := CochainComplex.closedUnderLimitsOfShape_discrete_flat A WalkingPair
    apply (siteFlat_iff_core R _).2
    apply ObjectProperty.prop_of_isLimit ObjectProperty.flat
      (isLimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i) p.isLimit)
    intro j
    exact (siteFlat_iff_core R _).1 ((p.prop_diag_obj j).2 i)
private theorem acyclicShift (K : CochainComplex A ℤ) (hK : K.Acyclic) (n : ℤ) :
    (K⟦n⟧).Acyclic := by
  let Q := HomotopyCategory.quotient A (.up ℤ)
  let P := HomotopyCategory.subcategoryAcyclic A
  have h : P (Q.obj K) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K).2 hK
  have hs : P ((Q.obj K)⟦n⟧) := P.le_shift n _ h
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    (P.prop_of_iso ((Q.commShiftIso n).app K).symm hs)
private theorem goodShift (K : CochainComplex A ℤ)
    (hK : K.IsKFlatIndependentCoefficients ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, v, r, r} (J := J) (R := R) (K.X i))
    (n : ℤ) :
    (K⟦n⟧).IsKFlatIndependentCoefficients ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, v, r, r} (J := J) (R := R) ((K⟦n⟧).X i) := by
  constructor
  · intro Z hZ i
    exact (acyclicShift R _ (hK.1 Z hZ) n i).of_iso
      (CochainComplex.mapBifunctorShift₂Iso Z K (curriedTensor A) n).symm
  · intro i
    exact hK.2 (i + n)

end

private theorem additive_descent
    {C : Type u} {D : Type v} {E : Type w}
    [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (L : C ⥤ D) [L.Additive] [L.EssSurj] (F : D ⥤ E) [(L ⋙ F).Additive] :
    F.Additive := by
  classical
  have : F.PreservesZeroMorphisms := by
    constructor
    intro X Y
    let eX := L.objObjPreimageIso X
    let eY := L.objObjPreimageIso Y
    have h : (0 : X ⟶ Y) = eX.inv ≫ L.map (0 : L.objPreimage X ⟶ L.objPreimage Y) ≫
        eY.hom := by simp
    rw [h, F.map_comp, F.map_comp]
    have hz := (L ⋙ F).map_zero (L.objPreimage X) (L.objPreimage Y)
    change F.map _ ≫ (L ⋙ F).map 0 ≫ F.map _ = 0
    rw [hz]
    simp
  have hpair (X Y : C) : PreservesLimit (pair (L.obj X) (L.obj Y)) F := by
    have hc := BinaryBiproduct.isLimit X Y
    have h : PreservesLimit (pair X Y ⋙ L) F :=
      preservesLimit_of_preserves_limit_cone (isLimitOfPreserves L hc)
        (isLimitOfPreserves (L ⋙ F) hc)
    exact preservesLimit_of_iso_diagram F (diagramIsoPair (pair X Y ⋙ L))
  have : PreservesLimitsOfShape (Discrete WalkingPair) F := by
    constructor
    intro K
    let T := Discrete.functor (fun j ↦ L.obj (L.objPreimage (K.obj ⟨j⟩)))
    have : PreservesLimit T F := by
      have h : PreservesLimit
          (pair (T.obj ⟨WalkingPair.left⟩) (T.obj ⟨WalkingPair.right⟩)) F := by
        exact hpair _ _
      exact preservesLimit_of_iso_diagram F (diagramIsoPair T).symm
    exact preservesLimit_of_iso_diagram F
      (Discrete.natIso (F := T) (G := K) (fun j ↦ L.objObjPreimageIso (K.obj j)))
  exact F.additive_of_preserves_binary_products

private theorem uniqueComparison {C : Type u} [Category.{v} C]
    {D : Type w} [Category D] {T : Type r} [Category T]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : D ⥤ T} {H : C ⥤ T} (e : L ⋙ F ≅ H) (e' : L ⋙ G ≅ H) :
    ∃! α : F ≅ G, isoWhiskerLeft L α ≪≫ e' = e := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W T
  let α := ff.preimageIso (e ≪≫ e'.symm)
  have hα : isoWhiskerLeft L α = e ≪≫ e'.symm :=
    ff.isoEquiv.apply_symm_apply _
  refine ⟨α, by dsimp only; rw [hα]; simp, ?_⟩
  intro β hβ
  apply ff.isoEquiv.injective
  change isoWhiskerLeft L β = isoWhiskerLeft L α
  rw [hα, ← hβ]
  simp

private theorem localized_action_app {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (μ : 𝟭 C ⟶ 𝟭 C) (X : C) :
    ((Localization.fullyFaithfulWhiskeringLeft L W D).preimage (X := 𝟭 D) (Y := 𝟭 D)
      (whiskerRight μ L)).app (L.obj X) = L.map (μ.app X) := by
  have h := (Localization.fullyFaithfulWhiskeringLeft L W D).map_preimage
    (X := 𝟭 D) (Y := 𝟭 D) (whiskerRight μ L)
  exact congrArg (fun η ↦ η.app X) h

private theorem action_descent {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (T : C ⥤ E) (F : D ⥤ E) (e : L ⋙ F ≅ T)
    (μ : 𝟭 D ⟶ 𝟭 D) (ν : 𝟭 E ⟶ 𝟭 E) (α : ∀ X : C, X ⟶ X)
    (hμ : ∀ X, μ.app (L.obj X) = L.map (α X))
    (hT : ∀ X, T.map (α X) = ν.app (T.obj X)) :
    ∀ X, F.map (μ.app X) = ν.app (F.obj X) := by
  have hη : whiskerRight μ F = whiskerLeft F ν := by
    apply (Localization.fullyFaithfulWhiskeringLeft L W E).map_injective
    ext X
    change F.map (μ.app (L.obj X)) = ν.app (F.obj (L.obj X))
    apply (cancel_mono (e.hom.app X)).mp
    rw [hμ]
    exact (e.hom.naturality (α X)).trans
      ((congrArg (fun f ↦ e.hom.app X ≫ f) (hT X)).trans (ν.naturality (e.hom.app X)))
  intro X
  exact congrArg (fun η ↦ η.app X) hη

private theorem action_descent_via_complex {C C' D E : Type*}
    [Category C] [Category C'] [Category D] [Category E]
    (P : ObjectProperty C) (Q : C ⥤ D) (R : C' ⥤ E)
    (L : P.FullSubcategory ⥤ D) (W : MorphismProperty P.FullSubcategory)
    [L.IsLocalization W] (hL : L = P.ι ⋙ Q)
    (T : C ⥤ C') (F : D ⥤ E) (e : L ⋙ F ≅ P.ι ⋙ T ⋙ R)
    (μ : 𝟭 D ⟶ 𝟭 D) (ν : 𝟭 E ⟶ 𝟭 E)
    (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 C' ⟶ 𝟭 C')
    (hμ : ∀ X, μ.app (Q.obj X) = Q.map (α.app X))
    (hν : ∀ X, ν.app (R.obj X) = R.map (β.app X))
    (hT : ∀ X, T.map (α.app X) = β.app (T.obj X))
    (X X' : D) (f : X ⟶ X') :
    F.map (μ.app X ≫ f) = ν.app (F.obj X) ≫ F.map f := by
  subst L
  have ha := action_descent (P.ι ⋙ Q) W (P.ι ⋙ T ⋙ R) F e μ ν
    (fun Z ↦ ObjectProperty.homMk (α.app Z.obj))
    (fun Z ↦ hμ Z.obj)
    (fun Z ↦ (congrArg R.map (hT Z.obj)).trans (hν (T.obj Z.obj)).symm) X
  rw [F.map_comp, ha]

private theorem inverts_on_subcategory {C D E : Type*}
    [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (T : C ⥤ D) (Q : D ⥤ E)
    (W : MorphismProperty C) (V : MorphismProperty D)
    (hT : ∀ (X Y : P.FullSubcategory) (f : X.obj ⟶ Y.obj), W f → V (T.map f))
    (hQ : V.IsInvertedBy Q) :
    (W.inverseImage P.ι).IsInvertedBy (P.ι ⋙ T ⋙ Q) := by
  intro X Y f hf
  exact hQ (T.map f.hom) (hT X Y f.hom hf)

end IntegralScalarAux

section ScalarDescent

attribute [local irreducible] ScalarModuleRoosProof.modulePi ScalarModuleRoosProof.complexPi

attribute [local irreducible] ScalarConeProof.coneFunctor RoosComparisonProof.strictRoos

attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local irreducible] limit integralScalarReductionWitness integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

private local instance integralScalarGood_binaryProducts :
    (integralOperationsGoodComplex l E Y).IsClosedUnderBinaryProducts := by
  unfold integralOperationsGoodComplex
  exact IntegralScalarAux.goodClosed (completedIntegralCommRingSheafUnrestricted l E Y)

private noncomputable local instance integralScalarGood_biproducts :
    HasBinaryBiproducts (integralOperationsGoodComplex l E Y).FullSubcategory := by
  have : HasLimitsOfShape (Discrete WalkingPair) (integralTowerModules l E Y) :=
    SheafOfModules.hasLimitsOfShape _ _
  have : HasLimitsOfShape (Discrete WalkingPair)
      (CochainComplex (integralTowerModules l E Y) ℤ) := inferInstance
  have : HasBinaryProducts (integralOperationsGoodComplex l E Y).FullSubcategory :=
    hasLimitsOfShape_of_closedUnderLimits (Discrete WalkingPair)
      (integralOperationsGoodComplex l E Y)
  exact HasBinaryBiproducts.of_hasBinaryProducts

private local instance integralScalarGood_shift :
    (integralOperationsGoodComplex l E Y).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        unfold integralOperationsGoodComplex at hK ⊢
        exact IntegralScalarAux.goodShift
          (completedIntegralCommRingSheafUnrestricted l E Y) K hK n }

private noncomputable def integralScalarModuleTransition (n : ℕ) :
    integralScalarOrdinaryLevel l E L ι Y (n + 1) ⟶
      integralScalarOrdinaryLevel l E L ι Y n where
  app M := integralScalarModuleStep l E L ι Y n M
  naturality := by
    intro M N f
    exact integralScalarModuleStep_naturality l E L ι Y n f

private theorem integralScalarTransition_termwise (n : ℕ) :
    integralScalarTransition l E L ι Y n =
      (integralScalarModuleTransition l E L ι Y n).mapHomologicalComplex (.up ℤ) := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply integralScalarReduction_hom_ext l E L ι Y (n + 1) (P.X i)
  intro U s x
  exact ((integralScalarTransition_existsUnique l E L ι Y n).exists.choose_spec P i U s x).trans
    (integralScalarModuleStep_tmul l E L ι Y n (P.X i) U s x).symm

private theorem integralScalarChainAction_termwise
    (a : Padic.coefficientExtensionIntegers l E) :
    integralScalarChainAction l E Y a =
      (integralScalarModuleAction l E Y a).mapHomologicalComplex (.up ℤ) := by
  exact (integralScalarChainAction_existsUnique l E Y a).unique
    (integralScalarChainAction_existsUnique l E Y a).exists.choose_spec
    (fun P i U x ↦ rfl)

private theorem integralScalarRho_constant (n : ℕ) (U : Y.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    ((integralScalarRho l E L ι Y n).hom.app U).hom
        (integralScalarConstant l E Y U a) =
      integralScalarFiniteConstant l L Y n U (integralScalarIntegerInclusion l E L ι a) := by
  have hπ := (integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n
  unfold integralScalarRho
  change ((integralScalarQuotientSheafMap l E L ι Y n).hom.app U).hom
    (((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom
      (integralScalarConstant l E Y U a)) = _
  rw [show ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom
      (integralScalarConstant l E Y U a) = integralScalarFiniteConstant l E Y n U a
    from hπ]
  let q := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((integralScalarQuotientMap l E L ι n).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  have h := congrArg (fun f ↦ (f.app U).hom
    (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a)))
    (toSheafify_naturality (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map q))
  exact h.symm

private theorem integralScalarModuleLevel_action (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) (M : integralTowerModules l E Y) :
    (integralScalarOrdinaryLevel l E L ι Y n).map
        ((integralScalarModuleAction l E Y a).app M) =
      (integralScalarModuleAction l L Y (integralScalarIntegerInclusion l E L ι a)).app
        ((integralScalarOrdinaryLevel l E L ι Y n).obj M) := by
  apply integralScalarReduction_hom_ext l E L ι Y n M
  intro U s x
  change ((integralScalarReduction l E L ι Y n).map
      ((integralScalarModuleAction l E Y a).app M)).val.app U _ = _
  refine (integralScalarReduction_map_tmul l E L ι Y n
    ((integralScalarModuleAction l E Y a).app M) U s x).trans ?_
  change integralScalarTensorSection l E L ι Y n M U s
      (integralScalarConstant l E Y U a • x) =
    ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U).hom
      (integralScalarConstant l L Y U (integralScalarIntegerInclusion l E L ι a)) •
        integralScalarTensorSection l E L ι Y n M U s x
  let r : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U :=
    integralScalarConstant l E Y U a
  let c := integralScalarConstant l L Y U (integralScalarIntegerInclusion l E L ι a)
  let ρ := ((integralScalarRho l E L ι Y n).hom.app U).hom
  let π := ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U).hom
  have hscalar : ρ r = π c := by
    rw [integralScalarRho_constant]
    exact ((integralScalarConstant_existsUnique l L Y U
      (integralScalarIntegerInclusion l E L ι a)).exists.choose_spec n).symm
  let T := SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
    (integralScalarRho l E L ι Y n) M
  let η := ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l L Y n)).obj)).unit.app T).app U ≫
    ((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U
  change η (s ⊗ₜ[_,ρ] (r • x)) = (π c) • η (s ⊗ₜ[_,ρ] x)
  rw [← η.hom.map_smul, ← hscalar]
  congr 1
  let : Module ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U)
      ((integralCoefficientCommRingSheaf l L Y n).obj.obj U) :=
    Module.compHom _ ρ
  change s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U]
      (r • x) = _
  rw [TensorProduct.tmul_smul]
  rfl

private theorem integralScalarComplex_eq :
    integralScalarComplexFunctor l E L ι Y =
      RoosComparisonProof.strictRoos (integralScalarOrdinaryLevel l E L ι Y)
        (integralScalarModuleTransition l E L ι Y) := by
  exact RoosComparisonProof.strictRoos_of_termwise (integralScalarOrdinaryLevel l E L ι Y)
    (integralScalarModuleTransition l E L ι Y) (integralScalarTransition l E L ι Y)
    (funext (integralScalarTransition_termwise l E L ι Y))

private theorem integralScalarComplex_structure :
    (integralScalarComplexFunctor l E L ι Y).Additive ∧
      Nonempty ((integralScalarComplexFunctor l E L ι Y).CommShift ℤ) := by
  let e := eqToIso (integralScalarComplex_eq l E L ι Y) ≪≫
    RoosComparisonProof.strictRoosIso (integralScalarOrdinaryLevel l E L ι Y)
      (integralScalarModuleTransition l E L ι Y)
  obtain ⟨hAdd, ⟨hShift⟩⟩ := ScalarModuleRoosProof.complexCone_structure
    (integralScalarOrdinaryLevel l E L ι Y) (integralScalarModuleTransition l E L ι Y)
  let := hAdd
  let := hShift
  exact ⟨Functor.additive_of_iso e.symm, ⟨Functor.CommShift.ofIso e.symm ℤ⟩⟩

private theorem integralScalarComplex_action (a : Padic.coefficientExtensionIntegers l E)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (integralScalarComplexFunctor l E L ι Y).map
        ((integralScalarChainAction l E Y a).app P) =
      (integralScalarChainAction l L Y (integralScalarIntegerInclusion l E L ι a)).app
        ((integralScalarComplexFunctor l E L ι Y).obj P) := by
  exact RoosComparisonProof.action_of_termwise (integralScalarOrdinaryLevel l E L ι Y)
    (integralScalarModuleTransition l E L ι Y) (integralScalarComplexFunctor l E L ι Y)
    (integralScalarComplex_eq l E L ι Y) (integralScalarModuleAction l E Y a)
    (integralScalarModuleAction l L Y (integralScalarIntegerInclusion l E L ι a))
    (integralScalarChainAction l E Y a)
    (integralScalarChainAction l L Y (integralScalarIntegerInclusion l E L ι a))
    (integralScalarChainAction_termwise l E Y a)
    (integralScalarChainAction_termwise l L Y (integralScalarIntegerInclusion l E L ι a))
    (fun n M ↦ integralScalarModuleLevel_action l E L ι Y n a M) P

private theorem integralScalarFinite_quasiIso
    (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (f : P.obj ⟶ P'.obj) (hf : QuasiIso f) (n : ℕ) :
    QuasiIso ((integralScalarFiniteComplex l E L ι Y n).map f) := by
  have hP := P.property
  have hP' := P'.property
  unfold integralOperationsGoodComplex at hP hP'
  exact @SheafOfModules.derivedChangeOfRingsIndependentCoefficients_kflat_invariance
    _ _ _ _ _ _ _ _ _ (integralScalarRho l E L ι Y n) (integralScalarReduction l E L ι Y n)
    (integralScalarReduction_obj l E L ι Y n)
    (fun a ↦ integralScalarReduction_map l E L ι Y n a)
    (integralScalarReduction_additive l E L ι Y n) _ _ f hP.1 hP'.1 hf

private local instance integralScalarGoodLocalization_isLocalization :
    (integralOperationsGoodLocalization l E Y).IsLocalization
      ((HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
        (integralOperationsGoodComplex l E Y).ι) := by
  exact WeilConjectures.integralOperationsGoodLocalization_isLocalization l E Y

private theorem integralScalarLevel_quasiIso
    (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (f : P.obj ⟶ P'.obj) (hf : QuasiIso f) (n : ℕ) :
    QuasiIso ((integralScalarLevel l E L ι Y n).map f) := by
  let α := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l L Y n)
  obtain ⟨hlim, hcolim⟩ := WeilConjectures.coefficientRestriction_exact α
  let := hlim
  let := hcolim
  have := integralScalarFinite_quasiIso l E L ι Y P P' f hf n
  change QuasiIso (((SheafOfModules.restrictScalars.{max u (t + 1)} α).mapHomologicalComplex
    (.up ℤ)).map ((integralScalarFiniteComplex l E L ι Y n).map f))
  infer_instance

private theorem integralScalarTower_map_quasiIso
    {P P' : CochainComplex (integralTowerModules l E Y) ℤ} (f : P ⟶ P') (n : ℕ)
    (hf : QuasiIso ((integralScalarLevel l E L ι Y n).map f)) :
    QuasiIso (((integralScalarTowerFunctor l E L ι Y).map f).app (op n)) := by
  exact hf

attribute [local irreducible] integralScalarTowerFunctor

private theorem integralScalarComplex_quasiIso
    (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (f : P.obj ⟶ P'.obj) (hf : QuasiIso f) :
    QuasiIso ((integralScalarComplexFunctor l E L ι Y).map f) := by
  exact WeilConjectures.integralOperationsRoosQuasiIsoInvariant l L Y
    ((integralScalarTowerFunctor l E L ι Y).map f)
    (fun n ↦ integralScalarTower_map_quasiIso l E L ι Y f n
      (integralScalarLevel_quasiIso l E L ι Y P P' f hf n))

private theorem integralScalarComplex_obj_roos
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (integralScalarComplexFunctor l E L ι Y).obj P =
      integralOperationsRoos ((integralScalarTowerFunctor l E L ι Y).obj P) := by
  rfl

attribute [local irreducible] integralScalarComplexFunctor

private noncomputable local instance integralScalarGoodLocalization_commShift :
    (integralOperationsGoodLocalization l E Y).CommShift ℤ := by
  unfold integralOperationsGoodLocalization
  infer_instance

private noncomputable local instance integralScalarOnGood_commShift
    [(integralScalarComplexFunctor l E L ι Y).CommShift ℤ] :
    (integralScalarOnGood l E L ι Y).CommShift ℤ := by
  unfold integralScalarOnGood
  infer_instance

private local instance integralScalarGoodLocalization_additive :
    (integralOperationsGoodLocalization l E Y).Additive := by
  unfold integralOperationsGoodLocalization
  infer_instance

private local instance integralScalarOnGood_additive
    [(integralScalarComplexFunctor l E L ι Y).Additive] :
    (integralScalarOnGood l E L ι Y).Additive := by
  unfold integralScalarOnGood
  infer_instance

private theorem integralScalarDerivedAction_app_Q (a : Padic.coefficientExtensionIntegers l E)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (integralScalarDerivedAction l E Y a).app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((integralScalarChainAction l E Y a).app P) := by
  rw [integralScalarDerivedAction_eq_preimage]
  exact IntegralScalarAux.localized_action_app
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
    (integralScalarChainAction l E Y a) P

private theorem integralScalarComplex_isDerivedLimit
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    integralOperationsDerivedLimitProperty l L Y
      ((integralScalarTowerFunctor l E L ι Y).obj P)
      (DerivedCategory.Q.obj ((integralScalarComplexFunctor l E L ι Y).obj P)) := by
  let C := (integralScalarTowerFunctor l E L ι Y).obj P
  exact Eq.mpr
    (congrArg (fun X : CochainComplex (integralTowerModules l L Y) ℤ ↦
      integralOperationsDerivedLimitProperty l L Y C (DerivedCategory.Q.obj X))
      (integralScalarComplex_obj_roos l E L ι Y P))
    (WeilConjectures.integralOperationsRoosDerivedLimit l L Y C)

private theorem integralScalarOnGood_eq_comp :
    integralScalarOnGood l E L ι Y = (integralOperationsGoodComplex l E Y).ι ⋙
      integralScalarComplexFunctor l E L ι Y ⋙
        (DerivedCategory.Q (C := integralTowerModules l L Y)) := by
  rfl

private theorem integralScalarOnGood_inverts :
    ((HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E Y).ι).IsInvertedBy
        (integralScalarOnGood l E L ι Y) := by
  rw [integralScalarOnGood_eq_comp]
  exact IntegralScalarAux.inverts_on_subcategory
    (integralOperationsGoodComplex l E Y) (integralScalarComplexFunctor l E L ι Y)
    (DerivedCategory.Q (C := integralTowerModules l L Y))
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
    (HomologicalComplex.quasiIso (integralTowerModules l L Y) (.up ℤ))
    (integralScalarComplex_quasiIso l E L ι Y)
    (Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (integralTowerModules l L Y) (.up ℤ)))

private theorem integralScalarFunctor_linear
    (F : DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l L Y))
    (e : integralOperationsGoodLocalization l E Y ⋙ F ≅ integralScalarOnGood l E L ι Y) :
    ∀ (a : Padic.coefficientExtensionIntegers l E)
      (K K' : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ K'),
      F.map ((integralScalarDerivedAction l E Y a).app K ≫ f) =
        (integralScalarDerivedAction l L Y
          (integralScalarIntegerInclusion l E L ι a)).app (F.obj K) ≫ F.map f := by
  intro a K K' f
  let e' := e ≪≫ eqToIso (integralScalarOnGood_eq_comp l E L ι Y)
  exact IntegralScalarAux.action_descent_via_complex
    (integralOperationsGoodComplex l E Y)
    (DerivedCategory.Q (C := integralTowerModules l E Y))
    (DerivedCategory.Q (C := integralTowerModules l L Y))
    (integralOperationsGoodLocalization l E Y)
    ((HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E Y).ι) rfl
    (integralScalarComplexFunctor l E L ι Y) F e'
    (integralScalarDerivedAction l E Y a)
    (integralScalarDerivedAction l L Y (integralScalarIntegerInclusion l E L ι a))
    (integralScalarChainAction l E Y a)
    (integralScalarChainAction l L Y (integralScalarIntegerInclusion l E L ι a))
    (integralScalarDerivedAction_app_Q l E Y a)
    (integralScalarDerivedAction_app_Q l L Y (integralScalarIntegerInclusion l E L ι a))
    (integralScalarComplex_action l E L ι Y a) K K' f

private noncomputable def integralScalarDescendedFunctor :
    DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l L Y) :=
  Localization.lift (integralScalarOnGood l E L ι Y)
    (integralScalarOnGood_inverts l E L ι Y) (integralOperationsGoodLocalization l E Y)

private noncomputable def integralScalarDescendedComparison :
    integralOperationsGoodLocalization l E Y ⋙ integralScalarDescendedFunctor l E L ι Y ≅
      integralScalarOnGood l E L ι Y :=
  Localization.fac (integralScalarOnGood l E L ι Y)
    (integralScalarOnGood_inverts l E L ι Y) (integralOperationsGoodLocalization l E Y)

attribute [local irreducible] integralScalarDescendedFunctor integralScalarDescendedComparison

attribute [local irreducible] integralScalarReduction integralScalarFiniteComplex
  integralScalarLevel integralScalarOrdinaryLevel

attribute [local irreducible] Localization.lift Localization.fac

set_option backward.isDefEq.respectTransparency true in
set_option Elab.async false in
/-- The three assertions: levelwise and Roos quasi-isomorphism invariance, additive
shift-compatible descent unique with its representative comparisons and derived-limit
values, and linearity for the actual constant-section actions.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: 1. The extending absolute values agree, giving the integer inclusion and quotient
maps above. Their reductions commute; tensor transitions are the canonical balanced
formula, linear over the target completion.
2. Apply lem-pur-change-of-rings-kflat-quasi-iso to ρ_n. No flatness of the quotient
is needed. Restriction of scalars preserves cohomology, so all tower level maps
are quasi-isomorphisms and commute strictly with transitions.
3. Exact countable products (lem-weil-proetale-countable-products-exact) and
lemma-reduction-derived-nakayama identify termwise products with derived products.
The rotated cone triangle is the Roos triangle of def-weil-derived-limit. The
diagonal product map is a triangle morphism; the distinguished-triangle
isomorphism criterion makes the cone map invertible. Cohomology detects the
asserted quasi-isomorphism.
4. Compare the termwise product of module functors with the product of their
termwise complex functors. This comparison intertwines one minus the transition
shift. The additive diagonal cone functor, shifted by minus one, is therefore
naturally isomorphic to the specified Roos functor.
5. Functorial flat resolutions give a localization presentation using good
complexes directly. Descend using lem-weil-pbc-localization-universal-property.
Binary biproduct preservation and essential surjectivity prove additivity.
Localization fully faithfulness gives exactly the unique natural isomorphism
compatible with e and e'.
6. Choose models by lem-pc-kflat-resolution. The comparison e_P and the inverse
image of q under F identify F(K) with the specified Roos value. Transport maps by
these comparisons; a second model choice gives their composite. The derived-limit
property transports along these isomorphisms. This needs no chain lift of a
derived morphism and asserts no uniqueness of arbitrary Roos-triangle fillers.
7. Shift preserves K-flatness and flat terms. Standard mapping-cone shift
isomorphisms and the termwise product comparison give natural comparisons for
every integer shift. On the two cone summands, the zero and addition coherence
equations reduce to the corresponding termwise equations and the addition law
for powers of minus one. Localization extends this coherent shift structure.
8. Constant sections act on the module category and descend to the canonical
action of lem-weil-linear-abelian-derived-category. Tensor balancing gives
(ax)⊗b=x⊗ι(a)b, also on every product and cone summand. Localization uniqueness
identifies the two natural endomorphisms on D(R). Compose with f to obtain the
displayed scalar-linearity equality; conjugation by the model comparisons preserves it. -/
theorem integralScalarExtensionWellDefined :
    (∀ (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (f : P.obj ⟶ P'.obj), QuasiIso f →
      (∀ n : ℕ, QuasiIso ((integralScalarFiniteComplex l E L ι Y n).map f)) ∧
        QuasiIso ((integralScalarComplexFunctor l E L ι Y).map f)) ∧
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l L Y))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅ integralScalarOnGood l E L ι Y),
      F.Additive ∧ Nonempty (F.CommShift ℤ) ∧
      (∀ (F' : DerivedCategory (integralTowerModules l E Y) ⥤
          DerivedCategory (integralTowerModules l L Y))
        (e' : integralOperationsGoodLocalization l E Y ⋙ F' ≅
          integralScalarOnGood l E L ι Y),
        ∃! α : F ≅ F',
          isoWhiskerLeft (integralOperationsGoodLocalization l E Y) α ≪≫ e' = e) ∧
      (∀ (K : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (_q : DerivedCategory.Q.obj P.obj ≅ K),
        Nonempty (F.obj K ≅ DerivedCategory.Q.obj
          ((integralScalarComplexFunctor l E L ι Y).obj P.obj)) ∧
        integralOperationsDerivedLimitProperty l L Y
          ((integralScalarTowerFunctor l E L ι Y).obj P.obj) (F.obj K)) ∧
      (∀ (a : Padic.coefficientExtensionIntegers l E)
        (K K' : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ K'),
        F.map ((integralScalarDerivedAction l E Y a).app K ≫ f) =
          (integralScalarDerivedAction l L Y
            (integralScalarIntegerInclusion l E L ι a)).app (F.obj K) ≫ F.map f) := by
  classical
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  let Λ := integralOperationsGoodLocalization l E Y
  have : Λ.EssSurj := Localization.essSurj Λ V
  obtain ⟨hAdd, ⟨hShift⟩⟩ := integralScalarComplex_structure l E L ι Y
  let := hAdd
  let := hShift
  let : (integralScalarOnGood l E L ι Y).Additive := inferInstance
  let : Λ.Additive := inferInstance
  let F := integralScalarDescendedFunctor l E L ι Y
  let e : Λ ⋙ F ≅ integralScalarOnGood l E L ι Y :=
    integralScalarDescendedComparison l E L ι Y
  let : Localization.Lifting Λ V (integralScalarOnGood l E L ι Y) F := ⟨e⟩
  let : (Λ ⋙ F).Additive := Functor.additive_of_iso e.symm
  have : F.Additive := IntegralScalarAux.additive_descent Λ F
  constructor
  · intro P P' f hf
    exact ⟨integralScalarFinite_quasiIso l E L ι Y P P' f hf,
      integralScalarComplex_quasiIso l E L ι Y P P' f hf⟩
  refine ⟨F, e, inferInstance,
    ⟨Functor.commShiftOfLocalization Λ V ℤ (integralScalarOnGood l E L ι Y) F⟩, ?_, ?_, ?_⟩
  · intro F' e'
    exact IntegralScalarAux.uniqueComparison Λ V e e'
  · intro K P q
    let m := (F.mapIso q).symm ≪≫ e.app P
    refine ⟨⟨m⟩, ?_⟩
    exact WeilConjectures.derivedLimit_of_iso _ m
      (integralScalarComplex_isDerivedLimit l E L ι Y P.obj)
  · exact integralScalarFunctor_linear l E L ι Y F e

end ScalarDescent

end WeilConjectures
