/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomMonoidalData
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Finite.FiniteConstructibleHom
import all WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import all WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomScalarMonoidal
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorComposition
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorIdentity
import WeilConjectures.SixFunctors.Etale.EtaleScalarUnitIdentity
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarUnitComposition

/-! # Finite coefficient domains and evaluation transposition

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lemma-change-coefficients-internal-hom--1, opening proof paragraph; Stacks 03TT, 0GKB, 06YY, 07A4
and 08J9 (blueprint: lem-coef-finite-hom-domain-calculus).

The index n denotes exponent n + 1, as in the recorded finite-Hom arrow.
Thus all positive exponents and all identity quotients are included.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a₁ a₂ a₃ b₁ b₂ b₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

attribute [local implicit_reducible] CategoryTheory.uniformProd

attribute [local implicit_reducible] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory

attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit Etale.upperStar
  Etale.scalarGeometricRepresentative

namespace FiniteHomDomainClosedCalculus

section ClosedCalculus

attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
  CoefficientClosedStructure.tensor
  CoefficientClosedStructure.evaluation CoefficientClosedStructure.transpose

private theorem domainUncurry
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (U K M : C) (g : U ⟶ H.obj (op K, M)) :
    (S.transpose U K M).symm g =
      S.tensor.map (Prod.mkHom g (𝟙 K)) ≫ S.evaluation K M := by
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
    CoefficientClosedStructure.tensor, Adjunction.homEquiv, Equiv.symm]
  let := S.monoidal
  change S.monoidal.whiskerRight g K ≫ _ = S.monoidal.tensorHom g (𝟙 K) ≫ _
  rw [MonoidalCategory.tensorHom_id]

private theorem domainEvaluation_natural
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 K')) ≫
      S.evaluation K' M' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M ≫ g := by
  let := S.monoidal
  have hf : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K')) ≫
      S.evaluation K' M =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫ _ =
      S.monoidal.tensorHom (𝟙 (H.obj (op K, M))) f ≫ _
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    exact S.evaluation_naturality K K' M f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K')) ≫
      S.evaluation K' M' = S.evaluation K' M ≫ g := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') ≫ _ = _
    rw [MonoidalCategory.tensorHom_id]
    exact (S.adjunction K').counit.naturality g
  have hh : Prod.mkHom f.op g =
      Prod.mkHom f.op (𝟙 M) ≫ Prod.mkHom (𝟙 (op K')) g := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]
  rw [hh, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 M)) ≫ H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

private theorem domainUncurry_pre
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) {U V K M : C}
    (f : U ⟶ V) (g : V ⟶ H.obj (op K, M)) :
    (S.transpose U K M).symm (f ≫ g) =
      S.tensor.map (Prod.mkHom f (𝟙 K)) ≫ (S.transpose V K M).symm g := by
  rw [domainUncurry, domainUncurry, ← S.tensor.map_comp_assoc]
  simp only [CategoryTheory.prod_comp, Category.comp_id, Category.id_comp]

private theorem domainUncurry_post
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) {U K K' M M' : C}
    (v : U ⟶ H.obj (op K, M)) (f : K' ⟶ K) (g : M ⟶ M') :
    (S.transpose U K' M').symm (v ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 U) f) ≫ (S.transpose U K M).symm v ≫ g := by
  rw [domainUncurry_pre, domainUncurry, domainEvaluation_natural, domainUncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]

private theorem domainBaseChange_uncurry
    {C : Type a₁} {C' : Type a₂} [Category.{b₁} C] [Category.{b₂} C']
    {H : Cᵒᵖ × C ⥤ C} {H' : C'ᵒᵖ × C' ⥤ C'}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : C ⥤ C') (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor) (K M : C) :
    (S'.transpose (F.obj (H.obj (op K, M))) (F.obj K) (F.obj M)).symm
        (coefficientBaseChangeHom S S' F μ K M) =
      μ.inv.app (H.obj (op K, M), K) ≫ F.map (S.evaluation K M) := by
  unfold coefficientBaseChangeHom
  exact (S'.transpose _ _ _).symm_apply_apply _

attribute [local irreducible] coefficientBaseChangeHom

end ClosedCalculus

end FiniteHomDomainClosedCalculus

/-- The existing coefficient ring, lifted to the ordinary small-etale coefficient universe.
Source: blueprint finite coefficient convention
(blueprint: lem-coef-finite-hom-domain-calculus). -/
abbrev finiteHomDomainCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

/-- Positive coefficient levels are finite, by the recorded coefficient-ring theorem.
Source: blueprint finite coefficient convention
(blueprint: lem-coef-finite-hom-domain-calculus). -/
instance finiteHomDomainCoeffFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (finiteHomDomainCoeff l E n) :=
  @Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))) Equiv.ulift.symm

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [hXover : X.Over (Spec (.of D.k))]
  [hXsep : IsSeparated (X ↘ Spec (.of D.k))]
  [hXft : LocallyOfFiniteType (X ↘ Spec (.of D.k))] [hXqc : QuasiCompact (X ↘ Spec (.of D.k))]

include D hl hXover hXsep hXft hXqc in
/-- Noetherianity and the flat constructible model in the original Tor interval, including
its actual scalar extension with its target coefficient action.
Source: blueprint opening proof paragraph; Stacks 01T6, 03TT, 0GKB, 06YQ and 06YY
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: the structure morphism is of finite type over the Noetherian field D.k, so X
is Noetherian (lem-weil-pbc-finite-type-over-noetherian). Apply
lem-sp-etale-scalar-flat-model to the actual finite-ring quotient. Its model is flat
constructible and supported in [a,b]. Bounded flatness gives K-flatness, and
lem-pur-kflat-change-of-rings preserves flat terms and K-flatness. Constructibility
of the scalar-extended terms is 0GKB. The universal K-flat counit of
lem-pur-derived-change-of-rings computes F_X on this model. Tensoring the reduced
bounded flat complex with any degree-zero B-module sheaf proves the same Tor bound.
No flatness of B over A is used. -/
theorem finiteHomDomain_flatModel {n m : ℕ} (h : m ≤ n) (a b : ℤ) (hab : a ≤ b)
    (T : finiteHomEtale l E X n)
    (hT : Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E n) X T)
    (hTor : Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E n) X a b T) :
    IsNoetherian X ∧
    (∃ P : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n))) ℤ,
      Etale.IsBoundedFlatComplex (finiteHomDomainCoeff l E n) a b P ∧
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X i)) ∧
      Nonempty (T ≅ _root_.DerivedCategory.Q.obj P) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
      Etale.IsBoundedFlatComplex (finiteHomDomainCoeff l E m) a b
        (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex (.up
          ℤ)).obj P) ∧
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex (.up
          ℤ)).obj P).X i)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex (.up
          ℤ)).obj P) ∧
      Nonempty ((finiteHomEtaleReduction l E X h).obj T ≅ _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex (.up
          ℤ)).obj P))) ∧
    Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E m) X
      ((finiteHomEtaleReduction l E X h).obj T) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E m) X a b
      ((finiteHomEtaleReduction l E X h).obj T) := by
  have : IsNoetherian X := by
    have : IsLocallyNoetherian X :=
      @LocallyOfFiniteType.isLocallyNoetherian X (Spec (.of D.k))
        (X ↘ Spec (.of D.k)) hXft inferInstance
    have : CompactSpace X :=
      @QuasiCompact.compactSpace_of_compactSpace X (Spec (.of D.k))
        (X ↘ Spec (.of D.k)) hXqc inferInstance
    exact ⟨⟩
  let J : _root_.DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n))) :=
    ⟨T, by
      obtain ⟨c, d, _, hv⟩ := hT.2
      exact ⟨⟨c, (_root_.DerivedCategory.isGE_iff T c).2
        (fun i hi ↦ hv i (.inl hi))⟩,
        ⟨d, (_root_.DerivedCategory.isLE_iff T d).2
          (fun i hi ↦ hv i (.inr hi))⟩⟩⟩
  obtain ⟨⟨P, hf, hc, hz, he⟩, models, ⟨L, ⟨eL⟩⟩, hcons, ht⟩ :=
    Etale.exists_etaleScalarFlatModel X (finiteHomDomainCoeff l E n)
      (finiteHomDomainCoeff l E m) (finiteHomQuotient l E h) a b hab J hT.1 hTor
  obtain ⟨hk, hQk, hQf, hQc, hQz, hQe⟩ := models P hf hc hz he
  have flat (q : ℤ) : ObjectProperty.flat (P.X q) :=
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (P.X q)).symm (hf q), hf q⟩
  refine ⟨inferInstance, ⟨P, ⟨hz, flat⟩, hc, ⟨he.some.symm⟩, hk,
    ⟨hQz, fun q ↦ ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight _).symm (hQf q), hQf q⟩⟩,
    hQc, hQk, hQe⟩, ⟨hcons, ?_⟩, ht⟩
  obtain ⟨c, hge⟩ := L.property.1
  obtain ⟨d, hle⟩ := L.property.2
  refine ⟨min c d, d, min_le_right _ _, fun i hi ↦ ?_⟩
  apply IsZero.of_iso _ ((_root_.DerivedCategory.homologyFunctor _ i).mapIso eL).symm
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff L.obj c).1 hge i
      (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff L.obj d).1 hle i hi

attribute [local irreducible] ProEtale.pbcFixedScalarExtension
  Etale.scalarExtensionRepresentative Etale.scalarSheafPullbackComplexIso

section PullbackCompatibility

attribute [local instance 2000] CommRing.toRing

section Pullback
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end Pullback
end PullbackCompatibility
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
include D hl hXover hXsep hXft hXqc in
/-- The canonical tensor and constant-unit comparisons make ambient coefficient change
strong symmetric monoidal, for the actual signed tensor and Koszul braiding.
Source: blueprint opening proof paragraph; Stacks 07A4 and 0FPT
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: use scalarExtension_coreMonoidal for the actual quotient ring map. That
proved generic theorem transports the native derived monoidal structure along
uniqueness of left adjoints. Right-exact tensor normalization identifies its
tensorator with the published tensorIso, the left unit law identifies its unit,
and braidedness descends from the ordinary scalar adjunction. The normalization
of finiteHomEtaleData identifies its tensor comparison with finiteHomEtaleTensor;
the all-complex tensor and unit normalization clauses are their choose_spec laws. -/
theorem finiteHomDomain_monoidal {n m : ℕ} (h : m ≤ n) :
    FiniteHomDomainMonoidal (finiteHomEtaleReduction l E X h)
      (fun U V ↦ (Etale.ExceptionalCoefficients.tensorIso
        (finiteHomQuotient l E h) X).app (U, V))
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E h) X)
      (finiteHomKoszulIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n))))
      (finiteHomKoszulIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E m)))) ∧
    HEq (finiteHomEtaleTensor l E X h)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X) ∧
    Etale.ExceptionalCoefficients.UnitNormalization (finiteHomQuotient l E h) X
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E h) X) ∧
    Etale.ExceptionalCoefficients.TensorNormalization (finiteHomQuotient l E h) X
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X) := by
  exact ⟨(finiteHomScalar_monoidal (finiteHomDomainCoeff l E n) (finiteHomDomainCoeff l E m)
      (finiteHomQuotient l E h) X).1,
    (finiteHomEtaleData_existsUnique l E X).choose_spec.1.tensor n m h,
    (finiteHomScalar_monoidal (finiteHomDomainCoeff l E n) (finiteHomDomainCoeff l E m)
      (finiteHomQuotient l E h) X).2⟩

end WeilConjectures
