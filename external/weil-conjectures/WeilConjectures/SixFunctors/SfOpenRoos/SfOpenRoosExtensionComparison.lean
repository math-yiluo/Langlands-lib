/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Basic.Denumerable
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProductsOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Normalized open-extension Roos comparison

Source: Stacks Project, proetale.tex, Tag 09BP (lemma-j-shriek-limits), and the
normalized open-factor argument of the six-functors blueprint
(blueprint: lem-sf-open-roos-extension-comparison).

The open site is presented as the slice at U in X.ProEt, exactly as in
ProEt.weaklyEtale_localization. Its coefficient sheaf is the restriction of B_X;
sf_clopen_coefficient_comparison identifies it with B_U, preserving all projections.
Thus the extension below is the recorded ringed-slice extension, not an arbitrary
functor. The integer n indexes the positive level n+1. The coefficient universe
max u (t+1) contains the site; no equality between t and u is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid repeatedly traversing the complete comparison specification.
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_over_proEtTopology

universe t u wA wB
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.SfOpenRoos

/-- Canonical sheafification on the open slice in the fixed module universe.
Source: Stacks 00XZ (blueprint: lem-sf-open-roos-extension-comparison). -/
instance sliceAbSheafify (X : Scheme.{t}) (U : X.ProEt) :
    HasSheafify ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The canonical local-bijection description of sheafification on the open slice.
Source: Stacks 00XZ (blueprint: lem-sf-open-roos-extension-comparison). -/
instance sliceAbLocallyBijective (X : Scheme.{t}) (U : X.ProEt) :
    ((Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{t}) (U : X.ProEt)

/-- The ambient modules over the actual completed ring sheaf.
Source: Stacks 09BP (blueprint: lem-sf-open-roos-extension-comparison). -/
abbrev modulesX :=
  ringedSiteModules.{max u (t + 1)} (completedIntegralCoefficientSheafUnrestricted l E X)

/-- The open module category in its ringed-slice presentation. The coefficient
comparison preserves every finite quotient projection.
Source: Stacks 09BP, 00XZ (blueprint: lem-sf-open-roos-extension-comparison). -/
abbrev modulesU :=
  ringedSiteModules.{max u (t + 1)}
    ((completedIntegralCoefficientSheafUnrestricted l E X).over U)

/-- The actual exact ringed extension by zero, with direct-sum presheaf and
module sheafification as in the recorded localized adjunction.
Source: Stacks 03DI--03DJ (blueprint: lem-sf-open-roos-extension-comparison). -/
def extension : modulesU l E X U ⥤ modulesX l E X :=
  SheafOfModules.localizedSystemExtension.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) U

/-- Additivity of the recorded extension, reused without changing its data.
Source: Stacks 03DJ (blueprint: lem-sf-open-roos-extension-comparison). -/
instance extensionAdditive : (extension l E X U).Additive :=
  SheafOfModules.localizedSystemExtensionAdditive.{t + 1, t, u} _ U

/-- Left exactness of the recorded extension.
Source: Stacks 03DJ (blueprint: lem-sf-open-roos-extension-comparison). -/
instance extensionLimits : PreservesFiniteLimits (extension l E X U) :=
  SheafOfModules.localizedSystemExtensionLimits.{t + 1, t, u} _ U

/-- Right exactness of the recorded extension.
Source: Stacks 03DJ (blueprint: lem-sf-open-roos-extension-comparison). -/
instance extensionColimits : PreservesFiniteColimits (extension l E X U) :=
  SheafOfModules.localizedSystemExtensionColimits.{t + 1, t, u} _ U

/-- The actual exact restriction, right adjoint to extension.
Source: Stacks 03DI--03DJ (blueprint: lem-sf-open-roos-extension-comparison). -/
abbrev restriction : modulesX l E X ⥤ modulesU l E X U :=
  SheafOfModules.localizedSystemRestriction.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) U

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

section SliceProducts
universe c d h k r
set_option backward.defeqAttrib.useBackward true
private theorem module_transport
    {C : Type c} {D : Type d} [Category.{h} C] [Category.{k} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J RingCat.{r}) (S : Sheaf K RingCat.{r})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{r} K J).obj R) :
    Nonempty (SheafOfModules.{r} R ≌ SheafOfModules.{r} S) := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{r} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact ⟨SheafOfModules.pushforwardPushforwardEquivalence
    (R := R) (S := S) e.symm c.hom ψ H₁ H₂⟩

private theorem slice_products (X : Scheme.{t}) (U : X.ProEt)
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)}) :
    HasExactLimitsOfShape (Discrete ℕ)
      (SheafOfModules.{max u (t + 1)} (R.over U)) := by
  let : HasSheafify ((Scheme.ProEt.topology X).over U)
      AddCommGrpCat.{max u (t + 1)} := sliceAbSheafify X U
  let e := Scheme.ProEt.sliceEquiv X U
  let J := (Scheme.ProEt.topology X).over U
  let K := Scheme.ProEt.topology U.left
  have : e.inverse.IsDenseSubsite K J := Scheme.ProEt.sliceDense X U
  let S := (e.inverse.sheafPushforwardContinuous RingCat.{max u (t + 1)} K J).obj
    (R.over U)
  obtain ⟨q⟩ := module_transport J K e (R.over U) S (Iso.refl _)
  have : HasExactLimitsOfShape (Discrete ℕ)
      (SheafOfModules.{max u (t + 1)} S) := Scheme.ProEt.products_exact U.left S ℕ
  exact HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) q.functor

end SliceProducts

/-- The geometric and product assertions in the open Roos comparison.
Source: Stacks 01T6, 01OY, 09BP and 0947
(blueprint: lem-sf-open-roos-extension-comparison).
Proof: finite type over Spec k gives Noetherian schemes; locally Noetherian
schemes are quasi-separated. Every affine-open preimage under the open immersion
is a Noetherian open subscheme, hence quasi-compact. The distinct prime l is a
unit in k and therefore in every structure-sheaf stalk. Identify the open site
with the slice and B_U with restricted B_X using weakly-etale localization and
the completed coefficient comparison. Tag 09BP gives the canonical product
comparison for the exact ringed extension. Weakly contractible affine covers
and coordinatewise lifts prove exactness of countable products on both sites.
These are the first three proof steps of the node. -/
theorem geometry_products
    (D : FiniteFieldDatum.{t}) (_hl : l ≠ D.p)
    (aX : X ⟶ Spec (CommRingCat.of D.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType (U.hom ≫ aX)] [QuasiCompact (U.hom ≫ aX)]
    [IsOpenImmersion U.hom] :
    IsNoetherian X ∧ IsNoetherian U.left ∧
    CompactSpace X ∧ QuasiSeparatedSpace X ∧
    CompactSpace U.left ∧ QuasiSeparatedSpace U.left ∧ QuasiCompact U.hom ∧
    (∀ x : X, IsUnit (l : X.presheaf.stalk x)) ∧
    (∀ x : U.left, IsUnit (l : U.left.presheaf.stalk x)) ∧
    HasExactLimitsOfShape (Discrete ℕ) (modulesU l E X U) ∧
    HasExactLimitsOfShape (Discrete ℕ) (modulesX l E X) ∧
    (∀ M : ℕ → modulesU l E X U, IsIso (piComparison (extension l E X U) M)) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hunit : IsUnit (l : D.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out) _hl.symm)
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian aX
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace aX
  let : IsNoetherian X := {}
  let : IsLocallyNoetherian U.left :=
    LocallyOfFiniteType.isLocallyNoetherian (U.hom ≫ aX)
  let : CompactSpace U.left :=
    QuasiCompact.compactSpace_of_compactSpace (U.hom ≫ aX)
  let : IsNoetherian U.left := {}
  let : TopologicalSpace.NoetherianSpace U.left :=
    IsNoetherian.noetherianSpace (X := U.left)
  let : QuasiCompact U.hom :=
    @quasiCompact_of_noetherianSpace_source U.left X
      (IsNoetherian.noetherianSpace (X := U.left)) U.hom
  have hx : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using hunit.map
      (((Scheme.ΓSpecIso (.of D.k)).inv ≫ aX.appTop) ≫
        X.presheaf.germ (⊤ : X.Opens) x (by trivial)).hom
  have hu : ∀ x : U.left, IsUnit (l : U.left.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using hunit.map
      (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (U.hom ≫ aX).appTop) ≫
        U.left.presheaf.germ (⊤ : U.left.Opens) x (by trivial)).hom
  have hpU : HasExactLimitsOfShape (Discrete ℕ) (modulesU l E X U) :=
    slice_products X U (completedIntegralCoefficientSheafUnrestricted l E X)
  have hpX : HasExactLimitsOfShape (Discrete ℕ) (modulesX l E X) :=
    Scheme.ProEt.products_exact X (completedIntegralCoefficientSheafUnrestricted l E X) ℕ
  have hprod : ∀ M : ℕ → modulesU l E X U,
      IsIso (piComparison (extension l E X U) M) := by
    intro M
    exact Scheme.proEtaleRingedExtensionByZero_products_of_universes U
      (completedIntegralCommRingSheafUnrestricted l E X) M
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hx, hu, hpU, hpX, hprod⟩

section Assertions

universe a b c d
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]

/-- The explicit normalization laws for the comparison in this node. This is a
specification, with no chosen data: it expands to the signed cone identifications,
canonical product maps, localization square, all resolution formulas, and strict
augmentation laws. Abstract category parameters keep repeated concrete sheaf-category
instance terms out of the statement's elaboration.
Source: Stacks 09BP; the signed normalization of
lem-cbc-exact-product-functor-strict-limit
(blueprint: lem-sf-open-roos-extension-comparison). -/
def ComparisonAssertions (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ⋙
        DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ⋙
        DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB) : Prop :=
    letI : HasLimitsOfShape ℕᵒᵖ (CochainComplex A ℤ) := inferInstance
    letI : HasLimitsOfShape ℕᵒᵖ (CochainComplex B ℤ) := inferInstance
    letI : HasLimitsOfShape (Discrete ℕ) (CochainComplex A ℤ) := inferInstance
    letI : HasLimitsOfShape (Discrete ℕ) (CochainComplex B ℤ) := inferInstance
    letI : ∀ T : ℕᵒᵖ ⥤ CochainComplex A ℤ, HasLimit T := fun _ ↦ inferInstance
    letI : ∀ T : ℕᵒᵖ ⥤ CochainComplex B ℤ, HasLimit T := fun _ ↦ inferInstance
    letI : ∀ T : Discrete ℕ ⥤ CochainComplex A ℤ, HasLimit T := fun _ ↦ inferInstance
    letI : ∀ T : Discrete ℕ ⥤ CochainComplex B ℤ, HasLimit T := fun _ ↦ inferInstance
    ∃ (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
      (hAobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, HA.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, HB.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
      (chiB : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (psi : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦
          (M).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op n))))
      (kappa : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj M) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        M))
      (beta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (limit I.asFunctor) ≅
          limit
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        I).asFunctor)
      (lambda : LA ⋙ F.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _
        _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦
          inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB),
      -- The signed coordinates are pinned to the actual shifted cone, in both categories.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (chiA M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (A) ℤ ↦ V.X (p +
          1)) (hAobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (chiB M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (B) ℤ ↦ V.X (p +
          1)) (hBobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      -- Roos maps are the product map on each signed coordinate.
      (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : M ⟶ N) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA N p).hom = (chiA M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : M ⟶ N) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB N p).hom = (chiB M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      -- K-injective normalization of the same thetaA and thetaB.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HB.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiB I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.{wB}.map iota) ∧
      -- The canonical product map, and its two-summand version kappa.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (psi M).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦
          M.asFunctor.obj (op k))
          n)) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappa M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA M p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f p =
          F.map ((chiA M p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f p)) ∧
      -- This square is lambda = thetaB inverse, kappa, F(thetaA), in Lean order.
      (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapDerivedCategory).map (thetaA.hom.app M) ≫ F.mapDerivedCategoryFactors.hom.app (HA.obj
          M) ≫
            DerivedCategory.Q.{wB}.map (kappa M).hom =
          lambda.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
                _ _ _ ↦
              inferInstance⟩)).hom.app M) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ∧
      -- Ordinary inverse limits are preserved, with the canonical projection normalization.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (beta I).hom ≫
        limit.π ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
        ℤ)).obj I).asFunctor (op n) =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (limit.π I.asFunctor
          (op n))) ∧
      -- Every pair of K-injective resolutions computes this same lambda.
      (∀ (M I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : M ⟶ I) [QuasiIso q]
        [I.IsKInjective]
        (Jt : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (r :
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          I ⟶ Jt) [QuasiIso r] [Jt.IsKInjective],
        ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅ LA.obj (DerivedCategory.Q.{wA}.obj
          M))
          (dJ : DerivedCategory.Q.{wB}.obj (limit Jt.asFunctor) ≅ LB.obj (DerivedCategory.Q.{wB}.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up
            ℤ)).obj I))),
          dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
          dJ.hom ≫ LB.map (DerivedCategory.Q.{wB}.map r) = etaB.app Jt ∧
          (F.mapDerivedCategory).map dI.hom ≫ lambda.hom.app
            (DerivedCategory.Q.{wA}.obj M) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩)
                  (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app M) ≫
              LB.map (DerivedCategory.Q.{wB}.map ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) =
            F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
              DerivedCategory.Q.{wB}.map (beta I).hom ≫
              DerivedCategory.Q.{wB}.map (lim.map
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) ≫ dJ.hom) ∧
      -- The strict augmentation maps are pinned by (gamma,0), not arbitrary derived arrows.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex
        (A) ℤ) (gamma : ∀ n : ℕ, Q ⟶ M.asFunctor.obj (op n))
        (_hgamma : ∀ n : ℕ, gamma (n + 1) ≫ M.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        ∃ (b : Q ⟶ HA.obj M) (b' : (F.mapHomologicalComplex (ComplexShape.up
          ℤ)).obj Q ⟶ HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          M)),
          (∀ i : ℤ, b.f (i + 1) ≫ (chiA M i).hom = biprod.lift ((Pi.lift gamma).f (i + 1)) 0) ∧
          (∀ i : ℤ, b'.f (i + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) i).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ (F.mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              (gamma n))).f (i + 1)) 0) ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map b ≫
            thetaA.inv.app M) ≫
              lambda.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩)
                  (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app M) =
            F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.{wB}.map
              b' ≫ thetaB.inv.app
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up
              ℤ)).obj M) ∧
          -- The coordinate maps are the actual maps induced by the augmentations.
          (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
              (q : M ⟶ I) [QuasiIso q] [I.IsKInjective],
            ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅
                LA.obj (DerivedCategory.Q.{wA}.obj M)) (a : Q ⟶ limit I.asFunctor),
              dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
              (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) = gamma n ≫
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
              DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app M =
                DerivedCategory.Q.{wA}.map a ≫ dI.hom) ∧
          (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
              (q : (((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ I)
              [QuasiIso q] [I.IsKInjective],
            ∃ (dI : DerivedCategory.Q.{wB}.obj (limit I.asFunctor) ≅
                LB.obj (DerivedCategory.Q.{wB}.obj
                  ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                    F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))
              (a : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶
                limit I.asFunctor),
              dI.hom ≫ LB.map (DerivedCategory.Q.{wB}.map q) = etaB.app I ∧
              (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) =
                (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (gamma n) ≫
                  (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
              DerivedCategory.Q.{wB}.map b' ≫ thetaB.inv.app
                ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                  F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
                DerivedCategory.Q.{wB}.map a ≫ dI.hom))

set_option maxHeartbeats 100000 in
-- The normalization calculation compares the complex-limit presentation repeatedly.
set_option backward.defeqAttrib.useBackward true in
private theorem augmentation_resolution
    [IsGrothendieckAbelian.{c} (ℕᵒᵖ ⥤ A)]
    (H : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ)
    (hobj : ∀ M, H.obj M = roosF.obj M)
    (χ : ∀ M p, (H.obj M).X (p + 1) ≅ (roosP M).X (p + 1) ⊞ (roosP M).X p)
    (hc : ∀ M p, (χ M p).hom =
      (eqToIso (congrArg (fun V ↦ V.X (p + 1)) (hobj M))).hom ≫ (signedχ M p).hom)
    (hm : ∀ {M N} (f : M ⟶ N) p, (H.map f).f (p + 1) ≫ (χ N p).hom =
      (χ M p).hom ≫ biprod.map ((roosPmap f).f (p + 1)) ((roosPmap f).f p))
    (L : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (η : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ⋙
        DerivedCategory.Q.{wA} (C := A) ⟶
        DerivedCategory.Q.{wA} (C := ℕᵒᵖ ⥤ A) ⋙ L)
    (hL : L.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)))
    (θ : DerivedCategory.Q.{wA} (C := ℕᵒᵖ ⥤ A) ⋙ L ≅
      H ⋙ DerivedCategory.Q.{wA} (C := A))
    (hn : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
      (_ : ∀ p : ℤ, Injective (I.X p)), ∃ ι : limit I.asFunctor ⟶ H.obj I,
        QuasiIso ι ∧ (∀ p : ℤ, ι.f (p + 1) ≫ (χ I p).hom =
          biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          η.app I ≫ θ.hom.app I = DerivedCategory.Q.{wA}.map ι)
    (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (P : CochainComplex A ℤ)
    (γ : ∀ n : ℕ, P ⟶ M.asFunctor.obj (op n))
    (hγ : ∀ n : ℕ, γ (n + 1) ≫ M.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (b : P ⟶ H.obj M)
    (hb : ∀ p : ℤ, b.f (p + 1) ≫ (χ M p).hom = biprod.lift ((Pi.lift γ).f (p + 1)) 0)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : M ⟶ I) [QuasiIso q] [I.IsKInjective] :
    ∃ (dI : DerivedCategory.Q.{wA}.obj (roosLimitFunctor.obj I) ≅
        L.obj (DerivedCategory.Q.{wA}.obj M)) (a : P ⟶ roosLimitFunctor.obj I),
      dI.hom ≫ L.map (DerivedCategory.Q.{wA}.map q) = η.app I ∧
      (∀ n : ℕ, a ≫ limit.π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj I)
        (op n) = γ n ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
      DerivedCategory.Q.{wA}.map b ≫ θ.inv.app M = DerivedCategory.Q.{wA}.map a ≫ dI.hom := by
  classical
  let := hL
  choose ι hi using fun X ↦ inclusion_exists X (H.obj X) (hobj X) (χ X) (hc X)
  have hu : ∀ X, η.app X ≫ θ.hom.app X = DerivedCategory.Q.{wA}.map (ι X) := by
    apply normalized_unit H L η θ ι (fun f ↦ inclusion_natural H χ hm ι hi f)
    intro J hJ hinj
    obtain ⟨i, _, hcoord, hunit⟩ := hn J hinj
    have he := inclusion_unique (χ J) i (ι J) hcoord (hi J)
    simpa only [he] using hunit
  let a₀ := roosAugmentLimit γ hγ
  have hb' : b = a₀ ≫ ι M := by
    apply HomologicalComplex.Hom.ext
    funext i
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
    apply (cancel_mono (χ M p).hom).mp
    change b.f (p + 1) ≫ (χ M p).hom =
      (a₀.f (p + 1) ≫ (ι M).f (p + 1)) ≫ (χ M p).hom
    rw [hb, Category.assoc, hi]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst]
      erw [← HomologicalComplex.comp_f]
      congr 1
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, Pi.lift_comp_π]
      exact (roosAugmentLimit_π γ hγ n).symm
    · simp only [Category.assoc, biprod.lift_snd, comp_zero]
  have : IsIso (η.app I) := limit_unit_iso L η I
  let dI := asIso (η.app I) ≪≫ (asIso (L.map (DerivedCategory.Q.{wA}.map q))).symm
  let a := a₀ ≫ roosLimitFunctor.map q
  refine ⟨dI, a, ?_, ?_, ?_⟩
  · simp [dI]
  · intro n
    dsimp only [a, roosLimitFunctor, Functor.comp_map]
    erw [Category.assoc, limMap_π, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ _) (roosAugmentLimit_π γ hγ n)
  · have hiu : DerivedCategory.Q.{wA}.map (ι M) ≫ θ.inv.app M = η.app M := by
      calc
        _ = (η.app M ≫ θ.hom.app M) ≫ θ.inv.app M :=
          congrArg (fun z ↦ z ≫ θ.inv.app M) (hu M).symm
        _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    have hbderived : DerivedCategory.Q.{wA}.map b ≫ θ.inv.app M =
        DerivedCategory.Q.{wA}.map a₀ ≫ η.app M := by
      calc
        _ = DerivedCategory.Q.{wA}.map (a₀ ≫ ι M) ≫ θ.inv.app M :=
          congrArg (fun z ↦ DerivedCategory.Q.{wA}.map z ≫ θ.inv.app M) hb'
        _ = DerivedCategory.Q.{wA}.map a₀ ≫
            (DerivedCategory.Q.{wA}.map (ι M) ≫ θ.inv.app M) := by
          rw [Functor.map_comp, Category.assoc]
        _ = _ := congrArg (fun z ↦ DerivedCategory.Q.{wA}.map a₀ ≫ z) hiu
    apply (cancel_mono (L.map (DerivedCategory.Q.{wA}.map q))).mp
    have hunit : DerivedCategory.Q.{wA}.map (roosLimitFunctor.map q) ≫ η.app I =
        η.app M ≫ L.map (DerivedCategory.Q.{wA}.map q) := η.naturality q
    calc
      _ = DerivedCategory.Q.{wA}.map a₀ ≫
          (η.app M ≫ L.map (DerivedCategory.Q.{wA}.map q)) := by
        rw [hbderived, Category.assoc]
      _ = DerivedCategory.Q.{wA}.map a₀ ≫
          (DerivedCategory.Q.{wA}.map (roosLimitFunctor.map q) ≫ η.app I) :=
        congrArg (fun z ↦ DerivedCategory.Q.{wA}.map a₀ ≫ z) hunit.symm
      _ = DerivedCategory.Q.{wA}.map a ≫ η.app I := by
        rw [← Category.assoc, ← Functor.map_comp]
      _ = _ := by
        dsimp only [dI, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in

private theorem complete_comparison
    [IsGrothendieckAbelian.{c} A] [IsGrothendieckAbelian.{d} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : roosLimitFunctor ⋙ DerivedCategory.Q.{wA} (C := A) ⟶
      DerivedCategory.Q.{wA} (C := ℕᵒᵖ ⥤ A) ⋙ LA)
    (etaB : roosLimitFunctor ⋙ DerivedCategory.Q.{wB} (C := B) ⟶
      DerivedCategory.Q.{wB} (C := ℕᵒᵖ ⥤ B) ⋙ LB)
    (hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)))
    (hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (ComplexShape.up ℤ)))
    (h : StrictLimitAssertions F LA LB etaA etaB) :
    ComparisonAssertions F LA LB etaA etaB := by
  classical
  let := hLA
  let := hLB
  unfold StrictLimitAssertions at h
  rcases h with ⟨HA, HB, hAobj, hBobj, chiA, chiB, thetaA, thetaB, psi, kappa, beta,
    lambda, laws⟩
  have hAc := @laws.1
  have hBc := @laws.2.1
  have hAm := @laws.2.2.1
  have hBm := @laws.2.2.2.1
  have hAn := @laws.2.2.2.2.1
  have hBn := @laws.2.2.2.2.2.1
  have hpsi := @laws.2.2.2.2.2.2.1
  have hkappa := @laws.2.2.2.2.2.2.2.1
  have hsquare := @laws.2.2.2.2.2.2.2.2.1
  have hbeta := @laws.2.2.2.2.2.2.2.2.2.1
  have hres := @laws.2.2.2.2.2.2.2.2.2.2.1
  have _htri := @laws.2.2.2.2.2.2.2.2.2.2.2.1
  have haug := @laws.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨HA, HB, hAobj, hBobj, chiA, chiB, thetaA, thetaB, psi, kappa, beta,
    lambda, hAc, hBc, hAm, hBm, hAn, hBn, hpsi, hkappa, hsquare, hbeta, hres, ?_⟩
  intro M Q gamma hgamma
  obtain ⟨b, b', hb, hb', heq⟩ := haug M Q gamma hgamma
  refine ⟨b, b', hb, hb', heq, ?_, ?_⟩
  · have : IsGrothendieckAbelian.{c} (ℕᵒᵖ ⥤ A) := towerGrothendieck
    apply augmentation_resolution HA hAobj chiA _ hAm LA etaA hLA thetaA hAn
      M Q gamma hgamma b hb
    intro V p
    simpa [signedχ, roosχ, Category.assoc] using hAc V p
  · have : IsGrothendieckAbelian.{d} (ℕᵒᵖ ⥤ B) := towerGrothendieck
    apply augmentation_resolution HB hBobj chiB _ hBm LB etaB hLB thetaB hBn
      _ _ _ _ b' hb'
    · intro V p
      simpa [signedχ, roosχ, Category.assoc] using hBc V p
    · intro n
      apply HomologicalComplex.Hom.ext
      funext i
      change F.map ((gamma (n + 1)).f i) ≫ F.map ((M.X i).map _) =
        F.map ((gamma n).f i)
      have h := congrArg (fun z ↦ F.map (z.f i)) (hgamma n)
      change F.map ((gamma (n + 1)).f i ≫ (M.X i).map _) =
        F.map ((gamma n).f i) at h
      exact (F.map_comp _ _).symm.trans h

end Assertions

attribute [local irreducible] ComparisonAssertions

set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 100000 in
-- Specialize both complete signed Roos specifications without unfolding the coefficient rings.
private theorem ringed_comparison.{siteA, homA, ringA, siteB, homB, ringB, derA, derB}
    {C : Type siteA} [Category.{homA} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max siteA homA ringA}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max siteA homA ringA}]
    (R : Sheaf J RingCat.{max siteA homA ringA})
    {D : Type siteB} [Category.{homB} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{max siteB homB ringB}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max siteB homB ringB}]
    (S : Sheaf K RingCat.{max siteB homB ringB})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max siteA homA ringA} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max siteB homB ringB} S)]
    [HasDerivedCategory.{derA} (ringedSiteModules.{max siteA homA ringA} R)]
    [HasDerivedCategory.{derA} (ℕᵒᵖ ⥤ ringedSiteModules.{max siteA homA ringA} R)]
    [HasDerivedCategory.{derB} (ringedSiteModules.{max siteB homB ringB} S)]
    [HasDerivedCategory.{derB} (ℕᵒᵖ ⥤ ringedSiteModules.{max siteB homB ringB} S)]
    (F : ringedSiteModules.{max siteA homA ringA} R ⥤ ringedSiteModules.{max siteB homB ringB} S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (_hphi : ∀ (M : ℕ → ringedSiteModules.{max siteA homA ringA} R), IsIso (piComparison F M))
    (LA : DerivedCategory.{derA} (ℕᵒᵖ ⥤ ringedSiteModules.{max siteA homA ringA} R) ⥤
      DerivedCategory.{derA}
      (ringedSiteModules.{max siteA homA ringA} R))
    (LB : DerivedCategory.{derB} (ℕᵒᵖ ⥤ ringedSiteModules.{max siteB homB ringB} S) ⥤
      DerivedCategory.{derB}
      (ringedSiteModules.{max siteB homB ringB} S))
    (etaA : roosLimitFunctor (A := ringedSiteModules.{max siteA homA ringA} R) ⋙
      DerivedCategory.Q.{derA}
          (C := ringedSiteModules.{max siteA homA ringA} R) ⟶
        DerivedCategory.Q.{derA}
          (C := ℕᵒᵖ ⥤ ringedSiteModules.{max siteA homA ringA} R) ⋙ LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max siteA homA ringA} R)
        (ComplexShape.up ℤ)))
    (etaB : roosLimitFunctor (A := ringedSiteModules.{max siteB homB ringB} S) ⋙
      DerivedCategory.Q.{derB}
          (C := ringedSiteModules.{max siteB homB ringB} S) ⟶
        DerivedCategory.Q.{derB}
          (C := ℕᵒᵖ ⥤ ringedSiteModules.{max siteB homB ringB} S) ⋙ LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max siteB homB ringB} S)
        (ComplexShape.up ℤ))) :
    ComparisonAssertions F LA LB etaA etaB := by
  let hA : IsGrothendieckAbelian.{max siteA homA ringA}
      (ringedSiteModules.{max siteA homA ringA} R) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses _ _
  let hB : IsGrothendieckAbelian.{max siteB homB ringB}
      (ringedSiteModules.{max siteB homB ringB} S) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses _ _
  apply complete_comparison
    (A := ringedSiteModules.{max siteA homA ringA} R)
    (B := ringedSiteModules.{max siteB homB ringB} S) F LA LB etaA etaB _hLA _hLB
  exact exactProductFunctorStrictLimit.{siteA, homA, ringA, siteB, homB, ringB, derA, derB}
    J R K S _hR _hS F _hphi LA LB etaA _hLA etaB _hLB

attribute [local irreducible] extension

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The normalized comparison for every unbounded strict tower, including its
actual strict augmentation maps.

Source: Stacks 09BP; blueprint open-factor argument, normalized by
lem-cbc-exact-product-functor-strict-limit and lem-weil-strict-roos-comparison
(blueprint: lem-sf-open-roos-extension-comparison).

Proof: first apply geometry_products (node proof steps 1--3). The recorded slice
adjunction is exact and additive. Apply exactProductFunctorStrictLimit to this
extension, using the two exact-product assertions. Its normalized signed Roos
identifications thetaA and thetaB have K-injective inclusion (iota,0). The chain
comparison kappa is the canonical product comparison on both signed summands.
Conjugating it by thetaA and thetaB gives lambda, natural on the derived tower
category. The formula for every pair of K-injective resolutions identifies the
same lambda, proving independence of resolutions (node step 4). Finally a strict
augmentation has representative (gamma,0). Projection normalization sends it to
(extension(gamma),0); the strict Roos theorem identifies these with the actual
induced maps. The final equality is lambda composed with extension(a_c)=a_Jc.
Functoriality and the coordinate formulas give naturality in strict tower maps
and augmentation squares (node step 5). Empty opens, zero objects, unbounded
complexes and nonseparated finite-type schemes require no separate assumptions.
-/
theorem comparison
    (D : FiniteFieldDatum.{t}) (_hl : l ≠ D.p)
    (aX : X ⟶ Spec (CommRingCat.of D.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType (U.hom ≫ aX)] [QuasiCompact (U.hom ≫ aX)]
    [IsOpenImmersion U.hom]
    [HasDerivedCategory.{wA} (modulesU l E X U)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ modulesU l E X U)]
    [HasDerivedCategory.{wB} (modulesX l E X)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ modulesX l E X)]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ modulesU l E X U) ⥤
      DerivedCategory.{wA} (modulesU l E X U))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ modulesX l E X) ⥤
      DerivedCategory.{wB} (modulesX l E X))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (modulesU l E X U) ℤ) ⥤
        CochainComplex (modulesU l E X U) ℤ) ⋙ DerivedCategory.Q.{wA} ⟶
      DerivedCategory.Q.{wA} ⋙ LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ modulesU l E X U) (ComplexShape.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (modulesX l E X) ℤ) ⥤
        CochainComplex (modulesX l E X) ℤ) ⋙ DerivedCategory.Q.{wB} ⟶
      DerivedCategory.Q.{wB} ⋙ LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ modulesX l E X) (ComplexShape.up ℤ))) :
    ComparisonAssertions (extension l E X U) LA LB etaA etaB := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, hA, hB, hphi⟩ :=
    geometry_products l E X U D _hl aX
  let := hA
  let := hB
  let : HasSheafify ((Scheme.ProEt.topology X).over U)
      AddCommGrpCat.{max u (t + 1)} := sliceAbSheafify X U
  exact ringed_comparison.{t + 1, t, u, t + 1, t, u, wA, wB}
    ((Scheme.ProEt.topology X).over U)
    ((completedIntegralCoefficientSheafUnrestricted l E X).over U)
    (Scheme.ProEt.topology X) (completedIntegralCoefficientSheafUnrestricted l E X)
    (fun V a b ↦ completedIntegralCoefficient_mul_commUnrestricted l E X
      (op V.unop.left) a b)
    (completedIntegralCoefficient_mul_commUnrestricted l E X)
    (extension l E X U) hphi LA LB etaA _hLA etaB _hLB

end WeilConjectures.SfOpenRoos
