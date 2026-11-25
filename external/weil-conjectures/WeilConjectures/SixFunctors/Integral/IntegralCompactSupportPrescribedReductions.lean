/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.Compact.CompactSupportNormalizedRealization
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.Compactification.BoundaryPreparation
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
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
import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity

/-!
# Integral compact supports have the prescribed reductions

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2135 (blueprint: lemma-change-coefficients-compact-support).

The integral value is specified by a Roos triangle of the very tower used in
`sfIntegralCompactSupportValue`. Specifying its projection retains the data needed
for the canonical coefficient maps, which are their tensor/restriction adjoints.
The result applies to every realization of that defining derived limit, including
its chosen value, and imposes no extra condition on the input. Natural index n
always denotes the positive exponent n+1.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] scalarReductionDerivedExtension
  scalarReductionExistence scalarReductionDerivedExistence
  pbcRestrictComp normalizedDVRRestrictionCompIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- Countable products for the defining compact-support tower, obtained from the
recorded completed-coefficient derived products, with no extra existence assumption.
Source: blueprint order 2135, Proof paragraph 2; Stacks Tag 07KC
(blueprint: lemma-change-coefficients-compact-support). -/
noncomputable instance coefCompactSupportHasProduct
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    HasProduct (sfCompactSupportTerm l E c K) := by
  let : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  infer_instance

private theorem derivedNatIso_refl
    {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.mapDerivedCategoryNatIso (Iso.refl F) = Iso.refl F.mapDerivedCategory := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro I
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app I)).1
  erw [Functor.mapDerivedCategoryNatIso_fac]
  change F.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map (𝟙 _) =
    𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app I
  simp

private theorem derived_eqToIso
    {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F G : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    HEq (Functor.mapDerivedCategoryNatIso (eqToIso h))
      (Iso.refl G.mapDerivedCategory) := by
  subst G
  exact heq_of_eq (derivedNatIso_refl F)

private theorem derived_functor_congr
    {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F G : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    F.mapDerivedCategory = G.mapDerivedCategory := by
  subst G
  rfl

private theorem derived_comp_heq
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F F' : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (h : F = F') (e : F ⋙ G ≅ H) (e' : F' ⋙ G ≅ H) (he : HEq e e') :
    HEq (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e)
      (Functor.mapDerivedCategoryCompIso F' G ≪≫
        Functor.mapDerivedCategoryNatIso e') := by
  subst F'
  have hh := eq_of_heq he
  subst e'
  rfl

-- Comparing the sectionwise associators elaborates dependent restriction functors.
private theorem ordinary_restriction_comp
    (W : Scheme.{u}) {A B C : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k) :
    pbcRestrictComp f g k h =
      normalizedDVRRestrictionCompIso
          ((sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f)
          ((sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g) ≪≫
        eqToIso (congrArg (fun q ↦ SheafOfModules.restrictScalars.{u + 1} q)
          (show (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f ≫
            (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g =
              (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k from
            ((sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_comp f g).symm.trans
              (congrArg (fun q ↦ (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q) h))) := by
  subst k
  unfold pbcRestrictComp
  exact (pbcRestrictComp_exists f g (f ≫ g) rfl).unique
    (pbcRestrictComp_exists f g (f ≫ g) rfl).exists.choose_spec
    (by
      intro M U x
      unfold normalizedDVRRestrictionCompIso
      simp only [Iso.refl_hom, Iso.trans_hom, eqToIso.hom,
        eqToHom_refl, NatTrans.id_app, Category.comp_id]
      rfl)

private theorem ordinary_restriction_comp_heq
    (W : Scheme.{u}) {A B C : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (q : (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B ⟶
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj C)
    (hq : q = (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
    (he : (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f ≫ q =
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k) :
    HEq (normalizedDVRRestrictionCompIso
        ((sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f) q ≪≫
      eqToIso (congrArg (fun r ↦ SheafOfModules.restrictScalars.{u + 1} r) he))
      (pbcRestrictComp f g k h) := by
  subst q
  exact heq_of_eq (ordinary_restriction_comp W f g k h).symm

private theorem quotient_adjacent (W : Scheme.{u}) (n : ℕ) :
    normalizedDVRQuotient l E W n.le_succ =
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift)) := by
  exact Functor.ofOpSequence_map_homOfLE_succ _ n

private theorem restriction_iso_adjacent (W : Scheme.{u}) (n : ℕ) :
    HEq (coefCompactSupportRestrictionIso l E W n.le_succ)
      (Iso.refl (sfCompactSupportFiniteRestriction l E W n).mapDerivedCategory) := by
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E (n + 1) n n.le_succ)
  unfold coefCompactSupportRestrictionIso
  have h := derived_eqToIso (normalizedDVRModuleRes l E W n.le_succ)
    (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ))
    (congrArg (fun q ↦ SheafOfModules.restrictScalars.{u + 1} q)
      (coefCompactSupportQuotient_eq l E W n.le_succ))
  convert h using 1
  congr 2

private theorem restriction_comp_eq (W : Scheme.{u}) (D : FiniteFieldDatum.{u})
    (hl : l ≠ D.p) (n : ℕ) :
    HEq (sfCompactSupportDerivedRestrictionComp l E W n)
      (normalizedDVRResCompletedComp l E W D hl (Nat.le_succ n)) := by
  unfold sfCompactSupportDerivedRestrictionComp normalizedDVRResCompletedComp
  apply derived_comp_heq
    (sfCompactSupportFiniteRestriction l E W n)
    (normalizedDVRModuleRes l E W n.le_succ)
    (scalarReductionRestriction l E W (n + 1)) (scalarReductionRestriction l E W n)
  · unfold normalizedDVRModuleRes
    rw [quotient_adjacent]
  · exact (ordinary_restriction_comp_heq W
      (completedIntegralCommRingProjectionUnrestricted l E W (n + 1))
      ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift))
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (sfCompactSupportProjection_transition l E W n)
      (normalizedDVRQuotient l E W n.le_succ) (quotient_adjacent l E W n)
      (limit.w (integralCoefficientSheafSystem l E W) (homOfLE n.le_succ).op)).symm

private theorem restriction_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (S S' : A ⥤ B) (R : B ⥤ C) (R' : A ⥤ C)
    (h : S = S') (i : S ≅ S') (hi : HEq i (Iso.refl S'))
    (e : S ⋙ R ≅ R') (e' : S' ⋙ R ≅ R') (he : HEq e e')
    {P : B} (Q : A) (v : P ⟶ S'.obj Q) :
    R.map (v ≫ i.inv.app Q) ≫ e.hom.app Q = R.map v ≫ e'.hom.app Q := by
  subst S'
  have hi' := eq_of_heq hi
  subst i
  have he' := eq_of_heq he
  subst e'
  simp

private theorem adjacentRoosProjection
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle f L p δ) (n : ℕ) :
    p ≫ Pi.π K (n + 1) ≫ f n = p ≫ Pi.π K n := by
  have hz : p ≫ towerTransitionEndomorphism f = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ _ hc
  have hn := congrArg (fun a ↦ a ≫ Pi.π K n) hz
  simp only [towerTransitionEndomorphism, Preadditive.comp_sub, Category.comp_id,
    Preadditive.sub_comp, Category.assoc, towerProductShift, Pi.lift_comp_π,
    zero_comp] at hn
  exact (sub_eq_zero.mp hn).symm

private theorem adjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    {M : C} {P : A} {Q : B} (a : M ⟶ Rm.obj P) (b : M ⟶ Rn.obj Q)
    (v : P ⟶ S.obj Q) (h : a ≫ Rm.map v ≫ e.hom.app Q = b) :
    (am.homEquiv M P).symm a ≫ v =
      (am.homEquiv M (S.obj (Ln.obj M))).symm
          (an.unit.app M ≫ e.inv.app (Ln.obj M)) ≫
        S.map ((an.homEquiv M Q).symm b) := by
  apply (am.homEquiv M (S.obj Q)).injective
  rw [am.homEquiv_naturality_right, Equiv.apply_symm_apply,
    am.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply (cancel_mono (e.hom.app Q)).1
  simp only [Category.assoc]
  have he := e.hom.naturality ((an.homEquiv M Q).symm b)
  dsimp only [Functor.comp_map] at he
  rw [he]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← an.homEquiv_unit, Equiv.apply_symm_apply]
  exact h

open CategoryTheory.Pretriangulated in
private theorem roosTransport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : ℕ → C} [HasProduct X]
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    (M : C) (p : M ⟶ ∏ᶜ X) (δ : (∏ᶜ X) ⟶ M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle f M p δ)
    (a : ∀ n, X n ≅ Y n) (q : ∀ n, M ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p ≫ Pi.π X n ≫ (a n).hom = q n) :
    ∃ hprod : HasProduct Y, letI := hprod
      ∃ δ' : (∏ᶜ Y) ⟶ M⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g M (Pi.lift q) δ' := by
  let : HasProduct Y :=
    hasProduct_of_equiv_of_iso X Y (Equiv.refl ℕ) (fun n ↦ (a n).symm)
  let A : (∏ᶜ X) ≅ (∏ᶜ Y) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨inferInstance, A.inv ≫ δ, ?_⟩
  apply isomorphic_distinguished _ hc _
  refine Triangle.isoMk _ _ (Iso.refl M) A.symm A.symm ?_ ?_ ?_
  · change Pi.lift q ≫ A.inv = 𝟙 M ≫ p
    apply Pi.hom_ext
    intro n
    simp only [A, Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc,
      Category.id_comp]
    apply (cancel_mono (a n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using (hp n).symm
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ht n))).symm
  · change (A.inv ≫ δ) ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 M) = A.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem support_of_torAmplitude (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b := by
  classical
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} := proEtaleConstantRing X A
  let C := SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  have := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  have : (DerivedCategory.Q (C := C)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso C (.up ℤ))
  let L := (DerivedCategory.Q (C := C)).objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K :=
    (DerivedCategory.Q (C := C)).objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionGeneral.{u + 1, u} (R := R) L
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let et : derivedTensor X A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C))
      P f hf hP ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  intro i hi
  by_contra hout
  have hoff : i < a ∨ b < i := by
    change ¬ (a ≤ i ∧ i ≤ b) at hout
    omega
  have hz := h.2 L P ⟨e⟩ f hf hP (MonoidalCategory.tensorUnit C) i hoff
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso et.symm))

private theorem torAmplitude_of_iso (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A L a b) :
    HasProEtaleTorAmplitude X A K a b := by
  refine ⟨h.1, ?_⟩
  intro Q P hQ f hf hP M i hi
  obtain ⟨eQ⟩ := hQ
  exact h.2 Q P ⟨eQ ≪≫ e⟩ f hf hP M i hi

end WeilConjectures
