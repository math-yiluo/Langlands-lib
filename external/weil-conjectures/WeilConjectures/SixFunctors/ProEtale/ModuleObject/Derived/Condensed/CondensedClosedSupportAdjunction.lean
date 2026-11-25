/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedSupport
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
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
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Closed support for arbitrary condensed coefficients

Source: blueprint `sec-smooth-purity/sk-prop-sf-localization`,
`sk-lem-formal-closed-support-adjunction.md` and its proof
(blueprint: lemma-sections-support-closed-subscheme).

Inverse image uses the canonical coefficient isomorphism and restriction of scalars along
its inverse. This works for noncommutative rings as well. The finite constant-coefficient
kernel construction is generalized to these coefficients, with the same module operations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]









/-- The kernel of the canonical open unit, functorially in the module.
Source: blueprint formula for Gamma (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def supportKernel {U X : Scheme.{u}} (j : U ⟶ X) :
    supportModules Λ X ⥤ supportModules Λ X where
  obj M := kernel ((supportPullbackAdjunction Λ j).unit.app M)
  map f := kernel.map _ _ f ((lowerStar Λ j).map ((supportPullback Λ j).map f))
    ((supportPullbackAdjunction Λ j).unit.naturality f).symm
  map_id M := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

/-- Kernel inclusion, natural in the module.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def supportKernelι {U X : Scheme.{u}} (j : U ⟶ X) :
    supportKernel Λ j ⟶ 𝟭 _ where
  app M := kernel.ι _
  naturality M N f := by simp [supportKernel]

/-- The support functor is precisely i* ker(id -> j* j*).
Source: blueprint statement formula (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def closedSupport {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    supportModules Λ X ⥤ supportModules Λ Z :=
  supportKernel Λ j ⋙ supportPullback Λ i

/-- Additivity of the kernel formula.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme).
The induced map on kernels is the restriction of the given module map; restriction commutes
with zero and addition. Inverse image is additive, so the composite is additive. -/
@[instance] theorem closedSupport_additive {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    (closedSupport Λ i j).Additive := by
  have : (supportKernel Λ j).Additive :=
    ⟨equalizer.hom_ext (by simp [supportKernel])⟩
  exact inferInstanceAs ((supportKernel Λ j ⋙ supportPullback Λ i).Additive)

/-- The comparison from the kernel to i* i^* of that kernel, given by the unit.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def closedSupportKernelComparison {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) :
    supportKernel Λ j ⟶ closedSupport Λ i j ⋙ lowerStar Λ i :=
  Functor.whiskerLeft (supportKernel Λ j) (supportPullbackAdjunction Λ i).unit ≫
    (Functor.associator _ _ _).inv

private theorem supportCounitOfAbelian {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hAb : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counit) :
    IsIso (supportPullbackAdjunction Λ f).counit := by
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)
  have hε (N) : IsIso (adj.counit.app N) := by
    have hh : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      change IsIso (adj.counit.app N).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  have ff := adj.fullyFaithfulROfIsIsoCounit
  have he := (supportCoefficientEquivalence Λ f).fullyFaithfulInverse
  have hcomp := he.comp ff
  have hfull := hcomp.ofIso
    ((Functor.associator _ _ _).symm ≪≫ comapPullbackHomCompIso Λ f)
  have := hfull.full
  have := hfull.faithful
  exact (supportPullbackAdjunction Λ f).counit_isIso_of_R_fully_faithful

set_option backward.isDefEq.respectTransparency false in
private theorem supportUnitOfAbelian {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : supportModules Λ Y)
    (hAb : IsIso ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X)) :
    IsIso ((supportPullbackAdjunction Λ f).unit.app M) := by
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)
  have hη : IsIso (adj.unit.app M) := by
    have hh : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      change IsIso (adj.unit.app M).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_unit_app_hom]
      exact hAb
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hcomp : IsIso ((adj.comp (supportCoefficientEquivalence Λ f).toAdjunction).unit.app M) := by
    rw [Adjunction.comp_unit_app]
    infer_instance
  change IsIso (((adj.comp (supportCoefficientEquivalence Λ f).toAdjunction).ofNatIsoRight
    ((Functor.associator _ _ _).symm ≪≫ comapPullbackHomCompIso Λ f)).unit.app M)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

private theorem supportOpenCounit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (supportPullbackAdjunction Λ j).counit := by
  have ff := (ProEtale.openImmersionRestrictionLowerStarAdjunction Ab.{u + 1} j
    ).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  exact supportCounitOfAbelian Λ j
    ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).counit_isIso_of_R_fully_faithful)

/-- Clause (1): the kernel comparison is a natural isomorphism.
Source: blueprint proof Steps 3--5 (blueprint: lemma-sections-support-closed-subscheme).
Restriction of the open unit is invertible, hence the kernel restricts to zero on U.
The open--closed exact sequence applied to the kernel then identifies it, by its closed
unit, with i* i^* of itself. The coefficient actions lift these abelian-sheaf identities. -/
theorem closedSupportKernelComparison_isIso {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    IsIso (closedSupportKernelComparison Λ i j) := by
  have := supportOpenCounit Λ j
  have hunit (M : supportModules Λ X) :
      IsIso ((supportPullback Λ j).map ((supportPullbackAdjunction Λ j).unit.app M)) := by
    have h := (supportPullbackAdjunction Λ j).left_triangle_components M
    have : IsIso ((supportPullback Λ j).map
        ((supportPullbackAdjunction Λ j).unit.app M) ≫
          (supportPullbackAdjunction Λ j).counit.app ((supportPullback Λ j).obj M)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((supportPullbackAdjunction Λ j).counit.app ((supportPullback Λ j).obj M))
  have hcomp (M : supportModules Λ X) :
      IsIso ((closedSupportKernelComparison Λ i j).app M) := by
    have hzero : IsZero ((supportPullback Λ j).obj ((supportKernel Λ j).obj M)) :=
      (isZero_kernel_of_mono
        ((supportPullback Λ j).map ((supportPullbackAdjunction Λ j).unit.app M))).of_iso
          (PreservesKernel.iso _ _)
    have habzero := (Mod.forget (condensedRingObj Λ U)).map_isZero hzero
    have hab := (ProEtale.abelian_closed_support_counit_and_unit i j
      (by rw [hij, compl_compl])).2 ((supportKernel Λ j).obj M).X habzero
    have hu := supportUnitOfAbelian Λ i ((supportKernel Λ j).obj M) hab
    simpa only [closedSupportKernelComparison, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id] using hu
  exact NatIso.isIso_of_isIso_app _

/-- The support inclusion, obtained from the inverse kernel comparison.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def closedSupportCounit {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    closedSupport Λ i j ⋙ lowerStar Λ i ⟶ 𝟭 _ :=
  letI := closedSupportKernelComparison_isIso Λ i j hij
  (asIso (closedSupportKernelComparison Λ i j)).inv ≫ supportKernelι Λ j

set_option backward.isDefEq.respectTransparency false in
private theorem supportCrossZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((supportPullback Λ j).obj ((lowerStar Λ i).obj M)) := by
  have hdisjoint : Set.range i.base ∩ Set.range j.base = ∅ := by
    rw [hij]
    exact Set.inter_compl_self _
  have hz : IsZero ((ProEtale.openImmersionRestriction Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)).obj T)
    have hempty : IsEmpty V.left := by
      refine ⟨fun z ↦ ?_⟩
      have hz : (pullback.fst (T.hom ≫ j) i ≫ T.hom ≫ j).base z ∈
          Set.range i.base ∩ Set.range j.base := by
        refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) i z), ?_⟩⟩
        · rw [pullback.condition]
          exact ⟨_, rfl⟩
        · rfl
      rw [hdisjoint] at hz
      exact hz
    exact (isZero_zero Ab.{u + 1}).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X V).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  have hz' : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) :=
    hz.of_iso ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget (condensedRingObj Λ U)).map_injective
  exact hz'.eq_of_src _ _

/-- Clause (1): the adjunction with its canonical support inclusion as counit.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme).
A map from i*A to M has zero composite to j*j^*M, by the open adjunction and j^*i*=0.
It factors uniquely through the kernel. Full faithfulness of i* gives a unique A -> H M.
The construction is natural in both variables and its counit is the displayed inclusion.
A fixed counit determines an adjunction, giving the asserted uniqueness. -/
theorem existsUnique_closedSupportAdjunction {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃! adj : lowerStar Λ i ⊣ closedSupport Λ i j,
      adj.counit = closedSupportCounit Λ i j hij := by
  classical
  have := supportCounitOfAbelian Λ i (ProEtale.abelian_closed_support_counit_and_unit i j
    (by rw [hij, compl_compl])).1
  have ff := (supportPullbackAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  have := closedSupportKernelComparison_isIso Λ i j hij
  let ε := closedSupportCounit Λ i j hij
  have hε (M : supportModules Λ X) : Mono (ε.app M) := by
    change Mono ((inv (closedSupportKernelComparison Λ i j)).app M ≫
      kernel.ι ((supportPullbackAdjunction Λ j).unit.app M))
    infer_instance
  have hvanish {B : supportModules Λ Z} {M : supportModules Λ X}
      (f : (lowerStar Λ i).obj B ⟶ M) :
      f ≫ (supportPullbackAdjunction Λ j).unit.app M = 0 := by
    apply ((supportPullbackAdjunction Λ j).homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    simp only [Functor.map_comp, Functor.map_zero, zero_comp]
    rw [Category.assoc, Adjunction.left_triangle_components, Category.comp_id]
    exact (supportCrossZero Λ i j (by rw [hij, compl_compl]) B).eq_of_src _ _
  let e (B : supportModules Λ Z) (M : supportModules Λ X) :
      (B ⟶ (closedSupport Λ i j).obj M) ≃ ((lowerStar Λ i).obj B ⟶ M) :=
    Equiv.ofBijective (fun g ↦ (lowerStar Λ i).map g ≫ ε.app M) (by
      constructor
      · intro g h heq
        exact (lowerStar Λ i).map_injective ((cancel_mono (ε.app M)).1 heq)
      · intro f
        refine ⟨(lowerStar Λ i).preimage
          (kernel.lift _ f (hvanish f) ≫ (closedSupportKernelComparison Λ i j).app M), ?_⟩
        simp [ε, closedSupportCounit, supportKernelι, Category.assoc])
  let adj : lowerStar Λ i ⊣ closedSupport Λ i j := Adjunction.mkOfHomEquiv
    { homEquiv := fun B M ↦ (e B M).symm
      homEquiv_naturality_left_symm := by
        intro B' B M f g
        change (lowerStar Λ i).map (f ≫ g) ≫ ε.app M =
          (lowerStar Λ i).map f ≫ ((lowerStar Λ i).map g ≫ ε.app M)
        simp [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro B M N f g
        apply (e B N).injective
        rw [Equiv.apply_symm_apply]
        change f ≫ g = (lowerStar Λ i).map
          ((e B M).symm f ≫ (closedSupport Λ i j).map g) ≫ ε.app N
        have hn := ε.naturality g
        change (lowerStar Λ i).map ((closedSupport Λ i j).map g) ≫ ε.app N =
          ε.app M ≫ g at hn
        rw [Functor.map_comp, Category.assoc, hn]
        have hf := (e B M).apply_symm_apply f
        change (lowerStar Λ i).map ((e B M).symm f) ≫ ε.app M = f at hf
        rw [← Category.assoc, hf] }
  have hadj : adj.counit = ε := by
    apply NatTrans.ext
    funext M
    change (e ((closedSupport Λ i j).obj M) M) (𝟙 _) = ε.app M
    simp [e]
  exact ⟨adj, hadj, fun a ha ↦ Adjunction.ext_counit (ha.trans hadj.symm)⟩

/-- The uniquely counit-normalized support adjunction.
Source: blueprint clause (1) (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def closedSupportAdjunction {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    lowerStar Λ i ⊣ closedSupport Λ i j :=
  Classical.choose (ExistsUnique.exists (existsUnique_closedSupportAdjunction Λ i j hij))

/-- Clause (1): left exactness of the additive support functor.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme).
The natural Hom bijection turns the universal property of any finite limit into the same
universal property after applying H. Thus the right adjoint preserves finite limits. -/
theorem closedSupport_leftExact {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    PreservesFiniteLimits (closedSupport Λ i j) := by
  have := (closedSupportAdjunction Λ i j hij).rightAdjoint_preservesLimits
  infer_instance

/-- Closed direct image is exact for a quasi-compact open complement, also for
noncommutative coefficient rings.
Source: blueprint proof Steps 3 and 5 (blueprint: lemma-sections-support-closed-subscheme).
The support adjunction exhibits closed direct image as a left adjoint, so it preserves
colimits, in particular finite colimits. The quasi-compact complement hypothesis is the
one in Stacks, Tag 09BM. -/
theorem closedSupport_lowerStarExact {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    PreservesFiniteColimits (lowerStar Λ i) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
    (closedSupportAdjunction Λ i j hij).leftAdjoint_preservesColimits
  infer_instance

/-- Clause (2): the total right derived support functor is right adjoint to exact i*.
Source: blueprint proof Steps 6--7 (blueprint: lemma-sections-support-closed-subscheme).
The uniquely normalized sheaf adjunction has exact left adjoint. Its right adjoint sends
K-injectives to K-injectives. The termwise Hom adjunction descends to homotopy categories,
and the Hom bijection into K-injectives identifies it with the derived adjunction. -/
noncomputable def closedSupportDerivedAdjunction {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    letI := closedSupport_lowerStarExact Λ i j hij
    (lowerStar Λ i).mapDerivedCategory ⊣ (closedSupport Λ i j).rightDerivedFunctor := by
  let := closedSupport_lowerStarExact Λ i j hij
  exact (closedSupportAdjunction Λ i j hij).mapDerivedCategoryRightDerivedAdjunction

/-- The open derived adjunction, with its canonical derived unit.
Source: blueprint proof Steps 6 and 10 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def closedSupportOpenDerivedAdjunction {U X : Scheme.{u}} (j : U ⟶ X) :
    (supportPullback Λ j).mapDerivedCategory ⊣ (lowerStar Λ j).rightDerivedFunctor :=
  (supportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction

/-- The open pullback of a K-injective is K-injective.
Source: blueprint proof Steps 3 and 10 (blueprint: lemma-sections-support-closed-subscheme).
Extension by zero is an exact left adjoint to open restriction, so its right adjoint
preserves K-injectives. This applies to modules with the transported coefficient action. -/
theorem closedSupport_open_isKInjective {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (I : CochainComplex (supportModules Λ X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((supportPullback Λ j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let a : (Mod.comap (condensedPullbackHom Λ j) ⋙
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
        (condensedRingObj Λ X)) ⊣ supportPullback Λ j :=
    (supportCoefficientEquivalence Λ j).symm.toAdjunction.comp
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction
      (B := condensedRingObj Λ X))
  have := a.preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map I

set_option backward.isDefEq.respectTransparency false in
/-- Clause (2), global RHom form, specified componentwise on K-injective representatives.
Source: blueprint proof Step 8 (blueprint: lemma-sections-support-closed-subscheme).
In degree n apply the sheaf Hom adjunction to every component A^p -> H(I)^(p+n).
Naturality in both differentials intertwines d(f)=d_I f-(-1)^n f d_A. These components
therefore give a Hom-complex isomorphism. H(I) is K-injective by the exact-left-adjoint
criterion; hence both sides compute global RHom. Quasi-isomorphisms in A induce
quasi-isomorphisms here, and changes of injective resolution are homotopy equivalences.
The component formula determines the isomorphism and makes it natural in both variables. -/
theorem closedSupport_globalRHom {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (A : CochainComplex (supportModules Λ Z) ℤ)
    (I : CochainComplex (supportModules Λ X) ℤ) [I.IsKInjective] :
    ∃ e : CochainComplex.HomComplex
        (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
      CochainComplex.HomComplex A
        (((closedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
      ∀ (n : ℤ) (a : CochainComplex.HomComplex.Cochain
        (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
        (p q : ℤ) (hpq : p + n = q),
        (e.hom.f n a) ⟨p, q, hpq⟩ =
          (closedSupportAdjunction Λ i j hij).homEquiv (A.X p) (I.X q) (a ⟨p, q, hpq⟩) := by
  let adj := closedSupportAdjunction Λ i j hij
  let e (n : ℤ) :
      CochainComplex.HomComplex.Cochain
        (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n ≃+
      CochainComplex.HomComplex.Cochain A
        (((closedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n :=
    AddEquiv.piCongrRight (fun T ↦ adj.homAddEquiv (A.X T.p) (I.X T.q))
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (e n).toAddCommGrpIso) ?_, ?_⟩
  · intro n m hnm
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    change (∀ T : CochainComplex.HomComplex.Triplet n,
      (lowerStar Λ i).obj (A.X T.p) ⟶ I.X T.q) at a
    funext T
    rcases T with ⟨p, q, hpq⟩
    change (CochainComplex.HomComplex.δ n m (e n a)) ⟨p, q, hpq⟩ =
      (e m (CochainComplex.HomComplex.δ n m a)) ⟨p, q, hpq⟩
    change
      adj.homEquiv _ _ (a ⟨p, p + n, rfl⟩) ≫
          (closedSupport Λ i j).map (I.d (p + n) q) +
        m.negOnePow • A.d p (p + m - n) ≫
          adj.homEquiv _ _ (a ⟨p + m - n, q, by omega⟩) =
      adj.homEquiv _ _ (a ⟨p, p + n, rfl⟩ ≫ I.d (p + n) q +
        m.negOnePow • (lowerStar Λ i).map (A.d p (p + m - n)) ≫
          a ⟨p + m - n, q, by omega⟩)
    rw [Adjunction.homAddEquiv_add]
    congr 1
    · exact (adj.homEquiv_naturality_right _ _).symm
    · change m.negOnePow • (A.d p (p + m - n) ≫
          adj.homEquiv _ _ (a ⟨p + m - n, q, by omega⟩)) =
        (adj.homAddEquiv _ _) (m.negOnePow •
          ((lowerStar Λ i).map (A.d p (p + m - n)) ≫ a ⟨p + m - n, q, by omega⟩))
      simp only [Units.smul_def, map_zsmul]
      congr 1
      exact (adj.homEquiv_naturality_left _ _).symm
  · intro n a p q hpq
    rfl

private noncomputable def supportOpenExtensionAdjunction {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (Mod.comap (condensedPullbackHom Λ j) ⋙
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
        (condensedRingObj Λ X)) ⊣ supportPullback Λ j :=
  (supportCoefficientEquivalence Λ j).symm.toAdjunction.comp
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction
      (B := condensedRingObj Λ X))

set_option backward.isDefEq.respectTransparency false in
private theorem supportOpenExtensionUnit {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (supportOpenExtensionAdjunction Λ j).unit := by
  let a₀ := ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} j
  have : IsIso a₀.unit :=
    (ProEtale.openImmersionAdjunctionTriple Ab.{u + 1} j).isIso_unit_iff_isIso_counit.mpr
      (ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit Ab.{u + 1} j)
  have ff₀ := a₀.fullyFaithfulLOfIsIsoUnit
  have := ff₀.full
  have := ff₀.faithful
  have hu : IsIso (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  let lin := (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
    ).mapModLeftAdjunction (B := condensedRingObj Λ X)
  have hlinapp (M) : IsIso (lin.unit.app M) := by
    have hh : IsIso ((Mod.forget _).map (lin.unit.app M)) := by
      dsimp [lin, Adjunction.mapModLeftAdjunction, Adjunction.mkOfHomEquiv,
        Adjunction.mk', Mod.forget, Mod.Hom.mk']
      rw [Adjunction.homEquiv_unit]
      simp only [Mod.id_hom']
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso lin.unit := NatIso.isIso_of_isIso_app _
  have ff := lin.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have he := (supportCoefficientEquivalence Λ j).fullyFaithfulInverse
  have hc := he.comp ff
  have : (Mod.comap (condensedPullbackHom Λ j) ⋙
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
        (condensedRingObj Λ X)).Full := hc.full
  have : (Mod.comap (condensedPullbackHom Λ j) ⋙
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
        (condensedRingObj Λ X)).Faithful := hc.faithful
  exact (supportOpenExtensionAdjunction Λ j).unit_isIso_of_L_fully_faithful

set_option backward.isDefEq.respectTransparency false in
private theorem supportOpenExtensionCounitMono {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M : supportModules Λ X) :
    Mono ((supportOpenExtensionAdjunction Λ j).counit.app M) := by
  let a := supportOpenExtensionAdjunction Λ j
  have := supportOpenExtensionUnit Λ j
  have hm : IsIso ((supportPullback Λ j).map (a.counit.app M)) := by
    have : IsIso (a.unit.app ((supportPullback Λ j).obj M) ≫
        (supportPullback Λ j).map (a.counit.app M)) := by
      rw [a.right_triangle_components]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (a.unit.app _) _
  let N := kernel (a.counit.app M)
  have hz : IsZero ((supportPullback Λ j).obj N) :=
    (isZero_kernel_of_mono ((supportPullback Λ j).map (a.counit.app M))).of_iso
      (PreservesKernel.iso _ _)
  have hAb : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj N.X) := by
    exact (Mod.forget _).map_isZero hz
  have hRes : IsZero ((ProEtale.openImmersionRestriction Ab.{u + 1} j).obj N.X) :=
    hAb.of_iso ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app N.X).symm
  have hzero : IsZero N.X :=
    ProEtale.isZero_of_mono_openImmersionLowerShriek Ab.{u + 1} j
      ((Mod.forget _).map (kernel.ι (a.counit.app M))) hRes
  apply Preadditive.mono_of_isZero_kernel
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget _).map_injective
  exact hzero.eq_of_src _ _

private theorem supportInjectiveUnitEpi
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R F : D ⥤ C} (adj : L ⊣ R) (adj' : F ⊣ L)
    (I : C) [Injective I] [Mono (adj'.counit.app (R.obj (L.obj I)))] :
    Epi (adj.unit.app I) := by
  let φ := (adj'.homEquiv _ _).symm (adj.counit.app (L.obj I))
  let σ : R.obj (L.obj I) ⟶ I := Injective.factorThru φ (adj'.counit.app _)
  have hσ : adj'.counit.app _ ≫ σ = φ := Injective.comp_factorThru _ _
  have hs : IsSplitEpi (adj.unit.app I) := by
    refine ⟨⟨σ, ?_⟩⟩
    apply (adj.homEquiv _ _).symm.injective
    have h₁ : L.map σ = adj.counit.app _ := by
      have h := congrArg (adj'.homEquiv _ _) hσ
      have he : (adj'.homEquiv (L.obj (R.obj (L.obj I))) I) φ =
          adj.counit.app (L.obj I) := (adj'.homEquiv _ _).apply_symm_apply _
      rw [he, Adjunction.homEquiv_unit, Functor.map_comp,
        ← Category.assoc, adj'.right_triangle_components, Category.id_comp] at h
      exact h
    change L.map (σ ≫ adj.unit.app I) ≫ adj.counit.app (L.obj I) =
      L.map (𝟙 (R.obj (L.obj I))) ≫ adj.counit.app (L.obj I)
    calc
      _ = L.map σ ≫ (L.map (adj.unit.app I) ≫ adj.counit.app (L.obj I)) := by
        rw [Functor.map_comp, Category.assoc]
      _ = L.map σ := by rw [adj.left_triangle_components I, Category.comp_id]
      _ = adj.counit.app (L.obj I) := h₁
      _ = _ := by rw [L.map_id, Category.id_comp]
  infer_instance

/-- Clause (3): the open unit is an epimorphism for every injective module.
Source: blueprint proof Step 9 (blueprint: lemma-sections-support-closed-subscheme).
The comparison j!j^*I -> j*j^*I is monic: its kernel has zero open and closed
restrictions, hence is zero by localization. Extend its map to I using injectivity.
After restriction the resulting section is the identity. Faithfulness on open direct
images implies that it splits the unit, which is therefore an epimorphism of sheaves. -/
theorem closedSupport_injective_unit_epi {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (I : supportModules Λ X) [Injective I] :
    Epi ((supportPullbackAdjunction Λ j).unit.app I) := by
  have _ := hij
  have := supportOpenExtensionCounitMono Λ j
    ((lowerStar Λ j).obj ((supportPullback Λ j).obj I))
  exact supportInjectiveUnitEpi (supportPullbackAdjunction Λ j)
    (supportOpenExtensionAdjunction Λ j) I

private theorem supportJointZero {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (M : supportModules Λ X)
    (hi : IsZero ((supportPullback Λ i).obj M))
    (hj : IsZero ((supportPullback Λ j).obj M)) : IsZero M := by
  have hAb := (Mod.forget _).map_isZero hj
  have hunit := supportUnitOfAbelian Λ i M
    ((ProEtale.abelian_closed_support_counit_and_unit i j (by rw [hij, compl_compl])).2 M.X hAb)
  exact ((lowerStar Λ i).map_isZero hi).of_iso
    (asIso ((supportPullbackAdjunction Λ i).unit.app M))

/-- Clause (4): the counit/unit localization triangle, natural on the unbounded category.
Source: blueprint proof Steps 10--11 (blueprint: lemma-sections-support-closed-subscheme).
Resolve K by a K-injective I with injective terms. Open restriction preserves
K-injectives, so j*j^*I computes Rj*j^*K. The kernel identification and surjectivity in
Step 9 give a degreewise short exact sequence i*H(I) -> I -> j*j^*I. Its canonical
connecting morphism gives the distinguished triangle. The short-exact-sequence triangle
is natural; maps between K-injective resolutions represent all derived maps, and
homotopies descend, giving a natural transformation as the connecting arrow. -/
theorem closedSupport_triangle {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    letI := closedSupport_lowerStarExact Λ i j hij
    ∃ δ : (supportPullback Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
      ((closedSupport Λ i j).rightDerivedFunctor ⋙ (lowerStar Λ i).mapDerivedCategory) ⋙
        shiftFunctor (DerivedCategory (supportModules Λ X)) (1 : ℤ),
      ∀ K : DerivedCategory (supportModules Λ X),
        Triangle.mk ((closedSupportDerivedAdjunction Λ i j hij).counit.app K)
          ((closedSupportOpenDerivedAdjunction Λ j).unit.app K) (δ.app K) ∈
            Pretriangulated.distinguishedTriangles := by
  let := closedSupport_lowerStarExact Λ i j hij
  classical
  have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
    (closedSupportAdjunction Λ i j hij).leftAdjoint_preservesColimits
  have hc := supportCounitOfAbelian Λ i
    (ProEtale.abelian_closed_support_counit_and_unit i j (by rw [hij, compl_compl])).1
  have ff := (supportPullbackAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  have := supportOpenCounit Λ j
  have ffj := (supportPullbackAdjunction Λ j).fullyFaithfulROfIsIsoCounit
  have := ffj.full
  have := ffj.faithful
  have : (lowerStar Λ i).PreservesKInjectiveComplexes :=
    (supportPullbackAdjunction Λ i).preservesKInjectiveComplexes
  have : (lowerStar Λ j).PreservesKInjectiveComplexes :=
    (supportPullbackAdjunction Λ j).preservesKInjectiveComplexes
  let L := (lowerStar Λ i).mapDerivedCategory
  let J := (supportPullback Λ j).mapDerivedCategory
  let aj := closedSupportOpenDerivedAdjunction Λ j
  let ac := closedSupportDerivedAdjunction Λ i j hij
  have : IsIso aj.counit := aj.counit_isIso_of_R_fully_faithful
  have : L.Full := Functor.Full.of_iso
    (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  have : L.Faithful := Functor.Faithful.of_iso
    (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  have hzero (M : DerivedCategory (supportModules Λ Z)) : IsZero (J.obj (L.obj M)) := by
    exact (Functor.isZero_mapDerivedCategory_obj (lowerStar Λ i ⋙ supportPullback Λ j)
      M (fun n ↦ supportCrossZero Λ i j (by rw [hij, compl_compl]) _)).of_iso
        (((lowerStar Λ i).mapDerivedCategoryCompIso _).app M)
  have hjoint (M : DerivedCategory (supportModules Λ X))
      (hi : IsZero ((supportPullback Λ i).mapDerivedCategory.obj M))
      (hj : IsZero (J.obj M)) : IsZero M := by
    rw [DerivedCategory.isZero_iff]
    intro n
    exact supportJointZero Λ i j hij _
      (((DerivedCategory.homologyFunctor _ n).map_isZero hi).of_iso
        (((supportPullback Λ i).mapDerivedCategoryHomologyFunctorIso n).app M))
      (((DerivedCategory.homologyFunctor _ n).map_isZero hj).of_iso
        (((supportPullback Λ j).mapDerivedCategoryHomologyFunctorIso n).app M))
  have hess (M : DerivedCategory (supportModules Λ X)) (hM : IsZero (J.obj M)) :
      L.essImage M := by
    let ai := ((supportPullbackAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction
      ).ofNatIsoRight (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
    have : IsIso ai.counit := ai.counit_isIso_of_R_fully_faithful
    obtain ⟨W, v, w, hW⟩ := distinguished_cocone_triangle (ai.unit.app M)
    have hiu : IsIso ((supportPullback Λ i).mapDerivedCategory.map (ai.unit.app M)) :=
      have := IsIso.id ((supportPullback Λ i).mapDerivedCategory.obj M)
      IsIso.of_isIso_fac_right (ai.left_triangle_components M)
    have hju : IsIso (J.map (ai.unit.app M)) :=
      isIso_of_source_target_iso_zero _ hM.isoZero (hzero _).isoZero
    have hz : IsZero W := hjoint W
      ((Triangle.isZero₃_iff_isIso₁ _
        ((supportPullback Λ i).mapDerivedCategory.map_distinguished _ hW)).2 hiu)
      ((Triangle.isZero₃_iff_isIso₁ _ (J.map_distinguished _ hW)).2 hju)
    have : IsIso (ai.unit.app M) := (Triangle.isZero₃_iff_isIso₁ _ hW).1 hz
    exact ⟨_, ⟨(asIso (ai.unit.app M)).symm⟩⟩
  have hex (K) := Recollement.existsUnique_distTriang_counit_unit aj ac
    (Functor.FullyFaithful.ofFullyFaithful L) hzero hess K
  choose δ hδ huniq using hex
  refine ⟨{ app := δ, naturality := ?_ }, fun K ↦ hδ K⟩
  intro K K' f
  obtain ⟨τ, h₁, h₂, h₃⟩ := Recollement.exists_triangleHom aj ac hzero f (hδ K) (hδ K')
  have h := τ.comm₃
  rw [h₁, h₃] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem supportOpenUnitComparison {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (I : CochainComplex (supportModules Λ X) ℤ) [I.IsKInjective] :
    ∃ e : (lowerStar Λ j).rightDerivedFunctor.obj
        ((supportPullback Λ j).mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≅
      DerivedCategory.Q.obj
        (((lowerStar Λ j).mapHomologicalComplex (.up ℤ)).obj
          (((supportPullback Λ j).mapHomologicalComplex (.up ℤ)).obj I)),
      (closedSupportOpenDerivedAdjunction Λ j).unit.app (DerivedCategory.Q.obj I) ≫
        e.hom = DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (supportPullbackAdjunction Λ j).unit
            (.up ℤ)).app I) := by
  let L := supportPullback Λ j
  let R := lowerStar Λ j
  let a := supportPullbackAdjunction Λ j
  let g := (a.mapHomologicalComplex (.up ℤ)).unit.app I
  let IH := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let LI := (L.mapHomologicalComplex (.up ℤ)).obj I
  have : CochainComplex.IsKInjective LI := closedSupport_open_isKInjective Λ j I
  let ρ := R.rightDerivedFunctorUnit
  have : IsIso (ρ.app ((L.mapHomotopyCategory (.up ℤ)).obj IH)) := by
    change IsIso (R.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj LI))
    infer_instance
  let eh := R.rightDerivedFunctor.mapIso (L.mapDerivedCategoryFactorsh.app IH) ≪≫
    (asIso (ρ.app ((L.mapHomotopyCategory (.up ℤ)).obj IH))).symm
  have hh : a.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Qh.obj IH) ≫ eh.hom =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app IH) := by
    have h := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom ρ IH
    dsimp only [eh, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app
        (DerivedCategory.Qh.obj IH) ≫ R.rightDerivedFunctor.map
          (L.mapDerivedCategoryFactorsh.app IH).hom = _ at h
    rw [← Category.assoc, h]
    change (_ ≫ ρ.app ((L.mapHomotopyCategory (.up ℤ)).obj IH)) ≫
      inv (ρ.app ((L.mapHomotopyCategory (.up ℤ)).obj IH)) = _
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hu : (a.mapHomotopyCategory (.up ℤ)).unit.app IH =
      (HomotopyCategory.quotient _ (.up ℤ)).map g := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  let e := R.rightDerivedFunctor.mapIso
      (L.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso _).app I).symm) ≪≫
    eh ≪≫ (DerivedCategory.quotientCompQhIso _).app
      ((R.mapHomologicalComplex (.up ℤ)).obj LI)
  refine ⟨e, ?_⟩
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj I) ≫
    R.rightDerivedFunctor.map (L.mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso _).app I).inv) ≫ eh.hom ≫
      ((DerivedCategory.quotientCompQhIso _).app
        ((R.mapHomologicalComplex (.up ℤ)).obj LI)).hom = _
  have hn := a.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    ((DerivedCategory.quotientCompQhIso _).app I).inv
  change _ = a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
    R.rightDerivedFunctor.map (L.mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso _).app I).inv) at hn
  rw [← Category.assoc, ← Category.assoc, ← hn]
  simp only [Functor.id_map]
  have hh' := congrArg (fun f ↦
    ((DerivedCategory.quotientCompQhIso _).app I).inv ≫ f ≫
      ((DerivedCategory.quotientCompQhIso _).app
        ((R.mapHomologicalComplex (.up ℤ)).obj LI)).hom) hh
  rw [hu] at hh'
  calc
    _ = ((DerivedCategory.quotientCompQhIso _).app I).inv ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map g) ≫
        ((DerivedCategory.quotientCompQhIso _).app
          ((R.mapHomologicalComplex (.up ℤ)).obj LI)).hom := by
      dsimp only [IH, Functor.comp_obj] at hh' ⊢
      simpa only [Category.assoc] using hh'
    _ = _ := by
      change _ = DerivedCategory.Q.map g
      have hnat := DerivedCategory.quotientCompQhIso_hom_naturality g
      have hresult := congrArg (fun f ↦
        ((DerivedCategory.quotientCompQhIso _).app I).inv ≫ f) hnat
      simpa only [Iso.app_inv, Iso.app_hom, Functor.id_obj, Category.assoc,
        Iso.inv_hom_id_app_assoc, R, L, LI, Functor.comp_obj] using hresult

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Clause (4), explicit fibre comparison on K-injective representatives.
Source: blueprint proof Step 11 (blueprint: lemma-sections-support-closed-subscheme).
First replace I by a homotopy equivalent K-injective J with injective terms. Additive
functors and the cone construction preserve this equivalence. For g:J -> j*j^*J the
canonical map i*H(J) -> cone(g)[-1] is n |-> (0,n).
Locally lift the first component of a fibre cocycle along the degreewise epimorphism g
and subtract d(0,-c); this proves surjectivity on cohomology. For a boundary (0,k)=d(a,b),
lift a to c and write k=d(b+dc) in the kernel; this proves injectivity. The map is thus a
quasi-isomorphism. Exact i^* and i^*i*=id identify RH(QI) with i^* of that fibre.
The fibre used here is the actual shifted mapping cone of the canonical unit. -/
theorem closedSupport_fiber {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (supportModules Λ X))
    (I : CochainComplex (supportModules Λ X) ℤ) [I.IsKInjective]
    (e : K ≅ DerivedCategory.Q.obj I) :
    Nonempty ((closedSupport Λ i j).rightDerivedFunctor.obj K ≅
      (supportPullback Λ i).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((CochainComplex.mappingCone
            ((NatTrans.mapHomologicalComplex (supportPullbackAdjunction Λ j).unit
              (ComplexShape.up ℤ)).app I))⟦(-1 : ℤ)⟧))) := by
  let := closedSupport_lowerStarExact Λ i j hij
  classical
  have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
    (closedSupportAdjunction Λ i j hij).leftAdjoint_preservesColimits
  obtain ⟨δ, hδ⟩ := closedSupport_triangle Λ i j hij
  let KI := DerivedCategory.Q.obj I
  let g := (NatTrans.mapHomologicalComplex (supportPullbackAdjunction Λ j).unit
    (.up ℤ)).app I
  let T := Triangle.mk ((closedSupportDerivedAdjunction Λ i j hij).counit.app KI)
    ((closedSupportOpenDerivedAdjunction Λ j).unit.app KI) (δ.app KI)
  let S := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle g)
  obtain ⟨eu, heu⟩ := supportOpenUnitComparison Λ j I
  let et := isoTriangleOfIso₁₂ T.rotate S.rotate (rot_of_distTriang _ (hδ KI))
    (rot_of_distTriang _ (DerivedCategory.mappingCocone_triangle_distinguished g))
    (Iso.refl _) eu (by
      change _ = 𝟙 _ ≫ DerivedCategory.Q.map g
      rw [Category.id_comp]
      convert heu using 1
      rfl)
  let ec := (shiftFunctor (DerivedCategory (supportModules Λ X)) (1 : ℤ)).preimageIso
    (Triangle.π₃.mapIso et)
  have hc := supportCounitOfAbelian Λ i
    (ProEtale.abelian_closed_support_counit_and_unit i j (by rw [hij, compl_compl])).1
  have ff := (supportPullbackAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  have : (lowerStar Λ i).PreservesKInjectiveComplexes :=
    (supportPullbackAdjunction Λ i).preservesKInjectiveComplexes
  have : (lowerStar Λ i).mapDerivedCategory.Full := Functor.Full.of_iso
    (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  have : (lowerStar Λ i).mapDerivedCategory.Faithful := Functor.Faithful.of_iso
    (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  let ai := ((supportPullbackAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction
    ).ofNatIsoRight (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  have : IsIso ai.counit := ai.counit_isIso_of_R_fully_faithful
  exact ⟨(closedSupport Λ i j).rightDerivedFunctor.mapIso e ≪≫
    (asIso (ai.counit.app ((closedSupport Λ i j).rightDerivedFunctor.obj KI))).symm ≪≫
    (supportPullback Λ i).mapDerivedCategory.mapIso ec⟩

end AlgebraicGeometry.ProEtale.CondensedRing
