/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedSupport
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction

import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-!
# Formal closed support for arbitrary condensed rings

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-formal-closed-support-adjunction, clauses (1)--(4)
(blueprint: lemma-sections-support-closed-subscheme).

The inverse coefficient comparison is used to transport the module action. In particular
no commutativity, constructibility or boundedness hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-- Modules over the actual pulled-back coefficient ring, including noncommutative rings.
Source: blueprint opening paragraph (blueprint: lemma-sections-support-closed-subscheme). -/
abbrev FormalSupportModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The module category is Grothendieck abelian without a commutativity hypothesis.
Source: blueprint proof Step 6 (blueprint: lemma-sections-support-closed-subscheme). -/
instance formalSupportModules_grothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (FormalSupportModules Λ X) :=
  Mod.isGrothendieckAbelian.{u + 1} (condensedRingObj Λ X)

/-- Inverse image followed by transport of the action along the canonical coefficient iso.
Source: blueprint opening paragraph and proof Steps 1--2
(blueprint: lemma-sections-support-closed-subscheme). -/
def formalSupportPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FormalSupportModules Λ Y ⥤ FormalSupportModules Λ X :=
  (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).inverse

/-- The canonical module adjunction, obtained by lifting the sheaf adjunction and
transporting scalars. Source: blueprint proof Step 2
(blueprint: lemma-sections-support-closed-subscheme). -/
abbrev formalSupportPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    formalSupportPullback Λ f ⊣ lowerStar Λ f :=
  supportPullbackAdjunction Λ f

/-- The transported inverse image is additive.
Source: blueprint proof Step 2 (blueprint: lemma-sections-support-closed-subscheme). -/
instance formalSupportPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (formalSupportPullback Λ f).Additive :=
  inferInstanceAs ((_ ⋙ Mod.comap (asIso (condensedPullbackHom Λ f)).inv).Additive)

/-- Exactness of inverse image on the underlying abelian sheaves and scalar transport.
Source: blueprint proof Step 2 (blueprint: lemma-sections-support-closed-subscheme). -/
instance formalSupportPullback_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (formalSupportPullback Λ f) :=
  inferInstanceAs (PreservesFiniteLimits (_ ⋙
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).inverse))

/-- Cokernels commute with inverse image and scalar transport.
Source: blueprint proof Step 2 (blueprint: lemma-sections-support-closed-subscheme). -/
instance formalSupportPullback_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (formalSupportPullback Λ f) :=
  inferInstanceAs (PreservesFiniteColimits (_ ⋙
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).inverse))

/-- The kernel of the open adjunction unit, on objects and morphisms.
Source: blueprint clause (1), generalizing definition-local-cohomology--1
(blueprint: lemma-sections-support-closed-subscheme). -/
def formalSupportKernel {V X : Scheme.{u}} (j : V ⟶ X) :
    FormalSupportModules Λ X ⥤ FormalSupportModules Λ X where
  obj M := kernel ((formalSupportPullbackAdjunction Λ j).unit.app M)
  map f := kernel.map _ _ f
    ((lowerStar Λ j).map ((formalSupportPullback Λ j).map f))
    ((formalSupportPullbackAdjunction Λ j).unit.naturality f).symm
  map_id M := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

/-- The support kernel respects addition, by the universal property of the kernel.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme). -/
instance formalSupportKernel_additive {V X : Scheme.{u}} (j : V ⟶ X) :
    (formalSupportKernel Λ j).Additive where
  map_add := equalizer.hom_ext (by simp [formalSupportKernel])

/-- The closed support functor is exactly i* ker(id → j*j*).
Source: blueprint opening formula (blueprint: lemma-sections-support-closed-subscheme). -/
def formalClosedSupport {Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) :
    FormalSupportModules Λ X ⥤ FormalSupportModules Λ Z :=
  formalSupportKernel Λ j ⋙ formalSupportPullback Λ i

/-- Additivity of the displayed support formula.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme). -/
instance formalClosedSupport_additive {Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) :
    (formalClosedSupport Λ i j).Additive :=
  inferInstanceAs ((formalSupportKernel Λ j ⋙ formalSupportPullback Λ i).Additive)

/-- The canonical support-kernel inclusion.
Source: blueprint clause (1) (blueprint: lemma-sections-support-closed-subscheme). -/
def formalSupportKernelInclusion {V X : Scheme.{u}} (j : V ⟶ X) :
    formalSupportKernel Λ j ⟶ 𝟭 (FormalSupportModules Λ X) where
  app M := kernel.ι ((formalSupportPullbackAdjunction Λ j).unit.app M)
  naturality _ _ f := by simp [formalSupportKernel]

/-- The canonical closed unit on the support kernel; clause (1) says it is invertible.
Source: blueprint proof Step 5 (blueprint: lemma-sections-support-closed-subscheme). -/
def formalSupportKernelComparison {Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) :
    formalSupportKernel Λ j ⟶ formalClosedSupport Λ i j ⋙ lowerStar Λ i :=
  Functor.whiskerLeft (formalSupportKernel Λ j)
    (formalSupportPullbackAdjunction Λ i).unit

private theorem comparison_eq {Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) :
    formalSupportKernelComparison Λ i j = closedSupportKernelComparison Λ i j := by
  apply NatTrans.ext
  funext M
  simp only [formalSupportKernelComparison, closedSupportKernelComparison,
    NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id]
  rfl

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

private theorem supportTriangle {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    [HasDerivedCategory.{w} (supportModules Λ X)]
    [HasDerivedCategory.{w} (supportModules Λ Z)]
    [HasDerivedCategory.{w} (supportModules Λ U)] :
    letI := closedSupport_lowerStarExact Λ i j hij
    ∃ δ : (supportPullback Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
      ((closedSupport Λ i j).rightDerivedFunctor ⋙ (lowerStar Λ i).mapDerivedCategory) ⋙
        shiftFunctor (DerivedCategory (supportModules Λ X)) (1 : ℤ),
      ∀ K : DerivedCategory (supportModules Λ X),
        Triangle.mk
          ((closedSupportAdjunction Λ i j hij).mapDerivedCategoryRightDerivedAdjunction.counit.app
            K)
          ((supportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app K)
          (δ.app K) ∈ Pretriangulated.distinguishedTriangles := by
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
  let aj := (supportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction
  let ac := (closedSupportAdjunction Λ i j hij).mapDerivedCategoryRightDerivedAdjunction
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

set_option linter.unusedVariables false in
/-- Sections with closed support, all four clauses, for arbitrary condensed coefficients.
The Hom-complex clause uses global abelian-group-valued Hom, on K-injective targets.
The last clause describes the fibre without selecting a cone in a triangulated category:
it holds for every distinguished fibre triangle of the specified open adjunction unit.

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization,
lemma-sections-support-closed-subscheme (1)--(4)
(blueprint: lemma-sections-support-closed-subscheme).

Proof:
1. Identify inverse-image coefficient rings by lemma-inverse-image-coefficient-sheaves--1. Lift
inverse/direct
   image to module actions; the lifted sheaf adjunction restricts to linear maps.
   Exactness is detected on underlying abelian kernels and sheafified cokernels
   (situation-conventions, lemma-sections-support-closed-subscheme).
2. Apply lemma-sections-support-closed-subscheme to underlying abelian sheaves.
   Its exact closed pushforward, localization sequence and zero cross-restrictions
   lift to modules, since their maps are linear. Closed pushforward is fully faithful.
   The open slice calculation in lemma-sections-support-closed-subscheme makes
   j*j_* the identity and the restricted open unit invertible.
3. The kernel of the open unit has zero open restriction. Its closed unit is therefore
   invertible by the localization sequence. Every map i_*A -> M factors uniquely
   through this kernel. Full faithfulness gives the sheaf adjunction and identifies
   its counit with the kernel inclusion under that unit. A right adjoint preserves
   finite limits, proving left exactness (clause 1).
4. Module sheaves are Grothendieck abelian (lemma-sections-support-closed-subscheme).
   Use lemma-sections-support-closed-subscheme for unbounded K-injective resolutions
   with injective terms. Total derivation is computed there by
   lemma-sections-support-closed-subscheme. The exact closed pushforward descends
   termwise by situation-conventions; its right adjoint sends
   K-injectives to K-injectives by lemma-sections-support-closed-subscheme.
5. The termwise Hom adjunction descends to homotopy categories by
   lemma-sections-support-closed-subscheme. Compute Hom into K-injectives using
   lemma-sections-support-closed-subscheme to obtain the derived adjunction (clause 2).
   Apply the ordinary adjunction in every component of the product Hom complex.
   Naturality intertwines d_I f - (-1)^n f d_A. These are global Hom complexes,
   and K-injectivity makes them compute global derived Hom, not internal sheaf Hom.
6. For injective I, the composite j!j*I -> I -> j*j*I is monic: both its open and
   closed restricted kernels vanish. Extend j!j*I -> I across that monomorphism
   by injectivity (lemma-sections-support-closed-subscheme). Its extension is a section of
   the open unit, as can be checked after open restriction; open direct image is
   fully faithful. Hence the open unit is epi (clause 3).
7. Resolve K by K-injective I with injective terms. Exact j! makes j*I K-injective.
   The canonical degreewise sequence 0 -> i_*Gamma(I) -> I -> j*j*I -> 0 is short
   exact by steps 3 and 6. Apply lemma-sections-support-closed-subscheme. Its first two
   arrows are the exceptional counit and open unit, giving clause 4.
8. The sequence and its connecting arrow are natural. Maps between K-injective
   resolutions represent all derived maps, and homotopic maps induce the same
   derived arrows (lemma-sections-support-closed-subscheme), so naturality descends.
   The canonical map from the kernel complex to Cone(I -> j*j*I)[-1], n -> (0,n),
   is a quasi-isomorphism: locally lift the first fibre coordinate, subtract its
   boundary, and obtain a kernel cocycle; the same lifting detects boundaries.
   Apply exact i* and i*i_* = id for the fibre formula. Any other distinguished
   fibre triangle is isomorphic to this one by the identity on its last two terms.
-/
theorem formal_closed_support_adjunction
    {X Z V : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    [HasDerivedCategory.{w} (FormalSupportModules Λ X)]
    [HasDerivedCategory.{w} (FormalSupportModules Λ Z)]
    [HasDerivedCategory.{w} (FormalSupportModules Λ V)] :
    IsIso (formalSupportKernelComparison Λ i j) ∧
    PreservesFiniteLimits (formalClosedSupport Λ i j) ∧
    ∃ a : lowerStar Λ i ⊣ formalClosedSupport Λ i j,
      (∀ M : FormalSupportModules Λ X,
        (formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
          (formalSupportKernelInclusion Λ j).app M) ∧
      (∀ (I : FormalSupportModules Λ X) [Injective I],
        Epi ((formalSupportPullbackAdjunction Λ j).unit.app I)) ∧
      (∀ (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        CochainComplex.IsKInjective
          (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ∧
      (∀ (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        IsIso ((formalClosedSupport Λ i j).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ∧
      (∀ (A : CochainComplex (FormalSupportModules Λ Z) ℤ)
        (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        ∃ e : CochainComplex.HomComplex
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
          CochainComplex.HomComplex A
            (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
          ∀ (n : ℤ) (f : CochainComplex.HomComplex.Cochain
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
            (p q : ℤ) (hpq : p + n = q),
            (((e.hom.f n).hom f).v p q hpq) =
              a.homEquiv (A.X p) (I.X q) (f.v p q hpq)) ∧
      Exists fun [hclosed : PreservesFiniteColimits (lowerStar Λ i)] ↦
        ∃ (b : (lowerStar Λ i).mapDerivedCategory ⊣
            (formalClosedSupport Λ i j).rightDerivedFunctor)
          (c : (formalSupportPullback Λ j).mapDerivedCategory ⊣
            (lowerStar Λ j).rightDerivedFunctor),
          ∃ δ : (formalSupportPullback Λ j).mapDerivedCategory ⋙
              (lowerStar Λ j).rightDerivedFunctor ⟶
            (formalClosedSupport Λ i j).rightDerivedFunctor ⋙
              (lowerStar Λ i).mapDerivedCategory ⋙
                shiftFunctor (DerivedCategory (FormalSupportModules Λ X)) (1 : ℤ),
            b = a.mapDerivedCategoryRightDerivedAdjunction ∧
            c = (formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction ∧
            (∀ K : DerivedCategory (FormalSupportModules Λ X),
              Triangle.mk (b.counit.app K) (c.unit.app K) (δ.app K) ∈ distTriang _) ∧
            (∀ (K F : DerivedCategory (FormalSupportModules Λ X)) (s : F ⟶ K)
              (t : (lowerStar Λ j).rightDerivedFunctor.obj
                ((formalSupportPullback Λ j).mapDerivedCategory.obj K) ⟶ F⟦(1 : ℤ)⟧),
              Triangle.mk s (c.unit.app K) t ∈ distTriang _ →
              Nonempty ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K ≅
                (formalSupportPullback Λ i).mapDerivedCategory.obj F)) := by
  classical
  have hji : Set.range i.base = (Set.range j.base)ᶜ := by
    rw [hij, compl_compl]
  have hcomp : IsIso (formalSupportKernelComparison Λ i j) := by
    rw [comparison_eq]
    exact closedSupportKernelComparison_isIso Λ i j hji
  have hexact := closedSupport_lowerStarExact Λ i j hji
  let a := closedSupportAdjunction Λ i j hji
  refine ⟨hcomp, closedSupport_leftExact Λ i j hji, a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M
    have ha := Classical.choose_spec
      (ExistsUnique.exists (existsUnique_closedSupportAdjunction Λ i j hji))
    dsimp only [a, closedSupportAdjunction]
    rw [ha]
    rw [comparison_eq]
    change (closedSupportKernelComparison Λ i j).app M ≫
      (closedSupportCounit Λ i j hji).app M = _
    simp only [closedSupportCounit, NatTrans.comp_app, asIso_inv]
    rw [← Category.assoc, ← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app,
      Category.id_comp]
    rfl
  · intro I _
    exact closedSupport_injective_unit_epi Λ i j hji I
  · have : (formalClosedSupport Λ i j).PreservesKInjectiveComplexes :=
      a.preservesKInjectiveComplexes
    intro I _
    exact Functor.PreservesKInjectiveComplexes.isKInjective_map I
  · have : (formalClosedSupport Λ i j).PreservesKInjectiveComplexes :=
      a.preservesKInjectiveComplexes
    intro I _
    infer_instance
  · intro A I _
    obtain ⟨e, he⟩ := closedSupport_globalRHom Λ i j hji A I
    exact ⟨e, he⟩
  · refine ⟨hexact, a.mapDerivedCategoryRightDerivedAdjunction,
      (supportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction, ?_⟩
    obtain ⟨δ, hδ⟩ := supportTriangle Λ i j hji
    refine ⟨δ, rfl, rfl, hδ, ?_⟩
    intro K F s t hF
    let T := Triangle.mk (a.mapDerivedCategoryRightDerivedAdjunction.counit.app K)
      ((supportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app K)
      (δ.app K)
    let S := Triangle.mk s
      ((supportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app K) t
    let e := isoTriangleOfIso₁₂ T.rotate S.rotate
      (rot_of_distTriang _ (hδ K)) (rot_of_distTriang _ hF)
      (Iso.refl _) (Iso.refl _) (by simp [T, S])
    let ec := (shiftFunctor (DerivedCategory (supportModules Λ X)) (1 : ℤ)).preimageIso
      (Triangle.π₃.mapIso e)
    have hc := supportCounitOfAbelian Λ i
      (ProEtale.abelian_closed_support_counit_and_unit i j hij).1
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
    exact ⟨(asIso (ai.counit.app ((closedSupport Λ i j).rightDerivedFunctor.obj K))).symm ≪≫
      (supportPullback Λ i).mapDerivedCategory.mapIso ec⟩

end AlgebraicGeometry.ProEtale.CondensedRing
