/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Sections with closed support for condensed module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-formal-closed-support,
node lemma-sections-support-closed-subscheme--1
(blueprint: lemma-sections-support-closed-subscheme--1); Stacks Project, Tags 09AA and 09AH.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Lift the abelian recollement maps through module objects and change of scalars.
set_option backward.isDefEq.respectTransparency false in
private theorem openRestrictionPushforwardZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((upperStar Λ j).obj ((lowerStar Λ i).obj M)) := by
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
  have hz'' := hz'.of_iso ((profinitePointModuleForgetPullbackIso Λ j).app
    ((lowerStar Λ i).obj M))
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget (condensedRingObj Λ U)).map_injective
  exact hz''.eq_of_src _ _

private theorem moduleCounitOfAbelian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (hAb : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit) :
    IsIso (upperStarLowerStarAdjunction Λ i).counit := by
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
    (condensedRingObj Λ X)
  have hε (N) : IsIso (adj.counit.app N) := by
    have hh : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      change IsIso (adj.counit.app N).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  have ff := adj.fullyFaithfulROfIsIsoCounit
  have he := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).fullyFaithfulFunctor
  have hcomp := he.comp ff
  have hfull := hcomp.ofIso (comapPullbackHomCompIso Λ i)
  have := hfull.full
  have := hfull.faithful
  exact (upperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful

set_option backward.isDefEq.respectTransparency false in
private theorem moduleUnitOfAbelian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hAb : IsIso ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app M.X)) :
    IsIso ((upperStarLowerStarAdjunction Λ i).unit.app M) := by
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
    (condensedRingObj Λ X)
  let scalar := Mod.extendRestrictAdjunction (condensedPullbackHom Λ i)
  have hη : IsIso (adj.unit.app M) := by
    have hh : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      change IsIso (adj.unit.app M).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_unit_app_hom]
      exact hAb
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hff := Functor.FullyFaithful.ofIso
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).fullyFaithfulInverse
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ i)).symm
  have := hff.full
  have := hff.faithful
  have : IsIso scalar.unit := scalar.unit_isIso_of_L_fully_faithful
  have hcomp : IsIso ((adj.comp scalar).unit.app M) := by
    rw [Adjunction.comp_unit_app]
    infer_instance
  change IsIso (((adj.comp scalar).ofNatIsoRight (comapPullbackHomCompIso Λ i)).unit.app M)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

private theorem exactClosedOfDetection
    {C Z U : Type*} [Category* C] [Category* Z] [Category* U]
    [Abelian C] [Abelian Z] [Abelian U]
    (ic : C ⥤ Z) (ip : Z ⥤ C) (jc : C ⥤ U)
    [ic.Additive] [ip.Additive] [jc.Additive]
    [PreservesFiniteLimits ip] [PreservesFiniteColimits ic] [PreservesFiniteColimits jc]
    (ai : ic ⊣ ip) [IsIso ai.counit]
    (hzero : ∀ M, IsZero (jc.obj (ip.obj M)))
    (hjoint : ∀ M, IsZero (ic.obj M) → IsZero (jc.obj M) → IsZero M) :
    PreservesFiniteColimits ip := by
  have hepi {M N : Z} (f : M ⟶ N) [Epi f] : Epi (ip.map f) := by
    have heq : ic.map (ip.map f) =
        ai.counit.app M ≫ f ≫ inv (ai.counit.app N) := by
      rw [← Category.assoc, IsIso.eq_comp_inv]
      exact ai.counit.naturality f
    have : Epi (ic.map (ip.map f)) := by rw [heq]; infer_instance
    apply Preadditive.epi_of_isZero_cokernel
    apply hjoint
    · exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ _)
    · exact (IsZero.of_epi (cokernel.π _) (hzero N)).of_iso (PreservesCokernel.iso _ _)
  have : ip.PreservesEpimorphisms := ⟨fun f _ ↦ hepi f⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels ip
  exact Functor.preservesFiniteColimits_of_preservesHomology ip

set_option backward.isDefEq.respectTransparency false in
private theorem kernelSupportAdjunction
    {C Z U : Type*} [Category* C] [Category* Z] [Category* U]
    [Abelian C] [Abelian Z] [Abelian U]
    (ic : C ⥤ Z) (ip : Z ⥤ C) (jc : C ⥤ U) (jp : U ⥤ C)
    [ic.Additive] [ip.Additive] [jc.Additive] [jp.Additive]
    [PreservesFiniteLimits jc] [ip.Full] [ip.Faithful]
    (ai : ic ⊣ ip) (aj : jc ⊣ jp) [IsIso aj.counit]
    (hzero : ∀ B, IsZero (jc.obj (ip.obj B)))
    (hsupport : ∀ F, IsZero (jc.obj F) → IsIso (ai.unit.app F)) :
    IsIso (Functor.whiskerLeft (kernel aj.unit) ai.unit) ∧
      Nonempty (ip ⊣ kernel aj.unit ⋙ ic) := by
  classical
  let S := kernel aj.unit
  let κ := kernel.ι aj.unit
  let eK (F : C) : S.obj F ≅ kernel (aj.unit.app F) :=
    PreservesKernel.iso ((evaluation C C).obj F) aj.unit
  have hκ (F : C) : (eK F).hom ≫ kernel.ι (aj.unit.app F) = κ.app F := by
    change (PreservesKernel.iso ((evaluation C C).obj F) aj.unit).hom ≫
      kernel.ι (aj.unit.app F) = _
    rw [PreservesKernel.iso_hom]
    exact kernelComparison_comp_ι aj.unit ((evaluation C C).obj F)
  have hs : ∀ F, IsIso (ai.unit.app (S.obj F)) := by
    intro F
    have hj : IsIso (jc.map (aj.unit.app F)) := by
      have : IsIso (jc.map (aj.unit.app F) ≫ aj.counit.app (jc.obj F)) := by
        erw [aj.left_triangle_components F]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (aj.counit.app (jc.obj F))
    apply hsupport
    exact ((isZero_kernel_of_mono (jc.map (aj.unit.app F))).of_iso
      (PreservesKernel.iso jc (aj.unit.app F))).of_iso (jc.mapIso (eK F))
  have hS : IsIso (Functor.whiskerLeft S ai.unit) :=
    (NatTrans.isIso_iff_isIso_app _).mpr hs
  let ε : (S ⋙ ic) ⋙ ip ⟶ 𝟭 C :=
    inv (Functor.whiskerLeft S ai.unit) ≫ κ
  have hε (F : C) : ε.app F = inv (ai.unit.app (S.obj F)) ≫ κ.app F := by
    simp only [ε, NatTrans.comp_app, NatIso.isIso_inv_app, Functor.whiskerLeft_app]
  have hvanish {B : Z} {F : C} (f : ip.obj B ⟶ F) : f ≫ aj.unit.app F = 0 := by
    apply (aj.homEquiv (ip.obj B) (jc.obj F)).symm.injective
    rw [aj.homEquiv_counit, aj.homEquiv_counit]
    simp only [Functor.map_comp, Functor.map_zero, zero_comp]
    rw [Category.assoc, aj.left_triangle_components, Category.comp_id]
    exact (hzero B).eq_of_src _ _
  let e (B : Z) (F : C) : (B ⟶ (S ⋙ ic).obj F) ≃ (ip.obj B ⟶ F) :=
    Equiv.ofBijective (fun g ↦ ip.map g ≫ ε.app F) (by
      constructor
      · intro g h heq
        rw [hε] at heq
        apply ip.map_injective
        simp only [← Category.assoc] at heq
        have : Mono (κ.app F) := by
          rw [← hκ F]
          infer_instance
        exact (cancel_mono _).1 ((cancel_mono (κ.app F)).1 heq)
      · intro f
        refine ⟨ip.preimage
          (kernel.lift (aj.unit.app F) f (hvanish f) ≫ (eK F).inv ≫
            ai.unit.app (S.obj F)), ?_⟩
        dsimp only
        rw [Functor.map_preimage, hε]
        simp only [Category.assoc, IsIso.hom_inv_id_assoc]
        rw [← hκ F]
        simp)
  refine ⟨hS, ⟨Adjunction.mkOfHomEquiv
    { homEquiv := fun B F ↦ (e B F).symm
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }⟩⟩
  · intro B' B F f g
    change ip.map (f ≫ g) ≫ ε.app F = ip.map f ≫ (ip.map g ≫ ε.app F)
    simp [Functor.map_comp, Category.assoc]
  · intro B F G f g
    apply (e B G).injective
    change (e B G) ((e B G).symm (f ≫ g)) =
      (e B G) ((e B F).symm f ≫ (S ⋙ ic).map g)
    rw [Equiv.apply_symm_apply]
    change f ≫ g = ip.map ((e B F).symm f ≫ (S ⋙ ic).map g) ≫ ε.app G
    have hn := ε.naturality g
    change ip.map ((S ⋙ ic).map g) ≫ ε.app G = ε.app F ≫ g at hn
    rw [Functor.map_comp, Category.assoc, hn]
    have hf := (e B F).apply_symm_apply f
    change ip.map ((e B F).symm f) ≫ ε.app F = f at hf
    rw [← Category.assoc, hf]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The kernel of the open restriction unit, formed in the functor category, so that
its maps are precisely the induced kernel maps.
Source: blueprint lemma-sections-support-closed-subscheme--1, definition of the supported kernel
(blueprint: lemma-sections-support-closed-subscheme--1). -/
noncomputable def moduleSectionsWithSupport {X V : Scheme.{u}} (j : V ⟶ X) :
    pulledBackModuleObjects Λ X ⥤ pulledBackModuleObjects Λ X :=
  kernel (upperStarLowerStarAdjunction Λ j).unit

/-- The sheaf on the closed subscheme: `i^* ker(M ⟶ j_* j^* M)`.
Source: blueprint lemma-sections-support-closed-subscheme--1, displayed definition
(blueprint: lemma-sections-support-closed-subscheme--1). -/
noncomputable def closedModuleSectionsWithSupport {X Z V : Scheme.{u}}
    (i : Z ⟶ X) (j : V ⟶ X) :
    pulledBackModuleObjects Λ X ⥤ pulledBackModuleObjects Λ Z :=
  moduleSectionsWithSupport Λ j ⋙ upperStar Λ i

/-- Sections with closed support give the right adjoint to the exact closed direct image.
Source: blueprint main-20261015, lemma-sections-support-closed-subscheme--1, clauses (1)--(3);
Stacks Project, Tags 09AA and 09AH (blueprint: lemma-sections-support-closed-subscheme--1).

Proof plan:
1. The standing scheme is Noetherian by finite type over the field
   (lem-weil-pbc-finite-type-over-noetherian), so its open complement is quasi-compact.
   The coefficient comparison alpha is an isomorphism, identifying the recorded module
   operations with ringed inverse/direct image for the actual pulled-back coefficient ring.
2. Use lem-weil-pbc-proetale-ringed-open-closed for exact closed direct image, the closed
   counit, vanishing of open restriction of closed direct image, and localization. The
   immersion-limit-preservation node gives exact inverse image. The open-comparison node
   identifies the open counit with the restriction counit; base-change evaluation makes it
   invertible. The closed-counit node makes closed direct image fully faithful.
3. Apply open inverse image to the unit kernel. The triangle identity and the invertible
   open counit imply this restriction is zero. Localization identifies that kernel with
   its closed inverse image followed by closed direct image, by the closed unit. Both the
   kernel construction and this unit are natural in the module. This proves (1).
4. A map from a closed direct image to M has zero composite with the open unit, hence
   factors uniquely through its kernel. Full faithfulness of closed direct image then
   identifies it with a map to the specified closed inverse image of the kernel. The
   inverse sends this map through the inverse closed unit and the kernel inclusion.
   Kernel uniqueness proves the inverse identities and naturality, giving the adjunction.
5. Kernel-map uniqueness gives additivity. Right adjoints preserve small limits
   (situation-conventions); in particular this gives left exactness.
6. Exact closed direct image preserves monomorphisms. Apply the generic
   lem-exc-rg-right-adjoint-preserves-injectives to obtain the injective-module assertion.
7. Lift the additive adjunction termwise and to homotopy categories using
   lem-weil-pbc-termwise-adjunction-homotopy. Exact closed direct image takes every
   acyclic complex to an acyclic complex (lem-sp-exact-functor-preserves-homology).
   Adjunction therefore identifies maps from an acyclic complex to the image of a
   K-injective complex with zero homotopy classes. This proves K-injectivity, including
   unbounded complexes, by def-pur-kinjective-complex.

The admissible coefficients are the recorded predicate of definition-localizing-subcategory.
The first conjunct is the canonical natural identification of clause (1).
The existential additive instance only makes the termwise functor on complexes available.
-/
theorem formal_closed_support_sheaves
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Z V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : V ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : Set.range j = (Set.range i)ᶜ) :
    IsIso (Functor.whiskerLeft (moduleSectionsWithSupport Λ j)
      (upperStarLowerStarAdjunction Λ i).unit) ∧
    PreservesFiniteLimits (lowerStar Λ i) ∧
    PreservesFiniteColimits (lowerStar Λ i) ∧
    Nonempty (lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j) ∧
    PreservesFiniteLimits (closedModuleSectionsWithSupport Λ i j) ∧
    PreservesLimitsOfSize.{u + 1, u + 1} (closedModuleSectionsWithSupport Λ i j) ∧
    ∃ (_ : (closedModuleSectionsWithSupport Λ i j).Additive),
      (∀ I : CochainComplex (pulledBackModuleObjects Λ X) ℤ,
        I.IsKInjective →
          CochainComplex.IsKInjective
            (((closedModuleSectionsWithSupport Λ i j).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) ∧
      (∀ I : pulledBackModuleObjects Λ X, Injective I →
        Injective ((closedModuleSectionsWithSupport Λ i j).obj I)) := by
  have _ := hΛ
  have hX : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : TopologicalSpace.NoetherianSpace V :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := inferInstance
  obtain ⟨hAb, hAbsupport⟩ := ProEtale.abelian_closed_support_counit_and_unit i j hij
  have hi := moduleCounitOfAbelian Λ i hAb
  have hzero := openRestrictionPushforwardZero Λ i j hij
  have hsupport : ∀ M : pulledBackModuleObjects Λ X,
      IsZero ((upperStar Λ j).obj M) →
        IsIso ((upperStarLowerStarAdjunction Λ i).unit.app M) := by
    intro M hjM
    apply moduleUnitOfAbelian Λ i M
    apply hAbsupport
    exact ((Mod.forget _).map_isZero hjM).of_iso
      ((profinitePointModuleForgetPullbackIso Λ j).app M).symm
  -- Full faithfulness depends only on the right adjoint, so either abelian
  -- inverse-image adjunction supplies the same counit invertibility.
  have hjAb : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).counit := by
    have ff := (ProEtale.openImmersionRestrictionLowerStarAdjunction Ab.{u + 1} j
      ).fullyFaithfulROfIsIsoCounit
    have := ff.full
    have := ff.faithful
    exact (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j
      ).counit_isIso_of_R_fully_faithful
  have hjcounit := moduleCounitOfAbelian Λ j hjAb
  have hjoint : ∀ M : pulledBackModuleObjects Λ X,
      IsZero ((upperStar Λ i).obj M) → IsZero ((upperStar Λ j).obj M) → IsZero M := by
    intro M hiM hjM
    have := hsupport M hjM
    exact ((lowerStar Λ i).map_isZero hiM).of_iso
      (asIso ((upperStarLowerStarAdjunction Λ i).unit.app M))
  have hclosed := exactClosedOfDetection (upperStar Λ i) (lowerStar Λ i)
    (upperStar Λ j) (upperStarLowerStarAdjunction Λ i) hzero hjoint
  have ff := (upperStarLowerStarAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  obtain ⟨hkernel, ⟨adj⟩⟩ := kernelSupportAdjunction
    (upperStar Λ i) (lowerStar Λ i) (upperStar Λ j) (lowerStar Λ j)
    (upperStarLowerStarAdjunction Λ i) (upperStarLowerStarAdjunction Λ j) hzero hsupport
  change lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j at adj
  have := adj.right_adjoint_additive
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (closedModuleSectionsWithSupport Λ i j) := adj.rightAdjoint_preservesLimits
  have : (lowerStar Λ i).PreservesHomology := {}
  have := adj.preservesKInjectiveComplexes
  refine ⟨hkernel, inferInstance, hclosed, ⟨adj⟩, inferInstance, inferInstance,
    inferInstance, ?_, ?_⟩
  · intro I hI
    exact inferInstance
  · intro I hI
    exact adj.map_injective I hI

end AlgebraicGeometry.ProEtale.CondensedRing
