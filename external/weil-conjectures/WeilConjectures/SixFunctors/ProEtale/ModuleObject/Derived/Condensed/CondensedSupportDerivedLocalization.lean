/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
/-! # Localization of ordinary derived condensed modules -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
omit [IsCommMonObj Λ] in
private theorem module_isZero_of_underlying {X : Scheme.{u}} (M : supportModules Λ X)
    (h : IsZero M.X) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  apply Mod.hom_ext
  exact h.eq_of_src _ _

omit [IsCommMonObj Λ] in
private theorem supportedUnit {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : supportModules Λ X) (h : IsZero ((supportPullback Λ j).obj M)) :
    IsIso ((supportPullbackAdjunction Λ i).unit.app M) := by
  have hj : Set.range j = (Set.range i)ᶜ := by
    rw [hij, compl_compl]
  have hb : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj M.X) :=
    (Mod.forget (condensedRingObj Λ U)).map_isZero h
  have ha := ProEtale.abelian_closed_support i j hj M.X hb
  have hm : IsIso (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
      (condensedRingObj Λ X)).unit.app M) := by
    have : IsIso ((Mod.forget (condensedRingObj Λ X)).map
        (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
          (condensedRingObj Λ X)).unit.app M)) := by
      change IsIso (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
      (condensedRingObj Λ X)).unit.app M).hom
      rw [Adjunction.mapModAdjunction_unit_app_hom]
      exact ha
    exact isIso_of_reflects_iso _ (Mod.forget (condensedRingObj Λ X))
  unfold supportPullbackAdjunction
  rw [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Adjunction.comp_unit_app]
  infer_instance

omit [IsCommMonObj Λ] in
private theorem closedCounit {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : IsIso (supportPullbackAdjunction Λ i).counit := by
  have hb := ProEtale.abelian_closed_counit i
  have hm : IsIso ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
      (condensedRingObj Λ X)).counit := by
    have : ∀ P, IsIso (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
        (condensedRingObj Λ X)).counit.app P) := fun P ↦ by
      have : IsIso ((Mod.forget _).map
          (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
            (condensedRingObj Λ X)).counit.app P)) := by
        change IsIso (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
            (condensedRingObj Λ X)).counit.app P).hom
        rw [Adjunction.mapModAdjunction_counit_app_hom]
        infer_instance
      exact isIso_of_reflects_iso _ (Mod.forget _)
    exact NatIso.isIso_of_isIso_app _
  unfold supportPullbackAdjunction
  rw [Adjunction.ofNatIsoRight_counit]
  have : IsIso (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
      (condensedRingObj Λ X)).comp (supportCoefficientEquivalence Λ i).toAdjunction).counit := by
    have : ∀ P, IsIso ((((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
        (condensedRingObj Λ X)).comp
          (supportCoefficientEquivalence Λ i).toAdjunction).counit.app P) := fun P ↦ by
      rw [Adjunction.comp_counit_app]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  infer_instance

private theorem openUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  let adj := ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have hm : IsIso (linearOpenImmersionLowerShriekAdjunction Λ j).unit := by
    have : ∀ P, IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app P) :=
      fun P ↦ by
        have : IsIso ((Mod.forget _).map
            ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app P)) := by
          change IsIso (((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app P).hom)
          simp only [linearOpenImmersionLowerShriekAdjunction,
            Adjunction.mapModLeftAdjunction, Adjunction.mkOfHomEquiv_unit_app,
            Adjunction.homEquiv_unit, Equiv.coe_fn_mk, Mod.Hom.mk'_hom,
            Mod.id_hom']
          change IsIso (adj.unit.app P.X ≫ (ProEtale.upperStar Ab.{u + 1} j).map
            (𝟙 ((ProEtale.openImmersionLowerShriek Ab.{u + 1} j).obj P.X)))
          infer_instance
        exact isIso_of_reflects_iso _ (Mod.forget _)
    exact NatIso.isIso_of_isIso_app _
  have : (Mod.comap (condensedPullbackHom Λ j)).Full :=
    (supportCoefficientEquivalence Λ j).fullyFaithfulInverse.full
  have : (Mod.comap (condensedPullbackHom Λ j)).Faithful :=
    (supportCoefficientEquivalence Λ j).fullyFaithfulInverse.faithful
  have : IsIso (Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j)).unit :=
    (Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j)).unit_isIso_of_L_fully_faithful
  unfold openImmersionLowerShriekUpperStarAdjunction
  rw [Adjunction.ofNatIsoRight_unit]
  have : ∀ P, IsIso (((Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j)).comp
      (linearOpenImmersionLowerShriekAdjunction Λ j)).unit.app P) := fun P ↦ by
    rw [Adjunction.comp_unit_app]
    infer_instance
  have := NatIso.isIso_of_isIso_app (((Mod.restrictCoextendAdjunction
    (condensedPullbackHom Λ j)).comp (linearOpenImmersionLowerShriekAdjunction Λ j)).unit)
  infer_instance

omit [IsCommMonObj Λ] in
private theorem mixedClosed {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : supportModules Λ Z) :
    IsZero ((supportPullback Λ j).obj ((lowerStar Λ i).obj P)) := by
  apply module_isZero_of_underlying Λ
  exact ProEtale.isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j
    (by rw [hij]; exact disjoint_compl_left) P.X

omit [IsCommMonObj Λ] in
private theorem jointZero {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (M : supportModules Λ X)
    (hi : IsZero ((supportPullback Λ i).obj M))
    (hj : IsZero ((supportPullback Λ j).obj M)) : IsZero M := by
  have := supportedUnit Λ i j hij M hj
  exact ((lowerStar Λ i).map_isZero hi).of_iso
    (asIso ((supportPullbackAdjunction Λ i).unit.app M))

omit [IsCommMonObj Λ] in
private theorem jointIso {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {M N : supportModules Λ X}
    (f : M ⟶ N) [IsIso ((supportPullback Λ i).map f)]
    [IsIso ((supportPullback Λ j).map f)] : IsIso f := by
  have hk : ∀ {Y : Scheme.{u}} (a : Y ⟶ X) [IsIso ((supportPullback Λ a).map f)],
      IsZero ((supportPullback Λ a).obj (kernel f)) := fun a _ ↦
    (isZero_kernel_of_mono ((supportPullback Λ a).map f)).of_iso
      (PreservesKernel.iso _ f)
  have hq : ∀ {Y : Scheme.{u}} (a : Y ⟶ X) [IsIso ((supportPullback Λ a).map f)],
      IsZero ((supportPullback Λ a).obj (cokernel f)) := fun a _ ↦
    (isZero_cokernel_of_epi ((supportPullback Λ a).map f)).of_iso
      (PreservesCokernel.iso _ f)
  have : Mono f := Preadditive.mono_of_isZero_kernel _
    (jointZero Λ i j hij _ (hk i) (hk j))
  have : Epi f := Preadditive.epi_of_isZero_cokernel _
    (jointZero Λ i j hij _ (hq i) (hq j))
  exact isIso_of_mono_of_epi f

private theorem derivedOpenUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openSupportDerivedAdjunction Λ j).unit := by
  let adj := (openImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (supportPullbackIsoUpperStar Λ j).symm
  have := openUnit Λ j
  have : IsIso adj.unit := by
    dsimp [adj]
    rw [Adjunction.ofNatIsoRight_unit]
    infer_instance
  let e := openImmersionLowerShriek Λ j
  let r := supportPullback Λ j
  have h := (openSupportDerivedAdjunction Λ j).fullyFaithfulLOfCompIsoId
    (Functor.mapDerivedCategoryCompIso e r ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso (supportModules Λ U))
  have := h.full
  have := h.faithful
  infer_instance

omit [IsCommMonObj Λ] in
private theorem derivedClosedCounit {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [PreservesFiniteColimits (lowerStar Λ i)] :
    IsIso (closedPullbackDerivedAdjunction Λ i).counit := by
  have := closedCounit Λ i
  let e := lowerStar Λ i
  let r := supportPullback Λ i
  have h := (closedPullbackDerivedAdjunction Λ i).fullyFaithfulROfCompIsoId
    (Functor.mapDerivedCategoryCompIso e r ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (supportPullbackAdjunction Λ i).counit) ≪≫
        Functor.mapDerivedCategoryIdIso (supportModules Λ Z))
  have := h.full
  have := h.faithful
  infer_instance

omit [IsCommMonObj Λ] in
private theorem derivedJointIso {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {M N : DerivedCategory (supportModules Λ X)} (f : M ⟶ N)
    [IsIso ((supportPullback Λ i).mapDerivedCategory.map f)]
    [IsIso ((supportPullback Λ j).mapDerivedCategory.map f)] : IsIso f := by
  apply (DerivedCategory.isIso_iff _ f).2
  intro n
  have hi : IsIso ((supportPullback Λ i).map
      ((DerivedCategory.homologyFunctor (supportModules Λ X) n).map f)) :=
    (NatIso.isIso_map_iff ((supportPullback Λ i).mapDerivedCategoryHomologyFunctorIso n) f).2
      (by change IsIso ((DerivedCategory.homologyFunctor _ n).map _); infer_instance)
  have hj : IsIso ((supportPullback Λ j).map
      ((DerivedCategory.homologyFunctor (supportModules Λ X) n).map f)) :=
    (NatIso.isIso_map_iff ((supportPullback Λ j).mapDerivedCategoryHomologyFunctorIso n) f).2
      (by change IsIso ((DerivedCategory.homologyFunctor _ n).map _); infer_instance)
  exact jointIso Λ i j hij _

omit [IsCommMonObj Λ] in
private theorem derivedMixedClosed {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [PreservesFiniteColimits (lowerStar Λ i)] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z)) :
    IsZero ((supportPullback Λ j).mapDerivedCategory.obj
      ((lowerStar Λ i).mapDerivedCategory.obj P)) := by
  apply Functor.isZero_mapDerivedCategory_obj
  intro n
  exact (mixedClosed Λ i j hij _).of_iso
    ((supportPullback Λ j).mapIso ((lowerStar Λ i).mapDerivedCategoryHomologyFunctorIso n
      |>.symm.app P))

/-- Open/closed localization for the exact functors on ordinary unbounded derived modules.
Source: Stacks Tags 09AA, 09AH, 09BN; original internal-Hom argument steps 1, 2 and 8
(blueprint: lem-sfb-condensed-support-derived-localization).

Proof: the forgetful functor from internal modules to abelian sheaves is faithful, exact
and conservative. Its composite with support inverse image is the abelian inverse image;
scalar transport along alpha leaves underlying objects and maps unchanged. The underlying
closed unit differs from the lifted abelian unit only by invertible scalar-transport maps.
The abelian closed-support theorem therefore makes this unit invertible on modules with
zero open restriction. The closed counit is invertible by the same lift of the abelian
closed counit. The open extension/restriction unit is invertible since the abelian extension
is fully faithful; its module action is the action induced by the projection formula.
The two mixed composites vanish on underlying sheaves by empty base change and adjunction.
All four functors are exact. Apply them degreewise to complexes. The units and counits
are the degreewise maps, transported along the canonical derived factorization isomorphisms.
Joint detection passes to derived morphisms since exact functors commute with homology.
The derived supported unit is invertible by its closed triangle identity, the invertible
closed counit, and its zero open restriction. Mixed closed-image vanishing follows on
homology; mixed open-extension vanishing follows by transposing its identity through
the two adjunctions into a zero Hom group. Finally a morphism whose two restrictions are
invertible has
kernel and cokernel zero on every homology degree, by ordinary localization. Hence every
homology map is invertible and the derived morphism is invertible. Empty strata and zero
coefficients are permitted throughout. No tensor, flat resolution or internal Hom is used. -/
theorem condensedSupportDerivedLocalization {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    let := closedSupport_lowerStarExact Λ i j hij
    (∀ L, IsIso ((openSupportDerivedAdjunction Λ j).unit.app L)) ∧
    (∀ P, IsIso ((closedPullbackDerivedAdjunction Λ i).counit.app P)) ∧
    (∀ M : DerivedCategory (supportModules Λ X),
      IsZero ((supportPullback Λ j).mapDerivedCategory.obj M) →
        IsIso ((closedPullbackDerivedAdjunction Λ i).unit.app M)) ∧
    (∀ L, IsZero ((supportPullback Λ i).mapDerivedCategory.obj
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))) ∧
    (∀ P, IsZero ((supportPullback Λ j).mapDerivedCategory.obj
      ((lowerStar Λ i).mapDerivedCategory.obj P))) ∧
    (∀ {M N : DerivedCategory (supportModules Λ X)} (f : M ⟶ N),
      IsIso ((supportPullback Λ i).mapDerivedCategory.map f) →
      IsIso ((supportPullback Λ j).mapDerivedCategory.map f) → IsIso f) := by
  let := closedSupport_lowerStarExact Λ i j hij
  have hu := derivedOpenUnit Λ j
  have hc := derivedClosedCounit Λ i
  have hz := derivedMixedClosed Λ i j hij
  refine ⟨fun L ↦ inferInstance, fun P ↦ inferInstance, ?_, ?_, hz, ?_⟩
  · intro M hM
    have hi : IsIso ((supportPullback Λ i).mapDerivedCategory.map
        ((closedPullbackDerivedAdjunction Λ i).unit.app M)) := by
      have h := (closedPullbackDerivedAdjunction Λ i).left_triangle_components M
      have : IsIso ((supportPullback Λ i).mapDerivedCategory.map
          ((closedPullbackDerivedAdjunction Λ i).unit.app M) ≫
          (closedPullbackDerivedAdjunction Λ i).counit.app
            ((supportPullback Λ i).mapDerivedCategory.obj M)) := by
        rw [h]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right
        ((supportPullback Λ i).mapDerivedCategory.map
          ((closedPullbackDerivedAdjunction Λ i).unit.app M))
        ((closedPullbackDerivedAdjunction Λ i).counit.app
          ((supportPullback Λ i).mapDerivedCategory.obj M))
    have hj : IsIso ((supportPullback Λ j).mapDerivedCategory.map
        ((closedPullbackDerivedAdjunction Λ i).unit.app M)) :=
      isIso_of_source_target_iso_zero _ hM.isoZero (hz _).isoZero
    exact derivedJointIso Λ i j hij _
  · intro L
    apply (IsZero.iff_id_eq_zero _).2
    apply ((closedPullbackDerivedAdjunction Λ i).homEquiv _ _).injective
    apply ((openSupportDerivedAdjunction Λ j).homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  · intro M N f hi hj
    have := hi
    have := hj
    exact derivedJointIso Λ i j hij f

end AlgebraicGeometry.ProEtale.CondensedRing
