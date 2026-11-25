/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Pushforward along a closed immersion of an extension by zero

Let `Λ` be a commutative condensed ring, `c : D ⟶ X` a closed immersion and `U` an open of `X`
containing the complement of the range of `c`, with preimage `V = c⁻¹(U)`. Then
`c_* V_! N ≅ U_! (c|_U)_* N` for every `Λ_V`-module `N`
(`ProEtale.CondensedRing.lowerStarOpenImmersionLowerShriekIso`): the sheaf `c_* V_! N` vanishes
on the closed complement `c(D ∖ V)` of `U`, so it is the extension by zero of its restriction to
`U` (`ProEtale.CondensedRing.isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app`), and
the restriction of `c_*` to the open `U` is computed by the weakly étale base change
(`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isPullback`).

On a scheme with noetherian underlying space the pushforward along a closed immersion is exact
(`ProEtale.CondensedRing.rightDerivedLowerStarSingleIsoOfIsClosedImmersion`), which gives the
derived version `Rc_* V_! Rc'_* L ≅ U_! R(c' ≫ c|_U)_* L` for `L` placed in degree `0`
(`ProEtale.CondensedRing.rightDerivedLowerStarOpenImmersionLowerShriekSingleIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The derived pushforward along a closed immersion into a scheme with noetherian underlying
space of a module object placed in degree `0` is its pushforward placed in degree `0`: the
pushforward along a closed immersion is exact. -/
noncomputable def rightDerivedLowerStarSingleIsoOfIsClosedImmersion {Z X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (R((i)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((i)_*⟦Λ⟧.obj F) :=
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  haveI : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hc : IsCompl (Set.range i.base) (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι U]
    exact isCompl_compl
  haveI := preservesFiniteColimits_lowerStar_of_isCompl Λ i U.ι hc
  ((i)_*⟦Λ⟧).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    (((i)_*⟦Λ⟧).mapDerivedCategorySingleFunctor 0).app F

/-- A module object whose restriction to the closed complement of a quasi-compact open
`j : U ⟶ X` vanishes is the extension by zero of its restriction to `U`: the counit
`j_! j^* M ⟶ M` is an isomorphism. -/
lemma isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsZero ((i)^*⟦Λ⟧.obj M)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app M) := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).unit_isIso_of_L_fully_faithful
  refine (jointlyReflectIsomorphisms_upperStar_of_isCompl Λ i j hij).isIso_of_pairFunctor _ ?_ ?_
  · exact IsIso.of_isIso_fac_left
      ((openImmersionLowerShriekUpperStarAdjunction Λ j).right_triangle_components M)
  · exact isIso_of_source_target_iso_zero _
      (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ j i hij.symm.disjoint
        _).isoZero hM.isoZero


/-- For a closed immersion `c : D ⟶ X` and an open `U` of `X` containing the complement of the
range of `c`, the closed immersion `D ∖ c⁻¹(U) ⟶ D ⟶ X` has range the complement of `U`. -/
lemma isCompl_range_closedComplement_preimage_comp {D X : Scheme.{u}} (c : D ⟶ X)
    [IsClosedImmersion c] (U : X.Opens) (hU : (U : Set X)ᶜ ⊆ Set.range c.base) :
    IsCompl (Set.range ((c ⁻¹ᵁ U).closedComplement ≫ c).base) (Set.range U.ι.base) := by
  have h : Set.range ((c ⁻¹ᵁ U).closedComplement ≫ c).base = (U : Set X)ᶜ := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_closedComplement]
    refine Set.ext fun x ↦ ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · obtain ⟨y, rfl⟩ := hU hx
      exact ⟨y, hx, rfl⟩
  rw [h, Scheme.Opens.range_ι]
  exact isCompl_compl.symm

/-- For a closed immersion `c : D ⟶ X` and an open `U` of `X`, the pushforward along `c` of an
extension by zero along `c⁻¹(U)` vanishes on `D ∖ c⁻¹(U)`. -/
lemma isZero_upperStar_lowerStar_obj_openImmersionLowerShriek_preimage {D X : Scheme.{u}}
    (c : D ⟶ X) [IsClosedImmersion c] (U : X.Opens)
    (N : Mod (Sheaf (Scheme.ProEt.topology (c ⁻¹ᵁ U)) Ab.{u + 1})
      (condensedRingObj Λ (c ⁻¹ᵁ U))) :
    IsZero (((c ⁻¹ᵁ U).closedComplement ≫ c)^*⟦Λ⟧.obj
      ((c)_*⟦Λ⟧.obj ((((c ⁻¹ᵁ U).ι)_!open⟦Λ⟧).obj N))) := by
  refine IsZero.of_iso ?_ ((upperStarComp Λ _ c).app _)
  refine IsZero.of_iso ?_ (((c ⁻¹ᵁ U).closedComplement)^*⟦Λ⟧.mapIso
    (asIso ((upperStarLowerStarAdjunction Λ c).counit.app _)))
  refine isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ (c ⁻¹ᵁ U).ι
    (c ⁻¹ᵁ U).closedComplement ?_ N
  rw [Opens.range_closedComplement, Scheme.Opens.range_ι]
  exact disjoint_compl_right

/-- For a closed immersion `c : D ⟶ X` and an open `U` of `X` containing the complement of the
range of `c`, the pushforward along `c` of the extension by zero along `V = c⁻¹(U)` is the
extension by zero along `U` of the pushforward along `c|_U : V ⟶ U`. -/
noncomputable def lowerStarOpenImmersionLowerShriekIso {D X : Scheme.{u}} (c : D ⟶ X)
    [IsClosedImmersion c] (U : X.Opens) [QuasiCompact U.ι]
    (hU : (U : Set X)ᶜ ⊆ Set.range c.base)
    (N : Mod (Sheaf (Scheme.ProEt.topology (c ⁻¹ᵁ U)) Ab.{u + 1})
      (condensedRingObj Λ (c ⁻¹ᵁ U))) :
    (c)_*⟦Λ⟧.obj ((((c ⁻¹ᵁ U).ι)_!open⟦Λ⟧).obj N) ≅ (U.ι)_!open⟦Λ⟧.obj ((c ∣_ U)_*⟦Λ⟧.obj N) :=
  have := isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app Λ U.ι _
    (isCompl_range_closedComplement_preimage_comp c U hU)
    (isZero_upperStar_lowerStar_obj_openImmersionLowerShriek_preimage Λ c U N)
  have := isIso_lowerStarBaseChange_of_isPullback Λ (isPullback_morphismRestrict c U).flip
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ (c ⁻¹ᵁ U).ι).unit :=
    (openImmersionLowerShriekUpperStarAdjunction Λ (c ⁻¹ᵁ U).ι).unit_isIso_of_L_fully_faithful
  (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app
    ((c)_*⟦Λ⟧.obj ((((c ⁻¹ᵁ U).ι)_!open⟦Λ⟧).obj N)))).symm ≪≫
    (U.ι)_!open⟦Λ⟧.mapIso ((asIso (lowerStarBaseChange Λ
      (isPullback_morphismRestrict c U).flip.toCommSq)).app _ ≪≫
      (c ∣_ U)_*⟦Λ⟧.mapIso
        (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ (c ⁻¹ᵁ U).ι).unit.app N)).symm)

/-- For a closed immersion `c : D ⟶ X` into a scheme with noetherian underlying space, an open
`U` of `X` containing the complement of the range of `c`, a closed immersion
`c' : E ⟶ V = c⁻¹(U)` and a `Λ_E`-module `L` placed in degree `0`,
`Rc_* V_! Rc'_* L ≅ U_! R(c' ≫ c|_U)_* L`. -/
noncomputable def rightDerivedLowerStarOpenImmersionLowerShriekSingleIso {D E X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (c : D ⟶ X) [IsClosedImmersion c] (U : X.Opens)
    (hU : (U : Set X)ᶜ ⊆ Set.range c.base) (c' : E ⟶ c ⁻¹ᵁ U) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)) :
    (R((c)_*⟦Λ⟧)).obj (D(((c ⁻¹ᵁ U).ι)_!open⟦Λ⟧).obj
        ((R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L))) ≅
      D((U.ι)_!open⟦Λ⟧).obj
        ((R((c' ≫ c ∣_ U)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L)) :=
  haveI : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  haveI : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  haveI : TopologicalSpace.NoetherianSpace (c ⁻¹ᵁ U) :=
    (c ⁻¹ᵁ U).ι.isOpenEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  (R((c)_*⟦Λ⟧)).mapIso ((D(((c ⁻¹ᵁ U).ι)_!open⟦Λ⟧)).mapIso
      (rightDerivedLowerStarSingleIsoOfIsClosedImmersion Λ c' L) ≪≫
    ((((c ⁻¹ᵁ U).ι)_!open⟦Λ⟧).mapDerivedCategorySingleFunctor 0).app _) ≪≫
  rightDerivedLowerStarSingleIsoOfIsClosedImmersion Λ c _ ≪≫
  (DerivedCategory.singleFunctor _ 0).mapIso (lowerStarOpenImmersionLowerShriekIso Λ c U hU _) ≪≫
  ((((U.ι)_!open⟦Λ⟧).mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
  (D((U.ι)_!open⟦Λ⟧)).mapIso
    ((rightDerivedLowerStarSingleIsoOfIsClosedImmersion Λ (c ∣_ U) _).symm ≪≫
    (R((c ∣_ U)_*⟦Λ⟧)).mapIso (rightDerivedLowerStarSingleIsoOfIsClosedImmersion Λ c' L).symm ≪≫
    (rightDerivedLowerStarComp Λ c' (c ∣_ U)).app _)

end AlgebraicGeometry.ProEtale.CondensedRing
