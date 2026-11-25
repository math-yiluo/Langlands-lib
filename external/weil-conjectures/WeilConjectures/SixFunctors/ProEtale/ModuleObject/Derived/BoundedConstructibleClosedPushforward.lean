/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative

/-!
# Closed pushforward of bounded constructible complexes

Let `Λ` be a commutative condensed ring and `X` a scheme with noetherian underlying space.

* A complex on `X` whose restrictions to an open `U` (with quasi-compact inclusion) and to a closed
  subscheme onto its complement are bounded constructible is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_of_openClosed`).
* The derived pushforward `Rc_*` along a closed immersion `c : Z ⟶ X` preserves bounded
  constructible complexes
  (`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion`):
  `Lc^* Rc_* B ≅ B`, and the restriction of `Rc_* B` to the open complement of `Z` vanishes, by
  the adjunctions `j_! ⊣ Lj^*` and `Lc^* ⊣ Rc_*` and the vanishing of `Lc^* j_!`.
* A complex whose restriction to a quasi-compact open `U` vanishes is supported on the closed
  complement `Z`: the unit `K ⟶ Ri_* Li^* K` is an isomorphism
  (`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero`).

No finiteness hypothesis on `X` over a field is needed, unlike for the general pushforward.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- A zero complex is bounded constructible. -/
lemma boundedConstructible_of_isZero {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hK : IsZero K) : boundedConstructible (condensedRingObj Λ X) K :=
  (mem_boundedConstructible_iff _ _).2
    ⟨⟨0, 0, fun _ _ ↦ (DerivedCategory.homologyFunctor _ _).map_isZero hK⟩,
      fun _ ↦ ProEtale.isConstructibleModuleObject_of_isZero _
        ((DerivedCategory.homologyFunctor _ _).map_isZero hK)⟩

/-- **Open–closed locality of bounded constructibility**: for an open immersion `j` with
quasi-compact range and a closed immersion `i` onto its complement, a complex whose derived
restrictions along `j` and `i` are bounded constructible is bounded constructible. -/
theorem boundedConstructible_of_openClosed {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hj : boundedConstructible (condensedRingObj Λ U) ((L((j)^*⟦Λ⟧)).obj K))
    (hi : boundedConstructible (condensedRingObj Λ Z) ((L((i)^*⟦Λ⟧)).obj K)) :
    boundedConstructible (condensedRingObj Λ X) K := by
  have hc : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [hij]
    exact isCompl_compl.symm
  obtain ⟨⟨aj, bj, habj⟩, hcj⟩ := (mem_boundedConstructible_iff _ _).1 hj
  obtain ⟨⟨ai, bi, habi⟩, hci⟩ := (mem_boundedConstructible_iff _ _).1 hi
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨min aj ai, max bj bi, fun q hq ↦ ?_⟩,
    fun q ↦ ?_⟩
  · have hqi : q < ai ∨ bi < q := hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_right _ _))
      (fun h ↦ lt_of_le_of_lt (le_max_right _ _) h)
    have hqj : q < aj ∨ bj < q := hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _))
      (fun h ↦ lt_of_le_of_lt (le_max_left _ _) h)
    exact isZero_of_isZero_upperStar_of_isCompl Λ i j hc _
      ((habi q hqi).of_iso ((leftDerivedUpperStarHomologyIso Λ i q).app K))
      ((habj q hqj).of_iso ((leftDerivedUpperStarHomologyIso Λ j q).app K))
  · exact isConstructibleModuleObject_of_openClosed Λ j i hij _
      ((hcj q).of_iso ((leftDerivedUpperStarHomologyIso Λ j q).app K).symm)
      ((hci q).of_iso ((leftDerivedUpperStarHomologyIso Λ i q).app K).symm)

/-- `Lj^* Rc_*` vanishes when the ranges of the open immersion `j` and of the closed immersion `c`
are disjoint: a morphism `N ⟶ Lj^* Rc_* B` is a morphism `Lc^* j_! N ⟶ B`, and `Lc^* j_! = 0`. -/
lemma isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (c : Z ⟶ X)
    (hjc : Disjoint (Set.range j.base) (Set.range c.base))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    IsZero ((L((j)^*⟦Λ⟧)).obj ((R((c)_*⟦Λ⟧)).obj B)) := by
  have h : IsZero (D((j)^*⟦Λ⟧).obj ((R((c)_*⟦Λ⟧)).obj B)) := by
    rw [IsZero.iff_id_eq_zero]
    apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _).symm.injective
    apply ((derivedUpperStarLowerStarAdjunction Λ c).homEquiv _ _).symm.injective
    exact (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j c hjc
      _).eq_of_src _ _
  exact h.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app _)

/-- **Closed pushforward preserves bounded constructibility**: for a closed immersion
`c : Z ⟶ X` into a scheme with noetherian underlying space, `Rc_*` maps bounded constructible
complexes to bounded constructible complexes. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion {X Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (c : Z ⟶ X) [IsClosedImmersion c]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))} (hB : boundedConstructible (condensedRingObj Λ Z) B) :
    boundedConstructible (condensedRingObj Λ X) ((R((c)_*⟦Λ⟧)).obj B) := by
  let U : X.Opens := ⟨(Set.range c.base)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hU : Set.range U.ι.base = (Set.range c.base)ᶜ := Scheme.Opens.range_ι U
  refine boundedConstructible_of_openClosed Λ U.ι c (by rw [hU, compl_compl]) _ ?_ ?_
  · exact boundedConstructible_of_isZero Λ
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint Λ U.ι c
        (by rw [hU]; exact disjoint_compl_left) B)
  · exact (boundedConstructible _).prop_of_iso
      (asIso ((derivedUpperStarLowerStarAdjunction Λ c).counit.app B)).symm hB

/-- A complex whose restriction to the open `U` vanishes is supported on the closed complement
`Z`: the unit `K ⟶ Ri_* Li^* K` is an isomorphism. -/
theorem isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hK : IsZero ((L((j)^*⟦Λ⟧)).obj K)) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K) := by
  have hN : IsZero ((L((j)^*⟦Λ⟧)).obj ((R((i)_*⟦Λ⟧)).obj ((L((i)^*⟦Λ⟧)).obj K))) :=
    isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint Λ j i
      hij.symm.disjoint _
  have h₁ : IsIso ((L((j)^*⟦Λ⟧)).map ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K)) :=
    isIso_of_source_target_iso_zero _ hK.isoZero hN.isoZero
  have h₂ : IsIso ((L((i)^*⟦Λ⟧)).map ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K)) :=
    IsIso.of_isIso_fac_right (hh := IsIso.id _)
      ((derivedUpperStarLowerStarAdjunction Λ i).left_triangle_components K)
  exact (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i j hij).isIso_of_pairFunctor
    _ h₁ h₂

end AlgebraicGeometry.ProEtale.CondensedRing
