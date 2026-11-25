/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ProperBaseChange

/-!

# Extensions by zero and finite pushforwards

Let `f : X' ⟶ X` be a finite morphism, `j : U ⟶ X` an open immersion with closed complement
`i : Z ⟶ X`, and `j' : U' ⟶ X'` the base change of `j` along `f`, with `v : U' ⟶ U`. For a
bounded constructible complex `M` on `U'` with finite coefficients,
`Rf_* (j'_! M) ≅ j_! (Rv_* M)`
(`ProEtale.CondensedRing.nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso`).

Indeed, the counit `j_! Lj^* A ⟶ A` at `A = Rf_* (j'_! M)` is an isomorphism, since `Lj^*` and
`Li^*` jointly reflect isomorphisms: `Lj^*` of it is invertible because `j_!` is fully faithful,
and `Li^*` kills both sides, `Li^* A` being `Rf_{Z*} Li'^* (j'_! M) = 0` by proper base change.
Finally `Lj^* A ≅ Rv_* Lj'^* j'_! M ≅ Rv_* M` by base change along the open immersion `j`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- If `Li^* A = 0` for the closed complement `i` of a quasi-compact open immersion `j`, the counit
`j_! j^* A ⟶ A` is an isomorphism. -/
theorem isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hA : IsZero (L((i)^*⟦Λ⟧).obj A)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).counit.app A) := by
  set adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j
  have : IsIso adj.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hj : IsIso (L((j)^*⟦Λ⟧).map (adj.counit.app A)) := by
    rw [NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j)]
    have h := adj.right_triangle_components A
    have : IsIso (adj.unit.app (D((j)^*⟦Λ⟧).obj A) ≫ D((j)^*⟦Λ⟧).map (adj.counit.app A)) := by
      rw [h]
      exact (Iso.refl _).isIso_hom
    exact IsIso.of_isIso_comp_left (adj.unit.app (D((j)^*⟦Λ⟧).obj A)) _
  have hi : IsIso (L((i)^*⟦Λ⟧).map (adj.counit.app A)) :=
    ⟨⟨0, (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j i
      hij.disjoint.symm _).eq_of_src _ _, hA.eq_of_src _ _⟩⟩
  have : ∀ b, IsIso ((pairFunctor L((j)^*⟦Λ⟧) L((i)^*⟦Λ⟧) b).map (adj.counit.app A)) := by
    intro b
    cases b
    · exact hi
    · exact hj
  exact (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i j hij).isIso _

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Finite pushforward of an extension by zero.** Let `f : X' ⟶ X` be finite,
`j : U ⟶ X` a quasi-compact open immersion whose range is complementary to that of a closed
immersion `i : Z ⟶ X`, and `j' : U' ⟶ X'`, `v : U' ⟶ U` the base change of `j` along `f`. For a
complex `M` on `U'` such that `j'_! M` is of étale origin, `Rf_* (j'_! M) ≅ j_! (Rv_* M)`. -/
theorem nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso {X X' U U' Z : Scheme.{u}}
    (f : X' ⟶ X) [IsFinite f] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (j' : U' ⟶ X')
    [IsOpenImmersion j'] (v : U' ⟶ U) (sq : IsPullback j' v f j) (i : Z ⟶ X)
    [IsClosedImmersion i] (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U') Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) U')))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X'
      ((finiteCoefficientDerivedEquivalence X' T).functor.obj
        (D((j')_!open⟦Profinite.continuousMapRingObj T⟧).obj M))) :
    Nonempty (R((f)_*⟦Profinite.continuousMapRingObj T⟧).obj
        (D((j')_!open⟦Profinite.continuousMapRingObj T⟧).obj M) ≅
      D((j)_!open⟦Profinite.continuousMapRingObj T⟧).obj
        (R((v)_*⟦Profinite.continuousMapRingObj T⟧).obj M)) := by
  have sqZ : IsPullback (pullback.snd i f) (pullback.fst i f) f i :=
    (IsPullback.of_hasPullback i f).flip
  have hZ' : Disjoint (Set.range j'.base) (Set.range (pullback.snd i f).base) := by
    rw [Set.disjoint_iff]
    rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h₁ : f.base (j'.base a) = j.base (v.base a) := by
      rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    have h₂ : f.base ((pullback.snd i f).base b) = i.base ((pullback.fst i f).base b) := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    rw [hb] at h₂
    exact Set.disjoint_iff.1 hij.disjoint ⟨⟨_, h₂.symm.trans h₁⟩, ⟨_, rfl⟩⟩
  have hbc := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T sqZ _ hM
  have hiA : IsZero (L((i)^*⟦Profinite.continuousMapRingObj T⟧).obj
      (R((f)_*⟦Profinite.continuousMapRingObj T⟧).obj
        (D((j')_!open⟦Profinite.continuousMapRingObj T⟧).obj M))) :=
    ((R(((pullback.fst i f))_*⟦Profinite.continuousMapRingObj T⟧)).map_isZero
      (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint _ j' _ hZ' M)).of_iso
      (asIso ((baseChangeMap (Profinite.continuousMapRingObj T) sqZ.toCommSq).app _))
  have hε := isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app _ j i hij _ hiA
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.continuousMapRingObj T) j').unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hbcj := isIso_baseChangeMap_of_weaklyEtale (Profinite.continuousMapRingObj T) sq
  exact ⟨(asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).counit.app _)).symm ≪≫
    D((j)_!open⟦Profinite.continuousMapRingObj T⟧).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _ j).symm.app _ ≪≫
        asIso ((baseChangeMap (Profinite.continuousMapRingObj T) sq.toCommSq).app _) ≪≫
        R((v)_*⟦Profinite.continuousMapRingObj T⟧).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _ j').app _ ≪≫
            (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction _ j').unit.app M)).symm))⟩

end AlgebraicGeometry.ProEtale.CondensedRing
