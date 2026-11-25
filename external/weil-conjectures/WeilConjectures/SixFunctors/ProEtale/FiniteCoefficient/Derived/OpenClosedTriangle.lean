/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Localization
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence

/-!
# The open–closed triangle on the pro-étale site

Let `i : Z ⟶ X` be a closed immersion with quasi-compact complementary open immersion
`j : U ⟶ X`, and `R` a commutative ring. On the unbounded derived categories of pro-étale
sheaves of `R`-modules:

* every `M` sits in a distinguished triangle `j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ (j_! j^* M)[1]`
  formed by the counit of `j_! ⊣ j^*` and the unit of `i^* ⊣ i_*`
  (`AlgebraicGeometry.ProEtale.exists_distTriang_openClosed`);
* in particular every `K ∈ D(U_proét)` sits in a distinguished triangle
  `j_! K ⟶ Rj_* K ⟶ i_* i^* Rj_* K ⟶ (j_! K)[1]`, functorial in `K`
  (`AlgebraicGeometry.ProEtale.exists_distTriang_openImmersionLowerShriek_rightDerived`,
  part (1) of blueprint `proposition-extension-zero-restriction-closed-subscheme`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {R : Type (u + 1)} [CommRing R] {Z U X : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

omit [IsClosedImmersion i] in
/-- `D(i^*) D(j_!) = 0` when the ranges of `i` and of the open immersion `j` are disjoint: on
homology sheaves this is `i^* j_! = 0`. -/
lemma isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (N : DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))) :
    IsZero (D((i)^*[ModuleCat.{u + 1} R]).obj (D((j)_!open[ModuleCat.{u + 1} R]).obj N)) :=
  (Functor.isZero_mapDerivedCategory_obj ((j)_!open[ModuleCat.{u + 1} R] ⋙
    (i)^*[ModuleCat.{u + 1} R]) N fun _ ↦ isZero_upperStar_openImmersionLowerShriek _ j i
      (Set.disjoint_iff_inter_eq_empty.1 hij.symm) _).of_iso
    ((((j)_!open[ModuleCat.{u + 1} R]).mapDerivedCategoryCompIso _).app N)

variable [QuasiCompact j] [PreservesFiniteColimits ((i)_*[ModuleCat.{u + 1} R])]

/-- **The open–closed triangle** on the pro-étale site: for a closed immersion `i` with
quasi-compact open complement `j`, every `M ∈ D(X_proét)` sits in a distinguished triangle
`j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ (j_! j^* M)[1]`, formed by the counit of `j_! ⊣ j^*` and the unit of
`i^* ⊣ i_*` (blueprint `proposition-extension-zero-restriction-closed-subscheme`). The exactness of
`i_*` is `AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`. -/
theorem exists_distTriang_openClosed (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    ∃ w, Triangle.mk
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app M)
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R)
        i).mapDerivedCategoryAdjunction.unit.app
        M) w ∈ distTriang _ := by
  set adj := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).mapDerivedCategoryAdjunction
  set adj' := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j
  have : IsIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit :=
    isIso_upperStarLowerStarAdjunction_counit (ModuleCat.{u + 1} R) i
  have : IsIso adj.counit := Adjunction.isIso_mapDerivedCategoryAdjunction_counit _
  have : IsIso adj'.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  -- complete the counit `j_! j^* M ⟶ M` to a distinguished triangle `j_! j^* M ⟶ M ⟶ C`
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (adj'.counit.app M)
  -- `j^* C = 0`, since `j^*` of the counit is invertible
  have hCj : IsZero (D((j)^*[ModuleCat.{u + 1} R]).obj C) := by
    refine (Triangle.isZero₃_iff_isIso₁ _
      (D((j)^*[ModuleCat.{u + 1} R]).map_distinguished _ hT)).2 ?_
    change IsIso (D((j)^*[ModuleCat.{u + 1} R]).map (adj'.counit.app M))
    rw [← IsIso.inv_eq_of_hom_inv_id (adj'.right_triangle_components M)]
    infer_instance
  -- `i^* g` is invertible, since `i^* j_! j^* M = 0`
  have hgi : IsIso (D((i)^*[ModuleCat.{u + 1} R]).map g) :=
    (Triangle.isZero₁_iff_isIso₂ _ (D((i)^*[ModuleCat.{u + 1} R]).map_distinguished _ hT)).1
      (isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek
        i j hij.disjoint _)
  -- the unit `C ⟶ i_* i^* C` is invertible: its cone is killed by `i^*` and `j^*`
  have hηC : IsIso (adj.unit.app C) := by
    obtain ⟨W, v, w, h₁⟩ := distinguished_cocone_triangle (adj.unit.app C)
    have hiu : IsIso (D((i)^*[ModuleCat.{u + 1} R]).map (adj.unit.app C)) :=
      have := IsIso.id (D((i)^*[ModuleCat.{u + 1} R]).obj C)
      IsIso.of_isIso_fac_right (adj.left_triangle_components C)
    have hju : IsIso (D((j)^*[ModuleCat.{u + 1} R]).map (adj.unit.app C)) :=
      isIso_of_source_target_iso_zero _ hCj.isoZero
        (isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_lowerStar i j hij.disjoint
          _).isoZero
    have hW : IsZero W := isZero_of_isZero_mapDerivedCategoryUpperStar_of_isCompl i j hij
      ((Triangle.isZero₃_iff_isIso₁ _
        (D((i)^*[ModuleCat.{u + 1} R]).map_distinguished _ h₁)).2 hiu)
      ((Triangle.isZero₃_iff_isIso₁ _
        (D((j)^*[ModuleCat.{u + 1} R]).map_distinguished _ h₁)).2 hju)
    exact (Triangle.isZero₃_iff_isIso₁ _ h₁).1 hW
  let e : C ≅ D((i)_*[ModuleCat.{u + 1} R]).obj (D((i)^*[ModuleCat.{u + 1} R]).obj M) :=
    asIso (adj.unit.app C) ≪≫
      D((i)_*[ModuleCat.{u + 1} R]).mapIso (asIso (D((i)^*[ModuleCat.{u + 1} R]).map g)).symm
  have he : g ≫ e.hom = adj.unit.app M := by
    have := adj.unit.naturality g
    dsimp at this
    simp only [e, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    rw [reassoc_of% this, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  refine ⟨e.inv ≫ h, isomorphic_distinguished _ hT _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp)
    (by rw [← he]; simp) (by simp)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`lemma-local-cohomology-right-adjoint--1`), part (1): for a closed immersion `i` with quasi-compact
open complement `j : U ⟶ X` and every `K ∈ D(U_proét)`, there is a distinguished triangle
`j_! K ⟶ Rj_* K ⟶ i_* i^* Rj_* K ⟶ (j_! K)[1]` in `D(X_proét)`, functorial in `K`: its first
map is adjoint to the inverse of the counit isomorphism `j^* Rj_* K ≅ K` and its second map is
the unit of `i^* ⊣ i_*`. It is the open–closed triangle
(`AlgebraicGeometry.ProEtale.exists_distTriang_openClosed`) of `Rj_* K`. -/
theorem exists_distTriang_openImmersionLowerShriek_rightDerived
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))) :
    ∃ w, Triangle.mk
      (D((j)_!open[ModuleCat.{u + 1} R]).map
          (inv ((mapDerivedUpperStarLowerStarAdjunction R j).counit.app K)) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app
          (R((j)_*[ModuleCat.{u + 1} R]).obj K))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R)
        i).mapDerivedCategoryAdjunction.unit.app
        (R((j)_*[ModuleCat.{u + 1} R]).obj K)) w ∈ distTriang _ := by
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed i j hij (R((j)_*[ModuleCat.{u + 1} R]).obj K)
  let e := D((j)_!open[ModuleCat.{u + 1} R]).mapIso
    (asIso ((mapDerivedUpperStarLowerStarAdjunction R j).counit.app K)).symm
  refine ⟨w ≫ e.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ hw _ ?_⟩
  refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_
  · simp [e]
  · simp only [Triangle.mk_mor₃, Iso.refl_hom,
      Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

end ProEtale

end AlgebraicGeometry
