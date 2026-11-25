/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.OpenClosed.Supported
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# The right adjoint of a closed direct image on étale sheaves

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. On étale sheaves, the
sections of `N` with support in `Z` form the kernel `Γ_Z N = ker(N ⟶ j_* j^* N)` of the unit of
`j^* ⊣ j_*`, and `i^! N = i^* Γ_Z N`. This file shows that `i^!` is right adjoint to `i_*` on
sheaves, for arbitrary coefficients, and that the right derived functor of `i^!` is right
adjoint to the direct image `Ri_* = i_*` on the unbounded derived categories of étale sheaves
of modules (blueprint `lemma-local-cohomology-right-adjoint--1`). No constructibility is involved.

The sheaf-level adjunction is the composite of three bijections
```
  Hom(M, i^* Γ_Z N) ≃ Hom(i_* M, i_* i^* Γ_Z N) ≃ Hom(i_* M, Γ_Z N) ≃ Hom(i_* M, N)
```
given by the full faithfulness of `i_*`, the unit `Γ_Z N ≅ i_* i^* Γ_Z N` (an isomorphism since
`Γ_Z N` restricts to zero on `U`, hence is a pushforward from `Z`,
`AlgebraicGeometry.Etale.mem_essImage_lowerStar_of_isZero_upperStar`), and the universal property
of the kernel (`j^* i_* M = 0`).

## Main definitions

- `AlgebraicGeometry.Etale.sectionsWithSupport`: `Γ_Z N = ker(N ⟶ j_* j^* N)`.
- `AlgebraicGeometry.Etale.closedUpperShriek`: `i^! = i^* ∘ Γ_Z`.
- `AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction`: `i_* ⊣ i^!` on sheaves.
- `AlgebraicGeometry.Etale.derivedLowerStarClosedUpperShriekAdjunction`: `Ri_* ⊣ Ri^!` on the
  unbounded derived categories (blueprint `lemma-local-cohomology-right-adjoint--1`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Etale

open Scheme

section Sheaf

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)

/-- The sheaf `Γ_Z N = ker(N ⟶ j_* j^* N)` of sections of an étale sheaf `N` on `X` with
support in the complement of `j`, the kernel of the unit of `j^* ⊣ j_*`. -/
noncomputable def sectionsWithSupport :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A where
  obj N := kernel ((upperStarLowerStarAdjunction A j).unit.app N)
  map φ := kernel.map _ _ φ ((j)_*[A].map ((j)^*[A].map φ))
    ((upperStarLowerStarAdjunction A j).unit.naturality φ).symm
  map_id N := equalizer.hom_ext (by simp)
  map_comp φ ψ := equalizer.hom_ext (by simp)

instance : (sectionsWithSupport A j).Additive where
  map_add := equalizer.hom_ext (by simp [sectionsWithSupport])

/-- The exceptional inverse image `i^! N = i^* ker(N ⟶ j_* j^* N)` along a closed immersion `i`
with complementary open immersion `j`, on étale sheaves: the inverse image of the sheaf of
sections with support in `Z` (`AlgebraicGeometry.Etale.sectionsWithSupport`). -/
noncomputable def closedUpperShriek :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Z.smallEtaleTopology A :=
  sectionsWithSupport A j ⋙ (i)^*[A]

instance : (closedUpperShriek A i j).Additive := by
  unfold closedUpperShriek
  infer_instance

/-- The inclusion `Γ_Z N ⟶ N`. -/
noncomputable def sectionsWithSupportι : sectionsWithSupport A j ⟶ 𝟭 _ where
  app N := kernel.ι _
  naturality _ _ φ := by simp [sectionsWithSupport]

@[reassoc (attr := simp)]
lemma sectionsWithSupportι_app_comp_unit_app (N : Sheaf X.smallEtaleTopology A) :
    (sectionsWithSupportι A j).app N ≫ (upperStarLowerStarAdjunction A j).unit.app N = 0 :=
  kernel.condition _

/-- The sheaf `Γ_Z N` restricts to zero along the open immersion `j`: `j^*` is exact and `j^*` of
the unit `N ⟶ j_* j^* N` is an isomorphism, a section of the invertible counit. -/
lemma isZero_upperStar_sectionsWithSupport [IsOpenImmersion j] (N : Sheaf X.smallEtaleTopology A) :
    IsZero ((j)^*[A].obj ((sectionsWithSupport A j).obj N)) := by
  set adj := upperStarLowerStarAdjunction A j
  have : IsIso ((j)^*[A].map (adj.unit.app N)) := by
    have : IsIso ((j)^*[A].map (adj.unit.app N) ≫ adj.counit.app ((j)^*[A].obj N)) := by
      rw [adj.left_triangle_components N]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  exact (isZero_kernel_of_mono ((j)^*[A].map (adj.unit.app N))).of_iso
    (PreservesKernel.iso _ _)

variable [IsClosedImmersion i] [IsOpenImmersion j]

/-- The unit `F ⟶ i_* i^* F` is an isomorphism for a sheaf `F` restricting to zero on the open
complement of `i`: such an `F` is a pushforward `i_* G`
(`AlgebraicGeometry.Etale.mem_essImage_lowerStar_of_isZero_upperStar`), and the unit at a
pushforward is invertible since `i_*` is fully faithful. -/
lemma isIso_upperStarLowerStarAdjunction_unit_app_of_isZero
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {F : Sheaf X.smallEtaleTopology A}
    (hF : IsZero ((j)^*[A].obj F)) :
    IsIso ((upperStarLowerStarAdjunction A i).unit.app F) := by
  set adj := upperStarLowerStarAdjunction A i
  obtain ⟨G, ⟨e⟩⟩ := mem_essImage_lowerStar_of_isZero_upperStar i hij hF
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  have hG : IsIso (adj.unit.app ((i)_*[A].obj G)) := by
    have h := adj.right_triangle_components G
    have : IsIso (adj.unit.app ((i)_*[A].obj G) ≫ (i)_*[A].map (adj.counit.app G)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ ((i)_*[A].map (adj.counit.app G))
  have h := adj.unit.naturality e.hom
  have : adj.unit.app F = e.inv ≫ adj.unit.app ((i)_*[A].obj G) ≫
      ((i)^*[A] ⋙ (i)_*[A]).map e.hom := by
    rw [← h]
    simp
  rw [this]
  infer_instance

omit [IsClosedImmersion i] in
/-- A morphism `i_* M ⟶ N` is killed by the unit `N ⟶ j_* j^* N`, since `j^* i_* M = 0`. -/
lemma lowerStar_map_comp_unit_app_eq_zero (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {M : Sheaf Z.smallEtaleTopology A} {N : Sheaf X.smallEtaleTopology A}
    (f : (i)_*[A].obj M ⟶ N) : f ≫ (upperStarLowerStarAdjunction A j).unit.app N = 0 := by
  have hz : IsZero ((j)^*[A].obj ((i)_*[A].obj M)) :=
    isZero_upperStar_lowerStar_of_disjoint_range A j i
      (by rw [hij]; exact disjoint_compl_right) M
  have h := (upperStarLowerStarAdjunction A j).unit.naturality f
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h
  rw [h, (((j)_*[A]).map_isZero hz).eq_of_tgt
    ((upperStarLowerStarAdjunction A j).unit.app _) 0, zero_comp]

/-- The bijection `Hom(i_* M, N) ≃ Hom(M, i^! N)` underlying
`AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction`, through the full faithfulness of
`i_*`, the invertible unit at `Γ_Z N` and the universal property of the kernel `Γ_Z N`. -/
noncomputable def lowerStarClosedUpperShriekHomEquiv
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (M : Sheaf Z.smallEtaleTopology A)
    (N : Sheaf X.smallEtaleTopology A) :
    ((i)_*[A].obj M ⟶ N) ≃ (M ⟶ (closedUpperShriek A i j).obj N) :=
  have := isIso_upperStarLowerStarAdjunction_unit_app_of_isZero A i j hij
    (isZero_upperStar_sectionsWithSupport A j N)
  { toFun f := (i)_*[A].preimage (kernel.lift _ f
        (lowerStar_map_comp_unit_app_eq_zero A i j hij f) ≫
      (upperStarLowerStarAdjunction A i).unit.app _)
    invFun g := (i)_*[A].map g ≫ inv ((upperStarLowerStarAdjunction A i).unit.app
      ((sectionsWithSupport A j).obj N)) ≫ kernel.ι _
    left_inv f := by
      simp only [Functor.map_preimage, Category.assoc]
      erw [IsIso.hom_inv_id_assoc]
      exact kernel.lift_ι _ _ _
    right_inv g := by
      apply (i)_*[A].map_injective
      simp only [Functor.map_preimage]
      refine (cancel_mono (inv ((upperStarLowerStarAdjunction A i).unit.app _))).1 ?_
      refine (cancel_mono (kernel.ι _)).1 ?_
      simp [closedUpperShriek, sectionsWithSupport] }

lemma lowerStarClosedUpperShriekHomEquiv_symm_apply
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {M : Sheaf Z.smallEtaleTopology A}
    {N : Sheaf X.smallEtaleTopology A} (g : M ⟶ (closedUpperShriek A i j).obj N) :
    haveI := isIso_upperStarLowerStarAdjunction_unit_app_of_isZero A i j hij
      (isZero_upperStar_sectionsWithSupport A j N)
    (lowerStarClosedUpperShriekHomEquiv A i j hij M N).symm g =
      (i)_*[A].map g ≫ inv ((upperStarLowerStarAdjunction A i).unit.app
        ((sectionsWithSupport A j).obj N)) ≫ kernel.ι _ :=
  rfl

lemma lowerStarClosedUpperShriekHomEquiv_symm_naturality_right
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {M : Sheaf Z.smallEtaleTopology A}
    {N N' : Sheaf X.smallEtaleTopology A} (g : M ⟶ (closedUpperShriek A i j).obj N)
    (ψ : N ⟶ N') :
    (lowerStarClosedUpperShriekHomEquiv A i j hij M N').symm
        (g ≫ (closedUpperShriek A i j).map ψ) =
      (lowerStarClosedUpperShriekHomEquiv A i j hij M N).symm g ≫ ψ := by
  have := isIso_upperStarLowerStarAdjunction_unit_app_of_isZero A i j hij
    (isZero_upperStar_sectionsWithSupport A j N)
  have := isIso_upperStarLowerStarAdjunction_unit_app_of_isZero A i j hij
    (isZero_upperStar_sectionsWithSupport A j N')
  have hη := (upperStarLowerStarAdjunction A i).unit.naturality ((sectionsWithSupport A j).map ψ)
  have hη' : (i)_*[A].map ((i)^*[A].map ((sectionsWithSupport A j).map ψ)) ≫
      inv ((upperStarLowerStarAdjunction A i).unit.app ((sectionsWithSupport A j).obj N')) =
      inv ((upperStarLowerStarAdjunction A i).unit.app ((sectionsWithSupport A j).obj N)) ≫
        (sectionsWithSupport A j).map ψ := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hη.symm
  rw [lowerStarClosedUpperShriekHomEquiv_symm_apply,
    lowerStarClosedUpperShriekHomEquiv_symm_apply]
  simp only [closedUpperShriek, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hη']
  simp [sectionsWithSupport]

/-- The sheaf-level adjunction `i_* ⊣ i^!` for a closed immersion `i` with complementary open
immersion `j`, on étale sheaves with values in an arbitrary Grothendieck abelian category. -/
noncomputable def lowerStarClosedUpperShriekAdjunction
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (i)_*[A] ⊣ closedUpperShriek A i j :=
  Adjunction.mkOfHomEquiv
    { homEquiv := lowerStarClosedUpperShriekHomEquiv A i j hij
      homEquiv_naturality_left_symm {M M' N} φ g := by
        simp [lowerStarClosedUpperShriekHomEquiv_symm_apply]
      homEquiv_naturality_right {M N N'} f ψ := by
        rw [← Equiv.eq_symm_apply, lowerStarClosedUpperShriekHomEquiv_symm_naturality_right,
          Equiv.symm_apply_apply] }

end Sheaf

section Derived

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`: Closed-immersion right adjoint before
restriction.

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. On the unbounded
derived categories of étale sheaves of modules, the direct image `Ri_*` has a right adjoint, the
right derived functor `Ri^!` of the sheaf-level `i^! = i^* Γ_Z`
(`AlgebraicGeometry.Etale.closedUpperShriek`). No constructibility is assumed of the values of
this right adjoint.

On sheaves `i_* ⊣ i^!` (`AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction`), and
`i_*` is exact (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`), so
`Ri_*` is `i_*` applied termwise and
`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction` applies: `i^!` is computed
on K-injective resolutions. -/
noncomputable def derivedLowerStarClosedUpperShriekAdjunction
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctor ⊣
      (closedUpperShriek (ModuleCat.{u + 1} R) i j).rightDerivedFunctor :=
  ((lowerStarClosedUpperShriekAdjunction _ i j hij).mapDerivedCategoryRightDerivedAdjunction
    ).ofNatIsoLeft ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctorIsoMapDerivedCategory.symm

/-- The direct image `Ri_*` along a closed immersion is a left adjoint on the unbounded derived
categories of étale sheaves of modules
(`AlgebraicGeometry.Etale.derivedLowerStarClosedUpperShriekAdjunction`). -/
lemma isLeftAdjoint_rightDerivedFunctor_lowerStar_of_isClosedImmersion
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctor.IsLeftAdjoint :=
  (derivedLowerStarClosedUpperShriekAdjunction i j hij).isLeftAdjoint

end Derived

end Etale

end AlgebraicGeometry
