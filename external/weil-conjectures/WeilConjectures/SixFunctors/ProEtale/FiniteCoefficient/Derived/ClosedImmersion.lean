/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# The exceptional inverse image along a closed immersion on pro-étale sheaves

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. On
pro-étale sheaves, the sections of `N` with support in `Z` form the kernel
`Γ_Z N = ker(N ⟶ j_* j^* N)` of the unit of `j^* ⊣ j_*`, and

`i^!₀ N = i^* Γ_Z N`

(`AlgebraicGeometry.ProEtale.closedUpperShriek`, blueprint
`definition-local-cohomology--1`). For pro-étale sheaves of modules it is right adjoint
to the exact functor `i_*` (`AlgebraicGeometry.ProEtale.lowerStarClosedUpperShriekAdjunction`),
so its right derived functor is right adjoint to `i_*` on the unbounded derived categories
(`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`, blueprint
`lemma-local-cohomology-right-adjoint--1`), and the unit of this adjunction is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app`,
blueprint `lemma-local-cohomology-right-adjoint--1`).

## The sheaf-level adjunction

Write `Sh_Z(X)` for the full subcategory of sheaves `F` with `j^* F = 0`. The adjunction
`i_* ⊣ i^!₀` is the composite of two adjunctions:

* `i_* : Sh(Z) ⥤ Sh_Z(X)` is an equivalence with inverse `i^*`: the counit `i^* i_* ⟶ 𝟭` is an
  isomorphism (`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`), and so
  is the unit `F ⟶ i_* i^* F` for `F ∈ Sh_Z(X)`
  (`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`);
* the inclusion `Sh_Z(X) ⥤ Sh(X)` is left adjoint to `Γ_Z`: a map `F ⟶ N` from `F ∈ Sh_Z(X)`
  is killed by the unit `N ⟶ j_* j^* N`, since `j_* j^* F = 0`, so it factors uniquely through
  the kernel `Γ_Z N`, and `j^* Γ_Z N = 0` because `j^*` is exact and `j^* j_* ≅ 𝟭`.

## Main definitions

- `AlgebraicGeometry.ProEtale.sectionsWithSupport`: `Γ_Z N = ker(N ⟶ j_* j^* N)`.
- `AlgebraicGeometry.ProEtale.closedUpperShriek`: `i^!₀ = i^* ∘ Γ_Z`.
- `AlgebraicGeometry.ProEtale.lowerStarClosedUpperShriekAdjunction`: `i_* ⊣ i^!₀`.
- `AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`: `i_* ⊣ R i^!₀` on
  the unbounded derived categories.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Definition

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)

/-- The sheaf `Γ_Z N = ker(N ⟶ j_* j^* N)` of sections of a pro-étale sheaf `N` on `X` with
support in the complement of `j`, the kernel of the unit of `j^* ⊣ j_*`. With
`AlgebraicGeometry.ProEtale.closedUpperShriek` and `AlgebraicGeometry.ProEtale.IsFlasqueFor`, this
is the pro-étale form of blueprint `definition-local-cohomology`. -/
noncomputable def sectionsWithSupport :
    Sheaf (ProEt.topology X) A ⥤ Sheaf (ProEt.topology X) A where
  obj N := kernel ((upperStarLowerStarAdjunction A j).unit.app N)
  map φ := kernel.map _ _ φ ((j)_*[A].map ((j)^*[A].map φ))
    ((upperStarLowerStarAdjunction A j).unit.naturality φ).symm
  map_id N := equalizer.hom_ext (by simp)
  map_comp φ ψ := equalizer.hom_ext (by simp)

instance : (sectionsWithSupport A j).Additive where
  map_add := equalizer.hom_ext (by simp [sectionsWithSupport])

/-- Blueprint `definition-local-cohomology--1`: for a closed immersion `i : Z ⟶ X` with
complementary open immersion `j`, the functor

`i^!₀ N = i^* ker(N ⟶ j_* j^* N)`

on pro-étale sheaves, the closed inverse image of the sheaf of sections with support in `Z`
(`AlgebraicGeometry.ProEtale.sectionsWithSupport`). A morphism of sheaves acts through the
induced map of kernels. It is also the functor `s^!` of blueprint `definition-local-cohomology`
(pro-étale form), with `s_* s^! ≅ 𝒢_Z`
(`AlgebraicGeometry.ProEtale.closedUpperShriekCompLowerStarIso`). -/
noncomputable def closedUpperShriek :
    Sheaf (ProEt.topology X) A ⥤ Sheaf (ProEt.topology Z) A :=
  sectionsWithSupport A j ⋙ (i)^*[A]

instance : (closedUpperShriek A i j).Additive := by
  unfold closedUpperShriek
  infer_instance

/-- The inclusion `Γ_Z N ⟶ N`. -/
noncomputable def sectionsWithSupportι : sectionsWithSupport A j ⟶ 𝟭 _ where
  app N := kernel.ι _
  naturality _ _ φ := by simp [sectionsWithSupport]

@[reassoc (attr := simp)]
lemma sectionsWithSupportι_app_comp_unit_app (N : Sheaf (ProEt.topology X) A) :
    (sectionsWithSupportι A j).app N ≫ (upperStarLowerStarAdjunction A j).unit.app N = 0 :=
  kernel.condition _


variable {A} in
/-- The counit `j^* j_* ⟶ 𝟭` of the pro-étale adjunction `j^* ⊣ j_*` along an open immersion is
an isomorphism: up to the identification of `j^*` with restriction, it is the counit of the
restriction adjunction. -/
instance isIso_upperStarLowerStarAdjunction_counit_of_isOpenImmersion {j : U ⟶ X}
    [IsOpenImmersion j] : IsIso (upperStarLowerStarAdjunction A j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  rw [← Adjunction.leftAdjointUniq_hom_app_counit (upperStarLowerStarAdjunction _ j)
    (openImmersionRestrictionLowerStarAdjunction _ j)]
  exact inferInstanceAs (IsIso ((upperStarIsoOpenImmersionRestriction _ j).hom.app _ ≫ _))

/-- The sheaf `Γ_Z N` of sections with support in the complement of an open immersion `j`
restricts to zero on `j`: `j^*` is exact and `j^*` of the unit `N ⟶ j_* j^* N` is an isomorphism,
inverse to the counit. -/
lemma isZero_upperStar_sectionsWithSupport [IsOpenImmersion j] (N : Sheaf (ProEt.topology X) A) :
    IsZero ((j)^*[A].obj ((sectionsWithSupport A j).obj N)) := by
  set adj := upperStarLowerStarAdjunction A j
  have : IsIso ((j)^*[A].map (adj.unit.app N)) := by
    have : IsIso ((j)^*[A].map (adj.unit.app N) ≫ adj.counit.app ((j)^*[A].obj N)) := by
      rw [adj.left_triangle_components N]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  exact (isZero_kernel_of_mono ((j)^*[A].map (adj.unit.app N))).of_iso
    (PreservesKernel.iso _ _)

/-- The pro-étale sheaves on `X` whose restriction along `j` vanishes, the sheaves supported on
the complement of `j`. -/
def supportedAway : ObjectProperty (Sheaf (ProEt.topology X) A) :=
  fun F ↦ IsZero ((j)^*[A].obj F)

/-- `Γ_Z`, as a functor to the sheaves supported on the complement `Z` of `j`. -/
noncomputable def sectionsWithSupportLift [IsOpenImmersion j] :
    Sheaf (ProEt.topology X) A ⥤ (supportedAway A j).FullSubcategory :=
  (supportedAway A j).lift (sectionsWithSupport A j) (isZero_upperStar_sectionsWithSupport A j)

/-- A morphism `F ⟶ N` from a sheaf supported on the complement of `j` is killed by the unit
`N ⟶ j_* j^* N`. -/
lemma comp_unit_app_eq_zero {F N : Sheaf (ProEt.topology X) A} (hF : supportedAway A j F)
    (f : F ⟶ N) : f ≫ (upperStarLowerStarAdjunction A j).unit.app N = 0 := by
  have h := (upperStarLowerStarAdjunction A j).unit.naturality f
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h
  rw [h, (((j)_*[A]).map_isZero hF).eq_of_tgt
    ((upperStarLowerStarAdjunction A j).unit.app F) 0, zero_comp]

/-- The inclusion of the sheaves supported on the complement of `j` is left adjoint to the
sheaf of sections with support `Γ_Z`: a morphism into `N` from a sheaf supported on the
complement factors uniquely through the kernel `Γ_Z N` of the unit of `j^* ⊣ j_*`. -/
noncomputable def supportedAwayιAdjunction [IsOpenImmersion j] :
    (supportedAway A j).ι ⊣ sectionsWithSupportLift A j :=
  Adjunction.mkOfHomEquiv
    { homEquiv F N :=
        { toFun f := ObjectProperty.homMk (kernel.lift _ f (comp_unit_app_eq_zero A j F.2 f))
          invFun g := g.hom ≫ kernel.ι _
          left_inv f := by simp
          right_inv g := by
            ext1
            exact equalizer.hom_ext (by simp) }
      homEquiv_naturality_left_symm _ _ := by simp
      homEquiv_naturality_right _ _ := by
        ext1
        exact equalizer.hom_ext (by simp [sectionsWithSupportLift, sectionsWithSupport]) }

end Definition

section Adjunction

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- `i_*`, as a functor to the sheaves supported on the complement `Z` of `j`. -/
noncomputable def lowerStarLift (hij : Disjoint (Set.range i.base) (Set.range j.base)) :
    Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R) ⥤
      (supportedAway (ModuleCat.{u + 1} R) j).FullSubcategory :=
  (supportedAway _ j).lift ((i)_*[ModuleCat.{u + 1} R])
    (isZero_upperStar_lowerStar_of_disjoint _ i j hij)

/-- The adjunction `i^* ⊣ i_*` restricted to the sheaves supported on the complement `Z` of
`j`. Its unit and counit are isomorphisms. -/
noncomputable def upperStarLowerStarLiftAdjunction
    (hij : Disjoint (Set.range i.base) (Set.range j.base)) :
    (supportedAway (ModuleCat.{u + 1} R) j).ι ⋙ (i)^*[ModuleCat.{u + 1} R] ⊣
      lowerStarLift i j hij :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        { toFun f := ObjectProperty.homMk
            ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).homEquiv _ _ f)
          invFun g := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).homEquiv _ _).symm
            g.hom
          left_inv f := by simp
          right_inv g := by
            ext1
            simp }
      homEquiv_naturality_left_symm _ _ := by
        simp [Adjunction.homEquiv_naturality_left_symm]
      homEquiv_naturality_right _ _ := by
        ext1
        simp [Adjunction.homEquiv_naturality_right, lowerStarLift] }

omit [IsClosedImmersion i] [QuasiCompact j] in
lemma upperStarLowerStarLiftAdjunction_unit_app_hom
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (F : (supportedAway (ModuleCat.{u + 1} R) j).FullSubcategory) :
    ((upperStarLowerStarLiftAdjunction i j hij).unit.app F).hom =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F.obj := by
  simp [upperStarLowerStarLiftAdjunction, Adjunction.homEquiv_unit]

omit [IsClosedImmersion i] [QuasiCompact j] in
lemma upperStarLowerStarLiftAdjunction_counit_app
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R)) :
    (upperStarLowerStarLiftAdjunction i j hij).counit.app M =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit.app M := by
  simp [upperStarLowerStarLiftAdjunction, Adjunction.homEquiv_counit]

/-- `i_*` is an equivalence onto the sheaves supported on the complement `Z` of `j`, with
inverse `i^*`. -/
noncomputable def lowerStarLiftEquivalence
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (supportedAway (ModuleCat.{u + 1} R) j).FullSubcategory ≌
      Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R) :=
  have : ∀ F, IsIso ((upperStarLowerStarLiftAdjunction (R := R) i j hij.disjoint).unit.app F) :=
    fun F ↦
    have := isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl i j hij F.obj F.2
    have : IsIso ((ObjectProperty.ι _).map
        ((upperStarLowerStarLiftAdjunction (R := R) i j hij.disjoint).unit.app F)) := by
      change IsIso ((upperStarLowerStarLiftAdjunction (R := R) i j hij.disjoint).unit.app F).hom
      rw [upperStarLowerStarLiftAdjunction_unit_app_hom]
      infer_instance
    isIso_of_fully_faithful (ObjectProperty.ι _) _
  have : ∀ M, IsIso ((upperStarLowerStarLiftAdjunction (R := R) i j hij.disjoint).counit.app M) :=
    fun M ↦ by
      rw [upperStarLowerStarLiftAdjunction_counit_app i j hij.disjoint M]
      infer_instance
  (upperStarLowerStarLiftAdjunction (R := R) i j hij.disjoint).toEquivalence

/-- The sheaf-level adjunction `i_* ⊣ i^!₀` of blueprint `lemma-local-cohomology-right-adjoint--1`,
for a closed immersion `i` with quasi-compact open complement `j`: the composite of the equivalence
between `Sh(Z)` and the sheaves supported on `Z`
(`AlgebraicGeometry.ProEtale.lowerStarLiftEquivalence`) and of the coreflection onto the
sheaves supported on `Z` given by the sections with support
(`AlgebraicGeometry.ProEtale.supportedAwayιAdjunction`). -/
noncomputable def lowerStarClosedUpperShriekAdjunction
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (i)_*[ModuleCat.{u + 1} R] ⊣ closedUpperShriek (ModuleCat.{u + 1} R) i j :=
  (((lowerStarLiftEquivalence i j hij).symm.toAdjunction.comp
    (supportedAwayιAdjunction (ModuleCat.{u + 1} R) j)).ofNatIsoLeft
      (Iso.refl _ : _ ≅ (i)_*[ModuleCat.{u + 1} R])).ofNatIsoRight
    (Iso.refl _ : _ ≅ closedUpperShriek (ModuleCat.{u + 1} R) i j)

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`: let `i : Z ⟶ X` be a closed immersion whose
open complement `j : U ⟶ X` is quasi-compact (for instance, `X` noetherian). On the unbounded
derived categories of pro-étale sheaves of modules, the direct image `Ri_*` has a right adjoint,
the right derived functor of the sheaf-level `i^!₀` of
`AlgebraicGeometry.ProEtale.closedUpperShriek`. No constructibility is assumed: the adjunction
holds on the whole derived categories.

The functor `i_*` is exact
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`), so `Ri_*` is `i_*`
applied termwise, and `i_*` is left adjoint to `i^!₀`
(`AlgebraicGeometry.ProEtale.lowerStarClosedUpperShriekAdjunction`), so
`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction` applies. -/
noncomputable def derivedLowerStarClosedUpperShriekAdjunction
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctor ⊣
      (closedUpperShriek (ModuleCat.{u + 1} R) i j).rightDerivedFunctor :=
  haveI := preservesFiniteColimits_lowerStar_of_isCompl (R := R) i j hij
  ((lowerStarClosedUpperShriekAdjunction i j hij).mapDerivedCategoryRightDerivedAdjunction
    ).ofNatIsoLeft ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctorIsoMapDerivedCategory.symm

omit [QuasiCompact j] in
/-- The direct image `Ri_*` along a closed immersion is fully faithful on the unbounded derived
categories of pro-étale sheaves of modules: `i_*` is fully faithful
(`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`) and preserves
K-injective complexes as a right adjoint of the exact `i^*`, and the right derived functor of a
fully faithful functor preserving K-injective complexes is fully faithful
(`CategoryTheory.Functor.full_rightDerivedFunctor`). -/
instance full_rightDerivedFunctor_lowerStar :
    ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctor.Full :=
  have : ((i)_*[ModuleCat.{u + 1} R]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).preservesKInjectiveComplexes
  inferInstance

omit [QuasiCompact j] in
instance faithful_rightDerivedFunctor_lowerStar :
    ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctor.Faithful :=
  have : ((i)_*[ModuleCat.{u + 1} R]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).preservesKInjectiveComplexes
  inferInstance

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`: let `i : Z ⟶ X` be a closed immersion whose
open complement `j` is quasi-compact (for instance, `X` noetherian), and let `Ri^!` be the right
adjoint of the direct image `Ri_*` on the unbounded derived categories of pro-étale sheaves of
modules (`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`). For every
`Q ∈ D(Z_proét)` the unit `Q ⟶ Ri^! Ri_* Q` is an isomorphism. No boundedness or
constructibility of `Q` is required.

The unit of an adjunction whose left adjoint is fully faithful is an isomorphism, and `Ri_*` is
fully faithful (`AlgebraicGeometry.ProEtale.full_rightDerivedFunctor_lowerStar`). -/
theorem isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (Q : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsIso ((derivedLowerStarClosedUpperShriekAdjunction i j hij).unit.app Q) :=
  inferInstance

end Adjunction

end ProEtale

end AlgebraicGeometry
