/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Constructible sheaves are compact in `Loc(Dᵇc)`, given the ind-constructible heart

Let `R` be a commutative ring object of sheaves on `X_proét`. Write `IndCons(X, R)` for the
filtered colimits of constructible sheaves of `R`-modules (blueprint
`proposition-ind-constructible-sheaves`, `CategoryTheory.ObjectProperty.ind` of
`IsConstructibleModuleObject R`), and `Dic(X, R)` for the complexes with cohomology sheaves in
`IndCons(X, R)` (blueprint `corollary-ambient-ind-derived`).

We isolate the inputs of blueprints `theorem-compactness-rational-coefficients` and
`proposition-compactness-proper-direct-image--1` on the coefficient ring:

* `AlgebraicGeometry.ProEtale.IsIndConstructibleHeart R` (blueprint
`proposition-ind-constructible-sheaves` (2),
  `proposition-compactness-proper-direct-image--1` (1)): `IndCons(X, R)` is closed in the category
  of `R`-modules under kernels, cokernels, extensions and direct sums;
* `AlgebraicGeometry.ProEtale.HasIndConstructibleExtBound R` (blueprint `corollary-ind-heart-b`):
  for a constructible sheaf `C` there is `d` with `Ext^q(C, B) = 0` for `q > d` and all `B` in
  `IndCons(X, R)`, and `Ext^q(C, -)` commutes with direct sums of objects of `IndCons(X, R)`;
* exactness of countable products of `R`-modules (blueprint `proposition-exact-products`), which
makes
  `D(X_proét, R)` left complete.

Given these, `Dic(X, R)` is a localizing subcategory containing `Loc(Dᵇc(X, R))`
(`AlgebraicGeometry.ProEtale.localizingClosure_boundedConstructible_le`), and every
constructible sheaf placed in degree `0` is compact in `Loc(Dᵇc(X, R))`
(`AlgebraicGeometry.ProEtale.isCompactObj_singleFunctor_of_isIndConstructibleHeart`): this is the
abstract finite-window argument `DerivedCategory.compactFor_of_homologyProperty`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory ZeroObject

namespace CategoryTheory

/-- In a category with coproducts, an object of the localizing closure `Loc(B)` of `B` is
compact in `Loc(B)` as soon as morphisms out of it commute with the direct sums, computed in the
ambient category, of families of objects of `Loc(B)`. -/
lemma ObjectProperty.isCompactObj_of_compactFor {D : Type*} [Category.{u'} D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    [IsTriangulated D] [HasCoproducts.{u'} D] (B : ObjectProperty D)
    (C : B.localizingClosure.FullSubcategory)
    (h : ∀ (J : Type u') (Y : J → B.localizingClosure.FullSubcategory),
      CompactFor C.obj fun j ↦ (Y j).obj) :
    BrownRepresentability.IsCompactObj C := by
  intro J Y c hc f
  have hc' : IsColimit (Cofan.mk c.pt.obj fun j ↦ (c.inj j).hom) :=
    isColimitCofanMkObjOfIsColimit B.localizingClosure.ι Y c.inj
      (hc.ofIsoColimit (Cofan.ext (Iso.refl _) (by simp)))
  obtain ⟨S, g, hg⟩ := (h J Y).of_isColimit hc' f.hom
  refine ⟨S, fun j ↦ ObjectProperty.homMk (g j), ?_⟩
  apply B.localizingClosure.ι.map_injective
  rw [Functor.map_sum]
  simpa using hg

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]


/-- The category of `R`-modules has direct sums. -/
instance hasColimitsOfShape_discrete_mod (J : Type (u + 1)) :
    HasColimitsOfShape (Discrete J) (Mod (Sheaf (Scheme.ProEt.topology X) A) R) :=
  have : HasColimitsOfSize.{u + 1, u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) A) R) :=
    IsGrothendieckAbelian.hasColimits _
  HasColimitsOfSize.has_colimits_of_shape _

/-- The derived category `D(X_proét, R)` has direct sums. -/
instance hasColimitsOfShape_discrete_derivedCategory_mod (J : Type (u + 1)) :
    HasColimitsOfShape (Discrete J)
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.hasColimitsOfShape_discrete J
/-- Blueprint `proposition-ind-constructible-sheaves`: the ind-constructible sheaves of `R`-modules,
the filtered colimits of constructible sheaves. -/
abbrev IsIndConstructibleModuleObject :
    ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) A) R) :=
  ObjectProperty.ind.{u + 1} (IsConstructibleModuleObject R)

/-- Blueprint `proposition-ind-constructible-sheaves` (2) (and
`proposition-compactness-proper-direct-image--1` (1) for `𝒪_E`): the ind-constructible sheaves are
closed under kernels, cokernels, extensions and direct sums. -/
structure IsIndConstructibleHeart : Prop where
  isClosedUnderKernels : (IsIndConstructibleModuleObject R).IsClosedUnderKernels
  isClosedUnderCokernels : (IsIndConstructibleModuleObject R).IsClosedUnderCokernels
  isClosedUnderExtensions : (IsIndConstructibleModuleObject R).IsClosedUnderExtensions
  isClosedUnderColimitsOfShape_discrete (J : Type (u + 1)) :
    (IsIndConstructibleModuleObject R).IsClosedUnderColimitsOfShape (Discrete J)

/-- Blueprint `corollary-ind-heart-b` (and `proposition-compactness-proper-direct-image--1` (1) for
`𝒪_E`): for a constructible sheaf `C`, `Ext^q(C, B) = Hom(C, B[q]) = 0` for `q` large and all
ind-constructible `B`, and `Ext^q(C, -)` commutes with direct sums of ind-constructible sheaves. -/
structure HasIndConstructibleExtBound : Prop where
  exists_eq_zero (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R)
    (hM : IsConstructibleModuleObject R M) :
    ∃ N : ℤ, ∀ B, IsIndConstructibleModuleObject R B →
      ∀ n ≤ N, ∀ f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (DerivedCategory.singleFunctor _ n).obj B, f = 0
  compactFor (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R)
    (hM : IsConstructibleModuleObject R M) (n : ℤ) {J : Type (u + 1)}
    (B : J → Mod (Sheaf (Scheme.ProEt.topology X) A) R)
    (hB : ∀ j, IsIndConstructibleModuleObject R (B j)) :
    CompactFor ((DerivedCategory.singleFunctor _ 0).obj M)
      fun j ↦ (DerivedCategory.singleFunctor _ n).obj (B j)

/-- Blueprint `lemma-uniform-ext-bound`: for a constructible sheaf `C` there is `d` with
`Ext^q(C, B) = Hom(C, B[q]) = 0` for `q > d` and all constructible `B`. -/
def HasUniformConstructibleExtBound : Prop :=
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) A) R, IsConstructibleModuleObject R M →
    ∃ N : ℤ, ∀ B, IsConstructibleModuleObject R B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (DerivedCategory.singleFunctor _ n).obj B,
        f = 0

/-- Blueprint `lemma-continuity-ext-out-constructible-complex--1` (1) (surjectivity, for filtered
diagrams of sheaves in degree `0`): for a constructible sheaf `C`, every morphism `C ⟶ B[n]` to a
filtered colimit `B = colim Bᵢ` of sheaves of `R`-modules factors through some `Bᵢ[n]`. -/
def HasConstructibleExtContinuity : Prop :=
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) A) R, IsConstructibleModuleObject R M →
    DerivedCategory.HomFactorsThroughFilteredColimits.{u + 1}
      ((DerivedCategory.singleFunctor _ 0).obj M)

variable {R} in
/-- Blueprint `corollary-ind-heart-b` from `lemma-continuity-ext-out-constructible-complex--1` and
`lemma-uniform-ext-bound`: an ind-constructible sheaf is a filtered colimit of
constructible ones, and a direct sum is the filtered colimit of its finite subsums
(`corollary-ind-heart-b--1`, `corollary-ind-heart-b--2`). -/
lemma HasIndConstructibleExtBound.of_continuity (h₁ : HasConstructibleExtContinuity R)
    (h₂ : HasUniformConstructibleExtBound R) : HasIndConstructibleExtBound R where
  exists_eq_zero M hM := by
    obtain ⟨N, hN⟩ := h₂ M hM
    exact ⟨N, DerivedCategory.eq_zero_of_ind _ (h₁ M hM) N hN⟩
  compactFor M hM n J B _ :=
    have : HasColimitsOfSize.{u + 1, u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) A) R) :=
      IsGrothendieckAbelian.hasColimits _
    DerivedCategory.compactFor_singleFunctor_of_homFactorsThroughFilteredColimits (h₁ M hM) n B

/-- The zero module object is ind-constructible. -/
instance : (IsIndConstructibleModuleObject R).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    ObjectProperty.le_ind _ _ (isConstructibleModuleObject_of_isZero R (isZero_zero _))⟩

variable {R} in
/-- Blueprint `corollary-ambient-ind-derived` (3): if `IndCons(X, R)` is closed under kernels,
cokernels, extensions and direct sums, the complexes with ind-constructible cohomology form a
localizing subcategory, which contains the bounded constructible complexes, hence their
localizing closure. -/
lemma localizingClosure_boundedConstructible_le [IsCommMonObj R] (hR : IsIndConstructibleHeart R) :
    (boundedConstructible R).localizingClosure ≤
      DerivedCategory.homologyProperty (IsIndConstructibleModuleObject R) := by
  have := hR.isClosedUnderKernels
  have := hR.isClosedUnderCokernels
  have := hR.isClosedUnderExtensions
  have := hR.isClosedUnderColimitsOfShape_discrete
  have : (DerivedCategory.homologyProperty (IsIndConstructibleModuleObject R)).IsLocalizing :=
    { isClosedUnderColimitsOfShape_discrete := fun J ↦ ⟨fun _ ⟨h⟩ ↦
        (DerivedCategory.homologyProperty (IsIndConstructibleModuleObject R)).prop_of_iso
          (h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
            (HasColimit.isoOfNatIso Discrete.natIsoFunctor) ≪≫ Iso.refl _).symm
          (DerivedCategory.homologyProperty_sigma _ _ fun j ↦ h.prop_diag_obj ⟨j⟩)⟩ }
  exact ObjectProperty.localizingClosure_le fun K hK n ↦
    ObjectProperty.le_ind _ _ (hK.2 n)

variable {R} in
/-- Blueprints `theorem-compactness-rational-coefficients` and
`proposition-compactness-proper-direct-image--1` (3), given the inputs on the ind-constructible
heart: a constructible sheaf `M` placed in degree `0` is compact in `Loc(Dᵇc(X, R))`. Morphisms out
of `M` into objects of `Loc(Dᵇc(X, R)) ⊆ Dic(X, R)`
only see a finite window of degrees (`lemma-reduction-finitely-many-degrees`, using left
completeness), on which they commute with direct sums by induction on the amplitude. -/
theorem isCompactObj_singleFunctor_of_isIndConstructibleHeart [IsCommMonObj R]
    [HasExactLimitsOfShape (Discrete ℕ) (Mod (Sheaf (Scheme.ProEt.topology X) A) R)]
    (hR : IsIndConstructibleHeart R) (hR' : HasIndConstructibleExtBound R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) (hM : IsConstructibleModuleObject R M)
    (hL : (boundedConstructible R).localizingClosure ((DerivedCategory.singleFunctor _ 0).obj M)) :
    BrownRepresentability.IsCompactObj
      (⟨(DerivedCategory.singleFunctor _ 0).obj M, hL⟩ :
        (boundedConstructible R).localizingClosure.FullSubcategory) := by
  have := hR.isClosedUnderColimitsOfShape_discrete
  obtain ⟨N, hN⟩ := hR'.exists_eq_zero M hM
  refine ObjectProperty.isCompactObj_of_compactFor _ _ fun J Y ↦ ?_
  exact DerivedCategory.compactFor_of_homologyProperty 0 N hN
    (fun n B hB ↦ hR'.compactFor M hM n B hB) _
    fun j ↦ localizingClosure_boundedConstructible_le hR _ (Y j).property

end AlgebraicGeometry.ProEtale
