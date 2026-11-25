/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# The heart hypotheses for the derived direct image of module objects

Let `Λ` be a commutative condensed ring, flat over `ℤ`, and `f : X ⟶ Y` a quasi-compact
quasi-separated morphism of schemes. We show that the derived direct image `Rf_*` of module
objects over `Λ` commutes with direct sums of module objects placed in degree `0` (blueprint
`corollary-continuity-cohomology`), and that a bound `Rf_*(N[0]) ∈ D^{≤ d}` for the objects `N` of a
class `P` extends to filtered colimits of objects of `P`. Both follow from the continuity of the
higher direct images of abelian sheaves
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`), the higher direct
images of module objects being computed on the underlying abelian sheaves.

We deduce the hypotheses `ProperLowerStarHeartHypotheses` from the ind-constructible heart and a
uniform bound on constructible module objects (blueprints `lemma-uniform-bound-proper-direct-image`,
`proposition-compactness-proper-direct-image--2` (1), formal part).

## Main results

All in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`:

* `isIso_sigmaComparison_rightDerivedLowerStar_singleFunctor`:
  `Rf_*` commutes with direct sums of module objects placed in degree `0`.
* `isLE_rightDerivedLowerStar_singleFunctor_of_ind`:
  degree bounds for `Rf_*` pass to filtered colimits.
* `properLowerStarHeartHypotheses_of_isIndConstructibleHeart`:
  the heart hypotheses follow from the ind-constructible heart and a uniform bound.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace DerivedCategory

variable {A : Type*} [Category* A] {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] {J : Type*} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) (DerivedCategory C)]

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions D] [HasColimitsOfShape (Discrete J) D]
  [HasExactColimitsOfShape (Discrete J) D] [HasColimitsOfShape (Discrete J) (DerivedCategory D)]
  [EnoughInjectives C]

/-- The total right derived functor `RG` commutes with a coproduct of objects placed in degree
`0` as soon as all the higher derived functors `RᵠG` commute with it. -/
lemma isIso_sigmaComparison_rightDerivedFunctor_singleFunctor (G : C ⥤ D) [G.Additive]
    (X : J → C) (h : ∀ q : ℕ, IsIso (sigmaComparison (G.rightDerived q) X)) :
    IsIso (sigmaComparison G.rightDerivedFunctor fun j ↦ (singleFunctor C 0).obj (X j)) := by
  have h' : IsIso (sigmaComparison (singleFunctor C 0 ⋙ G.rightDerivedFunctor) X) := by
    rw [isIso_sigmaComparison_iff]
    intro n
    rcases lt_or_ge n 0 with hn | hn
    · exact isIso_sigmaComparison_of_isZero _ _ fun Y ↦
        have := G.isGE_rightDerivedFunctor_obj_singleFunctor Y
        isZero_of_isGE (G.rightDerivedFunctor.obj ((singleFunctor C 0).obj Y)) 0 n hn
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      have := h q
      exact CategoryTheory.Limits.isIso_sigmaComparison_of_natIso
        (G.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso q).symm X
  rwa [sigmaComparison_comp, isIso_comp_right_iff] at h'

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Forget

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

omit [IsCommMonObj Λ] in
/-- If `Λ_X` is flat, the higher direct images of a module object are computed on its underlying
abelian sheaf: the base change morphism `(Rᵠf_* M)_ab ⟶ Rᵠf_*(M_ab)` is an isomorphism. -/
instance isIso_rightDerivedBaseChange_lowerStarForgetIso (q : ℕ) :
    IsIso (Functor.rightDerivedBaseChange (lowerStarForgetIso Λ f).inv q) := by
  rw [show (lowerStarForgetIso Λ f).inv = (Iso.refl _ :
    (f)_*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y) ≅
      Mod.forget (condensedRingObj Λ X) ⋙ (f)_*[Ab.{u + 1}]).hom from rfl]
  rw [NatTrans.isIso_iff_isIso_app]
  intro G
  rw [Functor.rightDerivedBaseChange_app]
  have := isIso_rightDerivedLowerStarPlusForget Λ f
  have : IsIso ((rightDerivedLowerStarPlusForget Λ f).app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) := inferInstance
  unfold rightDerivedLowerStarPlusForget at this
  infer_instance

omit [IsCommMonObj Λ] in
/-- If `Λ_X` is flat, the higher direct images of module objects preserve the colimits that the
higher direct images of abelian sheaves preserve. -/
lemma preservesColimitsOfShape_rightDerived_lowerStar_of_forget (K : Type (u + 1))
    [SmallCategory K] (q : ℕ)
    [PreservesColimitsOfShape K (((f)_*[Ab.{u + 1}]).rightDerived q)] :
    PreservesColimitsOfShape K (((f)_*⟦Λ⟧).rightDerived q) := by
  have : PreservesColimitsOfShape K
      (((f)_*⟦Λ⟧).rightDerived q ⋙ Mod.forget (condensedRingObj Λ Y)) :=
    preservesColimitsOfShape_of_natIso
      (asIso (Functor.rightDerivedBaseChange (lowerStarForgetIso Λ f).inv q)).symm
  have : ReflectsColimitsOfShape K
      (Mod.forget (D := Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (Mod.forget (D := Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))

variable [QuasiCompact f] [QuasiSeparated f]

/-- For a quasi-compact quasi-separated morphism `f`, the higher direct images of abelian sheaves
commute with direct sums indexed by `Type (u + 1)`. -/
lemma preservesColimitsOfShape_discrete_rightDerived_lowerStar_ab (B : Type (u + 1)) (q : ℕ) :
    PreservesColimitsOfShape (Discrete B) (((f)_*[Ab.{u + 1}]).rightDerived q) :=
  have := preservesColimitsOfShape_rightDerived_lowerStar f (Finset (Discrete B)) q
  preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts _

omit [IsCommMonObj Λ] in
/-- For a quasi-compact quasi-separated morphism `f`, `Rf_*` commutes with direct sums of module
objects placed in degree `0` (blueprint `corollary-continuity-cohomology`). -/
theorem isIso_sigmaComparison_rightDerivedLowerStar_singleFunctor (J : Type (u + 1))
    (N : J → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso (sigmaComparison R((f)_*⟦Λ⟧) fun j ↦ (DerivedCategory.singleFunctor _ 0).obj (N j)) :=
  DerivedCategory.isIso_sigmaComparison_rightDerivedFunctor_singleFunctor _ N fun q ↦
    have := preservesColimitsOfShape_discrete_rightDerived_lowerStar_ab f J q
    have := preservesColimitsOfShape_rightDerived_lowerStar_of_forget Λ f (Discrete J) q
    inferInstance

omit [IsCommMonObj Λ] in
/-- If `Rf_*` sends the objects of `P`, placed in degree `0`, into degrees `≤ d`, it does so for
the filtered colimits of objects of `P`. -/
theorem isLE_rightDerivedLowerStar_singleFunctor_of_ind
    (P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (d : ℤ)
    (hP : ∀ N, P N → (R((f)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE d)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : ObjectProperty.ind.{u + 1} P M) :
    (R((f)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d := by
  obtain ⟨K, _, _, pres, hK⟩ := hM
  rw [DerivedCategory.isLE_iff]
  intro n hn
  rcases lt_or_ge n 0 with hn' | hn'
  · have := ((f)_*⟦Λ⟧).isGE_rightDerivedFunctor_obj_singleFunctor M
    exact DerivedCategory.isZero_of_isGE _ 0 n hn'
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn'
  have := preservesColimitsOfShape_rightDerived_lowerStar f K q
  have := preservesColimitsOfShape_rightDerived_lowerStar_of_forget Λ f K q
  refine IsZero.of_iso ?_ (((f)_*⟦Λ⟧).homologyRightDerivedFunctorObjSingleFunctorIso M q)
  refine (isColimitOfPreserves (((f)_*⟦Λ⟧).rightDerived q) pres.isColimit).isZero_pt
    (Functor.isZero _ fun i ↦ ?_)
  have := hP _ (hK i)
  exact (DerivedCategory.isZero_of_isLE _ d q hn).of_iso
    (((f)_*⟦Λ⟧).homologyRightDerivedFunctorObjSingleFunctorIso (pres.diag.obj i) q).symm

end Forget

omit [IsCommMonObj Λ] in
/-- Blueprints `lemma-uniform-bound-proper-direct-image` /
`proposition-compactness-proper-direct-image--2` (1), formal part: if `Λ_Z` is flat, the heart
hypotheses for a quasi-compact quasi-separated `p` follow from the ind-constructible heart and a
uniform bound on constructible module objects. -/
theorem properLowerStarHeartHypotheses_of_isIndConstructibleHeart {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p] [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ Z))]
    (hR : IsIndConstructibleHeart (condensedRingObj Λ Z)) (d : ℤ)
    (hd : ∀ N, IsConstructibleModuleObject (condensedRingObj Λ Z) N →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE d) :
    ProperLowerStarHeartHypotheses Λ p :=
  ⟨⟨d, fun _ hM ↦ isLE_rightDerivedLowerStar_singleFunctor_of_ind Λ p _ d hd
      (hM _ (ObjectProperty.le_ind.{u + 1} _) inferInstance hR.isClosedUnderKernels
        hR.isClosedUnderCokernels hR.isClosedUnderExtensions
        hR.isClosedUnderColimitsOfShape_discrete)⟩,
    fun J N _ ↦ isIso_sigmaComparison_rightDerivedLowerStar_singleFunctor Λ p J N⟩

end AlgebraicGeometry.ProEtale.CondensedRing
