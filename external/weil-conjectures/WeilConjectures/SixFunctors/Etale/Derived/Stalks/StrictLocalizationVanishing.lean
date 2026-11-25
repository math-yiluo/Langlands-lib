/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic
public import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
public import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Vanishing of stalks of direct images via the strict localization

Let `f : U ⟶ Z` be quasi-compact and quasi-separated, `s : Spec Ω ⟶ Z` a geometric point with
`Ω` algebraically closed, `S = Z_(s)` the strict localization and `p : U ×_Z S ⟶ U` the
projection. For a sheaf `F` of `Λ`-modules on `U_ét`, the stalk formula
`(R^q f_* F)_s ≅ H^q(U ×_Z S, p^* F)` (Stacks 03Q9,
`AlgebraicGeometry.Etale.strictHenselizationStalkFormula`), applied to the underlying abelian
sheaf, shows: if the abelian cohomology `H^q(U ×_Z S, p^* F)` vanishes in every degree, then the
geometric stalk `(Rf_* F)_s = Ls^* Rf_* F` vanishes in `D(Λ)`
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`, stalk formula and forgetting `Λ`).

## Main statements

- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_rightDerivedLowerStar_of_subsingleton_sheafH`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Stacks 03Q9, after forgetting `Λ`: if the abelian cohomology of `p^* F` on `U ×_Z S`
vanishes in degree `q`, `S` the strict localization of `Z` at `s`, then the stalk at `s` of
the higher direct image `R^q f_* F` vanishes. -/
theorem isZero_sheafFiber_higherDirectImage_of_subsingleton_sheafH
    {U Z : Scheme.{u}} (f : U ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Z)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (hF : Subsingleton (Sheaf.H ((sheafForget₂ Λ _).obj
      ((pullback.fst f (Scheme.strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)) q)) :
    IsZero (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (higherDirectImage Λ f q F)) := by
  let : PreservesColimitsOfSize.{u, u} (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  let p := pullback.fst f (Scheme.strictLocalizationToBase s)
  obtain ⟨e₁⟩ := nonempty_higherDirectImage_forget_iso Λ f q F
  obtain ⟨r, -, hr⟩ := unrestricted_strictHenselization_stalk f s ((sheafForget₂ Λ _).obj F) q
  obtain ⟨e₂⟩ := Scheme.nonempty_sheafH_extDerivedIso (pullback f
    (Scheme.strictLocalizationToBase s)) q
  let E := (Scheme.pointSmallEtale s).sheafFiberCompIso.{u, u, u + 1, u + 1, u + 1, u + 2, u + 2}
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let e : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      ((Scheme.pointSmallEtale s).sheafFiber.obj (higherDirectImage Λ f q F)) ≅
      (Sheaf.functorH.{u + 1} _ q).obj
        ((sheafForget₂ Λ _).obj ((p)^*[ModuleCat.{u + 1} Λ].obj F)) :=
    (E.app _).symm ≪≫ (Scheme.pointSmallEtale s).sheafFiber.mapIso e₁ ≪≫
      asIso (r ≫ strictHenselizationCohomologyComparison s f ((sheafForget₂ Λ _).obj F) q) ≪≫
      (Etale.cohomology AddCommGrpCat.{u + 1} _ (q : ℤ)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          (asIso (upperStarForget₂Comparison Λ p F))) ≪≫ (e₂.app _).symm
  have h : IsZero ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      ((Scheme.pointSmallEtale s).sheafFiber.obj (higherDirectImage Λ f q F))) :=
    (@AddCommGrpCat.isZero_of_subsingleton _ hF).of_iso e
  rw [AddCommGrpCat.isZero_iff_subsingleton] at h
  exact ModuleCat.isZero_of_subsingleton _

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1` (stalk formula): if the abelian
étale cohomology of the pullback `p^* F` of a sheaf of `Λ`-modules to `U ×_Z S`, `S` the strict
localization of `Z` at `s`, vanishes in every degree, then the geometric stalk at `s` of
`Rf_* F` vanishes. -/
theorem isZero_leftDerivedUpperStar_rightDerivedLowerStar_of_subsingleton_sheafH
    {U Z : Scheme.{u}} (f : U ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Z)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ q : ℕ, Subsingleton (Sheaf.H ((sheafForget₂ Λ _).obj
      ((pullback.fst f (Scheme.strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)) q)) :
    IsZero ((L((s)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  rw [isZero_iff_forall_isZero_homology Λ]
  intro n
  refine Scheme.isZero_of_subsingleton_sections_of_isSepClosed _ ?_
  rw [← ModuleCat.isZero_iff_subsingleton]
  refine IsZero.of_iso ?_ (sheafFiberHomologyIso Λ s _ n).symm
  obtain ⟨q, rfl⟩ | hn : (∃ q : ℕ, n = q) ∨ n < 0 := by
    rcases le_or_gt 0 n with h | h
    · exact Or.inl ⟨n.toNat, (Int.toNat_of_nonneg h).symm⟩
    · exact Or.inr h
  · exact (isZero_sheafFiber_higherDirectImage_of_subsingleton_sheafH f s F q (hF q)).of_iso
      ((Scheme.pointSmallEtale s).sheafFiber.mapIso
        (Functor.homologyRightDerivedFunctorObjSingleFunctorIso _ F q ≪≫
          (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso _ F q).symm))
  · have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor (f)_*[ModuleCat.{u + 1} Λ] F
    exact Functor.map_isZero _ (DerivedCategory.isZero_of_isGE _ 0 n hn)

end AlgebraicGeometry.Etale
