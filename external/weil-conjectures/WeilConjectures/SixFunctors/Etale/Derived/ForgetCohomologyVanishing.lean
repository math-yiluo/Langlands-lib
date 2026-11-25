/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Vanishing of cohomology of module sheaves via the underlying abelian sheaves

The cohomology of a sheaf of `Λ`-modules on `X_ét` is, as an abelian group, that of its
underlying abelian sheaf (Stacks 03FD). Hence `RΓ(X, G) = 0` in `D(Λ)` if and only if all the
abelian cohomology groups `H^q(X, G)` vanish (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`, forgetting `Λ`).

## Main statements

- `AlgebraicGeometry.Etale.isZero_rightDerivedGlobalSections_singleFunctor_iff`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1` (forgetting `Λ`, Stacks 03FD): the
derived global sections of a sheaf of `Λ`-modules vanish if and only if the abelian cohomology of
the underlying abelian sheaf vanishes in every degree. -/
theorem isZero_rightDerivedGlobalSections_singleFunctor_iff (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) ↔
      ∀ q : ℕ, Subsingleton (Sheaf.H ((sheafForget₂ Λ X).obj G) q) := by
  have hq (q : ℕ) : IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj G)) ↔
      Subsingleton (Sheaf.H ((sheafForget₂ Λ X).obj G) q) := by
    obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ q
    obtain ⟨e'⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
    refine ModuleCat.isZero_iff_subsingleton.trans ((AddCommGrpCat.isZero_iff_subsingleton
      (G := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj _)).symm.trans
      (Iff.trans ?_ (AddCommGrpCat.isZero_iff_subsingleton
        (G := (Sheaf.functorH X.smallEtaleTopology q).obj ((sheafForget₂ Λ X).obj G)))))
    exact ⟨fun h ↦ h.of_iso (e'.app _ ≪≫ (e.app G).symm),
      fun h ↦ h.of_iso (e.app G ≪≫ (e'.app _).symm)⟩
  rw [DerivedCategory.isZero_iff]
  refine ⟨fun h q ↦ (hq q).1 (h q), fun h n ↦ ?_⟩
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact (hq q).2 (h q)
  have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) G
  exact DerivedCategory.isZero_of_isGE
    ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj _) 0 n hn

end AlgebraicGeometry.Etale
