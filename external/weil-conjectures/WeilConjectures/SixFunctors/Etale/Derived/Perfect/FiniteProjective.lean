/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect

/-!
# Finite projective étale sheaves of modules are dualizable

A sheaf `P` of `Λ`-modules on the small étale site of `X` is a *finite projective
`Λ_X`-module* if, étale locally on `X`, it is a direct summand of a finite free module
`Λ_U^{⊕m}` (`AlgebraicGeometry.Etale.IsFiniteProjectiveSheaf`). Placed in degree `0` it is
perfect on the coefficient site, hence dualizable in `D(X_ét, Λ)`. Consequently (blueprint
`theorem-poincare-duality--5`) the canonical map `P^∨ ⊗ᴸ N ⟶ RHom(P, N)` is an
isomorphism for every `N`
(`AlgebraicGeometry.Etale.DerivedCategory.isIso_coefficientDualTensorToDerivedHom`) and the
biduality map `P ⟶ P^∨∨` is an isomorphism
(`AlgebraicGeometry.Etale.DerivedCategory.isIso_coefficientDualDoubleDual_app`).

## Implementation notes

The blueprint works on the small pro-étale site; as for
`AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect`, the statement is made here on the small
étale site of the étale model.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- A sheaf `P` of `Λ`-modules on `X_ét` is a *finite projective `Λ_X`-module* if there is an
étale cover `{uᵢ : Uᵢ ⟶ X}` such that each restriction `uᵢ^* P` is a direct summand (a retract)
of a finite free module, the constant sheaf `(Λ^m)_{Uᵢ}`. -/
def IsFiniteProjectiveSheaf (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀, ∃ m : ℕ,
    Nonempty (Retract ((𝒰.f i)^*[ModuleCat.{u + 1} Λ].obj P)
      ((constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin m → Λ))))

namespace IsFiniteProjectiveSheaf

variable {P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- A finite projective `Λ_X`-module placed in degree `0` is perfect on the coefficient site:
on each member `u` of a trivializing cover, `Lu^* P ≅ u^* P` is the single complex on a
direct summand of `(Λ^m)_U`. -/
theorem isSitePerfect (hP : IsFiniteProjectiveSheaf P) :
    DerivedCategory.IsSitePerfect ((DerivedCategory.singleFunctor _ 0).obj P) := by
  obtain ⟨𝒰, h⟩ := hP
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨m, ⟨r⟩⟩ := h i
  let F := (𝒰.f i)^*[ModuleCat.{u + 1} Λ].obj P
  refine ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F, 0, 0, inferInstance,
    inferInstance, fun n ↦ ?_, ⟨(singleFunctorCompLeftDerivedUpperStarIso _ (𝒰.f i)).app P ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app F⟩⟩
  by_cases hn : n = 0
  · subst hn
    exact ⟨m, ⟨(Retract.ofIso (HomologicalComplex.singleObjXSelf _ 0 F)).trans r⟩⟩
  · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn
    exact ⟨0, ⟨{ i := 0, r := 0, retract := hz.eq_of_src _ _ }⟩⟩

/-- A finite projective `Λ_X`-module placed in degree `0` is dualizable in `D(X_ét, Λ)`. -/
theorem isDualizable (hP : IsFiniteProjectiveSheaf P) :
    DerivedCategory.IsDualizableEtale ((DerivedCategory.singleFunctor _ 0).obj P) :=
  hP.isSitePerfect.isDualizable

end IsFiniteProjectiveSheaf

end Etale

end AlgebraicGeometry
