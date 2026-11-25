/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.ConstructibleSheaf.FiniteMorphism
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Constructibility of direct images along finite surjections

Let `π : Y ⟶ X` be finite and surjective. This file proves that the constructibility of the
direct images `Rᵠ(π ≫ f)_*` implies that of the `Rᵠf_*`
(`proposition-proper-direct-image-finite-coefficients`), and the comparison of the direct images of
a constant sheaf along a finite modification
(`proposition-proper-direct-image-finite-coefficients`).

The cancellation argument embeds a constructible sheaf `Q` on `X` into `π_* π^* Q` (the unit
of `π^* ⊣ π_*` is a monomorphism for surjective `π`) and applies the resolution principle
`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_exists_mono`; the direct image `π_*` is
exact, so that `Rf_*((π_* π^* Q)[0]) = R(π ≫ f)_*((π^* Q)[0])`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Direct images along a finite morphism.** For a finite `π : Y ⟶ X`, the derived direct
image `Rf_*` of the direct image `π_* G` of a sheaf `G` placed in degree `0` is
`R(π ≫ f)_*(G[0])`, since `π_*` is exact. -/
noncomputable def rightDerivedLowerStarSingleLowerStarIso {X Y S : Scheme.{u}} (π : Y ⟶ X)
    [IsFinite π] (f : X ⟶ S) (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj ((π)_*[ModuleCat.{u + 1} Λ].obj G))
      ≅ (R((π ≫ f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj G) :=
  (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((((π)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G).symm ≪≫
    (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((rightDerivedFunctorLowerStarIsoMapDerivedCategory _ π).app _).symm ≪≫
    (rightDerivedLowerStarComp _ π f).app _

variable [Finite Λ]

/-- **Cancellation of a finite surjection, given that `π_*` preserves constructibility.** Let
`π : Y ⟶ X` be finite and surjective, and suppose that `π_*` sends constructible sheaves to
constructible sheaves. If `𝒞(π ≫ f)` holds, then `𝒞(f)` holds. -/
theorem HasConstructibleDirectImages.of_comp_of_isFinite_of_isConstructibleSheaf
    {X Y S : Scheme.{u}} (f : X ⟶ S) (π : Y ⟶ X) [IsFinite π]
    (hπ : Function.Surjective π.base)
    (hc : ∀ G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf G →
      IsConstructibleSheaf ((π)_*[ModuleCat.{u + 1} Λ].obj G))
    (h : HasConstructibleDirectImages Λ (π ≫ f)) : HasConstructibleDirectImages Λ f := by
  refine hasConstructibleDirectImages_of_exists_mono f fun Q hQ ↦ ?_
  have hG : IsConstructibleSheaf ((π)^*[ModuleCat.{u + 1} Λ].obj Q) :=
    IsConstructibleSheaf.upperStar π Q
  exact ⟨_, _, mono_unit_app_of_surjective Λ π hπ Q, hc _ hG,
    (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).prop_of_iso
      (rightDerivedLowerStarSingleLowerStarIso π f _).symm (h _ hG)⟩

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Constructibility descends
through a finite surjection.

Let `f : X ⟶ S` be a morphism with `X` of finite type over a field `k`, and let `π : Y ⟶ X` be
finite and surjective. If `𝒞(π ≫ f)` holds, then `𝒞(f)` holds. Here `Λ` is a finite ring. The
blueprint assumes `S` of finite type over `k` as well; this is not needed. -/
theorem HasConstructibleDirectImages.of_comp_of_isFinite {k : Type u} [Field k]
    {X Y S : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (f : X ⟶ S) (π : Y ⟶ X) [IsFinite π] [Surjective π]
    (h : HasConstructibleDirectImages Λ (π ≫ f)) : HasConstructibleDirectImages Λ f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  exact of_comp_of_isFinite_of_isConstructibleSheaf f π π.surjective
    (fun G _ ↦ Scheme.IsConstructibleSheaf.lowerStar_of_isFinite π G) h

end Etale

end AlgebraicGeometry
