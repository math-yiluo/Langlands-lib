/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProperNoetherianApproximation

/-!
# Proper direct images over a noetherian base

Let `k` be a field, `Λ` a finite ring killed by an integer invertible in `k`, `S` a noetherian
`k`-scheme and `b : Y ⟶ S` a proper morphism. The derived direct image `Rb_*` preserves bounded
constructible complexes of étale sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`,
blueprint `proposition-proper-direct-image-finite-coefficients--1`): this is the finiteness theorem
for proper morphisms (SGA 4, Exposé XIV, Théorème 1.1) together with the vanishing of `Rᵠb_*` above
twice the dimension of the geometric fibres (Stacks, Tag 095U).

For `S` of finite type over a field this is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper`. In general, the
constructibility of the higher direct images is reduced to that case by Noetherian approximation
(`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isProper_of_isNoetherian`), the
dimensions of the fibres of `b` are bounded
(`AlgebraicGeometry.exists_topologicalKrullDim_pullback_le_of_isProper_of_isNoetherian`), so
that the vanishing holds by
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_of_isProper`,
and we conclude by the dévissage
`AlgebraicGeometry.Etale.boundedConstructible_obj_of_forall_singleFunctor`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `proposition-proper-direct-image-finite-coefficients--1`: for a proper morphism
`b : Y ⟶ S` to a noetherian scheme over a field `k` in which the exponent of the finite ring `Λ` is
invertible, `Rb_*` maps
bounded constructible complexes of étale sheaves of `Λ`-modules to bounded constructible complexes
(SGA 4, Exposé XIV, Théorème 1.1; Stacks, Tag 095U). -/
theorem boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian {k : Type u}
    [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {Y S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [IsNoetherian S] (b : Y ⟶ S) [IsProper b]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_pullback_le_of_isProper_of_isNoetherian aS b
  have hb := hasConstructibleDirectImages_of_isProper_of_isNoetherian (Λ := Λ) aS b
  refine boundedConstructible_obj_of_forall_singleFunctor Λ _ (fun F hF ↦ ?_) hK
  exact ⟨⟨⟨0, ((b)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj_singleFunctor F⟩,
    ⟨2 * d, (isLE_iff _ _).2 fun q hq ↦
      isZero_homology_rightDerivedLowerStar_of_isProper b d (fun Ω _ _ s ↦ hd Ω s) F q hq⟩⟩,
    hb F hF⟩

end Etale

end AlgebraicGeometry
