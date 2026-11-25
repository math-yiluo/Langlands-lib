/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.TensorInverse
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Conservative
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom

/-!
# Étale-locally trivial sheaves are invertible

Let `F` be an `A`-valued étale sheaf on `X` which is trivial étale-locally: there is a jointly
surjective family of étale morphisms `gᵢ : Wᵢ ⟶ X` with `gᵢ^* F ≅ 𝟙`. Then the evaluation
`F ⊗ [F, 𝟙] ⟶ 𝟙` is an isomorphism, so the internal dual `[F, 𝟙]` is a two-sided tensor inverse
of `F` (`AlgebraicGeometry.Etale.tensorInverseOfUpperStarIso`).

The evaluation is checked after restriction to the `Wᵢ`, which is jointly conservative
(`AlgebraicGeometry.Etale.isIso_of_isIso_localizationRestriction`). Pullback along an étale
morphism is monoidal and commutes with internal homs
(`AlgebraicGeometry.Etale.isIso_ihomComparison_upperStar`), so the restricted evaluation is the
evaluation of `gᵢ^* F ≅ 𝟙`, which is an isomorphism since tensoring with an object isomorphic to
the unit is an equivalence.

## Main statements

- `AlgebraicGeometry.Etale.isIso_ihom_ev_app_unit_of_upperStar_iso`: the evaluation
  `F ⊗ [F, 𝟙] ⟶ 𝟙` is an isomorphism.

## Main definitions

- `AlgebraicGeometry.Etale.tensorInverseOfUpperStarIso`: the tensor inverse `[F, 𝟙]` of `F`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
  [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

variable {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
  [∀ i, Etale (g i)] (hg : ⋃ i, Set.range (g i).base = Set.univ)

include hg in
/-- The evaluation `F ⊗ [F, 𝟙] ⟶ 𝟙` of a sheaf `F` which is trivial after pullback to the
members of a jointly surjective family of étale morphisms is an isomorphism. -/
theorem isIso_ihom_ev_app_unit_of_upperStar_iso (F : Sheaf X.smallEtaleTopology A)
    (e : ∀ i, (g i)^*[A].obj F ≅ 𝟙_ _) :
    IsIso ((ihom.ev F).app (𝟙_ _)) := by
  refine isIso_of_isIso_localizationRestriction A _ g hg fun i ↦ ?_
  let G := (g i)^*[A]
  let r := upperStarIsoLocalizationRestriction A (g i) inferInstance
  suffices IsIso (G.map ((ihom.ev F).app (𝟙_ _))) by
    have h := r.hom.naturality ((ihom.ev F).app (𝟙_ _))
    rw [← cancel_epi (r.inv.app _), Iso.inv_hom_id_app_assoc] at h
    rw [← h]
    infer_instance
  -- the evaluation of an object isomorphic to the unit is an isomorphism
  have hev : ∀ (Y : Sheaf (W i).smallEtaleTopology A) (Z : Sheaf (W i).smallEtaleTopology A),
      (Y ≅ 𝟙_ _) → IsIso ((ihom.ev Y).app Z) := by
    intro Y Z eY
    have : (tensorLeft Y).IsEquivalence :=
      Functor.isEquivalence_of_iso (((tensoringLeft _).mapIso eY ≪≫ leftUnitorNatIso _).symm)
    exact NatIso.isIso_app_of_isIso (ihom.adjunction Y).counit Z
  have hc : IsIso ((ihomComparison G F).app (𝟙_ _)) := by
    have := isIso_ihomComparison_upperStar A (g i) F
    infer_instance
  have hμ : IsIso (μ G F ((ihom F).obj (𝟙_ _))) := inferInstance
  have h₁ := hev (G.obj F) (G.obj (𝟙_ _)) (e i)
  have key := ihomComparison_ev G F (𝟙_ _)
  rw [← cancel_epi (inv (μ G F ((ihom F).obj (𝟙_ _)))), IsIso.inv_hom_id_assoc] at key
  rw [← key]
  infer_instance

/-- The internal dual `[F, 𝟙]` of a sheaf `F` which is trivial after pullback to the members of
a jointly surjective family of étale morphisms is a two-sided tensor inverse of `F`, the
identifications being the evaluation and its composite with the braiding. -/
noncomputable def tensorInverseOfUpperStarIso (F : Sheaf X.smallEtaleTopology A)
    (e : ∀ i, (g i)^*[A].obj F ≅ 𝟙_ _) : TensorInverse F :=
  haveI := isIso_ihom_ev_app_unit_of_upperStar_iso A g hg F e
  { obj := (ihom F).obj (𝟙_ _)
    rightIso := asIso ((ihom.ev F).app (𝟙_ _))
    leftIso := β_ _ _ ≪≫ asIso ((ihom.ev F).app (𝟙_ _)) }

end Etale

end AlgebraicGeometry
