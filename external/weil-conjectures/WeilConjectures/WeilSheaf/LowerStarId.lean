/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion

/-!
# The pushforward of Weil sheaves along the identity

The pushforward `(𝟙 X)_*` of pro-étale Weil sheaves along the identity of a `k₀`-scheme is
isomorphic to the identity functor
(`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarIdIso`), and so is the pushforward of Weil
sheaves (`AlgebraicGeometry.WeilSheaf.lowerStarIdIso`): it is the transport of Weil structures
along the pushforward along the identity of `X̄`, an equivalence, hence fully faithful, and it
satisfies `(𝟙 X)_* ⋙ (𝟙 X)_* ≅ (𝟙 X ≫ 𝟙 X)_* = (𝟙 X)_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The pushforward of pro-étale Weil sheaves along the identity is fully faithful: it is the
transport of Weil structures along the pushforward along the identity of the geometric fiber,
an equivalence. -/
noncomputable def ProEtaleWeilSheaf.fullyFaithfulLowerStarId :
    (ProEtaleWeilSheaf.lowerStar k₀ l (𝟙 X)).FullyFaithful := by
  have : IsIso (Scheme.Hom.geometricFiberMap (𝟙 X)
      (comp_over (𝟙 X) (Spec (CommRingCat.of k₀)))) := by
    rw [Scheme.Hom.geometricFiberMap_id]
    infer_instance
  exact IsoAlgebra.fullyFaithfulMapOfNatIso _ (Functor.FullyFaithful.ofFullyFaithful _)

/-- The pushforward of pro-étale Weil sheaves along the identity is isomorphic to the identity
functor. -/
noncomputable def ProEtaleWeilSheaf.lowerStarIdIso :
    ProEtaleWeilSheaf.lowerStar k₀ l (𝟙 X) ≅ 𝟭 _ :=
  (ProEtaleWeilSheaf.fullyFaithfulLowerStarId k₀ l X).isoIdOfCompSelfIso
    (ProEtaleWeilSheaf.lowerStarCompIso k₀ l (𝟙 X) (𝟙 X) ≪≫
      ProEtaleWeilSheaf.lowerStarCongr k₀ l (Category.comp_id (𝟙 X)))

variable [Fact (ringChar k₀ ≠ l)] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The pushforward of Weil sheaves along the identity is isomorphic to the identity functor. -/
noncomputable def WeilSheaf.lowerStarIdIso : WeilSheaf.lowerStar (k₀ := k₀) (l := l) (𝟙 X) ≅ 𝟭 _ :=
  ((WeilSheaf.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.lowerStarIdIso k₀ l X) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

end AlgebraicGeometry
