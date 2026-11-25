/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange

/-!
# Pushforward of sheaves of continuous functions along an isomorphism

For an isomorphism `e : X ≅ Y` of schemes and a topological abelian group `A`, the pushforward of
the pro-étale sheaf `C(-, A)` along `e` is `C(-, A)`
(`AlgebraicGeometry.ProEtale.continuousSheafLowerStarIso`), compatibly with the maps induced by
continuous homomorphisms and with the inclusion `C(-, ℤ_ℓ) ⊆ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type) [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]
  {X Y : Scheme.{u}}

/-- The pushforward of `C(-, A)` along an isomorphism `e : X ≅ Y` is `C(-, A)`: its sections over
`V → Y` are the continuous functions on `V ×_Y X ≅ V`. -/
noncomputable def continuousSheafLowerStarIso (e : X ≅ Y) :
    (e.hom)_*[AddCommGrpCat.{u + 1}].obj (continuousSheaf X A) ≅ continuousSheaf Y A :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (show _ ≅ _ from
    (Functor.isoWhiskerRight (NatIso.op (overPullbackForgetIso e.hom))
      (continuousMapPresheafAbULift A)).symm)

variable {A} {B : Type} [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

lemma continuousSheafLowerStarIso_hom_naturality (e : X ≅ Y) (φ : ContinuousAddMonoidHom A B) :
    (e.hom)_*[AddCommGrpCat.{u + 1}].map (continuousSheafMap X φ) ≫
        (continuousSheafLowerStarIso B e).hom =
      (continuousSheafLowerStarIso A e).hom ≫ continuousSheafMap Y φ :=
  rfl

variable (l : ℕ) [Fact l.Prime]

lemma continuousSheafLowerStarIso_hom_continuousSheafToAdicConstantSheaf (e : X ≅ Y) :
    (e.hom)_*[AddCommGrpCat.{u + 1}].map (continuousSheafToAdicConstantSheaf l X) ≫
        (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) Y).map
          (adicConstantSheafLowerStarIso l e).hom =
      (continuousSheafLowerStarIso ℤ_[l] e).hom ≫ continuousSheafToAdicConstantSheaf l Y :=
  rfl

end AlgebraicGeometry.ProEtale
