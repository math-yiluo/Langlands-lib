/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingClosedImmersionLaw
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBaseUnique

/-!

# The composition law of the bounded constructible proper exchanges

For morphisms of models `φ : M ⟶ N` and `ψ : N ⟶ P` with composite `χ`, the proper exchanges
of bounded constructible complexes compose, `χ_χ = Rg'_*(χ_φ) ∘ χ_ψ(Rf_*)`, through the
composition isomorphisms of the direct images
(`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_comp_app_of_eq`), from the ambient
law `NearbyCyclesModel.Hom.pushforwardExchange_comp_app_of_eq`. This is the composition input of
the closed-immersion law of the dualizing maps (`CategoryTheory.closedImmersionLaw_aux`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Restriction

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

/-- The restricted nearby cycles of a bounded constructible complex are the nearby cycles of the
underlying complex. -/
lemma boundedConstructibleNearbyCycles_obj_obj (hM : M.PreservesBoundedConstructible Λ)
    (K : Dᵇc(X)⟦Λ⟧) :
    ((boundedConstructibleNearbyCycles hM).obj K).obj = (M.nearbyCycles Λ).obj K.obj :=
  rfl

/-- The restricted nearby cycles of a morphism of bounded constructible complexes are the nearby
cycles of the underlying morphism. -/
lemma boundedConstructibleNearbyCycles_map_hom (hM : M.PreservesBoundedConstructible Λ)
    {K L : Dᵇc(X)⟦Λ⟧} (f : K ⟶ L) :
    ((boundedConstructibleNearbyCycles hM).map f).hom = (M.nearbyCycles Λ).map f.hom :=
  rfl

end Restriction

section Composition

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {X' Y' Z' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {P : NearbyCyclesModel Z.left Z'.left}

/-- The composition law of exchanges on bounded constructible complexes, for arbitrary ambient
transformations: kept abstract so that elaboration never unfolds the ambient exchanges. -/
private lemma comp_app_of_hom_eq_aux {f : X ⟶ Y} {g : Y ⟶ Z} {fg : X ⟶ Z} {f' : X' ⟶ Y'}
    {g' : Y' ⟶ Z'} {fg' : X' ⟶ Z'}
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hP : P.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (χa : R((fg.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        P.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⟶
      M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        R((fg'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (ψa : R((g.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        P.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⟶
      N.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        R((g'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (φa : R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        N.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⟶
      M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        R((f'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (ca : R((fg.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        R((g.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (ca' : R((fg'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      R((f'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        R((g'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (hyp : ∀ E, χa.app E ≫ ca'.app ((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E) =
      (P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map (ca.app E) ≫
        ψa.app (R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj E) ≫
          R((g'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map (φa.app E))
    (χb : boundedConstructibleLowerStar ℓ fg ⋙ boundedConstructibleNearbyCycles hP ⟶
      boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar ℓ fg')
    (hχb : ∀ K, (χb.app K).hom = χa.app K.obj)
    (ψb : boundedConstructibleLowerStar ℓ g ⋙ boundedConstructibleNearbyCycles hP ⟶
      boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleLowerStar ℓ g')
    (hψb : ∀ K, (ψb.app K).hom = ψa.app K.obj)
    (φb : boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleNearbyCycles hN ⟶
      boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar ℓ f')
    (hφb : ∀ K, (φb.app K).hom = φa.app K.obj)
    (cb : boundedConstructibleLowerStar ℓ fg ⟶
      boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleLowerStar ℓ g)
    (hcb : ∀ K, (cb.app K).hom = ca.app K.obj)
    (cb' : boundedConstructibleLowerStar ℓ fg' ⟶
      boundedConstructibleLowerStar ℓ f' ⋙ boundedConstructibleLowerStar ℓ g')
    (hcb' : ∀ K, (cb'.app K).hom = ca'.app K.obj)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    χb.app K ≫ cb'.app ((boundedConstructibleNearbyCycles hM).obj K) =
      (boundedConstructibleNearbyCycles hP).map (cb.app K) ≫
        ψb.app ((boundedConstructibleLowerStar ℓ f).obj K) ≫
        (boundedConstructibleLowerStar ℓ g').map (φb.app K) := by
  ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleNearbyCycles_map_hom,
    boundedConstructibleLowerStar_map_hom, hχb, hcb', hcb, hψb, hφb]
  exact hyp K.obj
lemma Hom.boundedConstructiblePushforwardExchange_comp_app_of_eq {f : X ⟶ Y} {g : Y ⟶ Z}
    {fg : X ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'} {fg' : X' ⟶ Z'} (φ : M.Hom N f.left f'.left)
    (ψ : N.Hom P g.left g'.left) (χ : M.Hom P fg.left fg'.left) (h : f ≫ g = fg)
    (h' : f' ≫ g' = fg') (htot : φ.total ≫ ψ.total = χ.total)
    (hgen : φ.generic ≫ ψ.generic = χ.generic)
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hP : P.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (χ.boundedConstructiblePushforwardExchange ℓ hM hP).app K ≫
        (boundedConstructibleLowerStarCompOfEq ℓ f' g' h').inv.app
          ((boundedConstructibleNearbyCycles hM).obj K) =
      (boundedConstructibleNearbyCycles hP).map
          ((boundedConstructibleLowerStarCompOfEq ℓ f g h).inv.app K) ≫
        (ψ.boundedConstructiblePushforwardExchange ℓ hN hP).app
          ((boundedConstructibleLowerStar ℓ f).obj K) ≫
        (boundedConstructibleLowerStar ℓ g').map
          ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app K) :=
  comp_app_of_hom_eq_aux ℓ hM hN hP _ _ _ _ _
    (φ.pushforwardExchange_comp_app_of_eq (Profinite.padicAlgClRingObj ℓ) ψ χ
      (congrArg CommaMorphism.left h) (congrArg CommaMorphism.left h') htot hgen)
    _ (Hom.boundedConstructiblePushforwardExchange_app_hom ℓ χ hM hP)
    _ (Hom.boundedConstructiblePushforwardExchange_app_hom ℓ ψ hN hP)
    _ (Hom.boundedConstructiblePushforwardExchange_app_hom ℓ φ hM hN)
    _ (boundedConstructibleLowerStarCompOfEq_inv_app_hom ℓ f g fg h)
    _ (boundedConstructibleLowerStarCompOfEq_inv_app_hom ℓ f' g' fg' h') K

end Composition

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
