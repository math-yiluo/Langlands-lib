/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingBaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!

# The pullback exchange of nearby cycles commutes with the shifts

The nearby cycles `Ψ = Li^* Rj_* Lε^*` of a model
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCycles`) are a composite of
derived pullbacks and pushforwards, hence commute with the shifts and are triangulated. This
file shows that the pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of a morphism of models
(`NearbyCyclesModel.Hom.pullbackExchange`) commutes with the shifts, using that the pullback
comparison of a commutative square does
(`ProEtale.CondensedRing.commShift_pullbackSquareComparison_hom`).

## Main results

- `ProEtale.CondensedRing.NearbyCyclesModel.Hom.commShift_pullbackExchange`: the pullback
  exchange commutes with the shifts.

## Implementation notes

The compatibility of the pullback exchange with the shifts is proved for an abstract composite
of whiskered natural transformations (the private `_aux` lemma), where the reassociations of the
composite functors are cheap, and then instantiated.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Abstract computations -/

section Abstract

private lemma commShift_exchange_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    [HasShift DY' ℤ] [HasShift DX' ℤ] [HasShift DTN ℤ] [HasShift DTM ℤ] [HasShift DGN ℤ]
    [HasShift DGM ℤ] [HasShift DY ℤ] [HasShift DX ℤ]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JN : DTN ⥤ DGN} {JNs : DGN ⥤ DTN} {JM : DTM ⥤ DGM} {JMs : DGM ⥤ DTM}
    {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM} {F : DY ⥤ DX}
    [Fp'.CommShift ℤ] [IN.CommShift ℤ] [IM.CommShift ℤ] [T.CommShift ℤ] [JN.CommShift ℤ]
    [JNs.CommShift ℤ] [JM.CommShift ℤ] [JMs.CommShift ℤ] [G.CommShift ℤ] [EN.CommShift ℤ]
    [EM.CommShift ℤ] [F.CommShift ℤ]
    (adjN : JN ⊣ JNs) (adjM : JM ⊣ JMs) [adjN.CommShift ℤ] [adjM.CommShift ℤ]
    (θi : IN ⋙ Fp' ⟶ T ⋙ IM) (θj : T ⋙ JM ⟶ JN ⋙ G) (θε : EN ⋙ G ⟶ F ⋙ EM)
    [NatTrans.CommShift θi ℤ] [NatTrans.CommShift θj ℤ] [NatTrans.CommShift θε ℤ]
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
          Functor.whiskerRight (Functor.whiskerLeft EN (mateEquiv adjN adjM θj) ≫
            Functor.whiskerRight θε JMs) IM) :
    NatTrans.CommShift α ℤ := by
  have : NatTrans.CommShift (mateEquiv adjN adjM θj) ℤ :=
    NatTrans.CommShift.mateEquiv adjN adjM (TwoSquare.mk _ _ _ _ θj)
  have e : α = Functor.whiskerRight (Functor.associator EN JNs IN).inv Fp' ≫
      (Functor.associator (EN ⋙ JNs) IN Fp').hom ≫
      Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      (Functor.associator (EN ⋙ JNs) T IM).inv ≫
      Functor.whiskerRight ((Functor.associator EN JNs T).hom ≫
        Functor.whiskerLeft EN (mateEquiv adjN adjM θj) ≫
        (Functor.associator EN G JMs).inv ≫ Functor.whiskerRight θε JMs ≫
        (Functor.associator F EM JMs).hom) IM ≫
      (Functor.associator F (EM ⋙ JMs) IM).hom ≫
      Functor.whiskerLeft F (Functor.associator EM JMs IM).hom := by
    subst hα
    ext X
    simp
  rw [e]
  infer_instance

end Abstract

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}}

/-- The nearby cycles `Ψ = Li^* Rj_* Lε^*` commute with the shifts. -/
noncomputable instance commShift_nearbyCycles (M : NearbyCyclesModel X X') :
    (M.nearbyCycles Λ).CommShift ℤ :=
  inferInstanceAs ((L((M.ε)^*⟦Λ⟧) ⋙ R((M.j)_*⟦Λ⟧) ⋙ L((M.i)^*⟦Λ⟧)).CommShift ℤ)

/-- The nearby cycles `Ψ = Li^* Rj_* Lε^*` are triangulated. -/
instance isTriangulated_nearbyCycles (M : NearbyCyclesModel X X') :
    (M.nearbyCycles Λ).IsTriangulated :=
  inferInstanceAs ((L((M.ε)^*⟦Λ⟧) ⋙ R((M.j)_*⟦Λ⟧) ⋙ L((M.i)^*⟦Λ⟧)).IsTriangulated)

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of a morphism of models commutes with the
shifts. -/
instance Hom.commShift_pullbackExchange (φ : M.Hom N f f') :
    NatTrans.CommShift (φ.pullbackExchange Λ) ℤ :=
  commShift_exchange_aux (derivedUpperStarLowerStarAdjunction Λ N.j)
    (derivedUpperStarLowerStarAdjunction Λ M.j) (pullbackSquareComparison Λ φ.commSq_i).hom
    (pullbackSquareComparison Λ φ.commSq_j).hom (pullbackSquareComparison Λ φ.commSq_ε).hom
    (φ.pullbackExchange Λ) rfl

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
