/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroTransfer
public import WeilConjectures.TraceFormula.SupportedRestrictionIntegral

/-!

# The fibre product of the strictly local model and the product `X ⨯ X`

This file sets up the identification of `X × X` with the fibre product
`X ×_k X` of the classical model, with the factors interchanged
(`ProEtale.CondensedRing.swapPullbackToProd`): the library's correspondences have support
`(c₁, c₂)` and coefficients `K ⊠ D_X K`, the classical model
(`Etale.CurveLocalModel`) the transposed graph `(h, id)` and `D_X K ⊠ K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-- The identification `X ×_k X ≅ (X ⨯ X).left` interchanging the factors: the first projection
of `X ⨯ X` corresponds to the second projection of the fibre product. -/
noncomputable def swapPullbackToProd (X : Over (Spec (.of k))) :
    pullback X.hom X.hom ⟶ (X ⨯ X).left :=
  (pullbackSymmetry X.hom X.hom).hom ≫ (Over.prodLeftIsoPullback X X).inv

instance (X : Over (Spec (.of k))) : IsIso (swapPullbackToProd X) := by
  unfold swapPullbackToProd
  infer_instance

@[reassoc (attr := simp)]
lemma swapPullbackToProd_fst (X : Over (Spec (.of k))) :
    swapPullbackToProd X ≫ (prod.fst : X ⨯ X ⟶ X).left = pullback.snd X.hom X.hom := by
  simp [swapPullbackToProd]

@[reassoc (attr := simp)]
lemma swapPullbackToProd_snd (X : Over (Spec (.of k))) :
    swapPullbackToProd X ≫ (prod.snd : X ⨯ X ⟶ X).left = pullback.fst X.hom X.hom := by
  simp [swapPullbackToProd]

end AlgebraicGeometry.ProEtale.CondensedRing
