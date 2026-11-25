/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalInverseMateInterchange

/-! # The proper scalar comparison in geometric mate coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
universe u
namespace WeilConjectures.ExceptionalIntegralScalar
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

-- The chosen derived presentations require an extended conversion budget.
/-- The scalar-adjunction definition of the proper comparison is the geometric
adjunction mate of the canonical tensor/pullback comparison.
Source: Stacks Tags 0E46 and 0B56.
(blueprint: lem-sf-proper-scalar-mate-normalization).

Proof: the restriction/direct-image comparison is the geometric mate of the
restriction/pullback comparison, by its normalized adjunction equation evaluated
at the geometric counit. The scalar mate of that same pullback comparison is the
inverse tensor/pullback comparison. Apply inverse mate interchange, which follows
from conjugation under the two composite adjunctions. -/
theorem properScalarMate_normalized
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    PurCompactSupport.properComparison a g =
      (mateEquiv (proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g))
        (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g))
        (TwoSquare.mk _ _ _ _ (proEtaleReductionPullbackIso g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom)) := by
  let av := pbcDerivedScalarAdjunction (a.map V)
  let au := pbcDerivedScalarAdjunction (a.map U)
  let ar := proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)
  let az := proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g)
  let b := proEtaleRingRestrictionDerivedPullback g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let d := proEtaleRingRestrictionDerivedDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  have := proEtaleReductionPullbackInv_isIso g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let β := asIso (proEtaleReductionPullbackInv g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))
  have hβ : (mateEquiv av au (TwoSquare.mk _ _ _ _ β.hom)) = b.inv := by
    exact ((mateEquiv av au).apply_symm_apply
      (TwoSquare.mk _ _ _ _ b.inv))
  have hd : (mateEquiv az ar (TwoSquare.mk _ _ _ _ b.inv)) = d.hom := by
    apply NatTrans.ext
    funext N
    have h := (proEtaleRingSheafChangeAdjunction g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).2.2
      ((proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g)).obj N) N
      (az.counit.app N)
    have hid : az.homEquiv _ _ (az.counit.app N) = 𝟙 _ := by
      rw [← az.homEquiv_symm_id N]
      exact (az.homEquiv _ _).apply_symm_apply _
    change ar.homEquiv _ _ (b.inv.app _ ≫
      (proEtaleRingRestrictScalars (a.map U)).mapDerivedCategory.map (az.counit.app N)) =
        (proEtaleRingRestrictScalars (a.map V)).mapDerivedCategory.map
          (az.homEquiv _ _ (az.counit.app N)) ≫ d.hom.app N at h
    rw [hid] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    rw [← h]
    simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
      Functor.comp_obj, Functor.comp_map, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
      Adjunction.homEquiv_unit, Functor.map_comp]
    erw [Category.comp_id]
  exact inverseMateInterchange au av ar az b.symm β d hβ hd

end WeilConjectures.ExceptionalIntegralScalar
