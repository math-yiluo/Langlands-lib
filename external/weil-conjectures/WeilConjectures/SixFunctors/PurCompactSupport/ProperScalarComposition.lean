/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarGeometricPullComposition
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteProperMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Proper scalar mates and the proper compositor

Source: Stacks 03D8, 0D6D, 07A6; canonical restriction squares and mate pasting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

private theorem properComparison_mate {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    (mateEquiv (proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g))
      (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g))
      (TwoSquare.mk _ _ _ _ (scalarPull a g).inv)) = properComparison a g := by
  let ar := proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)
  let bs := proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g)
  ext M
  apply (bs.homEquiv _ _).symm.injective
  have hc := IntegralSystemRealization.geometric_scalar_mate ar bs
    (pbcDerivedScalarAdjunction (a.map V)) (pbcDerivedScalarAdjunction (a.map U))
    (proEtaleRingRestrictionDerivedDirectImage g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)) M
  simpa only [Adjunction.homEquiv_counit, scalarPull, properComparison] using
    (mateEquiv_counit ar bs (TwoSquare.mk _ _ _ _ (scalarPull a g).inv) M).trans hc.symm

private theorem properComparison_mate_square {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    mateEquiv (proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g))
      (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g))
      (TwoSquare.mk _ _ _ _ (scalarPull a g).inv) =
        TwoSquare.mk _ _ _ _ (properComparison a g) := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  exact congrArg (fun t ↦ t.app M) (properComparison_mate a g)

/-- The scalar mate commutes with inverse proper composition, including equality transport.
Source: Stacks 03D8, 0D6D, 07A6; Zheng 5.13--5.15.
(blueprint: lem-sf-proper-scalar-composition).

Proof: eliminate the geometric composite equality. Invert the component isomorphism
in scalarPull_geometric_composition. The resulting compatibility square has the
inverse scalar/pullback maps and the forward geometric pullback compositors as its
edges. The generic geometric_scalar_mate counit identity identifies each geometric
mate with properComparison. Apply mateEquiv_whiskerTop_conjugateEquiv and the mate
pasting law mateEquiv_hcomp. Since geometricPushComposition is the conjugate of
geometricPullComposition, this is the forward proper-compositor scalar square.
Evaluate at M and cancel the forward proper compositors to obtain the displayed
inverse-compositor formula. Equality transport was eliminated in the first step.
This works for arbitrary coefficient sheaves, all unbounded inputs, identity maps,
and zero objects; no properness or absolute separatedness is needed. -/
theorem properComparison_inverse_composition
    {R S : Coefficients.{u}} (a : Change R S)
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) (g : U ⟶ W)
    (w : h ≫ k = g)
    (hR : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h))
    (hS : S.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (S.ring W) (S.ring V) (S.ring U) (S.pull k) (S.pull h))
    (M : DerivedCategory (pbcModules U (R.ring U))) :
    let qR : push R h ⋙ push R k ≅ push R g :=
      geometricPushComposition R h k hR ≪≫
      eqToIso (congrArg (fun v ↦ push R v) w)
    let qS : push S h ⋙ push S k ≅ push S g :=
      geometricPushComposition S h k hS ≪≫
      eqToIso (congrArg (fun v ↦ push S v) w)
    (pbcDerivedExtend (a.map W)).map (qR.inv.app M) ≫
        (properComparison a k).app ((push R h).obj M) ≫
        (push S k).map ((properComparison a h).app M) =
      (properComparison a g).app M ≫
        qS.inv.app ((pbcDerivedExtend (a.map U)).obj M)  := by
  subst g
  let ar := proEtaleRingDerivedAdjunction h (R.ring V) (R.ring U) (R.pull h)
  let br := proEtaleRingDerivedAdjunction k (R.ring W) (R.ring V) (R.pull k)
  let cr := proEtaleRingDerivedAdjunction (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k))
  let as₀ := proEtaleRingDerivedAdjunction h (S.ring V) (S.ring U) (S.pull h)
  let bs := proEtaleRingDerivedAdjunction k (S.ring W) (S.ring V) (S.pull k)
  let cs := proEtaleRingDerivedAdjunction (h ≫ k) (S.ring W) (S.ring U) (S.pull (h ≫ k))
  let pR := geometricPullComposition R h k hR
  let pS := geometricPullComposition S h k hS
  let qR := geometricPushComposition R h k hR
  let qS := geometricPushComposition S h k hS
  let ellh := scalarPull a h
  let ellk := scalarPull a k
  let ellhk := scalarPull a (h ≫ k)
  let TX := pbcDerivedExtend (a.map U)
  let TY := pbcDerivedExtend (a.map W)
  let s₁ := TwoSquare.vComp (TwoSquare.mk _ _ _ _ ellk.inv)
    (TwoSquare.mk _ _ _ _ ellh.inv)
  let s₂ := TwoSquare.mk _ _ _ _ ellhk.inv
  have hc : s₂.whiskerLeft pR.hom = s₁.whiskerRight pS.hom := by
    ext L
    have he : TX.mapIso (pR.symm.app L) ≪≫ ellhk.app L =
        ellh.app ((pull R k).obj L) ≪≫ (pull S h).mapIso (ellk.app L) ≪≫
          pS.symm.app (TY.obj L) := by
      apply Iso.ext
      exact scalarPull_geometric_composition a h k hR hS L
    simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv,
      Category.assoc, s₁, s₂, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Category.id_comp, Category.comp_id] using congrArg Iso.inv he
  have hm := mateEquiv_whiskerTop_conjugateEquiv
    (br.comp ar) cr (bs.comp as₀) cs pR.hom pS.hom s₁ s₂ hc
  dsimp only [s₁, s₂] at hm
  rw [mateEquiv_hcomp] at hm
  dsimp only [ar, br, cr, as₀, bs, cs, ellh, ellk, ellhk] at hm
  rw [properComparison_mate_square, properComparison_mate_square,
    properComparison_mate_square] at hm
  have he := congrArg (fun z ↦ z.app M) hm
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj] at he
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at he
  change TY.map (qR.hom.app M) ≫ (properComparison a (h ≫ k)).app M =
    (properComparison a k).app ((push R h).obj M) ≫
      (push S k).map ((properComparison a h).app M) ≫
      qS.hom.app (TX.obj M) at he
  dsimp only
  simp only [eqToIso_refl, Iso.trans_refl]
  change TY.map (qR.inv.app M) ≫
      (properComparison a k).app ((push R h).obj M) ≫
      (push S k).map ((properComparison a h).app M) =
    (properComparison a (h ≫ k)).app M ≫ qS.inv.app (TX.obj M)
  apply (cancel_mono (qS.hom.app (TX.obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← he]
  rw [← TY.map_comp_assoc, qR.inv_hom_id_app, TY.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

end WeilConjectures.PurCompactSupport
