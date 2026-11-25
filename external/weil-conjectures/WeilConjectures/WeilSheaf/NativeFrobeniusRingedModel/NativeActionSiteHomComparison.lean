/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeFrobeniusRingedModel
public import WeilConjectures.WeilSheaf.DerivedHom

/-! # Internal Hom along a specified native action-site realization

Source: prose-10-20, internal-Hom and evaluation paragraph;
the twisted action-site calculation, steps 11--12.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.TwistedActionRingedSite Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Restrict an action-site module and transport its structure map through the
specified ordinary Frobenius comparison. No existence theorem chooses these data.
Source: native ringed presentation step 2
(blueprint: lem-sf-native-action-site-hom-comparison). -/
noncomputable def NativeFrobeniusRingedModel.toWeil
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X)
    (P : Presentation A.J A.s A.R A.a) :
    letI := P.category
    Modules P.coefficient ⥤ ProEtaleWeilSheaf k₀ l X :=
  letI := P.category
  P.modules.functor ⋙ Endofunctor.IsoAlgebra.mapOfNatIso A.comparison

private theorem ordinary_hom_action
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X)
    (P : Presentation A.J A.s A.R A.a) (M N : Modules A.R)
    (tM : (sigma A.J A.s A.R A.a).obj M ≅ M)
    (tN : (sigma A.J A.s A.R A.a).obj N ≅ N) :
    (WeilSheaf.frobeniusPullback k₀ l X).map (A.hom M N).hom ≫
        (ihom k₀ l X
          (Endofunctor.IsoAlgebra.mk (A.E.functor.obj M)
            (A.comparison.app M ≪≫ A.E.functor.mapIso tM))
          (Endofunctor.IsoAlgebra.mk (A.E.functor.obj N)
            (A.comparison.app N ≪≫ A.E.functor.mapIso tN))).obj.str =
      A.comparison.hom.app (SheafOfModules.homObj (R := A.R) M N) ≫
        A.E.functor.map ((P.sigmaHom M N).hom ≫
          SheafOfModules.homObjMap (R := A.R) tM.inv tN.hom) ≫ (A.hom M N).hom := by
  rw [ihom_obj_str]
  simp only [Endofunctor.IsoAlgebra.mk_str, Endofunctor.IsoAlgebra.mk_carrier,
    Endofunctor.IsoAlgebra.mk_obj, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Mod.ihomMap_comp, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (Mod.ihomMap (A.E.functor.map tM.inv)).naturality
    (A.comparison.app N).hom]
  rw [reassoc_of% A.hom_frobenius P M N]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ A.comparison.hom.app (SheafOfModules.homObj (R := A.R) M N) ≫
      A.E.functor.map (P.sigmaHom M N).hom ≫ f)
    (A.hom_naturality tM.inv tN.hom).symm

private noncomputable def action_hom_component
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X)
    (P : Presentation A.J A.s A.R A.a) :
    letI := P.category
    ∀ M N : Modules P.coefficient,
      (A.toWeil P).obj (SheafOfModules.homObj (R := P.coefficient) M N) ≅
        ihom k₀ l X ((A.toWeil P).obj M) ((A.toWeil P).obj N) := by
  let _ := P.category
  intro M N
  let m := P.modules.functor.obj M
  let n := P.modules.functor.obj N
  let S := P.modules.functor.obj (SheafOfModules.homObj (R := P.coefficient) M N)
  let b := A.E.functor.mapIso (P.hom M N) ≪≫ A.hom m.obj.a n.obj.a
  refine ObjectProperty.isoMk _ (Endofunctor.Algebra.isoMk b ?_)
  have ha := ordinary_hom_action A P m.obj.a n.obj.a (pairIso m) (pairIso n)
  have hn := A.comparison.hom.naturality (P.hom M N).hom
  simp only [Functor.comp_map] at hn
  change (WeilSheaf.frobeniusPullback k₀ l X).map b.hom ≫
      (ihom k₀ l X
        (Endofunctor.IsoAlgebra.mk (A.E.functor.obj m.obj.a)
          (A.comparison.app m.obj.a ≪≫ A.E.functor.mapIso (pairIso m)))
        (Endofunctor.IsoAlgebra.mk (A.E.functor.obj n.obj.a)
          (A.comparison.app n.obj.a ≪≫ A.E.functor.mapIso (pairIso n)))).obj.str =
    (A.comparison.hom.app S.obj.a ≫ A.E.functor.map S.obj.str) ≫ b.hom
  dsimp only [b, Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, Category.assoc, ha, reassoc_of% hn]
  simpa only [Functor.map_comp, Category.assoc, pairIso, asIso_hom] using
    congrArg (fun f ↦ A.comparison.hom.app S.obj.a ≫
      A.E.functor.map f ≫ (A.hom m.obj.a n.obj.a).hom) (P.hom_action M N).symm

/-- The specified action-site realization respects the actual native internal
Hom, naturally in both module arguments. This asserts only compatibility for a
specified functor; it does not construct a site or assert an equivalence.

Source: prose-10-20, internal-Hom/evaluation paragraph;
native ringed presentation step 3; twisted action-site steps 11--12; Stacks 03EO
(blueprint: lem-sf-native-action-site-hom-comparison).

Proof: compose the underlying isomorphisms E(P.hom) and A.hom. Expand the
native ihom_obj_str formula for structures c_M followed by E(theta_M) and c_N
followed by E(theta_N). Precomposition reverses the source composite. Commute
precomposition by E(theta_M inverse) past postcomposition by c_N using
naturality. The ordinary Frobenius square A.hom_frobenius identifies the initial
arrows, and A.hom_naturality inserts the two structure maps. Naturality of c
and P.hom_action then prove that the composite intertwines the native Weil
structures. Lift it by Algebra.isoMk and ObjectProperty.isoMk. Finally compose
P.hom_naturality with A.hom_naturality to obtain the naturality square in both
arguments and assemble the components by NatIso.ofComponents. This uses A's
specified ordinary comparisons; it does not infer preservation of Hom merely
from additivity. Zero modules and an empty geometric fiber obey the same
formulas, with no constructibility or local freeness hypothesis. -/
theorem native_action_site_hom_comparison
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X)
    (P : Presentation A.J A.s A.R A.a) :
    letI := P.category
    Nonempty
      (Functor.uncurry.obj (SheafOfModules.homFunctor (R := P.coefficient)) ⋙ A.toWeil P ≅
        ((A.toWeil P).op.prod (A.toWeil P)) ⋙
          Functor.uncurry.obj (ihomBifunctor k₀ l X)) := by
  let _ := P.category
  refine ⟨NatIso.ofComponents (fun MN ↦ action_hom_component A P MN.1.unop MN.2) ?_⟩
  intro MN MN' fg
  apply Endofunctor.IsoAlgebra.hom_ext
  change A.E.functor.map
      (P.modules.functor.map (SheafOfModules.homObjMap (R := P.coefficient)
        fg.1.unop fg.2)).hom.f ≫
        (A.E.functor.map (P.hom MN'.1.unop MN'.2).hom ≫
          (A.hom (P.modules.functor.obj MN'.1.unop).obj.a
            (P.modules.functor.obj MN'.2).obj.a).hom) =
    (A.E.functor.map (P.hom MN.1.unop MN.2).hom ≫
        (A.hom (P.modules.functor.obj MN.1.unop).obj.a
          (P.modules.functor.obj MN.2).obj.a).hom) ≫
      (Mod.ihomMap (A.E.functor.map (P.modules.functor.map fg.1.unop).hom.f)).app _ ≫
        (ProEtale.AdicSheaf.ihom
          (A.E.functor.obj (P.modules.functor.obj MN'.1.unop).obj.a)).map
          (A.E.functor.map (P.modules.functor.map fg.2).hom.f)
  have hp := congrArg (fun f ↦ A.E.functor.map f ≫
      (A.hom (P.modules.functor.obj MN'.1.unop).obj.a
        (P.modules.functor.obj MN'.2).obj.a).hom)
    (P.hom_naturality fg.1.unop fg.2)
  have hh := congrArg (fun f ↦ A.E.functor.map (P.hom MN.1.unop MN.2).hom ≫ f)
    (A.hom_naturality (P.modules.functor.map fg.1.unop).hom.f
      (P.modules.functor.map fg.2).hom.f)
  simp only [Functor.map_comp, Category.assoc] at hp
  simp only [Category.assoc] at hh ⊢
  exact hp.trans hh

end AlgebraicGeometry.ProEtaleWeilSheaf
