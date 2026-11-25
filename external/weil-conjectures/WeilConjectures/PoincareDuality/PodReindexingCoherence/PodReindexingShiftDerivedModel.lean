/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingDerivedSourceShift
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingDerivedTargetShift

/-! # Representative model part of the derived signed shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

This module isolates the equation on localized representatives.  The remaining
localization descent is recorded separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The component equation used in the derived signed shift square. -/
def derivedShiftEquation {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (M N : podReindexingDerived l E Y s) (a b : ℤ) : Prop :=
  c.derived.hom.app (op (M⟦a⟧), N⟦b⟧) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app M).op
          (((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app N)) ≫
      (signedShift l E X s ((podReindexingDerivedFunctor l E g s).obj M)
        ((podReindexingDerivedFunctor l E g s).obj N) a b).hom =
    (podReindexingDerivedFunctor l E g s).map (signedShift l E Y s M N a b).hom ≫
      ((podReindexingDerivedFunctor l E g s).commShiftIso (b-a)).hom.app
        ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
      (c.derived.hom.app (op M, N))⟦b-a⟧'

private theorem paste_shift_squares {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    (a b : ℤ) (A A' A'' : C) (B B' B'' : D)
    (k : F.obj A'' ⟶ B'') (sC : A'' ⟶ A'⟦-a⟧) (sD : B'' ⟶ B'⟦-a⟧)
    (x : F.obj A' ⟶ B') (tC : A' ⟶ A⟦b⟧) (tD : B' ⟶ B⟦b⟧)
    (z : F.obj A ⟶ B)
    (hs : k ≫ sD = F.map sC ≫ (F.commShiftIso (-a)).hom.app A' ≫ x⟦-a⟧')
    (ht : x ≫ tD = F.map tC ≫ (F.commShiftIso b).hom.app A ≫ z⟦b⟧') :
    k ≫ sD ≫ tD⟦-a⟧' ≫
        (shiftFunctorAdd' D b (-a) (b-a) (sub_eq_add_neg b a).symm).inv.app B =
      F.map (sC ≫ tC⟦-a⟧' ≫
        (shiftFunctorAdd' C b (-a) (b-a) (sub_eq_add_neg b a).symm).inv.app A) ≫
      (F.commShiftIso (b-a)).hom.app A ≫ z⟦b-a⟧' := by
  let dC := shiftFunctorAdd' C b (-a) (b-a) (sub_eq_add_neg b a).symm
  let dD := shiftFunctorAdd' D b (-a) (b-a) (sub_eq_add_neg b a).symm
  have hF : (F.commShiftIso (-a)).hom.app (A⟦b⟧) ≫
      ((F.commShiftIso b).hom.app A)⟦-a⟧' ≫ dD.inv.app (F.obj A) =
      F.map (dC.inv.app A) ≫ (F.commShiftIso (b-a)).hom.app A := by
    rw [F.commShiftIso_add' (sub_eq_add_neg b a).symm]
    simp only [Functor.CommShift.isoAdd'_hom_app, Functor.comp_obj, dC, dD,
      ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  change k ≫ sD ≫ tD⟦-a⟧' ≫ dD.inv.app B = _
  rw [← Category.assoc k sD, hs]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.commShiftIso_hom_naturality_assoc tC (-a)]
  have hn := dD.inv.naturality z
  change (z⟦b⟧')⟦-a⟧' ≫ dD.inv.app B =
    dD.inv.app (F.obj A) ≫ z⟦b-a⟧' at hn
  rw [hn, reassoc_of% hF]

set_option linter.unusedVariables false in
/-- The signed shift equation on K-injective localized representatives.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
Proof: expand the chosen K-injective representatives in `Comparison.derived_model`,
transport the signed reindexing through the chain shift isomorphisms, and use the
fixed product projections to identify both composites degree by degree. -/
theorem derived_shift_model {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∀ (P I : K l E Y s) (hI : I.IsKInjective) (a b : ℤ),
      derivedShiftEquation l E g s SX SY TX TY c
        ((podReindexingQ l E Y s).obj P)
        ((podReindexingQ l E Y s).obj I) a b := by
  intro P I _hI a b
  let M := (podReindexingQ l E Y s).obj P
  let N := (podReindexingQ l E Y s).obj I
  let F := podReindexingDerivedFunctor l E g s
  let HX := podReindexingDerivedHom l E X s
  let HY := podReindexingDerivedHom l E Y s
  let Hx := CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
    (ProEt.topology X) (podReindexingRing l E X s) (F.obj M)
  let Hy := CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
    (ProEt.topology Y) (podReindexingRing l E Y s) M
  let Hxa := CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
    (ProEt.topology X) (podReindexingRing l E X s) ((F.obj M)⟦a⟧)
  let sx := CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
    (ProEt.topology X) (podReindexingRing l E X s) (F.obj M) a
  let sy := CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
    (ProEt.topology Y) (podReindexingRing l E Y s) M a
  let f := (F.commShiftIso a).inv.app M
  let t := (F.commShiftIso b).hom.app N
  let k := c.derived.hom.app (op (M⟦a⟧), N⟦b⟧) ≫ HX.map (Prod.mkHom f.op t)
  let x := c.derived.hom.app (op M, N⟦b⟧) ≫ Hx.map t
  let z := c.derived.hom.app (op M, N)
  have hmap : HX.map (Prod.mkHom f.op t) =
      HX.map (Prod.mkHom f.op (𝟙 (F.obj (N⟦b⟧)))) ≫ Hxa.map t := by
    change HX.map (Prod.mkHom f.op t) =
      HX.map (Prod.mkHom f.op (𝟙 _)) ≫ HX.map (Prod.mkHom (𝟙 _) t)
    rw [← HX.map_comp]
    congr 1
    simp only [prod_comp, Category.comp_id, Category.id_comp]
  have hn : Hxa.map t ≫ sx.inv.app ((F.obj N)⟦b⟧) =
      sx.inv.app (F.obj (N⟦b⟧)) ≫ (Hx.map t)⟦-a⟧' := sx.inv.naturality t
  have hs : k ≫ sx.inv.app ((F.obj N)⟦b⟧) =
      F.map (sy.inv.app (N⟦b⟧)) ≫
        (F.commShiftIso (-a)).hom.app (Hy.obj (N⟦b⟧)) ≫ x⟦-a⟧' := by
    have h := derived_source_shift_square l E g s SX SY TX TY c M (N⟦b⟧) a
    change c.derived.hom.app (op (M⟦a⟧), N⟦b⟧) ≫
      HX.map (Prod.mkHom f.op (𝟙 _)) ≫ sx.inv.app (F.obj (N⟦b⟧)) =
      F.map (sy.inv.app (N⟦b⟧)) ≫
        (F.commShiftIso (-a)).hom.app (Hy.obj (N⟦b⟧)) ≫
        (c.derived.hom.app (op M, N⟦b⟧))⟦-a⟧' at h
    dsimp only [k]
    rw [hmap]
    simp only [Category.assoc]
    rw [hn]
    have hh := congrArg (fun q ↦ q ≫ (Hx.map t)⟦-a⟧') h
    simpa only [x, Functor.map_comp, Category.assoc] using hh
  have ht : x ≫ (Hx.commShiftIso b).hom.app (F.obj N) =
      F.map ((Hy.commShiftIso b).hom.app N) ≫
        (F.commShiftIso b).hom.app (Hy.obj N) ≫ z⟦b⟧' := by
    simpa only [x, z, Hx, Hy, t, F, Category.assoc,
      CategoryTheory.RingedHomUniverses.hom, podReindexingDerivedHom,
      Functor.curry_obj_obj_map, Functor.curry_obj_obj_obj] using
      (derived_target_shift_square l E g s SX SY TX TY c M N b)
  have hp := paste_shift_squares F a b
    (Hy.obj N) (Hy.obj (N⟦b⟧)) (HY.obj (op (M⟦a⟧), N⟦b⟧))
    (Hx.obj (F.obj N)) (Hx.obj ((F.obj N)⟦b⟧)) (Hxa.obj ((F.obj N)⟦b⟧))
    k (sy.inv.app (N⟦b⟧)) (sx.inv.app ((F.obj N)⟦b⟧)) x
    ((Hy.commShiftIso b).hom.app N) ((Hx.commShiftIso b).hom.app (F.obj N)) z hs ht
  simpa only [derivedShiftEquation, signedShift, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc,
    k, z, M, N, F, HX, HY, Hx, Hy, Hxa, sx, sy, f, t,
    CategoryTheory.RingedHomUniverses.hom, podReindexingDerivedHom,
    Functor.curry_obj_obj_obj] using hp

end WeilConjectures.PodReindexingCoherence
