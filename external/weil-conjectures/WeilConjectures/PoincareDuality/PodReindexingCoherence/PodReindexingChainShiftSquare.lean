/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData

/-! # Reindexing square for supplied signed chain shifts

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: new-pod-reindexing-chain-shift-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  homComplexFunctor homComplexπ WeilConjectures.podReindexingCoefficient

set_option allowUnsafeReducibility true in
attribute [local reducible] homComplex CochainComplex.shiftFunctor Functor.mapHomologicalComplex

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private lemma shift_formula_transport (W : Scheme.{u}) (s : Option ℕ)
    (S : ChainShift l E W s) (P I : K l E W s) (a b r p t q : ℤ)
    (ht : t = p - a) (hq : q = p + (r + (b - a))) :
    (S.iso P I a b).hom.f r ≫
        proj l E W s P I (r + (b - a)) p q hq.symm =
      (a * r).negOnePow •
        (proj l E W s (P⟦a⟧) (I⟦b⟧) r t (t + r) rfl ≫
          SheafOfModules.homObjMap (R := podReindexingRing l E W s)
            (P.shiftFunctorObjXIso a t p (by omega)).inv
            (I.shiftFunctorObjXIso b (t + r) q (by omega)).hom) := by
  subst t q
  exact S.formula P I a b r p

private lemma shift_formula (W : Scheme.{u}) (s : Option ℕ)
    (S : ChainShift l E W s) (P I : K l E W s) (a b r t : ℤ) :
    (S.iso P I a b).hom.f r ≫
        proj l E W s P I (r + (b - a)) (t + a) (t + r + b) (by omega) =
      (a * r).negOnePow • proj l E W s (P⟦a⟧) (I⟦b⟧) r t (t + r) rfl := by
  have h := shift_formula_transport l E W s S P I a b r (t + a) t (t + r + b)
    (by omega) (by omega)
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv] at h
  have hid := SheafOfModules.homObjMap_id (R := podReindexingRing l E W s)
    (M := P.X (t + a)) (N := I.X (t + r + b))
  erw [hid, Category.comp_id] at h
  exact h

private lemma complexShift_hom_f {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (s : Option ℕ) (a : ℤ) (P : K l E Y s) (r : ℤ) :
    ((complexShift l E g s a).hom.app P).f r = 𝟙 _ := by
  rfl

private lemma complexShift_inv_f {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (s : Option ℕ) (a : ℤ) (P : K l E Y s) (r : ℤ) :
    ((complexShift l E g s a).inv.app P).f r = 𝟙 _ := by
  rfl

private def sectionEval (W : Scheme.{u}) (s : Option ℕ)
    {A B : podReindexingModules l E W s} (U : W.ProEtᵒᵖ) (x : A.val.obj U) :
    (A ⟶ B) →+ B.val.obj U where
  toFun f := f.val.app U x
  map_zero' := rfl
  map_add' _ _ := rfl

private def homEval (W : Scheme.{u}) (s : Option ℕ)
    (A B : podReindexingModules l E W s) (U : W.ProEtᵒᵖ)
    (V : (Over U.unop)ᵒᵖ) (x : A.val.obj (op V.unop.left)) :
    (SheafOfModules.homObj (R := podReindexingRing l E W s) A B).val.obj U →+
      B.val.obj (op V.unop.left) where
  toFun f := (f.app V).hom x
  map_zero' := rfl
  map_add' _ _ := rfl

private lemma hom_units (W : Scheme.{u}) (s : Option ℕ)
    {A B D : podReindexingModules l E W s}
    (f : A ⟶ SheafOfModules.homObj (R := podReindexingRing l E W s) B D)
    (e : ℤˣ) (U : W.ProEtᵒᵖ) (z : A.val.obj U) (V : (Over U.unop)ᵒᵖ)
    (x : B.val.obj (op V.unop.left)) :
    ((((e • f).val.app U) z).app V).hom x =
      e • (((f.val.app U) z).app V).hom x := by
  change homEval l E W s B D U V x (sectionEval l E W s U z (e • f)) =
    e • homEval l E W s B D U V x (sectionEval l E W s U z f)
  simp only [Units.smul_def, map_zsmul]

private lemma chain_projection' {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) {SX : Closed l E X s} {SY : Closed l E Y s}
    {TX : Models l E X s SX} {TY : Models l E Y s SY}
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s)
    (n p q : ℤ) (h : p + n = q) (U : X.ProEtᵒᵖ) (V : (Over U.unop)ᵒᵖ)
    (z : ((hom l E Y s P I).X n).val.obj
      (op ((proEtaleIsoPostcompose g).obj U.unop)))
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj V.unop.left))) :
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) n p q h).val.app U
        (((c.chain P I).hom.f n).val.app U z)).app V).hom x =
      (((proj l E Y s P I n p q h).val.app
        (op ((proEtaleIsoPostcompose g).obj U.unop)) z).app
          (op (Over.mk ((proEtaleIsoPostcompose g).map V.unop.hom)))).hom x := by
  subst q
  exact c.chain_projection P I n p U.unop V.unop.left V.unop.hom z x

/-- The supplied signed shifts satisfy the chain reindexing square.

For each product projection, both routes reindex the source factor from `p`
to `p-a` and carry the scalar `(-1)^(a*r)`.  The `chain_projection` field of
the normalized comparison identifies the two projection maps.  Product
extensionality then gives the displayed equality of chain morphisms.  This is
strictly smaller than the existence theorem because the two shift structures
are fixed as hypotheses.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: new-pod-reindexing-chain-shift-square). -/
theorem chain_shift_reindexing_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (sX : ChainShift l E X s) (sY : ChainShift l E Y s) :
    (∀ (P I : K l E Y s) (a b : ℤ),
      (c.chain (P⟦a⟧) (I⟦b⟧)).hom ≫
        (((podReindexingHom l E X s).map
          ((complexShift l E g s a).inv.app P).op).app
            ((podReindexingComplexFunctor l E g s).obj (I⟦b⟧)) ≫
          ((podReindexingHom l E X s).obj
            (op (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧))).map
              ((complexShift l E g s b).hom.app I)) ≫
        (sX.iso ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I) a b).hom =
        (podReindexingComplexFunctor l E g s).map (sY.iso P I a b).hom ≫
          (complexShift l E g s (b-a)).hom.app
            (hom l E Y s P I) ≫ ((c.chain P I).hom)⟦b-a⟧') := by
  intro P I a b
  apply HomologicalComplex.hom_ext
  intro r
  apply homComplex_hom_ext
  intro p q hpq
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, p = t+a := ⟨p-a, by omega⟩
  dsimp only at hpq
  have hq : q = t+r+b := by omega
  subst hq
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    complexShift_hom_f]
  rw [Category.assoc, Category.assoc, shift_formula]
  simp only [Linear.comp_units_smul, Category.assoc]
  have hmap := homComplexFunctor_map_f_π (R := podReindexingRing l E X s)
    ((complexShift l E g s a).inv.app P) ((complexShift l E g s b).hom.app I)
    r t (t+r) rfl
  simp only [HomologicalComplex.comp_f, Category.assoc, complexShift_hom_f,
    complexShift_inv_f] at hmap
  erw [hmap]
  have hid := SheafOfModules.homObjMap_id (R := podReindexingRing l E X s)
    (M := ((podReindexingComplexFunctor l E g s).obj P).X (t + a))
    (N := ((podReindexingComplexFunctor l E g s).obj I).X (t + r + b))
  erw [hid, Category.comp_id, Category.id_comp]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  erw [hom_units]
  change (a * r).negOnePow •
      (((proj l E X s
        ((podReindexingComplexFunctor l E g s).obj (P⟦a⟧))
        ((podReindexingComplexFunctor l E g s).obj (I⟦b⟧))
        r t (t+r) rfl).val.app U
          (((c.chain (P⟦a⟧) (I⟦b⟧)).hom.f r).val.app U z)).app V).hom x =
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I)
      (r+(b-a)) (t+a) (t+r+b) (by omega)).val.app U
        (((c.chain P I).hom.f (r+(b-a))).val.app U
          (((sY.iso P I a b).hom.f r).val.app
            (op ((proEtaleIsoPostcompose g).obj U.unop)) z))).app V).hom x
  have hleft := chain_projection' l E g s c (P⟦a⟧) (I⟦b⟧)
    r t (t + r) rfl U V z x
  have hright := chain_projection' l E g s c P I
    (r + (b - a)) (t + a) (t + r + b) (by omega) U V
    (((sY.iso P I a b).hom.f r).val.app
      (op ((proEtaleIsoPostcompose g).obj U.unop)) z) x
  have hy := congrArg
    (fun f ↦ ((f.val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) z).app
      (op (Over.mk ((proEtaleIsoPostcompose g).map V.unop.hom)))).hom x)
    (shift_formula l E Y s sY P I a b r t)
  have hs := hom_units l E Y s
    (proj l E Y s (P⟦a⟧) (I⟦b⟧) r t (t + r) rfl) (a * r).negOnePow
    (op ((proEtaleIsoPostcompose g).obj U.unop)) z
    (op (Over.mk ((proEtaleIsoPostcompose g).map V.unop.hom))) x
  exact (congrArg ((a * r).negOnePow • ·) hleft).trans
    ((hy.trans hs).symm.trans hright.symm)

end WeilConjectures.PodReindexingCoherence
