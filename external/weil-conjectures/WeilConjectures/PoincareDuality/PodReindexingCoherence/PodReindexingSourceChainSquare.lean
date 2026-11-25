/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData

/-! # Signed source reindexing of the Hom chain comparison

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.
The square is proved for any two source reindexings satisfying LeftFormula.
(blueprint: lem-pod-reindexing-source-chain-square)
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

private lemma source_hom_sections_ext (W : Scheme.{u}) (s : Option ℕ)
    {A B D : podReindexingModules l E W s}
    {f g : A ⟶ SheafOfModules.homObj (R := podReindexingRing l E W s) B D}
    (h : ∀ (U : W.ProEtᵒᵖ) (z : A.val.obj U) (V : (Over U.unop)ᵒᵖ)
      (x : B.val.obj (op V.unop.left)),
      ((f.val.app U z).app V).hom x = ((g.val.app U z).app V).hom x) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h U z V)

private theorem source_chain_conjugate {D : Type*} [Category D]
    {A B C D₀ E₀ : D} (e : A ≅ B) (e' : E₀ ≅ D₀)
    (f : B ⟶ C) (k : C ⟶ D₀) (h : A ⟶ E₀)
    (w : e.hom ≫ f ≫ k = h ≫ e'.hom) : f ≫ k ≫ e'.inv = e.inv ≫ h := by
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (f ≫ k ≫ e'.inv) = (e.hom ≫ f ≫ k) ≫ e'.inv := by
      simp only [Category.assoc]
    _ = (h ≫ e'.hom) ≫ e'.inv := congrArg (fun t ↦ t ≫ e'.inv) w
    _ = e.hom ≫ (e.inv ≫ h) := by
      simp only [Category.assoc, e'.hom_inv_id, Category.comp_id, e.hom_inv_id_assoc]

private lemma source_complexShift_projection
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (s : Option ℕ)
    (P I : K l E Y s) (a r p q : ℤ) (hpq : p + r = q) :
    (((podReindexingHom l E X s).map ((complexShift l E g s a).inv.app P).op).app
      ((podReindexingComplexFunctor l E g s).obj I)).f r ≫
        proj l E X s (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧)
          ((podReindexingComplexFunctor l E g s).obj I) r p q hpq =
      proj l E X s ((podReindexingComplexFunctor l E g s).obj (P⟦a⟧))
        ((podReindexingComplexFunctor l E g s).obj I) r p q hpq := by
  have hmap := homComplexFunctor_map_f_π (R := podReindexingRing l E X s)
    ((complexShift l E g s a).inv.app P)
    (𝟙 ((podReindexingComplexFunctor l E g s).obj I)) r p q hpq
  have him := ((podReindexingHom l E X s).obj
    (op (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧))).map_id
      ((podReindexingComplexFunctor l E g s).obj I)
  dsimp only [podReindexingHom] at him
  simp only [Functor.comp_obj] at hmap
  erw [him, Category.comp_id] at hmap
  simp only [complexShift_inv_f, HomologicalComplex.id_f] at hmap
  have hid := SheafOfModules.homObjMap_id (R := podReindexingRing l E X s)
    (M := ((podReindexingComplexFunctor l E g s).obj (P⟦a⟧)).X p)
    (N := ((podReindexingComplexFunctor l E g s).obj I).X q)
  erw [hid, Category.comp_id] at hmap
  exact hmap

private lemma source_chain_leftFormula
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s) (a : ℤ)
    (eY : (hom l E Y s P I)⟦-a⟧ ≅ hom l E Y s (P⟦a⟧) I)
    (hY : CategoryTheory.RingedHomUniverses.LeftFormula.{u + 1, u, u}
      (ProEt.topology Y) (podReindexingRing l E Y s) P I a eY)
    (r p q : ℤ) (hpq : p + r = q) :
    ((podReindexingComplexFunctor l E g s).map eY.hom).f r ≫
      (c.chain (P⟦a⟧) I).hom.f r ≫
        proj l E X s ((podReindexingComplexFunctor l E g s).obj (P⟦a⟧))
          ((podReindexingComplexFunctor l E g s).obj I) r p q hpq =
      (a * r).negOnePow • ((c.chain P I).hom.f (r + -a) ≫
        proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I) (r + -a) (p + a) q (by omega)) := by
  apply source_hom_sections_ext l E X s
  intro U z V x
  refine Eq.trans ?_ (hom_units l E X s
    ((c.chain P I).hom.f (r + -a) ≫
      proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I) (r + -a) (p + a) q (by omega))
    (a * r).negOnePow U z V x).symm
  change
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj (P⟦a⟧))
      ((podReindexingComplexFunctor l E g s).obj I) r p q hpq).val.app U
        (((c.chain (P⟦a⟧) I).hom.f r).val.app U
          ((eY.hom.f r).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) z))).app V).hom x =
      (a * r).negOnePow •
        (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I) (r + -a) (p+a) q (by omega)).val.app U
            (((c.chain P I).hom.f (r + -a)).val.app U z)).app V).hom x
  rw [chain_projection', chain_projection']
  have hy := congrArg
    (fun f ↦ ((f.val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) z).app
      (op (Over.mk ((proEtaleIsoPostcompose g).map V.unop.hom)))).hom x)
    (hY r p q hpq)
  have hs := hom_units l E Y s
    (proj l E Y s P I (r + -a) (p+a) q (by omega)) (a * r).negOnePow
    (op ((proEtaleIsoPostcompose g).obj U.unop)) z
    (op (Over.mk ((proEtaleIsoPostcompose g).map V.unop.hom))) x
  exact hy.trans hs


/-- The signed source reindexings commute with the fixed sectionwise chain comparison.
Source: Stacks 0A8X, 08JA and blueprint dual-Tate compatibility, Step 4.
Proof: project to every source degree and evaluate the resulting local Hom family.
The two LeftFormula identities give the same sign and chain_projection identifies
both remaining families, including their restrictions to every object over U.
(blueprint: lem-pod-reindexing-source-chain-square) -/
theorem source_chain_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s) (a : ℤ)
    (eY : (hom l E Y s P I)⟦-a⟧ ≅ hom l E Y s (P⟦a⟧) I)
    (eX : (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I))⟦-a⟧ ≅
      hom l E X s (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧)
        ((podReindexingComplexFunctor l E g s).obj I))
    (hY : CategoryTheory.RingedHomUniverses.LeftFormula.{u + 1, u, u}
      (ProEt.topology Y) (podReindexingRing l E Y s) P I a eY)
    (hX : CategoryTheory.RingedHomUniverses.LeftFormula.{u + 1, u, u}
      (ProEt.topology X) (podReindexingRing l E X s)
      ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) a eX) :
    (c.chain (P⟦a⟧) I).hom ≫
        ((podReindexingHom l E X s).map
          ((complexShift l E g s a).inv.app P).op).app
            ((podReindexingComplexFunctor l E g s).obj I) ≫ eX.inv =
      (podReindexingComplexFunctor l E g s).map eY.inv ≫
        (complexShift l E g s (-a)).hom.app (hom l E Y s P I) ≫
        ((c.chain P I).hom)⟦-a⟧' := by
  apply source_chain_conjugate ((podReindexingComplexFunctor l E g s).mapIso eY) eX
  apply HomologicalComplex.hom_ext
  intro r
  apply homComplex_hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Category.assoc,
    CochainComplex.shiftFunctor_map_f', complexShift_hom_f]
  rw [source_complexShift_projection, hX, Linear.comp_units_smul]
  exact source_chain_leftFormula l E g s SX SY TX TY c P I a eY hY r p q hpq

end WeilConjectures.PodReindexingCoherence
