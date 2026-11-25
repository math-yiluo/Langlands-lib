/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData

/-! # Existence of the signed chain shift presentations

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: new-pod-reindexing-chain-shift-presentations).

This is the presentation part of the chain-shift argument.  The remaining
reindexing square is recorded separately in
`PodReindexingChainShiftSquare`.
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

private lemma proj_transport (W : Scheme.{u}) (s : Option ℕ) (P I : K l E W s)
    (n n' p' p q' q : ℤ) (hn : n = n') (hp : p' = p) (hq : q' = q)
    (h : p' + n = q') (h' : p + n' = q) :
    ((hom l E W s P I).XIsoOfEq hn).hom ≫ proj l E W s P I n' p q h' =
      proj l E W s P I n p' q' h ≫
        SheafOfModules.homObjMap (R := podReindexingRing l E W s)
          (P.XIsoOfEq hp).inv (I.XIsoOfEq hq).hom := by
  subst n' p' q'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    SheafOfModules.homObjMap_id, Category.id_comp, Category.comp_id]

private theorem chainShift_exists (W : Scheme.{u})
    [EssentiallySmall.{u + 1} W.ProEt] (s : Option ℕ) :
    Nonempty (ChainShift l E W s) := by
  classical
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E W s)
  let J := ProEt.topology W
  let R := podReindexingRing l E W s
  obtain ⟨SL, hSL, _⟩ :=
    CategoryTheory.RingedHomUniverses.leftShift_existsUnique.{u + 1, u, u, u + 2} J R
  obtain ⟨SR, hSR, _⟩ :=
    CategoryTheory.RingedHomUniverses.rightShift_existsUnique.{u + 1, u, u, u + 2} J R
  have hL (P I : K l E W s) (a : ℤ) :=
    hSL (DerivedCategory.Q.obj P) P I (Iso.refl _) a
  have hR (P I : K l E W s) (b : ℤ) :=
    hSR (DerivedCategory.Q.obj P) P I (Iso.refl _) b
  choose eL heL hnormL using hL
  choose eR heR hnormR using hR
  let e (P I : K l E W s) (a b : ℤ) :
      hom l E W s (P⟦a⟧) (I⟦b⟧) ≅ (hom l E W s P I)⟦b-a⟧ :=
    (eL P (I⟦b⟧) a).symm ≪≫
      (shiftFunctor _ (-a)).mapIso (eR P I b).symm ≪≫
      (shiftFunctorAdd' _ b (-a) (b-a) (sub_eq_add_neg b a).symm).symm.app _
  refine ⟨{ iso := e, formula := ?_ }⟩
  intro P I a b r p
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
  apply (cancel_epi ((eL P (I⟦b⟧) a).hom.f r)).mp
  simp only [← Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f, Category.id_comp]
  rw [Linear.comp_units_smul, ← Category.assoc, heL P (I⟦b⟧) a r (p-a) ((p-a)+r) rfl]
  simp only [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul]
  apply (cancel_epi ((eR P I b).hom.f (r + -a))).mp
  simp only [← Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f, Category.id_comp]
  rw [heR P I b (r + -a) (p-a+a) (p-a+r) (by omega)]
  simp only [CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorObjXIso]
  exact proj_transport l E W s P I ((r + -a) + b) (r + (b-a))
    (p-a+a) p ((p-a+r)+b) (p+(r+(b-a))) (by omega) (by omega) (by omega)
    (by omega) rfl

set_option linter.unusedVariables false in
/-- Signed Hom-complex shift presentations exist on each of the two sites.

The construction uses the product projections of the Hom complex.  In degree
`r`, the component indexed by `p` is reindexed to `p-a` and multiplied by
`(-1)^(a*r)`.  The ratio of consecutive scalars is the sign in the Hom
 differential, so the projectionwise maps form chain isomorphisms.  This
statement is the first, strictly smaller part of Step 4.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: new-pod-reindexing-chain-shift-presentations). -/
theorem chain_shift_presentations
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∃ (sX : ChainShift l E X s) (sY : ChainShift l E Y s),
      True := by
  obtain ⟨sX⟩ := chainShift_exists l E X s
  obtain ⟨sY⟩ := chainShift_exists l E Y s
  exact ⟨sX, sY, trivial⟩

end WeilConjectures.PodReindexingCoherence
