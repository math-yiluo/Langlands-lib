/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import WeilConjectures.Algebra.Homology.BifunctorHomComplex

/-!
# The hom complex of a bifunctor commutes with shifts

Let `H : Cᵒᵖ ⥤ D ⥤ E` be a bifunctor and `Y` a cochain complex in `D`. The hom complex
`K ↦ bifunctorHomObj H K Y` (`CochainComplex.bifunctorHomObj`) is contravariant in `K` and
turns shifts into opposite shifts: for `a + b = 0` there is an isomorphism
`Hom_H(K, Y)⟦b⟧ ≅ Hom_H(K⟦a⟧, Y)` (`CochainComplex.bifunctorHomShiftIso`), which on the factor
`H(K^{p + a}, Y^q)` is the sign `(-1)^(a p + a (a + 1) / 2)`. These isomorphisms make the functor
`K ↦ op Hom_H(K, Y)` from cochain complexes to the opposite category of cochain complexes, the
latter with the shift of `CategoryTheory.Pretriangulated.Opposite`, commute with the shifts
(`CochainComplex.bifunctorHomOpFunctor`).

This is the first step towards the exactness of the derived hom `RHom(-, L)`, used for the
Verdier dual of Weil complexes (blueprint `theorem-verdier-biduality`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated Pretriangulated.Opposite

namespace CochainComplex

open HomComplex

variable {C D E : Type*} [Category C] [Category D] [Category E] [Preadditive C] [Preadditive D]
  [Preadditive E] [HasCountableProducts E] (H : Cᵒᵖ ⥤ D ⥤ E)
  [∀ X, (H.obj X).Additive] [H.Additive]

/-- The sign `(-1)^(a p + a (a + 1) / 2)` of the commutation of hom complexes with shifts, on the
factor of `Hom_H(K⟦a⟧, Y)` indexed by `p`. -/
def bifunctorHomShiftSign (a p : ℤ) : ℤˣ :=
  (a * p + a * (a + 1) / 2).negOnePow

/-- Closes an equality `(-1)^x = (-1)^y` between products of signs `Int.negOnePow`, by deciding
the parity of `x - y`. -/
macro "sign_tac" : tactic => `(tactic| (
  simp only [bifunctorHomShiftSign, ← Int.negOnePow_add, Units.val_mul]
  rw [Int.negOnePow_eq_iff]
  ring_nf
  simp [parity_simps]))

lemma bifunctorHomShiftSign_succ (a p : ℤ) :
    bifunctorHomShiftSign a (p + 1) = a.negOnePow * bifunctorHomShiftSign a p := by
  rw [bifunctorHomShiftSign, bifunctorHomShiftSign, ← Int.negOnePow_add]
  congr 1
  ring

lemma bifunctorHomShiftSign_add (a b p : ℤ) :
    bifunctorHomShiftSign (a + b) p =
      bifunctorHomShiftSign b p * bifunctorHomShiftSign a (p + b) := by
  rw [bifunctorHomShiftSign, bifunctorHomShiftSign, bifunctorHomShiftSign, ← Int.negOnePow_add]
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self a
  obtain ⟨l, hl⟩ := Int.even_mul_succ_self b
  have e : (a + b) * (a + b + 1) = a * (a + 1) + b * (b + 1) + 2 * (a * b) := by ring
  rw [e, hk, hl]
  have h₁ : (k + k + (l + l) + 2 * (a * b)) / 2 = k + l + a * b := by lia
  have h₂ : (k + k) / 2 = k := by lia
  have h₃ : (l + l) / 2 = l := by lia
  rw [h₁, h₂, h₃]
  congr 1
  ring

lemma bifunctorHomShiftSign_one (p : ℤ) : bifunctorHomShiftSign 1 p = (p + 1).negOnePow := by
  rw [bifunctorHomShiftSign]
  congr 1
  lia

@[simp]
lemma bifunctorHomShiftSign_zero (p : ℤ) : bifunctorHomShiftSign 0 p = 1 := by
  simp [bifunctorHomShiftSign]

variable {H}

/-- Changing the first index of a projection of the hom complex along an equality. -/
@[reassoc]
lemma bifunctorHomπ_congr_left (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ)
    (n p₁ p₂ q : ℤ) (h₁ : p₁ + n = q) (h₂ : p₂ + n = q) (hp : p₂ = p₁) :
    bifunctorHomπ H K Y n p₁ q h₁ ≫ (H.map (K.XIsoOfEq hp).hom.op).app _ =
      bifunctorHomπ H K Y n p₂ q h₂ := by
  subst hp
  simp

/-- Changing the degree of a projection of the hom complex along an equality. -/
@[reassoc]
lemma bifunctorHomObj_XIsoOfEq_hom_π (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ)
    (n₁ n₂ p q : ℤ) (hn : n₁ = n₂) (h₂ : p + n₂ = q) :
    ((bifunctorHomObj H K Y).XIsoOfEq hn).hom ≫ bifunctorHomπ H K Y n₂ p q h₂ =
      bifunctorHomπ H K Y n₁ p q (by lia) := by
  subst hn
  simp

/-- Changing the first index of a projection of the hom complex, through the identification
`(K⟦a⟧)^i = K^{i + a}`. -/
@[reassoc]
lemma bifunctorHomπ_shiftFunctorObjXIso_inv (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ)
    (a n i p q : ℤ) (h₁ : i + a + n = q) (h : p + n = q) (hm : p = i + a) :
    bifunctorHomπ H K Y n (i + a) q h₁ ≫
        (H.map (K.shiftFunctorObjXIso a i p hm).inv.op).app _ =
      bifunctorHomπ H K Y n p q h := by
  subst hm
  change bifunctorHomπ H K Y n (i + a) q h₁ ≫ (H.map (𝟙 (op (K.X (i + a))))).app _ = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, comp_id]

/-- Changing the first index of a projection of the hom complex of a shifted complex, through
the identification `(K⟦a⟧)^i = K^{i + a}`. -/
@[reassoc]
lemma bifunctorHomπ_shift_shiftFunctorObjXIso_inv (K : CochainComplex C ℤ)
    (Y : CochainComplex D ℤ) (a n i j q : ℤ) (h₁ : i + n = q) (h : j + n = q)
    (hm : j + a = i + a) :
    bifunctorHomπ H (K⟦a⟧) Y n i q h₁ ≫
        (H.map (K.shiftFunctorObjXIso a i (j + a) hm).inv.op).app _ =
      bifunctorHomπ H (K⟦a⟧) Y n j q h := by
  obtain rfl : i = j := by lia
  change bifunctorHomπ H (K⟦a⟧) Y n i q h₁ ≫ (H.map (𝟙 (op ((K⟦a⟧).X i)))).app _ = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, comp_id]

omit [∀ X, (H.obj X).Additive] [HasCountableProducts E] [Preadditive D] in
@[simp]
lemma map_units_smul_op_app {X X' : C} (u : ℤˣ) (f : X ⟶ X') (Z : D) :
    (H.map (u • f).op).app Z = u • (H.map f.op).app Z := by
  rw [Units.smul_def, Units.smul_def, op_zsmul, Functor.map_zsmul, NatTrans.app_zsmul]

variable (H)

/-- The components of `CochainComplex.bifunctorHomShiftIso`. -/
noncomputable def bifunctorHomShiftXIso (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ)
    (a b : ℤ) (h : a + b = 0) (m : ℤ) :
    ((bifunctorHomObj H K Y)⟦b⟧).X m ≅ (bifunctorHomObj H (K⟦a⟧) Y).X m where
  hom := bifunctorHomLift H (K⟦a⟧) Y m fun p q hpq ↦
    bifunctorHomShiftSign a p • bifunctorHomπ H K Y (m + b) (p + a) q (by lia)
  inv := bifunctorHomLift H K Y (m + b) fun p q hpq ↦
    bifunctorHomShiftSign a (p - a) • (bifunctorHomπ H (K⟦a⟧) Y m (p - a) q (by lia) ≫
      (H.map (K.shiftFunctorObjXIso a (p - a) p (by lia)).inv.op).app _)
  hom_inv_id := by
    refine bifunctorHomObj_hom_ext fun p q hpq ↦ ?_
    rw [assoc, bifunctorHomLift_π, Linear.comp_units_smul, bifunctorHomLift_π_assoc,
      Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul, id_comp]
    exact bifunctorHomπ_shiftFunctorObjXIso_inv (H := H) K Y a (m + b) (p - a) p q _ hpq _
  inv_hom_id := by
    refine bifunctorHomObj_hom_ext fun p q hpq ↦ ?_
    have hs : bifunctorHomShiftSign a p * bifunctorHomShiftSign a (p + a - a) = 1 := by
      rw [show p + a - a = p by lia, Int.units_mul_self]
    rw [assoc, bifunctorHomLift_π, Linear.comp_units_smul]
    erw [bifunctorHomLift_π]
    rw [smul_smul, hs, one_smul, id_comp]
    exact bifunctorHomπ_shift_shiftFunctorObjXIso_inv (H := H) K Y a m (p + a - a) p q _ hpq _

@[reassoc (attr := simp)]
lemma bifunctorHomShiftXIso_hom_π (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ)
    (a b : ℤ) (h : a + b = 0) (m p q : ℤ) (hpq : p + m = q) :
    (bifunctorHomShiftXIso H K Y a b h m).hom ≫ bifunctorHomπ H (K⟦a⟧) Y m p q hpq =
      bifunctorHomShiftSign a p • bifunctorHomπ H K Y (m + b) (p + a) q (by lia) := by
  simp only [bifunctorHomShiftXIso, bifunctorHomLift_π]

/-- The commutation of the hom complex with the shifts: for `a + b = 0`, the isomorphism
`Hom_H(K, Y)⟦b⟧ ≅ Hom_H(K⟦a⟧, Y)` which is the sign `bifunctorHomShiftSign a p` on the factor
`H(K^{p + a}, Y^q)`. -/
noncomputable def bifunctorHomShiftIso (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ)
    (a b : ℤ) (h : a + b = 0) :
    (bifunctorHomObj H K Y)⟦b⟧ ≅ bifunctorHomObj H (K⟦a⟧) Y :=
  HomologicalComplex.Hom.isoOfComponents (bifunctorHomShiftXIso H K Y a b h) (by
    intro m m' hmm'
    simp only [ComplexShape.up_Rel] at hmm'
    subst hmm'
    obtain rfl : b = -a := by lia
    refine bifunctorHomObj_hom_ext fun p q hpq ↦ ?_
    rw [assoc, bifunctorHomObj_d_π H (K⟦a⟧) Y m (m + 1) p q hpq (q - 1) (p + 1) (by lia)
      (by lia), assoc, bifunctorHomShiftXIso_hom_π, shiftFunctor_obj_d']
    simp only [Linear.comp_units_smul, Preadditive.comp_sub, bifunctorHomShiftXIso_hom_π_assoc,
      Linear.units_smul_comp, shiftFunctor_obj_d', map_units_smul_op_app]
    rw [bifunctorHomObj_d_π H K Y (m + -a) (m + 1 + -a) (p + a) q (by lia) (q - 1)
      (p + 1 + a) (by lia) (by lia)]
    simp only [smul_sub, smul_smul]
    congr 2
    all_goals sign_tac)

@[reassoc (attr := simp)]
lemma bifunctorHomShiftIso_hom_f_π (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ)
    (a b : ℤ) (h : a + b = 0) (m p q : ℤ) (hpq : p + m = q) :
    (bifunctorHomShiftIso H K Y a b h).hom.f m ≫ bifunctorHomπ H (K⟦a⟧) Y m p q hpq =
      bifunctorHomShiftSign a p • bifunctorHomπ H K Y (m + b) (p + a) q (by lia) :=
  bifunctorHomShiftXIso_hom_π H K Y a b h m p q hpq

variable {H} in
/-- The isomorphisms `CochainComplex.bifunctorHomShiftIso` are natural in the first variable. -/
@[reassoc]
lemma bifunctorHomShiftIso_hom_naturality {K K' : CochainComplex C ℤ} (f : K ⟶ K')
    (Y : CochainComplex D ℤ) (a b : ℤ) (h : a + b = 0) :
    (bifunctorHomMapLeft (H := H) (Y := Y) f)⟦b⟧' ≫ (bifunctorHomShiftIso H K Y a b h).hom =
      (bifunctorHomShiftIso H K' Y a b h).hom ≫ bifunctorHomMapLeft (f⟦a⟧') := by
  ext m p q hpq
  simp

variable (Y : CochainComplex D ℤ)

/-- The hom complex `K ↦ op Hom_H(K, Y)`, as a functor from cochain complexes to the opposite
category of cochain complexes. -/
@[simps]
noncomputable def bifunctorHomOpFunctor : CochainComplex C ℤ ⥤ (CochainComplex E ℤ)ᵒᵖ where
  obj K := op (bifunctorHomObj H K Y)
  map f := (bifunctorHomMapLeft f).op
  map_id K := by rw [bifunctorHomMapLeft_id, op_id]
  map_comp f g := by rw [bifunctorHomMapLeft_comp, op_comp]

omit [HasCountableProducts E] in
@[simp]
lemma shiftFunctorOpIso_hom_app_neg (n : ℤ) (h : n + -n = 0) (X : (CochainComplex E ℤ)ᵒᵖ) :
    (shiftFunctorOpIso (CochainComplex E ℤ) n (-n) h).hom.app X = 𝟙 _ :=
  rfl

omit [HasCountableProducts E] in
@[simp]
lemma shiftFunctorOpIso_inv_app_zero (h : (0 : ℤ) + 0 = 0) (X : (CochainComplex E ℤ)ᵒᵖ) :
    (shiftFunctorOpIso (CochainComplex E ℤ) 0 0 h).inv.app X = 𝟙 _ :=
  rfl

omit [HasCountableProducts E] in
@[simp]
lemma shiftFunctorOpIso_inv_app_neg (n : ℤ) (h : n + -n = 0) (X : (CochainComplex E ℤ)ᵒᵖ) :
    (shiftFunctorOpIso (CochainComplex E ℤ) n (-n) h).inv.app X = 𝟙 _ :=
  rfl

/-- The commutation of `CochainComplex.bifunctorHomOpFunctor` with the shift by `n`. -/
noncomputable def bifunctorHomOpFunctorCommShiftIso (n : ℤ) :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) n ⋙ bifunctorHomOpFunctor H Y ≅
      bifunctorHomOpFunctor H Y ⋙ CategoryTheory.shiftFunctor (CochainComplex E ℤ)ᵒᵖ n :=
  NatIso.ofComponents (fun K ↦ (bifunctorHomShiftIso H K Y n (-n) (add_neg_cancel n)).op)
    (fun {K K'} f ↦ by
    apply Quiver.Hom.unop_inj
    simp only [Functor.comp_map, bifunctorHomOpFunctor_map, Iso.op_hom,
      shiftFunctorOpIso_inv_app_neg, shiftFunctor_op_map _ n (-n),
      shiftFunctorOpIso_hom_app_neg, unop_comp, Quiver.Hom.unop_op, assoc]
    erw [unop_id, unop_id]
    repeat erw [id_comp]
    exact (bifunctorHomShiftIso_hom_naturality f Y n (-n) _).symm)

noncomputable instance : (bifunctorHomOpFunctor H Y).CommShift ℤ where
  commShiftIso := bifunctorHomOpFunctorCommShiftIso H Y
  commShiftIso_zero := by
    ext : 2
    funext K
    apply Quiver.Hom.unop_inj
    simp only [Functor.CommShift.isoZero_hom_app, bifunctorHomOpFunctorCommShiftIso,
      NatIso.ofComponents_hom_app, Iso.op_hom, Quiver.Hom.unop_op, unop_comp,
      bifunctorHomOpFunctor_map, shiftFunctorZero_op_inv_app, shiftFunctorOpIso_inv_app_zero]
    erw [unop_id, id_comp]
    ext m : 1
    refine bifunctorHomObj_hom_ext fun p q hpq ↦ ?_
    simp only [HomologicalComplex.comp_f, assoc, bifunctorHomShiftIso_hom_f_π,
      bifunctorHomShiftSign_zero, one_smul, bifunctorHomMapLeft_f_π, shiftFunctorZero_hom_app_f]
    rw [bifunctorHomπ_congr_left (h₂ := by lia)]
    erw [bifunctorHomObj_XIsoOfEq_hom_π]
    rfl
  commShiftIso_add a b := by
    ext : 2
    funext K
    apply Quiver.Hom.unop_inj
    rw [Functor.CommShift.isoAdd_hom_app, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
      ← shiftFunctorAdd'_eq_shiftFunctorAdd,
      shiftFunctorAdd'_op_inv_app _ a b (a + b) rfl (-a) (-b) (-(a + b)) (by lia) (by lia) (by lia),
      shiftFunctor_op_map _ b (-b)]
    simp only [bifunctorHomOpFunctorCommShiftIso, NatIso.ofComponents_hom_app, Iso.op_hom,
      unop_comp, Quiver.Hom.unop_op, bifunctorHomOpFunctor_map, shiftFunctorOpIso_inv_app_neg,
      shiftFunctorOpIso_hom_app_neg, assoc]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [unop_id]
    repeat erw [id_comp]
    ext m : 1
    refine bifunctorHomObj_hom_ext fun p q hpq ↦ ?_
    simp only [HomologicalComplex.comp_f, assoc, bifunctorHomShiftIso_hom_f_π,
      bifunctorHomMapLeft_f_π, shiftFunctorAdd'_hom_app_f', shiftFunctor_map_f']
    erw [bifunctorHomShiftIso_hom_f_π_assoc]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp]
    erw [bifunctorHomShiftIso_hom_f_π_assoc]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]
    rw [bifunctorHomπ_congr_left (h₂ := by lia)]
    erw [bifunctorHomObj_XIsoOfEq_hom_π]
    rw [← bifunctorHomShiftSign_add]

@[simp]
lemma bifunctorHomOpFunctor_commShiftIso_hom_app (n : ℤ) (K : CochainComplex C ℤ) :
    ((bifunctorHomOpFunctor H Y).commShiftIso n).hom.app K =
      (bifunctorHomShiftIso H K Y n (-n) (add_neg_cancel n)).hom.op :=
  rfl

@[simp]
lemma bifunctorHomOpFunctor_commShiftIso_inv_app (n : ℤ) (K : CochainComplex C ℤ) :
    ((bifunctorHomOpFunctor H Y).commShiftIso n).inv.app K =
      (bifunctorHomShiftIso H K Y n (-n) (add_neg_cancel n)).inv.op :=
  rfl

end CochainComplex
