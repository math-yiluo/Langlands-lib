/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite

/-!

# Reduction steps for the sheaf–function compatibility of the Weil lower shriek

For a morphism `f : X ⟶ Y` of separated schemes of finite type over a finite field `k` and
automorphisms `e_X`, `e_Y` with `e_X ≫ f = f ≫ e_Y`, the *sheaf–function compatibility*
(`ProEtale.CondensedRing.ShriekTraceFunctionAt`) is the identity
```
t_{n+1}(Rf_!^Weil K; ȳ) = ∑_{x̄ ↦ ȳ} t_{n+1}(K; x̄)
```
of `ProEtale.CondensedRing.weilShriekTraceFunction`, for one triple `(f, e_X, e_Y)`. This file
proves the formal reduction steps of its proof:

- the local trace only depends on the Weil object up to isomorphism
  (`ProEtale.CondensedRing.weilStalkTraceAlternatingSum_congr`);
- the lower shriek of Weil objects is compatible with composition
  (`ProEtale.CondensedRing.weilLowerShriekCompIso`), through the pasting law of the
  compact-support base change (blueprint `proposition-composition-base-change-rf-shriek`, item (2));
- the compatibility is stable under composition
  (`ProEtale.CondensedRing.shriekTraceFunctionAt_comp`): a fibration `X ⟶ Z ⟶ Y` reduces it to
  the two factors.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace CategoryTheory.Iso

variable {C : Type*} [Category C] {X Y : C} (e : X ≅ X) (e' : Y ≅ Y)

/-- A morphism intertwining two automorphisms intertwines their powers. -/
lemma pow_hom_comp_eq_comp_pow_hom {s : X ⟶ Y} (h : e.hom ≫ s = s ≫ e'.hom) (n : ℕ) :
    (e.pow (n + 1)).hom ≫ s = s ≫ (e'.pow (n + 1)).hom := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ _ (n + 1), pow_succ _ (n + 1), trans_hom, trans_hom, Category.assoc, h,
      ← Category.assoc, ih, Category.assoc]

end CategoryTheory.Iso

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The local trace only depends on the Weil object up to isomorphism. -/
lemma weilStalkTraceAlternatingSum_congr {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] {e : X ≅ X} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x)
    {K K' : WeilBoundedConstructible ℓ e.hom} (i : K ≅ K') :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx K =
      weilStalkTraceAlternatingSum ℓ (n + 1) x hx K' := by
  rw [weilStalkTraceAlternatingSum, weilStalkTraceAlternatingSum]
  exact finsum_congr fun j ↦ congrArg _
    (weilSheafStalkTrace_congr ℓ (n + 1) x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).mapIso i))

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) (eZ : Z ≅ Z)

/-- The *sheaf–function compatibility* of the Weil lower shriek along `f` for the automorphisms
`e_X`, `e_Y`: for every Weil object `K` for `e_X`, every `n` and every point `ȳ` of `Y` of degree
`n + 1`, `t_{n+1}(Rf_!^Weil K; ȳ) = ∑_{x̄ ↦ ȳ} t_{n+1}(K; x̄)`. It is the conclusion of
`weilShriekTraceFunction` for one triple `(f, e_X, e_Y)`. -/
def ShriekTraceFunctionAt {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom) : Prop :=
  ∀ (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) (y : frobeniusFixedPoints eY (n + 1)),
    weilStalkTraceAlternatingSum ℓ (n + 1) y.1 y.2.2 ((weilLowerShriek ℓ eX eY hf).obj K) =
      ∑ᶠ x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1},
        weilStalkTraceAlternatingSum ℓ (n + 1) x.1.1 x.1.2.2 K

variable {h : X ⟶ Z} {g : Z ⟶ Y} (hh : eX.hom ≫ h = h ≫ eZ.hom) (hg : eZ.hom ≫ g = g ≫ eY.hom)

omit [Finite k] [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
include hh hg in
/-- The composite of morphisms intertwining automorphisms intertwines them. -/
lemma comp_comm_of_comp_comm : eX.hom ≫ h ≫ g = (h ≫ g) ≫ eY.hom := by
  rw [← Category.assoc, hh, Category.assoc, hg, Category.assoc]

/-- **The lower shriek of Weil objects is compatible with composition**:
`R(h ≫ g)_!^Weil K ≅ Rg_!^Weil Rh_!^Weil K`, the composition isomorphism of the lower shriek,
compatible with the Frobenius structures by the pasting law of the compact-support base change
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert`, blueprint
`proposition-composition-base-change-rf-shriek`, item (2)). -/
noncomputable def weilLowerShriekCompIso (K : WeilBoundedConstructible ℓ eX.hom) :
    (weilLowerShriek ℓ eX eY (comp_comm_of_comp_comm eX eY eZ hh hg)).obj K ≅
      (weilLowerShriek ℓ eZ eY hg).obj ((weilLowerShriek ℓ eX eZ hh).obj K) :=
  ObjectProperty.isoMk _ (Algebra.isoMk
    ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ h g).app K.carrier) (by
      have hp : (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
          (weilFrobeniusSquare eX eY (comp_comm_of_comp_comm eX eY eZ hh hg))).app K.carrier =
          _ :=
        boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert ℓ
          (weilFrobeniusSquare eX eZ hh) (weilFrobeniusSquare eZ eY hg) K.carrier
      have nat := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h g).hom.naturality
        K.str.hom
      rw [Functor.comp_map] at nat
      rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, weilLowerShriek_obj_str,
        weilLowerShriek_obj_str, weilLowerShriek_obj_str]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, weilLowerShriekComparison_hom,
        Functor.map_comp, Category.assoc]
      rw [hp]
      simp only [Category.assoc, nat, Iso.inv_hom_id_app_assoc]
      rfl))

/-- A point `x̄` of `X` of degree `n + 1` maps to a point `x̄ ≫ h` of `Z` of degree `n + 1`. -/
noncomputable def frobeniusFixedPointsMap (n : ℕ) (x : frobeniusFixedPoints eX (n + 1)) :
    frobeniusFixedPoints eZ (n + 1) :=
  ⟨x.1 ≫ h.left, by rw [Category.assoc, Over.w h, x.2.1], by
    rw [Category.assoc, ← Over.comp_left,
      ← Iso.pow_hom_comp_eq_comp_pow_hom eX eZ hh n, Over.comp_left, ← Category.assoc,
      x.2.2, Category.assoc]⟩

/-- The points of `X` over a point `ȳ` of `Y` are the points of `X` over the points of `Z` over
`ȳ`. -/
noncomputable def frobeniusFixedPointsFiberEquiv (n : ℕ) (y : frobeniusFixedPoints eY (n + 1)) :
    {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ (h ≫ g).left = y.1} ≃
      Σ z : {z : frobeniusFixedPoints eZ (n + 1) // z.1 ≫ g.left = y.1},
        {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ h.left = z.1.1} where
  toFun x := ⟨⟨frobeniusFixedPointsMap eX eZ hh n x.1, by
    simpa only [frobeniusFixedPointsMap, Over.comp_left, Category.assoc] using x.2⟩, ⟨x.1, rfl⟩⟩
  invFun p := ⟨p.2.1, by rw [Over.comp_left, ← Category.assoc, p.2.2, p.1.2]⟩
  left_inv x := rfl
  right_inv := by
    rintro ⟨⟨z, hz⟩, ⟨x, hx⟩⟩
    obtain rfl : frobeniusFixedPointsMap eX eZ hh n x = z := Subtype.ext hx
    rfl

/-- **Fibrations**: the sheaf–function compatibility along `h : X ⟶ Z` and along `g : Z ⟶ Y`
gives it along `h ≫ g`, for automorphisms `e_X`, `e_Z` of finite order. -/
theorem shriekTraceFunctionAt_comp (heX : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X)
    (heZ : ∃ m : ℕ, eZ.pow (m + 1) = Iso.refl Z) (H₁ : ShriekTraceFunctionAt ℓ eX eZ hh)
    (H₂ : ShriekTraceFunctionAt ℓ eZ eY hg) :
    ShriekTraceFunctionAt ℓ eX eY (comp_comm_of_comp_comm eX eY eZ hh hg) := by
  intro K n y
  have h1 := weilStalkTraceAlternatingSum_congr ℓ n y.1 y.2.2 (weilLowerShriekCompIso ℓ eX eY eZ hh
      hg K)
  have h2 := H₂ ((weilLowerShriek ℓ eX eZ hh).obj K) n y
  refine h1.trans (h2.trans ?_)
  refine (finsum_congr fun z : {z : frobeniusFixedPoints eZ (n + 1) // z.1 ≫ g.left = y.1} ↦
    H₁ K n z.1).trans ?_
  classical
  have := finite_frobeniusFixedPoints_of_pow_eq_refl eX heX n
  have := finite_frobeniusFixedPoints_of_pow_eq_refl eZ heZ n
  let := Fintype.ofFinite (frobeniusFixedPoints eX (n + 1))
  let := Fintype.ofFinite (frobeniusFixedPoints eZ (n + 1))
  simp only [finsum_eq_sum_of_fintype]
  symm
  rw [← Fintype.sum_equiv (frobeniusFixedPointsFiberEquiv eX eY eZ hh n y).symm
    (fun p ↦ weilStalkTraceAlternatingSum ℓ (n + 1) p.2.1.1 p.2.1.2.2 K) _ fun _ ↦ rfl,
        Fintype.sum_sigma]

end AlgebraicGeometry.ProEtale.CondensedRing
