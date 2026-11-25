/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChange.Iterate
public import WeilConjectures.TraceFormula.ShriekTraceFunction

/-!

# The Weil lower shriek commutes with the iterates

Let `f : X ⟶ Y` be a morphism of separated schemes of finite type over `Spec k`, with
automorphisms `e_X`, `e_Y` such that `e_X ≫ f = f ≫ e_Y`. For a Weil object `(K, φ)` for `e_X`,
the iterate of the lower shriek `Rf_!^Weil (K, φ)` is the lower shriek, for `e_X^{n+1}` and
`e_Y^{n+1}`, of the iterate `(K, φ^{(n+1)})`: both are `Rf_! K`, and the two structure
isomorphisms agree by the horizontal pasting law of the compact-support base change
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`),
the Frobenius square of `e^{n+2} = e^{n+1} ≫ e` being the pasting of those of `e^{n+1}` and `e`.

The general statement is `CategoryTheory.Iso.powSuccStr_hom_eq_of_isPullback`: a functor `H`
with comparison isomorphisms `H ⋙ Q g_Y ≅ P g_X ⋙ H` for the cartesian squares
`g_X ≫ f = f ≫ g_Y`, compatible with horizontal pasting and the composition isomorphisms,
commutes with the iterated structure isomorphisms.

## Main definitions

- `CategoryTheory.Iso.mapOfNatIsoPowSuccIsoOfIsPullback`: the generic comparison of the iterate
  of a transported algebra with the transport of the iterate.
- `ProEtale.CondensedRing.weilLowerShriekPowSuccIso`: the isomorphism
  `(Rf_!^Weil (K, φ))^{(n+1)} ≅ Rf_!^Weil (K, φ^{(n+1)})` of Weil objects for `e_Y^{n+1}`,
  given by the identity of `Rf_! K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {C : Type*} [Category C] {X Y : C} (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y}

/-- A cartesian square `e_X ≫ f = f ≫ e_Y` along automorphisms induces cartesian squares
`e_X^{n+1} ≫ f = f ≫ e_Y^{n+1}`, by horizontal pasting. -/
theorem IsPullback.powSucc (hf : IsPullback eX.hom f f eY.hom) (n : ℕ) :
    IsPullback (eX.pow (n + 1)).hom f f (eY.pow (n + 1)).hom := by
  induction n with
  | zero => simpa using hf
  | succ n ih => exact ih.paste_horiz hf

/-- Cancelling `F (α⁻¹_K) ≫ F (α_K)` at the end of a composite of four morphisms. -/
lemma Functor.comp_comp_comp_map_inv_app_comp_map_hom_app {D E : Type*} [Category D] [Category E]
    {G G' : C ⥤ D} (F : D ⥤ E) (α : G ≅ G') (K : C) {Z₀ Z₁ Z₂ : E} (a : Z₀ ⟶ Z₁) (b : Z₁ ⟶ Z₂)
    (c : Z₂ ⟶ F.obj (G'.obj K)) :
    (a ≫ b ≫ c ≫ F.map (α.inv.app K)) ≫ F.map (α.hom.app K) = a ≫ b ≫ c := by
  simp

namespace Iso

variable {D E : Type*} [Category D] [Category E]

/-- A functor `H : D ⥤ E` commutes with the iterated structure isomorphisms, for families `P` and
`Q` of endofunctors indexed by the endomorphisms of two objects `X` and `Y`: let
`h s : H ⋙ Q g_Y ≅ P g_X ⋙ H` be comparison isomorphisms for the cartesian squares
`s : g_X ≫ f = f ≫ g_Y`, compatible with horizontal pasting and the composition isomorphisms.
Then for `ψ = (h e).app a ≫ H φ`, the iterate `ψ^{(n+1)}` is `(h e^{n+1}).app a ≫ H φ^{(n+1)}`. -/
theorem powSuccStr_hom_eq_of_isPullback (hf : IsPullback eX.hom f f eY.hom)
    (P : (X ⟶ X) → D ⥤ D) (compP : ∀ g g' : X ⟶ X, P (g ≫ g') ≅ P g' ⋙ P g)
    (Q : (Y ⟶ Y) → E ⥤ E) (compQ : ∀ g g' : Y ⟶ Y, Q (g ≫ g') ≅ Q g' ⋙ Q g) (H : D ⥤ E)
    (h : ∀ {gX : X ⟶ X} {gY : Y ⟶ Y}, IsPullback gX f f gY → (H ⋙ Q gY ≅ P gX ⋙ H))
    (hcomp : ∀ {gX gX' : X ⟶ X} {gY gY' : Y ⟶ Y} (s : IsPullback gX f f gY)
      (s' : IsPullback gX' f f gY') (a : D),
      (h (s.paste_horiz s')).hom.app a ≫ H.map ((compP gX gX').hom.app a) =
        (compQ gY gY').hom.app (H.obj a) ≫ (Q gY).map ((h s').hom.app a) ≫
          (h s).hom.app ((P gX').obj a))
    {a : D} (φ : (P eX.hom).obj a ≅ a) (ψ : (Q eY.hom).obj (H.obj a) ≅ H.obj a)
    (hψ : ψ.hom = (h hf).hom.app a ≫ H.map φ.hom) (n : ℕ) :
    (eY.powSuccStr Q compQ ψ n).hom =
      (h (hf.powSucc eX eY n)).hom.app a ≫ H.map (eX.powSuccStr P compP φ n).hom := by
  induction n with
  | zero =>
    have key : ∀ {gX gX' : X ⟶ X} {gY gY' : Y ⟶ Y} (hX : gX = gX') (hY : gY = gY')
        (s : IsPullback gX f f gY) (s' : IsPullback gX' f f gY'),
        eqToHom (congrArg (fun g ↦ (Q g).obj (H.obj a)) hY) ≫ (h s').hom.app a =
          (h s).hom.app a ≫ H.map (eqToHom (congrArg (fun g ↦ (P g).obj a) hX)) := by
      rintro gX _ gY _ rfl rfl s s'
      simp
    rw [powSuccStr_zero, powSuccStr_zero]
    simp only [Iso.trans_hom, eqToIso.hom, Functor.map_comp, hψ]
    exact (reassoc_of% key (Category.id_comp eX.hom) (Category.id_comp eY.hom) _ hf) _
  | succ n ih =>
    change (compQ (eY.pow (n + 1)).hom eY.hom).hom.app (H.obj a) ≫
        (Q (eY.pow (n + 1)).hom).map ψ.hom ≫ (eY.powSuccStr Q compQ ψ n).hom =
      (h ((hf.powSucc eX eY n).paste_horiz hf)).hom.app a ≫
        H.map ((compP (eX.pow (n + 1)).hom eX.hom).hom.app a ≫
          (P (eX.pow (n + 1)).hom).map φ.hom ≫ (eX.powSuccStr P compP φ n).hom)
    have nat := (h (hf.powSucc eX eY n)).hom.naturality φ.hom
    simp only [Functor.comp_map] at nat
    rw [ih, hψ, Functor.map_comp_assoc, reassoc_of% nat, Functor.map_comp, Functor.map_comp,
      reassoc_of% (hcomp (hf.powSucc eX eY n) hf a)]

/-- The transport along `H` of the iterate of an algebra is the iterate of its transport, for
comparison isomorphisms `h s : H ⋙ Q g_Y ≅ P g_X ⋙ H` indexed by the cartesian squares
`g_X ≫ f = f ≫ g_Y` (`powSuccStr_hom_eq_of_isPullback`): for an algebra `(a, φ)` for `P e_X`,
the iterate for `Q e_Y^{n+1}` of `(H a, (h e).app a ≪≫ H φ)` is isomorphic, through the identity
of `H a`, to `(H a, (h e^{n+1}).app a ≪≫ H φ^{(n+1)})`. -/
noncomputable def mapOfNatIsoPowSuccIsoOfIsPullback (hf : IsPullback eX.hom f f eY.hom)
    (P : (X ⟶ X) → D ⥤ D) (compP : ∀ g g' : X ⟶ X, P (g ≫ g') ≅ P g' ⋙ P g)
    (Q : (Y ⟶ Y) → E ⥤ E) (compQ : ∀ g g' : Y ⟶ Y, Q (g ≫ g') ≅ Q g' ⋙ Q g) (H : D ⥤ E)
    (h : ∀ {gX : X ⟶ X} {gY : Y ⟶ Y}, IsPullback gX f f gY → (H ⋙ Q gY ≅ P gX ⋙ H))
    (hcomp : ∀ {gX gX' : X ⟶ X} {gY gY' : Y ⟶ Y} (s : IsPullback gX f f gY)
      (s' : IsPullback gX' f f gY') (a : D),
      (h (s.paste_horiz s')).hom.app a ≫ H.map ((compP gX gX').hom.app a) =
        (compQ gY gY').hom.app (H.obj a) ≫ (Q gY).map ((h s').hom.app a) ≫
          (h s).hom.app ((P gX').obj a))
    (A : IsoAlgebra (P eX.hom)) (n : ℕ) :
    IsoAlgebra.mk ((IsoAlgebra.mapOfNatIso (h hf)).obj A).carrier
        (eY.powSuccStr Q compQ ((IsoAlgebra.mapOfNatIso (h hf)).obj A).str n) ≅
      (IsoAlgebra.mapOfNatIso (h (hf.powSucc eX eY n))).obj
        (IsoAlgebra.mk A.carrier (eX.powSuccStr P compP A.str n)) :=
  IsoAlgebra.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id, ← IsoAlgebra.str_hom,
      ← IsoAlgebra.str_hom, IsoAlgebra.mk_str, IsoAlgebra.mapOfNatIso_obj_str]
    exact (powSuccStr_hom_eq_of_isPullback eX eY hf P compP Q compQ H h hcomp A.str _
      rfl n).symm)

/-- The underlying morphism of `mapOfNatIsoPowSuccIsoOfIsPullback` is the identity. -/
lemma mapOfNatIsoPowSuccIsoOfIsPullback_hom_hom_f (hf : IsPullback eX.hom f f eY.hom)
    (P : (X ⟶ X) → D ⥤ D) (compP : ∀ g g' : X ⟶ X, P (g ≫ g') ≅ P g' ⋙ P g)
    (Q : (Y ⟶ Y) → E ⥤ E) (compQ : ∀ g g' : Y ⟶ Y, Q (g ≫ g') ≅ Q g' ⋙ Q g) (H : D ⥤ E)
    (h : ∀ {gX : X ⟶ X} {gY : Y ⟶ Y}, IsPullback gX f f gY → (H ⋙ Q gY ≅ P gX ⋙ H))
    (hcomp : ∀ {gX gX' : X ⟶ X} {gY gY' : Y ⟶ Y} (s : IsPullback gX f f gY)
      (s' : IsPullback gX' f f gY') (a : D),
      (h (s.paste_horiz s')).hom.app a ≫ H.map ((compP gX gX').hom.app a) =
        (compQ gY gY').hom.app (H.obj a) ≫ (Q gY).map ((h s').hom.app a) ≫
          (h s).hom.app ((P gX').obj a))
    (A : IsoAlgebra (P eX.hom)) (n : ℕ) :
    (mapOfNatIsoPowSuccIsoOfIsPullback eX eY hf P compP Q compQ H h hcomp A n).hom.hom.f =
      𝟙 (H.obj A.carrier) :=
  rfl

end Iso

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The compact-support base change along the Frobenius squares is compatible with the
composition isomorphisms of the derived pullbacks: for cartesian squares
`g_X ≫ f = f ≫ g_Y` and `g'_X ≫ f = f ≫ g'_Y`, the base change of the pasted square, followed by
`Rf_!` of the composition isomorphism, is the composition isomorphism followed by the two base
changes (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`). -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz_comp {f : X ⟶ Y}
    {gX gX' : X ⟶ X} {gY gY' : Y ⟶ Y} (s : IsPullback gX f f gY) (s' : IsPullback gX' f f gY')
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (s.paste_horiz s')).app K ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ gX gX').hom.app
            K) =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ gY gY').hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ gY).map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s').app K) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ gX').obj K) := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ s s' K]
  exact Functor.comp_comp_comp_map_inv_app_comp_map_hom_app
    (boundedConstructibleLowerShriek ℓ f)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ gX gX') K _ _ _

variable {eX : X ≅ X} {eY : Y ≅ Y} {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

/-- **The Weil lower shriek commutes with the iterates**: for a Weil object `(K, φ)` for `e_X`,
the iterate `(Rf_!^Weil (K, φ))^{(n+1)}` is isomorphic, through the identity of `Rf_! K`, to the
lower shriek `Rf_!^Weil (K, φ^{(n+1)})` for `e_X^{n+1}` and `e_Y^{n+1}`. -/
noncomputable def weilLowerShriekPowSuccIso (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) :
    ((weilLowerShriek ℓ eX eY hf).obj K).powSucc ℓ n ≅
      (weilLowerShriek ℓ (eX.pow (n + 1)) (eY.pow (n + 1))
        (Iso.pow_hom_comp_eq_comp_pow_hom eX eY hf n)).obj (K.powSucc ℓ n) :=
  eX.mapOfNatIsoPowSuccIsoOfIsPullback eY (weilFrobeniusSquare eX eY hf)
    (fun g ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    (fun g g' ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g g')
    (fun g ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    (fun g g' ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g g')
    (boundedConstructibleLowerShriek ℓ f)
    (fun s ↦
      have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s
      asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s))
    (fun s s' K ↦ boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz_comp ℓ s s' K)
    K n

/-- The underlying morphism of `weilLowerShriekPowSuccIso` is the identity of `Rf_! K`. -/
@[simp]
lemma weilLowerShriekPowSuccIso_hom_hom_f (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) :
    (weilLowerShriekPowSuccIso ℓ hf K n).hom.hom.f =
      𝟙 ((boundedConstructibleLowerShriek ℓ f).obj K.carrier) :=
  Iso.mapOfNatIsoPowSuccIsoOfIsPullback_hom_hom_f _ _ _ _ _ _ _ _ _ _ K n

end AlgebraicGeometry.ProEtale.CondensedRing
