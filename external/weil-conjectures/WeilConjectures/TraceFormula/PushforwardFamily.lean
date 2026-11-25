/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PushforwardFamily
public import WeilConjectures.TraceFormula.PullbackFamily

/-!

# Base change for a family of pushforwards

Let `P` be a family of pullbacks `P f : D Y ⥤ D X` with composition isomorphisms
`c f g : P (f ≫ g) ≅ P g ⋙ P f` (`CategoryTheory.PullbackAssoc`), and `Q f : D X ⥤ D Y` right
adjoints `P f ⊣ Q f`. For a commutative square `g' ≫ f = f' ≫ g`, the base-change morphism
`Q f ⋙ P g ⟶ P g' ⋙ Q f'` (`CategoryTheory.pushforwardBaseChange`) is the exchange morphism of the
comparison `P g ⋙ P f' ≅ P f ⋙ P g'` of the composition isomorphisms
(`CategoryTheory.pullbackFamilySquareComparison`). This file proves:

- `CategoryTheory.pushforwardBaseChange_app_paste`: the pasting law of base-change morphisms of
  two horizontally adjacent squares;
- `CategoryTheory.Iso.powSuccStr_pushforwardBaseChange`: for `f : X ⟶ Y` with
  `e_X ≫ f = f ≫ e_Y`, the iterated structure isomorphism of the pushforward `Q f F` of an
  algebra `(F, φ)` for `P e_X` is the base change along `e_X^{n+1}`, `e_Y^{n+1}` followed by the
  pushforward of the iterated structure isomorphism of `F`;
- `Endofunctor.IsoAlgebra.nonempty_overPowSucc_mapOfNatIso_iso_of_eq`: the same as an isomorphism of
  algebras, for functors given through equations, so that it applies to the pushforward of Weil
  sheaves.

## Implementation notes

The statements are generic in the families `P` and `Q`. Instantiated directly for module objects on
the pro-étale sites, the elaborator and the kernel unfold the pullbacks while comparing terms that
are equal only up to unfolding (`WeilConjectures.TraceFormula.PullbackFamily`).

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : C → Type*} [∀ X, Category (D X)]
  {P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X}
  {c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f}
  {Q : ∀ {X Y : C}, (X ⟶ Y) → D X ⥤ D Y} (adj : ∀ {X Y : C} (f : X ⟶ Y), P f ⊣ Q f)

section Over

variable {T : C}

/-- **The iterated structure isomorphism of a pushforward**: for `f : X ⟶ Y` over `T` with
`e_X ≫ f = f ≫ e_Y` and an algebra `(F, φ)` for `P e_X`, the iterated structure isomorphism of the
pushforward `Q f F` with `P e_Y (Q f F) ⟶ Q f (P e_X F) ⟶ Q f F` (base change followed by
`Q f φ`) is the base change along `e_X^{n+1}`, `e_Y^{n+1}` followed by the pushforward of the
iterated structure isomorphism of `F`. -/
theorem Iso.powSuccStr_pushforwardBaseChange (hc : PullbackAssoc P c) {X Y : Over T}
    (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom) {F : D X.left}
    (φ : (P eX.hom.left).obj F ≅ F) (ψ : (P eY.hom.left).obj ((Q f.left).obj F) ≅ (Q f.left).obj F)
    (hψ : ψ.hom = (pushforwardBaseChange c adj (Over.left_comp_left_eq_of_comp_eq hf)).app F ≫
      (Q f.left).map φ.hom) (n : ℕ) :
    (eY.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) ψ n).hom =
      (pushforwardBaseChange c adj (Over.left_comp_left_eq_of_comp_eq
          (Iso.pow_hom_comp_eq_comp_pow_hom eX eY hf n))).app F ≫
        (Q f.left).map (eX.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) φ n).hom := by
  induction n with
  | zero =>
    have key : ∀ {gX gX' : X ⟶ X} {gY gY' : Y ⟶ Y} (hX : gX = gX') (hY : gY = gY')
        (s : gX.left ≫ f.left = f.left ≫ gY.left) (s' : gX'.left ≫ f.left = f.left ≫ gY'.left),
        eqToHom (congrArg (fun g : Y ⟶ Y ↦ (P g.left).obj ((Q f.left).obj F)) hY) ≫
            (pushforwardBaseChange c adj s').app F =
          (pushforwardBaseChange c adj s).app F ≫
            (Q f.left).map (eqToHom (congrArg (fun g : X ⟶ X ↦ (P g.left).obj F) hX)) := by
      rintro gX _ gY _ rfl rfl s s'
      simp
    rw [powSuccStr_zero, powSuccStr_zero]
    simp only [Iso.trans_hom, eqToIso.hom, Functor.map_comp, hψ]
    exact (reassoc_of% key (Category.id_comp eX.hom) (Category.id_comp eY.hom) _
      (Over.left_comp_left_eq_of_comp_eq hf)) _
  | succ n ih =>
    have hn := Over.left_comp_left_eq_of_comp_eq
      (Iso.pow_hom_comp_eq_comp_pow_hom eX eY hf n)
    have hf' := Over.left_comp_left_eq_of_comp_eq hf
    have nat := (pushforwardBaseChange c adj hn).naturality φ.hom
    simp only [Functor.comp_map] at nat
    change (c (eY.pow (n + 1)).hom.left eY.hom.left).hom.app ((Q f.left).obj F) ≫
        (P (eY.pow (n + 1)).hom.left).map ψ.hom ≫
        (eY.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) ψ n).hom =
      (pushforwardBaseChange c adj (show ((eX.pow (n + 1)).hom.left ≫ eX.hom.left) ≫ f.left =
          f.left ≫ ((eY.pow (n + 1)).hom.left ≫ eY.hom.left)
          by rw [Category.assoc, hf', ← Category.assoc, hn, Category.assoc])).app F ≫
        (Q f.left).map ((c (eX.pow (n + 1)).hom.left eX.hom.left).hom.app F ≫
          (P (eX.pow (n + 1)).hom.left).map φ.hom ≫
          (eX.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) φ n).hom)
    rw [ih, hψ, Functor.map_comp_assoc, reassoc_of% nat, Functor.map_comp, Functor.map_comp,
      ← pushforwardBaseChange_app_paste_assoc adj hc hf' hn]

/-- **The pushforward commutes with the iterated structures**, as an isomorphism of algebras:
for `f : X ⟶ Y` over `T` with `e_X ≫ f = f ≫ e_Y`, comparisons `β : Q f ⋙ P e_Y ≅ P e_X ⋙ Q f`
and `βₙ : Q f ⋙ P e_Y^{n+1} ≅ P e_X^{n+1} ⋙ Q f` given by the base-change morphisms, and an
algebra `F` for `P e_X`, the `(n + 1)`-st iterate of the transport of `F` along `β` is the
transport along `βₙ` of the `(n + 1)`-st iterate of `F`. The functors are given through
equations, so that concrete instances can use their own functors.

Implementation note: the categories are passed as variables, with their category instances,
together with `Sigma`-type equations to the generic ones, and the functors through `HEq`
hypotheses, as in `Endofunctor.IsoAlgebra.nonempty_obj_obj_iso_of_eq`. -/
theorem Endofunctor.IsoAlgebra.nonempty_overPowSucc_mapOfNatIso_iso_of_eq
    (hc : PullbackAssoc P c) {X Y : Over T} (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y)
    (hf : eX.hom ≫ f = f ≫ eY.hom) (n : ℕ)
    (β : Q f.left ⋙ P eY.hom.left ≅ P eX.hom.left ⋙ Q f.left)
    (hβ : β.hom = pushforwardBaseChange c adj (Over.left_comp_left_eq_of_comp_eq hf))
    (βn : Q f.left ⋙ P (eY.pow (n + 1)).hom.left ≅ P (eX.pow (n + 1)).hom.left ⋙ Q f.left)
    (hβn : βn.hom = pushforwardBaseChange c adj (Over.left_comp_left_eq_of_comp_eq
      (Iso.pow_hom_comp_eq_comp_pow_hom eX eY hf n)))
    (𝒜X 𝒜Y 𝒜Xn 𝒜Yn : Type _) {i𝒜X : Category 𝒜X} {i𝒜Y : Category 𝒜Y} {i𝒜Xn : Category 𝒜Xn}
    {i𝒜Yn : Category 𝒜Yn} (F : 𝒜X) (Λ₁ : 𝒜X ⥤ 𝒜Y) (Λn : 𝒜Xn ⥤ 𝒜Yn) (TX : 𝒜X ⥤ 𝒜Xn)
    (TY : 𝒜Y ⥤ 𝒜Yn)
    (h𝒜X : (⟨𝒜X, i𝒜X⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eX.hom.left), inferInstance⟩)
    (h𝒜Y : (⟨𝒜Y, i𝒜Y⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eY.hom.left), inferInstance⟩)
    (h𝒜Xn : (⟨𝒜Xn, i𝒜Xn⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P (eX.pow (n + 1)).hom.left), inferInstance⟩)
    (h𝒜Yn : (⟨𝒜Yn, i𝒜Yn⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P (eY.pow (n + 1)).hom.left), inferInstance⟩)
    (hΛ₁ : HEq Λ₁ (Endofunctor.IsoAlgebra.mapOfNatIso β))
    (hΛn : HEq Λn (Endofunctor.IsoAlgebra.mapOfNatIso βn))
    (hTX : HEq TX (Endofunctor.IsoAlgebra.overPowSuccFunctor c eX n))
    (hTY : HEq TY (Endofunctor.IsoAlgebra.overPowSuccFunctor c eY n)) :
    Nonempty (TY.obj (Λ₁.obj F) ≅ Λn.obj (TX.obj F)) := by
  cases h𝒜X
  cases h𝒜Y
  cases h𝒜Xn
  cases h𝒜Yn
  cases hΛ₁
  cases hΛn
  cases hTX
  cases hTY
  refine ⟨Endofunctor.IsoAlgebra.isoMk (Iso.refl _) ?_⟩
  change (P (eY.pow (n + 1)).hom.left).map (𝟙 _) ≫
      (βn.hom.app F.carrier ≫ (Q f.left).map
        (eX.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) F.str n).hom) =
    (eY.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left)
      ((Endofunctor.IsoAlgebra.mapOfNatIso β).obj F).str n).hom ≫ 𝟙 _
  rw [Functor.map_id, Category.id_comp, Category.comp_id, hβn,
    Iso.powSuccStr_pushforwardBaseChange adj hc eX eY f hf F.str _
      (by rw [Endofunctor.IsoAlgebra.mapOfNatIso_obj_str, Iso.trans_hom, Iso.app_hom, hβ,
        Functor.mapIso_hom]) n]

end Over

end CategoryTheory
