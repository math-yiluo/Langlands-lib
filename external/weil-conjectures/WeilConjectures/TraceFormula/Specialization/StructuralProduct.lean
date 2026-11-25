/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# The exceptional exchange and external duality, abstractly

Let `f = p₁ : V ⟶ W` be a projection, with `f^*` (`L`, `L'`) and `f^!` (`R`, `R'`) on the generic
and special fibres, nearby cycles `S_V`, `S_W` (lax monoidal, with unit `σ = ε`), the pullback
exchange `α_f : f_s^* S_W ⟶ S_V f^*`, the exceptional exchange `β_f : S_V f^! ⟶ f_s^! S_W`, and the
projection-formula maps `t : f^! M ⊗ f^* N ⟶ f^!(M ⊗ N)`, `t'` on the special fibre. For the
external-duality maps `ξ : Q ⟶ f^! 𝟙`, `ξ' : Q' ⟶ f_s^! 𝟙` the normalized external-duality maps
are `κ_M = t(ξ ⊗ 1)` (followed by the unitor).

Blueprint `lemma-base-change-maps-external-duality--1` derives its second equation (the *twisted
case*)

`β_f S(κ_M) μ (a ⊗ α_f) = κ_{S M} (b ⊗ 1)`

from its first equation (the *constant case*) `β_f S(ξ) a = f_s^! σ ξ_s b`, from
`lemma-compatibilities-base-change-maps` (2) and from the unit law `μ (σ ⊗ 1) = 1`
(`CategoryTheory.exceptionalTwisted_of_constant`). Here `a : Q₀ ⟶ S_V Q` is `α_{p₂}` and
`b : Q₀ ⟶ Q'` is `p_{2s}^* θ`, on `Q₀ = p_{2s}^* S_X ω`.

The constant case itself holds for a proper family (`CategoryTheory.exceptionalConstant`): `ξ` is
the `Rp₁ ⊣ p₁^!`-adjoint of the inverse of proper base change `Q : a^* Ra_* ≅ Rp₁* p₂^*` followed
by the counit of `a`, and the compact-support exchanges are compatible with `Q` (the composition
rule for `α` along `a p₁ = a p₂`).

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory

variable {V V' W W' : Type*} [Category V] [Category V'] [Category W] [Category W']
  [MonoidalCategory V] [MonoidalCategory V'] [MonoidalCategory W] [MonoidalCategory W']
  {SV : V ⥤ V'} {SW : W ⥤ W'} [SV.LaxMonoidal] [SW.LaxMonoidal]
  {L : W ⥤ V} {R : W ⥤ V} {L' : W' ⥤ V'} {R' : W' ⥤ V'}

/-- **The twisted case of the exceptional exchange and external duality** (blueprint
`lemma-base-change-maps-external-duality--1`, constant case ⇒ twisted case): with
`κ_M = t(ξ ⊗ 1) ≫ R(λ)` and `κ'_N = t'(ξ' ⊗ 1) ≫ R'(λ)`, the compatibility `hET` of `β` with the
projection formula (blueprint `lemma-compatibilities-base-change-maps` (2)), the naturality of `t'`
in its first variable and the constant case `hconst` give
`(a ⊗ α) ≫ μ ≫ S_V(κ_M) ≫ β = (b ⊗ 1) ≫ κ'_{S_W M}`. -/
theorem exceptionalTwisted_of_constant (α : SW ⋙ L' ⟶ L ⋙ SV) (β : R ⋙ SV ⟶ SW ⋙ R')
    (t : ∀ M N : W, R.obj M ⊗ L.obj N ⟶ R.obj (M ⊗ N))
    (t' : ∀ M N : W', R'.obj M ⊗ L'.obj N ⟶ R'.obj (M ⊗ N))
    (ht' : ∀ {M M' : W'} (g : M ⟶ M') (N : W'),
      R'.map g ▷ L'.obj N ≫ t' M' N = t' M N ≫ R'.map (g ▷ N))
    (hET : ∀ M N : W, SV.obj (R.obj M) ◁ α.app N ≫ μ SV _ _ ≫ SV.map (t M N) ≫ β.app (M ⊗ N) =
      β.app M ▷ L'.obj (SW.obj N) ≫ t' _ _ ≫ R'.map (μ SW M N))
    {Q : V} {Q' Q₀ : V'} (ξ : Q ⟶ R.obj (𝟙_ W)) (ξ' : Q' ⟶ R'.obj (𝟙_ W'))
    (a : Q₀ ⟶ SV.obj Q) (b : Q₀ ⟶ Q')
    (hconst : a ≫ SV.map ξ ≫ β.app (𝟙_ W) = b ≫ ξ' ≫ R'.map (ε SW)) (M : W) :
    (a ⊗ₘ α.app M) ≫ μ SV _ _ ≫
        SV.map (ξ ▷ L.obj M ≫ t (𝟙_ W) M ≫ R.map (λ_ M).hom) ≫ β.app M =
      b ▷ L'.obj (SW.obj M) ≫ ξ' ▷ L'.obj (SW.obj M) ≫ t' (𝟙_ W') (SW.obj M) ≫
        R'.map (λ_ (SW.obj M)).hom := by
  have hβ := β.naturality (λ_ M).hom
  simp only [Functor.comp_map] at hβ
  have hET' := hET (𝟙_ W) M
  have hcon : (a ≫ SV.map ξ ≫ β.app (𝟙_ W)) ▷ L'.obj (SW.obj M) ≫
      t' (SW.obj (𝟙_ W)) (SW.obj M) ≫ R'.map (μ SW (𝟙_ W) M) ≫ R'.map (SW.map (λ_ M).hom) =
      b ▷ L'.obj (SW.obj M) ≫ ξ' ▷ L'.obj (SW.obj M) ≫ t' (𝟙_ W') (SW.obj M) ≫
        R'.map (λ_ (SW.obj M)).hom := by
    rw [hconst, comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
      reassoc_of% (ht' (ε SW) (SW.obj M)), ← R'.map_comp, ← R'.map_comp,
      Functor.LaxMonoidal.left_unitality]
  rw [← hcon, tensorHom_def, Category.assoc, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, hβ, ← Functor.LaxMonoidal.μ_natural_left_assoc]
  dsimp only [Functor.comp_obj]
  rw [whisker_exchange_assoc, reassoc_of% hET']
  simp only [comp_whiskerRight, Category.assoc]

section Constant

variable {DS Ds CX CX' CP CP' : Type*} [Category DS] [Category Ds] [Category CX] [Category CX']
  [Category CP] [Category CP'] {SS : DS ⥤ Ds} {SX : CX ⥤ CX'} {SP : CP ⥤ CP'}
  {La : DS ⥤ CX} {Ra : CX ⥤ DS} {Sa : DS ⥤ CX} {La' : Ds ⥤ CX'} {Ra' : CX' ⥤ Ds}
  {Sa' : Ds ⥤ CX'} {L2 : CX ⥤ CP} {R1 : CP ⥤ CX} {S1 : CX ⥤ CP} {L2' : CX' ⥤ CP'}
  {R1' : CP' ⥤ CX'} {S1' : CX' ⥤ CP'}

/-- **The constant case of the exceptional exchange and external duality** (blueprint
`lemma-base-change-maps-external-duality--1`, first equation, for a proper family): let
`ξ : p₂^* a^! A ⟶ p₁^! a^* A` be the external-duality map, whose `Rp₁ ⊣ p₁^!`-adjoint is the inverse
of proper base change `Q : a^* Ra_* ⟶ Rp₁* p₂^*` followed by `a^*(ε_a)`, and similarly `ξ'` on the
special fibre. Let `β_{p₁}`, `β_a` be the mates of the compact-support exchanges `ν_{p₁}`, `ν_a`,
`θ = β_a(A) ≫ a_s^!(u⁻¹)` and `σ = a_s^*(u) ≫ α_a(A)` for `u : A' ≅ S_S A`. If `ν` is compatible
with proper base change (`hQ`, the composition rule for `α` along `a p₁ = a p₂`), then
`α_{p₂} ≫ S(ξ) ≫ β_{p₁} = p_{2s}^*(θ) ≫ ξ' ≫ p_{1s}^!(σ)`. -/
theorem exceptionalConstant (adja : Ra ⊣ Sa) (adja' : Ra' ⊣ Sa') (adj1 : R1 ⊣ S1)
    (adj1' : R1' ⊣ S1') (νa : SX ⋙ Ra' ⟶ Ra ⋙ SS) (ν1 : SP ⋙ R1' ⟶ R1 ⋙ SX)
    (αa : SS ⋙ La' ⟶ La ⋙ SX) (α2 : SX ⋙ L2' ⟶ L2 ⋙ SP)
    (Q : ∀ L : CX, La.obj (Ra.obj L) ≅ R1.obj (L2.obj L))
    (Q' : ∀ L : CX', La'.obj (Ra'.obj L) ≅ R1'.obj (L2'.obj L))
    (hQ' : ∀ {L M : CX'} (g : L ⟶ M),
      La'.map (Ra'.map g) ≫ (Q' M).hom = (Q' L).hom ≫ R1'.map (L2'.map g))
    (hQ : ∀ L : CX, La'.map (νa.app L) ≫ αa.app (Ra.obj L) ≫ SX.map (Q L).hom =
      (Q' (SX.obj L)).hom ≫ R1'.map (α2.app L) ≫ ν1.app (L2.obj L))
    (A : DS) (A' : Ds) (u : A' ≅ SS.obj A)
    (ξ : L2.obj (Sa.obj A) ⟶ S1.obj (La.obj A))
    (hξ : (adj1.homEquiv _ _).symm ξ = (Q (Sa.obj A)).inv ≫ La.map (adja.counit.app A))
    (ξ' : L2'.obj (Sa'.obj A') ⟶ S1'.obj (La'.obj A'))
    (hξ' : (adj1'.homEquiv _ _).symm ξ' = (Q' (Sa'.obj A')).inv ≫ La'.map (adja'.counit.app A'))
    (θ : SX.obj (Sa.obj A) ⟶ Sa'.obj A')
    (hθ : θ = (mateEquiv adja adja' νa).app A ≫ Sa'.map u.inv)
    (σ : La'.obj A' ⟶ SX.obj (La.obj A)) (hσ : σ = La'.map u.hom ≫ αa.app A) :
    α2.app (Sa.obj A) ≫ SP.map ξ ≫ (mateEquiv adj1 adj1' ν1).app (La.obj A) =
      L2'.map θ ≫ ξ' ≫ S1'.map σ := by
  apply (adj1'.homEquiv _ _).symm.injective
  have eL : (adj1'.homEquiv _ _).symm (α2.app (Sa.obj A) ≫ SP.map ξ ≫
      (mateEquiv adj1 adj1' ν1).app (La.obj A)) = R1'.map (α2.app (Sa.obj A)) ≫
      ν1.app (L2.obj (Sa.obj A)) ≫ SX.map (Q (Sa.obj A)).inv ≫
      SX.map (La.map (adja.counit.app A)) := by
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
      Category.assoc, mateEquiv_counit]
    have hn := ν1.naturality ξ
    simp only [Functor.comp_map] at hn
    have hξc := hξ
    rw [Adjunction.homEquiv_counit] at hξc
    rw [reassoc_of% hn, ← SX.map_comp, hξc, SX.map_comp]
  have eR : (adj1'.homEquiv _ _).symm (L2'.map θ ≫ ξ' ≫ S1'.map σ) =
      (Q' (SX.obj (Sa.obj A))).inv ≫ La'.map (νa.app (Sa.obj A)) ≫
        αa.app (Ra.obj (Sa.obj A)) ≫ SX.map (La.map (adja.counit.app A)) := by
    have hc1 := adj1'.counit.naturality σ
    simp only [Functor.comp_map, Functor.id_map] at hc1
    have hξc' := hξ'
    rw [Adjunction.homEquiv_counit] at hξc'
    have hq := hQ' θ
    have hq' : R1'.map (L2'.map θ) ≫ (Q' (Sa'.obj A')).inv =
        (Q' (SX.obj (Sa.obj A))).inv ≫ La'.map (Ra'.map θ) := by
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hq, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have inner : Ra'.map θ ≫ adja'.counit.app A' ≫ u.hom =
        νa.app (Sa.obj A) ≫ SS.map (adja.counit.app A) := by
      have hc2 := adja'.counit.naturality u.inv
      simp only [Functor.comp_map, Functor.id_map] at hc2
      rw [hθ, Ra'.map_comp, Category.assoc, reassoc_of% hc2, Iso.inv_hom_id, Category.comp_id,
        mateEquiv_counit]
    have hαn := αa.naturality (adja.counit.app A)
    simp only [Functor.comp_map, Functor.id_obj] at hαn
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
      Category.assoc]
    rw [hc1, reassoc_of% hξc', reassoc_of% hq', hσ, ← La'.map_comp_assoc,
      ← La'.map_comp_assoc, Category.assoc, inner, La'.map_comp, Category.assoc, hαn]
    rfl
  refine eL.trans (Eq.trans ?_ eR.symm)
  rw [← cancel_epi (Q' (SX.obj (Sa.obj A))).hom, Iso.hom_inv_id_assoc,
    ← reassoc_of% (hQ (Sa.obj A)), ← SX.map_comp_assoc, Iso.hom_inv_id, SX.map_id,
    Category.id_comp]

end Constant

end CategoryTheory
