/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.TraceFormula.Specialization.ExchangeOnProper

/-!

# Compact-support exchanges along a refinement of compactifications

Let `ν_C = χ_P⁻¹ ∘ R'_{P*}(ν_ι)` be the compact-support exchange of a compactification `ι : N ⊆ P`
(blueprint `prose-E-15` (3); `ν_ι` the adjoint of the inverse of the pullback
exchange `α_ι`, `χ_P` the proper exchange). This file proves, in abstract categories, the formal
steps showing that `ν_C` is unchanged along a refinement `π : P₃ ⟶ P₁` (with `ι₁ = ι₃ ≫ π`):

* `ProEtale.CondensedRing.lowerShriekExchangeOfInv_app_comp_map_comp_pushforwardExchange_app`:
  the composition law of the pullback exchanges and the description of the base change map
  `E : ι₁! ⟶ Rπ_* ι₃!` by its adjoint give
  `χ_π(ι₃! K) ∘ Ψ_{P₁}(E_K) ∘ ν_{ι₁}(K) = Rπ'_*(ν_{ι₃}(K)) ∘ E'_{Ψ_N K}`;
* `ProEtale.CondensedRing.compactSupportExchange_comp_eq_of_pushforwardExchange_comp`: with the
  composition law of the proper exchanges, this identity gives
  `χ₃⁻¹ ∘ R₃'(ν_{ι₃}) = χ₁⁻¹ ∘ R₁'(ν_{ι₁})` through `E`;
* `ProEtale.CondensedRing.compactSupportExchangeAux_eq_of_refinement` and
  `ProEtale.CondensedRing.compactSupportExchangeAux_lift_eq_of_refinement`: the same for the
  shape `compactSupportExchangeAux` of the compact-support exchange on restricted functors.

-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {DN DN' D₁ D₁' D₃ D₃' Ds Ds' : Type*} [Category DN] [Category DN'] [Category D₁]
  [Category D₁'] [Category D₃] [Category D₃'] [Category Ds] [Category Ds']

/-- **The refinement step for compact-support exchanges**, in abstract categories: let
`ν₁ : Ψ_N ⋙ Dh₁' ⟶ Dh₁ ⋙ Ψ₁` and `ν₃ : Ψ_N ⋙ Dh₃' ⟶ Dh₃ ⋙ Ψ₃` be exchanges for two "open"
functors, related at `K` by morphisms `e : Dh₁ K ⟶ Rπ Dh₃ K` and `e'` through an exchange
`χπ : Rπ ⋙ Ψ₁ ⟶ Ψ₃ ⋙ Rπ'` (`hE`), and let the exchanges `χ₁`, `χ₃` of the "proper" functors
`R₁` and `R₃ ≅ Rπ ⋙ R₁` satisfy the composition law `hχ`. If `χ₃` is invertible at `Dh₃ K`, then
`χ₃⁻¹ ∘ R₃'(ν₃)` and `χ₁⁻¹ ∘ R₁'(ν₁)` agree at `K` up to `e`, `e'`, `conj` and `conj'`, for right
inverses `χ₁inv` and `χ₃inv` of `χ₁` and `χ₃`:
```
R₁' Dh₁' Ψ_N K --R₁'(e')--> R₁' Rπ' Dh₃' Ψ_N K ≅ R₃' Dh₃' Ψ_N K --R₃'(ν₃)--> R₃' Ψ₃ Dh₃ K
      |                                                                          |
   R₁'(ν₁)                                                                     χ₃⁻¹
      v                                                                          v
R₁' Ψ₁ Dh₁ K --χ₁⁻¹--> Ψs R₁ Dh₁ K --Ψs(R₁(e))--> Ψs R₁ Rπ Dh₃ K ≅ Ψs R₃ Dh₃ K
```
-/
lemma compactSupportExchange_comp_eq_of_pushforwardExchange_comp {ΨN : DN ⥤ DN'}
    {Ψ₁ : D₁ ⥤ D₁'} {Ψ₃ : D₃ ⥤ D₃'}
    {Ψs : Ds ⥤ Ds'} {Dh₁ : DN ⥤ D₁} {Dh₁' : DN' ⥤ D₁'} {Dh₃ : DN ⥤ D₃} {Dh₃' : DN' ⥤ D₃'}
    {Rπ : D₃ ⥤ D₁} {Rπ' : D₃' ⥤ D₁'} {R₁ : D₁ ⥤ Ds} {R₁' : D₁' ⥤ Ds'} {R₃ : D₃ ⥤ Ds}
    {R₃' : D₃' ⥤ Ds'} (conj : R₃ ≅ Rπ ⋙ R₁) (conj' : R₃' ≅ Rπ' ⋙ R₁')
    (χπ : Rπ ⋙ Ψ₁ ⟶ Ψ₃ ⋙ Rπ') (χ₁ : R₁ ⋙ Ψs ⟶ Ψ₁ ⋙ R₁') (χ₃ : R₃ ⋙ Ψs ⟶ Ψ₃ ⋙ R₃')
    (hχ : ∀ A, χ₃.app A = Ψs.map (conj.hom.app A) ≫ χ₁.app (Rπ.obj A) ≫
      R₁'.map (χπ.app A) ≫ conj'.inv.app (Ψ₃.obj A))
    (ν₁ : ΨN ⋙ Dh₁' ⟶ Dh₁ ⋙ Ψ₁)
    (ν₃ : ΨN ⋙ Dh₃' ⟶ Dh₃ ⋙ Ψ₃) (K : DN) (e : Dh₁.obj K ⟶ Rπ.obj (Dh₃.obj K))
    (e' : Dh₁'.obj (ΨN.obj K) ⟶ Rπ'.obj (Dh₃'.obj (ΨN.obj K)))
    (hE : ν₁.app K ≫ Ψ₁.map e ≫ χπ.app (Dh₃.obj K) =
      e' ≫ Rπ'.map (ν₃.app K))
    [IsIso (χ₃.app (Dh₃.obj K))]
    (χ₁inv : R₁'.obj (Ψ₁.obj (Dh₁.obj K)) ⟶ Ψs.obj (R₁.obj (Dh₁.obj K)))
    (hχ₁ : χ₁inv ≫ χ₁.app (Dh₁.obj K) = 𝟙 _)
    (χ₃inv : R₃'.obj (Ψ₃.obj (Dh₃.obj K)) ⟶ Ψs.obj (R₃.obj (Dh₃.obj K)))
    (hχ₃ : χ₃inv ≫ χ₃.app (Dh₃.obj K) = 𝟙 _) :
    R₁'.map e' ≫ conj'.inv.app (Dh₃'.obj (ΨN.obj K)) ≫
        R₃'.map (ν₃.app K) ≫ χ₃inv =
      R₁'.map (ν₁.app K) ≫ χ₁inv ≫
        Ψs.map (R₁.map e ≫ conj.inv.app (Dh₃.obj K)) := by
  obtain rfl : χ₃inv = inv (χ₃.app (Dh₃.obj K)) := IsIso.eq_inv_of_inv_hom_id hχ₃
  rw [← cancel_mono (χ₃.app (Dh₃.obj K)), Category.assoc, Category.assoc, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id, hχ]
  have nχ := χ₁.naturality e
  have nconj := conj'.inv.naturality (ν₃.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at nχ nconj
  simp only [Functor.map_comp, Category.assoc]
  rw [← Ψs.map_comp_assoc (conj.inv.app _), Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% nχ, reassoc_of% hχ₁, ← R₁'.map_comp_assoc,
    ← R₁'.map_comp_assoc, Category.assoc, hE, R₁'.map_comp, Category.assoc, ← nconj]


/-- **The key identity of the refinement step**, in abstract categories: let `Dh₁ ⊣ Lh₁`,
`Dh₃ ⊣ Lh₃` (and their primed versions) be the open adjunctions of `ι₁ = ι₃ ≫ p` and `ι₃`,
`Lπ ⊣ Rπ` (and `Lπ' ⊣ Rπ'`) the adjunctions of `p`, with pullback exchanges `α₁`, `α₃`, `απ`
satisfying the composition law `hα` through the comparisons `c : Lh₁ ≅ Lπ ⋙ Lh₃`,
`c' : Lh₁' ≅ Lπ' ⋙ Lh₃'`, and `χπ` the mate of `απ` (`hχπ`). If `e : Dh₁ K ⟶ Rπ Dh₃ K` is the
base change map, characterized by its adjoint `e♭ : Lπ Dh₁ K ⟶ Dh₃ K` (`hE`: the `Lh₃`-adjoint
of `e♭` is the unit of `ι₁` read through `c`), and similarly for `e'` with `e'♭` invertible, then
the square of the mates `ν₁`, `ν₃` of `α₁⁻¹`, `α₃⁻¹` commutes:
```
Dh₁' Ψ_N K ----ν₁----> Ψ₁ Dh₁ K --Ψ₁(e)--> Ψ₁ Rπ Dh₃ K
     |                                          |
     e'                                       χπ
     v                                          v
Rπ' Dh₃' Ψ_N K ------Rπ'(ν₃)------> Rπ' Ψ₃ Dh₃ K
```
-/
lemma lowerShriekExchangeOfInv_app_comp_map_comp_pushforwardExchange_app {ΨN : DN ⥤ DN'}
    {Ψ₁ : D₁ ⥤ D₁'}
    {Ψ₃ : D₃ ⥤ D₃'} {Dh₁ : DN ⥤ D₁} {Lh₁ : D₁ ⥤ DN} {Dh₃ : DN ⥤ D₃} {Lh₃ : D₃ ⥤ DN}
    {Dh₁' : DN' ⥤ D₁'} {Lh₁' : D₁' ⥤ DN'} {Dh₃' : DN' ⥤ D₃'} {Lh₃' : D₃' ⥤ DN'}
    (adj₁ : Dh₁ ⊣ Lh₁) (adj₃ : Dh₃ ⊣ Lh₃) (adj₁' : Dh₁' ⊣ Lh₁') (adj₃' : Dh₃' ⊣ Lh₃')
    {Lπ : D₁ ⥤ D₃} {Rπ : D₃ ⥤ D₁} (adjπ : Lπ ⊣ Rπ) {Lπ' : D₁' ⥤ D₃'} {Rπ' : D₃' ⥤ D₁'}
    (adjπ' : Lπ' ⊣ Rπ') (α₁ : Ψ₁ ⋙ Lh₁' ⟶ Lh₁ ⋙ ΨN) (hα₁ : IsIso α₁)
    (α₃ : Ψ₃ ⋙ Lh₃' ⟶ Lh₃ ⋙ ΨN)
    (hα₃ : IsIso α₃) (απ : Ψ₁ ⋙ Lπ' ⟶ Lπ ⋙ Ψ₃) (χπ : Rπ ⋙ Ψ₁ ⟶ Ψ₃ ⋙ Rπ')
    (hχπ : ∀ A, Lπ'.map (χπ.app A) ≫ adjπ'.counit.app (Ψ₃.obj A) =
      απ.app (Rπ.obj A) ≫ Ψ₃.map (adjπ.counit.app A))
    (c : Lh₁ ≅ Lπ ⋙ Lh₃) (c' : Lh₁' ≅ Lπ' ⋙ Lh₃')
    (hα : ∀ A, α₁.app A = c'.hom.app (Ψ₁.obj A) ≫ Lh₃'.map (απ.app A) ≫ α₃.app (Lπ.obj A) ≫
      ΨN.map (c.inv.app A))
    (K : DN) (e : Dh₁.obj K ⟶ Rπ.obj (Dh₃.obj K))
    (e' : Dh₁'.obj (ΨN.obj K) ⟶ Rπ'.obj (Dh₃'.obj (ΨN.obj K)))
    (hE : adj₁.unit.app K ≫ c.hom.app (Dh₁.obj K) ≫
      Lh₃.map (Lπ.map e ≫ adjπ.counit.app (Dh₃.obj K)) = adj₃.unit.app K)
    (hE' : adj₁'.unit.app (ΨN.obj K) ≫ c'.hom.app (Dh₁'.obj (ΨN.obj K)) ≫
      Lh₃'.map (Lπ'.map e' ≫ adjπ'.counit.app (Dh₃'.obj (ΨN.obj K))) =
        adj₃'.unit.app (ΨN.obj K))
    (hEb' : IsIso (Lπ'.map e' ≫ adjπ'.counit.app (Dh₃'.obj (ΨN.obj K)))) :
    (lowerShriekExchangeOfInv adj₁ adj₁' α₁).app K ≫ Ψ₁.map e ≫ χπ.app (Dh₃.obj K) =
      e' ≫ Rπ'.map ((lowerShriekExchangeOfInv adj₃ adj₃' α₃).app K) := by
  have := hEb'
  apply (adjπ'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h1 := απ.naturality e
  have h2 := adjπ'.counit.naturality ((lowerShriekExchangeOfInv adj₃ adj₃' α₃).app K)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at h1 h2
  rw [hχπ, reassoc_of% h1, h2, ← Ψ₃.map_comp]
  -- the source is identified with `Dh₃' Ψ_N K` by `E'♭`
  rw [← cancel_epi (inv (Lπ'.map e' ≫ adjπ'.counit.app (Dh₃'.obj (ΨN.obj K))))]
  conv_rhs => rw [← Category.assoc (Lπ'.map _), IsIso.inv_hom_id_assoc]
  apply (adj₃'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have h3 : adj₃'.unit.app (ΨN.obj K) ≫
      Lh₃'.map (inv (Lπ'.map e' ≫ adjπ'.counit.app (Dh₃'.obj (ΨN.obj K)))) =
        adj₁'.unit.app (ΨN.obj K) ≫ c'.hom.app (Dh₁'.obj (ΨN.obj K)) := by
    rw [← hE', Category.assoc, Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id]
    simp
  have h4 := c'.hom.naturality ((lowerShriekExchangeOfInv adj₁ adj₁' α₁).app K)
  have h5 : c'.hom.app (Ψ₁.obj (Dh₁.obj K)) ≫ Lh₃'.map (απ.app (Dh₁.obj K)) =
      α₁.app (Dh₁.obj K) ≫ ΨN.map (c.hom.app (Dh₁.obj K)) ≫
        (inv α₃).app (Lπ.obj (Dh₁.obj K)) := by
    rw [hα]
    simp [← ΨN.map_comp_assoc]
  have h6 := (inv α₃).naturality (Lπ.map e ≫ adjπ.counit.app (Dh₃.obj K))
  simp only [Functor.comp_map, Functor.comp_obj] at h4 h6
  rw [unit_comp_lowerShriekExchangeOfInv_app, Functor.map_comp, reassoc_of% h3, Functor.map_comp,
    Functor.map_comp, ← reassoc_of% h4, reassoc_of% (unit_comp_lowerShriekExchangeOfInv_app adj₁
    adj₁' α₁ K), reassoc_of% h5, NatIso.isIso_inv_app α₁, IsIso.inv_hom_id_assoc, ← h6,
    ← ΨN.map_comp_assoc, ← ΨN.map_comp_assoc, Category.assoc, hE]
  rfl


/-- **The refinement step, assembled**: under the hypotheses of
`ProEtale.CondensedRing.compactSupportExchange_comp_eq_of_pushforwardExchange_comp`, if the
identifications `x₃` and `y₃` of the source and target through the third functors are those
through the first ones followed by `e'`, `conj'` (`hx`) and preceded by `e`, `conj` (`hy`), then
the two composites
`x ≫ R'(ν) ≫ χ⁻¹ ≫ y` agree. -/
lemma compactSupportExchange_eq_of_comp_eq {ΨN : DN ⥤ DN'} {Ψ₁ : D₁ ⥤ D₁'} {Ψ₃ : D₃ ⥤ D₃'}
    {Ψs : Ds ⥤ Ds'} {Dh₁ : DN ⥤ D₁} {Dh₁' : DN' ⥤ D₁'} {Dh₃ : DN ⥤ D₃} {Dh₃' : DN' ⥤ D₃'}
    {Rπ : D₃ ⥤ D₁} {Rπ' : D₃' ⥤ D₁'} {R₁ : D₁ ⥤ Ds} {R₁' : D₁' ⥤ Ds'} {R₃ : D₃ ⥤ Ds}
    {R₃' : D₃' ⥤ Ds'} (conj : R₃ ≅ Rπ ⋙ R₁) (conj' : R₃' ≅ Rπ' ⋙ R₁')
    (χπ : Rπ ⋙ Ψ₁ ⟶ Ψ₃ ⋙ Rπ') (χ₁ : R₁ ⋙ Ψs ⟶ Ψ₁ ⋙ R₁') (χ₃ : R₃ ⋙ Ψs ⟶ Ψ₃ ⋙ R₃')
    (hχ : ∀ A, χ₃.app A = Ψs.map (conj.hom.app A) ≫ χ₁.app (Rπ.obj A) ≫
      R₁'.map (χπ.app A) ≫ conj'.inv.app (Ψ₃.obj A))
    (ν₁ : ΨN ⋙ Dh₁' ⟶ Dh₁ ⋙ Ψ₁) (ν₃ : ΨN ⋙ Dh₃' ⟶ Dh₃ ⋙ Ψ₃) (K : DN)
    (e : Dh₁.obj K ⟶ Rπ.obj (Dh₃.obj K))
    (e' : Dh₁'.obj (ΨN.obj K) ⟶ Rπ'.obj (Dh₃'.obj (ΨN.obj K)))
    (hE : ν₁.app K ≫ Ψ₁.map e ≫ χπ.app (Dh₃.obj K) = e' ≫ Rπ'.map (ν₃.app K))
    [IsIso (χ₃.app (Dh₃.obj K))]
    (χ₁inv : R₁'.obj (Ψ₁.obj (Dh₁.obj K)) ⟶ Ψs.obj (R₁.obj (Dh₁.obj K)))
    (hχ₁ : χ₁inv ≫ χ₁.app (Dh₁.obj K) = 𝟙 _)
    (χ₃inv : R₃'.obj (Ψ₃.obj (Dh₃.obj K)) ⟶ Ψs.obj (R₃.obj (Dh₃.obj K)))
    (hχ₃ : χ₃inv ≫ χ₃.app (Dh₃.obj K) = 𝟙 _) {A T : Ds'}
    (x₁ : A ⟶ R₁'.obj (Dh₁'.obj (ΨN.obj K))) (x₃ : A ⟶ R₃'.obj (Dh₃'.obj (ΨN.obj K)))
    (hx : x₁ ≫ R₁'.map e' ≫ conj'.inv.app (Dh₃'.obj (ΨN.obj K)) = x₃)
    (y₁ : Ψs.obj (R₁.obj (Dh₁.obj K)) ⟶ T) (y₃ : Ψs.obj (R₃.obj (Dh₃.obj K)) ⟶ T)
    (hy : Ψs.map (R₁.map e ≫ conj.inv.app (Dh₃.obj K)) ≫ y₃ = y₁) :
    x₃ ≫ R₃'.map (ν₃.app K) ≫ χ₃inv ≫ y₃ = x₁ ≫ R₁'.map (ν₁.app K) ≫ χ₁inv ≫ y₁ := by
  rw [← hx, ← hy]
  have := compactSupportExchange_comp_eq_of_pushforwardExchange_comp conj conj' χπ χ₁ χ₃ hχ ν₁ ν₃ K
    e e' hE χ₁inv hχ₁ χ₃inv hχ₃
  simp only [Category.assoc] at this ⊢
  rw [reassoc_of% this]

end Abstract


section Shape

variable {CC CC' CP₁ CP₁' CP₃ CP₃' Cs Cs' DC DC' DP₁ DP₁' DP₃ DP₃' Ds Ds' : Type*}
  [Category CC] [Category CC'] [Category CP₁] [Category CP₁'] [Category CP₃] [Category CP₃']
  [Category Cs] [Category Cs'] [Category DC] [Category DC'] [Category DP₁] [Category DP₁']
  [Category DP₃] [Category DP₃'] [Category Ds] [Category Ds']

/-- **The refinement step on the shape `compactSupportExchangeAux`**: two compact-support
exchanges `ν = compactSupportExchangeAux …` built from compactifications `1` and `3`, sharing the
source and target functors and their compatibilities `cSp`, `cT` with the inclusions, agree if,
at every object, the hypotheses of `compactSupportExchange_eq_of_comp_eq` hold for the
ambient exchanges, with the factorizations of the source (`hx`) and of the target (`hy`) of the
two compactifications related by `e`, `e'` and the composition isomorphisms `conj`, `conj'`. -/
lemma compactSupportExchangeAux_eq_of_refinement {Sp : CC ⥤ CC'} {LSf' : CC' ⥤ Cs'}
    {LSf : CC ⥤ Cs} {Ts : Cs ⥤ Cs'} {ιC : CC ⥤ DC} {ιC' : CC' ⥤ DC'} {ιs : Cs ⥤ Ds}
    {ιs' : Cs' ⥤ Ds'} (hι : ιs'.FullyFaithful) {ΨC : DC ⥤ DC'} {Ψs : Ds ⥤ Ds'}
    (cSp : Sp ⋙ ιC' ≅ ιC ⋙ ΨC) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs)
    {OLS₁ : CC ⥤ CP₁} {OLS₁' : CC' ⥤ CP₁'} {LStp₁ : CP₁ ⥤ Cs} {LStp₁' : CP₁' ⥤ Cs'}
    {ιP₁ : CP₁ ⥤ DP₁} {ιP₁' : CP₁' ⥤ DP₁'} {ΨP₁ : DP₁ ⥤ DP₁'} {Dh₁ : DC ⥤ DP₁}
    {Dh₁' : DC' ⥤ DP₁'} {Rp₁ : DP₁ ⥤ Ds} {Rp₁' : DP₁' ⥤ Ds'}
    (i₁₁ : LSf' ≅ OLS₁' ⋙ LStp₁') (i₂₁ : LSf ≅ OLS₁ ⋙ LStp₁)
    (cO₁' : OLS₁' ⋙ ιP₁' ≅ ιC' ⋙ Dh₁') (cR₁' : LStp₁' ⋙ ιs' ≅ ιP₁' ⋙ Rp₁')
    (cO₁ : OLS₁ ⋙ ιP₁ ≅ ιC ⋙ Dh₁) (cR₁ : LStp₁ ⋙ ιs ≅ ιP₁ ⋙ Rp₁)
    (νh₁ : ΨC ⋙ Dh₁' ⟶ Dh₁ ⋙ ΨP₁) (χ₁ : Rp₁ ⋙ Ψs ⟶ ΨP₁ ⋙ Rp₁')
    (hφp₁ : IsIsoOn ιP₁ χ₁)
    {OLS₃ : CC ⥤ CP₃} {OLS₃' : CC' ⥤ CP₃'} {LStp₃ : CP₃ ⥤ Cs} {LStp₃' : CP₃' ⥤ Cs'}
    {ιP₃ : CP₃ ⥤ DP₃} {ιP₃' : CP₃' ⥤ DP₃'} {ΨP₃ : DP₃ ⥤ DP₃'} {Dh₃ : DC ⥤ DP₃}
    {Dh₃' : DC' ⥤ DP₃'} {Rp₃ : DP₃ ⥤ Ds} {Rp₃' : DP₃' ⥤ Ds'}
    (i₁₃ : LSf' ≅ OLS₃' ⋙ LStp₃') (i₂₃ : LSf ≅ OLS₃ ⋙ LStp₃)
    (cO₃' : OLS₃' ⋙ ιP₃' ≅ ιC' ⋙ Dh₃') (cR₃' : LStp₃' ⋙ ιs' ≅ ιP₃' ⋙ Rp₃')
    (cO₃ : OLS₃ ⋙ ιP₃ ≅ ιC ⋙ Dh₃) (cR₃ : LStp₃ ⋙ ιs ≅ ιP₃ ⋙ Rp₃)
    (νh₃ : ΨC ⋙ Dh₃' ⟶ Dh₃ ⋙ ΨP₃) (χ₃ : Rp₃ ⋙ Ψs ⟶ ΨP₃ ⋙ Rp₃')
    (hφp₃ : IsIsoOn ιP₃ χ₃)
    {Rπ : DP₃ ⥤ DP₁} {Rπ' : DP₃' ⥤ DP₁'} (conj : Rp₃ ≅ Rπ ⋙ Rp₁) (conj' : Rp₃' ≅ Rπ' ⋙ Rp₁')
    (χπ : Rπ ⋙ ΨP₁ ⟶ ΨP₃ ⋙ Rπ')
    (hχ : ∀ A, χ₃.app A = Ψs.map (conj.hom.app A) ≫ χ₁.app (Rπ.obj A) ≫
      Rp₁'.map (χπ.app A) ≫ conj'.inv.app (ΨP₃.obj A))
    (H : ∀ M : CC, ∃ (e : Dh₁.obj (ιC.obj M) ⟶ Rπ.obj (Dh₃.obj (ιC.obj M)))
      (e' : Dh₁'.obj (ΨC.obj (ιC.obj M)) ⟶ Rπ'.obj (Dh₃'.obj (ΨC.obj (ιC.obj M)))),
      νh₁.app (ιC.obj M) ≫ ΨP₁.map e ≫ χπ.app (Dh₃.obj (ιC.obj M)) =
        e' ≫ Rπ'.map (νh₃.app (ιC.obj M)) ∧
      (ιs'.map (i₁₁.hom.app (Sp.obj M)) ≫ cR₁'.hom.app (OLS₁'.obj (Sp.obj M)) ≫
        Rp₁'.map (cO₁'.hom.app (Sp.obj M) ≫ Dh₁'.map (cSp.hom.app M))) ≫ Rp₁'.map e' ≫
          conj'.inv.app (Dh₃'.obj (ΨC.obj (ιC.obj M))) =
        ιs'.map (i₁₃.hom.app (Sp.obj M)) ≫ cR₃'.hom.app (OLS₃'.obj (Sp.obj M)) ≫
          Rp₃'.map (cO₃'.hom.app (Sp.obj M) ≫ Dh₃'.map (cSp.hom.app M)) ∧
      Ψs.map (Rp₁.map e ≫ conj.inv.app (Dh₃.obj (ιC.obj M))) ≫
          (Ψs.map (Rp₃.map (cO₃.inv.app M) ≫ cR₃.inv.app (OLS₃.obj M)) ≫
            cT.inv.app (LStp₃.obj (OLS₃.obj M)) ≫ ιs'.map (Ts.map (i₂₃.inv.app M))) =
        Ψs.map (Rp₁.map (cO₁.inv.app M) ≫ cR₁.inv.app (OLS₁.obj M)) ≫
          cT.inv.app (LStp₁.obj (OLS₁.obj M)) ≫ ιs'.map (Ts.map (i₂₁.inv.app M))) :
    compactSupportExchangeAux hι i₁₃ i₂₃ cSp cO₃' cR₃' cO₃ cR₃ cT νh₃
        (invOnSubcategory ιP₃ χ₃ hφp₃) =
      compactSupportExchangeAux hι i₁₁ i₂₁ cSp cO₁' cR₁' cO₁ cR₁ cT νh₁
        (invOnSubcategory ιP₁ χ₁ hφp₁) := by
  ext M
  apply hι.map_injective
  obtain ⟨e, e', hE, hx, hy⟩ := H M
  have : IsIso (χ₃.app ((OLS₃ ⋙ ιP₃).obj M)) := hφp₃ (OLS₃.obj M)
  have : IsIso (χ₃.app (Dh₃.obj (ιC.obj M))) := NatTrans.isIso_app_of_iso χ₃ (cO₃.app M).symm
  rw [compactSupportExchangeAux_app, compactSupportExchangeAux_app]
  -- the right inverses of `χ` at `Dh (ιC M)`
  have key := compactSupportExchange_eq_of_comp_eq conj conj' χπ χ₁ χ₃ hχ νh₁ νh₃ (ιC.obj M)
    e e' hE
    (Rp₁'.map (ΨP₁.map (cO₁.inv.app M)) ≫ (invOnSubcategory ιP₁ χ₁ hφp₁).app (OLS₁.obj M) ≫
      Ψs.map (Rp₁.map (cO₁.hom.app M))) ?_
    (Rp₃'.map (ΨP₃.map (cO₃.inv.app M)) ≫ (invOnSubcategory ιP₃ χ₃ hφp₃).app (OLS₃.obj M) ≫
      Ψs.map (Rp₃.map (cO₃.hom.app M))) ?_ _ _ hx _ _ hy
  · simp only [Functor.map_comp, Category.assoc] at key ⊢
    simp only [← Ψs.map_comp_assoc, ← Rp₁.map_comp_assoc, ← Rp₃.map_comp_assoc,
      Iso.hom_inv_id_app] at key
    simpa using key
  · have n := χ₁.naturality (cO₁.hom.app M)
    simp only [Functor.comp_map, Functor.comp_obj] at n
    rw [Category.assoc, Category.assoc]
    erw [n, reassoc_of% (invOnSubcategory_app_comp ιP₁ χ₁ hφp₁ (OLS₁.obj M))]
    rw [← Rp₁'.map_comp, ← ΨP₁.map_comp]
    erw [Iso.inv_hom_id_app]
    simp
  · have n := χ₃.naturality (cO₃.hom.app M)
    simp only [Functor.comp_map, Functor.comp_obj] at n
    rw [Category.assoc, Category.assoc]
    erw [n, reassoc_of% (invOnSubcategory_app_comp ιP₃ χ₃ hφp₃ (OLS₃.obj M))]
    rw [← Rp₃'.map_comp, ← ΨP₃.map_comp]
    erw [Iso.inv_hom_id_app]
    simp


/-- **The refinement step for restricted functors**: the form of
`compactSupportExchangeAux_eq_of_refinement` where all the categories are full subcategories
(given by object properties `PC`, `PC'`, `PPᵢ`, `PPᵢ'`, `Ps`, `Ps'`), the restricted functors are
the lifts of the ambient ones and their compatibilities with the inclusions are the identities
`ObjectProperty.liftCompιIso`. The identifications of the source and target are then compared
directly (`hx`, `hy`), without the compatibilities. -/
lemma compactSupportExchangeAux_lift_eq_of_refinement {PC : ObjectProperty DC}
    {PC' : ObjectProperty DC'} {Ps : ObjectProperty Ds} {Ps' : ObjectProperty Ds'}
    {PP₁ : ObjectProperty DP₁} {PP₁' : ObjectProperty DP₁'} {PP₃ : ObjectProperty DP₃}
    {PP₃' : ObjectProperty DP₃'} {LSf' : PC'.FullSubcategory ⥤ Ps'.FullSubcategory}
    {LSf : PC.FullSubcategory ⥤ Ps.FullSubcategory} {ΨC : DC ⥤ DC'} {Ψs : Ds ⥤ Ds'}
    (hSp : ∀ X, PC' ((PC.ι ⋙ ΨC).obj X)) (hT : ∀ X, Ps' ((Ps.ι ⋙ Ψs).obj X))
    {ΨP₁ : DP₁ ⥤ DP₁'} {Dh₁ : DC ⥤ DP₁} {Dh₁' : DC' ⥤ DP₁'} {Rp₁ : DP₁ ⥤ Ds}
    {Rp₁' : DP₁' ⥤ Ds'} (hO₁ : ∀ X, PP₁ ((PC.ι ⋙ Dh₁).obj X))
    (hO₁' : ∀ X, PP₁' ((PC'.ι ⋙ Dh₁').obj X)) (hR₁ : ∀ X, Ps ((PP₁.ι ⋙ Rp₁).obj X))
    (hR₁' : ∀ X, Ps' ((PP₁'.ι ⋙ Rp₁').obj X))
    (i₁₁ : LSf' ≅ PP₁'.lift (PC'.ι ⋙ Dh₁') hO₁' ⋙ Ps'.lift (PP₁'.ι ⋙ Rp₁') hR₁')
    (i₂₁ : LSf ≅ PP₁.lift (PC.ι ⋙ Dh₁) hO₁ ⋙ Ps.lift (PP₁.ι ⋙ Rp₁) hR₁)
    (νh₁ : ΨC ⋙ Dh₁' ⟶ Dh₁ ⋙ ΨP₁) (χ₁ : Rp₁ ⋙ Ψs ⟶ ΨP₁ ⋙ Rp₁')
    (hφp₁ : IsIsoOn PP₁.ι χ₁)
    {ΨP₃ : DP₃ ⥤ DP₃'} {Dh₃ : DC ⥤ DP₃} {Dh₃' : DC' ⥤ DP₃'} {Rp₃ : DP₃ ⥤ Ds}
    {Rp₃' : DP₃' ⥤ Ds'} (hO₃ : ∀ X, PP₃ ((PC.ι ⋙ Dh₃).obj X))
    (hO₃' : ∀ X, PP₃' ((PC'.ι ⋙ Dh₃').obj X)) (hR₃ : ∀ X, Ps ((PP₃.ι ⋙ Rp₃).obj X))
    (hR₃' : ∀ X, Ps' ((PP₃'.ι ⋙ Rp₃').obj X))
    (i₁₃ : LSf' ≅ PP₃'.lift (PC'.ι ⋙ Dh₃') hO₃' ⋙ Ps'.lift (PP₃'.ι ⋙ Rp₃') hR₃')
    (i₂₃ : LSf ≅ PP₃.lift (PC.ι ⋙ Dh₃) hO₃ ⋙ Ps.lift (PP₃.ι ⋙ Rp₃) hR₃)
    (νh₃ : ΨC ⋙ Dh₃' ⟶ Dh₃ ⋙ ΨP₃) (χ₃ : Rp₃ ⋙ Ψs ⟶ ΨP₃ ⋙ Rp₃')
    (hφp₃ : IsIsoOn PP₃.ι χ₃)
    {Rπ : DP₃ ⥤ DP₁} {Rπ' : DP₃' ⥤ DP₁'} (conj : Rp₃ ≅ Rπ ⋙ Rp₁) (conj' : Rp₃' ≅ Rπ' ⋙ Rp₁')
    (χπ : Rπ ⋙ ΨP₁ ⟶ ΨP₃ ⋙ Rπ')
    (hχ : ∀ A, χ₃.app A = Ψs.map (conj.hom.app A) ≫ χ₁.app (Rπ.obj A) ≫
      Rp₁'.map (χπ.app A) ≫ conj'.inv.app (ΨP₃.obj A))
    (H : ∀ M : PC.FullSubcategory, ∃ (e : Dh₁.obj M.obj ⟶ Rπ.obj (Dh₃.obj M.obj))
      (e' : Dh₁'.obj (ΨC.obj M.obj) ⟶ Rπ'.obj (Dh₃'.obj (ΨC.obj M.obj))),
      νh₁.app M.obj ≫ ΨP₁.map e ≫ χπ.app (Dh₃.obj M.obj) = e' ≫ Rπ'.map (νh₃.app M.obj) ∧
      (i₁₁.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSp).obj M)).hom ≫ Rp₁'.map e' ≫
          conj'.inv.app (Dh₃'.obj (ΨC.obj M.obj)) =
        (i₁₃.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSp).obj M)).hom ∧
      Ψs.map (Rp₁.map e ≫ conj.inv.app (Dh₃.obj M.obj)) ≫ Ψs.map (i₂₃.inv.app M).hom =
        Ψs.map (i₂₁.inv.app M).hom) :
    compactSupportExchangeAux Ps'.fullyFaithfulι i₁₃ i₂₃ (PC'.liftCompιIso _ hSp)
        (PP₃'.liftCompιIso _ hO₃') (Ps'.liftCompιIso _ hR₃') (PP₃.liftCompιIso _ hO₃)
        (Ps.liftCompιIso _ hR₃) (Ps'.liftCompιIso _ hT) νh₃ (invOnSubcategory PP₃.ι χ₃ hφp₃) =
      compactSupportExchangeAux Ps'.fullyFaithfulι i₁₁ i₂₁ (PC'.liftCompιIso _ hSp)
        (PP₁'.liftCompιIso _ hO₁') (Ps'.liftCompιIso _ hR₁') (PP₁.liftCompιIso _ hO₁)
        (Ps.liftCompιIso _ hR₁) (Ps'.liftCompιIso _ hT) νh₁ (invOnSubcategory PP₁.ι χ₁ hφp₁) := by
  refine compactSupportExchangeAux_eq_of_refinement _ _ _ _ _ _ _ _ _ _ _ hφp₁ _ _ _ _ _ _ _ _
    hφp₃ conj conj' χπ hχ fun M ↦ ?_
  obtain ⟨e, e', hE, hx, hy⟩ := H M
  refine ⟨e, e', hE, ?_, ?_⟩
  · simpa [ObjectProperty.liftCompιIso] using hx
  · simpa [ObjectProperty.liftCompιIso] using hy

end Shape

end AlgebraicGeometry.ProEtale.CondensedRing
