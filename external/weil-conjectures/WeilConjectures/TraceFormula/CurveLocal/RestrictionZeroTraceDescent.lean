/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!

# Descent of a vanishing along a trace of invertible degree

The formal core of blueprint `lemma-descent-vanishing-finite-etale`: in the derived category of
`Λ`-modules, consider a commutative square
```
M₁ --r--> M₂
 |p₁       |p₂
 v         v
M₁' --r'-> M₂'
```
and a *trace* `t : M₂' ⟶ M₂` with `p₂ ≫ t = d • 𝟙` for an integer `d` invertible in `Λ`. Then
`d • r = r ≫ p₂ ≫ t = p₁ ≫ r' ≫ t`, so `r' = 0` forces `d • r = 0`, hence `r = 0`, since
multiplication by `d` is an isomorphism of every object of `D(Λ)` (it is so on cohomology).

## Main statements

- `DerivedCategory.isIso_smul_id_of_isUnit`: multiplication by an integer invertible in `Λ` is an
  isomorphism in `D(Λ)`.
- `DerivedCategory.eq_zero_of_comp_trace_of_isUnit`: the descent of the vanishing of `r'` to `r`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace DerivedCategory

variable {Λ : Type u} [CommRing Λ] [HasDerivedCategory (ModuleCat.{v} Λ)]

/-- Multiplication by an integer `d` invertible in `Λ` is an isomorphism of every object of the
derived category of `Λ`-modules: on each cohomology module it is multiplication by the unit
`d` of `Λ`. -/
lemma isIso_smul_id_of_isUnit (K : DerivedCategory (ModuleCat.{v} Λ)) {d : ℤ}
    (hd : IsUnit (d : Λ)) : IsIso (d • 𝟙 K) := by
  rw [isIso_iff]
  intro n
  rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]
  obtain ⟨w, hw⟩ := hd
  refine ⟨⟨(ModuleCat.ofHom (LinearMap.lsmul Λ _ (w⁻¹ : Λˣ))), ?_, ?_⟩⟩ <;>
  · ext x
    simp [← hw, smul_smul, ← Int.cast_smul_eq_zsmul Λ]

/-- **Descent of a vanishing along a trace of invertible degree** (blueprint
`lemma-descent-vanishing-finite-etale`, formal core): for a commutative square
`r ≫ p₂ = p₁ ≫ r'` and a trace `t` with `p₂ ≫ t = d • 𝟙`, `d` invertible in `Λ`, the vanishing
of `r'` implies that of `r`. -/
theorem eq_zero_of_comp_trace_of_isUnit {M₁ M₂ M₁' M₂' : DerivedCategory (ModuleCat.{v} Λ)}
    {r : M₁ ⟶ M₂} {r' : M₁' ⟶ M₂'} {p₁ : M₁ ⟶ M₁'} {p₂ : M₂ ⟶ M₂'} (w : r ≫ p₂ = p₁ ≫ r')
    {t : M₂' ⟶ M₂} {d : ℤ} (ht : p₂ ≫ t = d • 𝟙 M₂) (hd : IsUnit (d : Λ)) (hr' : r' = 0) :
    r = 0 := by
  have := isIso_smul_id_of_isUnit M₂ hd
  have h : r ≫ (d • 𝟙 M₂) = 0 := by
    rw [← ht, ← Category.assoc, w, hr', comp_zero, zero_comp]
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, zero_comp] using
    h =≫ inv (d • 𝟙 M₂)

end DerivedCategory
