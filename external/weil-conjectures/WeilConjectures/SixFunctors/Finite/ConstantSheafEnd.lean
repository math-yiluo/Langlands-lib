/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!

# Stalks of the endomorphisms of `f_* Λ` given by endomorphisms over the base

Let `f : Y ⟶ X` be finite and let `g : Y ⟶ Y` be a finite endomorphism over `X`, so that
`g ≫ f = f`. Pulling back sections along `g` is an endomorphism `g^♯` of `f_* Λ`
(`AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver`). At a geometric point `y` of `X`,
the stalk of `f_* Λ` is the product of the stalks of `Λ` at the geometric points `t` of `Y` over
`y` (`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`), and `g^♯` moves the factor at
`t ≫ g` to the factor at `t`: its composite with the restriction `ρ_t` of germs to `t` factors
through the restriction `ρ_{t ≫ g}` to `t ≫ g`.

## Main results

- `AlgebraicGeometry.Etale.sheafFiber_map_lowerStarConstantSheafEndOfOver_stalkRestrict`:
  `(g^♯)_y ≫ ρ_t = ρ_{t ≫ g} ≫ θ` for an explicit `θ : Λ_{t ≫ g} ⟶ Λ_t`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

open Scheme Etale Scheme.Hom

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Pulling back sections along `g` on stalks.** For a finite `f : Y ⟶ X`, a finite
endomorphism `g` of `Y` over `X` and a geometric point `t` of `Y` over `y`, restricting a germ
of `g^♯ s` to `t` is restricting the germ of `s` to `t ≫ g`, followed by the map
`Λ_{t ≫ g} ⟶ Λ_t` given by the unit `ε : Λ ⟶ g_* Λ` and the restriction of germs along `g`:

```
  (f_* Λ)_y ----(g^♯)_y----> (f_* Λ)_y
      |                          |
  ρ_{t ≫ g}                      ρ_t
      v                          v
  Λ_{t ≫ g} --ε--> (g_* Λ)_{t ≫ g} --ρ_t--> Λ_t
```
-/
lemma Etale.sheafFiber_map_lowerStarConstantSheafEndOfOver_stalkRestrict {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] (g : Y ⟶ Y) [IsFinite g] (h : g ≫ f = f) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ X) (t : GeometricFiber f y) :
    (pointSmallEtale y).sheafFiber.map (lowerStarConstantSheafEndOfOver (Λ := Λ) f g h) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t (𝟙_ _) =
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y
          ⟨t.1 ≫ g, by rw [Category.assoc, h, t.2]⟩ (𝟙_ _) ≫
        (pointSmallEtale (t.1 ≫ g)).sheafFiber.map
          (Functor.LaxMonoidal.ε (g)_*[ModuleCat.{u + 1} Λ]) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) g (t.1 ≫ g) ⟨t.1, rfl⟩ (𝟙_ _) := by
  rw [lowerStarConstantSheafEndOfOver_eq, Functor.map_comp, Category.assoc,
    Etale.sheafFiber_map_lowerStarComp_hom_app_stalkRestrict (ModuleCat.{u + 1} Λ) g f f h.symm
      y t, ← Category.assoc, ← Etale.stalkRestrict_naturality, Category.assoc]

end AlgebraicGeometry
