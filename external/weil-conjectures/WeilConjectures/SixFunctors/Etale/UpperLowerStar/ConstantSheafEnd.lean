/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# Endomorphisms of `f_* Λ` from endomorphisms over the base

For `f : Y ⟶ X` and an endomorphism `g : Y ⟶ Y` over `X`, pulling back sections along `g`
gives an endomorphism of the pushforward `f_* Λ` of the constant sheaf, the monoidal unit `𝟙_`.
The identification `g^* Λ ≅ Λ` is the unit isomorphism of the strong monoidal structure
`AlgebraicGeometry.Etale.monoidal_upperStar` of `g^*`.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver`: for `f : Y ⟶ X` and
  `g : Y ⟶ Y` with `g ≫ f = f`, the endomorphism of `f_* Λ` given by pulling back sections
  along `g`.
- `AlgebraicGeometry.Etale.lowerStarConstantSheafMul`: the multiplication
  `f_* Λ ⊗ f_* Λ ⟶ f_* Λ` of the monoid object `f_* Λ`.

## Main results

- `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_id` and
  `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_comp`: the construction is
  contravariantly functorial in `g`. Both reduce, via
  `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_eq`, to the compatibility of the
  unit `ε` of the lax monoidal pushforwards with the identity and composition isomorphisms
  (`AlgebraicGeometry.Etale.ε_lowerStar_id` and `AlgebraicGeometry.Etale.ε_lowerStar_comp`).
- `AlgebraicGeometry.Etale.lowerStarConstantSheafMul_comp_lowerStarConstantSheafEndOfOver`:
  pulling back sections is multiplicative, the composition isomorphisms of pushforwards being
  monoidal.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

open scoped CategoryTheory.Obj

noncomputable section

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- For `f : Y ⟶ X` and an endomorphism `g : Y ⟶ Y` over `X`, the endomorphism of `f_* Λ`
pulling back sections along `g`: `f_*` of the unit of `g^* ⊣ g_*`, followed by the unit
isomorphism `g^* Λ ≅ Λ` of the monoidal pullback and the composition isomorphism of
pushforwards,

```
f_* Λ --f_* η--> f_* g_* g^* Λ ≅ f_* g_* Λ ≅ (g ≫ f)_* Λ = f_* Λ
```
-/
def lowerStarConstantSheafEndOfOver {X Y : Scheme.{u}} (f : Y ⟶ X) (g : Y ⟶ Y)
    (h : g ≫ f = f) :
    (f)_*[ModuleCat Λ].obj (𝟙_ _) ⟶ (f)_*[ModuleCat Λ].obj (𝟙_ _) :=
  (f)_*[ModuleCat Λ].map ((upperStarLowerStarAdjunction _ g).unit.app _ ≫
      (g)_*[ModuleCat Λ].map (Functor.Monoidal.εIso (g)^*[ModuleCat Λ]).inv) ≫
    (lowerStarComp _ g f f h.symm).hom.app _

/-- The unit of `g^* ⊣ g_*` at `Λ` followed by `g_*` of the unit isomorphism `g^* Λ ≅ Λ` is the
unit `ε : Λ ⟶ g_* Λ` of the lax monoidal pushforward, the adjunction being monoidal. -/
lemma unit_app_comp_lowerStar_map_η {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    (upperStarLowerStarAdjunction (ModuleCat Λ) g).unit.app (𝟙_ _) ≫
      (g)_*[ModuleCat Λ].map (Functor.Monoidal.εIso (g)^*[ModuleCat Λ]).inv =
      Functor.LaxMonoidal.ε (g)_*[ModuleCat Λ] :=
  (upperStarLowerStarAdjunction (ModuleCat Λ) g).unit_app_unit_comp_map_η

/-- The unit `ε : Λ ⟶ (𝟙 V)_* Λ` of the lax monoidal pushforward along the identity is the
identity isomorphism `AlgebraicGeometry.Etale.lowerStarId` at `Λ`. -/
lemma ε_lowerStar_id (V : Scheme.{u}) :
    Functor.LaxMonoidal.ε (𝟙 V)_*[ModuleCat Λ] =
      (lowerStarId (ModuleCat Λ) V).inv.app (𝟙_ _) :=
  Functor.ε_sheafPushforwardContinuous_of_iso_id (ModuleCat Λ) V.smallEtaleTopology _
    (hF := isContinuous_overPullback (𝟙 V))

/-- The unit `ε` of the lax monoidal pushforward along a composite `h₁ ≫ h₂` is the composite
`Λ ⟶ (h₂)_* Λ ⟶ (h₂)_* (h₁)_* Λ ≅ (h₁ ≫ h₂)_* Λ` of the units of `(h₂)_*` and `(h₁)_*` and the
composition isomorphism `AlgebraicGeometry.Etale.lowerStarComp`. -/
lemma ε_lowerStar_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂) :
    Functor.LaxMonoidal.ε (h₁₂)_*[ModuleCat Λ] =
      Functor.LaxMonoidal.ε (h₂)_*[ModuleCat Λ] ≫
        (h₂)_*[ModuleCat Λ].map (Functor.LaxMonoidal.ε (h₁)_*[ModuleCat Λ]) ≫
          (lowerStarComp (ModuleCat Λ) h₁ h₂ h₁₂ hh₁₂).hom.app (𝟙_ _) :=
  Functor.ε_sheafPushforwardContinuous_of_iso_comp (ModuleCat Λ) R.smallEtaleTopology
    S.smallEtaleTopology T.smallEtaleTopology _ (hF := isContinuous_overPullback h₂)
    (hG := isContinuous_overPullback h₁) (hFG := isContinuous_overPullback h₁₂)

/-- `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver f g h` is `f_*` of the unit
`ε : Λ ⟶ g_* Λ` of the lax monoidal pushforward followed by the composition isomorphism. -/
lemma lowerStarConstantSheafEndOfOver_eq {X Y : Scheme.{u}} (f : Y ⟶ X) (g : Y ⟶ Y)
    (h : g ≫ f = f) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f g h =
      (f)_*[ModuleCat Λ].map (Functor.LaxMonoidal.ε (g)_*[ModuleCat Λ]) ≫
        (lowerStarComp _ g f f h.symm).hom.app _ :=
  congrArg (fun φ ↦ (f)_*[ModuleCat Λ].map φ ≫ (lowerStarComp _ g f f h.symm).hom.app _)
    (unit_app_comp_lowerStar_map_η g)

/-- The identity of `Y` acts trivially on `f_* Λ`. -/
lemma lowerStarConstantSheafEndOfOver_id {X Y : Scheme.{u}} (f : Y ⟶ X) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f (𝟙 Y) (Category.id_comp f) = 𝟙 _ := by
  rw [lowerStarConstantSheafEndOfOver_eq, ε_lowerStar_id, lowerStarComp_id_left]
  simp [← Functor.map_comp]

/-- Pulling back sections is contravariant: the endomorphism attached to `g ≫ g'` is that of
`g'` followed by that of `g`, i.e. writing `End(g)` for
`AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver f g h`, the triangle

```
f_* Λ ---End(g')---> f_* Λ
     \                 |
   End(g ≫ g')       End(g)
         \             |
          v            v
            f_* Λ
```

commutes. -/
lemma lowerStarConstantSheafEndOfOver_comp {X Y : Scheme.{u}} (f : Y ⟶ X) (g g' : Y ⟶ Y)
    (h : g ≫ f = f) (h' : g' ≫ f = f) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f (g ≫ g') (by rw [Category.assoc, h', h]) =
      lowerStarConstantSheafEndOfOver f g' h' ≫ lowerStarConstantSheafEndOfOver f g h := by
  have key := congr_app (lowerStarComp_assoc' (ModuleCat Λ) g g' f (g ≫ g') f f rfl h'.symm
    (by rw [Category.assoc, h', h])) (𝟙_ _)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  rw [lowerStarConstantSheafEndOfOver_eq, lowerStarConstantSheafEndOfOver_eq,
    lowerStarConstantSheafEndOfOver_eq, ε_lowerStar_comp g g' (g ≫ g') rfl]
  simp only [Functor.map_comp, Category.assoc, key]
  rw [← NatTrans.naturality_assoc]
  rfl

/-- A variant of `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_id` for an
endomorphism that is merely equal to the identity. -/
lemma lowerStarConstantSheafEndOfOver_of_eq_id {X Y : Scheme.{u}} (f : Y ⟶ X) (g : Y ⟶ Y)
    (hg : g = 𝟙 Y) (h : g ≫ f = f) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f g h = 𝟙 _ := by
  subst hg
  exact lowerStarConstantSheafEndOfOver_id f

/-- A variant of `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_comp` for an
endomorphism that is merely equal to a composite. -/
lemma lowerStarConstantSheafEndOfOver_of_eq_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    (g g' g'' : Y ⟶ Y) (hg : g'' = g ≫ g') (h : g ≫ f = f) (h' : g' ≫ f = f)
    (h'' : g'' ≫ f = f) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f g'' h'' =
      lowerStarConstantSheafEndOfOver f g' h' ≫ lowerStarConstantSheafEndOfOver f g h := by
  subst hg
  exact lowerStarConstantSheafEndOfOver_comp f g g' h h'

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards of sheaves of
`Λ`-modules is monoidal. -/
instance isMonoidal_lowerStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    NatTrans.IsMonoidal (lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
  unfold lowerStarComp
  infer_instance

/-- The multiplication `f_* Λ ⊗ f_* Λ ⟶ f_* Λ` of functions: the multiplication of the monoid
object `f_* Λ`, the image of the monoid object `Λ` under the lax monoidal functor `f_*`. -/
def lowerStarConstantSheafMul {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (f)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _) ⊗ (f)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _) ⟶
      (f)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _) :=
  μ (f)_*[ModuleCat.{u + 1} Λ] (𝟙_ _) (𝟙_ _) ≫ (f)_*[ModuleCat.{u + 1} Λ].map (λ_ _).hom

/-- Pulling back sections along `g` is multiplicative:

```
f_* Λ ⊗ f_* Λ ---mul---> f_* Λ
      |                    |
 g^♯ ⊗ g^♯                g^♯
      v                    v
f_* Λ ⊗ f_* Λ ---mul---> f_* Λ
```

The unit `ε : Λ ⟶ g_* Λ` is a morphism of monoids, `f_*` preserves these, and the composition
isomorphism `g_* ⋙ f_* ≅ f_*` is monoidal. -/
lemma lowerStarConstantSheafMul_comp_lowerStarConstantSheafEndOfOver {X Y : Scheme.{u}}
    (f : Y ⟶ X) (g : Y ⟶ Y) (h : g ≫ f = f) :
    lowerStarConstantSheafMul (Λ := Λ) f ≫ lowerStarConstantSheafEndOfOver f g h =
      (lowerStarConstantSheafEndOfOver f g h ⊗ₘ lowerStarConstantSheafEndOfOver f g h) ≫
        lowerStarConstantSheafMul f := by
  have hε : (λ_ (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).hom ≫
      ε (g)_*[ModuleCat.{u + 1} Λ] =
      (ε (g)_*[ModuleCat.{u + 1} Λ] ⊗ₘ ε (g)_*[ModuleCat.{u + 1} Λ]) ≫
        μ (g)_*[ModuleCat.{u + 1} Λ] (𝟙_ _) (𝟙_ _) ≫
          (g)_*[ModuleCat.{u + 1} Λ].map (λ_ _).hom := by
    simpa using IsMonHom.mul_hom (ε (g)_*[ModuleCat.{u + 1} Λ])
  have hC := NatTrans.IsMonoidal.tensor
    (τ := (lowerStarComp (ModuleCat.{u + 1} Λ) g f f h.symm).hom)
    (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (𝟙_ _)
  rw [comp_μ] at hC
  have hn := (lowerStarComp (ModuleCat.{u + 1} Λ) g f f h.symm).hom.naturality
    (λ_ (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).hom
  simp only [Functor.comp_map] at hn
  simp only [lowerStarConstantSheafEndOfOver_eq, lowerStarConstantSheafMul, Category.assoc,
    ← Functor.map_comp_assoc, hε]
  rw [Functor.map_comp_assoc, ← μ_natural_assoc, Functor.map_comp_assoc, hn, reassoc_of% hC,
    tensorHom_comp_tensorHom_assoc]

end AlgebraicGeometry.Etale

end
