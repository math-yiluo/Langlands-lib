/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# Germs of sections along a factorisation

Let `F` be a pro-étale sheaf on `Y`, `w : W ⟶ Y` a morphism and `y : P ⟶ W` a morphism with
`y ≫ w = s`. A global section `n` of `w^* F` restricts along `y` to a global section of
`y^* w^* F ≅ s^* F`: this is the *germ* `factorGerm h n` of `n` at `y`, for
`h : y ≫ w = s`. For `P` the spectrum of an algebraically closed field, `s` is a geometric
point of `Y`, `y` a lift of `s` to `W`, and the germ is the value of `n` in the stalk
`Γ(P, s^* F)` of `F` at `s`.

Germs compose (`AlgebraicGeometry.ProEtale.factorGerm_comp`): the germ at `x` of the germ
at `y` is the germ at `x ≫ y`. Two instances are the main applications:

- for an automorphism `τ` of `P` with `τ ≫ s = s`, the germ at `τ` is the action of `τ` on the
  stalk `Γ(P, s^* F)`; for `P = Spec Ω` and `τ` induced by a field automorphism this is the
  Galois action on the stalk at a geometric point;
- for an automorphism `g` of `W` over `Y`, the germ at `g` is the action of the deck
  transformation `g` on the global sections of `w^* F`.

## Main definitions

- `AlgebraicGeometry.ProEtale.factorGerm`: the germ `Γ(W, w^* F) ⟶ Γ(P, s^* F)` along
  `y ≫ w = s`.

## Main results

- `AlgebraicGeometry.ProEtale.factorGerm_comp`: germs compose.
- `AlgebraicGeometry.ProEtale.factorGerm_naturality`: germs are natural in the sheaf.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {Q P W Y : Scheme.{u}}

/-- The germ `Γ(W, w^* F) ⟶ Γ(P, s^* F)` of global sections of `w^* F` along a factorisation
`y ≫ w = s`: the restriction along `y`, followed by `y^* w^* F ≅ s^* F`. -/
noncomputable def factorGerm {w : W ⟶ Y} {y : P ⟶ W} {s : P ⟶ Y} (h : y ≫ w = s)
    (F : Sheaf (ProEt.topology Y) A) :
    (Sheaf.Γ _ A).obj ((w)^*[A].obj F) ⟶ (Sheaf.Γ _ A).obj ((s)^*[A].obj F) :=
  (globalSectionsToUpperStar A y).app _ ≫ (Sheaf.Γ _ A).map ((upperStarFactor A h).inv.app F)

/-- The germs are natural in the sheaf. -/
@[reassoc]
lemma factorGerm_naturality {w : W ⟶ Y} {y : P ⟶ W} {s : P ⟶ Y} (h : y ≫ w = s)
    {F G : Sheaf (ProEt.topology Y) A} (f : F ⟶ G) :
    (Sheaf.Γ _ A).map ((w)^*[A].map f) ≫ factorGerm A h G =
      factorGerm A h F ≫ (Sheaf.Γ _ A).map ((s)^*[A].map f) := by
  have n := (globalSectionsToUpperStar A y).naturality ((w)^*[A].map f)
  simp only [Functor.comp_map] at n
  simp only [factorGerm]
  rw [reassoc_of% n, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact ((upperStarFactor A h).inv.naturality f)

/-- **Germs compose**: the germ along `x ≫ s = t` of the germ along `y ≫ w = s` is the germ
along `(x ≫ y) ≫ w = t`. -/
@[reassoc]
lemma factorGerm_comp {x : Q ⟶ P} {y : P ⟶ W} {w : W ⟶ Y} {s : P ⟶ Y} {t : Q ⟶ Y}
    (h : y ≫ w = s) (h' : x ≫ s = t) (h'' : (x ≫ y) ≫ w = t)
    (F : Sheaf (ProEt.topology Y) A) :
    factorGerm A h F ≫ factorGerm A h' F = factorGerm A h'' F := by
  have e := upperStarFactor_hom_app_assoc A h h' (rfl : x ≫ y = x ≫ y) h'' F
  rw [upperStarFactor_rfl] at e
  -- invert the identity of factorisation isomorphisms
  have e' : (upperStarComp A x y).hom.app ((w)^*[A].obj F) ≫
      (x)^*[A].map ((upperStarFactor A h).inv.app F) ≫ (upperStarFactor A h').inv.app F =
      (upperStarFactor A h'').inv.app F := by
    rw [← cancel_epi ((upperStarFactor A h'').hom.app F), ← reassoc_of% e]
    simp only [Iso.hom_inv_id_app, ← Functor.map_comp_assoc]
    simp
  have n := (globalSectionsToUpperStar A x).naturality ((upperStarFactor A h).inv.app F)
  simp only [Functor.comp_map] at n
  simp only [factorGerm, Category.assoc]
  rw [reassoc_of% n, ← reassoc_of% globalSectionsToUpperStar_comp]
  simp only [← Functor.map_comp, e']

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {W W' Y : Scheme.{u}}

/-- **Deck transformations and the counit.** Let `g : W' ⟶ W` be a morphism over `Y`, that is
`g ≫ w = w'`, and let `η : G ⟶ g_* G'`. The morphism `σ : w_* G ⟶ w'_* G'` given by `w_* η`
followed by `w_* g_* ≅ w'_*` (for `w = w'` and `g` a deck transformation, its action on `w_* G`)
satisfies

`w'^* σ ≫ ε_{w'} = (w'^* ≅ g^* w^*) ≫ g^* ε_w ≫ η^♭`

as morphisms `w'^* w_* G ⟶ G'`, where `η^♭ : g^* G ⟶ G'` is the adjoint transpose of `η`. -/
lemma upperStar_map_lowerStarFactor_comp_counit {w : W ⟶ Y} {w' : W' ⟶ Y} {g : W' ⟶ W}
    (hg : g ≫ w = w') {G : Sheaf (ProEt.topology W) A} {G' : Sheaf (ProEt.topology W') A}
    (η : G ⟶ (g)_*[A].obj G') :
    (w')^*[A].map ((w)_*[A].map η ≫ (lowerStarFactor A hg).hom.app G') ≫
        (upperStarLowerStarAdjunction A w').counit.app G' =
      (upperStarFactor A hg).hom.app ((w)_*[A].obj G) ≫
        (g)^*[A].map ((upperStarLowerStarAdjunction A w).counit.app G) ≫
        ((upperStarLowerStarAdjunction A g).homEquiv G G').symm η := by
  apply ((upperStarLowerStarAdjunction A w').homEquiv ((w)_*[A].obj G) G').injective
  have h₁ := ((upperStarLowerStarAdjunction A w').homEquiv_counit (X := (w)_*[A].obj G)
    (Y := G') ((w)_*[A].map η ≫ (lowerStarFactor A hg).hom.app G')).symm
  rw [h₁, Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor]
  set θ := ((upperStarLowerStarAdjunction A g).homEquiv G G').symm η
  set M := (w)_*[A].obj G
  have n : (lowerStarFactor A hg).hom.app ((g)^*[A].obj ((w)^*[A].obj M)) ≫
      (w')_*[A].map ((g)^*[A].map ((upperStarLowerStarAdjunction A w).counit.app G) ≫ θ) =
      (w)_*[A].map ((g)_*[A].map
        ((g)^*[A].map ((upperStarLowerStarAdjunction A w).counit.app G) ≫ θ)) ≫
        (lowerStarFactor A hg).hom.app G' :=
    ((lowerStarFactor A hg).hom.naturality _).symm
  have n₂ : (upperStarLowerStarAdjunction A g).unit.app ((w)^*[A].obj M) ≫
      (g)_*[A].map ((g)^*[A].map ((upperStarLowerStarAdjunction A w).counit.app G)) =
      (upperStarLowerStarAdjunction A w).counit.app G ≫
        (upperStarLowerStarAdjunction A g).unit.app G :=
    ((upperStarLowerStarAdjunction A g).unit.naturality _).symm
  have h₂ : (upperStarLowerStarAdjunction A g).unit.app G ≫ (g)_*[A].map θ = η :=
    ((upperStarLowerStarAdjunction A g).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have h₃ : (upperStarLowerStarAdjunction A w).unit.app M ≫
      (w)_*[A].map ((upperStarLowerStarAdjunction A w).counit.app G) = 𝟙 M :=
    (upperStarLowerStarAdjunction A w).right_triangle_components G
  rw [← Functor.map_comp, n, ← Functor.map_comp_assoc, Functor.map_comp (g)_*[A],
    reassoc_of% n₂, h₂, Functor.map_comp, ← Category.assoc, ← Category.assoc, h₃,
    Category.id_comp]

end AlgebraicGeometry.ProEtale
