/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.TraceFormula.CurveLocal.Model

/-!

# The étale supported restriction and the strictly local model

For a cartesian square `ι ≫ c = d ≫ Δ` of schemes with `c` and `d` compactifiable, and finite
coefficients `Λ`, the *étale exchange restriction*
```
ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P
```
(`AlgebraicGeometry.Etale.exchangeRestriction`) is the `Rd_! ⊣ Rd^!` adjoint of the inverse of
compact-support base change followed by `LΔ^*` of the counit of `Rc_! ⊣ Rc^!`
(`CategoryTheory.Adjunction.exchangeRestriction`). For the fixed square of the Frobenius graph it
is the étale form of the supported restriction of blueprint `lemma-local-term-restriction-map--1`.

This file sets up its pullback to the strictly local model of a curve
(`AlgebraicGeometry.Etale.CurveLocalModel`): for a cartesian square `ι ≫ graph = d ≫ diagonal`
of the transposed graph `(h, id)` and the diagonal of `X ×_k X`, the strict localization
`τ : T ⟶ X ×_k X` at `(y, y)` pulls the square back to the square `Y = G ×_T B` of the model,
through the maps `τ_G : G ⟶ X`, `τ_B : B ⟶ X` and `τ_Y : Y ⟶ F`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section ExchangeRestriction

variable {S C X F : Scheme.{u}} {c : C ⟶ S} {Δ : X ⟶ S} {ι : F ⟶ C} {d : F ⟶ X}
  [HasCompactification c] [HasCompactification d] [QuasiCompact d]

/-- Compact-support base change `Rc_! ⋙ LΔ^* ≅ Lι^* ⋙ Rd_!` for a cartesian square
`ι ≫ c = d ≫ Δ`, with finite coefficients
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
noncomputable def lowerShriekBaseChangeIso (sq : IsPullback ι d c Δ) :
    R(c)_![ModuleCat.{u + 1} Λ] ⋙ L((Δ)^*[ModuleCat.{u + 1} Λ]) ≅
      L((ι)^*[ModuleCat.{u + 1} Λ]) ⋙ R(d)_![ModuleCat.{u + 1} Λ] :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)

/-- The **étale exchange restriction** `ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P` of a cartesian square
`ι ≫ c = d ≫ Δ` (blueprint `lemma-local-term-restriction-map--1`, (2)): the `Rd_! ⊣ Rd^!` adjoint of
the inverse of compact-support base change followed by `LΔ^*` of the counit of `Rc_! ⊣ Rc^!`. -/
noncomputable def exchangeRestriction (sq : IsPullback ι d c Δ)
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(c)^![Λ]).obj P) ⟶
      (R(d)^![Λ]).obj ((L((Δ)^*[ModuleCat.{u + 1} Λ])).obj P) :=
  (mateEquiv (rightDerivedUpperShriekAdjunction Λ c) (rightDerivedUpperShriekAdjunction Λ d)
    (TwoSquare.mk _ _ _ _ (lowerShriekBaseChangeIso Λ sq).inv)).app P

/-- The étale exchange restriction is the `Rd_! ⊣ Rd^!` adjoint of the inverse of compact-support
base change followed by `LΔ^*` of the counit of `Rc_! ⊣ Rc^!`. -/
lemma exchangeRestriction_eq_homEquiv (sq : IsPullback ι d c Δ)
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    exchangeRestriction Λ sq P = (rightDerivedUpperShriekAdjunction Λ d).homEquiv _ _
      ((lowerShriekBaseChangeIso Λ sq).inv.app _ ≫
        (L((Δ)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekAdjunction Λ c).counit.app P)) :=
  Adjunction.mateEquiv_app_eq_homEquiv _ _ _ _ _ P

end ExchangeRestriction

namespace CurveLocalModel

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

/-- The projection `τ_G : G ⟶ X` of the graph `G` inside `T` to the source of the graph. -/
noncomputable abbrev τG : M.G ⟶ M.X := pullback.fst M.graph M.τ

/-- The projection `τ_B : B ⟶ X` of the diagonal `B` inside `T` to `X`. -/
noncomputable abbrev τB : M.B ⟶ M.X := pullback.fst (pullback.diagonal M.f) M.τ

/-- The inclusion `ι' : Y ⟶ G` of the intersection `Y = G ×_T B`. -/
noncomputable abbrev ιY : M.Y ⟶ M.G := pullback.fst M.a M.b

/-- The square `Y = G ×_T B` of the model. -/
lemma isPullback_ιY : IsPullback M.ιY M.yB M.a M.b :=
  IsPullback.of_hasPullback M.a M.b

variable {F : Scheme.{u}} {ι d : F ⟶ M.X} (hsq : IsPullback ι d M.graph (pullback.diagonal M.f))

lemma ιY_τG_graph : (M.ιY ≫ M.τG) ≫ M.graph = (M.yB ≫ M.τB) ≫ pullback.diagonal M.f := by
  simp only [Category.assoc, pullback.condition, M.isPullback_ιY.w_assoc]

/-- The map `τ_Y : Y ⟶ F` of the intersection `Y = G ×_T B` to the fixed scheme `F`. -/
noncomputable def τY : M.Y ⟶ F :=
  hsq.lift (M.ιY ≫ M.τG) (M.yB ≫ M.τB) M.ιY_τG_graph

@[reassoc (attr := simp)]
lemma τY_ι : M.τY hsq ≫ ι = M.ιY ≫ M.τG :=
  hsq.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma τY_d : M.τY hsq ≫ d = M.yB ≫ M.τB :=
  hsq.lift_snd _ _ _

/-- `G = X ×_{X × X} T`: the square `τ_G ≫ graph = a ≫ τ` is cartesian. -/
lemma isPullback_τG : IsPullback M.τG M.a M.graph M.τ :=
  IsPullback.of_hasPullback M.graph M.τ

/-- `B = X ×_{X × X} T`: the square `τ_B ≫ diagonal = b ≫ τ` is cartesian. -/
lemma isPullback_τB : IsPullback M.τB M.b (pullback.diagonal M.f) M.τ :=
  IsPullback.of_hasPullback (pullback.diagonal M.f) M.τ

/-- `Y = F ×_X B`: the square `τ_Y ≫ d = y_B ≫ τ_B` is cartesian. -/
lemma isPullback_τY : IsPullback (M.τY hsq) M.yB d M.τB := by
  refine IsPullback.of_right ?_ (M.τY_d hsq) hsq
  rw [M.τY_ι hsq, M.isPullback_τB.w]
  exact M.isPullback_ιY.paste_horiz M.isPullback_τG

end CurveLocalModel

end AlgebraicGeometry.Etale
