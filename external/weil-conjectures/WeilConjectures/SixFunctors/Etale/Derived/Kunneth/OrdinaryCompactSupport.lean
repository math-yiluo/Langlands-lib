/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-!
# The Künneth formula for compactly supported étale cohomology

Let `k` be a separably closed field and `Λ` a finite ring whose exponent is invertible in `k`.
For `k`-schemes `X`, `Y` with compactifications `j_X : X ⟶ X̄`, `j_Y : Y ⟶ Ȳ` (open
immersions into proper `k`-schemes), compactly supported cohomology is
`RΓ_c(X, E) = RΓ(X̄, j_{X!} E)`, and the Künneth formula of
`AlgebraicGeometry.Etale.nonempty_iso_kunneth_of_isSepClosed` for `X̄` and `Ȳ` gives

`RΓ_c(X, E) ⊗ᴸ RΓ_c(Y, K) ≅ RΓ_c(X ×_k Y, Lp₁^* E ⊗ᴸ Lp₂^* K)`,

the right-hand side computed along the compactification `X ×_k Y ⟶ X̄ ×_k Ȳ`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kunneth_compactSupport_of_isSepClosed`
  (`cor-kun-compact-kunneth`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The projection formula `j_!(K ⊗ᴸ Lj^* M) ≅ j_! K ⊗ᴸ M` for an open immersion `j`, at
objects `K` and `M` (`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`). -/
noncomputable def openImmersionLowerShriekTensorIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D((j)_!open[ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K)).obj M :=
  ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} Λ) j).app K).app M

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

omit [Finite Λ] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))] in
/-- The projection formula for an open immersion `j`, with the extension by zero in the right
factor: `N ⊗ᴸ j_! M ≅ j_!(Lj^* N ⊗ᴸ M)`. -/
theorem nonempty_iso_derivedTensor_openImmersionLowerShriek {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj N).obj
        (D((j)_!open[ModuleCat.{u + 1} Λ]).obj M) ≅
      D((j)_!open[ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj N)).obj M)) := by
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X
  obtain ⟨γ⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) U
  exact ⟨(β.app N).app _ ≪≫ (openImmersionLowerShriekTensorIso Λ j M N).symm ≪≫
    D((j)_!open[ModuleCat.{u + 1} Λ]).mapIso ((γ.app M).app _)⟩

/-- `j_!(j'_! Z) ≅ J_! Z` for open immersions with `j' ≫ j = J`. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekCompObjIso {V U X : Scheme.{u}}
    (j' : V ⟶ U) (j : U ⟶ X) (J : V ⟶ X) [IsOpenImmersion j'] [IsOpenImmersion j]
    [IsOpenImmersion J] (h : j' ≫ j = J)
    (Z : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D((j)_!open[ModuleCat.{u + 1} Λ]).obj (D((j')_!open[ModuleCat.{u + 1} Λ]).obj Z) ≅
      D((J)_!open[ModuleCat.{u + 1} Λ]).obj Z :=
  ((mapDerivedCategoryOpenImmersionLowerShriekComp _ j' j).app Z).symm ≪≫
    (mapDerivedCategoryOpenImmersionLowerShriekCongr _ h).app Z

/-- Base change for the extension by zero, objectwise: `j'_!(Lg'^* K) ≅ Lg''^*(j_! K)` for a
cartesian square `g' ≫ j = j' ≫ g''` with `j` an open immersion. -/
noncomputable def derivedOpenImmersionLowerShriekBaseChangeObjIso {U' U Z' Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z} [IsOpenImmersion j]
    [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D((j')_!open[ModuleCat.{u + 1} Λ]).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (L((g'')^*[ModuleCat.{u + 1} Λ])).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) :=
  (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).app K

/-- `Lh^*(Lg^* (j_! K)) ≅ j'_!(Lg'^* K)` for a cartesian square `g' ≫ j = j' ≫ (h ≫ g)` with
`j` an open immersion. -/
noncomputable def leftDerivedUpperStarCompOpenImmersionLowerShriekIso {U' U Z' Y Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {h : Z' ⟶ Y} {g : Y ⟶ Z} [IsOpenImmersion j]
    [IsOpenImmersion j'] (hsq : IsPullback g' j' j (h ≫ g))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K)) ≅
      D((j')_!open[ModuleCat.{u + 1} Λ]).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h g).symm.app _ ≪≫
    (derivedOpenImmersionLowerShriekBaseChangeObjIso Λ hsq K).symm

/-- `Lh^*(Lg^* E) ≅ Lp^* E` for `h ≫ g = p`. -/
noncomputable def leftDerivedUpperStarCompObjIso {T S R : Scheme.{u}} (h : T ⟶ S) (g : S ⟶ R)
    (p : T ⟶ R) (hp : h ≫ g = p)
    (E : DerivedCategory (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj E) ≅
      (L((p)^*[ModuleCat.{u + 1} Λ])).obj E :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h g p hp.symm).app E).symm

omit [Finite Λ] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))] in
/-- The extension by zero along a product of open immersions is the external product of the
extensions by zero: in the diagram of cartesian squares `V = X ×_{X̄} W̄` (projections `r`,
`J₁`) and `W = V ×_{Ȳ} Y` (projections `J'`, `p₂`), with `J = J' ≫ J₁` and `p₁ = J' ≫ r`,

`Lq₁^* j_{X!} E ⊗ᴸ Lq₂^* j_{Y!} K ≅ J_! (Lp₁^* E ⊗ᴸ Lp₂^* K)`. -/
theorem nonempty_iso_derivedTensor_leftDerivedUpperStar_openImmersionLowerShriek
    {X Y Xb Yb V W Wb : Scheme.{u}} (jX : X ⟶ Xb) (jY : Y ⟶ Yb) [IsOpenImmersion jX]
    [IsOpenImmersion jY] (q₁ : Wb ⟶ Xb) (q₂ : Wb ⟶ Yb) (r : V ⟶ X) (J₁ : V ⟶ Wb)
    [IsOpenImmersion J₁] (hV : IsPullback r J₁ jX q₁) (p₁ : W ⟶ X) (p₂ : W ⟶ Y) (J' : W ⟶ V)
    [IsOpenImmersion J'] (hW : IsPullback p₂ J' jY (J₁ ≫ q₂)) (hJ'r : J' ≫ r = p₁)
    (J : W ⟶ Wb) [IsOpenImmersion J] (hJ : J' ≫ J₁ = J)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) Wb).obj
          ((L((q₁)^*[ModuleCat.{u + 1} Λ])).obj (D((jX)_!open[ModuleCat.{u + 1} Λ]).obj E))).obj
        ((L((q₂)^*[ModuleCat.{u + 1} Λ])).obj (D((jY)_!open[ModuleCat.{u + 1} Λ]).obj K)) ≅
      D((J)_!open[ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
          ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
        ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) := by
  obtain ⟨f⟩ := nonempty_iso_derivedTensor_openImmersionLowerShriek Λ J'
    ((L((r)^*[ModuleCat.{u + 1} Λ])).obj E) ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K)
  exact ⟨((derivedTensor (ModuleCat.{u + 1} Λ) Wb).mapIso
      (derivedOpenImmersionLowerShriekBaseChangeObjIso Λ hV E).symm).app _ ≪≫
    (openImmersionLowerShriekTensorIso Λ J₁ _ _).symm ≪≫
    D((J₁)_!open[ModuleCat.{u + 1} Λ]).mapIso
      (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj _).mapIso
          (leftDerivedUpperStarCompOpenImmersionLowerShriekIso Λ hW K) ≪≫ f ≪≫
        D((J')_!open[ModuleCat.{u + 1} Λ]).mapIso
          (((derivedTensor (ModuleCat.{u + 1} Λ) W).mapIso
            (leftDerivedUpperStarCompObjIso Λ J' r p₁ hJ'r E)).app _)) ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekCompObjIso Λ J' J₁ J hJ _⟩

/-- Blueprint `cor-kun-compact-kunneth`: the Künneth formula for compactly supported
cohomology.

Let `k` be separably closed and `Λ` a finite ring whose exponent is invertible in `k`. Let
`j_X : X ⟶ X̄` and `j_Y : Y ⟶ Ȳ` be open immersions into proper `k`-schemes, let `W` be the
fibre product of `X` and `Y` over `k` (projections `p₁`, `p₂`), `W̄` that of `X̄` and `Ȳ`
(projections `q₁`, `q₂`), and `J : W ⟶ W̄` the product open immersion. Then for all
`E ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)`, with `RΓ_c(X, E) = RΓ(X̄, j_{X!} E)`,

`RΓ_c(X, E) ⊗ᴸ RΓ_c(Y, K) ≅ RΓ(W̄, J_! (Lp₁^* E ⊗ᴸ Lp₂^* K)) = RΓ_c(W, Lp₁^* E ⊗ᴸ Lp₂^* K)`.

It is the Künneth formula for `X̄` and `Ȳ` (`proposition-ordinary-external-kunneth--1`), applied to
`j_{X!} E` and `j_{Y!} K`, followed by the identification `Lq₁^* j_{X!} E ⊗ᴸ Lq₂^* j_{Y!} K ≅
J_! (Lp₁^* E ⊗ᴸ Lp₂^* K)` given by base change and the projection formula for extensions by
zero. -/
theorem nonempty_iso_kunneth_compactSupport_of_isSepClosed {X Y Xb Yb : Scheme.{u}}
    (jX : X ⟶ Xb) (jY : Y ⟶ Yb) [IsOpenImmersion jX] [IsOpenImmersion jY]
    (bX : Xb ⟶ Spec (.of k)) (bY : Yb ⟶ Spec (.of k)) [IsProper bX] [IsProper bY]
    {W Wb : Scheme.{u}} (p₁ : W ⟶ X) (p₂ : W ⟶ Y) (sq : IsPullback p₁ p₂ (jX ≫ bX) (jY ≫ bY))
    (q₁ : Wb ⟶ Xb) (q₂ : Wb ⟶ Yb) (sqb : IsPullback q₁ q₂ bX bY)
    (J : W ⟶ Wb) [IsOpenImmersion J] (hJ₁ : J ≫ q₁ = p₁ ≫ jX) (hJ₂ : J ≫ q₂ = p₂ ≫ jY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Xb).obj
          (D((jX)_!open[ModuleCat.{u + 1} Λ]).obj E) ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Yb).obj
          (D((jY)_!open[ModuleCat.{u + 1} Λ]).obj K) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Wb).obj
        (D((J)_!open[ModuleCat.{u + 1} Λ]).obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
              ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
            ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K)))) := by
  obtain ⟨e₁⟩ := nonempty_iso_kunneth_of_isSepClosed Λ bX bY q₁ q₂ sqb
    (D((jX)_!open[ModuleCat.{u + 1} Λ]).obj E) (D((jY)_!open[ModuleCat.{u + 1} Λ]).obj K)
  -- the intermediate scheme `V = X ×_{X̄} W̄ = X ×_k Ȳ`
  have hV : IsPullback (pullback.fst jX q₁) (pullback.snd jX q₁) jX q₁ :=
    IsPullback.of_hasPullback jX q₁
  let J' : W ⟶ pullback jX q₁ := pullback.lift p₁ J hJ₁.symm
  have hJ'r : J' ≫ pullback.fst jX q₁ = p₁ := pullback.lift_fst _ _ _
  have hJ'J₁ : J' ≫ pullback.snd jX q₁ = J := pullback.lift_snd _ _ _
  have hW : IsPullback p₂ J' jY (pullback.snd jX q₁ ≫ q₂) :=
    IsPullback.of_bot (by rw [hJ'r]; exact sq.flip)
      (by rw [reassoc_of% hJ'J₁, hJ₂]) (hV.paste_vert sqb).flip
  have : IsOpenImmersion J' :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hW inferInstance
  obtain ⟨e₂⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_openImmersionLowerShriek Λ
    jX jY q₁ q₂ _ _ hV p₁ p₂ J' hW hJ'r J hJ'J₁ E K
  exact ⟨e₁ ≪≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Wb).mapIso e₂⟩

end Etale

end AlgebraicGeometry
