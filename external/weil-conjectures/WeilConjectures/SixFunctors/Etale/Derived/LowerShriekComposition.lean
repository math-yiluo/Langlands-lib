/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Comp
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-!
# The composition law for `Rf_!`

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes admitting compactifications. This file
constructs, for torsion coefficients, the composition isomorphism

`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`

of the compactly supported direct images on the unbounded derived categories of étale sheaves
(blueprint `proposition-composition-base-change-rf-shriek--1`).

Following the blueprint, compactify `g` as `Y ⟶[v] Ȳ ⟶[ḡ] S` and `f ≫ v` as
`X ⟶[a] X̄ ⟶[p] Ȳ`. Then `V = X̄ ×_Ȳ Y` with its open immersion `b : V ⟶ X̄` and proper
projection `p_Y : V ⟶ Y` gives the compactification `X ⟶[c] V ⟶[p_Y] Y` of `f`
(`AlgebraicGeometry.Compactification.restrict`), and `X ⟶[a] X̄ ⟶[p ≫ ḡ] S` is a
compactification of `f ≫ g` (`AlgebraicGeometry.Compactification.comp`). On these models

```
Rf_! ⋙ Rg_! = Dc_! ⋙ Rp_Y* ⋙ Dv_! ⋙ Rḡ_*
           ≅ Dc_! ⋙ Db_! ⋙ Rp_* ⋙ Rḡ_*        (v_! Rp_Y* ≅ Rp_* b_!)
           ≅ Da_! ⋙ R(p ≫ ḡ)_* = R(f ≫ g)_!
```

where the middle isomorphism is the exchange of an extension by zero with a proper
pushforward,
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring`,
which rests on proper base change. The comparison with the chosen compactifications of `f`
and `f ≫ g` is the independence of the compactification,
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`.

## Main definitions

- `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekComp`: the composition
  isomorphism `D((j' ≫ j)_!) ≅ D(j'_!) ⋙ D(j_!)` of derived extensions by zero.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationCompIso`: the isomorphism
  `Rf_!(e.restrict) ⋙ Rg_!(d) ≅ R(f ≫ g)_!(d.comp e)` on the models above.

The unbounded composition law `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`
needs no quasi-compactness and takes no closure of `X` in a product of compactifications.
Instead `Rf_!` is computed through any proper `π : P ⟶ Y` and any factorisation of `f` as a
proper `h : X ⟶ U` followed by an open immersion `e : U ⟶ P` and `π`:
`Rf_! ≅ Rh_* ⋙ De_! ⋙ Rπ_*`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriekOfCompactification`). This uses
only the exchange isomorphism `Rg'_* ⋙ Dj_! ≅ Dj'_! ⋙ Rg''_*` for a cartesian square with `j`
open and `g''` proper, applied to the graphs of `X` in fibre products.

On the bounded below derived categories, the same construction, carried out in the compact
support formalism `AlgebraicGeometry.Etale.derivedPlusFormalism`
(`WeilConjectures.SixFunctors.LowerShriek.Formalism`), gives a canonical composition isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso`, independent of all
compactification choices, equal to the identity when `f` or `g` is an identity, and associative.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso`: the canonical composition
  isomorphism `R(f)_!+ ⋙ R(g)_!+ ≅ R(f ≫ g)_!+` on bounded below derived categories.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`: the composition law
  `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on unbounded derived categories.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriekOfCompactification`:
  `Rf_!(c) ≅ Rh_* ⋙ De_! ⋙ Rπ_*` for every compactification `c` of `f`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso_hom_eq`: independence of the
  compactifications.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso_id_left`,
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso_id_right`: the unit laws.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso_assoc`: associativity.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section OpenImmersion

variable {V U X : Scheme.{u}}

/-- The composition isomorphism `D((j' ≫ j)_!) ≅ D(j'_!) ⋙ D(j_!)` of the extensions by zero
along open immersions `j' : V ⟶ U` and `j : U ⟶ X`, on unbounded derived categories, induced by
`AlgebraicGeometry.Etale.openImmersionLowerShriekComp`. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekComp (j' : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion j'] [IsOpenImmersion j] :
    D((j' ≫ j)_!open[A]) ≅ D((j')_!open[A]) ⋙ D((j)_!open[A]) :=
  Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekComp A j' j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The isomorphism `D(j_!) ≅ D(j'_!)` of derived extensions by zero induced by an equality
`j = j'` of open immersions. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekCongr {j j' : U ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : j = j') :
    D((j)_!open[A]) ≅ D((j')_!open[A]) := by
  subst h
  exact Iso.refl _

/-- The extension by zero along the identity is the identity: both are left adjoint to
`(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def openImmersionLowerShriekId (X : Scheme.{u}) : (𝟙 X)_!open[A] ≅ 𝟭 _ :=
  (openImmersionLowerShriekUpperStarAdjunction A (𝟙 X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (upperStarId A X).symm)

/-- The derived extension by zero along the identity is the identity. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekId (X : Scheme.{u}) :
    D((𝟙 X)_!open[A]) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekId A X) ≪≫
    Functor.mapDerivedCategoryIdIso _

end OpenImmersion

/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ Rg_*` for `g₁ ≫ g₂ = g`. -/
noncomputable def rightDerivedLowerStarCompOfEq {T S U : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ U)
    (g : T ⟶ U) (w : g₁ ≫ g₂ = g) : R((g₁)_*[A]) ⋙ R((g₂)_*[A]) ≅ R((g)_*[A]) := by
  subst w
  exact rightDerivedLowerStarComp A g₁ g₂


section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} {f : X ⟶ Y}
  {g : Y ⟶ S}

/-- The derived direct image along an identity is the identity. -/
noncomputable def rightDerivedLowerStarIdIso (Y : Scheme.{u}) :
    R((𝟙 Y)_*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  (Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- **Exchange of an extension by zero with a proper direct image**, for torsion coefficients:
for a cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions and `g''` proper,
`Rg'_* ⋙ Dj_! ≅ Dj'_! ⋙ Rg''_*`. -/
noncomputable def openImmersionLowerShriekLowerStarExchangeIso {U' U Z' Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z} [IsOpenImmersion j]
    [IsOpenImmersion j'] [IsProper g''] (hsq : IsPullback g' j' j g'') :
    R((g')_*[ModuleCat.{u + 1} Λ]) ⋙ D((j)_!open[ModuleCat.{u + 1} Λ]) ≅
      D((j')_!open[ModuleCat.{u + 1} Λ]) ⋙ R((g'')_*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite hsq
  asIso (openImmersionLowerShriekLowerStarExchange _ hsq)

/-- **Extension by zero of a proper direct image.** If a proper morphism `h : X ⟶ U` factors
as `h' ≫ u` through an open immersion `u : U' ⟶ U`, then `Rh'_* ⋙ Du_! ≅ Rh_*`, for torsion
coefficients. This is the exchange isomorphism for the cartesian square
`h' ≫ u = 𝟙 X ≫ h`. -/
noncomputable def rightDerivedLowerStarCompOpenImmersionLowerShriekIso {X U' U : Scheme.{u}}
    (h' : X ⟶ U') (u : U' ⟶ U) [IsOpenImmersion u] (h : X ⟶ U) [IsProper h]
    (w : h' ≫ u = h) :
    R((h')_*[ModuleCat.{u + 1} Λ]) ⋙ D((u)_!open[ModuleCat.{u + 1} Λ]) ≅
      R((h)_*[ModuleCat.{u + 1} Λ]) :=
  openImmersionLowerShriekLowerStarExchangeIso Λ
      (IsPullback.of_vert_isIso_mono (snd := 𝟙 X) ⟨by simp [w]⟩) ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryOpenImmersionLowerShriekId _ X) _ ≪≫
    Functor.leftUnitor _

/-- **`Rf_!` through a proper map with a locally closed factorisation.** Let `c` be a
compactification of `f : X ⟶ Y`, let `π : P ⟶ Y` be proper and let `f = h ≫ e ≫ π` with
`e : U ⟶ P` an open immersion and `h : X ⟶ U` proper. Then `Rf_!(c) ≅ Rh_* ⋙ De_! ⋙ Rπ_*`, for
torsion coefficients.

Both sides are compared with `X` embedded in `P ×_Y Z`, `Z` the compactification of `c`, by
the exchange isomorphism for the open immersions `P ×_Y X ⟶ P ×_Y Z` and
`U ×_Y Z ⟶ P ×_Y Z`, along the proper projections to `Z` and to `P`; on their intersection
the two embeddings of `X` agree. No quasi-compactness of `f` is needed. -/
theorem nonempty_iso_rightDerivedLowerShriekOfCompactification {X Y P U : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (π : P ⟶ Y) [IsProper π] (e : U ⟶ P)
    [IsOpenImmersion e] (h : X ⟶ U) [IsProper h] (fac : h ≫ e ≫ π = f) :
    Nonempty (Rf_!(c)[ModuleCat.{u + 1} Λ] ≅
      R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ D((e)_!open[ModuleCat.{u + 1} Λ]) ⋙
        R((π)_*[ModuleCat.{u + 1} Λ])) := by
  let 𝔸 := ModuleCat.{u + 1} Λ
  let p₁ := pullback.fst π c.g
  let p₂ := pullback.snd π c.g
  have : IsProper p₁ := MorphismProperty.pullback_fst _ _ c.isProper
  have : IsProper p₂ := MorphismProperty.pullback_snd _ _ ‹IsProper π›
  let ι : X ⟶ pullback π c.g := pullback.lift (h ≫ e) c.i (by
    rw [Category.assoc, fac]; exact c.comm)
  -- the graph of `X` in `P ×_Y X`, open in `P ×_Y Z`
  let a₁ := pullback.fst p₂ c.i
  let s₁ := pullback.snd p₂ c.i
  have : IsSeparated s₁ := MorphismProperty.pullback_snd _ _ inferInstance
  let Γ₁ : X ⟶ pullback p₂ c.i := pullback.lift ι (𝟙 X) (by simp [ι, p₂])
  have : IsProper (Γ₁ ≫ s₁) := by rw [show Γ₁ ≫ s₁ = 𝟙 X from pullback.lift_snd _ _ _]
                                  infer_instance
  have : IsProper Γ₁ := IsProper.of_comp Γ₁ s₁
  -- `X` in `U ×_Y Z`, open in `P ×_Y Z`
  let a₂ := pullback.fst p₁ e
  let s₂ := pullback.snd p₁ e
  have : IsSeparated s₂ := MorphismProperty.pullback_snd _ _ inferInstance
  let h₂ : X ⟶ pullback p₁ e := pullback.lift ι h (by simp [ι, p₁])
  have : IsProper (h₂ ≫ s₂) := by rw [show h₂ ≫ s₂ = h from pullback.lift_snd _ _ _]
                                  infer_instance
  have : IsProper h₂ := IsProper.of_comp h₂ s₂
  -- the intersection of the two opens
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  let γ : X ⟶ pullback a₁ a₂ := pullback.lift Γ₁ h₂ (by simp [Γ₁, h₂, a₁, a₂])
  let eΓ : R((γ)_*[𝔸]) ⋙ D((b₁)_!open[𝔸]) ≅ R((Γ₁)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ γ b₁ Γ₁ (pullback.lift_fst _ _ _)
  let eh : R((γ)_*[𝔸]) ⋙ D((b₂)_!open[𝔸]) ≅ R((h₂)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ γ b₂ h₂ (pullback.lift_snd _ _ _)
  -- the two extensions by zero agree
  let eC : R((Γ₁)_*[𝔸]) ⋙ D((a₁)_!open[𝔸]) ≅ R((h₂)_*[𝔸]) ⋙ D((a₂)_!open[𝔸]) :=
    Functor.isoWhiskerRight eΓ.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 b₁ a₁).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr 𝔸 pullback.condition ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 b₂ a₂) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eh _
  -- the side of `c`
  let eA : Rf_!(c)[𝔸] ≅ R((Γ₁)_*[𝔸]) ⋙ D((a₁)_!open[𝔸]) ⋙ R((p₁ ≫ π)_*[𝔸]) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight ((rightDerivedLowerStarIdIso Λ X).symm ≪≫
        (rightDerivedLowerStarCompOfEq 𝔸 Γ₁ s₁ (𝟙 X) (pullback.lift_snd _ _ _)).symm) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso Λ
          (IsPullback.of_hasPullback p₂ c.i).flip) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq 𝔸 p₂ c.g (p₁ ≫ π)
          pullback.condition.symm))
  -- the side of `π`
  let eB : R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((π)_*[𝔸]) ≅
      R((h₂)_*[𝔸]) ⋙ D((a₂)_!open[𝔸]) ⋙ R((p₁ ≫ π)_*[𝔸]) :=
    Functor.isoWhiskerRight (rightDerivedLowerStarCompOfEq 𝔸 h₂ s₂ h
        (pullback.lift_snd _ _ _)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso Λ
          (IsPullback.of_hasPullback p₁ e).flip) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq 𝔸 p₁ π (p₁ ≫ π) rfl))
  exact ⟨eA ≪≫ (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eC _ ≪≫
    Functor.associator _ _ _ ≪≫ eB.symm⟩

/-- **The composition isomorphism on compatible compactifications.** Let `d = (v, ḡ)` be a
compactification of `g : Y ⟶ S` and `e = (a, p)` a compactification of `f ≫ v`, and write
`V = e.Z ×_{d.Z} Y` with its open immersion `b : V ⟶ e.Z` and its proper projection
`p_Y : V ⟶ Y`. For torsion coefficients, the isomorphism

```
Rf_!(e.restrict) ⋙ Rg_!(d) = Dc_! ⋙ Rp_Y* ⋙ Dv_! ⋙ Rḡ_*
    ≅ Dc_! ⋙ Db_! ⋙ Rp_* ⋙ Rḡ_*  ≅  Da_! ⋙ R(p ≫ ḡ)_* = R(f ≫ g)_!(d.comp e)
```

built from the exchange isomorphism `v_! Rp_Y* ≅ Rp_* b_!` of the cartesian square
`AlgebraicGeometry.Compactification.isPullback_restrict` (an isomorphism by proper base
change), the composition of extensions by zero along `a = c ≫ b`, and the composition of
derived pushforwards. (blueprint: the construction in
`proposition-composition-base-change-rf-shriek--1`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationCompIso (d : Compactification g)
    (e : Compactification (f ≫ d.i)) :
    Rf_!(e.restrict)[ModuleCat.{u + 1} Λ] ⋙ Rf_!(d)[ModuleCat.{u + 1} Λ] ≅
      Rf_!(d.comp e)[ModuleCat.{u + 1} Λ] :=
  have := isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite e.isPullback_restrict
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D((e.restrict.i)_!open[ModuleCat.{u + 1} Λ])
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso (openImmersionLowerShriekLowerStarExchange _
          e.isPullback_restrict)) R((d.g)_*[ModuleCat.{u + 1} Λ]) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D((pullback.fst e.g d.i)_!open[ModuleCat.{u + 1} Λ])
          (rightDerivedLowerStarComp _ e.g d.g)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((mapDerivedCategoryOpenImmersionLowerShriekComp _ e.restrict.i
          (pullback.fst e.g d.i)).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr _ e.restrict_i_fst)
      R((e.g ≫ d.g)_*[ModuleCat.{u + 1} Λ])

/-- Blueprint `proposition-composition-base-change-rf-shriek--1` (detailed:
`proposition-composition-base-change-rf-shriek--1`): **the composition law for `Rf_!`**. For
composable `f : X ⟶ Y` and `g : Y ⟶ T` admitting compactifications and torsion coefficients, there
is an isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of functors between the unbounded derived categories of
étale sheaves, each side computed with the chosen compactifications. No quasi-compactness is needed.

With `X ⟶[k] V ⟶[r] T` and `Y ⟶[j] W ⟶[q] T` the compactifications of `f ≫ g` and `g`, the
scheme `P = V ×_T W` is proper over `T` and over `W`, and `X` sits in it as a closed subscheme
of the open `P ×_V X`. By `nonempty_iso_rightDerivedLowerShriekOfCompactification`,
`R(f ≫ g)_!` is computed in `P`. Over the open `Y ⊆ W` the same embedding computes `Rf_!` in
`P ×_W Y`, which is proper over `Y`, and the exchange isomorphism for the open immersion
`P ×_W Y ⟶ P` along the proper `P ⟶ W` moves `Dj_!` past the direct image. -/
theorem nonempty_iso_rightDerivedLowerShriek_comp {X Y T : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ T) [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ]) := by
  let 𝔸 := ModuleCat.{u + 1} Λ
  let cf := HasCompactification.compactification f
  let cg := HasCompactification.compactification g
  let cfg := HasCompactification.compactification (f ≫ g)
  -- `P = V ×_T W`
  let φ := pullback.fst cfg.g cg.g
  let ψ := pullback.snd cfg.g cg.g
  have : IsProper φ := MorphismProperty.pullback_fst _ _ cg.isProper
  have : IsProper ψ := MorphismProperty.pullback_snd _ _ cfg.isProper
  -- `X` in the open `P ×_V X` of `P`
  let e := pullback.fst φ cfg.i
  let σ := pullback.snd φ cfg.i
  have : IsSeparated σ := MorphismProperty.pullback_snd _ _ inferInstance
  have w₁ : cfg.i ≫ cfg.g = (f ≫ cg.i) ≫ cg.g := by
    rw [← cfg.comm, Category.assoc, ← cg.comm]
  let h : X ⟶ pullback φ cfg.i :=
    pullback.lift (pullback.lift cfg.i (f ≫ cg.i) w₁) (𝟙 X) (by simp [φ])
  have : IsProper (h ≫ σ) := by rw [show h ≫ σ = 𝟙 X from pullback.lift_snd _ _ _]
                                infer_instance
  have : IsProper h := IsProper.of_comp h σ
  have he : h ≫ e = pullback.lift cfg.i (f ≫ cg.i) w₁ := pullback.lift_fst _ _ _
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedLowerShriekOfCompactification Λ cfg (ψ ≫ cg.g) e h
    (by rw [reassoc_of% he, pullback.lift_snd_assoc, Category.assoc, ← cg.comm])
  -- `P ×_W Y`, open in `P` and proper over `Y`
  let eY := pullback.fst ψ cg.i
  let πY := pullback.snd ψ cg.i
  have : IsProper πY := MorphismProperty.pullback_snd _ _ inferInstance
  let uY := pullback.fst e eY
  let e' := pullback.snd e eY
  let ρ : X ⟶ pullback ψ cg.i := pullback.lift (h ≫ e) f (by rw [he]; simp [ψ])
  let h' : X ⟶ pullback e eY := pullback.lift h ρ (by simp [ρ, eY])
  have : IsProper (h' ≫ uY) := by rw [show h' ≫ uY = h from pullback.lift_fst _ _ _]
                                  infer_instance
  have : IsProper h' := IsProper.of_comp h' uY
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedLowerShriekOfCompactification Λ cf πY e' h'
    (by simp [h', e', ρ, πY])
  let eh : R((h')_*[𝔸]) ⋙ D((uY)_!open[𝔸]) ≅ R((h)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ h' uY h (pullback.lift_fst _ _ _)
  let ex : R((πY)_*[𝔸]) ⋙ D((cg.i)_!open[𝔸]) ≅ D((eY)_!open[𝔸]) ⋙ R((ψ)_*[𝔸]) :=
    openImmersionLowerShriekLowerStarExchangeIso Λ (IsPullback.of_hasPullback ψ cg.i).flip
  let e₃ : R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((ψ ≫ cg.g)_*[𝔸]) ≅
      (R((h')_*[𝔸]) ⋙ D((e')_!open[𝔸]) ⋙ R((πY)_*[𝔸])) ⋙ D((cg.i)_!open[𝔸]) ⋙
        R((cg.g)_*[𝔸]) :=
    Functor.isoWhiskerRight eh.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 uY e).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr 𝔸 pullback.condition ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 e' eY) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
            (rightDerivedLowerStarCompOfEq 𝔸 ψ cg.g _ rfl).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ex.symm _ ≪≫
          Functor.associator _ _ _)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
      Functor.associator _ _ _
  exact ⟨e₁ ≪≫ e₃ ≪≫ Functor.isoWhiskerRight e₂.symm _⟩

end Torsion


section Plus

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S T : Scheme.{u}}

/-- The isomorphism `R(f)_![Λ]+ ≅ R(f')_![Λ]+` for `f = f'`. -/
noncomputable abbrev rightDerivedLowerShriekPlusCongr {f f' : X ⟶ Y} [HasCompactification f]
    [HasCompactification f'] (h : f = f') :
    R(f)_![ModuleCat.{u + 1} Λ]+ ≅ R(f')_![ModuleCat.{u + 1} Λ]+ :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCongr h

/-- The identification `R(𝟙 X)_![Λ]+ ≅ 𝟭` of the bounded below compactly supported direct image
along the identity. -/
noncomputable abbrev rightDerivedLowerShriekPlusId (X : Scheme.{u}) [HasCompactification (𝟙 X)] :
    R(𝟙 X)_![ModuleCat.{u + 1} Λ]+ ≅ 𝟭 _ :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekId X

/-- Blueprint `proposition-composition-base-change-rf-shriek--1` (detailed:
`proposition-composition-base-change-rf-shriek--1`): **the canonical composition isomorphism**
`α_{g,f} : Rg_! Rf_! ≅ R(g ∘ f)_!` of functors `D⁺(X_ét, Λ) ⥤ D⁺(S_ét, Λ)` for torsion coefficients,
for composable `f`, `g` admitting compactifications with `f ≫ g` quasi-compact. It is the
composition isomorphism `CompactSupportFormalism.compIso` of the triangle of compactifications
`Compactification.Triangle.ofHasCompactification f g`: compactify `g` as `Y ⟶[v] Ȳ ⟶[ḡ] S` and
`f ≫ v` as `X ⟶[a] X̄ ⟶[p] Ȳ`; with `V = X̄ ×_Ȳ Y`, the exchange isomorphism
`v_! Rp_{Y*} ≅ Rp_* b_!` (proper base change) gives
`Rf_! ⋙ Rg_! = c_! Rp_{Y*} v_! Rḡ_* ≅ a_! R(p ≫ ḡ)_* = R(f ≫ g)_!`, compared with the chosen
compactifications of `f` and `f ≫ g`. Together with the coherent comparison isomorphisms
`CompactSupportFormalism.shriekIso` of `derivedPlusFormalism`, this is blueprint
`proposition-construction-independence-rf-shriek--7`. -/
noncomputable def rightDerivedLowerShriekPlusCompIso (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    R(f)_![ModuleCat.{u + 1} Λ]+ ⋙ R(g)_![ModuleCat.{u + 1} Λ]+ ≅
      R(f ≫ g)_![ModuleCat.{u + 1} Λ]+ :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso f g

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: **independence of all
compactification choices**. The composition isomorphism is computed by any triangle of
compactifications `T` of `(f, g)` (compactifications of `f`, `g`, `f ≫ g` linked by a cartesian
square): it is the composition isomorphism of `T`, conjugated by the comparison isomorphisms
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso` between the
compactifications of `T` and the chosen ones. -/
theorem rightDerivedLowerShriekPlusCompIso_hom_eq {f : X ⟶ Y} {g : Y ⟶ S}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] (T : Compactification.Triangle f g) :
    (rightDerivedLowerShriekPlusCompIso Λ f g).hom =
      NatTrans.hcomp
          (rightDerivedLowerShriekOfCompactificationPlusIso Λ
            (HasCompactification.compactification f) T.cf).hom
          (rightDerivedLowerShriekOfCompactificationPlusIso Λ
            (HasCompactification.compactification g) T.cg).hom ≫
        ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).compIso T).hom ≫
          (rightDerivedLowerShriekOfCompactificationPlusIso Λ T.cfg
            (HasCompactification.compactification (f ≫ g))).hom := by
  have h := (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso_hom_eq T
  simp only [derivedPlusFormalism_shriekIso] at h
  exact h

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: **the composition isomorphism is
the identity when `f` is an identity**. -/
theorem rightDerivedLowerShriekPlusCompIso_id_left (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (𝟙 X)] [HasCompactification (𝟙 X ≫ f)] [QuasiCompact f] :
    (rightDerivedLowerShriekPlusCompIso Λ (𝟙 X) f).hom =
      Functor.whiskerRight (rightDerivedLowerShriekPlusId Λ X).hom _ ≫
        (Functor.leftUnitor _).hom ≫
          (rightDerivedLowerShriekPlusCongr Λ (Category.id_comp f).symm).hom :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso_id_left f

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: **the composition isomorphism is
the identity when `g` is an identity**. -/
theorem rightDerivedLowerShriekPlusCompIso_id_right (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (𝟙 Y)] [HasCompactification (f ≫ 𝟙 Y)] [QuasiCompact f] :
    (rightDerivedLowerShriekPlusCompIso Λ f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (rightDerivedLowerShriekPlusId Λ Y).hom ≫
        (Functor.rightUnitor _).hom ≫
          (rightDerivedLowerShriekPlusCongr Λ (Category.comp_id f).symm).hom :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso_id_right f

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: **associativity of the composition
isomorphism**: for a third morphism `h : S ⟶ T`, the two composites
`Rh_! Rg_! Rf_! ≅ R(f ≫ g ≫ h)_!` agree. -/
theorem rightDerivedLowerShriekPlusCompIso_assoc (f : X ⟶ Y) (g : Y ⟶ S) (h : S ⟶ T)
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)] [QuasiCompact f]
    [QuasiCompact g] [QuasiCompact h] :
    Functor.whiskerRight (rightDerivedLowerShriekPlusCompIso Λ f g).hom
        R(h)_![ModuleCat.{u + 1} Λ]+ ≫ (rightDerivedLowerShriekPlusCompIso Λ (f ≫ g) h).hom ≫
        (rightDerivedLowerShriekPlusCongr Λ (Category.assoc f g h)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft R(f)_![ModuleCat.{u + 1} Λ]+
          (rightDerivedLowerShriekPlusCompIso Λ g h).hom ≫
          (rightDerivedLowerShriekPlusCompIso Λ f (g ≫ h)).hom :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso_assoc f g h

end Plus

end Etale

end AlgebraicGeometry
