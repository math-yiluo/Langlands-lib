/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow

/-!

# Derived Upper Shriek

Let `Λ` be a finite ring. For a morphism `f : X ⟶ Y` of schemes admitting a compactification,
the exceptional inverse image `Rf^!` on étale sheaves of `Λ`-modules is *constructed* here out of
the two halves of the derived lower shriek `Rf_! = Di_! ⋙ Rg_*` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`:

`Rf^! := Rg^! ⋙ Di^*`,

where `Rg^!` is a chosen right adjoint of the derived pushforward `Rg_*` along the *proper*
morphism `g`, and `Di^*` is the levelwise pullback along the open immersion `i`, which is right
adjoint to `Di_!` by `Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. The
adjunction `Rf_! ⊣ Rf^!` is then the composite of these two adjunctions.

On the unbounded derived categories, the only input is that `Rg_*` is a left adjoint for every
proper `g`, with no condition on the schemes. This is the instance
`isLeftAdjoint_rightDerivedLowerStar_of_isProper`. For `f` separated of finite type between
quasi-compact quasi-separated schemes, `Rf^!` sends `D⁺` into `D⁺` [Stacks, Tag 0GLA], so it
restricts to a right adjoint of the bounded below `Rf_! : D⁺(X_ét, Λ) ⥤ D⁺(Y_ét, Λ)`.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isProper` : for `g` proper,
  `Rg_* : D(Z_ét, Λ) ⥤ D(Y_ét, Λ)` is a left adjoint.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactification` : `Rf^!` with respect to
  a compactification `c`, with scoped notation `Rf^!(c)[Λ]`, and
  `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction` : the
  adjunction `Rf_!(c)[ModuleCat Λ] ⊣ Rf^!(c)[Λ]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét, Λ) ⥤ D(X_ét, Λ)` for the
  chosen compactification, with scoped notation `R(f)^![Λ]`, and
  `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`.
  In particular `Rf_!` is a left adjoint (`isLeftAdjoint_rightDerivedLowerShriek`).

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekPlus` : `Rf^! : D⁺(Y_ét, Λ) ⥤ D⁺(X_ét, Λ)`
  for `f` separated and locally of finite type between quasi-compact quasi-separated schemes,
  with scoped notation `R(f)^![Λ]+`, and
  `AlgebraicGeometry.Etale.rightDerivedUpperShriekPlusAdjunction` : the adjunction
  `Rf_! ⊣ Rf^!` on the bounded below derived categories.

## Implementation notes

* `isLeftAdjoint_rightDerivedLowerStar_of_isProper` is proved by Brown representability, `Rg_*`
  preserving coproducts for torsion coefficients
  (`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`), and
  `isPlus_rightDerivedUpperShriek_obj` from the finite cohomological amplitude of `Rf_!`
  (`AlgebraicGeometry.Etale.plus_obj_of_rightDerivedLowerShriek_adjunction`). They are
  stated for finite coefficients only. In the pro-étale setting the first one fails even for field
  coefficients: for an abelian variety `E` of positive dimension over an algebraically closed
  field, `Ra_*` does not preserve countable coproducts on `D(E_proét, Λ)`.
* `Rg^!` for proper `g` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint
  extracted from the instance, not a construction. Only the adjunction
  `Adjunction.ofIsLeftAdjoint` should be used about it. The composite `Rf^!` is a construction
  out of it and `Di^*`.
* The derived adjunction `Di_! ⊣ Di^*` goes through the total left derived functor of `i_!`,
  which uses the closed symmetric monoidal structure and the functorial flat resolutions of
  `ModuleCat Λ` (`ModuleCat.hasFunctorialFlatResolution`), see
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.

## TODO

* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Let `Λ` be a finite ring and `g : Z ⟶ Y` a proper morphism of schemes. Then the derived
pushforward `Rg_* : D(Z_ét, Λ) ⥤ D(Y_ét, Λ)` on the unbounded derived categories is a left
adjoint. Its right adjoint is the exceptional inverse image `Rg^!` along `g`.

The ring `Λ` is killed by some `n ≥ 1`, and for a proper morphism of schemes `Rg_*` on
unbounded complexes of `Λ`-modules commutes with direct sums [Stacks, Tag 0F0D]
(`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`). An exact
functor out of the derived category of a Grothendieck abelian category that commutes with direct
sums has a right adjoint [Stacks, Tag 0F5Y]. No condition on `Z` or `Y` is needed. -/
instance isLeftAdjoint_rightDerivedLowerStar_of_isProper [Finite Λ] {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) [IsProper g] :
    ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.IsLeftAdjoint := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g
  let : (R((g)_*[ModuleCat.{u + 1} Λ])).CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : (R((g)_*[ModuleCat.{u + 1} Λ])).IsTriangulated := adj.isTriangulated_rightAdjoint
  have (J : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete J) (R((g)_*[ModuleCat.{u + 1} Λ])) :=
    preservesColimitsOfShape_rightDerivedLowerStar_of_isProper Λ hΛ g J
  exact DerivedCategory.isLeftAdjoint_of_preservesCoproducts (R((g)_*[ModuleCat.{u + 1} Λ]))

variable [Finite Λ]

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The exceptional inverse image `Rf^! : D(Y_ét, Λ) ⥤ D(X_ét, Λ)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of étale sheaves of
`Λ`-modules. It is a chosen right adjoint `Rg^!` of the derived pushforward `Rg_*` along the
proper `g`, followed by the levelwise pullback `Di^*` along the open immersion `i`. -/
noncomputable def rightDerivedUpperShriekOfCompactification :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ((c.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.rightAdjoint ⋙
    D((c.i)^*[ModuleCat.{u + 1} Λ])

@[inherit_doc rightDerivedUpperShriekOfCompactification]
scoped notation "Rf^!("c")[" Λ "]" =>
  rightDerivedUpperShriekOfCompactification Λ c

end OfCompactification

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section Unbounded

/-- The exceptional inverse image `Rf^! : D(Y_ét, Λ) ⥤ D(X_ét, Λ)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves of
`Λ`-modules. It is the functor `rightDerivedUpperShriekOfCompactification` attached to the
chosen compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Rf^!(HasCompactification.compactification f)[Λ]

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" Λ "]" =>
  rightDerivedUpperShriek Λ f

lemma rightDerivedUpperShriek_eq : R(f)^![Λ] =
    Rf^!(HasCompactification.compactification f)[Λ] := rfl

end Unbounded

section Adjunction

/-- The adjunction `Rf_! ⊣ Rf^!` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
the composite of the derived adjunction `Di_! ⊣ Di^*` along the open immersion `i` and of the
adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def rightDerivedUpperShriekOfCompactificationAdjunction {f : X ⟶ Y}
    (c : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ⊣ Rf^!(c)[Λ] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves of
`Λ`-modules [Stacks, Tag 0G2C]. -/
noncomputable def rightDerivedUpperShriekAdjunction :
    R(f)_![ModuleCat.{u + 1} Λ] ⊣ R(f)^![Λ] :=
  rightDerivedUpperShriekOfCompactificationAdjunction Λ (HasCompactification.compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` is a left adjoint, its right
adjoint being `R(f)^![Λ]`. -/
instance isLeftAdjoint_rightDerivedLowerShriek :
    (R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint :=
  (rightDerivedUpperShriekAdjunction Λ f).isLeftAdjoint

instance : (R(f)^![Λ]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction Λ f).isRightAdjoint

variable (Λ' : Type*) [Ring Λ'] [Linear Λ' (ModuleCat.{u + 1} Λ)] in
/-- If the coefficients are `Λ'`-linear, the exceptional inverse image `Rf^!` is `Λ'`-linear,
being right adjoint to the `Λ'`-linear functor `Rf_!`. -/
instance linear_rightDerivedUpperShriek : (R(f)^![Λ]).Linear Λ' :=
  (rightDerivedUpperShriekAdjunction Λ f).right_adjoint_linear

end Adjunction

section Plus

/-- For a quasi-compact target `Y`, the exceptional inverse image `Rf^!` sends bounded below
objects to bounded below objects. `Rf_!` has finite cohomological amplitude, bounded by twice the
fibre dimension of the compactification, which is bounded as `Y` is quasi-compact: if `Rf_!`
sends `D^{≤ 0}` into `D^{≤ N}` then `Rf^!` sends `D^{≥ 0}` into `D^{≥ -N}`, by adjunction
[SGA 4, Exp. XVIII, 3.1.7]. -/
theorem plus_rightDerivedUpperShriek_obj [CompactSpace Y]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((R(f)^![Λ]).obj K) :=
  plus_obj_of_rightDerivedLowerShriek_adjunction Λ f (rightDerivedUpperShriekAdjunction Λ f) K hK

/-- Let `Λ` be a finite ring and `f : X ⟶ Y` a separated morphism, locally of finite type, of
quasi-compact quasi-separated schemes. Then `Rf^! : D(Y_ét, Λ) ⥤ D(X_ét, Λ)` sends bounded below
complexes to bounded below complexes.

This is [Stacks, Lemma 63.11.4, Tag 0GLA], for the torsion ring `Λ`: there is `N ≥ 0` such that
`Hⁱ(K) = 0` for `i < a` implies `Hⁱ(Rf^! K) = 0` for `i < a - N`. Since `X` is quasi-compact and
`Y` quasi-separated, `f` is quasi-compact, hence of finite type. `R(f)^![Λ]` is the right adjoint
of `Rf_!`, which does not depend on the compactification, so it agrees with the `Rf^!` of
[Stacks, Lemma 63.11.1, Tag 0G2C]. -/
theorem isPlus_rightDerivedUpperShriek_obj [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.TStructure.t :
      Triangulated.TStructure (DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)))).plus ((R(f)^![Λ]).obj (DerivedCategory.Plus.ι.obj K)) :=
  plus_obj_of_rightDerivedLowerShriek_adjunction Λ f (rightDerivedUpperShriekAdjunction Λ f) _
    K.property

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [IsSeparated f] [LocallyOfFiniteType f]

/-- The exceptional inverse image `Rf^! : D⁺(Y_ét, Λ) ⥤ D⁺(X_ét, Λ)` on the bounded below derived
categories, for a separated morphism `f : X ⟶ Y`, locally of finite type, of quasi-compact
quasi-separated schemes: the restriction of `R(f)^![Λ]`, by `isPlus_rightDerivedUpperShriek_obj`
[Stacks, Tag 0GLA]. -/
noncomputable def rightDerivedUpperShriekPlus :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ObjectProperty.lift _ (DerivedCategory.Plus.ι ⋙ R(f)^![Λ])
    (isPlus_rightDerivedUpperShriek_obj Λ f)

@[inherit_doc rightDerivedUpperShriekPlus]
scoped notation "R(" f ")^![" Λ "]+" =>
  rightDerivedUpperShriekPlus Λ f

/-- The bounded below `Rf^!` is the restriction of the unbounded one along the inclusions of the
bounded below derived categories. -/
noncomputable def rightDerivedUpperShriekPlusCompatibility :
    R(f)^![Λ]+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)^![Λ] :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `Rf_! ⊣ Rf^!` on the bounded below derived categories of étale sheaves of
`Λ`-modules, for a separated morphism `f`, locally of finite type, of quasi-compact
quasi-separated schemes: the restriction of `rightDerivedUpperShriekAdjunction`. -/
noncomputable def rightDerivedUpperShriekPlusAdjunction :
    R(f)_![ModuleCat.{u + 1} Λ]+ ⊣ R(f)^![Λ]+ :=
  (rightDerivedUpperShriekAdjunction Λ f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (rightDerivedLowerShriekPlusCompatibility _ f).symm
    (rightDerivedUpperShriekPlusCompatibility Λ f).symm

end Plus

end Etale

end AlgebraicGeometry
