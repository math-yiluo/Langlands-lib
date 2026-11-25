/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible

/-!
# The adjunctions of the six-functor datum

Blueprint `fix-prop-adjunctions` collects the adjunctions of the six-functor datum
`def-fix-six-functor-datum`, and blueprint
`proposition-composition-open-restriction-compactifications-f--1` the mate calculus for the
exceptional pair on the finite-Tor categories. The datum is the one of the six-operations package
`AlgebraicGeometry.Etale.SixOperationsPackage`: the coefficients are `ModuleCat Λ` for a finite ring
`Λ`, the schemes are of finite type over a field `k`, and the exponent of `Λ` is invertible on the
base.

1. The derived adjunction `Lf^* ⊣ Rf_*` restricts to the bounded constructible categories
   (`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.leftDerivedUpperStarAdjunction`).
2. The exceptional adjunction `Rf_! ⊣ Rf^!` restricts to the bounded constructible categories
   (`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.rightDerivedLowerShriekAdjunction`)
   and to the finite-Tor categories
   (`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`), and its
   unit and counit agree for the refinement comparisons
   (`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunctionOfCompactification_comparison`).
3. For composable `f` and `g`, the unit and counit of `D((g ∘ f)^*) ⊣ R(g ∘ f)_*` are the
   pasted ones through the composition isomorphisms
   (`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction_comp_eq`), and those of the
   exceptional pair are the pasted ones under the mate of the composition isomorphism of `Rf_!`
   (`AlgebraicGeometry.Etale.exists_rightDerivedUpperShriekAdjunction_comp_eq`, and on the
   finite-Tor categories `exists_rightDerivedLowerShriekAdjunction_comp_eq` in the namespace
   `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor`, which is blueprint
   `proposition-composition-open-restriction-compactifications-f--1`).
4. The transpose of the compact-support exchange `Ex_!` under the exceptional adjunctions and
   `Lg^* ⊣ Rg_*` is the exceptional-inverse-image identification `Rg'_* Rf'^! ≅ Rf^! Rg_*`
   (`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeMap`); that `Ex_*` is the
   transpose of the base-change composite is
   `AlgebraicGeometry.Etale.derivedUpperStar_map_derivedBaseChangeMap_app_counit`.

## Implementation notes

That `Rf^!` preserves `Dᵇc`, which clause (2) needs, is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedUpperShriek`. Blueprint
`rem-ptr-sf-datum-1`, that the datum of `def-sf-datum` satisfies axiom (A1), is
`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.nonempty_adjunctions_and_exists_comp_eq`.

Clause (3) for the derived pullback is stated for `D(g^*)`, the functor induced on derived
categories by the exact pullback `g^*`, which is the derived pullback
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`), and for the composition
isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerStarComp` of the derived direct images.

The triangle identities of every adjunction here are part of the structure
`CategoryTheory.Adjunction`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Composition

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Blueprint `fix-prop-adjunctions` (3), for the pair `(Lf^*, Rf_*)`: for composable
`g₁ : T ⟶ S` and `g₂ : S ⟶ U`, transporting the adjunction `D((g₁ ≫ g₂)^*) ⊣ R(g₁ ≫ g₂)_*` along
the composition isomorphisms `D((g₁ ≫ g₂)^*) ≅ D(g₂^*) ⋙ D(g₁^*)` and
`R(g₁ ≫ g₂)_* ≅ Rg₁_* ⋙ Rg₂_*` (`AlgebraicGeometry.Etale.rightDerivedLowerStarComp`) gives the
composite adjunction: the unit of the adjunction of `g₁ ≫ g₂` is the composite of the units and
its counit the composite of the counits. -/
theorem mapDerivedUpperStarLowerStarAdjunction_comp_eq {T S U : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ U) :
    ((mapDerivedUpperStarLowerStarAdjunction A (g₁ ≫ g₂)).ofNatIsoLeft
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A g₁ g₂) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm)).ofNatIsoRight
        (rightDerivedLowerStarComp A g₁ g₂).symm =
      (mapDerivedUpperStarLowerStarAdjunction A g₂).comp
        (mapDerivedUpperStarLowerStarAdjunction A g₁) :=
  Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ _

end Composition

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

section BoundedConstructible

variable {X Y : Scheme.{u}}

/-- Blueprint `fix-prop-adjunctions` (1): the restriction `Lf^* : Dᵇc(Y, Λ) ⥤ Dᵇc(X, Λ)` of the
derived pullback to the bounded constructible categories. -/
noncomputable def DerivedCategoryBoundedConstructible.leftDerivedUpperStar (f : X ⟶ Y) :
    DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) Y ⥤
      DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.lift _
    (DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) Y ⋙
      L((f)^*[ModuleCat.{u + 1} Λ]))
    fun K ↦ boundedConstructible_leftDerivedUpperStar _ f K.property

/-- Blueprint `fix-prop-adjunctions` (1): the restriction `Rf_* : Dᵇc(X, Λ) ⥤ Dᵇc(Y, Λ)` of the
derived direct image to the bounded constructible categories, for a morphism of finite-type
`k`-schemes and a finite `Λ` whose exponent is invertible on `Y` (finiteness theorem,
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_finite`). -/
noncomputable def DerivedCategoryBoundedConstructible.rightDerivedLowerStar
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasInvertibleExponent Λ Y] :
    DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) Y :=
  ObjectProperty.lift _
    (DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) X ⋙
      R((f)_*[ModuleCat.{u + 1} Λ]))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_of_finite Λ aX aY f hf K.property

/-- Blueprint `fix-prop-adjunctions` (1): the derived adjunction `Lf^* ⊣ Rf_*` restricts to an
adjunction between the bounded constructible categories `Dᵇc(Y, Λ)` and `Dᵇc(X, Λ)`, with unit
and counit those of the derived adjunction
`AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction`. -/
noncomputable def DerivedCategoryBoundedConstructible.leftDerivedUpperStarAdjunction
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasInvertibleExponent Λ Y] :
    DerivedCategoryBoundedConstructible.leftDerivedUpperStar Λ f ⊣
      DerivedCategoryBoundedConstructible.rightDerivedLowerStar Λ aX aY f hf :=
  (derivedUpperStarLowerStarAdjunction _ f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- Blueprint `fix-prop-adjunctions` (2): the restriction `Rf_! : Dᵇc(X, Λ) ⥤ Dᵇc(Y, Λ)` of the
compactly supported direct image to the bounded constructible categories, for a separated
finite-type `f` between finite-type `k`-schemes and a finite `Λ` whose exponent is invertible on
`Y` (finiteness theorem, `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`). -/
noncomputable def DerivedCategoryBoundedConstructible.rightDerivedLowerShriek
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    (hf : f ≫ aY = aX) [HasCompactification f] :
    DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) Y :=
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom f
  ObjectProperty.lift _
    (DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) X ⋙
      R(f)_![ModuleCat.{u + 1} Λ])
    fun K ↦ boundedConstructible_rightDerivedLowerShriek Λ f aX aY hf _ K.property

/-- Blueprint `fix-prop-adjunctions` (2): the restriction `Rf^! : Dᵇc(Y, Λ) ⥤ Dᵇc(X, Λ)` of the
exceptional inverse image to the bounded constructible categories
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedUpperShriek`). -/
noncomputable def DerivedCategoryBoundedConstructible.rightDerivedUpperShriek
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) Y ⥤
      DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.lift _
    (DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) Y ⋙
      R(f)^![Λ])
    fun K ↦ boundedConstructible_rightDerivedUpperShriek Λ aY f K.property

/-- Blueprint `fix-prop-adjunctions` (2): the exceptional adjunction `Rf_! ⊣ Rf^!` restricts to an
adjunction between the bounded constructible categories `Dᵇc(X, Λ)` and `Dᵇc(Y, Λ)`, for a
separated finite-type `f` between finite-type `k`-schemes and a finite `Λ` whose exponent is
invertible on `Y`; its unit and counit (and hence its triangle identities) are those of
`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction`. Its further restriction to the
finite-Tor categories is
`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`. -/
noncomputable def DerivedCategoryBoundedConstructible.rightDerivedLowerShriekAdjunction
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    (hf : f ≫ aY = aX) [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryBoundedConstructible.rightDerivedLowerShriek Λ aX aY f hf ⊣
      DerivedCategoryBoundedConstructible.rightDerivedUpperShriek Λ aY f :=
  (rightDerivedUpperShriekAdjunction _ f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

end BoundedConstructible

section Refinement

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f] [QuasiCompact f]

/-- Blueprint `fix-prop-adjunctions` (2): the exceptional adjunction `Rf_!(c) ⊣ Rf^!` for the
compactly supported direct image `Rf_!(c)` computed with an arbitrary compactification `c` of `f`,
transported from `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` along the
compactification-independence isomorphism `Rf_!(c) ≅ Rf_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`). -/
noncomputable def rightDerivedUpperShriekAdjunctionOfCompactification (c : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ⊣ R(f)^![Λ] :=
  (rightDerivedUpperShriekAdjunction _ f).ofNatIsoLeft (rightDerivedLowerShriekIso Λ c).symm

/-- Blueprint `fix-prop-adjunctions` (2): the units and counits of the exceptional adjunctions
agree for the refinement comparisons. For a refinement `r : c.Refinement d` of compactifications
of `f` whose square over `X` is cartesian, transporting the adjunction `Rf_!(d) ⊣ Rf^!` along the
refinement comparison `Rf_!(d) ≅ Rf_!(c)`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`) and along its
conjugate automorphism of `Rf^!` gives the adjunction `Rf_!(c) ⊣ Rf^!`. -/
theorem rightDerivedUpperShriekAdjunctionOfCompactification_comparison {c d : Compactification f}
    (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    ((rightDerivedUpperShriekAdjunctionOfCompactification Λ d).ofNatIsoLeft
        (asIso (rightDerivedLowerShriekOfCompactificationComparison _ r hcart))).ofNatIsoRight
        (conjugateIsoEquiv (rightDerivedUpperShriekAdjunctionOfCompactification Λ c)
          (rightDerivedUpperShriekAdjunctionOfCompactification Λ d)
          (asIso (rightDerivedLowerShriekOfCompactificationComparison _ r hcart))).symm =
      rightDerivedUpperShriekAdjunctionOfCompactification Λ c :=
  Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ _

end Refinement

section FiniteTor

variable {X Y Z : Scheme.{u}}

/-- Blueprint `fix-prop-adjunctions` (2): the exceptional adjunction `Rf_! ⊣ Rf^!` restricts to an
adjunction between the finite-Tor categories `Dctf(X, Λ)` and `Dctf(Y, Λ)`, for a separated
finite-type `f` over a finite-type `k`-scheme `Y` and a finite `Λ` whose exponent is invertible on
`Y`; its unit and counit are those of
`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction`. This is the adjunction of axiom
(A1) of `def-sf-datum`, which blueprint `rem-ptr-sf-datum-1` points to. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
      DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f :=
  (rightDerivedUpperShriekAdjunction _ f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`: Mate calculus for a
pasted adjunction.

In the setting of the six-functor datum, let `X ⟶[f] Y ⟶[g] Z` be separated finite-type
morphisms over a finite-type `k`-scheme `Z`, with the adjunctions `Rf_! ⊣ Rf^!`, `Rg_! ⊣ Rg^!`
and `R(g ∘ f)_! ⊣ R(g ∘ f)^!` on the finite-Tor categories of axiom (A1)
(`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`). There is
a composition isomorphism `e : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of functors between the finite-Tor
categories (`proposition-composition-base-change-rf-shriek--1`) whose mate
`Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!` carries the adjunction of `f ≫ g` to the composite adjunction: the unit
and counit of the composite adjunction are the pasted ones. -/
theorem DerivedCategoryFiniteTor.exists_rightDerivedLowerShriekAdjunction_comp_eq
    (aY : Y ⟶ Spec (.of k)) (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [HasInvertibleExponent Λ Y]
    [HasInvertibleExponent Λ Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) [HasCompactification f] [QuasiCompact f] [HasCompactification g] [QuasiCompact g]
    [HasCompactification (f ≫ g)] :
    ∃ e : DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aZ (f ≫ g) ≅
        DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⋙
          DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aZ g,
      ((DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ (f ≫ g)).ofNatIsoLeft
          e).ofNatIsoRight
        (conjugateIsoEquiv
          ((DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f).comp
            (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ g))
          (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ (f ≫ g)) e).symm =
        (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f).comp
          (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ g) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  exact ⟨((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (DerivedCategoryFiniteTor.ι _ X) e),
    Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ _⟩

/-- Blueprint `fix-prop-adjunctions` (1), on the finite-Tor categories: the derived adjunction
`Lf^* ⊣ Rf_*` restricts to an adjunction between `Dctf(Y, Λ)` and `Dctf(X, Λ)`, for a separated
morphism of finite-type `k`-schemes and a finite `Λ` whose exponent is invertible on `Y`. -/
noncomputable def DerivedCategoryFiniteTor.leftDerivedUpperStarAdjunction
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f]
    [HasInvertibleExponent Λ Y] :
    DerivedCategoryFiniteTor.leftDerivedUpperStar _ f ⊣
      DerivedCategoryFiniteTor.rightDerivedLowerStar Λ aX aY f hf :=
  (derivedUpperStarLowerStarAdjunction _ f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- Blueprint `rem-ptr-sf-datum-1`: in the notation of `def-sf-datum`, the properties of
`def-fix-six-functor-datum` and `fix-prop-adjunctions` hold, i.e. axiom (A1): for separated
finite-type `X ⟶[f] Y ⟶[g] Z` of finite-type `k`-schemes and a finite `Λ` whose exponent is
invertible on `Z`, there are adjunctions `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!` on the finite-Tor
categories, and the units and counits of the exceptional adjunction for `f ≫ g` are the pasted
ones under the mate of a composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`. -/
theorem DerivedCategoryFiniteTor.nonempty_adjunctions_and_exists_comp_eq
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) (aZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [HasInvertibleExponent Λ Y]
    [HasInvertibleExponent Λ Z] (f : X ⟶ Y) (hf : f ≫ aY = aX) (g : Y ⟶ Z) [IsSeparated f]
    [HasCompactification f] [QuasiCompact f] [HasCompactification g] [QuasiCompact g]
    [HasCompactification (f ≫ g)] :
    Nonempty (DerivedCategoryFiniteTor.leftDerivedUpperStar _ f ⊣
        DerivedCategoryFiniteTor.rightDerivedLowerStar Λ aX aY f hf) ∧
      Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
        DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f) ∧
      ∃ e : DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aZ (f ≫ g) ≅
          DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⋙
            DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aZ g,
        ((DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ (f ≫ g)).ofNatIsoLeft
            e).ofNatIsoRight
          (conjugateIsoEquiv
            ((DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f).comp
              (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ g))
            (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ (f ≫ g)) e).symm =
          (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f).comp
            (DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aZ g) :=
  ⟨⟨DerivedCategoryFiniteTor.leftDerivedUpperStarAdjunction Λ aX aY f hf⟩,
    ⟨DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f⟩,
    DerivedCategoryFiniteTor.exists_rightDerivedLowerShriekAdjunction_comp_eq Λ aY aZ f g⟩

end FiniteTor

section Exchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Blueprint `fix-prop-adjunctions` (4), and blueprint `definition-trace-morphism--1` (Dual base
change): the transpose of the compact-support exchange
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of a cartesian square
```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```
under the composite adjunctions `Lg^* ∘ Rf_! ⊣ Rf^! ∘ Rg_*` and `Rf'_! ∘ Lg'^* ⊣ Rg'_* ∘ Rf'^!`:
the exceptional-inverse-image exchange `Rg'_* Rf'^! ⟶ Rf^! Rg_*`, the conjugate of `Ex_!`. It is
an isomorphism (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekLowerStarBaseChangeMap`). -/
noncomputable def rightDerivedUpperShriekLowerStarBaseChangeMap [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    R(f')^![Λ] ⋙ R((g')_*[ModuleCat.{u + 1} Λ]) ⟶
      R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ R(f)^![Λ] :=
  conjugateEquiv
    ((derivedUpperStarLowerStarAdjunction _ g').comp (rightDerivedUpperShriekAdjunction _ f'))
    ((rightDerivedUpperShriekAdjunction _ f).comp (derivedUpperStarLowerStarAdjunction _ g))
    (rightDerivedLowerShriekBaseChangeMap Λ sq)

/-- Blueprint `fix-prop-adjunctions` (4), and blueprint `definition-trace-morphism--1` (Dual base
change; its isomorphism form is
`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeIso`): the
exceptional-inverse-image exchange
`Rg'_* Rf'^! ⟶ Rf^! Rg_*` is an isomorphism, being the conjugate of the compact-support exchange
`Ex_!`, which is an isomorphism by compact-support base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
theorem isIso_rightDerivedUpperShriekLowerStarBaseChangeMap [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  unfold rightDerivedUpperShriekLowerStarBaseChangeMap
  infer_instance

end Exchange

end Torsion

end Etale

end AlgebraicGeometry
