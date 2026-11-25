/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!

# Exactness of the direct image along a finite morphism

For a finite morphism `f : X ⟶ Y`, the pushforward `f_*` on étale sheaves is exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`): it is left exact
for any morphism, and it preserves epimorphisms because on the stalk at a geometric point `y`
with algebraically closed residue field it is the finite product of the stalk maps at the
geometric points over `y` (`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`), and these
stalks jointly detect epimorphisms
(`CategoryTheory.JointlyReflectIsomorphisms.epi_of_epi_map` applied to the conservative
family `AlgebraicGeometry.Scheme.uliftPointSmallEtale` of geometric points).

Consequently the total right derived functor of `f_*` is `f_*` applied levelwise
(`AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`).

Two restrictions are forced by the stalk formula and are not artefacts of the proof: `f` is
finite rather than integral, since the geometric fibre has to be finite; and the geometric
points used are those with *algebraically* closed residue field, since
`AlgebraicGeometry.Scheme.Hom.GeometricFiber` is the set of `Ω`-points of the fibre, which
for a merely separably closed `Ω` need not exhaust the topological fibre. The latter costs
nothing because these points already form a conservative family, which is how
`AlgebraicGeometry.Scheme.uliftPointSmallEtale` is defined.

Besides the standing assumptions on the coefficient category `A`, the results need `A` to be
concrete over `Type (u + 1)` in a way compatible with filtered colimits and sheafification,
since that is what the conservativity of the geometric points asks for. This holds for
`A = ModuleCat.{u + 1} Λ`.

## Main results

- `AlgebraicGeometry.Etale.epi_sheafFiber_lowerStar_map_of_isFinite`: `f_*` of an
  epimorphism is an epimorphism on the stalk at a geometric point with algebraically closed
  residue field.
- `AlgebraicGeometry.Etale.preservesEpimorphisms_lowerStar_of_isFinite`: the direct image
  along a finite morphism preserves epimorphisms.
- `AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`: the direct image
  along a finite morphism is exact.
- `AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`: its total
  right derived functor is itself, applied levelwise to complexes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

open Scheme Etale Scheme.Hom

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

omit [HasSmallSiteSheafify A] in
/-- **The direct image along a finite morphism is an epimorphism on stalks at geometric
points with algebraically closed residue field.** By the stalk formula the square
```
     ((f)_*[A] G)_y ------------(f_* φ)_y-----------> ((f)_*[A] G')_y
            |                                                |
   lowerStarSheafFiberIsoPi ≅                     lowerStarSheafFiberIsoPi ≅
            ↓                                                ↓
      ∏ᶜ (fun t ↦ G_t) --------∏ᶜ (fun t ↦ φ_t)-------> ∏ᶜ (fun t ↦ G'_t)
```
commutes, the products being over the finite geometric fibre of `f` over `y`; the bottom map
is an epimorphism because a finite product of epimorphisms is one. -/
lemma Etale.epi_sheafFiber_lowerStar_map_of_isFinite {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G') [Epi φ] :
    Epi ((pointSmallEtale y).sheafFiber.map ((f)_*[A].map φ)) := by
  rw [← Functor.comp_map, ← NatIso.naturality_2 (Etale.lowerStarSheafFiberIsoPi A f y) φ]
  have : Epi ((∏ᶜ fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber).map φ) :=
    epi_piObj_map (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber) φ
  infer_instance

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- **The direct image along a finite morphism preserves epimorphisms.** The geometric
points `AlgebraicGeometry.Scheme.algClosurePoint s` of `Y` jointly reflect epimorphisms, and
`f_* φ` is an epimorphism on the stalk at each of them by
`AlgebraicGeometry.Etale.epi_sheafFiber_lowerStar_map_of_isFinite`. -/
instance Etale.preservesEpimorphisms_lowerStar_of_isFinite :
    (f)_*[A].PreservesEpimorphisms where
  preserves {G G'} φ _ := by
    refine (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale Y A).epi_of_epi_map _ ?_
    rintro ⟨-, ⟨s⟩⟩
    have : Epi (((pointSmallEtale (Y.algClosurePoint s)).ulift.{u + 1}).sheafFiber.map
        ((f)_*[A].map φ)) := by
      rw [← NatIso.naturality_2 ((pointSmallEtale (Y.algClosurePoint s)).uliftSheafFiberIso A)
        ((f)_*[A].map φ)]
      have := Etale.epi_sheafFiber_lowerStar_map_of_isFinite A f (Y.algClosurePoint s) φ
      exact epi_comp _ _
    exact this

include hJ in
/-- The direct image along a finite morphism preserves homology. -/
instance Etale.preservesHomology_lowerStar_of_isFinite : (f)_*[A].PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

include hJ in
/-- **The direct image along a finite morphism is exact** (blueprint
`lemma-finite-direct-images--2`): it preserves finite colimits, and it preserves
finite limits by `AlgebraicGeometry.Etale.preservesFiniteLimits_lowerStar`. -/
instance Etale.preservesFiniteColimits_lowerStar_of_isFinite :
    PreservesFiniteColimits (f)_*[A] :=
  Functor.preservesFiniteColimits_of_preservesHomology _

section Derived

variable [HasDerivedCategory (Sheaf X.smallEtaleTopology A)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology A)]
  [Abelian.HasKInjectiveResolutions (Sheaf X.smallEtaleTopology A)]

include hJ in
/-- **The right derived functor of a finite direct image is the direct image itself**: since
`f_*` is exact, its total right derived functor is `f_*` applied levelwise to complexes.

This is definitionally `CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory` for
`f_*`; the content is that the exactness instance
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite` discharges its
hypothesis, so that the general isomorphism is available for a finite `f`
(blueprint `lemma-finite-direct-images--2`). -/
def Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory :
    (f)_*[A].rightDerivedFunctor ≅ (f)_*[A].mapDerivedCategory :=
  (f)_*[A].rightDerivedFunctorIsoMapDerivedCategory

end Derived

end AlgebraicGeometry

end
