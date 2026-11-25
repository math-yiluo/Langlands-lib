/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!
# The transverse boundary configuration

This file sets up the situation of the transverse boundary calculation of the trace formula
(blueprint `lemma-cohomology-near-two-transverse-divisors`, used by
`lemma-restriction-punctured-curve` on the curve route `remark-outline-local-computation`).

Let `Z` be a regular smooth surface over an algebraically closed field `k`, or an étale limit
with affine transition maps of such surfaces, and let `X, Y ⊆ Z` be regular divisors meeting
transversely at exactly one point `z`. Put `j : Z - Y ⟶ Z` and `i : Z - (X ∪ Y) ⟶ Z - Y`. For
a prime `ℓ` invertible in `k`, a finite commutative `ℓ`-primary ring `Λ` and a bounded complex
`E` of `Λ`-modules on `Z - (X ∪ Y)` with finite locally constant cohomology whose monodromy
factors through a finite `ℓ`-group, the transverse boundary calculation studies
`M = Rj_* i_! E`.

## Main definitions

- `AlgebraicGeometry.Scheme.IsEtaleLimitOfSmoothSurfaces`: `Z` is a cofiltered limit, with affine
  étale transition maps, of smooth surfaces over `k`.
- `AlgebraicGeometry.Scheme.TransverseCorner`: two regular divisors `X, Y` of such a `Z` meeting
  transversely at exactly one point, with the open immersions `j` and `i`.
- `AlgebraicGeometry.Etale.HasFiniteEllGroupMonodromy`: a sheaf of `Λ`-modules is trivialized by
  a finite étale Galois cover whose group is an `ℓ`-group, with finite constant value.
- `AlgebraicGeometry.Etale.IsBoundedFiniteEllGroupMonodromy`: a bounded complex whose cohomology
  sheaves have finite `ℓ`-group monodromy.
- `AlgebraicGeometry.Scheme.TransverseCorner.boundaryComplex`: the complex `M = Rj_* i_! E`.
- `AlgebraicGeometry.Scheme.TransverseCorner.puncturedY`: the punctured divisor `Y - z`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k]

/-- `aZ : Z ⟶ Spec k` is an *étale limit with affine transition maps of smooth surfaces*: `Z` is
the limit of a cofiltered diagram of `k`-schemes `Z_i`, smooth of relative dimension `2` over
`k`, whose transition maps are affine and étale. A smooth surface over `k` is such a limit, over
the trivial diagram (blueprint `lemma-cohomology-near-two-transverse-divisors`,
`lemma-vanishing-restrictions-after-blowing-up--1`). -/
def IsEtaleLimitOfSmoothSurfaces {Z : Scheme.{u}} (aZ : Z ⟶ Spec (.of k)) : Prop :=
  ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
    (a : ∀ i, D.obj i ⟶ Spec (.of k)) (c : Cone D) (_ : IsLimit c) (e : c.pt ≅ Z),
    (∀ {i i' : I} (f : i ⟶ i'), D.map f ≫ a i' = a i) ∧
    (∀ i, c.π.app i ≫ a i = e.hom ≫ aZ) ∧
    (∀ i, SmoothOfRelativeDimension 2 (a i)) ∧
    (∀ {i i' : I} (f : i ⟶ i'), Etale (D.map f) ∧ IsAffineHom (D.map f))

variable (k) in
/-- **The transverse corner** (blueprint `lemma-cohomology-near-two-transverse-divisors`): a scheme
`Z` over `k` which is a smooth surface, or an étale limit with affine transition maps of smooth
surfaces, with two regular divisors `X` and `Y` meeting transversely at exactly one point `z`,
together with the open immersions `j : U = Z - Y ⟶ Z` and `i : V = Z - (X ∪ Y) ⟶ U`.

The surface is regular, in particular locally noetherian. The divisors are regular closed
immersions of codimension one with regular source; they meet
transversely at `z` when their scheme-theoretic intersection `X ×_Z Y` is a regular closed
subscheme of codimension two of `Z`, that is, when local equations of `X` and `Y` form a regular
system of parameters at `z`. -/
structure TransverseCorner where
  /-- The surface. -/
  Z : Scheme.{u}
  /-- The structure morphism of the surface. -/
  aZ : Z ⟶ Spec (.of k)
  isEtaleLimitOfSmoothSurfaces : IsEtaleLimitOfSmoothSurfaces aZ
  [isLocallyNoetherian : IsLocallyNoetherian Z]
  [isRegular_Z : IsRegular Z]
  /-- The first divisor. -/
  X : Scheme.{u}
  /-- The second divisor, along which the direct image is taken. -/
  Y : Scheme.{u}
  /-- The closed immersion of the first divisor. -/
  iX : X ⟶ Z
  /-- The closed immersion of the second divisor. -/
  iY : Y ⟶ Z
  [isRegularImmersion_iX : IsRegularImmersion 1 iX]
  [isRegularImmersion_iY : IsRegularImmersion 1 iY]
  [isRegular_X : IsRegular X]
  [isRegular_Y : IsRegular Y]
  /-- The two divisors meet transversely. -/
  isRegularImmersion_inter : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX)
  /-- The scheme-theoretic intersection is regular (a reduced point): local equations of `X` and
  `Y` form a regular system of parameters, i.e. the divisors are not tangent. -/
  [isRegular_inter : IsRegular (pullback iX iY)]
  /-- The corner point. -/
  z : Z
  range_inter : Set.range iX ∩ Set.range iY = {z}
  /-- The complement `Z - Y`. -/
  U : Scheme.{u}
  /-- The open immersion `j : Z - Y ⟶ Z`. -/
  j : U ⟶ Z
  [isOpenImmersion_j : IsOpenImmersion j]
  range_j : Set.range j = (Set.range iY)ᶜ
  /-- The complement `Z - (X ∪ Y)`. -/
  V : Scheme.{u}
  /-- The open immersion `i : Z - (X ∪ Y) ⟶ Z - Y`. -/
  i : V ⟶ U
  [isOpenImmersion_i : IsOpenImmersion i]
  range_i_j : Set.range (i ≫ j) = (Set.range iX ∪ Set.range iY)ᶜ

attribute [instance] TransverseCorner.isLocallyNoetherian TransverseCorner.isRegular_Z
  TransverseCorner.isRegular_X TransverseCorner.isRegular_Y TransverseCorner.isRegular_inter
  TransverseCorner.isRegularImmersion_iX
  TransverseCorner.isRegularImmersion_iY
  TransverseCorner.isOpenImmersion_j TransverseCorner.isOpenImmersion_i

end Scheme

namespace Etale

open Scheme

variable (ℓ : ℕ) {Λ : Type (u + 1)} [CommRing Λ]

/-- A sheaf of `Λ`-modules on `V_ét` has *finite `ℓ`-group monodromy* if it is trivialized by a
finite étale Galois cover of `V` whose group is a finite `ℓ`-group: its pullback to the cover is
the constant sheaf on a finite `Λ`-module. Such a sheaf is finite locally constant, and on a
connected `V` its monodromy representation factors through the finite `ℓ`-group (blueprint
`lemma-cohomology-near-two-transverse-divisors`). -/
def HasFiniteEllGroupMonodromy {V : Scheme.{u}}
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G) (c : V.GaloisCover G)
    (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
    Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj F ≅
      (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)

/-- A complex `E ∈ D(V_ét, Λ)` is *bounded with finite `ℓ`-group monodromy* if it is bounded and
each of its cohomology sheaves has finite `ℓ`-group monodromy
(`AlgebraicGeometry.Etale.HasFiniteEllGroupMonodromy`): a bounded complex with finite locally
constant cohomology whose monodromy factors through a finite `ℓ`-group (blueprint
`lemma-cohomology-near-two-transverse-divisors`). -/
def IsBoundedFiniteEllGroupMonodromy {V : Scheme.{u}}
    (E : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  (∃ a b : ℤ, E.IsGE a ∧ E.IsLE b) ∧
    ∀ n : ℤ, HasFiniteEllGroupMonodromy ℓ ((DerivedCategory.homologyFunctor _ n).obj E)

end Etale

namespace Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k) (Λ : Type (u + 1)) [CommRing Λ]

/-- The complex `M = Rj_* i_! E` on `Z` of the transverse boundary calculation (blueprint
`lemma-cohomology-near-two-transverse-divisors`), for `E ∈ D(Z - (X ∪ Y), Λ)`. -/
noncomputable def boundaryComplex
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (Sheaf C.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (R((C.j)_*[ModuleCat.{u + 1} Λ])).obj
    (((C.i)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E)

/-- The corner point `z` is a closed point of `Z`: it is the intersection of the closed subsets
`X` and `Y`. -/
lemma isClosed_singleton_z : IsClosed ({C.z} : Set C.Z) := by
  rw [← C.range_inter]
  exact C.iX.isClosedEmbedding.isClosed_range.inter C.iY.isClosedEmbedding.isClosed_range

/-- The punctured divisor `Y - z`, as an open subscheme of `Y`. -/
def puncturedY : C.Y.Opens :=
  ⟨(C.iY ⁻¹' {C.z})ᶜ, (C.isClosed_singleton_z.preimage C.iY.continuous).isOpen_compl⟩

end Scheme.TransverseCorner

end AlgebraicGeometry
