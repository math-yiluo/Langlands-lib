/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.PerfectTowerQuotient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.NormalizedTowerLimit
public import WeilConjectures.EtaleCohomology.PoincareDuality.CompactSupportPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AdicRealization
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# Normalized adic systems and the realization of their compact cohomology and stalks

Let `R` be a ring with an ideal `I = (ϖ)` (the intended case being `R = 𝒪_E`, `I = 𝔪_E`) and
`A_n = R ⧸ Iⁿ`. A *normalized adic system* on a scheme `X` (`AlgebraicGeometry.Etale.AdicSystem`) is
a family `L_n ∈ Dᵇctf(X, A_n)` of complexes with transitions `L_{n+1} ⟶ Res L_n` exhibiting `L_n` as
`L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`.

For a separated finite-type scheme `a_X : X ⟶ s` over a separably closed field, the compact
cohomology complexes `P_n = RΓ_c(X, L_n) ∈ D(A_n)` and the geometric stalks `P_{x̄, n} = (L_n)_x̄`
form normalized towers of perfect complexes, whose derived limits over `R` are therefore perfect,
reduce to the levels, and carry lifts of compatible families of endomorphisms whose traces are the
limits of the levelwise traces.

## Main definitions

- `AlgebraicGeometry.Etale.AdicSystem`: a normalized `A_•`-system.
- `AlgebraicGeometry.Etale.IsCoefficientChange`: a natural isomorphism `Res ∘ Φ ≅ Φ' ∘ Res`
  carrying derived base changes to derived base changes.
- `AlgebraicGeometry.Etale.geometricStalk`: the geometric stalk `RΓ(s, Lx̄^* -)`.
- `AlgebraicGeometry.Etale.compactPullback`, `AlgebraicGeometry.Etale.stalkPullback`: the
  compact-support base change `RΓ_c(X, K) ⟶ RΓ_c(X, Lg^* K)` along an automorphism `g` of `X`
  over an automorphism `h` of the base, and the stalk transport `K_x̄ ⟶ (Lg^* K)_x̄` at a point
  fixed by `(g, h)`. They define the global and local Frobenius operators.
- `AlgebraicGeometry.Etale.AdicSystem.compactSupportTower`,
  `AlgebraicGeometry.Etale.AdicSystem.stalkTower`: the normalized towers of perfect complexes
  `RΓ_c(X, L_n)` and `(L_n)_x̄`.

## Implementation notes

The levels are complexes on the small étale site, where the six functors, the compact-support
exchange maps and the perfectness of compact cohomology are available
(`proposition-six-operations-dctf`, `lemma-perfect-complexes-geometric-point`); their realization
`R lim_n ν^* L_n` is formed on the pro-étale site, where the cohomological range of the levels is
preserved (`AlgebraicGeometry.Etale.AdicSystem.realization`). Bounded constructible complexes of
finite Tor amplitude on the pro-étale site are exactly the `ν^* L` with `L ∈ Dᵇctf(X_ét, A_n)`.

The coefficient categories at the levels are `ModuleCat (R ⧸ Iⁿ)`, and the comparison between the
levels goes through restriction of scalars: compact cohomology with `A_{n+1}`-coefficients of the
restriction of an `A_n`-complex is identified with the restriction of its compact cohomology
with `A_n`-coefficients. This identification, the fact that it carries derived base changes
of constructible complexes of finite Tor amplitude to derived base changes, and its
compatibility with pullback, are the finite-level coefficient change of compact cohomology
(`lemma-sp-reduction--1`, subsection `sk-def-sfb-coefficient-comparisons`)
and of geometric stalks
(`theorem-grothendieck-lefschetz-trace-formula--7`, subsection
`theorem-grothendieck-lefschetz-trace-formula--7`), statements recorded here as
`AlgebraicGeometry.Etale.exists_isCoefficientChange_compactlySupportedGlobalSections` and
`AlgebraicGeometry.Etale.exists_isCoefficientChange_geometricStalk`. The towers are built from any
such identifications, so that they are data independent of a choice.

Compact cohomology and geometric stalks are read in `D(A_n)` through the point identification
of blueprint `lemma-perfect-complexes-geometric-point`: `RΓ_c(X, -)` is
`AlgebraicGeometry.Etale.compactlySupportedGlobalSections` and the geometric stalk at
`x̄ : s ⟶ X` is `RΓ(s, Lx̄^* -)`.

The levels of the system are indexed by `n : ℕ` with coefficients `R ⧸ Iⁿ`, as in
`DerivedCategory.IsNormalizedTower`; the towers of perfect complexes live over the local rings
`n ↦ R ⧸ Iⁿ⁺¹` (`Ideal.powSuccMk`), omitting the zero ring `R ⧸ I⁰`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section CoefficientChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}

/-- A natural isomorphism `α : Res ∘ Φ ≅ Φ' ∘ Res` between functors
`Φ : D(X_ét, Λ) ⥤ D(Λ)` and `Φ' : D(X_ét, Λ') ⥤ D(Λ')`, along a ring map `ρ : Λ →+* Λ'`,
*is a coefficient change* if it carries derived base changes of bounded constructible complexes
of finite Tor amplitude to derived base changes: for `η : K ⟶ Res K'` exhibiting `K'` as
`K ⊗ᴸ_Λ Λ'`, the map `Φ K ⟶ Φ (Res K') ≅ Res (Φ' K')` exhibits `Φ' K'` as `Φ K ⊗ᴸ_Λ Λ'`. This is
the statement that the coefficient comparison `(Φ K) ⊗ᴸ_Λ Λ' ⟶ Φ' (K ⊗ᴸ_Λ Λ')` is an
isomorphism. In a diagram, `α` fills the square
```
  D(X_ét, Λ') ──Φ'──▶ D(Λ')
        │                │
       Res      ⇓ α     Res
        ▼                ▼
  D(X_ét, Λ)  ──Φ──▶  D(Λ)
```
and the condition is that the composite `Φ K ──Φ η──▶ Φ (Res K') ──α──▶ Res (Φ' K')` is again a
base-change map whenever `η : K ⟶ Res K'` is one. -/
def IsCoefficientChange
    (Φ : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ))
    (Φ' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ'))
    (α : Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙ Φ ≅
      Φ' ⋙ ModuleCat.derivedRestrictScalars ρ) : Prop :=
  ∀ ⦃K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))⦄
    ⦃K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))⦄
    (η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K'),
    DerivedCategory.boundedConstructibleFiniteTor Λ X K →
      Sheaf.IsDerivedBaseChange η → ModuleCat.IsDerivedBaseChange (Φ.map η ≫ α.hom.app K')

variable (Λ) in
/-- The geometric stalk `K_x̄ = RΓ(s, Lx̄^* K) ∈ D(Λ)` at a point `x̄ : s ⟶ X`, read in `D(Λ)`
through the point identification of blueprint `lemma-perfect-complexes-geometric-point`. -/
noncomputable abbrev geometricStalk {s : Scheme.{u}} (x : s ⟶ X) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ) :=
  L((x)^*[ModuleCat.{u + 1} Λ]) ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s

end CoefficientChange

section Pullback

variable (Λ : Type (u + 1)) [CommRing Λ] {X s : Scheme.{u}}

/-- The transport `RΓ(s, M) ≅ RΓ(s, Lh^* M)` of derived global sections along an automorphism
`h` of `s`: the inverse of the invariance `RΓ(s, h^* M) ≅ RΓ(s, M)`
(`AlgebraicGeometry.Etale.upperStarCompRightDerivedGlobalSectionsIso`), the exact pullback `h^*`
computing the derived pullback
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`). -/
noncomputable def globalSectionsTransport (h : s ⟶ s) [IsIso h] :
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s ≅
      L((h)^*[ModuleCat.{u + 1} Λ]) ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s :=
  (upperStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) (asIso h)).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ h).symm _

variable [Finite Λ] {g : X ⟶ X} {h : s ⟶ s} {a : X ⟶ s} [QuasiCompact a] [HasCompactification a]

/-- Blueprint `definition-frobenius-operator--1` (the transport `g_{γ,c}^*`): the compact-support
base change `RΓ_c(X, K) ⟶ RΓ_c(X, Lg^* K)` along an automorphism `g` of `X` lying over an
automorphism `h` of the base `s` (`sq : g ≫ a = a ≫ h` cartesian):
```
  RΓ(s, Ra_! K) ≅ RΓ(s, Lh^* Ra_! K) ──Ex_!──▶ RΓ(s, Ra_! Lg^* K)
```
the transport of derived global sections along `h`
(`AlgebraicGeometry.Etale.globalSectionsTransport`) followed by the compact-support exchange map
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`). For `g = g_γ` the geometric
Frobenius of `X = X₀ ×_{k₀} k`, the global Frobenius operator of a Weil datum
`φ : Lg^* K ⟶ K` is `RΓ_c(X, φ) ∘ g_{γ,c}^*` (`AlgebraicGeometry.Etale.globalOperator`). -/
noncomputable def compactPullback (sq : IsPullback g a a h) [IsIso h] :
    compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a ⟶
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a :=
  Functor.whiskerLeft (R(a)_![ModuleCat.{u + 1} Λ]) (globalSectionsTransport Λ h).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (rightDerivedLowerShriekBaseChangeMap Λ sq)
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s) ≫
    (Functor.associator _ _ _).hom

/-- Blueprint `definition-frobenius-operator--1` (2) (the stalk transport `τ_{x,m}`): for a point
`x̄ : s ⟶ X` fixed by the pair `(g, h)` (`h ≫ x̄ = x̄ ≫ g`), the transport
`K_x̄ ⟶ (Lg^* K)_x̄` of geometric stalks
```
  RΓ(s, Lx̄^* K) ≅ RΓ(s, Lh^* Lx̄^* K) ≅ RΓ(s, L(h ≫ x̄)^* K) = RΓ(s, L(x̄ ≫ g)^* K)
    ≅ RΓ(s, Lx̄^* Lg^* K)
```
by the transport of derived global sections along `h` and the composition isomorphisms of the
derived pullback. -/
noncomputable def stalkPullback {x : s ⟶ X} (hx : h ≫ x = x ≫ g) [IsIso h] :
    geometricStalk Λ x ⟶ L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ geometricStalk Λ x :=
  Functor.whiskerLeft (L((x)^*[ModuleCat.{u + 1} Λ])) (globalSectionsTransport Λ h).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((leftDerivedUpperStarComp _ h x (x ≫ g) hx.symm).inv ≫
      (leftDerivedUpperStarComp _ x g).hom) (rightDerivedGlobalSections _ s) ≫
    (Functor.associator _ _ _).hom

end Pullback

section AdicSystem

variable {R : Type (u + 1)} [CommRing R] (I : Ideal R) (X : Scheme.{u})

/-- A *normalized `A_•`-system* on `X`, for the rings `A_n = R ⧸ Iⁿ`: complexes
`L_n ∈ Dᵇctf(X, A_n)` with transitions `L_{n+1} ⟶ Res L_n` compatible with the quotient maps
`A_{n+1} ⟶ A_n`, exhibiting `L_n` as `L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`. Its realization is the derived
limit `R lim_n ν^* Res L_n` on the pro-étale site
(`AlgebraicGeometry.Etale.AdicSystem.realization`).

No Weil structure is part of the datum; the category `Dᵇctf,W,adic(X, 𝒪_E)` of the blueprint
consists of such systems with a compatible strict Weil structure at every level
(`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.IsWeil`). Up to the indexing of the levels
(`R ⧸ Iⁿ` instead of `R ⧸ Iⁿ⁺¹`), the underlying tower is a normalized DVR tower
(`AlgebraicGeometry.Etale.NormalizedTower`) whose levels are constructible of finite Tor
amplitude. -/
structure AdicSystem where
  /-- The level `L_n ∈ D(X_ét, R ⧸ Iⁿ)`. -/
  obj (n : ℕ) : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (R ⧸ I ^ n)))
  /-- The transition `L_{n+1} ⟶ Res L_n`. -/
  map (n : ℕ) : obj (n + 1) ⟶
    (_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).obj (obj n)
  /-- The transition exhibits `L_n` as `L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`. -/
  isDerivedBaseChange (n : ℕ) : Sheaf.IsDerivedBaseChange (map n)
  /-- Each level is bounded constructible of finite Tor amplitude. -/
  boundedConstructibleFiniteTor (n : ℕ) :
    DerivedCategory.boundedConstructibleFiniteTor (R ⧸ I ^ n) X (obj n)

namespace AdicSystem

variable {I X} (S : AdicSystem I X)

/-- The tower `n ↦ Res L_n` in `D(X_ét, R)` of a normalized system, with the restricted
transitions. -/
noncomputable def restrict :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  Functor.ofOpSequence
    (X := fun n ↦ (_root_.DerivedCategory.levelRestrictScalars _ I n).obj (S.obj n)) fun n ↦
    (_root_.DerivedCategory.levelRestrictScalars _ I (n + 1)).map (S.map n) ≫
      (_root_.DerivedCategory.levelRestrictScalarsCompIso _ I n.le_succ).hom.app (S.obj n)

/-- The tower of a normalized system is normalized in the sense of
`DerivedCategory.IsNormalizedTower`. -/
lemma isNormalizedTower_restrict :
    _root_.DerivedCategory.IsNormalizedTower _ I S.restrict S.obj :=
  ⟨fun n ↦ Iso.refl _, S.map, S.isDerivedBaseChange, fun n ↦ by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    erw [Category.comp_id]
    exact Functor.ofOpSequence_map_homOfLE_succ (C := DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) _ n⟩

end AdicSystem

end AdicSystem

section Compatibility

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ'] (ρ : Λ →+* Λ')
  {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s}

/-- A coefficient comparison `α : Res ∘ RΓ_c(X, -) ≅ RΓ_c(X, -) ∘ Res` *is compatible with the
compact-support base change* along a pair `(g, h)` of automorphisms
(`AlgebraicGeometry.Etale.compactPullback`): the square
```
  RΓ_c(X, Res K') ────── g_c^* ──────▶ RΓ_c(X, Lg^* Res K') ≅ RΓ_c(X, Res Lg^* K')
        │ α                                                        │ α
        ▼                                                          ▼
  Res RΓ_c(X, K') ──── Res g_c^* ────▶ Res RΓ_c(X, Lg^* K')
```
commutes, the identification `Lg^* Res ≅ Res Lg^*` being
`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso`. -/
def IsCompactPullbackCompatible {a : X ⟶ s} [QuasiCompact a] [HasCompactification a]
    (α : Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') a ⋙
        ModuleCat.derivedRestrictScalars ρ)
    (sq : IsPullback g a a h) [IsIso h] : Prop :=
  ∀ K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')),
    α.hom.app K' ≫ (ModuleCat.derivedRestrictScalars ρ).map ((compactPullback Λ' sq).app K') =
      (compactPullback Λ sq).app ((Sheaf.derivedRestrictScalars _ ρ).obj K') ≫
        (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).map
          ((leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K') ≫
        α.hom.app ((L((g)^*[ModuleCat.{u + 1} Λ'])).obj K')

/-- A coefficient comparison `β : Res ∘ (-)_x̄ ≅ (-)_x̄ ∘ Res` of geometric stalks *is compatible
with the stalk transport* at a point `x̄` fixed by a pair `(g, h)` of automorphisms
(`AlgebraicGeometry.Etale.stalkPullback`), in the same sense as
`AlgebraicGeometry.Etale.IsCompactPullbackCompatible`. -/
def IsStalkPullbackCompatible {x : s ⟶ X}
    (β : Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙ geometricStalk Λ x ≅
      geometricStalk Λ' x ⋙ ModuleCat.derivedRestrictScalars ρ)
    (hx : h ≫ x = x ≫ g) [IsIso h] : Prop :=
  ∀ K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')),
    β.hom.app K' ≫ (ModuleCat.derivedRestrictScalars ρ).map ((stalkPullback Λ' hx).app K') =
      (stalkPullback Λ hx).app ((Sheaf.derivedRestrictScalars _ ρ).obj K') ≫
        (geometricStalk Λ x).map ((leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K') ≫
        β.hom.app ((L((g)^*[ModuleCat.{u + 1} Λ'])).obj K')

end Compatibility

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} (S : AdicSystem I X)

section Geometric

variable {k : Type u} [Field k] [IsSepClosed k] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [IsSeparated aX] [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]


/-- The normalized tower of perfect complexes `P_n = RΓ_c(X, L_n)` over the local rings
`A_n = R ⧸ Iⁿ`, `n ≥ 1`, with transitions `RΓ_c(X, ν_n)` read through coefficient identifications
`α n` (`AlgebraicGeometry.Etale.exists_isCoefficientChange_compactlySupportedGlobalSections`). -/
noncomputable def compactSupportTower
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n)) :
    ModuleCat.NormalizedPerfectTower I.powSuccMk I.powSuccFactor I.powSuccMk_eq where
  obj n := (compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).obj
    (S.obj (n + 1))
  isPerfect n := isPerfect_compactlySupportedGlobalSections _ aX _
    (S.boundedConstructibleFiniteTor (n + 1))
  map n := (compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX).map
    (S.map (n + 1)) ≫ (α n).hom.app (S.obj (n + 1))
  isDerivedBaseChange n :=
    hα n _ (S.boundedConstructibleFiniteTor (n + 1 + 1)) (S.isDerivedBaseChange (n + 1))

/-- The normalized tower of perfect complexes `P_{x̄, n} = (L_n)_x̄` of geometric stalks at a
geometric point `x̄`, `n ≥ 1`, with transitions `(ν_n)_x̄` read through coefficient identifications
`β n` (`AlgebraicGeometry.Etale.exists_isCoefficientChange_geometricStalk`). -/
noncomputable def stalkTower (x : Spec (.of k) ⟶ X)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n)) :
    ModuleCat.NormalizedPerfectTower I.powSuccMk I.powSuccFactor I.powSuccMk_eq where
  obj n := (geometricStalk (R ⧸ I ^ (n + 1)) x).obj (S.obj (n + 1))
  isPerfect n := isPerfect_geometricStalk _ x _ (S.boundedConstructibleFiniteTor (n + 1))
  map n := (geometricStalk (R ⧸ I ^ (n + 1 + 1)) x).map (S.map (n + 1)) ≫
    (β n).hom.app (S.obj (n + 1))
  isDerivedBaseChange n :=
    hβ n _ (S.boundedConstructibleFiniteTor (n + 1 + 1)) (S.isDerivedBaseChange (n + 1))

variable [IsLocalRing R] [IsAdicComplete I R] {ϖ : R} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R)
  (hI : I = Ideal.span {ϖ})

omit [QuasiCompact aX] [IsSeparated aX] in
include hϖ hI in
/-- Compact cohomology: the derived limit `P_𝒪 = R lim_n RΓ_c(X, L_n)` over `R` of the compact
cohomology of a normalized system is perfect, represented by a bounded complex of finite free
`R`-modules, and it reduces to the levels: each projection `P_𝒪 ⟶ Res RΓ_c(X, L_{n+1})` exhibits
`RΓ_c(X, L_{n+1})` as `P_𝒪 ⊗ᴸ_R A_{n+1}`. -/
theorem compactSupportTower_realization
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n))
    {c : Cone (S.compactSupportTower aX α hα).restrict} (hc : IsHomotopyLimit c) :
    (∃ (M : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧
      M.IsStrictlyLE b ∧ (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
      Nonempty (c.pt ≅ DerivedCategory.Q.obj M)) ∧
    ∀ n, ModuleCat.IsDerivedBaseChange (f := I.powSuccMk n) (c.π.app (op n)) :=
  ⟨(S.compactSupportTower aX α hα).exists_iso_Q_obj_of_isAdicComplete hϖ hI hc,
    (S.compactSupportTower aX α hα).isDerivedBaseChange_π_app_of_isAdicComplete hϖ hI hc⟩

omit [QuasiCompact aX] [IsSeparated aX] [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))] in
include hϖ hI in
/-- Geometric stalks: the derived limit `P_{x̄, 𝒪} = R lim_n (L_n)_x̄` over `R` of the geometric
stalks of a normalized system is perfect, represented by a bounded complex of finite free
`R`-modules, and each projection `P_{x̄, 𝒪} ⟶ Res (L_{n+1})_x̄` exhibits `(L_{n+1})_x̄` as
`P_{x̄, 𝒪} ⊗ᴸ_R A_{n+1}`. -/
theorem stalkTower_realization (x : Spec (.of k) ⟶ X)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n))
    {c : Cone (S.stalkTower x β hβ).restrict} (hc : IsHomotopyLimit c) :
    (∃ (M : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧
      M.IsStrictlyLE b ∧ (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
      Nonempty (c.pt ≅ DerivedCategory.Q.obj M)) ∧
    ∀ n, ModuleCat.IsDerivedBaseChange (f := I.powSuccMk n) (c.π.app (op n)) :=
  ⟨(S.stalkTower x β hβ).exists_iso_Q_obj_of_isAdicComplete hϖ hI hc,
    (S.stalkTower x β hβ).isDerivedBaseChange_π_app_of_isAdicComplete hϖ hI hc⟩

end Geometric

end AdicSystem

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} (S : AdicSystem I X)
  {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

include hϖ hI in
/-- *Realization* of a normalized system: the derived limit `K_R = R lim_n ν^* Res L_n` on the
pro-étale site (the point of a homotopy limit cone `c` of the restricted tower
`AlgebraicGeometry.Etale.AdicSystem.restrict` followed by the comparison `ν^*`) is derived complete,
satisfies `K_R ⊗ᴸ_R R ⧸ Iⁿ ≅ ν^* L_n` compatibly with the transitions, and lies in every common
range of degrees `[a, b]` of the levels. -/
theorem realization {c : Cone (S.restrict ⋙
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory)}
    (hc : IsHomotopyLimit c) :
    _root_.DerivedCategory.derivedComplete (Scheme.ProEt.topology X) I c.pt ∧
      (∃ e : _root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I c.pt ≅
          S.restrict ⋙ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory,
        ∀ n : ℕ, c.π.app (op n) =
          (_root_.DerivedCategory.derivedCompletionCone (Scheme.ProEt.topology X) I c.pt).π.app
            (op n) ≫ e.hom.app (op n)) ∧
      ∀ a b : ℤ, (∀ n : ℕ, (S.restrict.obj (op n)).IsGE a ∧ (S.restrict.obj (op n)).IsLE b) →
        c.pt.IsGE a ∧ c.pt.IsLE b :=
  ProEtale.derivedComplete_and_exists_iso_of_isNormalizedTower hϖ hI
    S.isNormalizedTower_restrict hc

/-- The realization `R lim_n ν^* Res L_n` of a normalized system exists: the derived category of
pro-étale sheaves of `R`-modules has countable products, countable products of pro-étale
sheaves being exact (`CategoryTheory.derivedCategory_hasCountableProducts`). -/
lemma exists_isHomotopyLimit_realization :
    ∃ c : Cone (S.restrict ⋙
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory),
      IsHomotopyLimit c :=
  have := derivedCategory_hasCountableProducts
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))
  exists_isHomotopyLimit _

end AdicSystem

end AlgebraicGeometry.Etale
