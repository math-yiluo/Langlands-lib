/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisCoverConnected
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDual
public import WeilConjectures.TraceFormula.TransverseBoundary.DevissageStep

/-!
# Dévissage of complexes with finite `ℓ`-group monodromy

Let `V` be a connected scheme, `ℓ` a prime and `Λ` a finite commutative ring with `ℓ` nilpotent
in `Λ`. Every sheaf `H` of `Λ`-modules on `V_ét` with finite `ℓ`-group monodromy
(`AlgebraicGeometry.Etale.HasFiniteEllGroupMonodromy`) is an iterated extension of constant
sheaves `N_V` with `N` a finite `Λ`-module killed by `ℓ`: after replacing the trivializing Galois
cover by a connected subcover (`AlgebraicGeometry.Scheme.GaloisCover.exists_connected_subcover`),
the `ℓ`-group `G` acts `Λ`-linearly on the nonzero finite `ℓ`-group `M = Γ(P, π^* H)` and has a
nonzero fixed vector `v` with `ℓ v = 0`; the fixed vector descends to a section of `H` over `V`,
which spans an injection `(Λ v)_V ↪ H` whose cokernel is trivialized by the same cover with the
smaller value `M / Λ v`. By induction on the cardinality of `M`, and by truncation for bounded
complexes, a property of objects of `D(V_ét, Λ)` stable under isomorphisms, shifts and extensions
which holds for these constant sheaves holds for every bounded complex whose cohomology sheaves
have finite `ℓ`-group monodromy (blueprint `lemma-cohomology-near-two-transverse-divisors--1`,
dévissage).

## Main statements

- `AlgebraicGeometry.Etale.prop_singleFunctor_of_hasFiniteEllGroupMonodromy`: the dévissage for
  sheaves.
- `AlgebraicGeometry.Etale.prop_of_isBoundedFiniteEllGroupMonodromy`: the dévissage for bounded
  complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Having finite `ℓ`-group monodromy is a property of sheaves closed under isomorphisms. -/
instance HasFiniteEllGroupMonodromy.isClosedUnderIsomorphisms (ℓ : ℕ) {Λ : Type (u + 1)}
    [CommRing Λ] (V : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (HasFiniteEllGroupMonodromy (Λ := Λ) (V := V) ℓ) :=
  ⟨fun e h ↦ h.of_iso e⟩

variable {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime] {Λ : Type (u + 1)}
  [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
  (P : ObjectProperty (DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
  [P.IsClosedUnderIsomorphisms]
  (hshift : ∀ (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
    P K → P (K⟦n⟧))
  (hext : ∀ T ∈ distTriang (DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
    P T.obj₁ → P T.obj₃ → P T.obj₂)
  (hconst : ∀ (N : ModuleCat.{u + 1} Λ), Finite N → (∀ n : N, (ℓ : Λ) • n = 0) →
    P ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)))

omit [ConnectedSpace V] [Fact ℓ.Prime] [Finite Λ] in
include hconst in
/-- A property as in the dévissage, holding for the constant sheaf at the zero module, holds for
every zero object of `D(V_ét, Λ)`. -/
lemma prop_of_isZero (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero K) : P K :=
  P.prop_of_iso (IsZero.iso (Functor.map_isZero _ (Functor.map_isZero _
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of Λ PUnit)))) hK)
    (hconst (ModuleCat.of Λ PUnit) inferInstance fun _ ↦ Subsingleton.elim _ _)

omit [ConnectedSpace V] in
include hΛ hext hconst in
/-- The dévissage for a sheaf trivialized by a Galois cover with connected total space, by
induction on the cardinality of the value `M` of the trivialization: a nonzero global section
killed by `ℓ` (`AlgebraicGeometry.Etale.exists_ne_zero_smul_eq_zero_of_connected_cover`) spans
a constant subsheaf whose quotient is trivialized by the same cover with smaller value
(`AlgebraicGeometry.Etale.exists_mono_constantSheaf_of_connected_cover`)
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`). -/
theorem prop_singleFunctor_of_connected_cover {G : Type (u + 1)} [Group G] [Finite G]
    (hG : IsPGroup ℓ G) (c : V.GaloisCover G) [ConnectedSpace c.P]
    (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (M : ModuleCat.{u + 1} Λ) [Finite M]
    (φ : (c.π)^*[ModuleCat.{u + 1} Λ].obj H ≅
      (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :
    P ((DerivedCategory.singleFunctor _ 0).obj H) := by
  induction hn : Nat.card M using Nat.strong_induction_on generalizing H M with
  | _ n ih =>
  subst hn
  by_cases hM : Subsingleton M
  · refine prop_of_isZero ℓ P hconst _ (Functor.map_isZero _ ?_)
    exact isZero_of_isZero_upperStar_of_surjective _ c.π c.surjective.surj
      ((Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton M)).of_iso φ)
  rw [not_subsingleton_iff_nontrivial] at hM
  obtain ⟨y, hy0, hyℓ⟩ := exists_ne_zero_smul_eq_zero_of_connected_cover ℓ c hΛ hG H M φ
  obtain ⟨N, hN, hNℓ, χ, hχ, M', hM', hcard, ⟨φ'⟩⟩ :=
    exists_mono_constantSheaf_of_connected_cover ℓ c H M φ y hy0 hyℓ
  have hS : (ShortComplex.mk χ (cokernel.π χ) (cokernel.condition χ)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel χ) }
  exact hext _ hS.singleTriangle_distinguished (hconst N hN hNℓ)
    (ih _ hcard (cokernel χ) M' φ' rfl)

include hΛ hext hconst in
/-- **Dévissage of sheaves with finite `ℓ`-group monodromy** (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`): on a connected scheme, a property of objects of
`D(V_ét, Λ)` stable under isomorphisms and extensions which holds for the constant sheaves `N_V`,
`N` a finite `Λ`-module killed by `ℓ`, holds for every sheaf with finite `ℓ`-group monodromy,
placed in degree `0`. -/
theorem prop_singleFunctor_of_hasFiniteEllGroupMonodromy
    (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hH : HasFiniteEllGroupMonodromy ℓ H) :
    P ((DerivedCategory.singleFunctor _ 0).obj H) := by
  obtain ⟨G, _, _, hG, c, M, _, ⟨φ⟩⟩ := hH
  obtain ⟨K, c', _, i, hi⟩ := c.exists_connected_subcover
  exact prop_singleFunctor_of_connected_cover ℓ hΛ P hext hconst (hG.to_subgroup K) c' H M
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) i c.π c'.π hi.symm).app H ≪≫
      ((i)^*[ModuleCat.{u + 1} Λ]).mapIso φ ≪≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) i).app M)

include hΛ hshift hext hconst in
/-- **Dévissage of complexes with finite `ℓ`-group monodromy** (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`): on a connected scheme, a property of objects of
`D(V_ét, Λ)` stable under isomorphisms, shifts and extensions which holds for the constant
sheaves `N_V`, `N` a finite `Λ`-module killed by `ℓ`, holds for every bounded complex whose
cohomology sheaves have finite `ℓ`-group monodromy. -/
theorem prop_of_isBoundedFiniteEllGroupMonodromy
    (E : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : IsBoundedFiniteEllGroupMonodromy ℓ E) : P E := by
  obtain ⟨⟨a, b, ha, hb⟩, hE⟩ := hE
  exact DerivedCategory.prop_of_bounded_of_degreewise P (prop_of_isZero ℓ P hconst) hext
    (fun _ ↦ HasFiniteEllGroupMonodromy ℓ) (fun q H hH ↦ P.prop_of_iso
      (((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by lia)).app H)
      (hshift _ _ (prop_singleFunctor_of_hasFiniteEllGroupMonodromy ℓ hΛ P hext hconst H hH)))
    E ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hE

end AlgebraicGeometry.Etale
