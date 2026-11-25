/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

/-!
# Morphisms of normalized towers and their realizations

A family of isomorphisms `e_n : M_n ≅ N_n` between the levels of two normalized towers
(`AlgebraicGeometry.Etale.NormalizedTower`) commuting with the transition maps is an
isomorphism of normalized systems. Its restriction of scalars is an isomorphism of the towers
`n ↦ Res M_n` and `n ↦ Res N_n` in `D(X_ét, Λ)`, and it is realized by an isomorphism of the
derived limits `R lim_n Res M_n ≅ R lim_n Res N_n` whose reduction at every level `n` is `e_n`.
This is the step of the uniform-tower reconstruction that turns levelwise isomorphisms into an
isomorphism over the integral coefficients.

## Main definitions

- `AlgebraicGeometry.Etale.NormalizedTower.restrictIsoOfIso`: the isomorphism of the restricted
  towers induced by a levelwise isomorphism commuting with the transitions.

## Main statements

- `AlgebraicGeometry.Etale.NormalizedTower.exists_iso_of_isHomotopyLimit`: the realization of a
  levelwise isomorphism of normalized towers.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance localInstance_NormalizedTowerRealization_1 (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {X : Scheme.{u}}

/-- The morphism `(n ↦ Res M_n) ⟶ (n ↦ Res N_n)` of the restricted towers of two normalized
towers induced by morphisms `e_n : M_n ⟶ N_n` commuting with the transition maps. -/
noncomputable def NormalizedTower.restrictHomOfHom (M N : NormalizedTower I X)
    (e : ∀ n : ℕ, M.obj n ⟶ N.obj n)
    (he : ∀ n : ℕ, M.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor I n) X).map (e n) =
      e (n + 1) ≫ N.map n) :
    M.restrict ⟶ N.restrict :=
  NatTrans.ofOpSequence
    (fun n ↦ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ (n + 1))) X).map (e n))
    (fun n ↦ by
      have h := (derivedRestrictScalarsQuotientPowSuccIso (I := I) (X := X) n).hom.naturality
        (e n)
      simp only [Functor.comp_obj, Functor.comp_map] at h
      simp only [NormalizedTower.restrict, Functor.ofOpSequence_map_homOfLE_succ,
        Category.assoc, ← h, ← Functor.map_comp_assoc, he])

@[simp]
lemma NormalizedTower.restrictHomOfHom_app (M N : NormalizedTower I X)
    (e : ∀ n : ℕ, M.obj n ⟶ N.obj n)
    (he : ∀ n : ℕ, M.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor I n) X).map (e n) =
      e (n + 1) ≫ N.map n) (n : ℕ) :
    (NormalizedTower.restrictHomOfHom M N e he).app (op n) =
      (derivedRestrictScalars (Ideal.Quotient.mk (I ^ (n + 1))) X).map (e n) :=
  rfl

instance (M N : NormalizedTower I X) (e : ∀ n : ℕ, M.obj n ⟶ N.obj n) [∀ n, IsIso (e n)]
    (he : ∀ n : ℕ, M.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor I n) X).map (e n) =
      e (n + 1) ≫ N.map n) :
    IsIso (NormalizedTower.restrictHomOfHom M N e he) :=
  have (n : ℕᵒᵖ) : IsIso ((NormalizedTower.restrictHomOfHom M N e he).app n) := by
    rw [show n = op n.unop from rfl, NormalizedTower.restrictHomOfHom_app]
    infer_instance
  NatIso.isIso_of_isIso_app _

/-- The isomorphism `(n ↦ Res M_n) ≅ (n ↦ Res N_n)` of the restricted towers of two normalized
towers induced by isomorphisms `e_n : M_n ≅ N_n` commuting with the transition maps. -/
noncomputable def NormalizedTower.restrictIsoOfIso (M N : NormalizedTower I X)
    (e : ∀ n : ℕ, M.obj n ≅ N.obj n)
    (he : ∀ n : ℕ, M.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor I n) X).map (e n).hom =
      (e (n + 1)).hom ≫ N.map n) :
    M.restrict ≅ N.restrict :=
  asIso (NormalizedTower.restrictHomOfHom M N (fun n ↦ (e n).hom) he)

/-- **Realization of an isomorphism of normalized towers.** Let `e_n : M_n ≅ N_n` be
isomorphisms between the levels of two normalized towers commuting with the transition maps,
and let `R lim_n Res M_n` and `R lim_n Res N_n` be derived limits (the points of homotopy limit
cones `cM` and `cN`). Then there is an isomorphism `R lim_n Res M_n ≅ R lim_n Res N_n` whose
reduction at every level `n` is `e_n`: it commutes with the projections `π^M_n`, `π^N_n` to
`Res M_n` and `Res N_n`, that is `φ ≫ π^N_n = π^M_n ≫ Res(e_n)`:

```
R lim_n Res M_n ──── φ ────▶ R lim_n Res N_n
      │ π^M_n                      │ π^N_n
      ▼                            ▼
   Res M_n ─────── Res e_n ─────▶ Res N_n
```
-/
theorem NormalizedTower.exists_iso_of_isHomotopyLimit (M N : NormalizedTower I X)
    (e : ∀ n : ℕ, M.obj n ≅ N.obj n)
    (he : ∀ n : ℕ, M.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor I n) X).map (e n).hom =
      (e (n + 1)).hom ≫ N.map n)
    {cM : Cone M.restrict} (hcM : Pretriangulated.IsHomotopyLimit cM)
    {cN : Cone N.restrict} (hcN : Pretriangulated.IsHomotopyLimit cN) :
    ∃ φ : cM.pt ≅ cN.pt, ∀ n : ℕ, φ.hom ≫ cN.π.app (op n) =
      cM.π.app (op n) ≫ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ (n + 1))) X).map
        (e n).hom := by
  let E := NormalizedTower.restrictIsoOfIso M N e he
  let c : Cone N.restrict := (Cone.postcompose E.hom).obj cM
  have hc : Pretriangulated.IsHomotopyLimit c :=
    hcM.of_iso E c (Iso.refl _) fun n ↦ (Category.id_comp _).symm
  obtain ⟨φ, hφ⟩ := hc.exists_iso hcN
  exact ⟨φ, fun n ↦ hφ n⟩

end Etale

end AlgebraicGeometry
