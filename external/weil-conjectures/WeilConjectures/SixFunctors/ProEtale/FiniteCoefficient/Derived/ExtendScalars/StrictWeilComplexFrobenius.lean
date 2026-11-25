/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.CompactFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplex

/-!
# Finite-level coefficient change for the Frobenius operators of strict Weil complexes

Let `R → S` be a homomorphism of finite commutative rings whose exponent is invertible on a
scheme `X` of finite type over a field `k`, with structure morphism `a_X : X ⟶ Spec k`, and
write `Ψ = - ⊗ᴸ_R S` for derived scalar extension of pro-étale sheaves. Let `g` be an
automorphism of `X` (the geometric Frobenius `g_γ` of the geometric fibre of a scheme over a
finite field) and `c = (X ⟶[c.i] c.Z ⟶[c.g] Spec k)` a compactification of `a_X` with an
endomorphism `gZ` of `c.Z` compatible with `g` over the identity of `Spec k` (the base change
of a compactification of the model). Compact cohomology is `RΓ_c(X, K) = Ra_{X!}(c) K`
(blueprint `proposition-construction-independence-rf-shriek--7`) with the global Frobenius operators
`F_{c,m} = RΓ_c(X, φ_m) ∘ g_c^{m,*}` (`AlgebraicGeometry.ProEtale.compactFrobenius`), and the
geometric stalk at a point `x : Spec k ⟶ X` fixed by `g_m = g^m` is `K_x̄ = Lx^* K` with the
local Frobenius `F_{x,m}` (`AlgebraicGeometry.ProEtale.stalkFrobenius`).

For a strict Weil complex `(K, φ)` over `R` with scalar extension `(K_S, φ_S)`
(`AlgebraicGeometry.ProEtale.StrictWeilComplex.extendScalars`), compact cohomology and the
geometric stalks commute with `Ψ`, compatibly with the Frobenius operators (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`).

## Main definitions

- `AlgebraicGeometry.ProEtale.StrictWeilComplex.globalFrobenius`: the global Frobenius operator
  `F_{c,m}` on `RΓ_c(X, K)`.
- `AlgebraicGeometry.ProEtale.StrictWeilComplex.localFrobenius`: the local Frobenius operator
  `F_{x,m}` on `K_x̄`.

## Main statements

- `AlgebraicGeometry.ProEtale.StrictWeilComplex.extendScalars_compactCohomology_stalk`:
  blueprint `theorem-grothendieck-lefschetz-trace-formula--7`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace StrictWeilComplex

variable {R : Type (u + 1)} [CommRing R] [IsNoetherianRing R] {k : Type u} [Field k]
  {X : Scheme.{u}} {aX : X ⟶ Spec (.of k)} {g : X ≅ X} (c : Compactification aX)
  {gZ : c.Z ⟶ c.Z} (hi : IsPullback g.hom c.i c.i gZ) (hg : CommSq gZ c.g c.g (𝟙 _))

/-- Blueprint `definition-frobenius-operator--1` (item 1): the *global Frobenius operator*
`F_{c,m} : RΓ_c(X, K) ⟶ RΓ_c(X, K)` of a strict Weil complex `(K, φ)`, for
`RΓ_c(X, K) = Ra_{X!}(c) K`: the compact Frobenius
(`AlgebraicGeometry.ProEtale.compactFrobenius`) of the iterated Weil datum `φ_m`
(`AlgebraicGeometry.ProEtale.weilDatumIterate`) for the iterates `g^m` and `gZ^m`,
`F_{c,m} = RΓ_c(X, φ_m) ∘ g_c^{m,*}` (blueprint
`lemma-scheme-frobenius-geometric-frobenius--3`). -/
noncomputable def globalFrobenius (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) (m : ℕ) :
    Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj ⟶ Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj :=
  compactFrobenius _ c (hi.iterateHom m) (commSq_iterateHom_id hg m)
    (weilDatumIterate W.frobenius.hom m)

/-- Blueprint `definition-frobenius-operator--1` (item 2): the *local Frobenius operator*
`F_{x,m} : K_x̄ ⟶ K_x̄` of a strict Weil complex `(K, φ)` at a point `x : Spec k ⟶ X` fixed by
`g^m`: the local Frobenius (`AlgebraicGeometry.ProEtale.stalkFrobenius`) of the iterated Weil
datum `φ_m` on the stalk complex `K_x̄ = Lx^* K`. -/
noncomputable def localFrobenius (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) (m : ℕ)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ iterateHom g.hom m = x) :
    L((x)^*[ModuleCat.{u + 1} R]).obj W.obj.obj ⟶ L((x)^*[ModuleCat.{u + 1} R]).obj W.obj.obj :=
  stalkFrobenius hx (weilDatumIterate W.frobenius.hom m)

variable (S : Type (u + 1)) [CommRing S] [Algebra R S] [Finite R] [Finite S]
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent R X]

/-- The comparison map `ξ : RΓ_c(X, K) ⊗ᴸ_R S ⟶ RΓ_c(X, K_S)` carries `F_{c,m} ⊗ᴸ_R S` to the
global Frobenius operator `F_{c,m}` of the scalar extension `(K_S, φ_S)`. -/
theorem globalFrobenius_extendScalars (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) (m : ℕ) :
    L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).map (W.globalFrobenius c hi hg m) ≫
        (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app W.obj.obj =
      (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app W.obj.obj ≫
        (W.extendScalars S aX).globalFrobenius c hi hg m := by
  rw [globalFrobenius, globalFrobenius, compactFrobenius_extendScalarsWeilDatum,
    extendScalars_frobenius_hom, extendScalarsWeilDatum_weilDatumIterate]

/-- At a point `x` fixed by `g^m`, the isomorphism `(K_S)_x̄ ≅ K_x̄ ⊗ᴸ_R S` carries the local
Frobenius operator `F_{x,m}` of the scalar extension `(K_S, φ_S)` to `F_{x,m} ⊗ᴸ_R S`. -/
theorem localFrobenius_extendScalars (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) (m : ℕ)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ iterateHom g.hom m = x) :
    (W.extendScalars S aX).localFrobenius m x hx ≫
        (leftDerivedUpperStarExtendScalarsIso R S x).hom.app W.obj.obj =
      (leftDerivedUpperStarExtendScalarsIso R S x).hom.app W.obj.obj ≫
        L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).map (W.localFrobenius m x hx) := by
  rw [localFrobenius, localFrobenius, extendScalars_frobenius_hom,
    ← extendScalarsWeilDatum_weilDatumIterate]
  exact stalkFrobenius_extendScalarsWeilDatum_comp R S hx _

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--7`: **finite-level coefficient
change**. Let `R → S` be a homomorphism of finite commutative rings whose exponent is invertible on
`X`, `(K, φ)` a strict Weil complex over `R` and `(K_S, φ_S)` its scalar extension. Then compact
cohomology and the geometric stalks commute with derived scalar extension `Ψ = - ⊗ᴸ_R S`, with their
Frobenius operators:
- the comparison map `ξ : RΓ_c(X, K) ⊗ᴸ_R S ⟶ RΓ_c(X, K_S)` is an isomorphism, and it carries
  `F_{c,m} ⊗ᴸ_R S` to the global Frobenius operator `F_{c,m}` of `(K_S, φ_S)`, for every `m`;
- at every point `x : Spec k ⟶ X` fixed by `g^m`, the isomorphism
  `(K_S)_x̄ = Lx^* (K ⊗ᴸ_R S) ≅ K_x̄ ⊗ᴸ_R S` carries the local Frobenius operator `F_{x,m}` of
  `(K_S, φ_S)` to `F_{x,m} ⊗ᴸ_R S`. -/
theorem extendScalars_compactCohomology_stalk (W : StrictWeilComplex (ModuleCat.{u + 1} R) g)
    (m : ℕ) :
    IsIso ((rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app W.obj.obj) ∧
      L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).map (W.globalFrobenius c hi hg m) ≫
          (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app W.obj.obj =
        (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app W.obj.obj ≫
          (W.extendScalars S aX).globalFrobenius c hi hg m ∧
      ∀ (x : Spec (.of k) ⟶ X) (hx : x ≫ iterateHom g.hom m = x),
        (W.extendScalars S aX).localFrobenius m x hx ≫
            (leftDerivedUpperStarExtendScalarsIso R S x).hom.app W.obj.obj =
          (leftDerivedUpperStarExtendScalarsIso R S x).hom.app W.obj.obj ≫
            L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).map
              (W.localFrobenius m x hx) :=
  ⟨isIso_rightDerivedLowerShriekOfCompactificationExtendScalarsMap_app R S c W.obj.property,
    globalFrobenius_extendScalars c hi hg S W m, localFrobenius_extendScalars S W m⟩

end StrictWeilComplex

end AlgebraicGeometry.ProEtale
