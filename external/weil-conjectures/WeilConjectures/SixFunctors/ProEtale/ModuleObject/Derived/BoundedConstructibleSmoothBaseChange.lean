/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!

# Smooth base change for bounded constructible `ℚ̄_ℓ`-complexes

For a commutative square
```
X' --u--> X
|         |
p'        p
v         v
Y' --v--> Y
```
of separated `k`-schemes of finite type, the *base change map* of the derived pushforward,
`Lv^* Rp_* ⟶ Rp'_* Lu^*` on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧`, is
`ProEtale.CondensedRing.boundedConstructibleBaseChange`. This file states smooth base change for
it at `Λ = ℚ̲̄_ℓ`.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_smooth`: **smooth
  base change** for `Λ = ℚ̲̄_ℓ`, blueprint `theorem-smooth-base-change-all-admissible` (section
  `chap-Construction-of-f`): for a cartesian square with `v` smooth, the base change map is an
  isomorphism on bounded constructible complexes.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {p : X ⟶ Y} {v : Y' ⟶ Y} {p' : X' ⟶ Y'} {u : X' ⟶ X}

/-- **Smooth base change** for bounded constructible `ℚ̄_ℓ`-complexes (blueprint
`theorem-smooth-base-change-all-admissible`, section `chap-Construction-of-f`, at the coefficient
ring `ℚ̄_ℓ`): for a cartesian square with `v` smooth, the base change map
`Lv^* Rp_* K ⟶ Rp'_* Lu^* K` is an isomorphism for every bounded constructible `K`.

As in the blueprint proof, `K` has an integral model `K₀` over some `𝒪_E`, the scalar comparisons
reduce the claim to the integral base change morphism at `K₀`
(`isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral`), and derived Nakayama to its first
derived reduction, the pro-étale base change morphism with coefficients `𝔽_E` at a complex of
étale origin (`isIso_boundedConstructibleBaseChange_integral_app_of_reduction`). The latter is
finite-coefficient smooth base change (`ProEtale.isIso_derivedBaseChangeMap_app_of_smooth`), `𝔽_E`
being killed by `ℓ`, which is invertible on `Y`. -/
theorem isIso_boundedConstructibleBaseChange_of_smooth (sq : IsPullback u p' p v)
    [Smooth v.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleBaseChange ℓ
      sq.toCommSq).app K) := by
  have hsq : IsPullback u.left p'.left p.left v.left := sq.map (Over.forget _)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := {}
  have : CompactSpace Y'.left := QuasiCompact.compactSpace_of_compactSpace Y'.hom
  have : IsLocallyNoetherian Y'.left := LocallyOfFiniteType.isLocallyNoetherian Y'.hom
  have : IsNoetherian Y'.left := {}
  have : QuasiCompact (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
  have : QuasiSeparated (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
  have : QuasiCompact p.left := QuasiCompact.of_comp p.left Y.hom
  have : QuasiSeparated p.left := QuasiSeparated.of_comp p.left Y.hom
  have hℓ : IsUnit (ℓ : k) := by
    refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar k ≠ ℓ) ?_
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar k).Prime) Fact.out).1
      ((ringChar.spec k ℓ).1 h)
  have hℓY : IsUnit (ℓ : Γ(Y.left, ⊤)) := by
    simpa using (hℓ.map (ΓSpecIso (.of k)).inv.hom).map Y.hom.appTop.hom
  revert K
  rw [← NatTrans.isIso_iff_isIso_app]
  refine isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral ℓ _ hsq fun E K₀ ↦ ?_
  refine isIso_boundedConstructibleBaseChange_integral_app_of_reduction ℓ E.1 _ hsq K₀ ?_
  exact ProEtale.isIso_derivedBaseChangeMap_app_of_smooth _ v.left hsq ℓ
    (Fact.out : ℓ.Prime).ne_zero (ProEtale.natCast_eq_zero_residueFieldCoeff.{u} ℓ E.1) hℓY _
    (ProEtale.boundedConstructible_derivedReduction_obj X.left ℓ E.1 _ K₀.property)

end AlgebraicGeometry.ProEtale.CondensedRing
