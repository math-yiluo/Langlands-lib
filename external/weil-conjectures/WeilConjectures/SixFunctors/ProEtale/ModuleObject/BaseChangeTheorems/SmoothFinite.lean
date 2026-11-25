/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.TorsionSmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin

/-!
# Smooth base change for module objects with finite coefficients

Let `T` be a finite discrete commutative ring killed by an integer `N ≠ 0`, and `Λ = C(-, T)` the
corresponding condensed ring. Fix a Cartesian square of schemes

```
Y --e--> W
|        |
h        g
v        v
X --p--> S
```

with `p` smooth, `g` quasi-compact and quasi-separated, and `N` invertible on `S`. Then the base
change map `Lp^* Rg_* K ⟶ Rh_* Le^* K` of module objects over `Λ`
(`AlgebraicGeometry.ProEtale.CondensedRing.baseChangeMap`) is an isomorphism at every bounded
constructible complex `K`
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_baseChangeMap_app_of_smooth_of_finite`).

This is transported from the smooth base change for pro-étale sheaves of `T`-modules
(`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth_of_torsion`) along the
derived comparison `D(Φ)` of the two finite-coefficient models: `D(Φ)` of the condensed base change
map is isomorphic to the base change map of sheaves of `T`-modules at `D(Φ) K`
(`AlgebraicGeometry.ProEtale.nonempty_arrowIso_map_baseChangeMap_finiteCoefficient`), `D(Φ) K` is
of étale origin (`AlgebraicGeometry.ProEtale.isEtaleOrigin_of_isConstructible`), and sheaves of
`T`-modules are killed by `N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Sheaf

/-- A sheaf of modules over a ring in which the integer `N` vanishes is killed by `N`. -/
lemma nsmul_id_eq_zero_of_natCast_eq_zero {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Type*} [Ring R] {N : ℕ} (hN : (N : R) = 0) (F : Sheaf J (ModuleCat R)) :
    N • 𝟙 F = 0 := by
  apply (sheafToPresheaf J (ModuleCat R)).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  ext U x
  simp [← Nat.cast_smul_eq_nsmul R, hN]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {S W Y X : Scheme.{u}} {p : X ⟶ S} {g : W ⟶ S} {e : Y ⟶ W} {h : Y ⟶ X}

variable (p) in
/-- **Smooth base change for module objects with finite coefficients.** Let `T` be a finite
discrete commutative ring killed by an integer `N ≠ 0` invertible on `S`. For a Cartesian square
`e ≫ g = h ≫ p` with `p` smooth and `g` quasi-compact and quasi-separated, the base change map
`Lp^* Rg_* K ⟶ Rh_* Le^* K` of module objects over `C(-, T)` is an isomorphism at every bounded
constructible complex `K`. -/
theorem isIso_baseChangeMap_app_of_smooth_of_finite [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p) {N : ℕ} (hN₀ : N ≠ 0)
    (hNS : IsUnit (N : Γ(S, ⊤))) (hNT : (N : T) = 0)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) W)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} T) W) K) :
    IsIso ((baseChangeMap (Profinite.continuousMapRingObj.{u} T) sq.toCommSq).app K) := by
  rw [isIso_baseChangeMap_app_finiteCoefficient_iff]
  obtain ⟨K', hK', ⟨eK⟩⟩ := isEtaleOrigin_of_isConstructible T hK
  have hNT' : ((N : ULift.{u + 1} T)) = 0 := by
    rw [← ULift.down_inj, ULift.down_natCast, hNT, ULift.zero_down]
  exact isIso_derivedBaseChangeMap_app_of_smooth_of_torsion (ULift.{u + 1} T) p sq
    ⟨K', hK'.1.1⟩ (fun j ↦ IsTorsionSheafOfInvertibleOrder.of_nsmul_id_eq_zero _ hN₀ hNS
      (Sheaf.nsmul_id_eq_zero_of_natCast_eq_zero hNT' _)) _ eK

end AlgebraicGeometry.ProEtale.CondensedRing
