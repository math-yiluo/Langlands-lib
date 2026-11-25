/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.DerivedHomTensorMapShift
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHomAmplitude

/-!
# The derived hom on `Dctf` commutes with tensoring by a finite constant coefficient

Let `k` be a field, `X` a scheme of finite type over `k`, `Λ` a finite ring and `N` a finitely
generated `Λ`-module. For `K, M ∈ Dctf(X_ét, Λ)` the canonical map
`RHom(K, M) ⊗ᴸ N_X ⟶ RHom(K, M ⊗ᴸ N_X)`
(`AlgebraicGeometry.Etale.DerivedCategory.derivedHomTensorMap`) is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedHomTensorMap_constantSingle`).

As a natural transformation in the coefficient (`derivedHomTensorNatTrans`), it is a morphism of
triangulated functors commuting with the shifts. It is an isomorphism at `Λ_X`, which is
invertible, hence at the free modules of finite rank. Both sides vanish above a common degree at
every `N_X`: `M ⊗ᴸ N_X` has homology in the Tor interval `[c, d]` of `M`, and `RHom(K, -)` raises
the upper bound of such complexes by a uniform amount
(`AlgebraicGeometry.Etale.derivedHomBoundedAmplitude_of_constructibleFiniteTor`). The way-out
argument along the first syzygies (`DerivedCategory.isIso_app_of_exists_distTriang`) concludes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
  (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- The map `RHom(K, M) ⊗ᴸ T ⟶ RHom(K, M ⊗ᴸ T)` is an isomorphism at the constant complex
`Λ_X`, which is invertible. -/
lemma isIso_derivedHomTensorNatTrans_app_constantSingle_self :
    IsIso ((derivedHomTensorNatTrans K M).app
      (constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ Λ))) := by
  have : IsIso ((derivedHomTensorNatTrans K M).app (𝟙_ _)) := by
    rw [derivedHomTensorNatTrans_app]
    exact isIso_derivedHomTensorMap K isInvertible_unit M
  exact (NatTrans.isIso_app_iff_of_iso _
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).symm).1 this

/-- The map `RHom(K, M) ⊗ᴸ T ⟶ RHom(K, M ⊗ᴸ T)` is an isomorphism at the constant complex on a
zero module. -/
lemma isIso_derivedHomTensorNatTrans_app_constantSingle_of_isZero {N : ModuleCat.{u + 1} Λ}
    (hN : IsZero N) :
    IsIso ((derivedHomTensorNatTrans K M).app
      (constantSingle (ModuleCat.{u + 1} Λ) X N)) := by
  have h : IsZero (constantSingle (ModuleCat.{u + 1} Λ) X N) :=
    (_root_.DerivedCategory.singleFunctor _ 0).map_isZero
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_isZero hN)
  exact isIso_of_source_target_iso_zero _
    (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj
      ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj M)).map_isZero h).isoZero
    (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M ⋙ RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).map_isZero
      h).isoZero

/-- The map `RHom(K, M) ⊗ᴸ T ⟶ RHom(K, M ⊗ᴸ T)` is an isomorphism at the constant complex on a
free module of finite rank. -/
lemma isIso_derivedHomTensorNatTrans_app_constantSingle_pi (n : ℕ) :
    IsIso ((derivedHomTensorNatTrans K M).app
      (constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Fin n → Λ)))) := by
  induction n with
  | zero =>
    refine isIso_derivedHomTensorNatTrans_app_constantSingle_of_isZero K M ?_
    rw [IsZero.iff_id_eq_zero]
    ext x i
    exact i.elim0
  | succ n ih =>
    exact NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ _
      (((finSuccShortComplex_shortExact Λ n).map_of_exact
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).singleTriangle_distinguished)
      (isIso_derivedHomTensorNatTrans_app_constantSingle_self K M) ih

end Etale

end AlgebraicGeometry
