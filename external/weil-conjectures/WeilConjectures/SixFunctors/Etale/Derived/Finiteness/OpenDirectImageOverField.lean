/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.OpenImmersionFieldBaseChange

/-!
# Open direct images over a field

Let `j : X ⟶ Y` be an open immersion of schemes of finite type over a field `k` and let `Λ` be a
finite ring whose exponent is invertible in `k`. On the étale sites, `Rj_*` preserves bounded
constructibility, and it commutes with base change along `Y ×_k T ⟶ Y` for every `k`-scheme `T`
of finite type, on bounded constructible complexes.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_and_isIso_baseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Let `k` be a field, let `Λ` be a finite ring killed by a positive integer invertible in `k`, and
let `j : X ⟶ Y` be an open immersion with `Y` of finite type over `k`. Then:

1. `Rj_*` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`;
2. for every `k`-scheme `T` of finite type, with `g_Y : Y_T ⟶ Y` the projection from
   `Y_T = Y ×_k T` and `j_T : X_T ⟶ Y_T`, `g_X : X_T ⟶ X` the base change of `j` along `g_Y`,
   and every `K ∈ D^b_c(X, Λ)`, the base change map
   `g_Y^* Rj_* K ⟶ Rj_{T,*} g_X^* K` is an isomorphism. -/
theorem boundedConstructible_rightDerivedLowerStar_and_isIso_baseChange [Finite Λ]
    [HasInvertibleExponent Λ (Spec (.of k))] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (j : X ⟶ Y) [IsOpenImmersion j] :
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    ∀ {T YT XT : Scheme.{u}} (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
      {gY : YT ⟶ Y} {q : YT ⟶ T} (_ : IsPullback gY q aY aT) {gX : XT ⟶ X} {jT : XT ⟶ YT}
      (sq : IsPullback gX jT j gY)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K),
      IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app ⟨K, hK.1.1⟩) := by
  refine ⟨boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion Λ aY j,
    fun aT _ _ _ _ hW _ _ sq K hK ↦ ?_⟩
  obtain ⟨n, -, hΛ, hu⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Spec (.of k))
  have hn : IsUnit (n : k) := by simpa using hu.map (Scheme.ΓSpecIso (.of k)).hom.hom
  exact isIso_baseChange_app_of_isOpenImmersion_of_field Λ aY aT j hW sq n hn hΛ K hK

end Etale

end AlgebraicGeometry
