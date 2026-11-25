/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import WeilConjectures.AlgebraicGeometry.FormalGlueingCanonicalMaps

/-!
# A compatible chart tuple after localization

Source: Stacks Project, Remark 05EL and Lemma 05EP, as used in Proposition 05ER.
-/

@[expose] public section

universe u v w

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

private theorem map_comp.{w₁, w₂} (r : R)
    {M : ModuleCat.{w} R} {N : ModuleCat.{w₁} R} {P : ModuleCat.{w₂} R}
    (h : M →ₗ[R] N) (k : N →ₗ[R] P) :
    localMap r (k.comp h) = (localMap r k).comp (localMap r h) :=
  IsLocalizedModule.map_comp' _ _ _ _ h k

private theorem map_sub.{w₁} (r : R) {M : ModuleCat.{w} R} {N : ModuleCat.{w₁} R}
    (h k : M →ₗ[R] N) :
    localMap r (h - k) = localMap r h - localMap r k :=
  (IsLocalizedModule.map (Submonoid.powers r)
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N)).map_sub h k

private theorem map_mk.{w₁} (r : R) {M : ModuleCat.{w} R} {N : ModuleCat.{w₁} R} (h : M →ₗ[R] N)
    (m : M) (t : Submonoid.powers r) :
    localMap r h (LocalizedModule.mk m t) = LocalizedModule.mk (h m) t :=
  IsLocalizedModule.map_LocalizedModules _ h m t

private theorem power_zero (r : R) :
    (⟨r ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers r) = 1 := Subtype.ext (pow_zero r)

private theorem swap_mk (r s : R) (M : ModuleCat.{w} R) (y : localize r M) :
    swap r s M (LocalizedModule.mk y 1) =
      localMap r (LocalizedModule.mkLinearMap (Submonoid.powers s) M) y := by
  induction y using LocalizedModule.induction_on with
  | _ m t =>
    obtain ⟨t, ⟨n, rfl⟩⟩ := t
    simpa only [power_zero, localMap, IsLocalizedModule.map_LocalizedModules,
      LocalizedModule.mkLinearMap_apply] using
      (swap_properties M r s).2.2.1 m n 0

set_option backward.isDefEq.respectTransparency false in
private theorem compare_tensor (φ : R →+* S) (r : R) (M : ModuleCat.{w} R)
    (y : localize r M) :
    letI : Algebra R S := φ.toAlgebra
    compare φ r M (localMap r (TensorProduct.mk R S M 1) y) =
      TensorProduct.tmul R (1 : S) y := by
  let : Algebra R S := φ.toAlgebra
  induction y using LocalizedModule.induction_on with
  | _ m t =>
    obtain ⟨t, ⟨n, rfl⟩⟩ := t
    rw [map_mk]
    exact (compare_properties φ M r).2.1 m 1 n

set_option backward.isDefEq.respectTransparency false in
/-- The canonical localized chart tuple has compatibility differences vanishing after
localizing at the chart parameter. This only constructs a localized ambient tuple;
it does not clear denominators or produce an element of `h0`. The tuple is
specified by the inverse of the finite-product localization comparison, with
prime coordinate `(X.alpha i).symm (1 ⊗ x)` and chart coordinates
`X.alpha_overlap i j (x/1)`.
Source: Stacks Project, Remark 05EL, conditions (a) and (b), Lemma 05EP, and
Proposition 05ER, second paragraph
(blueprint: lem-weil-pbc-formal-glueing-localized-chart-tuple).

Proof:
Set `u = f i`. The prime coordinate is `(X.alpha i).symm (1 ⊗ x)` and the
`j` coordinate is `X.alpha_overlap i j (x/1)`. Localization commutes with the
finite product, so these coordinates determine an element of the localization
of the ambient product. Evaluate the square for
`(i,j)` on the prime coordinate and use the canonical swap and tensor comparison
fraction formulas. The comparison is injective by `compare_properties`; hence
equality after this comparison gives equality of the two terms in the localized
prime/chart difference.
Evaluate the cocycle for `(i,j,k)` on `(x/1)/1`, using the swap fraction formula:
the two terms in the localized overlap difference agree. Thus all the displayed
differences vanish. If `f i = 0`, all modules localized there are zero. An index
`i` excludes the empty index set; no nonzero ring or module hypothesis is needed. -/
theorem localized_chart_tuple_compatible {t : ℕ} (φ : R →+* S)
    (f : Fin t → R) (X : Data.{u, v, w} φ f) (i : Fin t)
    (x : piece (f i) (X.M i)) :
    letI : Algebra R S := φ.toAlgebra
    let A := ModuleCat.of R (restrict φ X.M' × ∀ j : Fin t, piece (f j) (X.M j))
    let p : ∀ j : Fin t, A →ₗ[R] piece (f j) (X.M j) :=
      fun j ↦ (LinearMap.proj j).comp (LinearMap.snd R _ _)
    let a := fun j : Fin t ↦
      (((X.alpha j).toLinearMap.comp
        (LocalizedModule.mkLinearMap _ (restrict φ X.M'))).comp
          (LinearMap.fst R _ _) -
        (TensorProduct.mk R S (piece (f j) (X.M j)) 1).comp (p j))
    let b := fun j k : Fin t ↦
      (((X.alpha_overlap j k).toLinearMap.comp
        (LocalizedModule.mkLinearMap _ (piece (f j) (X.M j)))).comp (p j) -
        (LocalizedModule.mkLinearMap _ (piece (f k) (X.M k))).comp (p k))
    let T := Submonoid.powers (f i)
    let ell₀ := LocalizedModule.mkLinearMap T (restrict φ X.M')
    let ell₁ : (∀ j, piece (f j) (X.M j)) →ₗ[R]
        (∀ j, LocalizedModule T (piece (f j) (X.M j))) :=
      LinearMap.pi fun j ↦ (LocalizedModule.mkLinearMap T _).comp (LinearMap.proj j)
    let e := IsLocalizedModule.linearEquiv T (ell₀.prodMap ell₁)
      (LocalizedModule.mkLinearMap T A)
    let z := e ((X.alpha i).symm (TensorProduct.tmul R (1 : S) x),
      fun j ↦ X.alpha_overlap i j (LocalizedModule.mk x 1))
    (∀ j, localMap (f i) (a j) z = 0) ∧
      (∀ j k, localMap (f i) (b j k) z = 0) := by
  let : Algebra R S := φ.toAlgebra
  intro A p a b T ell₀ ell₁ e z
  have hfst : localMap (f i) (LinearMap.fst R (restrict φ X.M')
      (∀ j : Fin t, piece (f j) (X.M j))) z =
      (X.alpha i).symm (TensorProduct.tmul R (1 : S) x) := by
    have he : (localMap (f i) (LinearMap.fst R (restrict φ X.M')
        (∀ j : Fin t, piece (f j) (X.M j)))).comp e.toLinearMap =
        LinearMap.fst R _ _ := by
      apply IsLocalizedModule.ext T (ell₀.prodMap ell₁)
        (IsLocalizedModule.map_units ell₀)
      apply LinearMap.ext
      intro m
      change localMap (f i) (LinearMap.fst R _ _) (e ((ell₀.prodMap ell₁) m)) =
        ell₀ m.1
      rw [show e ((ell₀.prodMap ell₁) m) = LocalizedModule.mk m 1 from
        IsLocalizedModule.linearEquiv_apply T _ _ m]
      simp [localMap, ell₀, T, IsLocalizedModule.map_LocalizedModules]
      rfl
    exact LinearMap.congr_fun he _
  have hp (j : Fin t) : localMap (f i) (p j) z =
      X.alpha_overlap i j (LocalizedModule.mk x 1) := by
    have he : (localMap (f i) (p j)).comp e.toLinearMap =
        (LinearMap.proj j).comp (LinearMap.snd R _ _) := by
      apply IsLocalizedModule.ext T (ell₀.prodMap ell₁)
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T _))
      apply LinearMap.ext
      intro m
      change localMap (f i) (p j) (e ((ell₀.prodMap ell₁) m)) = ell₁ m.2 j
      rw [show e ((ell₀.prodMap ell₁) m) = LocalizedModule.mk m 1 from
        IsLocalizedModule.linearEquiv_apply T _ _ m]
      simp [localMap, ell₁, T, p, IsLocalizedModule.map_LocalizedModules]
      rfl
    exact LinearMap.congr_fun he _
  constructor
  · intro j
    dsimp only [a]
    rw [map_sub, map_comp, map_comp, map_comp]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [hfst, hp]
    apply sub_eq_zero.mpr
    apply (compare_properties φ (piece (f j) (X.M j)) (f i)).2.2.2.2.1
    rw [compare_tensor]
    have hs := LinearMap.congr_fun (X.square i j)
      (LocalizedModule.mk ((X.alpha i).symm (TensorProduct.tmul R (1 : S) x)) 1)
    simp only [LinearMap.comp_apply] at hs
    rw [localMap, IsLocalizedModule.map_LocalizedModules] at hs
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hs
    rw [swap_mk] at hs
    have hc := (compare_properties φ (piece (f i) (X.M i)) (f j)).2.1 x 1 0
    simp only [power_zero] at hc
    rw [hc] at hs
    have ht : extendMapR φ (X.alpha_overlap i j).toLinearMap
        (TensorProduct.tmul R (1 : S) (LocalizedModule.mk x 1)) =
        TensorProduct.tmul R (1 : S) (X.alpha_overlap i j (LocalizedModule.mk x 1)) := by
      change LinearMap.baseChange S (X.alpha_overlap i j).toLinearMap
        (TensorProduct.tmul R (1 : S) (LocalizedModule.mk x 1)) = _
      exact LinearMap.baseChange_tmul _ _ _
    exact hs.symm.trans ht
  · intro j k
    dsimp only [b]
    rw [map_sub, map_comp, map_comp, map_comp]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [hp, hp]
    apply sub_eq_zero.mpr
    have hc := LinearMap.congr_fun (X.cocycle i j k)
      (LocalizedModule.mk (LocalizedModule.mk x 1) 1)
    simp only [LinearMap.comp_apply] at hc
    simp only [localMap, IsLocalizedModule.map_LocalizedModules,
      LinearEquiv.coe_coe] at hc
    rw [swap_mk, swap_mk] at hc
    simp only [localMap, IsLocalizedModule.map_LocalizedModules,
      LocalizedModule.mkLinearMap_apply] at hc
    rw [swap_mk] at hc
    exact hc

end FormalGlueing
