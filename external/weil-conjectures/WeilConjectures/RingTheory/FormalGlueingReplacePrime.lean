/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
import WeilConjectures.AlgebraicGeometry.FormalGlueingCanonicalMaps

/-!
# Replacing the prime component of a glueing datum

Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (2),
and Remark 05EL (blueprint: lem-weil-pbc-formal-glueing-replace-prime).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

private theorem local_comp {R : Type u} [CommRing R]
    {M N T : ModuleCat.{w} R} (a : R) (h : M →ₗ[R] N) (k : N →ₗ[R] T) :
    localMap a (k.comp h) = (localMap a k).comp (localMap a h) :=
  IsLocalizedModule.map_comp' _ _ _ _ _ _

private theorem local_id {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{w} R) :
    localMap a (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  IsLocalizedModule.map_id _ _

private theorem swap_natural {R : Type u} [CommRing R]
    {M N : ModuleCat.{w} R} (a b : R) (h : M →ₗ[R] N) :
    (swap a b N).comp (localMap b (localMap a h)) =
      (localMap a (localMap b h)).comp (swap a b M) := by
  ext x
  induction x using LocalizedModule.induction_on with
  | _ m t =>
    induction m using LocalizedModule.induction_on with
    | _ p s =>
      rcases s with ⟨_, n, rfl⟩
      rcases t with ⟨_, k, rfl⟩
      simp only [LinearMap.comp_apply, localMap, IsLocalizedModule.map_LocalizedModules,
        (swap_properties M a b).2.2.1, (swap_properties N a b).2.2.1]

/-- Replace the prime component along a map that is invertible on every chart.
Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (2),
and Remark 05EL (blueprint: lem-weil-pbc-formal-glueing-replace-prime).

Proof: Keep all chart modules and overlap equivalences of X. Set the new prime
module to Q. On chart i use X.alpha i composed with the inverse of the localized
map gamma. The localized map is S-linear by localMap_smul, and its inverse is
S-linear by applying its injectivity to the required scalar identity. Hence the
new alpha has the required scalar compatibility. Naturality of swap follows
by writing an element as a double fraction: both composites send x/(fi^a fj^b)
to gamma(x)/(fj^b fi^a). Localization preserves compositions and inverses.
Precompose the proposed new square with the double localization of gamma.
Cancel the inverse localized maps; naturality of swap reduces both sides to
the square for X. This precomposition is bijective, so the new square holds.
The cocycle equation is unchanged. The prime component gamma and identity
chart maps give mu: its prime compatibility cancels the localized inverse,
and its overlap compatibility is the identity law. These chart maps are
bijective. The construction works also for the empty chart family and for
zero chart generators; no flatness or quotient hypothesis is required. -/
theorem exists_replace_prime {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) {t : ℕ} (f : Fin t → R)
    (X : Data.{u, v, max u v w} φ f) (Q : ModuleCat.{max u v w} S)
    (γ : X.M' →ₗ[S] Q)
    (hγ : ∀ i, Function.Bijective (localMap (f i) (restrictMap φ γ))) :
    ∃ (Y : Data.{u, v, max u v w} φ f) (hQ : Y.M' = Q) (μ : X ⟶ Y),
      (eqToIso hQ).hom.hom.comp μ.prime = γ ∧
      ∀ i, Function.Bijective (μ.chart i) := by
  classical
  let δ (i : Fin t) := localMap (f i) (restrictMap φ γ)
  let e (i : Fin t) := LinearEquiv.ofBijective (δ i) (hγ i)
  let α (i : Fin t) := (e i).symm.trans (X.alpha i)
  have hα (i : Fin t) : (α i).toLinearMap.comp (δ i) = (X.alpha i).toLinearMap := by
    ext x
    exact congrArg (X.alpha i) ((e i).symm_apply_apply x)
  have hαloc (i j : Fin t) :
      (localMap (f j) (α i).toLinearMap).comp (localMap (f j) (δ i)) =
        localMap (f j) (X.alpha i).toLinearMap := by
    rw [← local_comp, hα]
  let Y : Data.{u, v, max u v w} φ f :=
    { M' := Q
      M := X.M
      alpha := α
      alpha_smul := by
        intro i s x
        change X.alpha i ((e i).symm ((localizedSModule φ (f i) Q).smul s x)) =
          s • X.alpha i ((e i).symm x)
        rw [← X.alpha_smul]
        apply congrArg (X.alpha i)
        apply (e i).injective
        change δ i ((e i).symm ((localizedSModule φ (f i) Q).smul s x)) =
          δ i ((localizedSModule φ (f i) X.M').smul s ((e i).symm x))
        rw [show δ i ((e i).symm ((localizedSModule φ (f i) Q).smul s x)) =
          (localizedSModule φ (f i) Q).smul s x from (e i).apply_symm_apply _]
        rw [localMap_smul, show δ i ((e i).symm x) = x from (e i).apply_symm_apply x]
      alpha_overlap := X.alpha_overlap
      square := by
        intro i j
        have hs : Function.Surjective (localMap (f j) (δ i)) :=
          IsLocalizedModule.map_surjective _ _ _ _ (hγ i).2
        apply LinearMap.ext
        intro y
        obtain ⟨x, rfl⟩ := hs y
        have hn := swap_natural (f i) (f j) (restrictMap φ γ)
        have hX := LinearMap.congr_fun (X.square i j) x
        dsimp only [LinearMap.comp_apply] at hX ⊢
        have hi := LinearMap.congr_fun (hαloc i j) x
        have hj := LinearMap.congr_fun (hαloc j i)
          (swap (f i) (f j) (restrict φ X.M') x)
        have hnat := LinearMap.congr_fun hn x
        dsimp only [LinearMap.comp_apply] at hi hj hnat
        rw [hi, hnat, hj]
        exact hX
      cocycle := X.cocycle }
  let μ : X ⟶ Y :=
    { prime := γ
      chart := fun i ↦ LinearMap.id
      prime_compat := by
        intro i
        change (α i).toLinearMap.comp (δ i) =
          (extendMapR φ LinearMap.id).comp (X.alpha i).toLinearMap
        rw [hα]
        have hid : extendMapR φ (LinearMap.id : piece (f i) (X.M i) →ₗ[R]
            piece (f i) (X.M i)) = LinearMap.id := by
          let : Algebra R S := φ.toAlgebra
          simp only [extendMapR, extendMap, LinearMap.baseChange_id]
          rfl
        rw [hid, LinearMap.id_comp]
      chart_compat := by
        intro i j
        change (X.alpha_overlap i j).toLinearMap.comp
          (localMap (f j) LinearMap.id) =
          (localMap (f i) LinearMap.id).comp (X.alpha_overlap i j).toLinearMap
        rw [local_id, local_id, LinearMap.comp_id, LinearMap.id_comp] }
  refine ⟨Y, rfl, μ, ?_, ?_⟩
  · rfl
  · intro i
    exact Function.bijective_id

end FormalGlueing
