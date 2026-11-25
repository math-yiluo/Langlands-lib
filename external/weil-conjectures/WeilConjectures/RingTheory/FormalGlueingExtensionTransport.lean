/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
import WeilConjectures.RingTheory.FormalGlueingCanonicalFunctorMaps
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Transport of glueing maps along a localized isomorphism

Source: Stacks Project, More on Algebra, Proposition 05ER.
(blueprint: lem-weil-pbc-formal-glueing-extension-transport).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

private theorem local_comp {R : Type u} [CommRing R] (a : R)
    {A B C : ModuleCat.{w} R} (h : A →ₗ[R] B) (k : B →ₗ[R] C) :
    localMap a (k.comp h) = (localMap a k).comp (localMap a h) :=
  IsLocalizedModule.map_comp' _ _ _ _ h k

private theorem extend_comp {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) {A B C : ModuleCat.{w} R} (h : A →ₗ[R] B) (k : B →ₗ[R] C) :
    extendMapR φ (k.comp h) = (extendMapR φ k).comp (extendMapR φ h) := by
  let : Algebra R S := φ.toAlgebra
  simp only [extendMapR, extendMap, LinearMap.baseChange_comp]
  rfl

private theorem factor_transport {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {φ : R →+* S} {t : ℕ} {f : Fin t → R}
    {A B X : Data.{u, v, w} φ f} (F : A ⟶ B) (ψ : A ⟶ X)
    (p : B.M' ≃ₗ[S] X.M') (hp : p.toLinearMap.comp F.prime = ψ.prime)
    (hc : ∀ i, Function.Bijective (F.chart i))
    (hψ : ∀ i, Function.Bijective (ψ.chart i)) :
    ∃ Φ : B ⟶ X, Function.Bijective Φ.prime ∧
      ∀ i, Function.Bijective (Φ.chart i) := by
  classical
  let e (i : Fin t) := LinearEquiv.ofBijective (F.chart i) (hc i)
  let c (i : Fin t) := (ψ.chart i).comp (e i).symm.toLinearMap
  have cc (i : Fin t) : (c i).comp (F.chart i) = ψ.chart i := by
    ext x
    exact congrArg (ψ.chart i) ((e i).symm_apply_apply x)
  have hs (i : Fin t) :
      Function.Surjective (localMap (f i) (restrictMap φ F.prime)) := by
    have he : Function.Surjective (extendMapR φ (F.chart i)) := by
      let : Algebra R S := φ.toAlgebra
      exact LinearMap.baseChange_surjective S (hc i).2
    intro y
    obtain ⟨z, hz⟩ := he ((B.alpha i) y)
    obtain ⟨x, hx⟩ := (A.alpha i).surjective z
    refine ⟨x, (B.alpha i).injective ?_⟩
    have h := LinearMap.congr_fun (F.prime_compat i) x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx, hz] using h
  let Φ : B ⟶ X :=
    { prime := p.toLinearMap
      chart := c
      prime_compat := by
        intro i
        apply LinearMap.ext
        intro y
        obtain ⟨x, rfl⟩ := hs i y
        have h := LinearMap.congr_fun (ψ.prime_compat i) x
        have hF := LinearMap.congr_fun (F.prime_compat i) x
        have hl : (localMap (f i) (restrictMap φ p.toLinearMap)).comp
            (localMap (f i) (restrictMap φ F.prime)) =
            localMap (f i) (restrictMap φ ψ.prime) := by
          rw [← local_comp]
          change localMap (f i) (restrictMap φ (p.toLinearMap.comp F.prime)) = _
          rw [hp]
        have hr : (extendMapR φ (c i)).comp (extendMapR φ (F.chart i)) =
            extendMapR φ (ψ.chart i) := by rw [← extend_comp, cc]
        have hlx := LinearMap.congr_fun hl x
        have hrx := LinearMap.congr_fun hr ((A.alpha i) x)
        dsimp only [LinearMap.comp_apply] at h hF hlx hrx ⊢
        simp only [LinearEquiv.coe_coe] at h hF hrx ⊢
        rw [hlx, hF, hrx]
        exact h
      chart_compat := by
        intro i k
        apply LinearMap.ext
        intro y
        have hsur : Function.Surjective (localMap (f k) (F.chart i)) :=
          IsLocalizedModule.map_surjective _ _ _ _ (hc i).2
        obtain ⟨x, rfl⟩ := hsur y
        have h := LinearMap.congr_fun (ψ.chart_compat i k) x
        have hF := LinearMap.congr_fun (F.chart_compat i k) x
        have hi : (localMap (f k) (c i)).comp (localMap (f k) (F.chart i)) =
            localMap (f k) (ψ.chart i) := by rw [← local_comp, cc]
        have hk : (localMap (f i) (c k)).comp (localMap (f i) (F.chart k)) =
            localMap (f i) (ψ.chart k) := by rw [← local_comp, cc]
        have hix := LinearMap.congr_fun hi x
        have hkx := LinearMap.congr_fun hk ((A.alpha_overlap i k) x)
        dsimp only [LinearMap.comp_apply] at h hF hix hkx ⊢
        simp only [LinearEquiv.coe_coe] at h hF hkx ⊢
        rw [hix, hF, hkx]
        exact h }
  exact ⟨Φ, p.bijective, fun i ↦ (hψ i).comp (e i).symm.bijective⟩

private theorem transport_map {R : Type u} [CommRing R]
    {A B A' B' : ModuleCat.{w} R} (hA : A = A') (hB : B = B')
    (h : A →ₗ[R] B) (k : A' →ₗ[R] B') (hk : HEq h k) :
    (eqToIso hB).hom.hom.comp (h.comp (eqToIso hA).inv.hom) = k := by
  subst A' B'
  simpa using eq_of_heq hk

private theorem cast_comp_heq {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (h : A = B) (g : A →ₗ[R] C) :
    HEq (g.comp (eqToIso h.symm).hom.hom) g := by
  cases h
  rfl

private theorem bijective_transport {R : Type u} [CommRing R]
    {A B A' B' : ModuleCat.{w} R} (hA : A = A') (hB : B = B')
    (h : A →ₗ[R] B) (k : A' →ₗ[R] B') (hk : HEq h k)
    (hb : Function.Bijective k) : Function.Bijective h := by
  subst A' B'
  exact (eq_of_heq hk).symm ▸ hb

private theorem canonical_piece {R : Type u} [CommRing R]
    (a : R) (M : ModuleCat.{w} R) :
    piece a (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M)) =
      localize a M := by
  dsimp [piece, restrict, ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj']
  congr 1
  ext r x
  exact IsScalarTower.algebraMap_smul (Localization.Away a) r x

/-- Transport the chart maps across localizations of an extension injection.
Source: Stacks Project, More on Algebra, Proposition 05ER, third paragraph.
(blueprint: lem-weil-pbc-formal-glueing-extension-transport).
Proof: identify the restricted canonical chart with the localized R-module by
module extensionality and algebraMap_smul. The bundled object equalities transport
the component maps, and the heterogeneous equalities identify the structural maps.
Define the prime map to be theta and each chart map to be psi.chart i
composed with the inverse of j localized at f i. The chart maps are bijective.
To check the prime compatibility, precompose with the localization of the scalar
extension of j. It is bijective because comparison identifies it with the scalar
extension of the bijective localized j. Naturality of comparison and the equation
theta composed with the scalar extension of j equals psi.prime reduce both sides
to psi's prime compatibility. For the overlap compatibility, precompose with j
localized first at f i and then at f k. Localization preserves inverses, so this
map is bijective. Naturality of interchange reduces both sides to psi's overlap
compatibility. These two equations define the required morphism. The prime map
is bijective by theta, and the chart maps are composites of bijections.
No condition on Can's morphism maps is used: only its canonical object maps enter.
For an empty chart set only the prime map and its bijectivity remain. -/
theorem exists_extension_transport {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (H E : ModuleCat.{max u v w} R) (X : Data.{u, v, max u v w} φ f)
    (ψ : Can.obj H ⟶ X) (j : H →ₗ[R] E)
    (θ : extend φ E ≃ₗ[S] X.M')
    (hj : ∀ i, Function.Bijective (localMap (f i) j))
    (hψ : ∀ i, Function.Bijective (ψ.chart i))
    (hθ : HEq (θ.toLinearMap.comp (extendMap φ j)) ψ.prime) :
    ∃ Φ : Can.obj E ⟶ X,
      Function.Bijective Φ.prime ∧ ∀ i, Function.Bijective (Φ.chart i) := by
  classical
  obtain ⟨maps, _, _, hm⟩ := canonical_functor_maps φ t f Can.obj hobj
  let F : Can.obj H ⟶ Can.obj E := maps (ModuleCat.ofHom j)
  have hF := hm H E (ModuleCat.ofHom j)
  let p := (eqToIso (hobj E).1).toLinearEquiv.trans θ
  have hp : p.toLinearMap.comp F.prime = ψ.prime := by
    have ht := transport_map (hobj H).1 (hobj E).1 F.prime (extendMap φ j) hF.1
    have hψp : ψ.prime.comp (eqToIso (hobj H).1).inv.hom =
        θ.toLinearMap.comp (extendMap φ j) := by
      exact eq_of_heq ((cast_comp_heq (hobj H).1 ψ.prime).trans hθ.symm)
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun ht ((eqToIso (hobj H).1).hom.hom x)
    have hψx := LinearMap.congr_fun hψp ((eqToIso (hobj H).1).hom.hom x)
    dsimp only [LinearMap.comp_apply] at hh hψx
    simp only [show (eqToIso (hobj H).1).inv.hom
        ((eqToIso (hobj H).1).hom.hom x) = x from
          (eqToIso (hobj H).1).toLinearEquiv.symm_apply_apply x] at hh hψx
    change θ ((eqToIso (hobj E).1).hom.hom (F.prime x)) = ψ.prime x
    rw [hh]
    exact hψx.symm
  have hc (i : Fin t) : Function.Bijective (F.chart i) := by
    exact bijective_transport
      ((congrArg (piece (f i)) ((hobj H).2.1 i)).trans (canonical_piece (f i) H))
      ((congrArg (piece (f i)) ((hobj E).2.1 i)).trans (canonical_piece (f i) E))
      (F.chart i) (localMap (f i) j) (hF.2 i) (hj i)
  exact factor_transport F ψ p hp hc hψ

end FormalGlueing
