/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.LocalizationLocalization
/-! # Tensor products of localizations of a pushout
Source: Stacks Project, Algebra, Tag 00QV, verification of assertion (4).
(blueprint: lem-weil-pbc-localized-pushout-tensor)
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingHom
/-- Localizing a pushout at nested denominator sets gives a localization of its tensor product.
Source: Stacks Project, Algebra, Tag 00QV, verification of assertion (4).
Proof: First base change the localization of A at M along A to C. This gives the
localization Z of C at the image of M, identified by the pushout universal property
with LA tensor over R with S. The inclusion of the image of M in N lets the map
Z to LC factor the localization C to LC. Localization at nested submonoids shows
that LC is a localization of Z at the image of N. The tensor lift sends x tensor y
to m(x)n(y); its restrictions are the two prescribed maps by pushout uniqueness.
This argument does not assume injectivity, flatness, primality, or nonzero rings.
(blueprint: lem-weil-pbc-localized-pushout-tensor) -/
theorem exists_localized_pushout_tensor
    (R A S C LA LC : CommRingCat.{u})
    (σ : R →+* A) (ρ : R →+* S) (a : A →+* C) (b : S →+* C)
    (hp : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom a) (CommRingCat.ofHom b))
    (lA : A →+* LA) (lC : C →+* LC) (m : LA →+* LC)
    (hm : m.comp lA = lC.comp a)
    (M : Submonoid A) (N : Submonoid C) (hMN : M.map a ≤ N)
    (hLA : letI := lA.toAlgebra; IsLocalization M LA)
    (hLC : letI := lC.toAlgebra; IsLocalization N LC) :
    letI := σ.toAlgebra
    letI := ρ.toAlgebra
    letI := (lA.comp σ).toAlgebra
    ∃ φ : LA ⊗[R] S →+* LC,
      (∀ (x : LA) (y : S), φ (x ⊗ₜ[R] y) = m x * lC (b y)) ∧
      (letI := φ.toAlgebra
       ∃ U : Submonoid (LA ⊗[R] S), IsLocalization U LC) := by
  classical
  let := σ.toAlgebra
  let := ρ.toAlgebra
  let := lA.toAlgebra
  let := (lA.comp σ).toAlgebra
  let := lC.toAlgebra
  have : IsLocalization M LA := hLA
  have : IsLocalization N LC := hLC
  let M' := M.map a
  let L := Localization M'
  let t : LA →+* L := IsLocalization.map L a (Submonoid.le_comap_map M)
  have ht : t.comp lA = (algebraMap C L).comp a :=
    IsLocalization.map_comp (Submonoid.le_comap_map M)
  have hs : IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom lA)
      (CommRingCat.ofHom (algebraMap C L)) (CommRingCat.ofHom t) :=
    CommRingCat.isPushout_of_isLocalization a t ht M
  have hbig : IsPushout (CommRingCat.ofHom (lA.comp σ)) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom t) (CommRingCat.ofHom ((algebraMap C L).comp b)) :=
    hp.paste_horiz hs.flip
  have hcan := CommRingCat.isPushout_tensorProduct R LA S
  let eIso := hcan.isoIsPushout LA S hbig
  let e : LA ⊗[R] S ≃+* L := eIso.commRingCatIsoToRingEquiv
  have heA (x : LA) : e (x ⊗ₜ[R] 1) = t x :=
    ConcreteCategory.congr_hom (hcan.inl_isoIsPushout_hom LA S hbig) x
  have heS (y : S) : e (1 ⊗ₜ[R] y) = algebraMap C L (b y) :=
    ConcreteCategory.congr_hom (hcan.inr_isoIsPushout_hom LA S hbig) y
  let v : L →+* LC := IsLocalization.lift (M := M')
    (fun y ↦ IsLocalization.map_units LC ⟨y.val, hMN y.property⟩)
  let := v.toAlgebra
  have hv : v.comp (algebraMap C L) = lC := IsLocalization.lift_comp _
  have : IsScalarTower C L LC := IsScalarTower.of_algebraMap_eq' hv.symm
  have hvm : v.comp t = m := by
    apply IsLocalization.ringHom_ext M
    change (v.comp t).comp lA = m.comp lA
    rw [RingHom.comp_assoc, ht, ← RingHom.comp_assoc, hv, hm]
  have hloc : IsLocalization (N.map (algebraMap C L)) LC :=
    IsLocalization.isLocalization_of_submonoid_le L LC M' N hMN
  let φ : LA ⊗[R] S →+* LC := v.comp e.toRingHom
  refine ⟨φ, ?_, ?_⟩
  · intro x y
    change v (e (x ⊗ₜ[R] y)) = _
    have he : e (x ⊗ₜ[R] y) = t x * algebraMap C L (b y) := by
      rw [← heA, ← heS, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [he, map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hvm x) (DFunLike.congr_fun hv (b y))
  · let := φ.toAlgebra
    have : IsLocalization (N.map (algebraMap C L)) LC := hloc
    refine ⟨(N.map (algebraMap C L)).map e.symm.toMonoidHom, ?_⟩
    apply IsLocalization.of_ringEquiv_left (M₁ := N.map (algebraMap C L))
      (M₂ := (N.map (algebraMap C L)).map e.symm.toMonoidHom) e
    · ext x
      simp
    · intro x
      rfl
end RingHom
