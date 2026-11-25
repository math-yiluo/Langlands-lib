/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import WeilConjectures.RingTheory.EtaleSectionNeighbourhoodRefinement

@[expose] public section

universe u

namespace Polynomial

/-! Auxiliary decomposition of the lifting theorem. -/

/-- The universal étale construction and the first coefficient reduction in Tag 0ALH;
the remaining coefficient reduction is isolated below for a separate proof.
Proof: follow the universal coprime factorization ring, the quotient section, and the
étale idempotent localization from the six-step proof of Tag 0ALH.
(blueprint: lem-weil-pbc-lift-monic-coprime-factorization-etale-core) -/
theorem exists_etale_lift_monic_coprime_factorization_core
    {A : Type u} [CommRing A] (I : Ideal A) (f : A[X]) (hf : f.Monic)
    (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (hcoprime : IsCoprime g₀ h₀) :
    ∃ (A' : Type u) (_ : CommRing A') (φ : A →+* A'),
      let J : Ideal A' := I.map φ
      let α : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧
        Function.Bijective α ∧
        ∃ g' h' : A'[X], g'.Monic ∧ h'.Monic ∧ f.map φ = g' * h' ∧
          g'.map (Ideal.Quotient.mk J) = g₀.map α := by
  classical
  let P : CategoryTheory.ObjectProperty (CategoryTheory.Under (CommRingCat.of A)) := fun C ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
        Ideal.le_comap_map)
  let M : CategoryTheory.Under (CommRingCat.of A) := CategoryTheory.Under.mk
    (CategoryTheory.CategoryStruct.id (CommRingCat.of A))
  have hM : P M := by
    constructor
    · apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.Etale)).mpr
      exact RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A A)
    · have hI : I.map (RingHom.id A) = I := Ideal.map_id I
      have he : Ideal.quotientMap (I.map (RingHom.id A)) (RingHom.id A)
          Ideal.le_comap_map = (Ideal.quotEquivOfEq hI).symm.toRingHom := by
        apply RingHom.ext
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        apply (Ideal.quotEquivOfEq hI).injective
        simp only [Ideal.quotientMap_mk, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
          Ideal.quotEquivOfEq_mk]
        exact ((Ideal.quotEquivOfEq hI).apply_symm_apply _).symm
      change Function.Bijective
        (Ideal.quotientMap (I.map (RingHom.id A)) (RingHom.id A) Ideal.le_comap_map)
      rw [he]
      exact (Ideal.quotEquivOfEq hI).symm.bijective
  let i : P.FullSubcategory := ⟨M, hM⟩
  cases subsingleton_or_nontrivial (A ⧸ I) with
  | inl htriv =>
    let := htriv
    refine ⟨A, inferInstance, RingHom.id A, hM.1, hM.2, f, 1, hf, monic_one, ?_, ?_⟩
    · simp
    · let : Subsingleton (A ⧸ I.map (RingHom.id A)) :=
        (Ideal.quotEquivOfEq (Ideal.map_id I)).injective.subsingleton
      apply Subsingleton.elim
  | inr hnontriv =>
    let := hnontriv
    let m := g₀.natDegree
    let k := h₀.natDegree
    have hn : f.natDegree = m + k := by
      rw [← hf.natDegree_map (Ideal.Quotient.mk I), hfactor, hg₀.natDegree_mul hh₀]
    let p : MonicDegreeEq A f.natDegree := MonicDegreeEq.mk f hf rfl
    let B := UniversalCoprimeFactorizationRing m k hn p
    let G := UniversalCoprimeFactorizationRing.factor₁ m k hn p
    let H := UniversalCoprimeFactorizationRing.factor₂ m k hn p
    let E := UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I) m k hn p
    let factors : { q : MonicDegreeEq (A ⧸ I) m × MonicDegreeEq (A ⧸ I) k //
        q.1.1 * q.2.1 = p.1.map (algebraMap A (A ⧸ I)) ∧ IsCoprime q.1.1 q.2.1 } :=
      ⟨⟨MonicDegreeEq.mk g₀ hg₀ rfl, MonicDegreeEq.mk h₀ hh₀ rfl⟩,
        hfactor.symm, hcoprime⟩
    let s : B →ₐ[A] A ⧸ I := E.symm factors
    have hsG : G.1.map s.toRingHom = g₀ := by
      have he := congrArg (fun q ↦ q.1.1.1) (E.apply_symm_apply factors)
      change (UniversalFactorizationRing.factor₁ m k hn p).1.map
        (s.comp (IsScalarTower.toAlgHom A (UniversalFactorizationRing m k hn p) B))
          = g₀ at he
      change (UniversalFactorizationRing.factor₁ m k hn p).1.map
        (s.toRingHom.comp (algebraMap (UniversalFactorizationRing m k hn p) B)) = g₀ at he
      simpa only [G, UniversalCoprimeFactorizationRing.factor₁, MonicDegreeEq.map_coe,
        Polynomial.map_map] using he
    have hs : (s.toRingHom.comp (algebraMap A B)).comp (RingHom.id A) =
        Ideal.Quotient.mk I := by
      ext a
      exact s.commutes a
    obtain ⟨N, j, t, r, ht, hr, hrt⟩ :=
      RingTheory.etale_section_neighbourhood_refinement A I i B (algebraMap A B)
        (by
          change @Algebra.Etale A B _ _ (algebraMap A B).toAlgebra
          rw [toAlgebra_algebraMap]
          infer_instance) s.toRingHom hs
    let A' := N.obj.right
    let φ : A →+* A' := N.obj.hom.hom
    let J := I.map φ
    let α := Ideal.quotientMap J φ Ideal.le_comap_map
    have hrφ : r.comp φ = Ideal.Quotient.mk I := hr
    have hJ : J ≤ RingHom.ker r := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change r (φ a) = 0
      rw [← RingHom.comp_apply, hrφ]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    let β : A' ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J r hJ
    have hβα : β.comp α = RingHom.id (A ⧸ I) := by
      apply RingHom.ext
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change r (φ a) = Ideal.Quotient.mk I a
      exact DFunLike.congr_fun hrφ a
    have hβinj : Function.Injective β := by
      intro x y hxy
      obtain ⟨x, rfl⟩ := N.property.2.2 x
      obtain ⟨y, rfl⟩ := N.property.2.2 y
      change β (α x) = β (α y) at hxy
      have hx : β (α x) = x := DFunLike.congr_fun hβα x
      have hy : β (α y) = y := DFunLike.congr_fun hβα y
      exact congrArg α (by simpa only [hx, hy] using hxy)
    refine ⟨A', inferInstance, φ, N.property.1, N.property.2,
      G.1.map t, H.1.map t, G.monic.map t, H.monic.map t, ?_, ?_⟩
    · rw [← Polynomial.map_mul, UniversalCoprimeFactorizationRing.factor₁_mul_factor₂,
        MonicDegreeEq.map_coe, Polynomial.map_map]
      change f.map φ = f.map (t.comp (algebraMap A B))
      congr 1
      symm
      apply ht.trans
      apply RingHom.ext
      intro a
      have hj := congrArg (fun z ↦ z.hom a) j.hom.w
      exact hj
    · apply Polynomial.map_injective β hβinj
      rw [Polynomial.map_map, Polynomial.map_map, Polynomial.map_map, hβα,
        Polynomial.map_id]
      change G.1.map (r.comp t) = g₀
      rw [hrt]
      exact hsG

/-- The second factor reduction follows from the product identity and the first factor
reduction, coefficientwise in the quotient polynomial ring.
Proof: map the product identity to the quotient, rewrite the first factor by the
given reduction, and cancel the monic first factor using the prescribed factorization.
(blueprint: lem-weil-pbc-lift-monic-coprime-factorization-etale-h-reduction) -/
theorem lift_monic_coprime_factorization_h_reduction
    {A : Type u} [CommRing A] (I : Ideal A) (f : A[X])
    (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfactor₀ : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (A' : Type u) [CommRing A'] (φ : A →+* A')
    (g' h' : A'[X]) (hfactor : f.map φ = g' * h')
    (hgred : g'.map (Ideal.Quotient.mk (I.map φ)) =
      g₀.map (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    h'.map (Ideal.Quotient.mk (I.map φ)) =
      h₀.map (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) := by
  have _ := hh₀
  let q := Ideal.Quotient.mk (I.map φ)
  let α := Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map
  apply (hg₀.map α).isRegular.left
  calc
    g₀.map α * h'.map q = (g' * h').map q := by rw [Polynomial.map_mul, hgred]
    _ = (f.map φ).map q := congrArg (map q) hfactor.symm
    _ = (f.map (Ideal.Quotient.mk I)).map α := by
      rw [map_map, map_map, Ideal.quotientMap_comp_mk]
    _ = g₀.map α * h₀.map α := by rw [hfactor₀, Polynomial.map_mul]

end Polynomial
