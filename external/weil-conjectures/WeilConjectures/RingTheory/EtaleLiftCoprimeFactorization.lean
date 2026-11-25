/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.RingTheory.LiftMonicCoprimeFactorizationEtale

/-!
# Lifting a coprime factorization after an étale extension

Source: Stacks Project, More on Algebra, Tag 07M1, lemma-lift-factorization-easy
(blueprint: lem-weil-pbc-lift-coprime-factorization-etale).
-/

@[expose] public section

universe u

namespace Polynomial

/-- A coprime factorization modulo an arbitrary ideal, whose first factor has unit leading
coefficient, lifts after an étale extension inducing an isomorphism on the quotient.
Source: Stacks Project, Tag 07M1, lemma-lift-factorization-easy
(blueprint: lem-weil-pbc-lift-coprime-factorization-etale).

Proof:
1. Choose a lift `a` of the leading coefficient of `g₀` and localize at `a`. By
   `lem-weil-pbc-lift-invertible-element` (Tag 07LX), this extension is étale, induces
   an isomorphism modulo `I`, and makes `a` a unit `u`.
2. Transport the factors along that quotient isomorphism and replace them by
   `u⁻¹ * g₀` and `u * h₀`. Their product and coprimality are preserved. The first
   factor is monic; since the product is monic the second is monic too. In the zero
   quotient ring every polynomial is monic, so this case is included.
3. Apply `lem-weil-pbc-lift-monic-coprime-factorization-etale` (Tag 0ALH) to obtain
   monic lifted factors after a further étale extension trivial on the quotient.
4. Compose the two étale extensions using `definition-torsion-sheaves--3`.
   The induced quotient map is the composite of the quotient isomorphisms. If `v` is
   the image of `u` in the final ring, multiply the first lifted factor by `v` and
   the second by `v⁻¹`. Their product remains the image of `f`, and their reductions
   are precisely the transported original factors.
-/
theorem exists_etale_lift_coprime_factorization
    {A : Type u} [CommRing A] (I : Ideal A) (f : A[X]) (hf : f.Monic)
    (g₀ h₀ : (A ⧸ I)[X])
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (hleading : IsUnit g₀.leadingCoeff) (hcoprime : IsCoprime g₀ h₀) :
    ∃ (A' : Type u) (_ : CommRing A') (φ : A →+* A'),
      let J : Ideal A' := I.map φ
      let α : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧
        Function.Bijective α ∧
        ∃ g' h' : A'[X], f.map φ = g' * h' ∧
          g'.map (Ideal.Quotient.mk J) = g₀.map α ∧
          h'.map (Ideal.Quotient.mk J) = h₀.map α := by
  classical
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective g₀.leadingCoeff
  let B := Localization.Away a
  let φ₁ : A →+* B := algebraMap A B
  let I₁ : Ideal B := I.map φ₁
  let α₁ : A ⧸ I →+* B ⧸ I₁ := Ideal.quotientMap I₁ φ₁ Ideal.le_comap_map
  have hφ₁ : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ₁)) := by infer_instance
  have hα₁ : Function.Bijective α₁ := by
    let M := Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers a)
    have hM : M ≤ IsUnit.submonoid (A ⧸ I) := by
      rw [show M = Submonoid.powers (Ideal.Quotient.mk I a) by
        simp [M, Algebra.algebraMapSubmonoid_powers]]
      rw [Submonoid.powers_le]
      change IsUnit (Ideal.Quotient.mk I a)
      simpa [ha] using hleading
    exact (IsLocalization.atUnits (S := B ⧸ I₁) (A ⧸ I) M hM).bijective
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := B) a
  let ū : (B ⧸ I₁)ˣ := Units.map (Ideal.Quotient.mk I₁) u
  have hū : (ū : B ⧸ I₁) = α₁ g₀.leadingCoeff := by
    change Ideal.Quotient.mk I₁ (↑u) = α₁ g₀.leadingCoeff
    rw [hu, ← ha]
    rfl
  let G : (B ⧸ I₁)[X] := C (↑(ū⁻¹) : B ⧸ I₁) * g₀.map α₁
  let H : (B ⧸ I₁)[X] := C (↑ū : B ⧸ I₁) * h₀.map α₁
  have hG : G.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [leadingCoeff_map_of_injective hα₁.1, ← hū]
    simp
  have hGH : (f.map φ₁).map (Ideal.Quotient.mk I₁) = G * H := by
    have hmaps : (Ideal.Quotient.mk I₁).comp φ₁ = α₁.comp (Ideal.Quotient.mk I) :=
      (Ideal.quotientMap_comp_mk Ideal.le_comap_map).symm
    rw [map_map, hmaps, ← map_map, hfactor, Polynomial.map_mul]
    dsimp [G, H]
    rw [mul_mul_mul_comm, ← C_mul]
    simp
  have hH : H.Monic := hG.of_mul_monic_left (hGH ▸ (hf.map φ₁).map _)
  have hcop : IsCoprime G H := by
    exact (isCoprime_mul_units_left (ū⁻¹.isUnit.map C) (ū.isUnit.map C) _ _).2
      (hcoprime.map (mapRingHom α₁))
  obtain ⟨D, instD, ψ, hψ, hβ, g, h, hg, hh, hmul, hgred, hhred⟩ :=
    exists_etale_lift_monic_coprime_factorization I₁ (f.map φ₁) (hf.map φ₁)
      G H hG hH hGH hcop
  let φ := ψ.comp φ₁
  let J := I₁.map ψ
  have hJ : J = I.map φ := Ideal.map_map φ₁ ψ
  let β : B ⧸ I₁ →+* D ⧸ J := Ideal.quotientMap J ψ Ideal.le_comap_map
  let α : A ⧸ I →+* D ⧸ J := Ideal.quotientMap J φ
    (hJ.symm ▸ Ideal.le_comap_map)
  have hα : α = β.comp α₁ := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp [α, β, α₁, φ, RingHom.comp_apply]
  have hfinal : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) := by
    have := hφ₁
    have := hψ
    change AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
      (CategoryTheory.CategoryStruct.comp
        (CommRingCat.ofHom φ₁) (CommRingCat.ofHom ψ)))
    rw [AlgebraicGeometry.Spec.map_comp]
    infer_instance
  let v : Dˣ := Units.map ψ u
  have hresult : ∀ hle : I ≤ J.comap φ,
      let α := Ideal.quotientMap J φ hle
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧
      Function.Bijective α ∧ ∃ g' h' : D[X], f.map φ = g' * h' ∧
        g'.map (Ideal.Quotient.mk J) = g₀.map α ∧
        h'.map (Ideal.Quotient.mk J) = h₀.map α := by
    intro hle
    change AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧
      Function.Bijective α ∧ ∃ g' h' : D[X], f.map φ = g' * h' ∧
        g'.map (Ideal.Quotient.mk J) = g₀.map α ∧
        h'.map (Ideal.Quotient.mk J) = h₀.map α
    refine ⟨hfinal, ?_, C (↑v : D) * g, C (↑(v⁻¹) : D) * h, ?_, ?_, ?_⟩
    · rw [hα]
      exact hβ.comp hα₁
    · rw [map_map] at hmul
      change f.map (ψ.comp φ₁) = _
      rw [hmul, mul_mul_mul_comm, ← C_mul]
      simp
    · change g.map (Ideal.Quotient.mk J) = G.map β at hgred
      rw [Polynomial.map_mul, map_C, hgred]
      dsimp only [G]
      rw [Polynomial.map_mul, map_C, map_map, ← hα]
      have hv : Ideal.Quotient.mk J (↑v) = β (↑ū) := by
        simp [v, ū, β]
      rw [hv, ← mul_assoc, ← C_mul, ← map_mul]
      simp
    · change h.map (Ideal.Quotient.mk J) = H.map β at hhred
      rw [Polynomial.map_mul, map_C, hhred]
      dsimp only [H]
      rw [Polynomial.map_mul, map_C, map_map, ← hα]
      have hv : Ideal.Quotient.mk J (↑(v⁻¹)) = β (↑(ū⁻¹)) := by
        simp [v, ū, β]
      rw [hv, ← mul_assoc, ← C_mul, ← map_mul]
      simp
  refine ⟨D, instD, φ, ?_⟩
  rw [hJ] at hresult
  exact hresult Ideal.le_comap_map

end Polynomial
