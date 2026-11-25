/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.DesingularizeAnnihilatorConstruction
import WeilConjectures.RingTheory.SingularIdealsOfAnnihilatorBound

/-!
# Desingularization along a strictly standard element

Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07CT
(blueprint: lem-weil-pbc-popescu-desingularize-strictly-standard).
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- Desingularization along a strictly standard element, Stacks Project, Lemma Tag 07CT.
Compatibility modulo the fourth power is tested on representatives: if the image of `a`
under the quotient map is represented by `d`, their images in the quotient of `Λ` agree.
Every quotient class has a representative, so this is exactly the commuting triangle.

Proof: (1) `D` is Noetherian by finite type over `R`
(`lem-weil-pbc-finite-type-algebra-noetherian`). Form `A' = A ⊗[R] D` and the map to `Λ`.
Finite presentation is preserved by base change
(`lem-weil-pbc-finite-presentation-base-change-composition`).
(2) The element remains strictly standard by `lem-weil-pbc-strictly-standard-base-change`.
The given quotient map induces the section for `A'` modulo the fourth power; the
annihilator condition on `Λ` is unchanged.
(3) Apply `lem-weil-pbc-popescu-desingularize` over `D` to obtain `B`, with
`aB ≤ H_{B/D}`, where `a` annihilates `Ann_D(π²)/Ann_D(π)`. Composition gives finite
presentation over `R` and the two compatible factorization maps.
(4) At an `R`-flat prime of `D`, the quotient of annihilators vanishes by
`lem-weil-pbc-annihilator-element-flat-base-change`. It is finite since `D` is Noetherian;
`lem-weil-pbc-finite-module-support-annihilator` shows `a` is not contained in that prime.
(5) A smooth prime is flat by `lem-weil-pbc-smooth-ring-map-flat`, localization flatness
(`lem-weil-pbc-localization-flat`), and `lem-weil-pbc-flat-ring-map-comp`.
(6) Thus primes of `B` over the smooth locus of `D/R` are smooth for `B/D`.
The zero-locus/radical criterion (`lem-weil-pbc-zero-locus-eq-iff-radical-eq`) gives
`H_{D/R}B ≤ H_{B/D}`.
(7) Smooth base change and composition (`lem-weil-pbc-smooth-ring-map-base-change-composition`)
make those primes smooth for `B/R`; the same radical criterion gives the second inclusion.
(blueprint: lem-weil-pbc-popescu-desingularize-strictly-standard). -/
theorem exists_desingularization_strictlyStandard
    (R : Type u) (Λ : Type v) (A : Type w) (D : Type z)
    [CommRing R] [CommRing Λ] [CommRing A] [CommRing D]
    [Algebra R Λ] [Algebra R A] [Algebra R D] [IsNoetherianRing R]
    [FinitePresentation R A] [FinitePresentation R D]
    (π : R) (α : A →ₐ[R] Λ) (δ : D →ₐ[R] Λ)
    (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (hΛ : ∀ l : Λ, l * algebraMap R Λ π = 0 ↔
      l * (algebraMap R Λ π) ^ 2 = 0)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hquot : ∃ φ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (D ⧸ Ideal.span {(algebraMap R D π) ^ 4}),
      ∀ (a : A) (d : D),
        φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ d →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (δ d)) :
    ∃ (B : Type (max u v w z)) (_ : CommRing B) (_ : Algebra R B),
      FinitePresentation R B ∧
      ∃ (β : B →ₐ[R] Λ) (aB : A →ₐ[R] B) (dB : D →ₐ[R] B),
        β.comp aB = α ∧ β.comp dB = δ ∧
        Ideal.map dB.toRingHom (singularIdeal R D) ≤
          @singularIdeal D B _ _ dB.toRingHom.toAlgebra ∧
        Ideal.map dB.toRingHom (singularIdeal R D) ≤ singularIdeal R B := by
  obtain ⟨B, instB, instRB, β, aB, dB, hfp, ha, hd, hbound⟩ :=
    exists_desingularization_annihilator_bound R Λ A D π α δ hΛ hstandard hquot
  let : CommRing B := instB
  let : Algebra R B := instRB
  let : Algebra D B := dB.toRingHom.toAlgebra
  have : IsScalarTower R D B := IsScalarTower.of_algHom dB
  have : FinitePresentation D B := hfp
  have : FinitePresentation R B := FinitePresentation.trans R D B
  obtain ⟨hrelative, habsolute⟩ :=
    singularIdeals_of_annihilator_bound R D B dB hfp π hR hbound
  exact ⟨B, instB, instRB, inferInstance, β, aB, dB, ha, hd, hrelative, habsolute⟩

end Algebra
