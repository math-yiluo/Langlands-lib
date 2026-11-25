/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Polynomial lifts annihilating a conormal complement

Source: Stacks Project, Algebra, Lemma 04EB, the polynomial lift correction argument.
(blueprint: lem-weil-pbc-conormal-complement-polynomial-lift).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Algebra

/-- Correct an arbitrary polynomial lift by the negative conormal obstruction. -/
private theorem polynomialLift_exists
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type u} (G : Generators R S ι) (K : Ideal G.Ring)
    (hK : K ≤ G.toExtension.ker)
    (hsurj : ∀ w : G.toExtension.CotangentSpace,
      ∃ x : G.toExtension.ker, x.val ∈ K ∧
        G.toExtension.cotangentComplex (Extension.Cotangent.mk x) = w)
    (hinj : ∀ x : G.toExtension.ker, x.val ∈ K →
      G.toExtension.cotangentComplex (Extension.Cotangent.mk x) = 0 →
        x.val ∈ G.toExtension.ker ^ 2)
    (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A) (hI : I ^ 2 = ⊥)
    (a : S →ₐ[R] A ⧸ I) :
    ∃ β : G.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp β = a.comp (IsScalarTower.toAlgHom R G.Ring S) ∧
        ∀ x : G.Ring, x ∈ K → β x = 0 := by
  classical
  let z : ι → A := fun i =>
    (Ideal.Quotient.mkₐ_surjective R I (a (G.val i))).choose
  have hz (i : ι) : Ideal.Quotient.mkₐ R I (z i) = a (G.val i) :=
    (Ideal.Quotient.mkₐ_surjective R I (a (G.val i))).choose_spec
  let β : G.Ring →ₐ[R] A := MvPolynomial.aeval z
  have hβ : (Ideal.Quotient.mkₐ R I).comp β =
      a.comp (IsScalarTower.toAlgHom R G.Ring S) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [β, Generators.algebraMap_apply] using hz i
  let := β.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
  have hJI : G.toExtension.ker ≤ I.comap β.toRingHom := by
    intro x hx
    change G.Ring at x
    change β x ∈ I
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ R I (β x) = 0
    have hx0 : algebraMap G.Ring S x = 0 := hx
    exact (AlgHom.congr_fun hβ x).trans (by
      change a (algebraMap G.Ring S x) = 0
      rw [hx0, map_zero])
  have hJsq (x : G.Ring) (hx : x ∈ G.toExtension.ker ^ 2) : β x = 0 := by
    have h : G.toExtension.ker ^ 2 ≤ (I ^ 2).comap β.toRingHom :=
      (pow_le_pow_left' hJI 2).trans (Ideal.le_comap_pow β.toRingHom 2)
    have hm := h hx
    rw [hI] at hm
    exact hm
  let t : K →ₗ[G.Ring] G.toExtension.CotangentSpace :=
    (KaehlerDifferential.kerToTensor R G.Ring S).comp (Submodule.inclusion hK)
  have ht : Function.Surjective t := by
    intro w
    obtain ⟨x, hx, hdx⟩ := hsurj w
    exact ⟨⟨x.val, hx⟩, hdx⟩
  let b : K →ₗ[G.Ring] I :=
    { toFun := fun x => ⟨β x, hJI (hK x.property)⟩
      map_add' := fun x y => Subtype.ext (map_add β (x : G.Ring) (y : G.Ring))
      map_smul' := fun r x => Subtype.ext (map_mul β r (x : G.Ring)) }
  have htb : LinearMap.ker t ≤ LinearMap.ker b := by
    intro x hx
    apply Subtype.ext
    exact hJsq x (hinj ⟨x.val, hK x.property⟩ x.property hx)
  let l : G.toExtension.CotangentSpace →ₗ[G.Ring] I :=
    (t.ker.liftQ b htb).comp (t.quotKerEquivOfSurjective ht).symm.toLinearMap
  have hl (x : K) : l (t x) = b x := by
    simp [l, LinearMap.quotKerEquivOfSurjective_symm_apply]
  let j : KaehlerDifferential R G.Ring →ₗ[G.Ring] G.toExtension.CotangentSpace :=
    TensorProduct.mk G.Ring S (KaehlerDifferential R G.Ring) 1
  let D : Derivation R G.Ring I :=
    ((-l).comp j).compDer (KaehlerDifferential.D R G.Ring)
  let β' : G.Ring →ₐ[R] A := liftOfDerivationToSquareZero I hI D
  refine ⟨β', ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    change Ideal.Quotient.mk I (β' x) = a (algebraMap G.Ring S x)
    rw [liftOfDerivationToSquareZero_mk_apply]
    exact AlgHom.congr_fun hβ x
  · intro x hx
    change (D x : A) + β x = 0
    have hDx : D x = -b ⟨x, hx⟩ := by
      change -l (t ⟨x, hx⟩) = -b ⟨x, hx⟩
      rw [hl]
    rw [hDx]
    exact neg_add_cancel (β x)

/-- The difference derivation is zero because the differentials of `K` span. -/
private theorem polynomialLift_unique
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type u} (G : Generators R S ι) (K : Ideal G.Ring)
    (hsurj : ∀ w : G.toExtension.CotangentSpace,
      ∃ x : G.toExtension.ker, x.val ∈ K ∧
        G.toExtension.cotangentComplex (Extension.Cotangent.mk x) = w)
    (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A) (hI : I ^ 2 = ⊥)
    (a : S →ₐ[R] A ⧸ I) (β₁ β₂ : G.Ring →ₐ[R] A)
    (h₁ : (Ideal.Quotient.mkₐ R I).comp β₁ =
      a.comp (IsScalarTower.toAlgHom R G.Ring S))
    (h₂ : (Ideal.Quotient.mkₐ R I).comp β₂ =
      a.comp (IsScalarTower.toAlgHom R G.Ring S))
    (hz₁ : ∀ x : G.Ring, x ∈ K → β₁ x = 0)
    (hz₂ : ∀ x : G.Ring, x ∈ K → β₂ x = 0) : β₁ = β₂ := by
  let := β₂.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' β₂.comp_algebraMap.symm
  have he : (Ideal.Quotient.mkₐ R I).comp β₁ =
      IsScalarTower.toAlgHom R G.Ring (A ⧸ I) := h₁.trans h₂.symm
  let D := derivationToSquareZeroOfLift I hI β₁ he
  have htors : Module.IsTorsionBySet A I I := by
    intro i r
    apply Subtype.ext
    change r.val * i.val = 0
    apply Ideal.mem_bot.mp
    rw [← hI, pow_two]
    exact Ideal.mul_mem_mul r.property i.property
  let := htors.module
  let := Module.compHom I a.toRingHom
  have hscalar (p : G.Ring) (i : I) : algebraMap G.Ring S p • i = p • i := by
    change a (algebraMap G.Ring S p) • i = β₂ p • i
    have hp : a (algebraMap G.Ring S p) = Ideal.Quotient.mk I (β₂ p) :=
      (AlgHom.congr_fun h₂ p).symm
    rw [hp]
    rfl
  have := IsScalarTower.of_algebraMap_smul hscalar
  let F : S ⊗[G.Ring] KaehlerDifferential R G.Ring →ₗ[S] I :=
    D.liftKaehlerDifferential.liftBaseChange S
  have hFD (x : G.Ring) :
      F (TensorProduct.tmul G.Ring (1 : S) (KaehlerDifferential.D R G.Ring x)) = D x := by
    simp [F]
  have hF (w : G.toExtension.CotangentSpace) : F w = 0 := by
    obtain ⟨x, hx, hdx⟩ := hsurj w
    rw [← hdx]
    change F (TensorProduct.tmul G.Ring (1 : S)
      (KaehlerDifferential.D R G.Ring x.val)) = 0
    rw [hFD]
    apply Subtype.ext
    change β₁ x.val - β₂ x.val = 0
    rw [hz₁ x.val hx, hz₂ x.val hx, sub_self]
  apply AlgHom.ext
  intro x
  have hDx : D x = 0 := (hFD x).symm.trans (hF _)
  exact sub_eq_zero.mp (congrArg Subtype.val hDx)

/-- A polynomial lift can be uniquely corrected to annihilate an ideal whose conormal
map is an isomorphism onto the base changed differential module.
Source: Stacks Project, Algebra, Lemma 04EB, from the choice of `β` to the last sentence.
(blueprint: lem-weil-pbc-conormal-complement-polynomial-lift).

Proof: Lift the images of the polynomial variables through the surjection `A → A/I`.
This gives an algebra map `β` with the prescribed reduction. Its restriction to `K`
takes values in `I` and vanishes on `J²`, since `β(J) ⊆ I` and `I² = 0`.
The restriction descends to `K/(K ∩ J²) → I`. The two differential hypotheses
identify `K/(K ∩ J²)` with `S ⊗[P] Ω[P/R]` as `P`-modules.
Compose the negative obstruction map with this inverse and the universal differential
to obtain an `R`-derivation `D : P → I`. Then `β + D` is an algebra map: the Leibniz
identity gives multiplicativity because products of two elements of `I` vanish.
It has the same reduction as `β` and vanishes on `K` by the definition of `D`.
For uniqueness, the difference of any two lifts is an `R`-derivation into `I`.
The square-zero hypothesis gives `I` an `A/I`-module structure, hence an `S`-module
structure through `a`, compatible with its `P`-action. The difference derivation thus
factors through `S ⊗[P] Ω[P/R]` and vanishes on the image of `K`.
Surjectivity of that image forces the derivation to be zero, hence the lifts agree. -/
theorem conormalComplement_polynomial_lift
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type u} (G : Generators R S ι) (K : Ideal G.Ring)
    (hK : K ≤ G.toExtension.ker)
    (hsurj : ∀ w : G.toExtension.CotangentSpace,
      ∃ x : G.toExtension.ker, x.val ∈ K ∧
        G.toExtension.cotangentComplex (Extension.Cotangent.mk x) = w)
    (hinj : ∀ x : G.toExtension.ker, x.val ∈ K →
      G.toExtension.cotangentComplex (Extension.Cotangent.mk x) = 0 →
        x.val ∈ G.toExtension.ker ^ 2)
    (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A) (hI : I ^ 2 = ⊥)
    (a : S →ₐ[R] A ⧸ I) :
    ∃! β : G.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp β = a.comp (IsScalarTower.toAlgHom R G.Ring S) ∧
        ∀ x : G.Ring, x ∈ K → β x = 0 := by
  obtain ⟨β, hβ⟩ := polynomialLift_exists R S G K hK hsurj hinj A I hI a
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  exact polynomialLift_unique R S G K hsurj A I hI a γ β hγ.1 hβ.1 hγ.2 hβ.2

end Algebra
