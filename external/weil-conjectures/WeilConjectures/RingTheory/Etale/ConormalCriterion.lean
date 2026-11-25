/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Etale ring maps and the conormal criterion

Source: literature/stacks-project/algebra.tex, Definition Tag 00U1 and Lemma Tag 00U9
(blueprint: `lem-weil-pbc-etale-ring-map-conormal-criterion`)
-/

@[expose] public section

universe u

namespace Algebra

/-- The derivative formula descends to an S-linear map on J/J², and etaleness is
 equivalent to its bijectivity. The S-action is transported along P/J ≃ S.

Source: literature/stacks-project/algebra.tex, Definition Tag 00U1, text before Tag 00S1,
Lemma Tag 00U9; morphisms.tex, Tag 02GJ
(blueprint: `lem-weil-pbc-etale-ring-map-conormal-criterion`). -/
theorem etale_specMap_iff_bijective_conormalMap
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S)
    (hα : Function.Surjective α)
    (hfg : (RingHom.ker α.toRingHom).FG) :
    let J := RingHom.ker α.toRingHom
    let e := RingHom.quotientKerEquivOfSurjective hα
    letI : Module S J.Cotangent := Module.compHom J.Cotangent e.symm.toRingHom
    ∃ d : J.Cotangent →ₗ[S] (Fin n → S),
      (∀ (g : J) (i : Fin n),
        d (Ideal.toCotangent J g) i = α (MvPolynomial.pderiv i g.1)) ∧
      (AlgebraicGeometry.Etale
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔
        Function.Bijective d) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    let P := MvPolynomial (Fin n) R
    let : Algebra P S := α.toAlgebra
    let : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq' α.comp_algebraMap.symm
    let J := RingHom.ker α.toRingHom
    let e := RingHom.quotientKerEquivOfSurjective hα
    let : Module S J.Cotangent := Module.compHom J.Cotangent e.symm.toRingHom
    let : IsScalarTower P S J.Cotangent := ⟨by
      intro p s x
      change (e.symm (α p * s)) • x = p • (e.symm s • x)
      rw [map_mul]
      have hp : e.symm (α p) = Ideal.Quotient.mk J p :=
        RingHom.quotientKerEquivOfSurjective_symm_apply hα p
      rw [hp]
      exact smul_assoc p (e.symm s) x⟩
    let c := KaehlerDifferential.kerCotangentToTensor R P S
    let cS := c.extendScalarsOfSurjective hα
    let b := (KaehlerDifferential.mvPolynomialBasis R (Fin n)).baseChange S
    let t : (TensorProduct P S (KaehlerDifferential R P)) ≃ₗ[S] (Fin n → S) :=
      b.repr.trans (Finsupp.linearEquivFunOnFinite S S (Fin n))
    let d := t.toLinearMap.comp cS
    refine ⟨d, ?_, ?_⟩
    · intro g i
      change t (c (Ideal.toCotangent J g)) i = _
      change t (TensorProduct.tmul P 1 (KaehlerDifferential.D R P g.1)) i = _
      change b.repr (TensorProduct.tmul P 1 (KaehlerDifferential.D R P g.1)) i = _
      rw [Module.Basis.baseChange_repr_tmul,
        KaehlerDifferential.mvPolynomialBasis_repr_apply]
      simp only [Algebra.smul_def, mul_one]
      rfl
    · have hfin : FinitePresentation R S := ⟨n, α, hα, hfg⟩
      rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
      change (algebraMap R S).Etale ↔ Function.Bijective d
      rw [RingHom.etale_algebraMap, etale_iff, formallyEtale_iff]
      have hi := FormallySmooth.kerCotangentToTensor_injective_iff (R := R) hα
      have he := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R P S hα
      have hw := KaehlerDifferential.mapBaseChange_surjective R P S hα
      have hs : Function.Surjective c ↔ Subsingleton (KaehlerDifferential R S) := by
        constructor
        · intro hc
          refine ⟨fun x y ↦ ?_⟩
          have hz : ∀ x : KaehlerDifferential R S, x = 0 := by
            intro x
            obtain ⟨z, rfl⟩ := hw x
            obtain ⟨a, rfl⟩ := hc z
            exact he.apply_apply_eq_zero a
          rw [hz x, hz y]
        · intro h
          let := h
          intro x
          exact (he x).mp (Subsingleton.elim _ _)
      have hb : Function.Bijective d ↔ Function.Bijective c := by
        constructor
        · intro hd
          refine ⟨fun x y h ↦ hd.1 (congrArg t h), fun x ↦ ?_⟩
          obtain ⟨a, ha⟩ := hd.2 (t x)
          exact ⟨a, t.injective ha⟩
        · intro hc
          exact t.bijective.comp hc
      rw [hb]
      change (Subsingleton (KaehlerDifferential R S) ∧
        Subsingleton (H1Cotangent R S)) ∧ FinitePresentation R S ↔
        Function.Injective c ∧ Function.Surjective c
      rw [hi, hs]
      exact ⟨fun h ↦ ⟨h.1.2, h.1.1⟩, fun h ↦ ⟨⟨h.2, h.1⟩, hfin⟩⟩

end Algebra
