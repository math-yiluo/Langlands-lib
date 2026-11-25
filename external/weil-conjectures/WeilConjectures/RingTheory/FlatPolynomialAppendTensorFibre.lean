/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.PolynomialAppendClosedFibreParameters
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.FlatOverRegular

/-!
# Flatness of the polynomial-append closed-fibre map

Source: Stacks Project, Smoothing Ring Maps, Tag 07FH, lemma-solution-modulo,
property (1); Algebra, Tags 00OP and 07DY.
-/

@[expose] public section

open scoped TensorProduct
set_option autoImplicit false
universe u v
namespace Algebra

/-- The closed fibre of adjoining polynomial coordinates is flat on a target where
those coordinates form a regular sequence on the original closed fibre.
Source: Stacks Project, Tag 07FH, lemma-solution-modulo, property (1);
Algebra, Tags 00OP and 07DY.
(blueprint: lem-weil-pbc-flat-polynomial-append-tensor-fibre).

Proof: Write A₀ = k[X_j]_{p₀}, A₁ = k[X_j,Y_i]_{p₁}, and L = Λ_q.
Reduction by p₀ identifies A₁/m₀A₁ with κ(p₀)[Y_i] localized at its
origin ideal. Modulo q every new coordinate is zero. Polynomial evaluation therefore gives
p₁ = p₀P₁ + (Y_i): the constant-in-Y term is in the kernel exactly when its
coefficient lies in p₀. Inverting P₀ \ p₀ and reducing modulo p₀ leaves
κ(p₀)[Y_i] with contracted prime precisely (Y_i).
Localization and quotient universal properties give the canonical comparison,
carrying the variable images to the standard origin parameters. By Tag 00OP
the source fibre is regular local of dimension e, with these e generators of
its maximal ideal. Let S = L/p₀L. The induced local map from the source fibre
to S takes the origin parameters to the given regular sequence. The final
quotient is nonzero by regularity; thus S is a Noetherian local ring. Tag 07DY
makes this map flat. The quotient-tensor equivalence identifies
(A₁/m₀A₁) ⊗[A₁] L with S as modules over A₁/m₀A₁, since the localized
first-coordinate map is the composite of α and β. Transport the flatness
along that equivalence. For e = 0 the source fibre is κ(p₀) and flatness is
flatness over a field. No initial flatness, generation, or regular-local
hypothesis on S is used. The equality hc fixes the canonical inclusion map;
proof irrelevance makes its choice immaterial. -/
theorem flat_tensor_fibre_polynomial_append_of_regular_sequence
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (q : Ideal Λ) [q.IsPrime]
    (t e : ℕ) (xs : Fin t → Λ) (zs : Fin e → Λ)
    (hzq : ∀ i, zs i ∈ q)
    (hseq : RingTheory.Sequence.IsRegular (Localization.AtPrime q ⧸
      (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp
          (MvPolynomial.aeval (R := k) xs).toRingHom))
      (List.ofFn (fun i : Fin e ↦ Ideal.Quotient.mk
        ((q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
          ((algebraMap Λ (Localization.AtPrime q)).comp
            (MvPolynomial.aeval (R := k) xs).toRingHom))
        (algebraMap Λ (Localization.AtPrime q) (zs i))))) :
    let φ₀ : MvPolynomial (Fin t) k →ₐ[k] Λ := MvPolynomial.aeval xs
    let φ₁ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
      MvPolynomial.aeval (Fin.addCases xs zs)
    let ι : MvPolynomial (Fin t) k →+* MvPolynomial (Fin (t + e)) k :=
      (MvPolynomial.rename (Fin.castAdd e)).toRingHom
    let p₀ := q.comap φ₀.toRingHom
    let p₁ := q.comap φ₁.toRingHom
    ∀ hc : p₀ = p₁.comap ι,
      let α := Localization.localRingHom p₀ p₁ ι hc
      let β := Localization.localRingHom p₁ q φ₁.toRingHom rfl
      letI : Algebra (Localization.AtPrime p₀) (Localization.AtPrime p₁) := α.toAlgebra
      letI : Algebra (Localization.AtPrime p₁) (Localization.AtPrime q) := β.toAlgebra
      let J := (IsLocalRing.maximalIdeal (Localization.AtPrime p₀)).map α
      Module.Flat (Localization.AtPrime p₁ ⧸ J)
        ((Localization.AtPrime p₁ ⧸ J) ⊗[Localization.AtPrime p₁]
          Localization.AtPrime q) := by
  classical
  dsimp only
  intro hc
  let φ₀ : MvPolynomial (Fin t) k →ₐ[k] Λ := MvPolynomial.aeval xs
  let φ₁ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
    MvPolynomial.aeval (Fin.addCases xs zs)
  let ι : MvPolynomial (Fin t) k →+* MvPolynomial (Fin (t + e)) k :=
    (MvPolynomial.rename (Fin.castAdd e)).toRingHom
  let p₀ := q.comap φ₀.toRingHom
  let p₁ := q.comap φ₁.toRingHom
  let A₀ := Localization.AtPrime p₀
  let A₁ := Localization.AtPrime p₁
  let L := Localization.AtPrime q
  let α := Localization.localRingHom p₀ p₁ ι hc
  let β := Localization.localRingHom p₁ q φ₁.toRingHom rfl
  let : Algebra A₀ A₁ := α.toAlgebra
  let : Algebra A₁ L := β.toAlgebra
  let J := (IsLocalRing.maximalIdeal A₀).map α
  let C := A₁ ⧸ J
  let pars := List.ofFn (fun i : Fin e ↦ Ideal.Quotient.mk J
    (algebraMap (MvPolynomial (Fin (t + e)) k) A₁
      (MvPolynomial.X (Fin.natAdd t i))))
  have hz : ∀ i : Fin e, MvPolynomial.X (Fin.natAdd t i) ∈ p₁ := by
    intro i
    change φ₁ (MvPolynomial.X (Fin.natAdd t i)) ∈ q
    simpa [φ₁] using hzq i
  obtain ⟨hC, hdim, hgen⟩ :=
    polynomial_append_closed_fibre_parameters k t e p₀ p₁ hc hz
  let : IsRegularLocalRing C := hC
  let K := J.map (algebraMap A₁ L)
  let S := L ⧸ K
  have hK : K = p₀.map ((algebraMap Λ L).comp φ₀.toRingHom) := by
    dsimp only [K, J]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro f
    change β (α (algebraMap _ A₀ f)) = algebraMap Λ L (φ₀ f)
    dsimp only [α, β]
    rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map]
    congr 1
    change φ₁ (MvPolynomial.rename (Fin.castAdd e) f) = φ₀ f
    simp only [φ₁, φ₀, MvPolynomial.aeval_rename]
    rw [show ((fun i ↦ Fin.addCases xs zs i) ∘ Fin.castAdd e) = xs from
      by funext i; simp]
  have hKmem : K ≤ IsLocalRing.maximalIdeal L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact map_nonunit β a (by
      apply (Ideal.map_le_iff_le_comap.mpr ?_ : J ≤ IsLocalRing.maximalIdeal A₁) ha
      intro b hb
      exact map_nonunit α b hb)
  have hKne : K ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal L).ne_top hKmem
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hKne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk K) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let ψ : C →+* S := algebraMap C S
  let : IsLocalHom ψ := by
    constructor
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply (Ideal.Quotient.mk J).isUnit_map
    apply isUnit_of_map_unit β b
    exact isUnit_of_map_unit (Ideal.Quotient.mk K) (β b) ha
  have hreg : RingTheory.Sequence.IsRegular S (pars.map ψ) := by
    have hs : RingTheory.Sequence.IsRegular S
        (List.ofFn (fun i : Fin e ↦ Ideal.Quotient.mk K
          (algebraMap Λ L (zs i)))) := by
      change RingTheory.Sequence.IsRegular (L ⧸ K) _
      rw [hK]
      exact hseq
    convert hs using 1
    rw [List.map_ofFn]
    congr 1
    funext i
    change Ideal.Quotient.mk K
      (β (algebraMap (MvPolynomial (Fin (t + e)) k) A₁
        (MvPolynomial.X (Fin.natAdd t i)))) = _
    dsimp only [β]
    rw [Localization.localRingHom_to_map]
    change Ideal.Quotient.mk K (algebraMap Λ L
      (φ₁ (MvPolynomial.X (Fin.natAdd t i)))) = _
    simp [φ₁]
  have hflat : Module.Flat C S :=
    RingHom.flat_algebraMap_iff.mp
      (RingHom.flat_of_regular_parameters ψ e pars hdim (by simp [pars]) hgen hreg)
  let := hflat
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor L J).symm.toLinearEquiv

end Algebra
