/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.FlatPolynomialAppendTensorFibre
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.FlatAndFlatOfFlatFibreNoetherian

/-!
# Appending coordinates regular on the closed fibre preserves flatness

Source: Stacks Project, Smoothing Ring Maps, Tag 07FH, lemma-solution-modulo,
property (1); Algebra, Tags 00OP, 07DY and 00MP.
-/

@[expose] public section

open scoped TensorProduct

set_option autoImplicit false
universe u v
namespace Algebra

/-- Appending elements of the prime whose images form a regular sequence in the first
closed fibre preserves flatness of the localized polynomial coordinate map.
Source: Stacks Project, Tag 07FH, lemma-solution-modulo, the flatness argument for
property (1); Algebra, Tags 00OP, 07DY and 00MP.
(blueprint: lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence).

Proof: Put P₀ = k[X_j], p₀ = φ₀⁻¹(q), A₀ = (P₀)_{p₀}, L = Λ_q, and
S = L/p₀L. Put P₁ = k[X_j,Y_i], let p₁ be the contraction of q under the
appended evaluation, and put A₁ = (P₁)_{p₁}. Inclusion of the first coordinates
induces a local map A₀ → A₁, and evaluation induces a local map A₁ → L;
their composite is the original localization map. All these rings are Noetherian.
Since every z_i belongs to q, the closed fibre A₁/m₀A₁ is canonically the
localization of κ(p₀)[Y_i] at the ideal of all Y_i: reduction kills p₀, the
remaining contracted prime contains every Y_i, and the quotient by their ideal
is the field κ(p₀), so that contracted prime is exactly the origin ideal.
By Tag 00OP this fibre is regular local of dimension e, with parameters Y_i.
The induced local map to S takes these parameters to the prescribed regular
sequence. By Tag 07DY it is flat. Identify the tensor fibre
(A₁/m₀A₁) ⊗[A₁] L with S by the canonical quotient-tensor equivalence.
Apply Tag 00MP to A₀ → A₁ → L and the finite nonzero L-module L, using
hflat and this fibre flatness. This makes L flat over A₁. The resulting map
is the canonical localRingHom by the localization universal property.
Regularity of the sequence includes nonvanishing of its final quotient, hence
of S and L. For e = 0 the origin fibre is κ(p₀), and the same argument applies.
No generation or regular-local hypothesis on S is required. -/
theorem flat_polynomial_append_of_fibre_regular_sequence
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (q : Ideal Λ) [q.IsPrime]
    (t e : ℕ) (xs : Fin t → Λ) (zs : Fin e → Λ)
    (hzq : ∀ i, zs i ∈ q)
    (hflat : (Localization.localRingHom
      (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom) q
      (MvPolynomial.aeval (R := k) xs).toRingHom rfl).Flat)
    (hseq : RingTheory.Sequence.IsRegular (Localization.AtPrime q ⧸
      (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp
          (MvPolynomial.aeval (R := k) xs).toRingHom))
      (List.ofFn (fun i : Fin e ↦ Ideal.Quotient.mk
        ((q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
          ((algebraMap Λ (Localization.AtPrime q)).comp
            (MvPolynomial.aeval (R := k) xs).toRingHom))
        (algebraMap Λ (Localization.AtPrime q) (zs i))))) :
    let φ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
      MvPolynomial.aeval (Fin.addCases xs zs)
    (Localization.localRingHom (q.comap φ.toRingHom) q φ.toRingHom rfl).Flat := by
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
  have heval : φ₁.toRingHom.comp ι = φ₀.toRingHom := by
    change (φ₁.comp (MvPolynomial.rename (Fin.castAdd e))).toRingHom = _
    congr 1
    ext j
    simp [φ₁, φ₀]
  have hc : p₀ = p₁.comap ι := by
    change q.comap φ₀.toRingHom = (q.comap φ₁.toRingHom).comap ι
    rw [Ideal.comap_comap, heval]
  let α : A₀ →+* A₁ := Localization.localRingHom p₀ p₁ ι hc
  let β : A₁ →+* L := Localization.localRingHom p₁ q φ₁.toRingHom rfl
  let γ : A₀ →+* L := Localization.localRingHom p₀ q φ₀.toRingHom rfl
  have hcomp : β.comp α = γ := by
    symm
    apply Localization.localRingHom_unique
    intro x
    change (Localization.localRingHom p₁ q φ₁.toRingHom rfl)
      ((Localization.localRingHom p₀ p₁ ι hc)
        (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime p₀) x)) = _
    rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map]
    exact congrArg (algebraMap Λ L) (DFunLike.congr_fun heval x)
  let : Algebra A₀ A₁ := α.toAlgebra
  let : Algebra A₁ L := β.toAlgebra
  let : Algebra A₀ L := γ.toAlgebra
  have : IsScalarTower A₀ A₁ L := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : IsLocalHom (algebraMap A₀ A₁) :=
    Localization.isLocalHom_localRingHom p₀ p₁ ι hc
  have : IsLocalHom (algebraMap A₁ L) :=
    Localization.isLocalHom_localRingHom p₁ q φ₁.toRingHom rfl
  have : Module.Flat A₀ L := (RingHom.flat_algebraMap_iff).mp hflat
  have hfibre : Module.Flat
      (A₁ ⧸ (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ A₁))
      ((A₁ ⧸ (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ A₁)) ⊗[A₁] L) :=
    flat_tensor_fibre_polynomial_append_of_regular_sequence k Λ q t e xs zs hzq hseq hc
  have : Module.Flat A₁ L :=
    (Module.flat_and_flat_of_flat_fibre_noetherian A₀ A₁ L L hfibre).2
  exact (RingHom.flat_algebraMap_iff).mpr ‹Module.Flat A₁ L›

end Algebra
