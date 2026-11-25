/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.PopescuFlatCoordinatesA0
import WeilConjectures.RingTheory.PopescuFlatCoordinatesGivenAdmissible

/-!
# Flat coordinates adapted to an Artinian subalgebra

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FH, through property (1).
(blueprint: lem-weil-pbc-popescu-flat-coordinates).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Choose an admissible subalgebra containing a finite set and flat polynomial coordinates
whose residue differentials span its differentials. This is the coordinate-construction part,
not the essentially smooth factorization, of Stacks Tag 07FH.
(blueprint: lem-weil-pbc-popescu-flat-coordinates).

Proof: Localize the geometrically regular Noetherian algebra at q. Tensor products commute
with localization, and regularity is preserved by localization, so it remains geometrically
regular. Its prime-power quotient B is Artinian local, with maximal ideal the image of q.
The injectivity theorem 07E5 embeds H1 of its residue field into the finite conormal space
q/q²; consequently that H1 is finite dimensional. Apply 07FG and directedness to obtain an
admissible subalgebra A₀ containing the finite set E. Apply the corrected enlargement lemma
PopescuSolutionModuloChoose to A₀. This gives an admissible A containing A₀, elements of Λ
mapping into A whose residue differentials are a basis, and elements of q mapping into A
which generate qΛ_q. Use the basis elements as the first t polynomial coordinates. By 07E6
this polynomial localization maps flatly to Λ_q and its closed fibre is regular local.
Select from the q-generators a minimal set generating the maximal ideal of that fibre.
Nakayama and regular-local regularity make these a regular system of parameters and a
regular sequence. Append these elements as further coordinates. Their images generate the
closed-fibre maximal ideal, giving pΛ_q = qΛ_q. The closed fibre of the extended polynomial
localization over the first localization is the polynomial ring over κ(p') localized at its
origin, with parameters the added variables. The regular-sequence flatness criterion 07DY
makes its map to the regular closed fibre flat. Apply the Noetherian local fibre-flatness
criterion 00MP to conclude flatness of the extended localization map ψ. All coordinates
still map into A, and their differentials span because the first t already form a basis.
The maximal ideal of A is the contraction of the ambient maximal ideal: admissibility puts
it inside that contraction, which is proper because it excludes 1; maximality gives equality.
This proves every asserted property. No quotient factorization or étaleness is asserted. -/
theorem exists_popescu_flat_coordinates
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (E : Finset (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom
        ((q.map (algebraMap Λ (Localization.AtPrime q))).map
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      (∀ e ∈ E, e ∈ A) ∧
      ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
        (ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q),
        ψ.comp (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom))) =
          (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom ∧
        q.map (algebraMap Λ (Localization.AtPrime q)) =
          (q.comap φ.toRingHom).map
            ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ∧
        ψ.Flat ∧
        ∃ a : Fin m → A,
          (∀ j, (a j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (φ (MvPolynomial.X j)))) ∧
          Submodule.span (IsLocalRing.ResidueField A)
            (Set.range (fun j ↦ KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (a j)))) = ⊤ := by
  obtain ⟨A₀, hA₀loc, hA₀, hE⟩ :=
    exists_popescu_admissible_containing_finset k Λ p hp hreg q n hn E
  obtain ⟨A, hAloc, hA, hmA, hle, hcoords⟩ :=
    exists_popescu_flat_coordinates_given_admissible k Λ p hp hreg q n hn A₀ hA₀loc hA₀
  exact ⟨A, hAloc, hA, hmA, (fun e he ↦ hle (hE e he)), hcoords⟩

end Algebra
