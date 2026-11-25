/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.CompletionAtQuasiFinitePrimeMap
import WeilConjectures.RingTheory.CompletionAtQuasiFinitePrimeSplit
import WeilConjectures.RingTheory.QuasiFiniteAtFiniteSubalgebraAway

@[expose] public section

universe u v

/-!
# Completion at a quasi-finite prime is a direct factor

Source: Stacks Project, Algebra, Lemma Tag 07NC (blueprint:
lem-weil-pbc-completion-at-quasi-finite-prime).
-/

namespace Algebra

/-- Completion at a quasi-finite prime splits off via the natural projection.

Source: Stacks Project, Algebra, Lemma Tag 07NC
(blueprint: lem-weil-pbc-completion-at-quasi-finite-prime).

The local map is `Localization.localRingHom` and the completions are taken at the
maximal ideals of the localizations, as in `AdicCompletion.completion_finite_extension`.
The map `ψ` is characterized on every quotient coordinate, so it is the map induced on
completions.
The formula for `φ` on pure tensors specifies the natural projection, including its
compatibility with both the `S`-action and the completed-base action. Transporting these
actions along `β` gives the corresponding actions on `B` and the product.

Proof (the eight steps of the node):
1. Choose a finite R-subalgebra S' and g outside q' = S' ∩ q with S'_g ≅ S_g, using
   lem-weil-pbc-quasi-finite-at-finite-subalgebra-away (00QB, pointwise via 00Q9).
2. Clearing powers of g proves S'_{q'} ≅ S_q; the isomorphism carries maximal-ideal
   powers onto one another, hence gives an isomorphism α of completions. The induced
   local and completed maps commute (def-weil-pbc-localization-at-prime,
   def-weil-pbc-module-localization-away, def-weil-pbc-adic-completion).
3. Apply lem-weil-pbc-completion-finite-extension (07N9) to T = Rph ⊗[R] S'. Select
   the idempotent e corresponding to the q' factor; Te maps isomorphically to its
   completed local ring (def-weil-finitely-generated-module).
4. For j = 1 ⊗ inclusion : T → U, check φ ∘ j = α ∘ φ' on pure tensors, using step 2.
5. Localization commutes with these tensor products, so j becomes an isomorphism after
   inverting g (lem-weil-pbc-localization-tensor-over-base,
   def-weil-pbc-module-localization-away).
6. The image of g in the first completed factor is a unit. Thus γe is a unit in Te,
   where γ = 1 ⊗ g. Its inverse v gives vγe = e; put f₀ = j(e) and w = j(v).
7. The restriction j : Te → Uf₀ is bijective: clear g-denominators using step 5, then
   multiply by powers of v or w using step 6 (def-weil-pbc-module-localization-away).
8. Put B = U(1-f₀) and β(u) = u(1-f₀). Step 4 shows φ vanishes on 1-f₀, and steps
   2, 3, 7 show its restriction to Uf₀ is an isomorphism. Compose the idempotent
   decomposition U ≅ Uf₀ × B with this isomorphism to obtain (φ, β). The pure-tensor
   formula gives the S- and Rph-algebra compatibilities, including the source's sanity
   check that the projection is the natural map. -/
theorem completion_at_quasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [IsNoetherianRing R]
    (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) :
    let p : Ideal R := q.comap (algebraMap R S)
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Ip := IsLocalRing.maximalIdeal Rp
    let Iq := IsLocalRing.maximalIdeal Sq
    let Rph := AdicCompletion Ip Rp
    let Sqh := AdicCompletion Iq Sq
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    let U := TensorProduct R Rph S
    ∃ ψ : Rph →+* Sqh,
      (∀ (n : ℕ) (x : Rph) (a : Rp),
        AdicCompletion.evalₐ Ip n x = Ideal.Quotient.mk (Ip ^ n) a →
        AdicCompletion.evalₐ Iq n (ψ x) = Ideal.Quotient.mk (Iq ^ n) (f a)) ∧
      ∃ (B : Type (max u v)) (_ : CommRing B) (β : U →+* B) (φ : U →+* Sqh),
        (∀ (x : Rph) (y : S),
          φ (TensorProduct.tmul R x y) =
            ψ x * algebraMap Sq Sqh (algebraMap S Sq y)) ∧
        ∃ e : U ≃+* Sqh × B, e.toRingHom = RingHom.prod φ β := by
  dsimp
  obtain ⟨S', hfinite, g, hg, haway⟩ :=
    exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime R S q hq
  let : Module.Finite R S' := hfinite
  obtain ⟨ψ, hψ⟩ := exists_completion_map_atPrime R S q
  obtain ⟨B, _inst, β, φ, hφ, e, he⟩ :=
    completion_split_of_finite_subalgebra_away R S q S' g hg haway ψ hψ
  exact ⟨ψ, hψ, B, inferInstance, β, φ, hφ, e, he⟩

end Algebra
