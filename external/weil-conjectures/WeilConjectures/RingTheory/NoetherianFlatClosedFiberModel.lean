/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.RingTheory.NoetherianLocalModelTowerExistence
import WeilConjectures.RingTheory.NoetherianLocalModelTowerBaseFlat
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberFlat

/-!
# A common Noetherian stage for base and closed-fibre flatness

Source: Stacks Project, Algebra, proof of Tag 00R7, paragraphs 1 and 2.
(blueprint: lem-weil-pbc-noetherian-flat-closed-fiber-model).
-/

@[expose] public section

universe u v w t p q

open scoped TensorProduct

namespace Module

/-- A Noetherian model at which the base module and the closed-fibre module are flat.
Source: Stacks Project, Algebra, proof of Tag 00R7, first two paragraphs, with the
localization corrections in steps 1--8 of `lem-weil-pbc-criterion-flatness-fibre`.
(blueprint: lem-weil-pbc-noetherian-flat-closed-fiber-model).

This asserts the inputs to the Noetherian fibre criterion, not its conclusions: it does
not assert flatness of `S₀` over `R₀` or of `N₀` over `S₀`. The last two clauses identify
`S` and `M` with localizations of the appropriate base changes. Only the scalar actions
needed to express and use these identifications are retained from the directed system.

Proof:
1. Present `M` by a finite matrix over `S'`. Apply
   `lem-weil-pbc-limit-tower-essentially-finite-presentation` to the two given localized
   presentations and this matrix. Lift rings to a common universe before applying its
   same-universe formulation, and transport the limit comparison maps back along the
   lift equivalences. Its stage rings lie in `Type (max u v w)` and its stage modules
   in `Type t`, as in the statement here. Lift transport preserves the local maps,
   tensor products and flatness hypotheses.
2. The stage rings are Noetherian: the integers are Noetherian; finite type extensions
   and localizations preserve Noetherianity. The maps are local by the tower theorem.
   Consequently each stage maximal ideal is the inverse image of the maximal ideal
   of `R`, and likewise under the transition maps.
3. Compose the two transition localization clauses by tensor associativity and
   localization base change. This makes the transition from the top stage after base
   change along the base ring a localization. Apply
   `lem-weil-pbc-colimit-eventually-flat` to the base and top rings and stage modules.
   Flatness of `M` over `R` gives base flatness at one stage. It persists at later stages:
   base change of a flat module is flat, and localizing a module preserves base flatness.
4. Quotient each stage by the extended maximal ideal of its base. The quotient rings
   are Noetherian local; the quotient modules are finite. Tensor over a quotient and
   localization base change give the same transition localization and module-isomorphism
   clauses for this system. Its colimits are `S/m_R S`, `S'/m_R S'`, and `M/m_R M`.
   Indeed, elements and finite ideal expressions descend to a common stage; an equality
   at the limit holds at a later stage. Locality identifies membership in the maximal
   ideal already at that stage. Thus the kernel of the map from the quotient colimit
   is zero, and surjectivity follows by representing elements at a stage.
5. Apply `lem-weil-pbc-colimit-eventually-flat` to that fibre system and the hypothesis
   `h_fibre`, using the quotient-tensor identification. Obtain fibre flatness at one
   stage; it persists at later stages by base change and localization as in step 3.
   Directedness supplies a common stage `R₀ → S₀ → T₀`, with module `N₀`, at which both
   flatness properties hold. Finiteness is a clause of the tower theorem. No nonzero
   hypothesis is needed: the construction also applies to the zero module.
6. The limit localization clauses identify `S` with a localization of `R ⊗[R₀] S₀`.
   A localization of a ring agrees with its module localization, giving the first
   displayed linear equivalence. For the second, put `C = S ⊗[S₀] T₀` and use its
   canonical action on `S ⊗[S₀] N₀`. The limit clause identifies `S'` with a localization
   of `C`, and identifies `M` with `S' ⊗[T₀] N₀`. Tensor associativity identifies the
   latter with the localization of `S ⊗[S₀] N₀` at the same submonoid. These
   identifications are `S`-linear and the canonical `C`-action has the required tower.
-/
theorem exists_noetherian_flat_closedFiber_model
    (R : Type u) (S : Type v) (S' : Type w) (M : Type t)
    [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    (P : Type p) (Q : Type q) [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra R Q] [Algebra Q S'] [IsScalarTower R Q S']
    [Algebra.FinitePresentation R P] [Algebra.FinitePresentation R Q]
    (W : Submonoid P) (V : Submonoid Q) [IsLocalization W S] [IsLocalization V S']
    [Module.FinitePresentation S' M]
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M))
    [Module.Flat R M] :
    ∃ (R₀ S₀ T₀ : Type (max u v w)) (N₀ : Type t)
      (_ : CommRing R₀) (_ : CommRing S₀) (_ : CommRing T₀)
      (_ : IsLocalRing R₀) (_ : IsLocalRing S₀) (_ : IsLocalRing T₀)
      (_ : IsNoetherianRing R₀) (_ : IsNoetherianRing S₀)
      (_ : IsNoetherianRing T₀)
      (_ : Algebra R₀ S₀) (_ : Algebra S₀ T₀) (_ : Algebra R₀ T₀)
      (_ : IsScalarTower R₀ S₀ T₀)
      (_ : IsLocalHom (algebraMap R₀ S₀)) (_ : IsLocalHom (algebraMap S₀ T₀))
      (_ : AddCommGroup N₀) (_ : Module T₀ N₀) (_ : Module S₀ N₀)
      (_ : Module R₀ N₀) (_ : IsScalarTower S₀ T₀ N₀)
      (_ : IsScalarTower R₀ S₀ N₀)
      (_ : Algebra R₀ R) (_ : Algebra S₀ S),
      Module.Finite T₀ N₀ ∧ Module.Flat R₀ N₀ ∧
      Module.Flat
        (S₀ ⧸ Ideal.map (algebraMap R₀ S₀) (IsLocalRing.maximalIdeal R₀))
        ((S₀ ⧸ Ideal.map (algebraMap R₀ S₀) (IsLocalRing.maximalIdeal R₀)) ⊗[S₀] N₀) ∧
      (∃ U : Submonoid (R ⊗[R₀] S₀),
        Nonempty (LocalizedModule U (R ⊗[R₀] S₀) ≃ₗ[R] S)) ∧
      (∃ (_ : Module (S ⊗[S₀] T₀) (S ⊗[S₀] N₀))
        (_ : IsScalarTower S (S ⊗[S₀] T₀) (S ⊗[S₀] N₀))
        (U : Submonoid (S ⊗[S₀] T₀)),
        Nonempty (LocalizedModule U (S ⊗[S₀] N₀) ≃ₗ[S] M)) := by
  obtain ⟨X⟩ := exists_noetherian_localModelTower R S S' M P Q W V
  let := X.preorder
  let := X.directed
  let := X.commR
  let := X.commS
  let := X.commT
  let := X.localR
  let := X.localS
  let := X.localT
  let := X.noethR
  let := X.noethS
  let := X.noethT
  let := X.algRS
  let := X.algST
  let := X.algRT
  let := X.towerRST
  let := X.localRS
  let := X.localST
  let := X.addN
  let := X.moduleT
  let := X.moduleS
  let := X.moduleR
  let := X.towerSTN
  let := X.towerRSN
  let := X.algRLimit
  let := X.algSLimit
  obtain ⟨i, hi⟩ := X.eventually_baseFlat
  obtain ⟨j, hj⟩ := X.eventually_fiberFlat h_fibre
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact ⟨X.R₀ k, X.S₀ k, X.T₀ k, X.N₀ k,
    X.commR k, X.commS k, X.commT k, X.localR k, X.localS k, X.localT k,
    X.noethR k, X.noethS k, X.noethT k, X.algRS k, X.algST k, X.algRT k,
    X.towerRST k, X.localRS k, X.localST k, X.addN k, X.moduleT k, X.moduleS k,
    X.moduleR k, X.towerSTN k, X.towerRSN k, X.algRLimit k, X.algSLimit k,
    X.finite k, hi k hik, hj k hjk, X.baseLocalization k, X.moduleLocalization k⟩

end Module
