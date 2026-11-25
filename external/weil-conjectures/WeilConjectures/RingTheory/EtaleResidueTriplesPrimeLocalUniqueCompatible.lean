/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Compatible affine models of étale residue triples over a prime localization

Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Existence of a compatible descended affine model.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-compatible)
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model)

Take the identity triple over R and the composite R → Rₚ → t.B. The structure
equality is immediate, and compatibility follows from t.compatible, hψ and hK.
-/
theorem etaleResidueTriples_primeLocalization_component_extension_compatible
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ) :
    ∃ (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B),
      c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ := by
  let c : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  refine ⟨c, CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α,
    ?_, ?_⟩
  · simp [c]
  · change (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α) ≫
      (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ
    rw [Category.assoc, t.compatible, hψ, hK]

end AlgebraicGeometry.Scheme
