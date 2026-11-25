/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationExtensionUniqueAux

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Compatible component legs are unique.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension-unique)

Proof: Put A = R_p and S = R minus p. By the principal-localization colimit
(00CR), Spec A is the inverse limit of the affine Spec R_s for s in S, with
affine transitions. Descend Spec t.B as an etale scheme of finite presentation
by finite-data descent (01ZM, 07RP). The upper-tail base changes of its qcqs
model have affine transitions and affine limit Spec t.B. The affine-limit
theorem (01Z6) therefore gives an affine model Spec C at a later stage.
C is etale over R_s and hence over R, and its base change to A identifies t.B
with S^{-1}C. Restrict the pointing t.B to K along the localization map i.
Its kernel is prime; extend the injection of C modulo that kernel to its
fraction field inside K to obtain the residue-field embedding. The identities
hψ and hK make the prime lie over p and the embedding compatible with χ.
This defines a global triple c for which i : c.B to t.B satisfies the two
compatibility equations in hb and hb'. Apply both hypotheses at this c and i.
They give i followed by b = η.app c = i followed by b'. Ring homomorphisms
out of S^{-1}C agreeing on C are equal by IsLocalization.ringHom_ext. Transport
that equality across the base-change identification to obtain b = b'.
This argument needs only a pointed affine model, not existence of an extension
of η and not morphism descent for arbitrary global triples. -/
theorem etaleResidueTriples_primeLocalization_component_extension_unique
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
    (V : CommRingCat.{u})
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (b b' : t.B ⟶ V)
    (hb : ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
        s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
          t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        β ≫ b = η.app s)
    (hb' : ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
        s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
          t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        β ≫ b' = η.app s) :
    b = b' := by
  obtain ⟨s, β, hα, hφ, hEpi⟩ :=
    etaleResidueTriples_primeLocalization_component_extension_unique_aux
      R p K χ q ψ hψ hK t
  apply (cancel_epi β).mp
  rw [hb s β hα hφ, hb' s β hα hφ]

end AlgebraicGeometry.Scheme

