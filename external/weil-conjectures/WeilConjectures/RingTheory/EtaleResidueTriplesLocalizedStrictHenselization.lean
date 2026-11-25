/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselizationCore

/-! # Local-base presentation of a residue-triple colimit

Source: Stacks Project, Tag 04GW (lemma-strict-henselization-different).
(blueprint: lem-sbc-etale-triples-localized-strict-henselization)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Any realization of the residue-triple colimit is an algebraic strict henselization
of the prime localization, with the prescribed structural map from R.
Source: Stacks Project, Tag 04GW (lemma-strict-henselization-different).
(blueprint: lem-sbc-etale-triples-localized-strict-henselization)

Proof: Write A = R_p. Every element outside p becomes invertible in the triple colimit,
because the pointed principal localization adjoining its inverse is an etale triple.
Thus the structural R-map extends uniquely to A. Base change from R to A preserves the
pointed triple colimit: every finitely presented etale A-algebra descends after inverting
one element outside p, as do each morphism and each equality of morphisms. Including
those principal localizations in the R-triple diagram makes these descents cofinal.
Identify the residue field of A with the scheme residue field at p and transport the
given separable closure K through that isomorphism, obtaining L. Over the local base A,
a pointed etale algebra S -> L determines the triple with prime ker(S -> L) and its
unique residue-field embedding; conversely a triple gives that map by evaluation.
These constructions are inverse up to natural isomorphism and preserve structural maps.
The transported universal ring cocone is universal in A-algebras: its descended maps
respect A since they respect R and the inverted elements. Transport its vertex through
e to C and use hbase to identify the R-map with b. This supplies the A-algebra structure,
the residue-field scalar tower on L, and the cocone required by IsStrictHenselization.
The ring C is given; no ring is selected from an unproved existence statement. -/
theorem etaleResidueTriples_localized_isStrictHenselization
    (R : CommRingCat.{u}) (p : Spec R)
    (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c) (C : CommRingCat.{u}) (e : c.pt ≅ C) (b : R ⟶ C)
    (hbase : ∀ t, t.α ≫ c.ι.app t ≫ e.hom = b) :
    ∃ (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : Algebra (Localization.AtPrime p.asIdeal) L)
      (_ : IsScalarTower (Localization.AtPrime p.asIdeal)
        (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : Algebra (Localization.AtPrime p.asIdeal) C),
      (∀ r : R, algebraMap (Localization.AtPrime p.asIdeal) C
        (algebraMap R (Localization.AtPrime p.asIdeal) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime p.asIdeal) L C := by
  obtain ⟨L, iFL, iAL, iSL, iLA, iST, iAC, hmap, hstrict⟩ :=
    etaleResidueTriples_localized_core R p K c hc C e
  let : Field L := iFL
  let : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L := iAL
  let : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L := iSL
  let : Algebra (Localization.AtPrime p.asIdeal) L := iLA
  let : IsScalarTower (Localization.AtPrime p.asIdeal)
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L := iST
  let : Algebra (Localization.AtPrime p.asIdeal) C := iAC
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · intro r
    let t0 : EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)) :=
      ⟨R, 𝟙 R, inferInstance, p, by simp,
        CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K), by simp⟩
    rw [hmap r]
    exact congrArg (fun f : R ⟶ C ↦ f.hom r)
      (hbase t0)
  · exact hstrict

end AlgebraicGeometry.Scheme
