/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTripleUnitRefinement
import WeilConjectures.RingTheory.EtaleResidueTriplesStrictHenselization
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationComparison

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue-triple colimit gives the local-base strict henselization.
Source: Stacks Project, Tag 04GW.
(blueprint: new-lem-sbc-etale-triples-localized-core)

Proof: Apply `etaleResidueTriple_unit_refinement` to the identity triple and each
s outside p. The resulting pointed principal-localization triple makes s a unit;
cocone naturality makes its image under the identity leg, followed by e, a unit.
`IsLocalization.lift` therefore extends this ring map uniquely to A = R_p.
`Spec.residueFieldIso R p` identifies the scheme residue field with the residue
field of A. Compose its inverse with the given embedding in K to construct the
residue-field algebra structure on K, and compose with the residue map to construct
its A-algebra structure. `Algebra.IsSeparable.of_equiv_equiv` transports separability;
separable closedness of K is unchanged, so this is the required separable closure.
The field-point equivalence `SpecToEquivOfField` gives a point of Spec A and a
residue embedding whose evaluation is precisely A to K. The original R to K
map agrees with its restriction by `Spec.algebraMap_residueFieldIso_inv`.
`etaleResidueTriples_primeLocalization_comparison` now supplies a universal local-base
ring cocone on the given vertex C, with all legs respecting the constructed A-map.
Its proof uses `CommRingCat.localization_colimit_principalLocalizations` to express
A as the filtered colimit of principal localizations and `etale_finite_data_descent`
to descend pointed etale objects, morphisms and equalities: restrict the pointing
to each descended object, lift each finite-presentation morphism at a common stage,
and clear the finitely many relations at a later stage. Pointing compatibility
is checked after mapping to K, where all elements outside p are already units.
Each descended principal-localization algebra is an R-triple. These refinements
identify cocones and their unique descended maps; uniqueness on fractions forces
them to respect A. The comparison uses the original legs followed by e, so its
structural map is the displayed identity-triple map, rather than an arbitrary map.
Finally `etaleResidueTriples_colimit_isStrictHenselization` converts this universal
local-base ring cocone to the pointed-algebra presentation, giving strict henselization.
The vertex and both algebra maps were explicitly constructed before the comparison. -/
theorem etaleResidueTriples_localized_core
    (R : CommRingCat.{u}) (p : Spec R)
    (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c) (C : CommRingCat.{u}) (e : c.pt ≅ C) :
    ∃ (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : Algebra (Localization.AtPrime p.asIdeal) L)
      (_ : IsScalarTower (Localization.AtPrime p.asIdeal)
        (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : Algebra (Localization.AtPrime p.asIdeal) C),
      (∀ r : R, algebraMap (Localization.AtPrime p.asIdeal) C
        (algebraMap R (Localization.AtPrime p.asIdeal) r) =
        (c.ι.app ⟨R, 𝟙 R, inferInstance, p, by simp,
          CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K), by simp⟩ ≫ e.hom).hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime p.asIdeal) L C  := by
  classical
  let A := Localization.AtPrime p.asIdeal
  let χ := CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)
  let t0 : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  let b : R ⟶ C := c.ι.app t0 ≫ e.hom
  have hu (s : p.asIdeal.primeCompl) : IsUnit (b.hom (s : R)) := by
    obtain ⟨t, f, hf⟩ := etaleResidueTriple_unit_refinement R p K χ t0 s s.property
    have hw := c.w f
    change (etaleResidueTriplesRingDiagram R p K χ).map f ≫ c.ι.app t =
      c.ι.app t0 at hw
    have h := congrArg (fun g : R ⟶ c.pt ↦ g.hom (s : R)) hw
    change (c.ι.app t).hom
      (((etaleResidueTriplesRingDiagram R p K χ).map f).hom (s : R)) =
        (c.ι.app t0).hom (s : R) at h
    change IsUnit (e.hom.hom ((c.ι.app t0).hom (s : R)))
    rw [← h]
    exact (hf.map (c.ι.app t).hom).map e.hom.hom
  let aC : A →+* C := IsLocalization.lift hu
  let : Algebra A C := aC.toAlgebra
  have hmap (r : R) : algebraMap A C (algebraMap R A r) = b.hom r :=
    IsLocalization.lift_eq hu r
  let η : p.asIdeal.ResidueField →+* K :=
    (algebraMap ((Spec R).residueField p) K).comp (Spec.residueFieldIso R p).inv.hom
  let : Algebra (IsLocalRing.ResidueField A) K := η.toAlgebra
  let : IsSepClosure (IsLocalRing.ResidueField A) K :=
    ⟨IsSepClosure.sep_closed ((Spec R).residueField p),
      Algebra.IsSeparable.of_equiv_equiv
        (Spec.residueFieldIso R p).commRingCatIsoToRingEquiv (RingEquiv.refl K) (by
          ext x
          change algebraMap ((Spec R).residueField p) K
            ((Spec.residueFieldIso R p).inv.hom ((Spec.residueFieldIso R p).hom.hom x)) = _
          exact congrArg (algebraMap ((Spec R).residueField p) K)
            ((Spec.residueFieldIso R p).commRingCatIsoToRingEquiv.symm_apply_apply x))⟩
  let : Algebra A K := (η.comp (algebraMap A (IsLocalRing.ResidueField A))).toAlgebra
  let : IsScalarTower A (IsLocalRing.ResidueField A) K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let q := SpecToEquivOfField K (Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A K)))
  have hχA : (ΓSpecIso (CommRingCat.of A)).inv ≫
      (Spec (CommRingCat.of A)).Γevaluation q.1 ≫ q.2 =
        CommRingCat.ofHom (algebraMap A K) := by
    apply Spec.map_injective
    rw [show Spec.map ((ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).Γevaluation q.1 ≫ q.2) =
        Spec.map q.2 ≫ (Spec (CommRingCat.of A)).fromSpecResidueField q.1 by
          simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
          rfl]
    exact (SpecToEquivOfField K (Spec (CommRingCat.of A))).symm_apply_apply _
  have hK : CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom (algebraMap A K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ := by
    have hcanon := Spec.algebraMap_residueFieldIso_inv R p
    change CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
      (Spec.residueFieldIso R p).inv =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p at hcanon
    rw [← Category.assoc, ← hcanon, Category.assoc]
    ext r
    change η (algebraMap A (IsLocalRing.ResidueField A) (algebraMap R A r)) =
      η (algebraMap R p.asIdeal.ResidueField r)
    rw [← IsScalarTower.algebraMap_apply R A (IsLocalRing.ResidueField A)]
  obtain ⟨ι, ⟨hd⟩, hρ⟩ := etaleResidueTriples_primeLocalization_comparison
    R p K χ c hc C e q.1 q.2 hχA hK hmap
  have hs : Algebra.IsStrictHenselization A K C :=
    etaleResidueTriples_colimit_isStrictHenselization (CommRingCat.of A) q.1 K
      q.2 hχA (Cocone.mk C ι) hd hρ
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hmap, hs⟩

end AlgebraicGeometry.Scheme
