/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation

/-!
# Local structure of a ring strict henselization

Source: Stacks Project, Tags 04GP(2),(4) and 04GW
(blueprint: lem-sc-ring-strict-henselization-local-maximal-ideal).
-/

@[expose] public section

universe u

namespace Algebra

/-- A strict henselization is local, with maximal ideal extended from the base.
Source: Stacks Project, Tags 04GP(2),(4) and 04GW
(blueprint: lem-sc-ring-strict-henselization-local-maximal-ideal).

Proof: Set p to the closed point of Spec A. Identify its scheme residue field with
A's residue field and transport the given separable closure structure to it.
A pointed etale A-algebra S with map f : S → K determines the triple whose prime
is ker f and whose residue embedding sends s/t to f(s)/f(t). The denominator is
nonzero since t is outside ker f. Its prime lies over p because f restricts to
the canonical map A → K. Conversely a triple gives its structural map to K by
composition through its residue field. The two constructions are inverse up to
canonical isomorphism: a field homomorphism is injective, and fraction-field
extension uniquely determines the residue embedding. Morphisms on both sides
are exactly A-algebra maps commuting with these maps to K. This gives an
equivalence of index categories intertwining the underlying ring diagrams.
The forgetful functor from A-algebras to rings preserves the colimit (the
structural map from A is induced by the compatible stage maps). Apply
Scheme.strictHenselization_triples to obtain a local ring T and a structural
map rho : A → T with maximalIdeal T = (maximalIdeal A).map rho. Transport its
colimit along the equivalence just described. Uniqueness of colimits gives an
A-algebra isomorphism T ≃ₐ[A] C. Transport locality along this ring isomorphism.
An isomorphism preserves units, hence carries the maximal ideal to the maximal
ideal; its A-linearity identifies the image of rho with algebraMap A C.
Consequently maximalIdeal C = (maximalIdeal A).map (algebraMap A C).
No Noetherian assumption or completion theorem is used. -/
theorem strictHenselization_local_maximalIdeal
    (A K C : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    ∃ (_ : IsLocalRing C),
      IsLocalRing.maximalIdeal C = (IsLocalRing.maximalIdeal A).map (algebraMap A C) := by
  open CategoryTheory CategoryTheory.Limits in
  exact by
    obtain ⟨p, hp, a, hk, ι, ⟨hι⟩, hιA⟩ := hC.triples_presentation A K C
    let := a
    let := hk
    obtain ⟨_, c, ⟨hc⟩, hlocal, ρ, ψ, hρ, _, _, hm, hker, _⟩ :=
      AlgebraicGeometry.Scheme.strictHenselization_triples (CommRingCat.of A) p K
    let e := (hc.coconePointUniqueUpToIso hι).commRingCatIsoToRingEquiv
    have he : e.toRingHom.comp ρ.hom = algebraMap A C := by
      let t : AlgebraicGeometry.Scheme.EtaleResidueTriples (CommRingCat.of A) p K
          (CommRingCat.ofHom (algebraMap
            ((AlgebraicGeometry.Spec (CommRingCat.of A)).residueField p) K)) :=
        ⟨CommRingCat.of A, 𝟙 _, inferInstance, p, by simp,
          CommRingCat.ofHom (algebraMap
            ((AlgebraicGeometry.Spec (CommRingCat.of A)).residueField p) K), by simp⟩
      have htρ : c.ι.app t = ρ := by simpa [t] using hρ t
      have htι : ι.app t = CommRingCat.ofHom (algebraMap A C) := by
        simpa [t] using hιA t
      have h := hc.comp_coconePointUniqueUpToIso_hom hι t
      rw [htρ] at h
      change ρ ≫ (hc.coconePointUniqueUpToIso hι).hom = ι.app t at h
      rw [htι] at h
      exact congrArg CommRingCat.Hom.hom h
    let := hlocal
    let := e.isLocalRing
    refine ⟨inferInstance, ?_⟩
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, hm, hker, hp]
    change ((IsLocalRing.maximalIdeal A).map ρ.hom).map e.toRingHom = _
    rw [Ideal.map_map, he]

end Algebra
