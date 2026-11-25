/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Compatible maps to prime-localized pointed etale triples

Source: Stacks Project, Tags 04GW, 00CP and 00U2 (3).
(blueprint: new-lem-sbc-etale-triples-prime-localization-compatible-map-exists)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Every pointed étale `R`-triple admits a compatible map into a pointed étale
`R_p`-triple. This is the localization construction used in the uniqueness
argument for compatible cocone legs.
Source: Stacks Project, Tags 04GW (pointed triples), 00CP (localization
universal property), and 00U2 (3) (etale base change). The construction below
is an explicit consequence, valid for any field K, without separable closure.
(blueprint: new-lem-sbc-etale-triples-prime-localization-compatible-map-exists)

Proof: Put A = R_p and let f : B_s -> K be evaluation at s.q followed by s.phi.
Set M to be the image under s.alpha of the multiplicative subset R minus p,
and construct C = M^{-1}B_s, with canonical map beta : B_s -> C. The map
R -> C inverts R minus p, so it extends uniquely to a : A -> C. The standard
localization base-change identification C = A tensor_R B_s identifies a with
the base change of s.alpha; hence Spec(a) is etale by Tag 00U2 (3).

For r outside p, compatibility of s identifies f(s.alpha(r)) with evaluation
of r at p followed by chi. The evaluation has kernel p and the field map chi
is injective, so this value is nonzero, hence a unit of K. By Tag 00CP, f
extends to g : C -> K with g beta = f. The two maps g a and the specified
A-algebra map to K agree on R by hK and compatibility of s; uniqueness for
R -> A gives their equality.

Let Q = ker(g), a prime because K is a field. The injection C/Q -> K extends
to its fraction field by sending c/d to g(c)/g(d); this gives a residue-field
embedding phi_Q whose composite with C -> kappa(Q) is g. Transfer Q and this
embedding to Spec(C) using the canonical affine residue-field identification.
The contraction of Q under a is the kernel of the specified A -> K. By hpsi,
this map is evaluation at q followed by psi. Evaluation has kernel q, and psi
is injective, so the contraction is q. Thus (C, a, Q, phi_Q) is a pointed
etale A-triple t: its compatibility equation is g a = evaluation_q followed
by psi. Finally a composed with R -> A equals beta composed with s.alpha
by construction, and g beta = f is precisely the required pointing equation.
All objects here are explicit localizations, kernels and fraction maps. -/
private lemma pointing_spec_map (B : CommRingCat.{u}) (r : Spec B)
    (K : Type u) [Field K] (φ : (Spec B).residueField r ⟶ CommRingCat.of K) :
    Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation r ≫ φ) =
      Spec.map φ ≫ (Spec B).fromSpecResidueField r := by
  simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

private lemma exists_pointing (B : CommRingCat.{u}) (K : Type u) [Field K]
    (b : B ⟶ CommRingCat.of K) :
    ∃ (r : Spec B) (φ : (Spec B).residueField r ⟶ CommRingCat.of K),
      (ΓSpecIso B).inv ≫ (Spec B).Γevaluation r ≫ φ = b := by
  generalize he : (SpecToEquivOfField K (Spec B)) (Spec.map b) = z
  obtain ⟨r, φ⟩ := z
  refine ⟨r, φ, ?_⟩
  apply Spec.map_injective
  rw [pointing_spec_map]
  have h := (SpecToEquivOfField K (Spec B)).symm_apply_apply (Spec.map b)
  rw [he] at h
  exact h

private lemma pointing_over (A B : CommRingCat.{u}) (q : Spec A)
    (K : Type u) [Field K] (ψ : (Spec A).residueField q ⟶ CommRingCat.of K)
    (a : A ⟶ B) (r : Spec B) (φ : (Spec B).residueField r ⟶ CommRingCat.of K)
    (hc : a ≫ (ΓSpecIso B).inv ≫ (Spec B).Γevaluation r ≫ φ =
      (ΓSpecIso A).inv ≫ (Spec A).Γevaluation q ≫ ψ) :
    Spec.map a r = q := by
  have h := congrArg Spec.map hc
  rw [Spec.map_comp, pointing_spec_map, pointing_spec_map] at h
  have h' := congrArg
    (fun f : Spec (CommRingCat.of K) ⟶ Spec A ↦ f (IsLocalRing.closedPoint K)) h
  simpa using h'

/-- (blueprint: new-lem-sbc-etale-triples-prime-localization-compatible-map-exists) -/
theorem etaleResidueTriples_primeLocalization_compatible_map_exists
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
    (s : EtaleResidueTriples R p K χ) :
    ∃ (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
      (β : s.B ⟶ t.B),
      s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ := by
  classical
  let bs := (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ
  let ba := (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
    (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ
  let P := pushout s.α (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)))
  let β : s.B ⟶ P := pushout.inl s.α _
  let α : CommRingCat.of (Localization.AtPrime p.asIdeal) ⟶ P := pushout.inr s.α _
  let b : P ⟶ CommRingCat.of K :=
    pushout.desc bs ba (s.compatible.trans (by
      change (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ =
        CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ ba
      rw [← hK]
      congr 1
      exact hψ.symm))
  obtain ⟨r, φ, hφ⟩ := exists_pointing P K b
  have hc : α ≫ (ΓSpecIso P).inv ≫ (Spec P).Γevaluation r ≫ φ = ba := by
    rw [hφ]
    exact pushout.inr_desc _ _ _
  have hetale : Etale (Spec.map α) :=
    MorphismProperty.of_isPullback
      (isPullback_SpecMap_pushout s.α (CommRingCat.ofHom (algebraMap R
        (Localization.AtPrime p.asIdeal)))) s.etale
  have hα : s.α ≫ β = CommRingCat.ofHom (algebraMap R
      (Localization.AtPrime p.asIdeal)) ≫ α := pushout.condition
  have hpoint : β ≫ (ΓSpecIso P).inv ≫ (Spec P).Γevaluation r ≫ φ = bs := by
    rw [hφ]
    exact pushout.inl_desc _ _ _
  have hover : Spec.map α r = q := by
    apply pointing_over (CommRingCat.of (Localization.AtPrime p.asIdeal)) P q K ψ α r φ
    exact hc
  let t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ :=
    ⟨P, α, hetale, r, hover, φ, hc⟩
  refine ⟨t, β, hα, ?_⟩
  exact hpoint

end AlgebraicGeometry.Scheme
