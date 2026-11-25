/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeExtension
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRestriction

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Cocones on pointed étale ring diagrams before and after prime localization are
naturally equivalent, with the same vertex and the same restricted base map.
Source: Stacks Project, Tags 04GW, 00CR, 01ZM and 07RP.
(blueprint: new-lem-sbc-etale-triples-prime-localization-cocone-equiv)

Proof: Write A = R_p as the filtered colimit of the principal localizations R_s for
s outside p (Tag 00CR). A finitely presented étale A-algebra descends to an étale
R_s-algebra (Tags 01ZM, 07RP). Restrict its map to K to this model. Its kernel
is a prime over p, and its map to K factors uniquely through the residue field;
composition R → R_s → B_s is étale, so this is an R-triple. Define its leg to V
using the given R-cocone. Naturality along further principal refinements inverts
all s outside p in this leg: each refinement is still an R-triple. The leg
therefore extends uniquely from B_s to its localization, identified with the
original A-algebra. Morphisms descend at a common stage, and equalities at a
later stage (01ZM); this proves independence of the model and naturality of
these extended legs. Descending both directions and the inverse relations of
a comparison isomorphism deals with different models of an object.
Conversely, localize each R-triple B at the images of R outside p; base change
preserves étaleness, and its pointing extends uniquely because these images
are units in K. Restrict the corresponding A-cocone leg along B → B localized.
These constructions are inverse: on an A-triple this follows from independence
of its model; on an R-triple use its principal refinements and naturality,
together with uniqueness of extension from a localization. Both operations
commute with postcomposition into every V → W by the same uniqueness.
Finally, the identity R-triple maps into each descended R-triple. Naturality
of the original cocone along this map gives the asserted equality on R.
No universal cocone or algebra structure on the vertex is assumed here. -/
theorem etaleResidueTriples_primeLocalization_coconeEquiv
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    : ∃ E : ∀ V : CommRingCat.{u},
        (etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V) ≃
        (etaleResidueTriplesRingDiagram
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
            (Functor.const _).obj V),
      (∀ (V W : CommRingCat.{u}) η (f : V ⟶ W),
        E W (η ≫ (Functor.const _).map f) =
          E V η ≫ (Functor.const _).map f) ∧
      ∀ (V : CommRingCat.{u}) η
          (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
          (r : R),
        (t.α ≫ (E V η).app t).hom (algebraMap R (Localization.AtPrime p.asIdeal) r) =
          (η.app ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩).hom r := by
  classical
  let F := fun V η ↦
    (etaleResidueTriples_primeLocalization_cocone_extension R p K χ q ψ hψ hK V η).choose
  have hF : ∀ V η,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η (F V η) :=
    fun V η ↦
      (etaleResidueTriples_primeLocalization_cocone_extension
        R p K χ q ψ hψ hK V η).choose_spec.1
  have uniqueF : ∀ V η θ,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ →
      θ = F V η :=
    fun V η θ h ↦
      (etaleResidueTriples_primeLocalization_cocone_extension
        R p K χ q ψ hψ hK V η).choose_spec.2 θ h
  have bijectiveF : ∀ V, Function.Bijective (F V) := by
    intro V
    constructor
    · intro η η' he
      obtain ⟨η₀, hη₀, hu⟩ :=
        etaleResidueTriples_primeLocalization_cocone_restriction
          R p K χ q ψ hψ hK V (F V η)
      have hη' := hF V η'
      rw [← he] at hη'
      exact (hu η (hF V η)).trans (hu η' hη').symm
    · intro θ
      obtain ⟨η, hη, _⟩ :=
        etaleResidueTriples_primeLocalization_cocone_restriction R p K χ q ψ hψ hK V θ
      exact ⟨η, (uniqueF V η θ hη).symm⟩
  let E := fun V ↦ Equiv.ofBijective (F V) (bijectiveF V)
  refine ⟨E, ?_, ?_⟩
  · intro V W η f
    change F W (η ≫ (Functor.const _).map f) = F V η ≫ (Functor.const _).map f
    symm
    apply uniqueF
    intro s t β hb hp
    change β ≫ (F V η).app t ≫ f = η.app s ≫ f
    rw [← Category.assoc, hF V η s t β hb hp]
  · intro V η t r
    let s : EtaleResidueTriples R p K χ :=
      ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
    let β := CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α
    have hb : s.α ≫ β =
        CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α := by
      simp [s, β]
    have hp : β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ := by
      dsimp [β, s]
      rw [Category.assoc, t.compatible, hψ, hK]
    have h := ConcreteCategory.congr_hom (hF V η s t β hb hp) r
    exact h


end AlgebraicGeometry.Scheme
