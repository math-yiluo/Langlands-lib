/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.RingTheory.EtaleResidueTriplesFiltered
import WeilConjectures.RingTheory.EtaleResidueTriplesExistsColimit

/-!
# Filtered colimit of pointed etale algebras

Source: Stacks Project, Algebra, Tag 04GW (lemma-strict-henselization-different),
and Tag 00D5 (lemma-colimit).
(blueprint: lem-weil-pbc-etale-triples-filtered-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tag 04GW (lemma-strict-henselization-different),
and Tag 00D5 (lemma-colimit).

Proof: Regard a triple as an etale R-algebra equipped with a map to K, recovering its
prime as the kernel and its residue embedding by extension to the fraction field.
The identity R-algebra supplies an object. Tensor products supply common successors.
For parallel maps S → S', use (S' ⊗[S] S') ⊗[S' ⊗[R] S'] S'; the rightmost map
from S' equalizes them, is etale, and admits the compatible map to K.
Finite presentation gives an essentially small category of triples: take a small skeleton
of affine etale R-schemes and the set of residue embeddings over each object.
Construct its ring colimit, and transport the colimit along the equivalence with the
full category. The compatible structural maps R → S and maps S → K give ρ and ψ.
The universal property gives the two displayed compatibilities.
(blueprint: lem-weil-pbc-etale-triples-filtered-colimit). -/
theorem etaleResidueTriples_filtered_colimit
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K] :
    IsFiltered (EtaleResidueTriples R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))) ∧
    ∃ c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))),
      Nonempty (IsColimit c) ∧ ∃ (ρ : R ⟶ c.pt) (ψ : c.pt →+* K),
        (∀ t, t.α ≫ c.ι.app t = ρ) ∧
        (∀ t, ψ.comp (c.ι.app t).hom =
          ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) := by
  exact ⟨etaleResidueTriples_filtered_part R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)),
    etaleResidueTriples_exists_colimit_part R p K⟩

end AlgebraicGeometry.Scheme
