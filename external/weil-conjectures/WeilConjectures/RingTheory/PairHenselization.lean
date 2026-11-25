/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.PairHenselizationEssentiallySmall
import WeilConjectures.RingTheory.PairHenselizationFiltered
import WeilConjectures.RingTheory.PairHenselizationColimit

/-!
# Henselization of a pair

Source: Stacks Project, More on Algebra, Tag 0A02, proof of Lemma 15.12.1
(blueprint: lem-weil-pbc-pair-henselization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Henselization of a pair as the colimit of étale algebras trivial modulo the ideal.
Source: Stacks Project, Tag 0A02, proof of Lemma 15.12.1
(blueprint: lem-weil-pbc-pair-henselization).

The full subcategory of `Under (CommRingCat.of B)` has precisely the prescribed objects;
its morphisms are all `B`-algebra maps. The cocone is taken in that under category, so its
vertex carries the canonical structure map from `B`.

Proof (the eight steps of the node):
1. Each object has a unique `B`-algebra map to `B/J`, inverse to its quotient isomorphism.
   These maps are compatible with all morphisms. Morphisms are étale by cancellation
   (definition-torsion-sheaves--3).
2. Finite presentation gives essential smallness, using
   lem-weil-pbc-affine-etale-essentially-small-cover. Pass to a small full subcategory
   (lem-weil-pbc-colimit-initial-full-subcategory) and use filtered algebra colimits
   (def-weil-pbc-category-colimit, lem-weil-pbc-filtered-colimit-algebras-elementwise).
3. The identity algebra is an object. Tensor products provide common successors:
   étaleness follows by base change and composition, and reduction modulo `J` gives
   `(B/J) ⊗[B/J] (B/J)`. Use lem-weil-pbc-etale-ring-base-change and cancellation.
4. For parallel maps `f,g : C → C'`, use the Stacks tensor-product coequalizer
   `(C' ⊗[C] C') ⊗[C' ⊗[B] C'] C'`. Its reduction is `B/J`; it is étale by the same
   base-change and cancellation lemmas. Thus the category is filtered.
5. The compatible maps to `B/J` induce a retraction of the colimit quotient map.
   Every element comes from a stage, where it is congruent to an element of `B`.
   This proves bijectivity (lem-weil-pbc-filtered-colimit-algebras-elementwise).
6. Descend an étale algebra over the colimit to an étale algebra over a stage
   (lem-weil-pbc-etale-algebra-filtered-colimit-descent). The given section modulo the
   ideal then induces a map from this stage algebra to `B/J`.
7. Split the descended section by an idempotent modulo `J`, lift that idempotent to `g`,
   and localize at `g` (lem-weil-pbc-etale-section-idempotent-splitting). This localization
   is an object of the diagram, by étale base change and composition.
8. Its coprojection induces the desired section by the tensor-product universal property;
   compatibility modulo `J` follows from uniqueness in step 1. Apply
   lem-weil-pbc-etale-section-lifting-henselian-pair to conclude henselianness, in the
   terminology of def-weil-pbc-henselian-terminology. -/
theorem pair_henselization (B : Type u) [CommRing B] (J : Ideal B) :
    EssentiallySmall.{u} (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))) ∧
    IsFiltered (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))) ∧
    ∃ c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))),
      Nonempty (IsColimit c) ∧
        HenselianRing c.pt.right (J.map c.pt.hom.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom
          (Ideal.le_comap_map)) := by
  exact ⟨pair_henselization_essentiallySmall B J,
    pair_henselization_filtered B J, pair_henselization_colimit B J⟩

end RingTheory
