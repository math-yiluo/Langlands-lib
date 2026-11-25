/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Pi

/-! # The finite-partition principal w-localization

Source: blueprint, proper base change, definition of the affine w-localization, order 1222
(blueprint: theorem-existence-contractible-covers--1).

The indices remember both the finite constructible partition and its denominators.
Refinement requires divisibility of denominators, so the component localization maps exist.
This construction is distinct from the upstream `WLocalization`, whose stages use localizations
at larger submonoids. No geometric property or comparison with that construction is asserted.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization

variable (A : Type u) [CommRing A]

/-- A finite constructible partition of `Spec A` with one nonvanishing denominator per part.
The unique-membership condition allows the empty partition precisely for an empty spectrum.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
structure Index where
  parts : Finset (Set (PrimeSpectrum A))
  nonempty : ∀ E ∈ parts, Set.Nonempty E
  constructible : ∀ E ∈ parts, Topology.IsConstructible E
  partition : ∀ p : PrimeSpectrum A, ∃! E : parts, p ∈ E.val
  denominator : parts → A
  nonvanishing : ∀ E : parts, E.val ⊆ PrimeSpectrum.basicOpen (denominator E)

variable {A}

/-- Refinement together with divisibility from each parent denominator to the child denominator.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
def Refines (i j : Index A) : Prop :=
  ∀ F : j.parts, ∃ E : i.parts, F.val ⊆ E.val ∧ i.denominator E ∣ j.denominator F

/-- Refinement is reflexive: use each part itself and reflexivity of subset and divisibility.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
theorem refines_refl (i : Index A) : Refines i i := by
  intro F
  exact ⟨F, Set.Subset.rfl, dvd_refl _⟩

/-- Refinement is transitive: choose the intermediate parent, then its parent, and compose
subset inclusions and divisibility relations. Source: blueprint order 1222
(blueprint: theorem-existence-contractible-covers--1). -/
theorem refines_trans (i j k : Index A) (hij : Refines i j) (hjk : Refines j k) :
    Refines i k := by
  intro F
  obtain ⟨E, hFE, hdFE⟩ := hjk F
  obtain ⟨D, hED, hdED⟩ := hij E
  exact ⟨D, hFE.trans hED, hdED.trans hdFE⟩

/-- The index preorder, with exactly the refinement/divisibility relation as its order.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
instance indexPreorder : Preorder (Index A) where
  le := Refines
  le_refl := refines_refl
  le_trans := refines_trans

/-- The product of principal localizations at an index; the empty product is the zero ring.
Its ring operations and its diagonal algebra structure are the standard Pi structures.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
abbrev Stage (i : Index A) : Type u :=
  (E : i.parts) → Localization.Away (i.denominator E)

/-- Choose the parent supplied by refinement. It is unique because the child is nonempty
and different parts of a partition are disjoint. Source: blueprint order 1222
(blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def parent {i j : Index A} (h : i ≤ j) (F : j.parts) : i.parts :=
  Classical.choose (h F)

/-- The chosen parent's denominator divides the child's denominator, by the refinement data.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1).
Proof: take the divisibility clause of the witness selected by `parent`. -/
theorem parent_dvd {i j : Index A} (h : i ≤ j) (F : j.parts) :
    i.denominator (parent h F) ∣ j.denominator F := by
  exact (Classical.choose_spec (h F)).2

/-- The component map is projection to the parent followed by the unique localization map.
The parent's denominator is a unit in the child localization by divisibility. The lift sends
`a/f^n` to `(a/1)(f/1)^(-n)`. Source: blueprint order 1222
(blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def transition {i j : Index A} (h : i ≤ j) : Stage i →ₐ[A] Stage j :=
  AlgHom.pi fun F ↦
    (IsLocalization.Away.liftAlgHom (i.denominator (parent h F))
      (f := Algebra.ofId A (Localization.Away (j.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd (j.denominator F) (parent_dvd h F))).comp
        (Pi.evalAlgHom A (fun E : i.parts ↦ Localization.Away (i.denominator E)) (parent h F))

private theorem parent_eq_of_subset {i j : Index A} (h : i ≤ j) (F : j.parts)
    (E : i.parts) (hFE : F.val ⊆ E.val) : parent h F = E := by
  obtain ⟨p, hp⟩ := j.nonempty F.val F.property
  exact (i.partition p).unique ((Classical.choose_spec (h F)).1 hp) (hFE hp)

private theorem parent_self (i : Index A) (E : i.parts) : parent (le_refl i) E = E :=
  parent_eq_of_subset _ _ _ Set.Subset.rfl

private theorem component_eq {B : Type u} [CommRing B] [Algebra A B]
    (i : Index A) {E F : i.parts} (h : E = F)
    (φ : Localization.Away (i.denominator E) →ₐ[A] B)
    (ψ : Localization.Away (i.denominator F) →ₐ[A] B) (x : Stage i) :
    φ (x E) = ψ (x F) := by
  subst F
  exact DFunLike.congr_fun
    (Subsingleton.elim (h := IsLocalization.algHom_subsingleton
      (Submonoid.powers (i.denominator E))) φ ψ) (x E)

/-- Identity transitions are identities. A nonempty part has itself as its unique parent;
localization uniqueness identifies its component map with the identity.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
theorem transition_id (i : Index A) : transition (le_refl i) = AlgHom.id A (Stage i) := by
  apply AlgHom.ext
  intro x
  funext E
  exact component_eq i (parent_self i E)
    (IsLocalization.Away.liftAlgHom (i.denominator (parent (le_refl i) E))
      (f := Algebra.ofId A (Localization.Away (i.denominator E)))
      (IsLocalization.Away.isUnit_of_dvd (i.denominator E) (parent_dvd (le_refl i) E)))
    (AlgHom.id A _) x

/-- Transitions compose. For each final child the two successive parents equal its direct
parent by the partition property. The resulting localization maps agree on `A`, so
`IsLocalization.ringHom_ext` identifies them; product extensionality finishes.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
theorem transition_comp {i j k : Index A} (hij : i ≤ j) (hjk : j ≤ k) :
    transition (le_trans hij hjk) = (transition hjk).comp (transition hij) := by
  apply AlgHom.ext
  intro x
  funext F
  have hparent : parent (le_trans hij hjk) F = parent hij (parent hjk F) :=
    parent_eq_of_subset _ _ _
      ((Classical.choose_spec (hjk F)).1.trans
        (Classical.choose_spec (hij (parent hjk F))).1)
  exact component_eq i hparent
    (IsLocalization.Away.liftAlgHom (i.denominator (parent (le_trans hij hjk) F))
      (f := Algebra.ofId A (Localization.Away (k.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd (k.denominator F)
        (parent_dvd (le_trans hij hjk) F)))
    ((IsLocalization.Away.liftAlgHom (j.denominator (parent hjk F))
      (f := Algebra.ofId A (Localization.Away (k.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd (k.denominator F) (parent_dvd hjk F))).comp
        (IsLocalization.Away.liftAlgHom (i.denominator (parent hij (parent hjk F)))
          (f := Algebra.ofId A (Localization.Away (j.denominator (parent hjk F))))
          (IsLocalization.Away.isUnit_of_dvd (j.denominator (parent hjk F))
            (parent_dvd hij (parent hjk F))))) x

/-- The diagram of commutative `A`-algebras with the specified component localization maps.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def diagram : Index A ⥤ CommAlgCat.{u} A where
  obj i := CommAlgCat.of A (Stage i)
  map h := CommAlgCat.ofHom (transition h.le)
  map_id i := congrArg CommAlgCat.ofHom (transition_id i)
  map_comp h g := congrArg CommAlgCat.ofHom (transition_comp h.le g.le)

/-- The index category is filtered. It is inhabited by the one-part partition with denominator
one when the spectrum is nonempty, and by the empty partition otherwise. For two indices,
take all nonempty intersections, with denominator the product of the two denominators.
Constructibility is closed under intersections; primality gives nonvanishing of the product.
Each factor divides that product, giving both refinement arrows. Parallel arrows are equal
because the category is a preorder. Source: blueprint order 1222
(blueprint: theorem-existence-contractible-covers--1). -/
theorem index_isFiltered : IsFiltered (Index A) := by
  classical
  have hnonempty : Nonempty (Index A) := by
    let P := ({Set.univ} : Finset (Set (PrimeSpectrum A))).filter Set.Nonempty
    refine ⟨{
      parts := P
      nonempty := fun E hE ↦ (Finset.mem_filter.mp hE).2
      constructible := ?_
      partition := ?_
      denominator := fun _ ↦ 1
      nonvanishing := ?_ }⟩
    · intro E hE
      have h : E = Set.univ := Finset.mem_singleton.mp (Finset.mem_filter.mp hE).1
      rw [h]
      exact Topology.IsConstructible.univ
    · intro p
      have hU : Set.univ ∈ P :=
        Finset.mem_filter.mpr ⟨Finset.mem_singleton_self _, ⟨p, Set.mem_univ p⟩⟩
      refine ⟨⟨Set.univ, hU⟩, Set.mem_univ p, ?_⟩
      intro E _
      exact Subtype.ext (Finset.mem_singleton.mp (Finset.mem_filter.mp E.property).1)
    · intro E
      simp only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top]
      exact Set.subset_univ _
  have hcommon : ∀ i j : Index A, ∃ k : Index A, i ≤ k ∧ j ≤ k := by
    intro i j
    let P := ((i.parts ×ˢ j.parts).image fun EF ↦ EF.1 ∩ EF.2).filter Set.Nonempty
    have hparts : ∀ G ∈ P, ∃ (E : i.parts) (F : j.parts), G = E.val ∩ F.val := by
      intro G hG
      obtain ⟨hG, _⟩ := Finset.mem_filter.mp hG
      obtain ⟨EF, hEF, hG⟩ := Finset.mem_image.mp hG
      obtain ⟨hE, hF⟩ := Finset.mem_product.mp hEF
      exact ⟨⟨EF.1, hE⟩, ⟨EF.2, hF⟩, hG.symm⟩
    choose left right heq using fun G : P ↦ hparts G.val G.property
    let k : Index A := {
      parts := P
      nonempty := fun G hG ↦ (Finset.mem_filter.mp hG).2
      constructible := by
        intro G hG
        have h : G = (left ⟨G, hG⟩).val ∩ (right ⟨G, hG⟩).val := heq ⟨G, hG⟩
        rw [h]
        exact (i.constructible _ (left ⟨G, hG⟩).property).inter
          (j.constructible _ (right ⟨G, hG⟩).property)
      partition := by
        intro p
        obtain ⟨E, hpE, hE⟩ := i.partition p
        obtain ⟨F, hpF, hF⟩ := j.partition p
        have hG : E.val ∩ F.val ∈ P := by
          apply Finset.mem_filter.mpr
          refine ⟨?_, ⟨p, hpE, hpF⟩⟩
          exact Finset.mem_image.mpr
            ⟨(E.val, F.val), Finset.mem_product.mpr ⟨E.property, F.property⟩, rfl⟩
        refine ⟨⟨E.val ∩ F.val, hG⟩, ⟨hpE, hpF⟩, ?_⟩
        intro G hpG
        have hp : p ∈ (left G).val ∩ (right G).val := (heq G) ▸ hpG
        have hleft : left G = E := hE _ hp.1
        have hright : right G = F := hF _ hp.2
        apply Subtype.ext
        exact (heq G).trans (by rw [hleft, hright])
      denominator := fun G ↦ i.denominator (left G) * j.denominator (right G)
      nonvanishing := by
        intro G p hp
        rw [PrimeSpectrum.basicOpen_mul]
        have hp' : p ∈ (left G).val ∩ (right G).val := (heq G) ▸ hp
        exact ⟨i.nonvanishing (left G) hp'.1, j.nonvanishing (right G) hp'.2⟩ }
    refine ⟨k, ?_, ?_⟩
    · intro G
      refine ⟨left G, ?_, dvd_mul_right _ _⟩
      exact fun p hp ↦ ((heq G) ▸ hp).1
    · intro G
      refine ⟨right G, ?_, dvd_mul_left _ _⟩
      exact fun p hp ↦ ((heq G) ▸ hp).2
  exact {
    nonempty := hnonempty
    cocone_objs := fun i j ↦ by
      obtain ⟨k, hi, hj⟩ := hcommon i j
      exact ⟨k, homOfLE hi, homOfLE hj, trivial⟩
    cocone_maps := fun {i j} f g ↦ ⟨j, 𝟙 j, Subsingleton.elim _ _⟩ }

attribute [instance] index_isFiltered

/-- The affine principal w-localization is the colimit of the partition/denominator diagram
in commutative `A`-algebras. Its algebra structure is the structural map induced by the diagonal
maps into the stages. Source: blueprint order 1222 (blueprint:
theorem-existence-contractible-covers--1). -/
noncomputable def algebra (A : Type u) [CommRing A] : CommAlgCat.{u} A :=
  colimit (diagram (A := A))

/-- This colimit is ind-Zariski in the principal-localization sense. Use the filtered diagram
above and its colimit cocone; enumerate each finite set of parts by `Fin n` and transport the
product along that enumeration. The empty set gives `n = 0`.
Source: blueprint order 1222 (blueprint: theorem-existence-contractible-covers--1). -/
theorem isIndPrincipalZariski : Algebra.IsIndPrincipalZariski A (algebra A) := by
  classical
  refine ⟨Index A, inferInstance, inferInstance,
    ColimitPresentation.colimit (diagram (A := A)), ?_⟩
  intro i
  let e := Fintype.equivFin i.parts
  refine ⟨Fintype.card i.parts, fun j ↦ i.denominator (e.symm j), ?_⟩
  exact ⟨AlgEquiv.piCongrLeft' A
    (fun E : i.parts ↦ Localization.Away (i.denominator E)) e⟩

end PrincipalWLocalization
