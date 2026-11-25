/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-!
# Strata of stratifications and bounded constructible complexes

Preliminaries on bounded constructible complexes of module objects over a commutative condensed
ring `Λ`, used for dévissages along stratifications:

* some stratum of a stratification of a nonempty scheme contains a nonempty open
  (`ProEtale.CondensedRing.exists_nonempty_opens_subset_stratum`);
* a complex all of whose cohomology sheaves vanish is zero
  (`ProEtale.CondensedRing.isZero_of_forall_isZero_homology`), so every complex on the empty
  scheme is zero (`ProEtale.CondensedRing.isZero_derivedCategory_of_isEmpty'`);
* a constructible sheaf placed in any degree is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_singleFunctor_obj`), and the derived pullback of
  such a sheaf placed in degree `0` is its pullback placed in degree `0`
  (`ProEtale.CondensedRing.leftDerivedUpperStarSingleIso`);
* local finite presentation is transported along commutative squares
  (`ProEtale.CondensedRing.isLocallyFinitelyPresented_upperStar_comp_of_comm`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- In a finite union of closed sets with empty interiors, the interior is empty. -/
lemma interior_iUnion_eq_empty_of_isClosed {X : Type*} [TopologicalSpace X] {n : ℕ}
    (s : Fin n → Set X) (hc : ∀ a, IsClosed (s a)) (hi : ∀ a, interior (s a) = ∅) :
    interior (⋃ a, s a) = ∅ := by
  suffices h : ∀ t : Finset (Fin n), interior (⋃ a ∈ t, s a) = ∅ by
    simpa using h Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t _ ih =>
    rw [Finset.set_biUnion_insert, Set.union_comm,
      interior_union_isClosed_of_interior_empty (isClosed_biUnion_finset fun b _ ↦ hc b) (hi a), ih]

/-- A finite partition of a nonempty topological space into locally closed sets has a member
containing a nonempty open set. -/
lemma exists_nonempty_isOpen_subset_of_isLocallyClosed {X : Type*} [TopologicalSpace X]
    [Nonempty X] {n : ℕ} (s : Fin n → Set X) (hs : ∀ a, IsLocallyClosed (s a))
    (hU : ⋃ a, s a = Set.univ) :
    ∃ a, ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧ V ⊆ s a := by
  obtain ⟨a, ha⟩ : ∃ a, (interior (closure (s a))).Nonempty := by
    by_contra! h
    have h' := interior_iUnion_eq_empty_of_isClosed (fun a ↦ closure (s a))
      (fun _ ↦ isClosed_closure) h
    have : (⋃ a, closure (s a)) = Set.univ :=
      Set.eq_univ_of_univ_subset (hU ▸ Set.iUnion_mono fun _ ↦ subset_closure)
    rw [this, interior_univ] at h'
    exact Set.univ_nonempty.ne_empty h'
  obtain ⟨U, C, hUo, hCc, hsUC⟩ := hs a
  obtain ⟨x, hx⟩ := ha
  have hxs : x ∈ closure (s a) := interior_subset hx
  obtain ⟨y, hyW, hys⟩ := mem_closure_iff.1 hxs _ isOpen_interior hx
  refine ⟨a, interior (closure (s a)) ∩ U, isOpen_interior.inter hUo,
    ⟨y, hyW, (hsUC ▸ hys).1⟩, fun z ⟨hzW, hzU⟩ ↦ ?_⟩
  rw [hsUC]
  refine ⟨hzU, ?_⟩
  have : closure (s a) ⊆ C := closure_minimal (hsUC ▸ Set.inter_subset_right) hCc
  exact this (interior_subset hzW)

/-- On a nonempty scheme, some stratum of a stratification contains a nonempty open. -/
lemma exists_nonempty_opens_subset_stratum {X : Scheme.{u}} [Nonempty X]
    (S : Scheme.Stratification X) :
    ∃ a, ∃ V : X.Opens, (V : Set X).Nonempty ∧ (V : Set X) ⊆ S.stratum a := by
  obtain ⟨a, V, hV, hne, hsub⟩ := exists_nonempty_isOpen_subset_of_isLocallyClosed S.stratum
    S.isLocallyClosed_stratum S.iUnion_stratum_eq_univ
  exact ⟨a, ⟨V, hV⟩, hne, hsub⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- A complex all of whose cohomology sheaves vanish is zero. -/
lemma isZero_of_forall_isZero_homology {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (h : ∀ n, IsZero ((DerivedCategory.homologyFunctor _ n).obj K)) : IsZero K := by
  have : K.IsGE 0 := (DerivedCategory.isGE_iff K 0).2 fun n _ ↦ h n
  have : K.IsLE (-1) := (DerivedCategory.isLE_iff K (-1)).2 fun n _ ↦ h n
  exact DerivedCategory.TStructure.t.isZero K (-1) 0 (by lia)

omit [IsCommMonObj Λ] in
/-- Every complex of module objects on an empty scheme is zero. -/
lemma isZero_derivedCategory_of_isEmpty' {X : Scheme.{u}} [IsEmpty X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : IsZero K := by
  exact isZero_of_forall_isZero_homology Λ fun _ ↦ isZero_mod_of_isEmpty Λ _

/-- The derived pullback of a sheaf placed in degree `0` is the pullback, placed in degree
`0`. -/
noncomputable def leftDerivedUpperStarSingleIso {W X : Scheme.{u}} (g : W ⟶ X)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (L((g)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((g)^*⟦Λ⟧.obj F) :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ g).app _ ≪≫
    (((g)^*⟦Λ⟧).mapDerivedCategorySingleFunctor 0).app F

omit [IsCommMonObj Λ] in
/-- The shifted constructible sheaves `M[-n]` are bounded constructible complexes. -/
lemma boundedConstructible_singleFunctor_obj (X : Scheme.{u}) (n : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    boundedConstructible (condensedRingObj Λ X) ((DerivedCategory.singleFunctor _ n).obj M) := by
  refine ⟨⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩, fun i ↦ ?_⟩
  rcases lt_trichotomy i n with hi | rfl | hi
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isGE _ n i hi)
  · exact IsConstructibleModuleObject.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app M).symm hM
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isLE _ n i hi)

omit [IsCommMonObj Λ] in
/-- A constructible sheaf placed in degree `0` is bounded constructible. -/
lemma boundedConstructible_singleFunctor_zero_obj {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    boundedConstructible (condensedRingObj Λ X) ((DerivedCategory.singleFunctor _ 0).obj M) :=
  boundedConstructible_singleFunctor_obj Λ X 0 M hM

omit [IsCommMonObj Λ] in
/-- Along a commutative square `a ≫ f = b ≫ g`, if `g^* M` is pro-étale locally finitely
presented, so is `(a ≫ f)^* M`. -/
lemma isLocallyFinitelyPresented_upperStar_comp_of_comm [IsCommMonObj Λ] {P U W X : Scheme.{u}}
    {a : P ⟶ U} {b : P ⟶ W} {f : U ⟶ X} {g : W ⟶ X} (h : a ≫ f = b ≫ g)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ P) ((a ≫ f)^*⟦Λ⟧.obj M) :=
  (IsLocallyFinitelyPresented.upperStar Λ b hM).of_iso
    (((upperStarComp Λ b g).app M).symm ≪≫ (upperStarCongr Λ h.symm).app M)

end AlgebraicGeometry.ProEtale.CondensedRing
