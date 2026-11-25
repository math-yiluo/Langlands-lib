/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.NestedSliceExtensionStalks
import WeilConjectures.Topology.ConstantIntegerOpenExtensionComparison

/-! # Inclusion between constant integer extensions on nested opens

Source: Stacks Project, Cohomology, Lemma 0A38, final paragraph; Sheaves, Lemma 00A5
(blueprint: lem-sc-abelian-integer-open-inclusion).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- The nested-open inclusion is the identity on stalks inside the smaller open.

Source: Stacks Project, Cohomology, Lemma 0A38, final paragraph, and Sheaves, Lemma 00A5.
Proof: identify both extensions with the sheafifications of the slice extension
presheaves of the constant integer sheaf C on X, using the constant-integer open-extension
comparison. Over an open W, the presheaf map sends the summand indexed by W → V to the
summand indexed by the composite W → V → U, identically on C(W). This is natural since
restriction sends each summand to the corresponding composite index and restricts its
section. If W is contained in V, both sums have exactly one summand, and the map is the
identity on C(W). For a point in V, neighborhoods contained in V are cofinal, so this
presheaf map induces a stalk isomorphism. Sheafification preserves stalks and their maps;
conjugating the sheafified map by the two open-extension comparisons gives f with the
claimed stalk isomorphisms. For V empty the condition is vacuous; for V=U the index map
is identity. This is the direct-sum construction of the nested-open arrow in 0A38.
(blueprint: lem-sc-abelian-integer-open-inclusion). -/
theorem abelianIntegerOpen_exists_inclusion
    (X : TopCat.{u}) (U V : Opens X) (hVU : V ≤ U) :
    ∃ f : (abelianOpenExtensionByZero V).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶
      (abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))),
      ∀ x : X, x ∈ V →
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) := by
  classical
  let C := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  obtain ⟨g, hg⟩ := nested_slice_extension_stalks C U V hVU
  obtain ⟨eV⟩ := TopCat.constant_integer_open_extension_comparison X V
  obtain ⟨eU⟩ := TopCat.constant_integer_open_extension_comparison X U
  let sg := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map g
  refine ⟨eV.hom ≫ sg ≫ eU.inv, ?_⟩
  intro x hx
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : IsIso (S.map g) := hg x hx
  have : IsIso (S.map (toSheafify (Opens.grothendieckTopology X)
      ((siteExtensionByZeroPresheaf V).obj (C.over V).obj))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  have : IsIso (S.map (toSheafify (Opens.grothendieckTopology X)
      ((siteExtensionByZeroPresheaf U).obj (C.over U).obj))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  have hnat := congrArg (fun f => S.map f)
    (toSheafify_naturality (Opens.grothendieckTopology X) g)
  rw [Functor.map_comp, Functor.map_comp] at hnat
  have : IsIso (S.map sg.hom) := by
    have hcomp : IsIso (S.map
        (toSheafify (Opens.grothendieckTopology X)
          ((siteExtensionByZeroPresheaf V).obj (C.over V).obj)) ≫ S.map sg.hom) := by
      rw [← hnat]
      infer_instance
    exact IsIso.of_isIso_comp_left (S.map
      (toSheafify (Opens.grothendieckTopology X)
        ((siteExtensionByZeroPresheaf V).obj (C.over V).obj))) (S.map sg.hom)
  change IsIso (S.map (eV.hom.hom ≫ sg.hom ≫ eU.inv.hom))
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance


end TopCat.Sheaf
