/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Compactness.Compact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.Topology.AbelianSectionsFilteredColimit
import WeilConjectures.Topology.DirectedInjectiveDerivedSectionsAcyclic

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace TopCat

/-! # Cohomology commutes with filtered colimits on quasi-compact spaces
Source: literature/stacks-project/cohomology.tex, Lemma 01FF
(blueprint: lem-sc-topological-filtered-cohomology).
-/

/-- On a space with a quasi-compact open basis whose pairwise intersections are
quasi-compact, cohomology over a quasi-compact open commutes with directed colimits.

Source: literature/stacks-project/cohomology.tex, Tag 01FF,
lemma-quasi-separated-cohomology-colimit (abelian sheaves: constant ring sheaf ℤ).
(blueprint: lem-sc-topological-filtered-cohomology).

Proof:
1. `abelianSections_preservesDirectedColimits` proves degree-zero preservation by
   stalk colimits, finite compact refinements, eventual equality, and sheaf gluing.
2. Induct on the derived degree. At zero use `rightDerivedZeroIsoSelf`. At the
   successor use `preservesColimitsOfShape_rightDerived_succ`, which packages
   functorial injective embeddings, exact filtered colimits, and the natural long
   exact sequences. Its acyclicity premise is precisely
   `directedInjective_isZero_rightDerived_sections` on the compact open in question.
3. `nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived` identifies the evaluated
   Ext cohomology functor naturally with derived sections. Transport the colimit
   universal property along this isomorphism and identify the resulting universal
   comparison with the canonical map in the statement. -/
theorem topological_filtered_cohomology
    (X : Type u) [TopologicalSpace X]
    (hbas : ∀ (U : Set X), IsOpen U → ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧
      IsCompact V ∧ x ∈ V ∧ V ⊆ U)
    (hint : ∀ (U V : Set X), IsOpen U → IsOpen V → IsCompact U → IsCompact V →
      IsCompact (U ∩ V))
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u})
    (q : ℕ) (U : TopologicalSpace.Opens X) (hU : IsCompact (U : Set X))
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u})] :
    IsIso (colimit.desc
      (F ⋙ CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q ⋙
        (evaluation (Opens X)ᵒᵖ (AddCommGrpCat.{u})).obj (op U))
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q ⋙
        (evaluation (Opens X)ᵒᵖ (AddCommGrpCat.{u})).obj (op U)).mapCocone
        (colimit.cocone F))) := by
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  have hΓ : PreservesColimitsOfShape I Γ :=
    abelianSections_preservesDirectedColimits X hbas hint I U hU
  have hderived (n : ℕ) : PreservesColimitsOfShape I (Γ.rightDerived n) := by
    induction n with
    | zero =>
        exact preservesColimitsOfShape_of_natIso Γ.rightDerivedZeroIsoSelf.symm
    | succ n hn =>
        let := hn
        apply Γ.preservesColimitsOfShape_rightDerived_succ I n
        intro J hJ
        exact directedInjective_isZero_rightDerived_sections X hbas hint I J hJ U hU n
  let := hderived q
  obtain ⟨e⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    (Opens.grothendieckTopology X) U q
  have hc := IsColimit.mapCoconeEquiv e.symm
    (isColimitOfPreserves (Γ.rightDerived q) (colimit.isColimit F))
  exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.mp ⟨hc⟩

end TopCat
