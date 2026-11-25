/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.ConstantSubsheafPositiveRefinementFactor

/-! # Refinement of compact-open integer components -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Refine an arbitrary finite compact-open component map into positive components,
retaining a factorization of the given map. No epimorphy assumption or conclusion is used.
Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph.
https://stacks.math.columbia.edu/tag/0A38
(blueprint: lem-sc-constant-subsheaf-positive-refinement)

Proof: Compose each coproduct injection with g and evaluate on the canonical unit section.
Under ι and isoC, this section is a locally constant integer function on U i. Compactness
makes its range finite. Its fibres are clopen in U i, hence open in X and compact in X.
Restrict the original section to each nonzero fibre. Negate it on negative fibres, and
label the resulting section by the positive absolute value. Integer multiplication by
this section gives a map from the constant presheaf; sheafification and the extension by
zero counit give the required component f. Naturality of the unit proves the value formula.

For each original domain, use its finite clopen partition to split the extension by zero
of its constant sheaf into the coproduct of the extensions on its fibres. Explicitly,
restrict locally constant sections to the fibres; inverse maps extend sections across
the complementary clopen pieces by zero and add them. These maps descend through
sheafification and are inverse, as can be checked locally on the partition. Send each
nonzero fibre to its new coproduct summand with the sign of its original value, and send
zero fibres to zero. This defines the component of l on each old summand. Its composite
with Sigma.desc f agrees with the old component on each fibre: the two sign changes
cancel, and on a zero fibre monicity of ι forces the old section to vanish. Maps out of
the constant integer sheaf are determined by the unit section (by sheafification and
integer multiplication); the same holds for its open extension by zero. Thus the maps
agree on each fibre and therefore globally. Coproduct extensionality gives l ≫ Sigma.desc f
= g. Enumerate the finite nonzero fibres by Fin n. If there are none, the old components
are zero and the zero map to the empty coproduct gives the same factorization. -/
theorem constantSubsheaf_positive_refinement
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (m : ℕ) (U : Fin m → Opens X)
    (hU : ∀ i, IsCompact (U i : Set X))
    (g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K) :
    ∃ (n : ℕ) (A : Fin n → Opens X),
      (∀ i, IsCompact (A i : Set X)) ∧
      ∃ (c : Fin n → ℕ), (∀ i, 0 < c i) ∧
      ∃ (f : ∀ i, (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ K),
        (∃ l : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶
          (∐ fun i => (abelianOpenExtensionByZero (A i)).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))),
          l ≫ Sigma.desc f = g) ∧ ∀ i,
        (ι ≫ isoC.hom).hom.app (op (A i))
      ((f i).hom.app (op (A i)) (abelianOpenExtensionSection (A i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1)))) =
      (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op (A i)) (ULift.up (c i : ℤ)) := by
  obtain ⟨d, _⟩ := positive_refinement_data X K C ι isoC m U hU g
  obtain ⟨l, hl⟩ := positive_refinement_factor X K C ι isoC m U g d
  exact ⟨d.n, d.A, d.hA, d.c, d.hc, d.f, ⟨l, hl⟩, d.hv⟩

end TopCat.Sheaf
