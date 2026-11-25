/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.RepresentationTheory.DiscreteContinuousFunctorialInjectives
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Injectives and left exact invariants for discrete integer representations

Source: Stacks Project, Injectives, Tag 04JF; Etale Cohomology, Tag 0DVG.
(blueprint: lem-sc-discrete-integer-invariants-infrastructure).
-/

@[expose] public section

universe u v w s

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- Discrete integer representations have enough injectives, and their invariant functor
preserves finite limits, after transport along any equivalence of categories.

Source: Stacks Project, Injectives, Tag 04JF; Etale Cohomology, Tag 0DVG,
final profinite comparison.
(blueprint: lem-sc-discrete-integer-invariants-infrastructure).

Proof: The functorial injective-embedding theorem for arbitrary rings gives a monomorphism
M to J(M), with J(M) injective, in the discrete representation category. These are
injective presentations. EnoughInjectives.of_equivalence transports them across E.
The functor giving a module its trivial action lands in discrete representations, since
every element is fixed by the whole group. Restrict the Mathlib trivial-action/invariants
adjunction along the fully faithful inclusion of the discrete subcategory. Consequently
its invariants functor is a right adjoint and preserves limits. The equivalence E and
the underlying additive-group functor also preserve limits, so their composite preserves
finite limits. Neither compactness nor an abelian structure on A is needed here. -/
theorem discreteInteger_invariants_infrastructure
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    : EnoughInjectives A ∧ PreservesFiniteLimits
    (E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat) := by
  classical
  obtain ⟨J, j, hmono, hinj⟩ :=
    discreteContinuousRep_functorialInjectiveEmbeddings_of_topologicalGroup.{0, u, s} ℤ G
  let : EnoughInjectives (DiscreteContinuousRep.{0, u, max u s} ℤ G) :=
    ⟨fun M ↦ ⟨⟨J.obj M, hinj M, j.app M, hmono M⟩⟩⟩
  refine ⟨EnoughInjectives.of_equivalence E.functor, ?_⟩
  let P : ObjectProperty (Rep.{max u s} ℤ G) :=
    fun X ↦ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x}
  let L : ModuleCat.{max u s} ℤ ⥤ P.FullSubcategory :=
    P.lift (trivialFunctor ℤ G) (by
      intro X x
      change IsOpen {g : G | x = x}
      simp)
  let R : P.FullSubcategory ⥤ ModuleCat.{max u s} ℤ := P.ι ⋙ invariantsFunctor ℤ G
  have adj : L ⊣ R :=
    (invariantsAdjunction ℤ G).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful (𝟭 (ModuleCat.{max u s} ℤ)))
      P.fullyFaithfulι (Iso.refl _) (Iso.refl _)
  let : R.IsRightAdjoint := adj.isRightAdjoint
  change PreservesFiniteLimits (E.functor ⋙ R ⋙
    forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat)
  infer_instance

end Rep
