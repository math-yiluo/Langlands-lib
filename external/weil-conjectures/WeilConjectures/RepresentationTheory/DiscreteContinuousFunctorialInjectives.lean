/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.GroupTheory.GroupAlgebraFunctorialInjectiveEmbeddings
import WeilConjectures.RepresentationTheory.OpenStabilizerAdjunction
import WeilConjectures.RepresentationTheory.RepresentationLiftedGroupAlgebraEquivalence

/-!
# Functorial injective embeddings of discrete continuous representations

Source: Stacks Project, Injectives, Tag 04JF, Lemma 19.3.1
(blueprint: lem-exc-rg-discrete-modules-functorial-injective-embeddings).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

private theorem transferEmbeddings
    {D : Type*} [Category* D] {M : Type*} [Category* M]
    (V : D ⥤ M) (U : M ⥤ D) (adj : V ⊣ U)
    [V.PreservesMonomorphisms] [V.Faithful]
    (J : M ⥤ M) (j : 𝟭 M ⟶ J)
    (hmono : ∀ X, Mono (j.app X)) (hinj : ∀ X, Injective (J.obj X)) :
    ∃ (jd : 𝟭 D ⟶ V ⋙ J ⋙ U),
      (∀ X, Mono (jd.app X)) ∧ ∀ X, Injective ((V ⋙ J ⋙ U).obj X) := by
  let jd : 𝟭 D ⟶ V ⋙ J ⋙ U :=
    { app := fun X ↦ adj.unit.app X ≫ U.map (j.app (V.obj X))
      naturality := by
        intro X Y f
        dsimp
        have hj : V.map f ≫ j.app (V.obj Y) = j.app (V.obj X) ≫ J.map (V.map f) :=
          j.naturality (V.map f)
        rw [← Category.assoc, ← adj.unit_naturality f, Category.assoc,
          ← U.map_comp, hj, U.map_comp, Category.assoc] }
  refine ⟨jd, ?_, fun X ↦ adj.map_injective _ (hinj _)⟩
  intro X
  have := hmono (V.obj X)
  have := hinj (V.obj X)
  exact (adj.injectivePresentationOfMap X
    { J := J.obj (V.obj X), f := j.app (V.obj X) }).mono

/-- (blueprint: lem-exc-rg-discrete-modules-functorial-injective-embeddings)
For any ring `R` and topological group `G`, the category of discrete continuous
representations has functorial injective embeddings. Source: Stacks Project,
Injectives, Tag 04JF, Lemma 19.3.1.

Proof: first use functorial injective embeddings for modules over the group ring `R[G]`
(`lem-exc-rg-group-algebra-functorial-injective-embeddings`). The fully faithful inclusion
of the open-stabilizer subcategory preserves monomorphisms and has the open-stabilizer
submodule functor as its right adjoint (`lem-exc-rg-open-stabilizer-adjoint`). Apply
`lem-exc-rg-adjoint-transfer-functorial-injectives` to these functors and the group-ring
embedding functor. It gives an endofunctor `J`, a natural transformation from the identity,
monic components, and injective values, as asserted. -/
theorem discreteContinuousRep_functorialInjectiveEmbeddings_of_topologicalGroup
    (R : Type u) [Ring R] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ (J : DiscreteContinuousRep.{u, v, max u v w} R G ⥤
          DiscreteContinuousRep.{u, v, max u v w} R G)
      (j : 𝟭 (DiscreteContinuousRep.{u, v, max u v w} R G) ⟶ J),
      (∀ M, Mono (j.app M)) ∧ ∀ M, Injective (J.obj M) := by
  obtain ⟨E⟩ := representation_liftedGroupAlgebra_equivalence.{u, v, w} R G
  obtain ⟨Jm, jm, hjm, hJm⟩ :=
    ModuleCat.groupAlgebra_functorialInjectiveEmbeddings (G := G) (ULift.{w} R)
  obtain ⟨jr, hjr, hJr⟩ := transferEmbeddings
    E.functor E.inverse E.toAdjunction Jm jm hjm hJm
  obtain ⟨_, hfaithful, hmono, U, adj, _⟩ :=
    ModuleCat.openStabilizerAdjunction.{u, v, max u v w} R G
  let V := ModuleCat.forgetDiscreteGModule.{u, v, max u v w} R G
  let : V.Faithful := hfaithful
  let : V.PreservesMonomorphisms := ⟨fun f _ ↦ hmono f inferInstance⟩
  obtain ⟨jd, hjd, hJd⟩ := transferEmbeddings
    V U adj (E.functor ⋙ Jm ⋙ E.inverse) jr hjr hJr
  exact ⟨V ⋙ (E.functor ⋙ Jm ⋙ E.inverse) ⋙ U, jd, hjd, hJd⟩

end Rep
