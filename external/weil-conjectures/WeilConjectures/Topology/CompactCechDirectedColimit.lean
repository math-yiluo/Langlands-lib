/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Spaces
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.Topology.AbelianSectionsFilteredColimit
import all WeilConjectures.CategoryTheory.DirectedColimitHomology

/-!
# Directed colimits and finite compact Čech complexes

Source: Stacks Project, Cohomology, Tag 01FF, the comparison of Čech complexes
(blueprint: lem-sc-compact-cech-cohomology-directed-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- Source: Stacks Project, Algebra, Tag 00DB. Taking the three adjacent terms
preserves colimits degreewise; compose with short-complex homology preservation. -/
private theorem complexHomologyPreserves
    {I : Type u} [SmallCategory I] [IsFiltered I] (p : ℕ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p) := by
  have : PreservesColimitsOfShape I
      (ShortComplex.homologyFunctor AddCommGrpCat.{u}) :=
    CategoryTheory.shortComplexHomologyPreserves
  have : PreservesColimitsOfShape I
      (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p) := by
    refine ⟨fun {F} ↦ ⟨fun {s} hs ↦ ⟨?_⟩⟩⟩
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves
        (HomologicalComplex.eval _ _ ((ComplexShape.up ℕ).prev p)) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ p) hs
    · exact isColimitOfPreserves
        (HomologicalComplex.eval _ _ ((ComplexShape.up ℕ).next p)) hs
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso AddCommGrpCat.{u} (ComplexShape.up ℕ) p).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Finite compact Čech cohomology preserves an existing directed colimit of abelian
sheaves on a space with a compact open basis and compact intersections.

Source: Stacks Project, Cohomology, Lemma 01FF, the Čech-complex comparison.
(blueprint: lem-sc-compact-cech-cohomology-directed-colimit).

Proof: the compact-basis and compact-intersection hypotheses ensure that sections on
every compact chosen intersection preserve the directed colimit, by 01FF's degree-zero
argument. In degree k the tuple index Fin (k+1) → T is finite, so its product commutes
with filtered colimits of abelian groups. The resulting identifications commute with
restriction maps and finite alternating sums, and hence with all differentials and
cocone maps. Colimits of complexes are calculated degreewise. Exactness of filtered
colimits of abelian groups identifies the homology of this colimit complex with the
colimit of its homology groups. The identification respects the cocone legs, proving
preservation of the given colimit. This works also for the empty covering, where each
term is the zero group, and for the empty open. No injectivity of the diagram objects
is used. -/
theorem compact_siteCech_cohomology_preserves_directedColimit
    (X : Type u) [TopologicalSpace X]
    (hbas : ∀ (V : Set X), IsOpen V → ∀ x ∈ V, ∃ W : Set X, IsOpen W ∧
      IsCompact W ∧ x ∈ W ∧ W ⊆ V)
    (hint : ∀ (V W : Set X), IsOpen V → IsOpen W → IsCompact V → IsCompact W →
      IsCompact (V ∩ W))
    {T : Type u} [Finite T] {U : TopologicalSpace.Opens X}
    {f : T → TopologicalSpace.Opens X} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom)
    (hcompact : ∀ (p : ℕ) (a : Fin (p + 1) → T),
      IsCompact ((S.W p a : TopologicalSpace.Opens X) : Set X))
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p : ℕ) :
    PreservesColimit F
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        S.cohomologyFunctor p) := by
  classical
  let C := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    S.complexFunctor
  have : PreservesColimitsOfShape I C := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval C
    intro q
    let A := Fin (q + 1) → T
    let G : Discrete A ⥤ (TopologicalSpace.Opens X)ᵒᵖ :=
      Discrete.functor fun a ↦ Opposite.op (S.W q a)
    let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (Functor.whiskeringLeft (Discrete A) (TopologicalSpace.Opens X)ᵒᵖ
        AddCommGrpCat.{u}).obj G
    have : PreservesColimitsOfShape I E :=
      preservesColimitsOfShape_of_evaluation E I (fun a ↦ by
        exact TopCat.abelianSections_preservesDirectedColimits
          X hbas hint I (S.W q a.as) (hcompact q a.as))
    have : HasFiniteBiproducts AddCommGrpCat.{u} := Abelian.hasFiniteBiproducts
    have : PreservesColimitsOfShape I
        (lim (J := Discrete A) (C := AddCommGrpCat.{u})) :=
      preservesColimitsOfShape_of_natIso (HasBiproductsOfShape.colimIsoLim (J := A))
    let e : C ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) q ≅ E ⋙ lim :=
      NatIso.ofComponents (fun H ↦
        (AddCommGrpCat.HasLimit.productLimitCone
          (fun a : A ↦ H.obj.obj (Opposite.op (S.W q a)))).isLimit.conePointUniqueUpToIso
            (productIsProduct _) ≪≫ Pi.isoLimit (E.obj H)) (by
        intro H H' φ
        apply limit.hom_ext
        rintro ⟨a⟩
        simp only [Functor.comp_map, Iso.trans_hom, Category.assoc, lim_map, limMap_π,
          Pi.isoLimit_hom_π, Pi.isoLimit_hom_π_assoc]
        have hp (H : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
            ((AddCommGrpCat.HasLimit.productLimitCone
              (fun a : A ↦ H.obj.obj (Opposite.op (S.W q a)))).isLimit.conePointUniqueUpToIso
                (productIsProduct _)).hom ≫ Pi.π _ a =
              AddCommGrpCat.ofHom
                (Pi.evalAddMonoidHom (fun a : A ↦ H.obj.obj (Opposite.op (S.W q a))) a) :=
          IsLimit.conePointUniqueUpToIso_hom_comp
            (AddCommGrpCat.HasLimit.productLimitCone
              (fun a : A ↦ H.obj.obj (Opposite.op (S.W q a)))).isLimit
            (productIsProduct _) (Discrete.mk a)
        erw [hp H', ← Category.assoc, hp H]
        rfl)
    exact preservesColimitsOfShape_of_natIso e.symm
  have := complexHomologyPreserves (I := I) p
  change PreservesColimit F
    (C ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p)
  infer_instance

end CategoryTheory.Sheaf
