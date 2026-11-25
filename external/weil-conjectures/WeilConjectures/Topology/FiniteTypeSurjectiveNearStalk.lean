/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.Topology.FiniteTypeLocalCoefficients

/-!
# Surjectivity near a stalk for a finite type target

Source: Stacks Project, Sheaves of Modules, Lemma 17.9.4, Tag 01B8
(blueprint: lem-weil-pbc-module-finite-type-surjective-on-stalk).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

private theorem lift_section_near (X : RingedSpace.{u})
    {G F : SheafOfModules.{u} (moduleRings X)} (φ : G ⟶ F) (x : X)
    (hφ : Function.Surjective ((moduleStalkFunctor X x).map φ))
    (V : Opens X) (hx : x ∈ V) (s : F.val.obj (op V)) :
    ∃ (U : Opens X) (hU : U ≤ V), x ∈ U ∧
      ∃ g : G.val.obj (op U), φ.val.app (op U) g =
        F.val.map (homOfLE hU).op s := by
  obtain ⟨m, hm⟩ := hφ (TopCat.Presheaf.germ F.val.presheaf V x hx s)
  obtain ⟨W, hWV, hxW, g, hg⟩ := TopCat.Presheaf.exists_le_germ_eq G.val.presheaf m hx
  have he : TopCat.Presheaf.germ F.val.presheaf W x hxW (φ.val.app (op W) g) =
      TopCat.Presheaf.germ F.val.presheaf V x hx s := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map φ.val) m = _ at hm
    rw [← hg] at hm
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hm
    exact hm
  obtain ⟨U, hxU, iW, iV, heq⟩ := TopCat.Presheaf.germ_eq F.val.presheaf x hxW hx _ _ he
  refine ⟨U, leOfHom iV, hxU, G.val.map iW.op g, ?_⟩
  rw [PresheafOfModules.naturality_apply]
  exact heq

/-- A morphism to a finite type module sheaf on a ringed space which is surjective at one
stalk is surjective as a sheaf map on an open neighbourhood of that point. The conclusion
spells out sheaf surjectivity as local lifting on an open cover, as the node does.

Source: Stacks Project, Sheaves of Modules, Lemma 17.9.4, Tag 01B8
(blueprint: lem-weil-pbc-module-finite-type-surjective-on-stalk).

Proof:
1. By def-weil-pbc-module-finite-type-presentation (1), choose finitely many
sections generating `F` on a neighbourhood `U₀` of `x`, or equivalently an
epimorphism from a finite free module sheaf to `F` there.
2. Lift their germs using surjectivity at `x`. By def-weil-pbc-module-stalk,
each lift is represented by a section near `x`, and equality of germs holds on
a smaller neighbourhood. Intersect these finitely many neighbourhoods with `U₀`
to obtain one neighbourhood `U` where every generator has a lift in `G`.
3. For any section over an open `W ≤ U`, the generating epimorphism gives local
coefficients on a cover of `W`, by lem-weil-pbc-ringed-space-module-exactness-local-lifting (1).
Substitute the lifted generators into those linear combinations. Linearity of
`φ` (situation-conventions) makes them local lifts of the section.
With no generators take `U = U₀`; all local sections vanish and their lifts are zero. -/
theorem exists_surjective_neighbourhood_of_surjective_stalk (X : RingedSpace.{u})
    {G F : SheafOfModules.{u} (moduleRings X)} (φ : G ⟶ F) (x : X) [F.IsFiniteType]
    (hφ : Function.Surjective ((moduleStalkFunctor X x).map φ)) :
    ∃ U : Opens X, x ∈ U ∧
      ∀ (W : Opens X), W ≤ U → ∀ t : F.val.obj (op W),
        ∃ (I : Type u) (V : I → Opens X) (hV : ∀ i, V i ≤ W)
          (g : ∀ i, G.val.obj (op (V i))),
          (⨆ i, V i) = W ∧
            ∀ i, φ.val.app (op (V i)) (g i) =
              F.val.map (homOfLE (hV i)).op t := by
  classical
  obtain ⟨U₀, hx₀, n, s, hs⟩ := exists_finite_type_local_coefficients X F x
  choose V hV hxV g hg using fun j ↦ lift_section_near X φ x hφ U₀ hx₀ (s j)
  let U : Opens X := U₀ ⊓ ⨅ j, V j
  have hUU₀ : U ≤ U₀ := inf_le_left
  have hUV (j : Fin n) : U ≤ V j := inf_le_right.trans (iInf_le V j)
  have hxU : x ∈ U := by
    refine ⟨hx₀, ?_⟩
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV
  let l (j : Fin n) : G.val.obj (op U) := G.val.map (homOfLE (hUV j)).op (g j)
  have hl (j : Fin n) : φ.val.app (op U) (l j) =
      F.val.map (homOfLE hUU₀).op (s j) := by
    dsimp [l]
    rw [PresheafOfModules.naturality_apply, hg j]
    rw [← PresheafOfModules.map_comp_apply]
    rfl
  refine ⟨U, hxU, ?_⟩
  intro W hW t
  choose A hA hyA a ha using fun y : W ↦ hs W (hW.trans hUU₀) t y.val y.property
  refine ⟨W, A, hA, fun y ↦ ∑ j, a y j •
    G.val.map (homOfLE ((hA y).trans hW)).op (l j), ?_, ?_⟩
  · apply le_antisymm (iSup_le hA)
    intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyA ⟨y, hy⟩⟩
  · intro y
    rw [ha y, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul, PresheafOfModules.naturality_apply, hl j]
    rw [← PresheafOfModules.map_comp_apply]
    rfl

end AlgebraicGeometry.RingedSpace
