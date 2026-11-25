/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.ModuleCompatibleFamilyPresheaf

/-! # A step of the compatible-family sheaf construction -/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

section

variable
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
  (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
  (φij : ∀ i j : I,
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))


private theorem local_section_ext
    (V : Opens X) (S : Sieve V) (hS : S ∈ Opens.grothendieckTopology X V)
    (i : I) (W : Opens X) (hi : W ≤ U i) (hWV : W ≤ V)
    (a b : (Fi i).val.obj (op (Over.mk (homOfLE hi))))
    (h : ∀ (Z : Opens X) (hZW : Z ≤ W) (_hf : S (homOfLE (hZW.trans hWV))),
      (Fi i).val.map (Over.homMk (homOfLE hZW) :
        Over.mk (homOfLE (hZW.trans hi)) ⟶ Over.mk (homOfLE hi)).op a =
        (Fi i).val.map (Over.homMk (homOfLE hZW) :
          Over.mk (homOfLE (hZW.trans hi)) ⟶ Over.mk (homOfLE hi)).op b) : a = b := by
  let O : Over (U i) := Over.mk (homOfLE hi)
  let T := (Sieve.overEquiv O).symm (S.pullback (homOfLE hWV))
  have hT := (Opens.grothendieckTopology X).overEquiv_symm_mem_over O _
    ((Opens.grothendieckTopology X).pullback_stable (homOfLE hWV) hS)
  apply (Fi i).isSheaf.isSeparated O T hT
  intro Z f hf
  exact h Z.left (leOfHom f.left) hf

private theorem family_coherent_of_local_gluing
    (V : Opens X) (S : Sieve V) (hS : S ∈ Opens.grothendieckTopology X V)
    (sf : Presieve.FamilyOfElements
      ((coherentOpenModulePresheaf X I U Fi φij).presheaf ⋙ forget _) S.arrows)
    (a : OpenModuleFamily X I U Fi V)
    (ha : ∀ (i : I) (W : Opens X) (hi : W ≤ U i) (hWV : W ≤ V)
      (Z : Opens X) (hZW : Z ≤ W) (hf : S (homOfLE (hZW.trans hWV))),
      (Fi i).val.map (Over.homMk (homOfLE hZW)).op (a i W hi hWV) =
        (sf (homOfLE (hZW.trans hWV)) hf).1 i Z (hZW.trans hi) le_rfl) :
    OpenModuleFamilyCoherent X I U Fi φij V a := by
  constructor
  · intro i W Z hi hWV hZW
    apply local_section_ext X I U Fi V S hS i Z (hZW.trans hi) (hZW.trans hWV)
    intro T hTZ hf
    let f : Over.mk (homOfLE (hZW.trans hi)) ⟶ Over.mk (homOfLE hi) :=
      Over.homMk (homOfLE hZW)
    let g : Over.mk (homOfLE (hTZ.trans (hZW.trans hi))) ⟶
        Over.mk (homOfLE (hZW.trans hi)) := Over.homMk (homOfLE hTZ)
    exact ((Fi i).val.map_comp_apply f.op g.op (a i W hi hWV)).symm.trans
      ((ha i W hi hWV T (hTZ.trans hZW) hf).trans
        (ha i Z (hZW.trans hi) (hZW.trans hWV) T hTZ hf).symm)
  · intro i j W hi hj hWV
    apply local_section_ext X I U Fi V S hS j W hj hWV
    intro T hTW hf
    have hn := PresheafOfModules.naturality_apply (φij i j).hom.val
      (Over.homMk (homOfLE hTW) :
        Over.mk (homOfLE (le_inf (hTW.trans hi) (hTW.trans hj))) ⟶
          Over.mk (homOfLE (le_inf hi hj))).op (a i W hi hWV)
    change (φij i j).hom.val.app
      (op (Over.mk (homOfLE (le_inf (hTW.trans hi) (hTW.trans hj)))))
        ((Fi i).val.map (Over.homMk (homOfLE hTW)).op (a i W hi hWV)) =
      (Fi j).val.map (Over.homMk (homOfLE hTW)).op
        ((φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj))))
          (a i W hi hWV)) at hn
    refine hn.symm.trans ?_
    exact (congrArg
      (fun s => (φij i j).hom.val.app
        (op (Over.mk (homOfLE (le_inf (hTW.trans hi) (hTW.trans hj))))) s)
      (ha i W hi hWV T hTW hf)).trans
        (((sf (homOfLE (hTW.trans hWV)) hf).2.2
          i j T (hTW.trans hi) (hTW.trans hj) le_rfl).trans
            (ha j W hj hWV T hTW hf).symm)

private theorem coherent_open_module_type_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      ((coherentOpenModulePresheaf X I U Fi φij).presheaf ⋙ forget _) := by
  classical
  intro V S hS sf hcompat
  have hlocal (i : I) : Presieve.IsSheaf ((Opens.grothendieckTopology X).over (U i))
      ((Fi i).val.presheaf ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (((sheafCompose _ (forget _)).obj ⟨(Fi i).val.presheaf, (Fi i).isSheaf⟩).property)
  have hex (i : I) (W : Opens X) (hi : W ≤ U i) (hWV : W ≤ V) :
      ∃ a : (Fi i).val.obj (op (Over.mk (homOfLE hi))),
        ∀ (Z : Opens X) (hZW : Z ≤ W)
          (hf : S (homOfLE (hZW.trans hWV))),
          (Fi i).val.map (Over.homMk (homOfLE hZW)).op a =
            (sf (homOfLE (hZW.trans hWV)) hf).1 i Z (hZW.trans hi) le_rfl := by
    let O : Over (U i) := Over.mk (homOfLE hi)
    let T := (Sieve.overEquiv O).symm (S.pullback (homOfLE hWV))
    have hT : T ∈ ((Opens.grothendieckTopology X).over (U i)) O :=
      (Opens.grothendieckTopology X).overEquiv_symm_mem_over O _
        ((Opens.grothendieckTopology X).pullback_stable (homOfLE hWV) hS)
    let t : Presieve.FamilyOfElements ((Fi i).val.presheaf ⋙ forget _) T.arrows :=
      fun Z f hf => (sf (f.left ≫ homOfLE hWV) hf).1
        i Z.left (leOfHom Z.hom) le_rfl
    have ht : t.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro Z Y f g hf
      dsimp [t]
      have hg := (Presieve.compatible_iff_sieveCompatible sf).mp hcompat
        (f.left ≫ homOfLE hWV) g.left hf
      have hh := congrArg
        (fun b : coherentOpenModuleSubmodule X I U Fi φij Y.left =>
          b.1 i Y.left (leOfHom Y.hom) le_rfl) hg
      change (sf (g.left ≫ (f.left ≫ homOfLE hWV)) _).1
        i Y.left (leOfHom Y.hom) le_rfl =
        (sf (f.left ≫ homOfLE hWV) hf).1
          i Y.left (leOfHom Y.hom) (leOfHom g.left) at hh
      have hr := (sf (f.left ≫ homOfLE hWV) hf).2.1
        i Z.left Y.left (leOfHom Z.hom) le_rfl (leOfHom g.left)
      change (sf ((g.left ≫ f.left) ≫ homOfLE hWV) _).1
        i Y.left (leOfHom Y.hom) le_rfl =
          (Fi i).val.map g.op
            ((sf (f.left ≫ homOfLE hWV) hf).1 i Z.left (leOfHom Z.hom) le_rfl)
      exact hh.trans hr.symm
    refine ⟨(hlocal i T hT).amalgamate t ht, ?_⟩
    intro Z hZW hf
    let f : Over.mk (homOfLE (hZW.trans hi)) ⟶ O := Over.homMk (homOfLE hZW)
    have hf' : T f := hf
    exact (hlocal i T hT).valid_glue ht f hf'
  choose a ha using hex
  have hcoh := family_coherent_of_local_gluing X I U Fi φij V S hS sf a ha
  refine ⟨⟨a, hcoh⟩, ?_, ?_⟩
  · intro W f hf
    apply Subtype.ext
    funext i Z hi hZW
    have hfZ := S.downward_closed hf (homOfLE hZW)
    have ha0 := ha i Z hi (hZW.trans (leOfHom f)) Z le_rfl hfZ
    have hh := (Presieve.compatible_iff_sieveCompatible sf).mp hcompat
      f (homOfLE hZW) hf
    have he := congrArg
      (fun b : coherentOpenModuleSubmodule X I U Fi φij Z => b.1 i Z hi le_rfl) hh
    have ha0' : a i Z hi (hZW.trans (leOfHom f)) =
        (sf (homOfLE (hZW.trans (leOfHom f))) hfZ).1 i Z hi le_rfl := by
      change (Fi i).val.map (𝟙 (op (Over.mk (homOfLE hi))))
        (a i Z hi (hZW.trans (leOfHom f))) = _ at ha0
      simpa using ha0
    exact ha0'.trans he
  · intro b hb
    apply Subtype.ext
    funext i W hi hWV
    apply local_section_ext X I U Fi V S hS i W hi hWV
    intro Z hZW hf
    rw [b.2.1, ha i W hi hWV Z hZW hf]
    have hh := hb (homOfLE (hZW.trans hWV)) hf
    exact congrArg
      (fun b : coherentOpenModuleSubmodule X I U Fi φij Z =>
        b.1 i Z (hZW.trans hi) le_rfl) hh

end

/-- Componentwise gluing makes the explicitly constructed small presheaf a sheaf.
Source: Stacks Project, Sheaves, Tags 00AL (first proof) and 00AM.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf-condition)

Proof: work through the shrinking equivalences. For a covering of V and a
compatible family of coherent families on its members, fix i and W contained
in U i and V. Its intersections with the covering members cover W in Over (U i).
The given families supply compatible local sections there, so the sheaf axiom
of Fi i yields a unique section on W. Define every component this way.
Restrictions agree by uniqueness: their values agree on the same induced cover.
For the overlap equations, naturality of each overlap morphism makes the two
candidate sections agree on the induced covering of the common subopen;
separation in Fi j makes them equal. This produces a coherent family on V.
It restricts to each given family by uniqueness in Fi i, and is itself unique
by separation in each Fi i. Transport this unique gluing through the shrinking
equivalences to obtain the sheaf axiom of the displayed presheaf. The argument
works for the empty cover and requires no cover hypothesis on U, no diagonal
law, and no cocycle law. -/
theorem small_coherent_open_module_isSheaf
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
  (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
  (φij : ∀ i j : I,
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    [∀ V : Opens X, Small.{max u v} (coherentOpenModuleSubmodule X I U Fi φij V)] :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (smallCoherentOpenModulePresheaf X I U Fi φij).presheaf  := by
  apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X)
    _ (forget _)
  rw [isSheaf_iff_isSheaf_of_type]
  apply Presieve.isSheaf_of_nat_equiv
    (fun {V} => (coherentOpenModuleShrinkEquiv X I U Fi φij V).symm.toEquiv)
    _ (coherent_open_module_type_isSheaf X I U Fi φij)
  intro V W f a
  apply (coherentOpenModuleShrinkEquiv X I U Fi φij V).injective
  change coherentOpenModuleShrinkEquiv X I U Fi φij V
    ((coherentOpenModuleShrinkEquiv X I U Fi φij V).symm
      ((coherentOpenModulePresheaf X I U Fi φij).map f.op a)) =
    coherentOpenModuleShrinkEquiv X I U Fi φij V
      ((smallCoherentOpenModulePresheaf X I U Fi φij).map f.op
        ((coherentOpenModuleShrinkEquiv X I U Fi φij W).symm a))
  rw [LinearEquiv.apply_symm_apply, smallCoherentOpenModulePresheaf_map_equiv,
    LinearEquiv.apply_symm_apply]

end AlgebraicGeometry
