/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Sheaves.Over

/-! # Integer extensions by zero embed in the constant integer sheaf

Source: Stacks Project, Cohomology, Lemma 02UX, third paragraph of the proof.
(blueprint: lem-sc-abelian-integer-extension-mono).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace TopCat

private noncomputable def integerRestrictionIso (X : TopCat.{u}) (U : Opens X) :
    (constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ≅
    TopCat.Sheaf.abelianOpenRestriction U
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) := by
  let J := Opens.grothendieckTopology X
  let K := J.over U
  let A := AddCommGrpCat.{u}
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  let G := U.overEquivalence.inverse
  let e : constantSheaf K A ⋙ U.sheafEquivOver.functor ≅
      constantSheaf (Opens.grothendieckTopology U) A :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Functor.const (Over U)ᵒᵖ)
        ((G.pushforwardContinuousSheafificationCompatibility A
          (Opens.grothendieckTopology U) K).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ G.op)
        (presheafToSheaf (Opens.grothendieckTopology U) A)
  exact (e.app M).symm ≪≫ U.sheafEquivOver.functor.mapIso
    ((J.overPullbackConstantSheafIso A U).app M).symm

/-- The integer extension by zero on any open embeds in the constant integer sheaf.

Source: Stacks Project, Cohomology, Lemma 02UX
(label `lemma-vanishing-generated-one-section`), the assertion that the kernel
of a one-section presentation is a subsheaf of the constant integer sheaf.

Proof:
1. Restriction of the constant integer sheaf on X to U is the constant integer
   sheaf on U: both are the sheaf of locally constant integer-valued functions.
   This identification commutes with the germ of each constant section.
2. Apply extension by zero to this identification, and then the counit
   j_! j^* Z_X → Z_X. This gives the required morphism.
3. At a point in U, the extension-by-zero stalk and restriction-stalk
   identifications turn this map into the identity of the integer stalk.
   Outside U its source stalk is zero. All stalk maps are therefore injective,
   and the stalkwise criterion for monomorphisms proves that the map is monic.
   No compactness is used; U = ∅ gives the zero-source map, and U = X gives
   the identity up to the canonical identifications.
(blueprint: lem-sc-abelian-integer-extension-mono). -/
theorem abelianIntegerExtension_exists_mono (X : TopCat.{u}) (U : Opens X) :
    ∃ ι : (TopCat.Sheaf.abelianOpenExtensionByZero U).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)), Mono ι := by
  classical
  let C := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let e := integerRestrictionIso X U
  let ε := TopCat.Sheaf.abelianOpenCounit U C
  have hε : Mono ε := by
    apply (TopCat.Presheaf.mono_iff_stalk_mono ε).2
    intro x
    obtain ⟨a, _, _, hout, hεst⟩ := TopCat.Sheaf.abelianOpenExtensionByZero_stalks X U
    by_cases hx : x ∈ U
    · obtain ⟨r, _, hr⟩ := hεst C ⟨x, hx⟩
      have hcomp : Mono ((a ⟨x, hx⟩ (TopCat.Sheaf.abelianOpenRestriction U C)).hom ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ε.hom) := by
        rw [hr]
        infer_instance
      let _ := hcomp
      rw [← mono_comp_iff_of_isIso
        (a ⟨x, hx⟩ (TopCat.Sheaf.abelianOpenRestriction U C)).hom]
      exact hcomp
    · exact mono_of_source_iso_zero _
        (hout (TopCat.Sheaf.abelianOpenRestriction U C) x hx).isoZero
  let _ := hε
  refine ⟨(TopCat.Sheaf.abelianOpenExtensionByZero U).map e.hom ≫ ε, ?_⟩
  infer_instance

end TopCat
