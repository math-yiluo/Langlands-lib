/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import Mathlib.Algebra.Category.Grp.Zero
import all WeilConjectures.Topology.AbelianSheafLocalIntegerGenerator

/-! # ConstantSubsheafQuotientGluing

Source: Stacks Project, Cohomology, Lemma 0A38
(blueprint: lem-sc-constant-subsheaf-quotient-gluing).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

-- Strengthen the local generator construction from germ values to values on every subopen.
private theorem integerExtension_of_section
    (X : TopCat.{u}) (F : Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) (s : F.obj.obj (op U)) :
    ∃ f : (abelianOpenExtensionByZero U).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F,
      ∀ (V : Opens X) (hV : V ≤ U), f.hom.app (op V)
        (abelianOpenExtensionSection U
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) V hV
          ((toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map U.inclusion').obj V)) (ULift.up 1))) =
          F.obj.map (homOfLE hV).op s := by
  classical
  let H := abelianOpenRestriction U F
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let J := Opens.grothendieckTopology ((Opens.toTopCat X).obj U)
  let P : TopCat.Presheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
    (Functor.const _).obj Z
  have image_le (V : Opens ((Opens.toTopCat X).obj U)) :
      U.isOpenEmbedding.functor.obj V ≤ U := by
    rintro y ⟨z, hz, rfl⟩
    exact z.property
  let η : P ⟶ H.obj :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦ z.down • F.obj.map (homOfLE (image_le V.unop)).op s
          map_zero' := by simp
          map_add' := by intros; simp [add_zsmul] }
      naturality := fun V W f ↦ by
        ext z
        dsimp [H, abelianOpenRestriction, abelianOpenRestrictionPresheaf, P]
        rw [map_zsmul, ← AddCommGrpCat.comp_apply, ← F.obj.map_comp]
        rfl }
  let G := (constantSheaf J AddCommGrpCat.{u}).obj Z
  let α : G ⟶ H := ObjectProperty.homMk (sheafifyLift J η H.property)
  let f := (abelianOpenExtensionByZero U).map α ≫ abelianOpenCounit U F
  refine ⟨f, ?_⟩
  intro V hV
  let V' := (Opens.map U.inclusion').obj V
  let one : G.obj.obj (op V') := (toSheafify J P).app (op V') ⟨1⟩
  have hh := TopCat.extensionSection_naturality U G H α V hV
  have hc := TopCat.extensionSection_counit U F V hV
  have ha := congr_app (toSheafify_sheafifyLift J η H.property) (op V')
  change (toSheafify J P).app (op V') ≫ α.hom.app (op V') = η.app (op V') at ha
  have hv := openImage_preimage_eq U V hV
  have hs :
      F.obj.map (homOfLE (image_le V')).op ≫
        eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W)) hv) =
        F.obj.map (homOfLE hV).op := by
    have ht := congrArg op hv
    have hm : F.obj.map (eqToHom ht) =
        eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W)) hv) :=
      eqToHom_map F.obj ht
    rw [← hm, ← F.obj.map_comp]
    congr 1
  change (abelianOpenExtensionSection U G V hV ≫
    ((abelianOpenExtensionByZero U).map α).hom.app (op V) ≫
    (abelianOpenCounit U F).hom.app (op V)) one = _
  rw [← Category.assoc, ← hh, Category.assoc, hc]
  change ((toSheafify J P).app (op V') ≫ α.hom.app (op V') ≫ _) ⟨1⟩ = _
  rw [← Category.assoc]
  erw [ha]
  change (eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W)) hv))
    ((1 : ℤ) • F.obj.map (homOfLE (image_le V')).op s) = _
  rw [one_zsmul]
  change (F.obj.map (homOfLE (image_le V')).op ≫ _) s = _
  exact congrArg (fun g ↦ g s) hs

/-- Source: Stacks Project, Cohomology, Lemma 0A38, final paragraph.
Proof: The opens with label b+1 together with the lower-label union cover iSup A,
since every positive label is at most b+1. On the top opens the sections s i agree
on intersections: apply the monomorphism into the constant integer sheaf and use
naturality of the constant section. Their images under π therefore glue on the top
union. The sheaf Q restricted to the lower union is zero, because all its stalks
there vanish. Consequently those images agree with zero on overlaps with the lower
union. Glue with zero to obtain a section on iSup A. Use the constant-sheaf
adjunction to define a morphism on the restriction, then send each open-slice
summand of the extension presheaf by restriction of that morphism and apply
sheafifyLift. On each A i with top label its unit section has the stated image.
Empty unions and an absent top layer give the zero morphism and vacuous equations.
(blueprint: lem-sc-constant-subsheaf-quotient-gluing). -/
theorem constantSubsheaf_quotient_gluing
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (n : ℕ) (A : Fin n → Opens X) (c : Fin n → ℕ)
    (s : ∀ i, K.obj.obj (op (A i)))
    (hvalue : ∀ i, (ι ≫ isoC.hom).hom.app (op (A i)) (s i) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op (A i)) (ULift.up (c i : ℤ)))
    (b : ℕ) (hc : ∀ i, 0 < c i ∧ c i ≤ b + 1)
    (Q : Sheaf AddCommGrpCat X) (π : K ⟶ Q)
    (hzero : ∀ x : X, x ∈ (⨆ i : Fin n, if c i ≤ b then A i else ⊥) →
      IsZero (TopCat.Presheaf.stalk Q.obj x)) :
    ∃ q : (abelianOpenExtensionByZero (iSup A)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ Q,
      ∀ i, c i = b + 1 → q.hom.app (op (A i))
        (abelianOpenExtensionSection (iSup A)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
          (A i) (le_iSup A i)
          ((toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (iSup A)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (iSup A).inclusion').obj (A i))) (ULift.up 1))) =
          π.hom.app (op (A i)) (s i) := by
  classical
  let V : Opens X := ⨆ i : Fin n, if c i ≤ b then A i else ⊥
  have zero_on (W : Opens X) (hW : W ≤ V) (a d : Q.obj.obj (op W)) : a = d := by
    apply TopCat.Presheaf.section_ext Q W a d
    intro x hx
    have hz := hzero x (hW hx)
    have := AddCommGrpCat.isZero_iff_subsingleton.mp hz
    exact Subsingleton.elim _ _
  have lower_le (i : Fin n) (hi : c i ≠ b + 1) : A i ≤ V := by
    have hci : c i ≤ b := by
      have hbound := (hc i).2
      omega
    exact le_iSup_of_le i (by simp [hci])
  let sf : ∀ i, Q.obj.obj (op (A i)) := fun i ↦
    if c i = b + 1 then π.hom.app (op (A i)) (s i) else 0
  have hcompat : TopCat.Presheaf.IsCompatible Q.obj A sf := by
    intro i j
    by_cases hi : c i = b + 1
    · by_cases hj : c j = b + 1
      · dsimp [sf]
        rw [ite_eq_left hi, ite_eq_left hj]
        have hn (l : Fin n) (W : Opens X) (hW : W ≤ A l) :
            (ι ≫ isoC.hom).hom.app (op W) (K.obj.map (homOfLE hW).op (s l)) =
              (toSheafify (Opens.grothendieckTopology X)
                ((Functor.const (Opens X)ᵒᵖ).obj
                  (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op W)
                    (ULift.up (c l : ℤ)) := by
          have hn := ConcreteCategory.congr_hom
            ((ι ≫ isoC.hom).hom.naturality (homOfLE hW).op) (s l)
          have hu := ConcreteCategory.congr_hom
            ((toSheafify (Opens.grothendieckTopology X)
              ((Functor.const (Opens X)ᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u} ℤ)))).naturality
                  (homOfLE hW).op) (ULift.up (c l : ℤ))
          simp only [AddCommGrpCat.comp_apply] at hn hu
          rw [hn, hvalue l]
          erw [← hu]
          rfl
        have he : K.obj.map (Opens.infLELeft (A i) (A j)).op (s i) =
            K.obj.map (Opens.infLERight (A i) (A j)).op (s j) := by
          have : Mono (ι ≫ isoC.hom).hom := inferInstance
          have : Mono ((ι ≫ isoC.hom).hom.app (op (A i ⊓ A j))) := inferInstance
          apply (AddCommGrpCat.mono_iff_injective
            ((ι ≫ isoC.hom).hom.app (op (A i ⊓ A j)))).mp inferInstance
          change (ι ≫ isoC.hom).hom.app (op (A i ⊓ A j))
              (K.obj.map (homOfLE inf_le_left).op (s i)) =
            (ι ≫ isoC.hom).hom.app (op (A i ⊓ A j))
              (K.obj.map (homOfLE inf_le_right).op (s j))
          rw [hn i (A i ⊓ A j) inf_le_left, hn j (A i ⊓ A j) inf_le_right, hi, hj]
        have hπi := ConcreteCategory.congr_hom
          (π.hom.naturality (Opens.infLELeft (A i) (A j)).op) (s i)
        have hπj := ConcreteCategory.congr_hom
          (π.hom.naturality (Opens.infLERight (A i) (A j)).op) (s j)
        simp only [AddCommGrpCat.comp_apply] at hπi hπj
        rw [← hπi, ← hπj, he]
      · exact zero_on (A i ⊓ A j) (inf_le_right.trans (lower_le j hj)) _ _
    · exact zero_on (A i ⊓ A j) (inf_le_left.trans (lower_le i hi)) _ _
  obtain ⟨t, ht, -⟩ := Q.existsUnique_gluing A sf hcompat
  obtain ⟨q, hq⟩ := integerExtension_of_section X Q (iSup A) t
  refine ⟨q, ?_⟩
  intro i hi
  rw [hq (A i) (le_iSup A i)]
  exact (ht i).trans (ite_eq_left hi)

end TopCat.Sheaf
