/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.Topology.Sheaves.CechComparison

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero homology of the categorical Čech complex of an open cover
is the group of global sections, with coefficients one universe above the space.
Source: Stacks Project, Tag 03AN (the degree-zero sheaf condition),
as used in Tag 03AZ.
(blueprint: lem-sc-open-cech-zeroth-homology)

Proof: Augment the Čech complex by restricting a global section to each
one-fold product. The augmentation has zero differential because the two
restrictions to every two-fold product coincide. The zeroth cycles are exactly
compatible local sections: project the equation d c = 0 to the two-fold
product and restrict further to the intersection. Sheaf gluing supplies a
unique global section for these cycles. Thus the augmentation identifies
global sections with the cycles. There are no incoming boundaries in degree
zero, so cycles project isomorphically to homology. This includes an empty
cover of the empty space. -/
theorem nonempty_openCech_zerothHomology
    {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (hU : iSup U = ⊤)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}) :
    Nonempty (F.obj.obj (op ⊤) ≅ ((CategoryTheory.cechComplexFunctor U).obj F.obj).homology 0) := by
  classical
  let P := F.obj
  let K := (CategoryTheory.cechComplexFunctor U).obj P
  let V := fun y : Fin 1 → ι ↦ ∏ᶜ fun l ↦ U (y l)
  have hV : (⊤ : Opens X) ≤ iSup V := by
    rw [← hU]
    refine iSup_le fun j ↦ le_iSup_of_le (fun _ ↦ j) ?_
    exact (Pi.lift fun _ ↦ homOfLE le_rfl).le
  let a : P.obj (op ⊤) ⟶ K.X 0 := Pi.lift fun y ↦ P.map (homOfLE le_top).op
  have hap (y : Fin 1 → ι) :
      a ≫ TopCat.Presheaf.cechComplexFunctorπ U P 0 y = P.map (homOfLE le_top).op :=
    Pi.lift_comp_π _ y
  have ha : a ≫ K.d 0 1 = 0 := by
    apply Pi.hom_ext
    intro y
    rw [Category.assoc, zero_comp]
    change a ≫ K.d 0 1 ≫ TopCat.Presheaf.cechComplexFunctorπ U P 1 y = 0
    rw [TopCat.Presheaf.cechComplexFunctor_d_π]
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
    have hh (j : Fin 2) : a ≫ TopCat.Presheaf.cechComplexFunctorπ U P 0
        (y ∘ j.succAbove) ≫ P.map
          (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (j.succAbove l)).op =
        P.map (homOfLE le_top).op := by
      rw [← Category.assoc, hap, ← Functor.map_comp]
      congr 1
    simp_rw [hh]
    simp [Fin.sum_univ_two]
  let b := K.liftCycles a 1 (by simp) ha
  have hb : IsIso b := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have hi : Function.Injective (K.iCycles 0) :=
      (AddCommGrpCat.mono_iff_injective _).1 inferInstance
    have hbi (s : P.obj (op ⊤)) : K.iCycles 0 (b s) = a s :=
      ConcreteCategory.congr_hom (K.liftCycles_i _ _ _ _) s
    constructor
    · intro s t hst
      apply TopCat.Sheaf.eq_of_locally_eq' F V ⊤ (fun _ ↦ homOfLE le_top) hV
      intro y
      have h := congrArg (fun c ↦ (TopCat.Presheaf.cechComplexFunctorπ U P 0 y)
        (K.iCycles 0 c)) hst
      simp only [hbi] at h
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hap] at h
      exact h
    · intro c
      have hd : K.d 0 1 (K.iCycles 0 c) = 0 :=
        ConcreteCategory.congr_hom (K.iCycles_d 0 1) c
      let sf := fun y ↦ TopCat.Presheaf.cechComplexFunctorπ U P 0 y (K.iCycles 0 c)
      have hc : TopCat.Presheaf.IsCompatible P V sf := by
        intro y z
        let t : Fin 2 → ι := fun j ↦ if j = 0 then y 0 else z 0
        have h0 : t ∘ (0 : Fin 2).succAbove = z := by
          funext l
          fin_cases l
          simp [t]
        have h1 : t ∘ (1 : Fin 2).succAbove = y := by
          funext l
          fin_cases l
          simp [t]
        let W := ∏ᶜ fun l ↦ U (t l)
        let f : V y ⊓ V z ⟶ W := Pi.lift fun j ↦ homOfLE (by
          fin_cases j
          · exact inf_le_left.trans ((Pi.π (fun l ↦ U (y l)) 0).le)
          · exact inf_le_right.trans ((Pi.π (fun l ↦ U (z l)) 0).le))
        have he := congrArg (fun x ↦ TopCat.Presheaf.cechComplexFunctorπ U P 1 t x) hd
        rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.cechComplexFunctor_d_π] at he
        simp only [AddCommGrpCat.sum_apply, map_zero] at he
        erw [Fin.sum_univ_two] at he
        simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
          neg_one_zsmul, ConcreteCategory.comp_apply] at he
        change P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (t l))
            ((0 : Fin 2).succAbove l)).op
            (TopCat.Presheaf.cechComplexFunctorπ U P 0
              (t ∘ (0 : Fin 2).succAbove) (K.iCycles 0 c)) + -
          P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (t l))
            ((1 : Fin 2).succAbove l)).op
            (TopCat.Presheaf.cechComplexFunctorπ U P 0
              (t ∘ (1 : Fin 2).succAbove) (K.iCycles 0 c)) = 0 at he
        have he' := eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using he)
        have hh := congrArg (P.map f.op) he'.symm
        have hr (j : Fin 2) (v : Fin 1 → ι) (hv : t ∘ j.succAbove = v)
            (g : V y ⊓ V z ⟶ V v) :
            P.map f.op (P.map (Pi.lift fun l ↦
              Pi.π (fun l ↦ U (t l)) (j.succAbove l)).op
                (sf (t ∘ j.succAbove))) = P.map g.op (sf v) := by
          cases hv
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
          congr 1
        change P.map f.op (P.map _ (sf (t ∘ (1 : Fin 2).succAbove))) =
          P.map f.op (P.map _ (sf (t ∘ (0 : Fin 2).succAbove))) at hh
        exact (hr 1 y h1 ((V y).infLELeft (V z))).symm.trans
          (hh.trans (hr 0 z h0 ((V y).infLERight (V z))))
      obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' F V ⊤
        (fun _ ↦ homOfLE le_top) hV sf hc
      refine ⟨s, hi ?_⟩
      rw [hbi]
      apply Concrete.limit_ext
      intro y
      change TopCat.Presheaf.cechComplexFunctorπ U P 0 y.as (a s) = sf y.as
      rw [← ConcreteCategory.comp_apply, hap]
      exact hs y.as
  have hp : IsIso (K.homologyπ 0) := K.isIso_homologyπ 0 0 (by simp) (by simp)
  exact ⟨asIso b ≪≫ asIso (K.homologyπ 0)⟩

end TopCat.Sheaf
