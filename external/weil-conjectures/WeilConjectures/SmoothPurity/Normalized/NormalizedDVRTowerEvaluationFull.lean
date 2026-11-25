/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Lifting compatible derived maps of sequential towers

Source: Stacks Project, Injectives, Tag 079P, and Derived Categories, Tag 070I;
sequential homotopy correction as written in the DAG proof
(blueprint: lem-pur-normalized-dvr-tower-evaluation-full).

The natural-number index `n` denotes the positive level `n + 1` of the source.
-/

@[expose] public section

set_option autoImplicit false

universe u v g wA wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Surjectivity of localization on maps into a K-injective target. -/
private theorem tower_chainMap_rep
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P J : CochainComplex A ℤ) [J.IsKInjective]
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj J) :
    ∃ a : P ⟶ J, DerivedCategory.Q.map a = f := by
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨a, ha⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj P) J).surjective
      (e.hom.app P ≫ f ≫ e.inv.app J)
  obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective a
  refine ⟨a, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality a
  rw [ha] at h
  simpa [e] using h.symm

/-- Equality after localization into a K-injective target gives a chain homotopy. -/
private theorem tower_homotopy_of_Q_eq
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P J : CochainComplex A ℤ} [J.IsKInjective]
    (a b : P ⟶ J) (h : DerivedCategory.Q.map a = DerivedCategory.Q.map b) :
    Nonempty (Homotopy a b) := by
  apply Nonempty.intro
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ J).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app J)).1
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]

/-- Lift a commutation homotopy through degreewise sections and subtract its boundary. -/
private theorem tower_correct_map
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P J K : CochainComplex A ℤ}
    (a : P ⟶ J) (b : P ⟶ K) (t : J ⟶ K)
    (s : ∀ i, K.X i ⟶ J.X i) (hs : ∀ i, s i ≫ t.f i = 𝟙 _)
    (H : Homotopy (a ≫ t) b) :
    ∃ c : P ⟶ J, c ≫ t = b ∧ DerivedCategory.Q.map c = DerivedCategory.Q.map a := by
  let l := fun i j ↦ H.hom i j ≫ s j
  let d := Homotopy.nullHomotopicMap l
  have hd : d ≫ t = a ≫ t - b := by
    rw [Homotopy.nullHomotopicMap_comp]
    have he : (fun i j ↦ l i j ≫ t.f j) = H.hom := by
      funext i j
      dsimp [l]
      rw [Category.assoc, hs, Category.comp_id]
    rw [he]
    ext i
    simpa [Homotopy.nullHomotopicMap] using
      (eq_sub_iff_add_eq.mpr (H.comm i).symm)
  refine ⟨a - d, ?_, ?_⟩
  · rw [Preadditive.sub_comp, hd]
    abel
  · have hzero : DerivedCategory.Q.map d = 0 := by
      simpa using DerivedCategory.Q_map_eq_of_homotopy A
        (Homotopy.nullHomotopy l (fun i j hij ↦ by simp [l, H.zero i j hij]))
    simp [hzero]

/-- Extend the finite staircase map into an injective tower by one level. -/
private theorem injective_tower_transition_split
    {A : Type*} [Category A] [Abelian A]
    (T : ℕᵒᵖ ⥤ A) [Injective T]
    (n : ℕ) : IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op) := by
  classical
  let k := (homOfLE (Nat.le_succ n)).op
  let M := T.obj (op n)
  let L := (evaluationLeftAdjoint A (op n)).obj M
  let L' := (evaluationLeftAdjoint A (op (n + 1))).obj M
  let i : L ⟶ L' :=
    { app := fun m ↦ Sigma.desc fun g ↦ Sigma.ι (fun _ ↦ M) (k ≫ g)
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, L', evaluationLeftAdjoint, Category.assoc] }
  have (m : ℕᵒᵖ) : Mono (i.app m) := by
    let r : L'.obj m ⟶ L.obj m := Sigma.desc fun _ ↦
      if h : Nonempty (op n ⟶ m) then Sigma.ι (fun _ ↦ M) h.some else 0
    have hr : i.app m ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro g
      simp only [i, r, colimit.ι_desc_assoc, Cofan.mk_ι_app,
        dite_eq_left (show Nonempty (op n ⟶ m) from ⟨g⟩), colimit.ι_desc]
      exact (congrArg (Sigma.ι (fun _ : op n ⟶ m ↦ M))
        (Subsingleton.elim _ g)).trans (Category.comp_id _).symm
    exact (IsSplitMono.mk' ⟨r, hr⟩).mono
  have : Mono i := NatTrans.mono_of_mono_app i
  let a : L ⟶ T :=
    { app := fun m ↦ Sigma.desc fun g ↦ T.map g
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, evaluationLeftAdjoint, Functor.map_comp] }
  let b := Injective.factorThru a i
  have hb : i ≫ b = a := Injective.comp_factorThru a i
  refine IsSplitEpi.mk' ⟨Sigma.ι (fun _ ↦ M) (𝟙 (op (n + 1))) ≫
    b.app (op (n + 1)), ?_⟩
  rw [Category.assoc, ← b.naturality k, ← Category.assoc]
  have hn := congrArg (fun f : L ⟶ T ↦
    Sigma.ι (fun _ ↦ M) (𝟙 (op n)) ≫ f.app (op n)) hb
  simpa [L', evaluationLeftAdjoint, i, a] using hn

/-- Recursively correct chain representatives and assemble the resulting strict tower map. -/
private theorem tower_strictify
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hK : ∀ n : ℕ, CochainComplex.IsKInjective (J.asFunctor.obj (op n)))
    (hS : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((J.X i).map (homOfLE (Nat.le_succ n)).op))
    (f : ∀ n : ℕ, DerivedCategory.Q.obj (P.asFunctor.obj (op n)) ⟶
      DerivedCategory.Q.obj (J.asFunctor.obj (op n)))
    (hf : ∀ n, f (n + 1) ≫ DerivedCategory.Q.map
        (J.asFunctor.map (homOfLE (Nat.le_succ n)).op) =
      DerivedCategory.Q.map (P.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫ f n) :
    ∃ b : P ⟶ J, ∀ n : ℕ, DerivedCategory.Q.map
      ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).map b) = f n := by
  classical
  have : ∀ n : ℕ, CochainComplex.IsKInjective (J.asFunctor.obj (op n)) := hK
  have : ∀ (n : ℕ) (i : ℤ),
      IsSplitEpi ((J.X i).map (homOfLE (Nat.le_succ n)).op) := hS
  let L (n : ℕ) := {a : P.asFunctor.obj (op n) ⟶ J.asFunctor.obj (op n) //
    DerivedCategory.Q.map a = f n}
  have inhabited (n : ℕ) : Nonempty (L n) := by
    obtain ⟨a, ha⟩ := tower_chainMap_rep _ _ (f n)
    exact ⟨⟨a, ha⟩⟩
  have extend (n : ℕ) (b : L n) :
      ∃ c : L (n + 1), c.val ≫ J.asFunctor.map (homOfLE (Nat.le_succ n)).op =
        P.asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ b.val := by
    let a := (inhabited (n + 1)).some
    have he : DerivedCategory.Q.map
        (a.val ≫ J.asFunctor.map (homOfLE (Nat.le_succ n)).op) =
        DerivedCategory.Q.map
          (P.asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ b.val) := by
      simp only [Functor.map_comp, a.property, b.property, hf]
    obtain ⟨H⟩ := tower_homotopy_of_Q_eq _ _ he
    obtain ⟨c, hc, hc'⟩ := tower_correct_map a.val
      (P.asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ b.val)
      (J.asFunctor.map (homOfLE (Nat.le_succ n)).op)
      (fun i ↦ section_ ((J.X i).map (homOfLE (Nat.le_succ n)).op))
      (fun i ↦ IsSplitEpi.id _) H
    exact ⟨⟨c, hc'.trans a.property⟩, hc⟩
  let next (n : ℕ) (b : L n) : L (n + 1) := (extend n b).choose
  let lifts : ∀ n, L n := fun n ↦ Nat.rec (inhabited 0).some next n
  have compat (n : ℕ) :
      P.asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ (lifts n).val =
      (lifts (n + 1)).val ≫ J.asFunctor.map (homOfLE (Nat.le_succ n)).op :=
    (extend n (lifts n)).choose_spec.symm
  let b : P ⟶ J :=
    { f := fun i ↦ NatTrans.ofOpSequence (fun n ↦ (lifts n).val.f i)
        (fun n ↦ congrArg (fun a ↦ HomologicalComplex.Hom.f a i) (compat n))
      comm' := by
        intro i j hij
        ext n
        exact (lifts n.unop).val.comm i j }
  exact ⟨b, fun n ↦ (lifts n).property⟩

private theorem smallDiagrams_grothendieck
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{g} A]
    (J : Type g) [SmallCategory J] : IsGrothendieckAbelian.{g} (J ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : J ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (J ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{g, g} (J ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{g, g} (J ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact {}

private theorem towerCategory_grothendieck
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{g} A] :
    IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A) := by
  have : IsGrothendieckAbelian.{g} (AsSmall.{g} ℕᵒᵖ ⥤ A) :=
    smallDiagrams_grothendieck A (AsSmall.{g} ℕᵒᵖ)
  let e : ℕᵒᵖ ≌ AsSmall.{g} ℕᵒᵖ := AsSmall.equiv
  exact IsGrothendieckAbelian.of_equivalence (Equivalence.congrLeft e.symm)

variable (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ A)]

/-- Exact evaluation of a strict tower induces evaluation on its derived category.
Source: Stacks Project, Derived Categories, Tag 05RU, and the levelwise exactness of
functor categories (blueprint: lem-pur-normalized-dvr-tower-evaluation-full).
Here `n` denotes positive level `n + 1`. -/
private noncomputable abbrev grothendieckTowerEvaluation (n : ℕ) :
    DerivedCategory (ℕᵒᵖ ⥤ A) ⥤
      DerivedCategory (A) :=
  ((evaluation ℕᵒᵖ (A)).obj (op n)).mapDerivedCategory

/-- The canonical derived transition from level `n + 2` to level `n + 1`.
Source: Stacks Project, Derived Categories, Tags 05RU and 08TC
(blueprint: lem-pur-normalized-dvr-tower-evaluation-full).
This is the localization lift of the degreewise tower transition, using the canonical
factorizations of the exact evaluation functors. No arbitrary transition is chosen. -/
private noncomputable def grothendieckTowerTransition (n : ℕ) :
    grothendieckTowerEvaluation A (n + 1) ⟶ grothendieckTowerEvaluation A n :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
    _ _ (grothendieckTowerEvaluation A (n + 1)) (grothendieckTowerEvaluation A n)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (A)).map (homOfLE (Nat.le_succ n)).op)
        (ComplexShape.up ℤ)) DerivedCategory.Q)

set_option backward.isDefEq.respectTransparency false in
private theorem grothendieckTowerTransition_Q
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    (grothendieckTowerTransition A n).app (DerivedCategory.Q.obj K) ≫
        ((evaluation ℕᵒᵖ (A)).obj
          (op n)).mapDerivedCategoryFactors.hom.app K =
      ((evaluation ℕᵒᵖ (A)).obj
        (op (n + 1))).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (K.asFunctor.map (homOfLE (Nat.le_succ n)).op) := by
  simp only [grothendieckTowerTransition, Localization.liftNatTrans_app, Category.assoc]
  change
    ((evaluation ℕᵒᵖ (A)).obj
      (op (n + 1))).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map (K.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
      ((evaluation ℕᵒᵖ (A)).obj (op n)).mapDerivedCategoryFactors.inv.app K ≫
      ((evaluation ℕᵒᵖ (A)).obj
        (op n)).mapDerivedCategoryFactors.hom.app K = _
  simp only [Iso.inv_hom_id_app]
  exact congrArg
    (fun f ↦ ((evaluation ℕᵒᵖ (A)).obj
      (op (n + 1))).mapDerivedCategoryFactors.hom.app K ≫ f)
    (Category.comp_id (DerivedCategory.Q.map
      (K.asFunctor.map (homOfLE (Nat.le_succ n)).op)))

set_option backward.isDefEq.respectTransparency false in
private theorem grothendieckTowerTransition_transport
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (Z : DerivedCategory (ℕᵒᵖ ⥤ A))
    (e : DerivedCategory.Q.obj K ≅ Z) (n : ℕ) :
    DerivedCategory.Q.map (K.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
        (((evaluation ℕᵒᵖ (A)).obj
          (op n)).mapDerivedCategoryFactors.inv.app K ≫
          (grothendieckTowerEvaluation A n).map e.hom) =
      (((evaluation ℕᵒᵖ (A)).obj
        (op (n + 1))).mapDerivedCategoryFactors.inv.app K ≫
          (grothendieckTowerEvaluation A (n + 1)).map e.hom) ≫
        (grothendieckTowerTransition A n).app Z := by
  have ht := grothendieckTowerTransition_Q A K n
  have hn := (grothendieckTowerTransition A n).naturality e.hom
  simp only [Category.assoc]
  rw [hn]
  simp only [← Category.assoc]
  apply (cancel_epi
    (((evaluation ℕᵒᵖ (A)).obj
      (op (n + 1))).mapDerivedCategoryFactors.hom.app K)).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← ht]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Compatible derived evaluation maps lift to a map of strict derived towers; every
levelwise invertible lift is invertible. Source: Stacks Project, Injectives, Tag 079P,
and Derived Categories, Tag 070I, with the sequential correction argument below
(blueprint: lem-pur-normalized-dvr-tower-evaluation-full).

Proof plan:
1. Represent `X,Y` by strict tower complexes `P,V`. The small module diagram category
is Grothendieck abelian by `lem-weil-pbc-small-module-diagrams-grothendieck`. Resolve `V`
by a K-injective tower complex `J` with injective tower objects in each degree, using
`lem-pur-kinjective-degreewise-existence`. Exact evaluation preserves quasi-isomorphisms
by `lem-weil-tower-category-levelwise-abelian`; transport the specified maps to `P_n,J_n`.
2. For an injective tower `T`, extend the map from the staircase `L_n(T_n)` to `T` across
its monic inclusion into `L_{n+1}(T_n)` by `def-sp-injective-resolutions`. At level `n`
this extension is the identity, so its next component splits `T_{n+1} → T_n`.
Choose these sections in every degree of `J`, without requiring differential compatibility.
3. By `lem-weil-tower-evaluation-kinjective`, each `J_n` is K-injective. The bijection
`lem-weil-pbc-kinjective-hom-derived` represents each specified map by a chain map `a_n`
and makes each adjacent commutation defect null-homotopic.
4. Inductively set `b_0 = a_0`. Given `b_n`, choose a homotopy `H` for
`t a_{n+1} - b_n t`, lift it degreewise using the sections, and subtract
`d H̃ + H̃ d` from `a_{n+1}`. This is a null-homotopic chain-map correction. Since
`t H̃ = H` and `t` commutes with differentials, the corrected map commutes strictly
with the adjacent transition and still represents the prescribed derived map.
5. Adjacent commutation implies all naturality equations. Assemble the corrected maps
into a strict tower chain map, localize, and transport back to `X,Y` by
`def-weil-abstract-derived-category`. Its evaluations are the prescribed maps.
Individual homotopies need not assemble into a tower homotopy; no uniqueness is claimed.
6. For ANY lift with invertible evaluations, represent it by a chain map into `J`
using `lem-weil-pbc-kinjective-hom-derived` in the tower category. All evaluated cohomology
maps are invertible. Cohomology is levelwise by `lem-weil-tower-category-levelwise-abelian`,
and component inverses are natural. Thus the tower chain map is a quasi-isomorphism,
so its localization, and hence the lift, is invertible. -/
private theorem grothendieckTowerEvaluation_full
    [IsGrothendieckAbelian.{g} A]
    (X Y : DerivedCategory (ℕᵒᵖ ⥤ A))
    (f : ∀ n : ℕ, (grothendieckTowerEvaluation A n).obj X ⟶
      (grothendieckTowerEvaluation A n).obj Y)
    (hf : ∀ n : ℕ, f (n + 1) ≫ (grothendieckTowerTransition A n).app Y =
      (grothendieckTowerTransition A n).app X ≫ f n) :
    (∃ g : X ⟶ Y, ∀ n : ℕ, (grothendieckTowerEvaluation A n).map g = f n) ∧
    (∀ g : X ⟶ Y, (∀ n : ℕ, (grothendieckTowerEvaluation A n).map g = f n) →
      (∀ n : ℕ, IsIso (f n)) → IsIso g) := by
  classical
  let B := ℕᵒᵖ ⥤ A
  have : IsGrothendieckAbelian.{g} B := towerCategory_grothendieck A
  let P : CochainComplex B ℤ := DerivedCategory.Q.objPreimage X
  let V : CochainComplex B ℤ := DerivedCategory.Q.objPreimage Y
  let J : CochainComplex B ℤ := (CochainComplex.kInjectiveResolutionFunctor.{g} B).obj V
  let v : V ⟶ J := (CochainComplex.toKInjectiveResolution.{g} B).app V
  have : QuasiIso v :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app B V).2
  let eP : DerivedCategory.Q.obj P ≅ X := DerivedCategory.Q.objObjPreimageIso X
  let eJ : DerivedCategory.Q.obj J ≅ Y :=
    (asIso (DerivedCategory.Q.map v)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Y
  let E := fun n : ℕ ↦ (evaluation ℕᵒᵖ A).obj (op n)
  let D := fun n : ℕ ↦ grothendieckTowerEvaluation A n
  let α (n : ℕ) : DerivedCategory.Q.obj (P.asFunctor.obj (op n)) ≅ (D n).obj X :=
    ((E n).mapDerivedCategoryFactors.app P).symm ≪≫ (D n).mapIso eP
  let β (n : ℕ) : DerivedCategory.Q.obj (J.asFunctor.obj (op n)) ≅ (D n).obj Y :=
    ((E n).mapDerivedCategoryFactors.app J).symm ≪≫ (D n).mapIso eJ
  let f' := fun n ↦ (α n).hom ≫ f n ≫ (β n).inv
  have hα (n : ℕ) :
      DerivedCategory.Q.map (P.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
        (α n).hom = (α (n + 1)).hom ≫ (grothendieckTowerTransition A n).app X :=
    grothendieckTowerTransition_transport A P X eP n
  have hβ (n : ℕ) :
      DerivedCategory.Q.map (J.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
        (β n).hom = (β (n + 1)).hom ≫ (grothendieckTowerTransition A n).app Y :=
    grothendieckTowerTransition_transport A J Y eJ n
  have hf' (n : ℕ) : f' (n + 1) ≫
      DerivedCategory.Q.map (J.asFunctor.map (homOfLE (Nat.le_succ n)).op) =
      DerivedCategory.Q.map (P.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫ f' n := by
    apply (cancel_mono (β n).hom).1
    dsimp only [f']
    simp only [Category.assoc, hβ, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [hf, ← Category.assoc
      (DerivedCategory.Q.map (P.asFunctor.map (homOfLE (Nat.le_succ n)).op)), hα]
    simp only [Category.assoc]
  have hK (n : ℕ) : CochainComplex.IsKInjective (J.asFunctor.obj (op n)) :=
    tower_evaluation_isKInjective A J (op n)
  have hS (n : ℕ) (i : ℤ) : IsSplitEpi ((J.X i).map (homOfLE (Nat.le_succ n)).op) :=
    injective_tower_transition_split (J.X i) n
  obtain ⟨b, hb⟩ := tower_strictify P J hK hS f' hf'
  constructor
  · refine ⟨eP.inv ≫ DerivedCategory.Q.map b ≫ eJ.hom, ?_⟩
    intro n
    have hn := (E n).mapDerivedCategoryFactors_hom_naturality b
    have he : (D n).map (DerivedCategory.Q.map b) =
        (E n).mapDerivedCategoryFactors.hom.app P ≫ f' n ≫
          (E n).mapDerivedCategoryFactors.inv.app J := by
      rw [hb n] at hn
      apply (cancel_mono ((E n).mapDerivedCategoryFactors.hom.app J)).1
      simp only [Category.assoc, Iso.inv_hom_id_app]
      exact hn.trans (congrArg (fun f ↦ (E n).mapDerivedCategoryFactors.hom.app P ≫ f)
        (Category.comp_id (f' n)).symm)
    change (D n).map (eP.inv ≫ DerivedCategory.Q.map b ≫ eJ.hom) = f n
    rw [Functor.map_comp, Functor.map_comp, he]
    dsimp only [f', α, β, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
    rw [← Category.assoc ((D n).map eP.inv), ← Functor.map_comp,
      eP.inv_hom_id, Functor.map_id, Category.id_comp]
    exact Category.comp_id (f n)
  · intro g hg hi
    have (n : ℕ) : IsIso ((D n).map g) := by rw [hg]; exact hi n
    obtain ⟨c, hc⟩ := tower_chainMap_rep P J (eP.hom ≫ g ≫ eJ.inv)
    have hciso (n : ℕ) : IsIso ((D n).map (DerivedCategory.Q.map c)) := by
      rw [hc, Functor.map_comp, Functor.map_comp]
      infer_instance
    have hce (n : ℕ) : QuasiIso (((E n).mapHomologicalComplex (.up ℤ)).map c) := by
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).1
      have hn := (E n).mapDerivedCategoryFactors_hom_naturality c
      have he : DerivedCategory.Q.map (((E n).mapHomologicalComplex (.up ℤ)).map c) =
          (E n).mapDerivedCategoryFactors.inv.app P ≫
            (D n).map (DerivedCategory.Q.map c) ≫
            (E n).mapDerivedCategoryFactors.hom.app J := by
        change _ = (E n).mapDerivedCategoryFactors.inv.app P ≫
          (E n).mapDerivedCategory.map (DerivedCategory.Q.map c) ≫
          (E n).mapDerivedCategoryFactors.hom.app J
        rw [hn]
        simp
      rw [he]
      infer_instance
    have : QuasiIso c := (HomologicalComplex.quasiIso_iff_evaluation c).2
      (fun n ↦ hce n.unop)
    have he : g = eP.inv ≫ DerivedCategory.Q.map c ≫ eJ.hom := by simp [hc]
    rw [he]
    infer_instance

end CategoryTheory

namespace WeilConjectures

universe d t r

/-- Compatible maps between evaluations of actual strict completed-coefficient towers
lift to the derived category of those towers, with independent site/coefficient universes.
Source: Stacks 079P and 070I, and the chain-map proof of sequential evaluation fullness
(blueprint: lem-pur-normalized-dvr-tower-evaluation-full).

Proof: the pro-etale site is essentially small in the module universe, so module
sheaves are Grothendieck there. Evaluation left adjoints give a separator for towers
and AB5 is pointwise. Resolve the target tower by a degreewise injective K-injective
complex. Its transition maps split degreewise and its evaluations are K-injective.
Represent each prescribed derived map by a chain map. Inductively subtract a lifted
null-homotopy of the adjacent commutation defect; the correction preserves its derived
class and makes the adjacent square commute strictly. Assemble the corrected maps as
a strict tower chain map and localize. The canonical evaluation factorizations give
exactly the prescribed maps. This is the same sequential homotopy correction as for
a small ringed site; no equality of the raw site and coefficient universes is used. -/
theorem normalizedDVRTowerEvaluation_full
    (l : ℕ) [Fact l.Prime] (E : Type r) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (X Y : normalizedDVRDerivedTowers l E W D hl)
    (f : ∀ n : ℕ, (normalizedDVRTowerEvaluation l E W D hl n).obj X ⟶
      (normalizedDVRTowerEvaluation l E W D hl n).obj Y)
    (hf : ∀ n : ℕ, f (n + 1) ≫
        (normalizedDVRTowerTransition l E W D hl (Nat.le_succ n)).app Y =
      (normalizedDVRTowerTransition l E W D hl (Nat.le_succ n)).app X ≫ f n) :
    ∃ g : X ⟶ Y, ∀ n : ℕ, (normalizedDVRTowerEvaluation l E W D hl n).map g = f n := by
  let A := completedIntegralModuleSheaves l E W D hl
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ A)
  let : EssentiallySmall.{max r (t + 1)} (AlgebraicGeometry.Scheme.ProEt W) :=
    essentiallySmallSelf _
  let : IsGrothendieckAbelian.{max r (t + 1)} A :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse
      (completedIntegralCoefficientSheaf l E W D hl)
  exact (CategoryTheory.grothendieckTowerEvaluation_full A X Y f hf).1

end WeilConjectures
