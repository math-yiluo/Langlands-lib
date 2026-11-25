/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExactIntrinsic
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemVerdier
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Colimit.Module
public import WeilConjectures.SmoothPurity.SfAlgebraicallyClosedCoefficients.SfCoefficientStageCore

import WeilConjectures.CategoryTheory.StageSystem.Shift

/-! # Intrinsic algebraically closed coefficients without idempotent completion

Source: blueprint `sec-smooth-purity/sk-def-sf-operations`, order 1462;
current main snapshot `sec-proetale-coefficients/sk-def-sf-operations`, order 1821
(blueprint: def-weil-algebraically-closed-coefficients).
Objects are actual pairs and Hom is the directed colimit of the stated abelian groups.
Finite stages use the repaired intrinsic integral constructibility predicate.

The similarly named legacy theorems quantify over `AlgebraicallyClosedCoefficients.Stage`,
which uses `rationalConstructibleCategory` and the withdrawn integral predicate.
Here the eleven formerly ambiguous signatures bind every source parameter explicitly
and qualify their intrinsic stage, pair, transition and Hom data. They concern
`sfRationalConstructibleCategory` on `sfIntegralConstructibleCategory`; no identification
with the legacy stages is assumed. Existing generic pair/cone/Verdier constructions
and the shared coefficient transport are reused.
The legacy coefficient-size transports are reused without identifying the old and new stages.
The existing upstream pair category supplies its quotient, identities and composition;
its Hom groups are canonically the displayed abelian-group colimits.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures
namespace SfAlgebraicallyClosedCoefficients

attribute [-instance] StageSystem.PairCategory.hasShift StageSystem.ι_commShift
  StageSystem.transIso_commShift

private theorem integer_commShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

private theorem shift_ext {C : Type*} [Category C] (s t : HasShift C ℤ)
    (hf : ∀ n, @shiftFunctor C ℤ _ _ s n = @shiftFunctor C ℤ _ _ t n)
    (hz : HEq (@shiftFunctorZero C ℤ _ _ s) (@shiftFunctorZero C ℤ _ _ t))
    (ha : ∀ n m, HEq (@shiftFunctorAdd C ℤ _ _ s n m)
      (@shiftFunctorAdd C ℤ _ _ t n m)) : s = t := by
  cases s with
  | mk F f =>
    cases t with
    | mk G g =>
      have h : F = G := Discrete.functor_ext hf
      cases h
      congr 1
      apply Functor.Monoidal.ext
      · exact congrArg Iso.inv (eq_of_heq hz)
      · funext n m
        exact congrArg Iso.inv (eq_of_heq (ha n.as m.as))
      · exact congrArg Iso.hom (eq_of_heq hz)
      · funext n m
        exact congrArg Iso.hom (eq_of_heq (ha n.as m.as))

private theorem normalized_shift_ext
    {I : Type*} {D : Type*} [Category D]
    {C : I → Type*} [∀ i, Category (C i)] [∀ i, HasShift (C i) ℤ]
    (J : ∀ i, C i ⥤ D) (cover : ∀ X : D, ∃ i, ∃ K : C i, (J i).obj K = X)
    (s t : HasShift D ℤ)
    (hf : ∀ n, @shiftFunctor D ℤ _ _ s n = @shiftFunctor D ℤ _ _ t n)
    (cs : ∀ i, @Functor.CommShift _ _ _ _ (J i) ℤ _ _ s)
    (ct : ∀ i, @Functor.CommShift _ _ _ _ (J i) ℤ _ _ t)
    (hc : ∀ i n K,
      HEq ((Functor.commShiftIso (J i) (self := cs i) n).hom.app K)
        ((Functor.commShiftIso (J i) (self := ct i) n).hom.app K)) : s = t := by
  cases s with
  | mk F f =>
    cases t with
    | mk G g =>
      have h : F = G := Discrete.functor_ext hf
      cases h
      have he (i) (n : ℤ) :
          Functor.commShiftIso (J i) (self := cs i) n =
            Functor.commShiftIso (J i) (self := ct i) n := by
        apply Iso.ext
        apply NatTrans.ext
        funext K
        exact eq_of_heq (hc i n K)
      apply shift_ext _ _ hf
      · apply heq_of_eq
        apply Iso.ext_inv
        apply NatTrans.ext
        funext X
        obtain ⟨i, K, rfl⟩ := cover X
        have e := congrArg (fun a ↦ a.hom.app K) (he i 0)
        rw [(cs i).commShiftIso_zero, (ct i).commShiftIso_zero] at e
        simp only [Functor.CommShift.isoZero_hom_app] at e
        exact (cancel_epi ((J i).map ((shiftFunctorZero (C i) ℤ).hom.app K))).mp e
      · intro n m
        apply heq_of_eq
        apply Iso.ext_inv
        apply NatTrans.ext
        funext X
        obtain ⟨i, K, rfl⟩ := cover X
        have e := congrArg (fun a ↦ a.hom.app K) (he i (n + m))
        rw [(cs i).commShiftIso_add, (ct i).commShiftIso_add] at e
        simp only [Functor.CommShift.isoAdd_hom_app] at e
        simp only [he] at e
        exact (cancel_epi _).mp ((cancel_epi _).mp ((cancel_epi _).mp e))

private theorem sandwich_add {C : Type*} [Category C] [Preadditive C]
    {W X Y Z : C} (a : W ⟶ X) (f g : X ⟶ Y) (b : Y ⟶ Z) :
    a ≫ (f + g) ≫ b = a ≫ f ≫ b + a ≫ g ≫ b := by
  rw [Preadditive.add_comp, Preadditive.comp_add]

section PairShiftNormalization

attribute [local instance] StageSystem.PairCategory.hasShift StageSystem.ι_commShift
  StageSystem.transIso_commShift

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, HasShift (C i) ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ (i j k : I) (h : i ≤ j) (k : j ≤ k), NatTrans.CommShift (S.assoc h k).hom ℤ]

private theorem pairShift_unique
    (s : HasShift S.PairCategory ℤ)
    (hobj : ∀ n X, (@shiftFunctor S.PairCategory ℤ _ _ s n).obj X =
      ⟨X.stage, (shiftFunctor (C X.stage) n).obj X.obj⟩)
    (hmap : ∀ n (X Y : S.PairCategory) (L : I) (hX : X.stage ≤ L) (hY : Y.stage ≤ L)
      (f : X.toStage hX ⟶ Y.toStage hY),
      HEq ((@shiftFunctor S.PairCategory ℤ _ _ s n).map
        (StageSystem.PairCategory.mkHom L hX hY f))
        (StageSystem.PairCategory.mkHom
          (X := ⟨X.stage, (shiftFunctor (C X.stage) n).obj X.obj⟩)
          (Y := ⟨Y.stage, (shiftFunctor (C Y.stage) n).obj Y.obj⟩) L hX hY
          (((S.T hX).commShiftIso n).hom.app X.obj ≫
            (shiftFunctor (C L) n).map f ≫ ((S.T hY).commShiftIso n).inv.app Y.obj)))
    (c : ∀ i, @Functor.CommShift _ _ _ _ (S.ι i) ℤ _ _ s)
    (hc : ∀ i n K, HEq ((Functor.commShiftIso (S.ι i) (self := c i) n).hom.app K)
      (𝟙 ((S.ι i).obj ((shiftFunctor (C i) n).obj K)))) :
    s = StageSystem.PairCategory.hasShift S ℤ := by
  refine normalized_shift_ext (S.ι) (fun X ↦ ⟨X.stage, X.obj, rfl⟩) s
    (StageSystem.PairCategory.hasShift S ℤ) ?_ c
    (fun i ↦ StageSystem.ι_commShift (S := S) (A := ℤ) i) ?_
  · intro n
    refine Functor.hext (hobj n) ?_
    intro X Y f
    induction f using StageSystem.PairCategory.hom_induction with
    | h L hX hY f =>
      exact hmap n X Y L hX hY f
  · intro i n K
    exact hc i n K

private theorem pairShift_transIso
    (s : HasShift S.PairCategory ℤ) (hs : s = StageSystem.PairCategory.hasShift S ℤ)
    (c : ∀ i, @Functor.CommShift _ _ _ _ (S.ι i) ℤ _ _ s)
    (hc : ∀ i n K, HEq ((Functor.commShiftIso (S.ι i) (self := c i) n).hom.app K)
      (𝟙 ((S.ι i).obj ((shiftFunctor (C i) n).obj K))))
    {i j : I} (h : i ≤ j) :
    letI := s
    letI := c
    NatTrans.CommShift (S.transIso h).hom ℤ := by
  subst s
  have hci : c = (fun i ↦ StageSystem.ι_commShift (S := S) (A := ℤ) i) := by
    funext i
    apply integer_commShift_ext
    intro n
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact eq_of_heq (hc i n K)
  subst c
  exact StageSystem.transIso_commShift (S := S) (A := ℤ) h

variable [∀ i, Preadditive (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive] [Preadditive S.PairCategory]

private theorem pairShift_additive
    (hadd : ∀ {X Y : S.PairCategory} {L : I} (hX : X.stage ≤ L) (hY : Y.stage ≤ L)
      (f g : X.toStage hX ⟶ Y.toStage hY),
      StageSystem.PairCategory.mkHom L hX hY f + StageSystem.PairCategory.mkHom L hX hY g =
        StageSystem.PairCategory.mkHom L hX hY (f + g)) (n : ℤ) :
    (shiftFunctor S.PairCategory n).Additive := by
  constructor
  intro X Y f g
  obtain ⟨L, -, hX, hY, _, _, u, v, rfl, rfl⟩ :=
    StageSystem.PairCategory.exists_common_stage f g X.stage
  rw [hadd, StageSystem.PairCategory.shiftFunctor_map_mkHom,
    StageSystem.PairCategory.shiftFunctor_map_mkHom,
    StageSystem.PairCategory.shiftFunctor_map_mkHom]
  refine Eq.trans ?_ (hadd
    (X := ⟨X.stage, (shiftFunctor (C X.stage) n).obj X.obj⟩)
    (Y := ⟨Y.stage, (shiftFunctor (C Y.stage) n).obj Y.obj⟩) hX hY
    (((S.T hX).commShiftIso n).hom.app X.obj ≫
      (shiftFunctor (C L) n).map u ≫ ((S.T hY).commShiftIso n).inv.app Y.obj)
    (((S.T hX).commShiftIso n).hom.app X.obj ≫
      (shiftFunctor (C L) n).map v ≫ ((S.T hY).commShiftIso n).inv.app Y.obj)).symm
  exact congrArg (fun f ↦ StageSystem.PairCategory.mkHom
    (X := ⟨X.stage, (shiftFunctor (C X.stage) n).obj X.obj⟩)
    (Y := ⟨Y.stage, (shiftFunctor (C Y.stage) n).obj Y.obj⟩) L hX hY f)
    (by rw [Functor.map_add]; exact sandwich_add _ _ _ _)

end PairShiftNormalization

attribute [local irreducible] ScalarLocalization.category sfRationalTriangulationDatum

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

private abbrev PairCommon
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {S : StageSystem C} (A B : S.PairCategory) :=
  {L : I // A.stage ≤ L ∧ B.stage ≤ L}
private abbrev PairStageHom
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {S : StageSystem C} (A B : S.PairCategory) (L : PairCommon A B) :=
  (S.T L.property.1).obj A.obj ⟶ (S.T L.property.2).obj B.obj
private theorem generic_coordinates
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (ht : ∀ L M h f, t L M h f = S.tr h f)
    (dt : DirectedSystem (PairStageHom A B) (fun {L M} h ↦ t L M h)) :
    ∃! e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t,
      ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
        AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f := by
  classical
  let q : (A ⟶ B) ≃ _root_.DirectLimit ((PairStageHom A B))
      (fun L M h ↦ t L M h) :=
    { toFun := Quotient.lift
        (fun r : StageSystem.PairCategory.Rep A B ↦
          ⟦⟨⟨r.k, r.hX, r.hY⟩, r.u⟩⟧)
        (by
          rintro r s ⟨N, hr, hs, he⟩
          apply Quotient.sound
          refine ⟨⟨N, r.hX.trans hr, r.hY.trans hr⟩, hr, hs, ?_⟩
          simpa only [ht] using he)
      invFun := Quotient.lift
        (fun r : Σ L : (PairCommon A B), (PairStageHom A B) L ↦
          StageSystem.PairCategory.mkHom r.1.val r.1.property.1 r.1.property.2 r.2)
        (by
          rintro ⟨L, f⟩ ⟨M, g⟩ ⟨N, hL, hM, he⟩
          exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).2
            ⟨N.val, hL, hM, by simpa only [ht] using he⟩)
      left_inv := by intro f; induction f using Quotient.inductionOn; rfl
      right_inv := by intro f; induction f using Quotient.inductionOn; rfl }
  have : DirectedSystem ((PairStageHom A B))
      (fun L M h ↦ (t L M h).toNatLinearMap) := by
    constructor
    · intro L f
      exact @DirectedSystem.map_self _ _ ((PairStageHom A B))
        (fun {L M} h ↦ t L M h) dt L f
    · intro N M L h k f
      exact @DirectedSystem.map_map _ _ ((PairStageHom A B))
        (fun {L M} h ↦ t L M h) dt N M L h k f
  let e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t := q.trans
    (Module.DirectLimit.linearEquiv ((PairStageHom A B))
      (fun L M h ↦ (t L M h).toNatLinearMap)).symm.toEquiv
  have he (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f : (PairStageHom A B) ⟨L, hA, hB⟩) :
      e (StageSystem.PairCategory.mkHom L hA hB f) =
        AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f := by
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Equiv.ext
  intro f
  induction f using StageSystem.PairCategory.hom_induction with
  | h L hA hB f => exact (he' L hA hB f).trans (he L hA hB f).symm

private theorem coordinates_add
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t)
    (he : ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
      AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f)
    (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f g : PairStageHom A B ⟨L, hA, hB⟩) :
    letI := e.addCommGroup
    StageSystem.PairCategory.mkHom L hA hB f +
      StageSystem.PairCategory.mkHom L hA hB g =
        StageSystem.PairCategory.mkHom L hA hB (f + g) := by
  let := e.addCommGroup
  apply e.injective
  rw [show e (_ + _) = e _ + e _ from e.addEquiv.map_add _ _,
    he L hA hB f, he L hA hB g, he L hA hB (f + g)]
  exact (map_add (AddCommGroup.DirectLimit.of (PairStageHom A B) t
    ⟨L, hA, hB⟩) f g).symm

private theorem coordinates_zero
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t)
    (he : ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
      AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f)
    (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L) :
    letI := e.addCommGroup
    StageSystem.PairCategory.mkHom L hA hB
      (0 : PairStageHom A B ⟨L, hA, hB⟩) = 0 := by
  let := e.addCommGroup
  apply e.injective
  rw [he L hA hB (0 : PairStageHom A B ⟨L, hA, hB⟩),
    show e (0 : A ⟶ B) = 0 from e.addEquiv.map_zero]
  exact map_zero (AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩)

private theorem pair_composition_bilinear
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    (S : StageSystem C) [∀ A B : S.PairCategory, AddCommGroup (A ⟶ B)]
    (hadd : ∀ {A B : S.PairCategory} {L : I} (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f g : A.toStage hA ⟶ B.toStage hB),
      StageSystem.PairCategory.mkHom L hA hB f +
        StageSystem.PairCategory.mkHom L hA hB g =
          StageSystem.PairCategory.mkHom L hA hB (f + g)) :
    (∀ (A B C : S.PairCategory) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : S.PairCategory) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  constructor
  · intro A B C f f' g
    obtain ⟨L, -, hA, hB, _, _, u, v, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage f f' A.stage
    obtain ⟨M, hLM, hB', hC, _, _, w, _, rfl, -⟩ :=
      StageSystem.PairCategory.exists_common_stage g g L
    rw [← StageSystem.PairCategory.mkHom_tr hLM u,
      ← StageSystem.PairCategory.mkHom_tr hLM v, hadd,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom, hadd, Preadditive.add_comp]
  · intro A B C f g g'
    obtain ⟨L, -, hB, hC, _, _, v, w, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage g g' B.stage
    obtain ⟨M, hLM, hA, hB', _, _, u, _, rfl, -⟩ :=
      StageSystem.PairCategory.exists_common_stage f f L
    rw [← StageSystem.PairCategory.mkHom_tr hLM v,
      ← StageSystem.PairCategory.mkHom_tr hLM w, hadd,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom, hadd, Preadditive.comp_add]

private theorem stage_transport_additive
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    [∀ i, Preadditive (C i)] (S : StageSystem C)
    {i j n p : I} (hi : i ≤ n) (hj : j ≤ n) (h : n ≤ p)
    [(S.T h).Additive] (x : C i) (y : C j) :
    S.tr (hi := hi) (hj := hj) h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 ∧
      ∀ f g : (S.T hi).obj x ⟶ (S.T hj).obj y,
        S.tr h (f + g) = S.tr h f + S.tr h g := by
  constructor
  · simp only [StageSystem.tr, Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
  · intro f g
    simp only [StageSystem.tr, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

private theorem stage_transport_self
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) {i j n : I} (hi : i ≤ n) (hj : j ≤ n)
    [(S.T (le_refl n)).Faithful] (x : C i) (y : C j)
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) : S.tr (le_refl n) f = f := by
  apply (S.T (le_refl n)).map_injective
  apply (StageSystem.tr_injective (S := S) (le_refl n)).mp
  exact StageSystem.tr_tr (S := S) (le_refl n) (le_refl n) f

private theorem stage_spec_existsUnique
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    (T : ∀ {i j : I}, i ≤ j → C i ⥤ C j)
    (a : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), T h ⋙ T h' ≅ T (h.trans h'))
    (c : ∀ {i j k m : I} (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ m),
      Functor.whiskerRight (a h h').hom (T h'') ≫ (a (h.trans h') h'').hom =
        (Functor.associator (T h) (T h') (T h'')).hom ≫
          Functor.whiskerLeft (T h) (a h' h'').hom ≫ (a h (h'.trans h'')).hom) :
    ∃! R : StageSystem C,
      (∀ (i j : I) (h : i ≤ j), R.T h = T h) ∧
      (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), HEq (R.assoc h h') (a h h')) := by
  let S : StageSystem C :=
    { T := T
      assoc := a
      cocycle := fun h h' h'' X ↦ by
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, Category.id_comp] using
          NatTrans.congr_app (c h h' h'') X }
  refine ⟨S, ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩, ?_⟩
  rintro ⟨T', a', c'⟩ ⟨hT, ha⟩
  have ht : @T' = @T := by funext i j h; exact hT i j h
  cases ht
  have he : @a' = @a := by funext i j k h h'; exact eq_of_heq (ha i j k h h')
  cases he
  rfl

private theorem exact_cast
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) (e : F = G) (c : G.CommShift ℤ)
    (hc : @Functor.IsTriangulated _ _ _ _ _ _ G c _ _ _ _ _ _ _ _) :
    @Functor.IsTriangulated _ _ _ _ _ _ F
      (cast (congrArg (fun H : C ⥤ D ↦ H.CommShift ℤ) e.symm) c)
      _ _ _ _ _ _ _ _ := by
  subst G
  exact hc

private theorem compIso_commShift_cast
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    (hF : F = F') (hG : G = G') (hH : H = H')
    (cF : F'.CommShift ℤ) (cG : G'.CommShift ℤ) (cH : H'.CommShift ℤ)
    (a : F ⋙ G ≅ H) (a' : F' ⋙ G' ≅ H') (ha : HEq a a')
    (hc : letI := cF; letI := cG; letI := cH; NatTrans.CommShift a'.hom ℤ) :
    letI := cast (congrArg (fun J : C ⥤ D ↦ J.CommShift ℤ) hF.symm) cF
    letI := cast (congrArg (fun J : D ⥤ E ↦ J.CommShift ℤ) hG.symm) cG
    letI := cast (congrArg (fun J : C ⥤ E ↦ J.CommShift ℤ) hH.symm) cH
    NatTrans.CommShift a.hom ℤ := by
  subst F'
  subst G'
  subst H'
  obtain rfl := eq_of_heq ha
  exact hc

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

section
attribute [local irreducible] stageCategory transition associator unitor
  stagePreadditive stageShift stagePretriangulated

private theorem associator_pentagon
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) :
    Functor.whiskerRight (associator D l hl Ω Y E L M h k).hom (transition D l hl Ω Y M N m) ≫
        (associator D l hl Ω Y E M N (h.trans k) m).hom =
      (Functor.associator (transition D l hl Ω Y E L h) (transition D l hl Ω Y L M k)
        (transition D l hl Ω Y M N m)).hom ≫
      Functor.whiskerLeft (transition D l hl Ω Y E L h) (associator D l hl Ω Y L M N k m).hom ≫
        (associator D l hl Ω Y E L N h (k.trans m)).hom := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
    associator_cocycle D l hl Ω Y E L M N h k m K

/-- The tensor transitions and associators uniquely determine the stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take T to be transition and assoc to be associator; associator_cocycle is
precisely the required coherence equation. Conversely the displayed equalities fix
all data fields of StageSystem; the remaining cocycle proof is proof irrelevant. -/
theorem stageSystem_existsUnique
    (D : WeilConjectures.FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    :
    ∃! S : StageSystem (SfAlgebraicallyClosedCoefficients.Stage D l hl Ω Y),
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L), S.T h =
          SfAlgebraicallyClosedCoefficients.transition D l hl Ω Y E L h) ∧
      (∀ (E L M : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (k : L ≤ M),
        HEq (S.assoc h k) (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E L M h k)) := by
  exact stage_spec_existsUnique
    (fun {E L} h ↦ transition D l hl Ω Y E L h)
    (fun {E L M} h k ↦ associator D l hl Ω Y E L M h k)
    (fun {E L M N} h k m ↦ associator_pentagon D l hl Ω Y E L M N h k m)

end

attribute [local irreducible] stageCategory

/-- The stage system with exactly the specified tensor functors and associators.
The uniqueness specification fixes every data field, retaining a small opaque interface
for later elaboration of dependent representative types.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageSystem : StageSystem (Stage D l hl Ω Y) :=
  (stageSystem_existsUnique D l hl Ω Y).exists.choose

/-- The existing tensor functor as a transition of the uniquely fixed stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageTransition (E L : Index l Ω) (h : E ≤ L) :=
  (stageSystem D l hl Ω Y).T h

/-- The specified shift comparison transported by equality of the transition functors.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).CommShift ℤ :=
  cast (congrArg (fun F : Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L ↦ F.CommShift ℤ)
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h).symm)
    (transitionCommShift D l hl Ω Y E L h)

/-- Exactness of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: stageSystem_existsUnique identifies this functor and its shift comparison
with the specified tensor extension. Apply transitionExact. -/
@[instance]
theorem stageTransition_exact
    (D : WeilConjectures.FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    (SfAlgebraicallyClosedCoefficients.stageTransition D l hl Ω Y E L h).IsTriangulated := by
  exact exact_cast _ _
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h)
    (transitionCommShift D l hl Ω Y E L h) (transitionExact D l hl Ω Y E L h)

/-- Additivity of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: equality of functors with transition reduces the claim to transitionAdditive. -/
@[instance]
theorem stageTransition_additive
    (D : WeilConjectures.FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    (SfAlgebraicallyClosedCoefficients.stageTransition D l hl Ω Y E L h).Additive := by
  unfold stageTransition
  rw [(stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h]
  exact transitionAdditive D l hl Ω Y E L h

private theorem stageAssociator_commShift (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    NatTrans.CommShift ((stageSystem D l hl Ω Y).assoc h k).hom ℤ := by
  exact compIso_commShift_cast
    (stageTransition D l hl Ω Y E L h) (transition D l hl Ω Y E L h)
    (stageTransition D l hl Ω Y L M k) (transition D l hl Ω Y L M k)
    (stageTransition D l hl Ω Y E M (h.trans k)) (transition D l hl Ω Y E M (h.trans k))
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h)
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 L M k)
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E M (h.trans k))
    (transitionCommShift D l hl Ω Y E L h) (transitionCommShift D l hl Ω Y L M k)
    (transitionCommShift D l hl Ω Y E M (h.trans k))
    ((stageSystem D l hl Ω Y).assoc h k) (associator D l hl Ω Y E L M h k)
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.2 E L M h k)
    (associator_commShift D l hl Ω Y E L M h k)

attribute [local instance] stageAssociator_commShift

/-- The upstream common-stage pair category, specialized to the specified rational stages.
Its objects are literal pairs, and no idempotents are adjoined.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Pair := (stageSystem D l hl Ω Y).PairCategory

/-- Cache the existing upstream category on the named concrete pair type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pairCategory : Category (Pair D l hl Ω Y) :=
  inferInstanceAs (Category (stageSystem D l hl Ω Y).PairCategory)

variable {D l hl Ω Y}

/-- The directed index of common finite coefficient overfields of two pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev Common (A B : Pair D l hl Ω Y) :=
  {L : Index l Ω // A.stage ≤ L ∧ B.stage ≤ L}

/-- The compositum of the source and target fields supplies a common coefficient stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonNonempty (A B : Pair D l hl Ω Y) : Nonempty (Common A B) :=
  ⟨⟨Padic.finiteCoefficientCompositum l Ω A.stage B.stage,
    (Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage⟩⟩

/-- Composita make the common-overfield poset directed while retaining both lower bounds.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDirected (A B : Pair D l hl Ω Y) :
    IsDirectedOrder (Common A B) where
  directed L M :=
    ⟨⟨Padic.finiteCoefficientCompositum l Ω L.val M.val,
        L.property.1.trans ((Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val).1,
        L.property.2.trans ((Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val).1⟩,
      (Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val⟩

/-- Hom at one common coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def StageHom (A B : Pair D l hl Ω Y) (L : Common A B) :=
  ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
    (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj)

/-- Cache the abelian group of a stage Hom before forming the dependent colimit family.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageHomAddCommGroup (A B : Pair D l hl Ω Y) (L : Common A B) :
    AddCommGroup (StageHom A B L) :=
  inferInstanceAs (AddCommGroup
    ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
      (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj))

/-- Extend the representative and conjugate by the specified associators.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transport (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L) : StageHom A B M :=
  ((stageSystem D l hl Ω Y).assoc L.property.1 h).inv.app A.obj ≫
    (stageTransition D l hl Ω Y L.val M.val h).map f ≫
    ((stageSystem D l hl Ω Y).assoc L.property.2 h).hom.app B.obj

/-- Transport is additive and preserves zero.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: scalar extension is additive. Left and right composition by each fixed
associator component are additive by preadditivity of the rational target stage. -/
theorem transport_additive
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) (L M :
        SfAlgebraicallyClosedCoefficients.Common A B) (h : L ≤ M) :
    SfAlgebraicallyClosedCoefficients.transport A B L M h 0 = 0 ∧
      ∀ f g, SfAlgebraicallyClosedCoefficients.transport A B L M h (f + g) =
        SfAlgebraicallyClosedCoefficients.transport A B L M h f +
            SfAlgebraicallyClosedCoefficients.transport A B L M h g := by
  exact stage_transport_additive (stageSystem D l hl Ω Y)
    L.property.1 L.property.2 h A.obj B.obj

/-- The transition homomorphism of the directed Hom system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transportHom (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M) :
    StageHom A B L →+ StageHom A B M where
  toFun := transport A B L M h
  map_zero' := (transport_additive A B L M h).1
  map_add' := (transport_additive A B L M h).2

/-- The actual representative transports form a directed system of abelian groups.
Source: blueprint order 1462, displayed Hom colimit
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: for a reflexive extension, the normalized tensor unit and the two unit coherence
laws identify the conjugated map with the original map. For two successive extensions,
expand transport and use the associator cocycle and naturality; the inner inverse
associators cancel. This gives identity and composition on each representative. -/
@[instance]
theorem transportSystem (A B : Pair D l hl Ω Y) :
    DirectedSystem (StageHom A B) (fun {L M} h ↦ transportHom A B L M h) := by
  -- Faithfulness turns the cocycle's idempotent reflexive transport into the identity.
  constructor
  · intro L f
    have hf : (stageTransition D l hl Ω Y L.val L.val le_rfl).Faithful := by
      unfold stageTransition
      rw [(stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 L.val L.val le_rfl]
      exact Functor.Faithful.of_iso (unitor D l hl Ω Y L.val).symm
    exact stage_transport_self (stageSystem D l hl Ω Y)
      L.property.1 L.property.2 A.obj B.obj f
  · intro N M L h k f
    exact StageSystem.tr_tr (S := stageSystem D l hl Ω Y) h k f

/-- Decidable equality is used only to realize Mathlib's algebraic direct limit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDecidableEq (A B : Pair D l hl Ω Y) :
    DecidableEq (Common A B) := Classical.decEq _

/-- The actual abelian-group colimit, with no completion of its objects.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def ColimitHom (A B : Pair D l hl Ω Y) :=
  AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)

/-- The direct limit's abelian group structure, on the fixed Hom type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance colimitHomGroup (A B : Pair D l hl Ω Y) : AddCommGroup (ColimitHom A B) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)))

/-- The class of a map over a common finite coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def colimitOf (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : ColimitHom A B :=
  AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B) ⟨L, hA, hB⟩ f

/-- The upstream quotient Hom has exactly the stated abelian-colimit coordinates.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: send each common-stage representative to its direct-limit class. The tensor
cocycle and unit law make transport a directed system; the quotient relation is exactly
equality after extension. The direct-limit representative criterion therefore makes
this map well-defined and bijective. Every Hom is represented, proving uniqueness. -/
theorem homCoordinates_existsUnique
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) :
    ∃! e : (A ⟶ B) ≃ SfAlgebraicallyClosedCoefficients.ColimitHom A B,
      ∀ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (f : SfAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩),
        e (StageSystem.PairCategory.mkHom L hA hB f) = SfAlgebraicallyClosedCoefficients.colimitOf A
            B L hA hB f := by
  exact @generic_coordinates (Index l Ω) inferInstance inferInstance (Stage D l hl Ω Y)
    (fun E ↦ stageCategory D l hl Ω Y E)
    (stageSystem D l hl Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (fun _ _ _ _ ↦ rfl) (transportSystem A B)

/-- The canonical Hom coordinates, fixed on every common-stage representative.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def homCoordinates (A B : Pair D l hl Ω Y) :=
  (homCoordinates_existsUnique A B).exists.choose

/-- The abelian group transported from the specified directed colimit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance homAddCommGroup (A B : Pair D l hl Ω Y) : AddCommGroup (A ⟶ B) :=
  (homCoordinates A B).addCommGroup

/-- The map represented at L, using the existing upstream quotient constructor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev ofHom (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : A ⟶ B :=
  StageSystem.PairCategory.mkHom L hA hB f

private theorem mkHom_add {A B : Pair D l hl Ω Y} {L : Index l Ω}
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f g : A.toStage hA ⟶ B.toStage hB) :
    StageSystem.PairCategory.mkHom L hA hB f +
      StageSystem.PairCategory.mkHom L hA hB g =
        StageSystem.PairCategory.mkHom L hA hB (f + g) := by
  exact @coordinates_add (Index l Ω) inferInstance inferInstance (Stage D l hl Ω Y)
    (fun E ↦ stageCategory D l hl Ω Y E)
    (stageSystem D l hl Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (homCoordinates A B)
    (homCoordinates_existsUnique A B).exists.choose_spec L hA hB f g

private theorem mkHom_zero {A B : Pair D l hl Ω Y} {L : Index l Ω}
    (hA : A.stage ≤ L) (hB : B.stage ≤ L) :
    StageSystem.PairCategory.mkHom L hA hB (0 : A.toStage hA ⟶ B.toStage hB) = 0 := by
  exact @coordinates_zero (Index l Ω) inferInstance inferInstance (Stage D l hl Ω Y)
    (fun E ↦ stageCategory D l hl Ω Y E)
    (stageSystem D l hl Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (homCoordinates A B)
    (homCoordinates_existsUnique A B).exists.choose_spec L hA hB

/-- The fixed composition is additive in each variable.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: represent the three maps at a common compositum. Colimit structure maps are
additive and stage composition is bilinear, giving both asserted equations. -/
theorem composition_bilinear
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    :
    (∀ (A B C : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  exact pair_composition_bilinear (stageSystem D l hl Ω Y)
    (fun hA hB f g ↦ mkHom_add hA hB f g)

/-- Preadditivity uses the actual colimit abelian groups.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance preadditive : Preadditive (Pair D l hl Ω Y) where
  homGroup A B := homAddCommGroup A B
  add_comp A B C f f' g := composition_bilinear.1 A B C f f' g
  comp_add A B C f g g' := composition_bilinear.2 A B C f g g'

/-- The existing upstream inclusion of the actual rational finite stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev inclusion (E : Index l Ω) : Stage D l hl Ω Y E ⥤ Pair D l hl Ω Y :=
  (stageSystem D l hl Ω Y).ι E

/-- The inclusion preserves the abelian-colimit addition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: inclusion sends f to its normalized representative, and homCoordinates sends
that representative to its direct-limit class. Both normalization by fixed unit
components and the direct-limit structure maps are additive. -/
@[instance]
theorem inclusion_additive
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (E : Padic.FiniteCoefficientFields l Ω) : (SfAlgebraicallyClosedCoefficients.inclusion E :
        SfAlgebraicallyClosedCoefficients.Stage D l hl Ω Y E ⥤ _).Additive := by
  constructor
  intro X Z f g
  rw [StageSystem.ι_map_eq le_rfl, StageSystem.ι_map_eq le_rfl,
    StageSystem.ι_map_eq le_rfl, Functor.map_add]
  exact (mkHom_add (D := D) (l := l) (hl := hl) (Ω := Ω) (Y := Y)
    (A := ⟨E, X⟩) (B := ⟨E, Z⟩) le_rfl le_rfl _ _).symm

/-- Every class has a finite representative, and equality is equality at a later stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: composita make each common-overfield index nonempty and directed. The normalized
tensor unit and associator pentagon make transport an actual directed system. Apply
Mathlib's directed-colimit representation and zero-exactness criteria to the difference
of two representatives. This gives precisely equality after one further extension. -/
theorem representatives
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) :
    (∀ f : A ⟶ B, ∃ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (u : SfAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩), f =
          SfAlgebraicallyClosedCoefficients.ofHom A B L hA hB u) ∧
    (∀ (L M : SfAlgebraicallyClosedCoefficients.Common A B) (f :
        SfAlgebraicallyClosedCoefficients.StageHom A B L) (g :
        SfAlgebraicallyClosedCoefficients.StageHom A B M),
      SfAlgebraicallyClosedCoefficients.ofHom A B L.val L.property.1 L.property.2 f =
          SfAlgebraicallyClosedCoefficients.ofHom A B M.val M.property.1 M.property.2 g ↔
        ∃ (N : SfAlgebraicallyClosedCoefficients.Common A B) (hL : L ≤ N) (hM : M ≤ N),
          SfAlgebraicallyClosedCoefficients.transport A B L N hL f =
              SfAlgebraicallyClosedCoefficients.transport A B M N hM g) := by
  constructor
  · intro f
    induction f using StageSystem.PairCategory.hom_induction with
    | h L hA hB f => exact ⟨L, hA, hB, f, rfl⟩
  · intro L M f g
    constructor
    · intro e
      obtain ⟨N, hL, hM, he⟩ :=
        (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).mp e
      exact ⟨⟨N, L.property.1.trans hL, L.property.2.trans hL⟩, hL, hM, he⟩
    · rintro ⟨N, hL, hM, he⟩
      exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).mpr
        ⟨N.val, hL, hM, he⟩

/-- Stagewise object shift, with the coefficient field unchanged.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftPair (n : ℤ) (A : Pair D l hl Ω Y) : Pair D l hl Ω Y :=
  ⟨A.stage, (shiftFunctor (Stage D l hl Ω Y A.stage) n).obj A.obj⟩

/-- The shifted representative uses the prescribed scalar-extension shift comparison.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftRepresentative (n : ℤ) (A B : Pair D l hl Ω Y)
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) :
    StageHom (shiftPair n A) (shiftPair n B) ⟨L, hA, hB⟩ :=
  ((stageTransition D l hl Ω Y A.stage L hA).commShiftIso n).hom.app A.obj ≫
    (shiftFunctor (Stage D l hl Ω Y L) n).map f ≫
    ((stageTransition D l hl Ω Y B.stage L hB).commShiftIso n).inv.app B.obj

set_option linter.unusedVariables false in
/-- The induced shift is specified on every object, representative and stage inclusion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: shift each finite representative using shiftRepresentative. Exact scalar
extension and associator compatibility with shifts make this independent of stage.
The finite-stage shift units and addition isomorphisms descend componentwise; equality
and coherence may be checked after moving the finite diagrams to a common field.
The inclusion comparisons are identities on the displayed shifted pairs. Thus these
formulas determine the functors and their coherent comparisons on the generators.
Every object is literally in its own stage. The identity inclusion comparisons and
their coherence equations fix the zero and addition comparisons there, hence everywhere.
This proves uniqueness of the full shift structure, not just its object and arrow maps. -/
theorem shift_existsUnique :
    ∃! s : HasShift (Pair D l hl Ω Y) ℤ,
      (fun [shiftInst : HasShift (Pair D l hl Ω Y) ℤ] ↦
        (∀ n : ℤ, (shiftFunctor (Pair D l hl Ω Y) n).Additive) ∧
        (∀ (n : ℤ) (A : Pair D l hl Ω Y),
          (shiftFunctor (Pair D l hl Ω Y) n).obj A = shiftPair n A) ∧
        (∀ (n : ℤ) (A B : Pair D l hl Ω Y) (L : Index l Ω)
          (hA : A.stage ≤ L) (hB : B.stage ≤ L) (f : StageHom A B ⟨L, hA, hB⟩),
          HEq ((shiftFunctor (Pair D l hl Ω Y) n).map (ofHom A B L hA hB f))
            (ofHom (shiftPair n A) (shiftPair n B) L hA hB
              (shiftRepresentative n A B L hA hB f))) ∧
        ∃ c : ∀ E : Index l Ω, (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ,
          (fun [commInst : ∀ E : Index l Ω,
              (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ] ↦
            ∀ (n : ℤ) (E : Index l Ω) (K : Stage D l hl Ω Y E),
              HEq (((inclusion E : Stage D l hl Ω Y E ⥤ _).commShiftIso n).hom.app K)
                (𝟙 ((inclusion E : Stage D l hl Ω Y E ⥤ _).obj
                  ((shiftFunctor (Stage D l hl Ω Y E) n).obj K)))) (commInst := c))
        (shiftInst := s) := by
  let S := stageSystem D l hl Ω Y
  let s := StageSystem.PairCategory.hasShift S ℤ
  let := s
  refine ⟨s, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n
    exact pairShift_additive S (fun hA hB f g ↦ mkHom_add hA hB f g) n
  · intro n A
    rfl
  · intro n A B L hA hB f
    exact HEq.rfl
  · refine ⟨fun E ↦ StageSystem.ι_commShift (S := S) (A := ℤ) E, ?_⟩
    intro n E K
    exact HEq.rfl
  · intro s' hs'
    obtain ⟨c, hc⟩ := hs'.2.2.2
    exact pairShift_unique S s' hs'.2.1 hs'.2.2.1 c (fun E n K ↦ hc n E K)

/-- The stagewise shift with the representative formula of shift_existsUnique.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance hasShift : HasShift (Pair D l hl Ω Y) ℤ := shift_existsUnique.exists.choose

/-- Each induced integer shift is additive.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (Pair D l hl Ω Y) n).Additive := shift_existsUnique.exists.choose_spec.1 n

/-- The normalized exact-stage shift comparison, fixed to identity on shifted pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusionCommShift (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ :=
  shift_existsUnique.exists.choose_spec.2.2.2.choose E

/-- A stage zero object remains zero after forming directed Hom colimits.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take the zero object at the bottom coefficient field. Every transition is exact
and therefore preserves zero. At every common field its Hom groups to and from any
object vanish. Their directed colimits vanish, giving the zero-object universal property. -/
theorem zero_exists : HasZeroObject (Pair D l hl Ω Y) := by
  let E := Padic.finiteCoefficientBase l Ω
  let X : Pair D l hl Ω Y := (inclusion E).obj (0 : Stage D l hl Ω Y E)
  refine ⟨⟨X, ?_⟩⟩
  rw [IsZero.iff_id_eq_zero, StageSystem.PairCategory.id_eq_mkHom X le_rfl,
    ← mkHom_zero (A := X) (B := X) le_rfl le_rfl]
  have hz : IsZero (X.toStage le_rfl) :=
    Functor.map_isZero (stageTransition D l hl Ω Y E E le_rfl) (isZero_zero _)
  exact congrArg (StageSystem.PairCategory.mkHom E le_rfl le_rfl) (hz.eq_of_src _ _)

attribute [instance] zero_exists

/-- The canonical coefficient-stage identifications commute with shifts.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: on finite representatives this is scalar-extension shift compatibility and
sfRationalScalar_coherence. The normalized inclusion comparisons are
identities on shifted pairs. The cocycle equation identifies both composites. -/
@[instance]
theorem transitionIso_commShift
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    NatTrans.CommShift ((SfAlgebraicallyClosedCoefficients.stageSystem D l hl Ω Y).transIso h).hom ℤ
        := by
  let S := stageSystem D l hl Ω Y
  have hs := (shift_existsUnique (D := D) (l := l) (hl := hl) (Ω := Ω)
    (Y := Y)).exists.choose_spec
  exact pairShift_transIso S (hasShift (D := D) (l := l) (hl := hl) (Ω := Ω) (Y := Y))
    (pairShift_unique S _ hs.2.1 hs.2.2.1
      (fun E ↦ inclusionCommShift E) (fun E n K ↦ hs.2.2.2.choose_spec n E K))
    (fun E ↦ inclusionCommShift E) (fun E n K ↦ hs.2.2.2.choose_spec n E K) h

/-- The recorded common-stage distinguished-triangle criterion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Distinguished (T : Triangle (Pair D l hl Ω Y)) : Prop :=
  (stageSystem D l hl Ω Y).CommonStageDistinguished T

/-- The unique pretriangulation supplied by the common-stage Verdier theorem.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pretriangulated : Pretriangulated (Pair D l hl Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose

/-- The Verdier axiom for the specified common-stage triangles.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance isTriangulated : IsTriangulated (Pair D l hl Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose_spec.2.1

/-- Each actual rational finite-stage inclusion is exact.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusion_exact (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).IsTriangulated :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose_spec.2.2 E

/-- The triangle criterion, exposing the finite-field-of-definition clause.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: this is the distinguished-set clause of commonStage_verdier_existsUnique
for the actual scalar-extension stage system. -/
theorem distinguished_iff
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (T : Triangle (SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)) :
    T ∈ distTriang (SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) ↔
        SfAlgebraicallyClosedCoefficients.Distinguished T := by
  exact (StageSystem.commonStage_verdier_existsUnique
    (stageSystem D l hl Ω Y)).exists.choose_spec.1 T

end SfAlgebraicallyClosedCoefficients

end WeilConjectures
