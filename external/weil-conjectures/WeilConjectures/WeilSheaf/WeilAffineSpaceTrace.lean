/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist
import WeilConjectures.WeilSheaf.OpenClosedTriangle

/-!
# Integration over standard affine space on constructible Weil complexes

Source: vector-bundle Thom theorem, specialized to the standard trivial bundle.
(blueprint: lem-fd-weil-standard-affine-trace)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineSpace

/-- Splitting off a coordinate presents affine space as a trivial line bundle. -/
private theorem option_coordinate_pullback (n : Type u) (S : Scheme.{u}) :
    IsPullback (reindex (Option.some : n → Option n) S)
      (reindex (fun _ : PUnit.{u + 1} ↦ (none : Option n)) S)
      (AffineSpace n S ↘ S) (AffineSpace PUnit.{u + 1} S ↘ S) := by
  let q := reindex (Option.some : n → Option n) S
  let t := reindex (fun _ : PUnit.{u + 1} ↦ (none : Option n)) S
  have hc : q ≫ (AffineSpace n S ↘ S) = t ≫ (AffineSpace PUnit.{u + 1} S ↘ S) :=
    (reindex_over _ S).trans (reindex_over _ S).symm
  let lift (s : PullbackCone (AffineSpace n S ↘ S)
      (AffineSpace PUnit.{u + 1} S ↘ S)) :=
    homOfVector (s.fst ≫ AffineSpace n S ↘ S)
      (fun a : Option n ↦ a.elim (s.snd.appTop (coord S PUnit.unit))
        (fun i ↦ s.fst.appTop (coord S i)))
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk _ lift (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_)⟩⟩
  · refine hom_ext ?_ fun i ↦ ?_
    · simp only [lift, Category.assoc, reindex_over, homOfVector_over]
    · simp only [lift, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        reindex_appTop_coord, homOfVector_appTop_coord, Option.elim_some]
  · refine hom_ext ?_ fun ⟨⟩ ↦ ?_
    · simp only [lift, Category.assoc, reindex_over, homOfVector_over]
      exact s.condition
    · simp only [lift, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        reindex_appTop_coord, homOfVector_appTop_coord, Option.elim_none]
  · refine hom_ext ?_ fun i ↦ ?_
    · have e := congrArg (fun a ↦ a ≫ (AffineSpace n S ↘ S)) hm₁
      simpa only [q, Category.assoc, reindex_over, lift, homOfVector_over] using e
    · cases i with
      | none =>
        have e := congrArg (fun a ↦ a.appTop (coord S PUnit.unit)) hm₂
        simpa only [t, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          reindex_appTop_coord, lift, homOfVector_appTop_coord, Option.elim_none] using e
      | some i =>
        have e := congrArg (fun a ↦ a.appTop (coord S i)) hm₁
        simpa only [q, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          reindex_appTop_coord, lift, homOfVector_appTop_coord, Option.elim_some] using e


end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry.WeilComplex

/-- For any isomorphism, inverse image followed by image with compact support is identity. -/
private theorem iso_integral_edge
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (p : Y ⟶ X) [IsIso p] [p.IsOver (Spec (CommRingCat.of k₀))] :
    Nonempty (upperStar p ⋙ derivedLowerShriek k₀ l p ≅ 𝟭 _) := by
  have sq : IsPullback p p (𝟙 X) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨rfl⟩
  obtain ⟨bc⟩ := nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    (𝟙 X) (𝟙 X) p p sq
  obtain ⟨ui⟩ := nonempty_iso_upperStar_id (k₀ := k₀) (l := l) (X := X)
  obtain ⟨di⟩ := nonempty_iso_derivedLowerShriek_id (k₀ := k₀) (l := l) (X := X)
  exact ⟨bc.symm ≪≫ Functor.isoWhiskerRight di (upperStar (𝟙 X)) ≪≫
    Functor.leftUnitor _ ≪≫ ui⟩
/-- The rank-zero specialization agrees with the zero twist and zero shift. -/
private theorem rank_zero_edge
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    letI : (AffineSpace PEmpty.{u + 1} X).Over (Spec (CommRingCat.of k₀)) :=
      ⟨(AffineSpace PEmpty.{u + 1} X ↘ X) ≫ (X ↘ Spec (CommRingCat.of k₀))⟩
    letI : (AffineSpace PEmpty.{u + 1} X ↘ X).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    Nonempty (upperStar (AffineSpace PEmpty.{u + 1} X ↘ X) ⋙
        derivedLowerShriek k₀ l (AffineSpace PEmpty.{u + 1} X ↘ X) ≅
      tateTwist k₀ l X (-(Fintype.card PEmpty.{u + 1} : ℤ)) ⋙
        shiftFunctor _ (-(2 * (Fintype.card PEmpty.{u + 1} : ℤ)))) := by
  let : (AffineSpace PEmpty.{u + 1} X).Over (Spec (CommRingCat.of k₀)) :=
    ⟨(AffineSpace PEmpty.{u + 1} X ↘ X) ≫ (X ↘ Spec (CommRingCat.of k₀))⟩
  have : (AffineSpace PEmpty.{u + 1} X ↘ X).IsOver
      (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  obtain ⟨e⟩ := iso_integral_edge (k₀ := k₀) (l := l) (AffineSpace PEmpty.{u + 1} X ↘ X)
  obtain ⟨t⟩ := nonempty_iso_tensorLisse_adicConstant (k₀ := k₀) (l := l) (X := X)
  have t₀ : tateTwist k₀ l X 0 ≅ 𝟭 _ := t
  simp only [Fintype.card_pempty, Int.natCast_zero, neg_zero, mul_zero]
  exact ⟨e ≪≫ ((Functor.isoWhiskerRight t₀ (shiftFunctor _ (0 : ℤ))) ≪≫
    Functor.leftUnitor _ ≪≫ shiftFunctorZero _ ℤ).symm⟩


section

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The natural Tate comparison needed to sum the twists in the coordinate tower. -/
private noncomputable def twist_add_edge (m n : ℤ) :
    tateTwist k₀ l X m ⋙ tateTwist k₀ l X n ≅ tateTwist k₀ l X (m + n) :=
  ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tateTwist k₀ l X m) (tateTwistCompιIso n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (tateTwistCompιIso m) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (objectProperty k₀ l X).ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (ProEtaleWeilSheaf.constantTwistCompConstantTwistIso k₀ l X _ _ ≪≫
              ProEtaleWeilSheaf.constantTwistFunctorCongrIso k₀ l X
                (zpow_add (WeilSheaf.cyclotomicUnit k₀ l) m n).symm)) ≪≫
      (tateTwistCompιIso (m + n)).symm)

/-- Tate twists commute with inverse image in the coordinate-tower calculation. -/
private noncomputable def twist_upperStar_edge {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] (m : ℤ) :
    tateTwist k₀ l Y m ⋙ upperStar f ≅ upperStar f ⋙ tateTwist k₀ l X m := by
  let IX := objectProperty k₀ l X
  let IY := objectProperty k₀ l Y
  let U := upperStar (k₀ := k₀) (l := l) f
  let U' := (ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory
  let T'X := (ProEtaleWeilSheaf.constantTwist k₀ l X
    (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategory
  let T'Y := (ProEtaleWeilSheaf.constantTwist k₀ l Y
    (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategory
  have eU : U ⋙ IX.ι ≅ IY.ι ⋙ U' :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  refine (IX.fullyFaithfulι.whiskeringRight _).preimageIso ?_
  exact Functor.associator (tateTwist k₀ l Y m) U IX.ι ≪≫
    Functor.isoWhiskerLeft (tateTwist k₀ l Y m) eU ≪≫
    (Functor.associator (tateTwist k₀ l Y m) IY.ι U').symm ≪≫
    Functor.isoWhiskerRight (tateTwistCompιIso m) U' ≪≫
    Functor.associator IY.ι T'Y U' ≪≫
    Functor.isoWhiskerLeft IY.ι
      (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompUpperStarIso k₀ l f
        (WeilSheaf.cyclotomicUnit k₀ l ^ m)) ≪≫
    (Functor.associator IY.ι U' T'X).symm ≪≫
    Functor.isoWhiskerRight eU.symm T'X ≪≫
    Functor.associator U IX.ι T'X ≪≫
    Functor.isoWhiskerLeft U (tateTwistCompιIso m).symm ≪≫
    (Functor.associator U (tateTwist k₀ l X m) IX.ι).symm


end


private theorem integral_transport_edge
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (f : Y ⟶ X) (g : Z ⟶ X)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : Y ≅ Z) [e.hom.IsOver (Spec (CommRingCat.of k₀))] (he : e.hom ≫ g = f) :
    Nonempty (upperStar f ⋙ derivedLowerShriek k₀ l f ≅
      upperStar g ⋙ derivedLowerShriek k₀ l g) := by
  have sq : IsPullback e.hom f g (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id f).symm⟩
  obtain ⟨bc⟩ := nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    g (𝟙 X) f e.hom sq
  obtain ⟨ui⟩ := nonempty_iso_upperStar_id (k₀ := k₀) (l := l) (X := X)
  obtain ⟨uc⟩ := nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) e.hom g
  let ue := upperStarCongrIso (k₀ := k₀) (l := l) he
  let U := upperStar (k₀ := k₀) (l := l) g
  let D := derivedLowerShriek k₀ l g
  let Df := derivedLowerShriek k₀ l f
  exact ⟨((Functor.rightUnitor (U ⋙ D)).symm ≪≫
    Functor.isoWhiskerLeft (U ⋙ D) ui.symm ≪≫
    Functor.isoWhiskerLeft U bc ≪≫
    (Functor.associator U (upperStar e.hom) Df).symm ≪≫
    Functor.isoWhiskerRight (uc.symm ≪≫ ue) Df).symm⟩

private noncomputable def coordinateIso {α β : Type u} (e : α ≃ β) (X : Scheme.{u}) :
    AffineSpace α X ≅ AffineSpace β X where
  hom := AffineSpace.reindex e.symm X
  inv := AffineSpace.reindex e X
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      simp

private def traceClaim
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] : Prop :=
  letI : (AffineSpace n X).Over (Spec (CommRingCat.of k₀)) :=
    ⟨(AffineSpace n X ↘ X) ≫ (X ↘ Spec (CommRingCat.of k₀))⟩
  letI : (AffineSpace n X ↘ X).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  Nonempty (upperStar (AffineSpace n X ↘ X) ⋙
      derivedLowerShriek k₀ l (AffineSpace n X ↘ X) ≅
    tateTwist k₀ l X (-(Fintype.card n : ℤ)) ⋙
      shiftFunctor _ (-(2 * (Fintype.card n : ℤ))))

private def tower_comparison
    {C B Y : Type*} [Category C] [Category B] [Category Y]
    {U : C ⥤ B} {Q : B ⥤ Y} {D : Y ⥤ B} {V : B ⥤ C}
    {T R S : C ⥤ C} {TB SB : B ⥤ B}
    (line : Q ⋙ D ≅ TB ⋙ SB) (pull : T ⋙ U ≅ U ⋙ TB)
    (shift : SB ⋙ V ≅ V ⋙ S) (ih : U ⋙ V ≅ R) :
    (U ⋙ Q) ⋙ (D ⋙ V) ≅ T ⋙ R ⋙ S :=
  Functor.isoWhiskerLeft U (Functor.isoWhiskerRight line V) ≪≫
    Functor.isoWhiskerRight pull.symm (SB ⋙ V) ≪≫
    Functor.isoWhiskerLeft (T ⋙ U) shift ≪≫
    Functor.isoWhiskerLeft T (Functor.isoWhiskerRight ih S)

private theorem trace_option_step
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n]
    (ih : ∀ (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
      [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))], traceClaim (k₀ := k₀) (l := l) n X)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    traceClaim (k₀ := k₀) (l := l) (Option n) X := by
  let B := AffineSpace n X
  let Y := AffineSpace (Option n) X
  let p : B ⟶ X := AffineSpace n X ↘ X
  let q : Y ⟶ B := AffineSpace.reindex (Option.some : n → Option n) X
  let f : Y ⟶ X := AffineSpace (Option n) X ↘ X
  let : B.Over (Spec (CommRingCat.of k₀)) :=
    ⟨p ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  let : Y.Over (Spec (CommRingCat.of k₀)) :=
    ⟨f ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : p.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : f.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change q ≫ (p ≫ X ↘ Spec (CommRingCat.of k₀)) = _
    rw [← Category.assoc, AffineSpace.reindex_over]
    rfl⟩
  have : LocallyOfFiniteType (B ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (B ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (p ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiSeparated (B ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (p ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : IsSeparated (B ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (IsSeparated (p ≫ X ↘ Spec (CommRingCat.of k₀)))
  let t := AffineSpace.reindex (fun _ : PUnit.{u + 1} ↦ (none : Option n)) X
  let s := t ≫ AffineSpace.map PUnit.{u + 1} (X ↘ Spec (CommRingCat.of k₀))
  have hq := (AffineSpace.option_coordinate_pullback n X).flip.paste_horiz
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) (X ↘ Spec (CommRingCat.of k₀)))
  have : IsSeparated q := MorphismProperty.of_isPullback hq inferInstance
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback hq inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback hq inferInstance
  obtain ⟨trLine⟩ := nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback
    (k₀ := k₀) (l := l) q s hq.flip
  obtain ⟨trRest⟩ := ih X
  obtain ⟨uc⟩ := nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) q p
  obtain ⟨dc⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) q p
  let r := (Fintype.card n : ℤ)
  let T := tateTwist k₀ l X (-1)
  let S := shiftFunctor (WeilComplex k₀ l X) (-2 : ℤ)
  let R := tateTwist k₀ l X (-r) ⋙ shiftFunctor _ (-(2 * r))
  have step : (upperStar p ⋙ upperStar q) ⋙
      (derivedLowerShriek k₀ l q ⋙ derivedLowerShriek k₀ l p) ≅ T ⋙ R ⋙ S :=
    tower_comparison trLine (twist_upperStar_edge p (-1))
      (Functor.commShiftIso (derivedLowerShriek k₀ l p) (-2 : ℤ)) trRest
  have sum : T ⋙ R ⋙ S ≅
      tateTwist k₀ l X (-1 + -r) ⋙ shiftFunctor _ (-(2 * r) + -2) :=
    Functor.isoWhiskerRight (twist_add_edge (-1) (-r))
      (shiftFunctor _ (-(2 * r)) ⋙ S) ≪≫
    Functor.isoWhiskerLeft (tateTwist k₀ l X (-1 + -r))
      (shiftFunctorAdd _ (-(2 * r)) (-2)).symm
  have he : q ≫ p = f := AffineSpace.reindex_over _ X
  have e : upperStar (k₀ := k₀) (l := l) (q ≫ p) ⋙
      derivedLowerShriek k₀ l (q ≫ p) ≅
      tateTwist k₀ l X (-1 + -r) ⋙ shiftFunctor _ (-(2 * r) + -2) :=
    Functor.isoWhiskerRight uc (derivedLowerShriek k₀ l (q ≫ p)) ≪≫
      Functor.isoWhiskerLeft (upperStar p ⋙ upperStar q) dc ≪≫ step ≪≫ sum
  have ha : -1 + -r = -(Fintype.card (Option n) : ℤ) := by
    dsimp [r]
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    ring
  have hb : -(2 * r) + -2 = -(2 * (Fintype.card (Option n) : ℤ)) := by
    dsimp [r]
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    ring
  rw [ha, hb] at e
  have ueq := upperStarCongrIso (k₀ := k₀) (l := l) he
  have deq := derivedLowerShriekIsoOfEq (k₀ := k₀) (l := l) he
  exact ⟨Functor.isoWhiskerRight ueq.symm (derivedLowerShriek k₀ l f) ≪≫
    Functor.isoWhiskerLeft (upperStar (q ≫ p)) deq.symm ≪≫ e⟩

private theorem trace_reindex_step
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {α β : Type u} [Fintype α] [Fintype β] (e : α ≃ β)
    (ih : ∀ (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
      [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))], traceClaim (k₀ := k₀) (l := l) α X) :
    ∀ (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
      [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))], traceClaim (k₀ := k₀) (l := l) β X := by
  intro X _ _ _ _ _
  let pα := AffineSpace α X ↘ X
  let pβ := AffineSpace β X ↘ X
  let : (AffineSpace α X).Over (Spec (CommRingCat.of k₀)) :=
    ⟨pα ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  let : (AffineSpace β X).Over (Spec (CommRingCat.of k₀)) :=
    ⟨pβ ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : pα.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : pβ.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  let eA := coordinateIso e X
  have he : eA.hom ≫ pβ = pα := AffineSpace.reindex_over _ X
  have : eA.hom.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change eA.hom ≫ (pβ ≫ X ↘ Spec (CommRingCat.of k₀)) = _
    rw [← Category.assoc, he]
    rfl⟩
  obtain ⟨tr⟩ := ih X
  obtain ⟨transport⟩ := integral_transport_edge (k₀ := k₀) (l := l) pα pβ eA he
  have hc : Fintype.card α = Fintype.card β := Fintype.card_congr e
  refine ⟨transport.symm ≪≫ ?_⟩
  simpa only [hc] using tr

private theorem trace_all
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n] :
    ∀ (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
      [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))], traceClaim (k₀ := k₀) (l := l) n X := by
  refine Fintype.induction_empty_option
    (P := fun n _ ↦ ∀ (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
      [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))], traceClaim (k₀ := k₀) (l := l) n X)
    ?_ ?_ ?_ n
  · intro α β _ e ih
    let : Fintype α := Fintype.ofEquiv β e.symm
    exact trace_reindex_step (k₀ := k₀) (l := l) e ih
  · intro X _ _ _ _ _
    exact rank_zero_edge (k₀ := k₀) (l := l) X
  · intro α _ ih
    exact trace_option_step (k₀ := k₀) (l := l) α ih



/-- The trace of the standard affine-space projection on arbitrary Weil complexes.
Source: `lemma-integral-linear-character--1`, convolution-kernel proof Step 4.

Proof: induct on the finite coordinate type. For the empty type the structure
map is an isomorphism, so its integral is the identity and the zero twist and
zero shift are identities. In the inductive step split off one coordinate.
The resulting map to the remaining affine space is a trivial line bundle.
The relative affine-line trace computes its integral as `(-1)[-2]`. Compose
with the induction hypothesis for the remaining coordinates. Pullback and
compact-support composition factor the full integral. Pullback commutes with
Tate lines, so bring the line twist to the original base; compact-support
images commute with shifts. Tensor multiplication of Tate lines adds the
twists, and shift composition adds degrees. Reindexing the coordinate type is
an isomorphism over the base and compact-support base change transports the
result through it. All the comparisons are natural in the input Weil complex.
No character or support statement is involved.
(blueprint: lem-fd-weil-standard-affine-trace) -/
theorem nonempty_iso_affineSpace_integral
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    letI : (AffineSpace n X).Over (Spec (CommRingCat.of k₀)) :=
      ⟨(AffineSpace n X ↘ X) ≫ (X ↘ Spec (CommRingCat.of k₀))⟩
    letI : (AffineSpace n X ↘ X).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    Nonempty (upperStar (AffineSpace n X ↘ X) ⋙
        derivedLowerShriek k₀ l (AffineSpace n X ↘ X) ≅
      tateTwist k₀ l X (-(Fintype.card n : ℤ)) ⋙
        shiftFunctor _ (-(2 * (Fintype.card n : ℤ)))) := by
  exact trace_all (k₀ := k₀) (l := l) n X

end AlgebraicGeometry.WeilComplex
