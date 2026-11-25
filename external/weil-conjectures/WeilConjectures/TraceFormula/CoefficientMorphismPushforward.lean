/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CoefficientMorphismBasic
public import WeilConjectures.TraceFormula.FibreModel
public import WeilConjectures.TraceFormula.RelativeFrobeniusIterate

/-!

# The trace formula along a morphism with proper fibres

Let `f : X ⟶ Y` be the base change of a morphism of models over a finite field, commuting with
the model Frobenii. The pushforward `ψ' = Rf_! ψ ∘ θ_f` of a Frobenius coefficient morphism `ψ`
(`ProEtale.CondensedRing.lowerShriekFrobeniusCoefficient`) has the same global operator
(`ProEtale.CondensedRing.frobeniusCompactOperator_lowerShriekFrobeniusCoefficient`), and its stalk
map at a fixed point `y` is the global operator of the restriction of `ψ` to the fibre
(`ProEtale.CondensedRing.stalk_lowerShriekFrobeniusCoefficient_iterate`). Hence the trace formula
on `Y` and on the fibres gives the trace formula on `X` (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 4, with
`lemma-comparison-via-relative-frobenius--4`). The trace formula on the fibres, which are proper in
the application, is taken as a hypothesis for all proper models.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-! ### Fixed points and fibres -/

section Fibre

variable {k₁ : Type u} [Field k₁] {X₁ Y₁ : Over (Spec (.of k₁))} {ΦX₁ : X₁ ⟶ X₁} {ΦY₁ : Y₁ ⟶ Y₁}
  {f₁ : X₁ ⟶ Y₁}

/-- A rational point fixed by `Φ` is fixed by the first iterate `Φ_1 = Φ`. -/
lemma comp_frobeniusIterate_one_of_comp_eq {y : RationalPoint Y₁} (hy : y ≫ ΦY₁ = y) :
    y ≫ frobeniusIterate ΦY₁ 1 = y := by
  rwa [frobeniusIterate_one]

/-- The fibre of `f : X ⟶ Y` at a rational point `y` is cartesian over `y`, with the structure
morphism of the fibre as second projection. -/
lemma isPullback_pullbackFst_toPoint (f : X₁ ⟶ Y₁) (y : RationalPoint Y₁) :
    IsPullback (pullback.fst f y) (toPoint (pullback f y)) f y := by
  rw [toPoint_ext (toPoint _) (pullback.snd f y)]
  exact IsPullback.of_hasPullback f y

/-- A rational point of the fibre `X ×_Y y` fixed by the restriction of `Φ_X` gives a rational point
of `X` fixed by `Φ_X`. -/
lemma comp_fst_comp_eq_of_comp_fibreFrobenius_eq (hf : ΦX₁ ≫ f₁ = f₁ ≫ ΦY₁)
    {y : RationalPoint Y₁}
    (hy : y ≫ frobeniusIterate ΦY₁ 1 = y) {z : RationalPoint (pullback f₁ y)}
    (hz : z ≫ fibreFrobenius f₁ hf 1 y hy = z) :
    (z ≫ pullback.fst f₁ y) ≫ ΦX₁ = z ≫ pullback.fst f₁ y := by
  have h := fibreFrobenius_fst f₁ hf 1 y hy
  rw [frobeniusIterate_one] at h
  rw [Category.assoc, ← h, ← Category.assoc, hz]

/-- The map `x ↦ x ≫ f` from the rational points of `X` fixed by `Φ_X` to the rational points
of `Y` fixed by `Φ_Y`, for `Φ_X ≫ f = f ≫ Φ_Y`. -/
noncomputable def fixedPointComp (hf : ΦX₁ ≫ f₁ = f₁ ≫ ΦY₁)
    (x : {x : RationalPoint X₁ // x ≫ ΦX₁ = x}) :
    {y : RationalPoint Y₁ // y ≫ ΦY₁ = y} :=
  ⟨x.1 ≫ f₁, by rw [Category.assoc, ← hf, ← Category.assoc, x.2]⟩

/-- The rational points of `X` fixed by `Φ_X` lying over a rational point `y` of `Y` fixed by
`Φ_Y` are the rational points of the fibre `X ×_Y y` fixed by the restriction of `Φ_X`
(blueprint `lemma-comparison-via-relative-frobenius--4`). -/
noncomputable def fixedPointCompFibreEquiv (hf : ΦX₁ ≫ f₁ = f₁ ≫ ΦY₁)
    (y : {y : RationalPoint Y₁ // y ≫ ΦY₁ = y}) :
    {x : {x : RationalPoint X₁ // x ≫ ΦX₁ = x} // fixedPointComp hf x = y} ≃
      {z : RationalPoint (pullback f₁ y.1) //
        z ≫ fibreFrobenius f₁ hf 1 y.1 (comp_frobeniusIterate_one_of_comp_eq y.2) = z} where
  toFun x := ⟨pullback.lift x.1.1 (𝟙 _) (by
      rw [Category.id_comp]
      exact congrArg Subtype.val x.2), pullback.hom_ext
    (by rw [Category.assoc, fibreFrobenius_fst, pullback.lift_fst_assoc, frobeniusIterate_one,
      x.1.2, pullback.lift_fst])
    (toPoint_ext _ _)⟩
  invFun z := ⟨⟨z.1 ≫ pullback.fst f₁ y.1, comp_fst_comp_eq_of_comp_fibreFrobenius_eq hf _ z.2⟩,
    Subtype.ext (by
      dsimp only [fixedPointComp]
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        toPoint_ext (z.1 ≫ pullback.snd f₁ y.1) (𝟙 _), Category.id_comp])⟩
  left_inv x := Subtype.ext (Subtype.ext (pullback.lift_fst _ _ _))
  right_inv z := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _) (toPoint_ext _ _))

/-- The structure morphism of the model `Z₀` of a quasi-compact `Z = Z₀ ×_{k₀} k` is
quasi-compact: the projection `Z ⟶ Z₀` is surjective, as the base change of
`Spec k ⟶ Spec k₀`, so `Z₀` is quasi-compact. -/
lemma IsModelFrobenius.quasiCompact {Z : Over (Spec (.of k₁))} [QuasiCompact Z.hom]
    {Φ : Z ⟶ Z} {k₀ : Type u} [Field k₀] [Algebra k₀ k₁] {Z₀ : Scheme.{u}}
    {g₀ : Z₀ ⟶ Spec (.of k₀)} {p : Z.left ⟶ Z₀} (h : IsModelFrobenius Φ g₀ p) :
    QuasiCompact g₀ := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) :=
    ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Surjective p := MorphismProperty.IsStableUnderBaseChange.of_isPullback h.isPullback.flip
    this
  have := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace Z₀ := p.surjective.compactSpace p.continuous
  infer_instance

end Fibre

section FibreFiniteness

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The fibre `X ×_Y y` of `f : X ⟶ Y` at a rational point `y` is the base change of `f` along
`y`. -/
lemma isPullback_pullbackFst_left (f : X ⟶ Y) (y : RationalPoint Y) :
    IsPullback (pullback.fst f y).left (pullback f y).hom f.left y.left := by
  have hZ := (IsPullback.of_hasPullback f y).map (Over.forget _)
  simp only [Over.forget_map] at hZ
  have h : (pullback f y).hom = (pullback.snd f y).left := by
    rw [← Over.w (pullback.snd f y)]
    exact (Category.comp_id _).symm
  rw [h]
  exact hZ

omit [QuasiCompact X.hom] [IsSeparated X.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
instance (f : X ⟶ Y) (y : RationalPoint Y) : LocallyOfFiniteType (pullback f y).hom := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have := locallyOfFiniteType_of_comp f.left Y.hom
  exact MorphismProperty.of_isPullback (isPullback_pullbackFst_left f y) this

omit [LocallyOfFiniteType X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] in
instance (f : X ⟶ Y) (y : RationalPoint Y) : QuasiCompact (pullback f y).hom := by
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have := QuasiCompact.of_comp f.left Y.hom
  exact MorphismProperty.of_isPullback (isPullback_pullbackFst_left f y) this

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] in
instance (f : X ⟶ Y) (y : RationalPoint Y) : IsSeparated (pullback f y).hom := by
  have : IsSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have := IsSeparated.of_comp f.left Y.hom
  exact MorphismProperty.of_isPullback (isPullback_pullbackFst_left f y) this

end FibreFiniteness

/-- **The trace of the stalk map of the pushforward at a fixed point** (blueprint
`lemma-comparison-via-relative-frobenius--4`): for `y` fixed by `Φ_Y` with proper fibre
`Z = X ×_Y y`, proper base change identifies the stalk map at `y` of `ψ' = Rf_! ψ ∘ θ_f` with the
degree-one global operator of the restriction of `ψ` to `Z`; by the trace formula on the proper
model `Z`, its trace is the sum of the traces of the stalk maps of `ψ` at the fixed points of `X` in
`Z`. -/
theorem trace_graphStalkMap_lowerShriekFrobeniusCoefficient [IsAlgClosed k] {k₀ : Type u}
    [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ Y₀ : Scheme.{u}} {fX₀ : X₀ ⟶ Spec (.of k₀)}
    {fY₀ : Y₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType fX₀] {pX : X.left ⟶ X₀}
    {pY : Y.left ⟶ Y₀} {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} (hX : IsModelFrobenius ΦX fX₀ pX)
    (hY : IsModelFrobenius ΦY fY₀ pY) [IsFinite ΦX.left] [IsUniversalHomeomorphism ΦX.left]
    [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left] {f : X ⟶ Y} (hf : ΦX ≫ f = f ≫ ΦY)
    {f₀ : X₀ ⟶ Y₀} (hfp : f.left ≫ pY = pX ≫ f₀) (h₀ : f₀ ≫ fY₀ = fX₀)
    (y : RationalPoint Y) (hy : y ≫ ΦY = y)
    (hfib : ∀ (k' : Type u) [Field k'] [Finite k'] [Algebra k' k] (Z₀ : Scheme.{u})
      (g₀ : Z₀ ⟶ Spec (.of k')) [LocallyOfFiniteType g₀] (pZ : (pullback f y).left ⟶ Z₀),
      IsModelFrobenius (fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy)) g₀ pZ →
        ∀ [IsProper (fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy)).left],
          TraceFormulaHolds ℓ (fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy)))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K ⟶ K)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).obj
      ((boundedConstructibleLowerShriek ℓ f).obj K))]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)]
    [Fintype {z : RationalPoint (pullback f y) //
      z ≫ fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy) = z}] :
    trace (Correspondence.graphStalkMap
        ((boundedConstructibleLowerShriek ℓ f).obj K) ΦY
        (lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ) y hy) =
      ∑ z : {z : RationalPoint (pullback f y) //
          z ≫ fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy) = z},
        trace (Correspondence.graphStalkMap K ΦX ψ (z.1 ≫ pullback.fst f y)
          (comp_fst_comp_eq_of_comp_fibreFrobenius_eq hf _ z.2)) := by
  obtain ⟨k', _, _, _, Z₀, g₀, pZ, -, _, hZm⟩ :=
    hX.exists_isModelFrobenius_fibreFrobenius hY hf hfp h₀ one_ne_zero y
      (comp_frobeniusIterate_one_of_comp_eq hy)
  have : IsFinite (fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy)).left := by
    have := hZm.isFinite 1
    rwa [frobeniusIterate_one] at this
  have hi : fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy) ≫
      pullback.fst f y = pullback.fst f y ≫ ΦX := by
    rw [fibreFrobenius_fst, frobeniusIterate_one]
  have hZ := isPullback_pullbackFst_toPoint f y
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ
  obtain ⟨_⟩ := nonempty_hasRightDual_point ℓ k
    ((boundedConstructibleLowerShriek ℓ
      (toPoint (pullback f y))).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (pullback.fst f y)).obj K))
  have : ∀ z : RationalPoint (pullback f y),
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (pullback.fst f y)).obj K)) :=
    fun z ↦ (nonempty_hasRightDual_point ℓ k _).some
  rw [Correspondence.graphStalkMap, lowerShriekFrobeniusCoefficient]
  rw [trace_eq_of_iso
    (X := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).obj
      ((boundedConstructibleLowerShriek ℓ f).obj K))
    (X' := (boundedConstructibleLowerShriek ℓ
      (toPoint (pullback f y))).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (pullback.fst f y)).obj K))
    (asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K))
    _ _ (stalk_weilLowerShriekFrobeniusComparison_comp ℓ (IsPullback.of_hasPullback ΦY f).flip
      (relativeFrobenius f ΦX ΦY hf) (relativeFrobenius_snd ..) (relativeFrobenius_fst ..) hi hy
      hZ ψ), frobeniusCompactOperator_one,
    hfib k' Z₀ g₀ pZ hZm]
  exact Finset.sum_congr rfl fun z _ ↦ trace_graphStalkMap_upperStar hi K ψ z.1 z.2

/-- **The trace formula along a morphism of models** (blueprint
`theorem-trace-formula-frobenius-correspondence`, induction on affine coordinates;
`lemma-comparison-via-relative-frobenius` (3) and (4);
`theorem-trace-formula-frobenius-correspondence--1`, Step 4, with
`lemma-comparison-via-relative-frobenius--4`): let `f : X ⟶ Y` be the base change of a morphism
`f₀ : X₀ ⟶ Y₀` of models over the finite field `k₀`, commuting with the model Frobenii. If the trace
formula in degree one holds on `Y` and on the fibres of `f` over the rational points of `Y` fixed by
`Φ_Y`, for every model of these fibres, it holds on `X`. -/
theorem traceFormulaHolds_of_fibres [IsAlgClosed k] {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ Y₀ : Scheme.{u}} {fX₀ : X₀ ⟶ Spec (.of k₀)}
    {fY₀ : Y₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType fX₀] [LocallyOfFiniteType fY₀]
    {pX : X.left ⟶ X₀} {pY : Y.left ⟶ Y₀} {ΦX : X ⟶ X} {ΦY : Y ⟶ Y}
    (hX : IsModelFrobenius ΦX fX₀ pX) (hY : IsModelFrobenius ΦY fY₀ pY) [IsProper ΦX.left]
    [IsProper ΦY.left] {f : X ⟶ Y} (hf : ΦX ≫ f = f ≫ ΦY) {f₀ : X₀ ⟶ Y₀}
    (hfp : f.left ≫ pY = pX ≫ f₀) (h₀ : f₀ ≫ fY₀ = fX₀)
    (hfib : ∀ (y : RationalPoint Y) (hy : y ≫ ΦY = y) (k' : Type u) [Field k'] [Finite k']
      [Algebra k' k] (Z₀ : Scheme.{u}) (g₀ : Z₀ ⟶ Spec (.of k')) [LocallyOfFiniteType g₀]
      (pZ : (pullback f y).left ⟶ Z₀),
      IsModelFrobenius (fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy)) g₀ pZ →
        ∀ [IsProper (fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy)).left],
          TraceFormulaHolds ℓ (fibreFrobenius f hf 1 y (comp_frobeniusIterate_one_of_comp_eq hy)))
    (hYtf : TraceFormulaHolds ℓ ΦY) : TraceFormulaHolds ℓ ΦX := by
  intro K ψ _ _ _
  classical
  have : IsFinite ΦX.left := by
    have := hX.isFinite 1
    rwa [frobeniusIterate_one] at this
  have : IsUniversalHomeomorphism ΦX.left := by
    have := hX.isUniversalHomeomorphism 1
    rwa [frobeniusIterate_one] at this
  have : IsFinite ΦY.left := by
    have := hY.isFinite 1
    rwa [frobeniusIterate_one] at this
  have : IsUniversalHomeomorphism ΦY.left := by
    have := hY.isUniversalHomeomorphism 1
    rwa [frobeniusIterate_one] at this
  have : QuasiCompact fY₀ := hY.quasiCompact
  have hfin := hY.finite_fixedPoint (m := 1) one_ne_zero
  simp only [FixedPoint, frobeniusIterate_one] at hfin
  let := Fintype.ofFinite {y : RationalPoint Y // y ≫ ΦY = y}
  obtain ⟨_⟩ := nonempty_hasRightDual_point ℓ k
    ((boundedConstructibleLowerShriek ℓ (toPoint Y)).obj
      ((boundedConstructibleLowerShriek ℓ f).obj K))
  have : ∀ y : RationalPoint Y,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).obj
        ((boundedConstructibleLowerShriek ℓ f).obj K)) :=
    fun y ↦ (nonempty_hasRightDual_point ℓ k _).some
  rw [← frobeniusCompactOperator_one, ← trace_eq_of_iso
    (X := (boundedConstructibleLowerShriek ℓ (toPoint Y)).obj
      ((boundedConstructibleLowerShriek ℓ f).obj K))
    (X' := (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)
    ((boundedConstructibleLowerShriekCompToPoint ℓ f).app K) _ _
    (frobeniusCompactOperator_lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ 1),
    frobeniusCompactOperator_one, hYtf, ← Fintype.sum_fiberwise (fixedPointComp hf)]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  let := Fintype.ofEquiv _ (fixedPointCompFibreEquiv hf y)
  rw [trace_graphStalkMap_lowerShriekFrobeniusCoefficient hX hY hf hfp h₀ y.1 y.2 (hfib y.1 y.2)]
  exact Fintype.sum_equiv (fixedPointCompFibreEquiv hf y).symm _ _ fun _ ↦ rfl

end AlgebraicGeometry.ProEtale.CondensedRing
