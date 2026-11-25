/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CoefficientMorphismAdditivity
public import WeilConjectures.TraceFormula.CoefficientMorphismCurve
public import WeilConjectures.TraceFormula.CoefficientMorphismPushforward
public import WeilConjectures.TraceFormula.ModelExtension
public import WeilConjectures.TraceFormula.ModelLineTower
public import WeilConjectures.TraceFormula.ModelOpenClosed

/-!

# The trace formula for Frobenius coefficient morphisms

Let `Φ` be the model Frobenius of `X = X₀ ×_{k₀} k`, `K` a bounded constructible complex on `X`
and `ψ : LΦ^* K ⟶ K` an arbitrary, not necessarily invertible, morphism (a *Frobenius
coefficient morphism*, blueprint `definition-frobenius-correspondences-their-operators`), with
iterates `ψ_m : LΦ_m^* K ⟶ K` and global operators `F_{c,m}(ψ) = RΓ_c(X, ψ_m) ∘ Φ_m^♯`
(`ProEtale.CondensedRing.frobeniusCompactOperator`). The trace formula
```
tr(F_{c,m}(ψ) | RΓ_c(X, K)) = ∑_{x ∈ X₀(𝔽_{q^m})} tr(ψ_{m,x} | K_x)
```
(`ProEtale.CondensedRing.trace_frobeniusCompactOperator_eq_sum`, blueprint
`theorem-trace-formula-frobenius-correspondence`,
`theorem-trace-formula-frobenius-correspondence--1`) is the coefficient-morphism variant of the
Grothendieck–Lefschetz formula.

The proof follows the blueprint route: the geometric content lies in the Frobenius local term on
curves (blueprint `proposition-frobenius-local-term-curve`), and everything else is a formal
reduction. In particular neither nearby cycles nor Varshavsky's contracting theorem is used.

* The trace formula in degree `m` for `Φ` is the trace formula in degree one
  (`ProEtale.CondensedRing.TraceFormulaHolds`) for the iterate `Φ_m`, the model Frobenius of the
  base change of `X₀` to the extension of degree `m` of `k₀`; this is why every step is proved
  for all finite fields at once.
* On a proper smooth curve, the Lefschetz–Verdier formula (blueprint
`theorem-proper-pushforward-lefschetz-verdier`) and the
  Frobenius local term on a curve (blueprint `proposition-frobenius-local-term-curve`) give the
  trace formula (`ProEtale.CondensedRing.traceFormulaHolds_of_smoothOfRelativeDimension_one`); on a
  point it holds since the open piece at the point is zero
  (`ProEtale.CondensedRing.traceFormulaHolds_of_isClosedImmersion`).
* The trace formula passes along a morphism of models whose fibres over the fixed points satisfy
  it (`ProEtale.CondensedRing.traceFormulaHolds_of_fibres`, blueprint
  `lemma-comparison-via-relative-frobenius` (3) and (4)). Applied to the projections `ℙ¹_B ⟶ B`,
  whose fibres are projective lines, it gives the trace formula on the towers of projective lines
  `ℙ¹ ×_{k₀} ⋯ ×_{k₀} ℙ¹`
  (`ProEtale.CondensedRing.traceFormulaHolds_of_isModelFrobenius_projectiveLineTower`). Applied to
  an immersion of an affine model `X₀ ⟶ 𝔸ᵈ_{k₀} ⊆ ℙ¹ ×_{k₀} ⋯ ×_{k₀} ℙ¹`, whose fibres are empty or
  a point, it gives the affine case (`ProEtale.CondensedRing.traceFormulaHolds_of_isAffine`). The
  only compactification used is `𝔸¹ ⊆ ℙ¹`, in each coordinate.
* A finite affine open cover of `X₀` and the additivity of the trace along open–closed
  decompositions (`ProEtale.CondensedRing.TraceFormulaHolds.of_isCompl`, blueprint
  `lemma-additivity-open-subscheme-complement`) give the general case.

The blueprint reduces closed subschemes of `𝔸ᵈ` to closed subschemes of `𝔸¹` by forgetting the
last coordinate, and the affine line to `ℙ¹`; here the affine model is immersed into
`ℙ¹ ×_{k₀} ⋯ ×_{k₀} ℙ¹` first, so that the fibres of the coordinate projections are projective
lines and those of the immersion are points. The inputs are the same.

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

omit [Fact (ringChar k).Prime] in
/-- The model Frobenius is finite. -/
lemma IsModelFrobenius.isFinite_left {X : Over (Spec (.of k))} {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀]
    {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p) : IsFinite Φ.left := by
  have := hΦ.isFinite 1
  rwa [frobeniusIterate_one] at this

omit [Fact (ringChar k).Prime] in
/-- The model Frobenius is a universal homeomorphism. -/
lemma IsModelFrobenius.isUniversalHomeomorphism_left {X : Over (Spec (.of k))} {k₀ : Type u}
    [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p) :
    IsUniversalHomeomorphism Φ.left := by
  have := hΦ.isUniversalHomeomorphism 1
  rwa [frobeniusIterate_one] at this

/-! ### Towers of projective lines -/

section Tower

variable [IsAlgClosed k] {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]

omit [Fact (ringChar k).Prime] [IsAlgClosed k] [Finite k₀] in
/-- A model Frobenius whose model is `Spec k₀` lives on a scheme `X` with `X ⟶ Spec k` an
isomorphism, in particular a closed immersion. -/
lemma IsModelFrobenius.isClosedImmersion_hom_of_isIso {X : Over (Spec (.of k))}
    {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} [IsIso f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X}
    (hΦ : IsModelFrobenius Φ f₀ p) : IsClosedImmersion X.hom := by
  have : IsIso X.hom :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u}) hΦ.isPullback
      (show IsIso f₀ from inferInstance)
  infer_instance

set_option linter.overlappingInstances false in
/-- **The trace formula on a tower of projective lines** (blueprint
`theorem-trace-formula-frobenius-correspondence`, the affine line through `ℙ¹` and the induction on
coordinates): for every model Frobenius `Φ_Y` of `Y = P_d ×_{k₀} k`, where
`P_d = ℙ¹_{k₀} ×_{k₀} ⋯ ×_{k₀} ℙ¹_{k₀}` is the tower of projective lines, the trace formula in
degree one holds. By induction on `d`: `P_0 = Spec k₀` is a point, and the projection
`P_{d+1} = ℙ¹_{P_d} ⟶ P_d` has proper smooth curves as fibres, where the trace formula holds by
the Frobenius local term on curves (`traceFormulaHolds_of_smoothOfRelativeDimension_one`); the
trace formula passes along the projection (`traceFormulaHolds_of_fibres`). -/
theorem traceFormulaHolds_of_isModelFrobenius_projectiveLineTower (d : ℕ) :
    ∀ {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [IsSeparated Y.hom] {pY : Y.left ⟶ (projectiveLineTower (Spec (.of k₀)) d).left}
      {ΦY : Y ⟶ Y}, IsModelFrobenius ΦY (projectiveLineTower (Spec (.of k₀)) d).hom pY →
        ∀ [IsProper ΦY.left], TraceFormulaHolds ℓ ΦY := by
  induction d with
  | zero =>
    intro Y _ _ _ pY ΦY hY _
    have : IsIso (projectiveLineTower (Spec (.of k₀)) 0).hom :=
      inferInstanceAs (IsIso (𝟙 (Spec (.of k₀))))
    have := hY.isClosedImmersion_hom_of_isIso
    exact traceFormulaHolds_of_isClosedImmersion hY
  | succ d ih =>
    intro Y _ _ _ pY ΦY hY _
    obtain ⟨Y', _, _, _, pY', ΦY', f, hY', hf, hfp, hpb⟩ :=
      hY.exists_comp_eq_comp (projectiveLineTower (Spec (.of k₀)) d)
        (overProjectiveLineProj (projectiveLineTower (Spec (.of k₀)) d)).left rfl
    have := hY'.isFinite_left
    have : IsProper f.left := MorphismProperty.of_isPullback hpb.flip
      (inferInstanceAs (IsProper (overProjectiveLineProj
        (projectiveLineTower (Spec (.of k₀)) d)).left))
    have : SmoothOfRelativeDimension 1 f.left :=
      have := smoothOfRelativeDimension_isStableUnderBaseChange 1
      MorphismProperty.of_isPullback hpb.flip
        (inferInstanceAs (SmoothOfRelativeDimension 1 (overProjectiveLineProj
          (projectiveLineTower (Spec (.of k₀)) d)).left))
    refine traceFormulaHolds_of_fibres hY hY' hf hfp rfl ?_ (ih hY')
    intro y hy k' _ _ _ Z₀ g₀ _ pZ hZ _
    have := isProper_pullback_hom f y
    have := smoothOfRelativeDimension_pullback_hom f y
    exact traceFormulaHolds_of_smoothOfRelativeDimension_one hZ

set_option linter.overlappingInstances false in
/-- **The trace formula on an affine model** (blueprint
`theorem-trace-formula-frobenius-correspondence`, the affine case; detailed form
`theorem-trace-formula-frobenius-correspondence--1`, Step 4): for the model Frobenius `Φ` of an
affine model `X₀` of finite type over `k₀`, the trace formula in degree one holds. The model `X₀`
admits an immersion into a tower of projective lines
(`Scheme.exists_isImmersion_projectiveLineTower`), on whose base change the trace formula holds
(`traceFormulaHolds_of_isModelFrobenius_projectiveLineTower`); the fibres of the immersion are empty
or a point, where the trace formula holds (`traceFormulaHolds_of_isClosedImmersion`), and the trace
formula passes along the immersion (`traceFormulaHolds_of_fibres`). -/
theorem traceFormulaHolds_of_isAffine {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] {X₀ : Scheme.{u}} [IsAffine X₀]
    {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X}
    (hΦ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left] : TraceFormulaHolds ℓ Φ := by
  obtain ⟨d, ι, hι, hcomp⟩ := exists_isImmersion_projectiveLineTower f₀
  obtain ⟨Y, _, _, _, pY, ΦY, f, hY, hf, hfp, hpb⟩ :=
    hΦ.exists_comp_eq_comp (projectiveLineTower (Spec (.of k₀)) d) ι hcomp
  have := hY.isFinite_left
  have : IsImmersion f.left := MorphismProperty.of_isPullback hpb.flip hι
  refine traceFormulaHolds_of_fibres hΦ hY hf hfp hcomp ?_
    (traceFormulaHolds_of_isModelFrobenius_projectiveLineTower d hY)
  intro y hy k' _ _ _ Z₀ g₀ _ pZ hZ _
  have := isClosedImmersion_pullback_hom_of_isImmersion f y
  exact traceFormulaHolds_of_isClosedImmersion hZ

end Tower

/-! ### General models -/

omit [Fact (ringChar k).Prime] in
/-- A model covered by the empty family of opens is empty, hence affine. -/
lemma isAffine_of_card_eq_zero {X₀ : Scheme.{u}} {s : Finset X₀.Opens} (hs : s.card = 0)
    (hcov : ⨆ U ∈ s, U = ⊤) : IsAffine X₀ := by
  have h : (⊤ : X₀.Opens) = ⊥ := by
    rw [← hcov, Finset.card_eq_zero.1 hs]
    simp
  have : IsEmpty X₀ := ⟨fun x ↦ by
    have hx : x ∈ (⊤ : X₀.Opens) := trivial
    rw [h] at hx
    simp at hx⟩
  infer_instance

/-- The trace formula in degree one for a model Frobenius whose model is covered by `n` affine
opens, by induction on `n` (blueprint `theorem-trace-formula-frobenius-correspondence`, general
schemes; `theorem-trace-formula-frobenius-correspondence--1`, Step 5): the open–closed additivity of
the trace (blueprint `lemma-additivity-open-subscheme-complement`) reduces it to the affine case. -/
theorem traceFormulaHolds_of_card_eq [IsAlgClosed k] {k₀ : Type u} [Field k₀] [Finite k₀]
    [Algebra k₀ k] (n : ℕ) :
    ∀ {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated X.hom] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀]
      {p : X.left ⟶ X₀} {Φ : X ⟶ X} (_ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left]
      {s : Finset X₀.Opens}, s.card = n → (∀ U ∈ s, IsAffineOpen U) → ⨆ U ∈ s, U = ⊤ →
        TraceFormulaHolds ℓ Φ := by
  induction n with
  | zero =>
    intro X _ _ _ X₀ f₀ _ p Φ hΦ _ s hs _ hcov
    have := isAffine_of_card_eq_zero hs hcov
    exact traceFormulaHolds_of_isAffine hΦ
  | succ n ih =>
    intro X _ _ _ X₀ f₀ _ p Φ hΦ _ s hs hsa hcov
    obtain ⟨U, _, _, _, Z, _, _, _, j, i, _, _, ΦU, ΦZ, U₀, fU₀, pU, Z₀, fZ₀, pZ, t, hj, hi,
      hcompl, _, _, hΦU, _, hΦZ, ht, hta, htcov⟩ := hΦ.exists_isCompl hs hsa hcov
    have := hΦ.isFinite_left
    have := hΦ.isUniversalHomeomorphism_left
    have := hΦU.isFinite_left
    have := hΦU.isUniversalHomeomorphism_left
    have := hΦZ.isFinite_left
    have := hΦZ.isUniversalHomeomorphism_left
    exact TraceFormulaHolds.of_isCompl hcompl hj hi (traceFormulaHolds_of_isAffine hΦU)
      (ih hΦZ ht hta htcov)

/-- **The trace formula in degree one for a model Frobenius** (blueprint
`theorem-trace-formula-frobenius-correspondence`;
`theorem-trace-formula-frobenius-correspondence--1`, the statement `TF(X₀, K, ψ, 1)`). -/
theorem traceFormulaHolds_of_isModelFrobenius [IsAlgClosed k] {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] {k₀ : Type u}
    [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p)
    [IsProper Φ.left] : TraceFormulaHolds ℓ Φ := by
  obtain ⟨s, hsa, hcov⟩ := hΦ.exists_finset_isAffineOpen
  exact traceFormulaHolds_of_card_eq s.card hΦ rfl hsa hcov

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

variable (ℓ) in
/-- **The trace formula for Frobenius coefficient morphisms** (blueprint
`theorem-trace-formula-frobenius-correspondence`,
`theorem-trace-formula-frobenius-correspondence--1`): for the model Frobenius `Φ` of a separated
model `X₀` of finite type over a finite field `k₀`, a bounded constructible `K` with an arbitrary
map `ψ : LΦ^* K ⟶ K` and `m ≥ 1`, the trace of `F_{c,m}(ψ)` on `RΓ_c(X, K)` is the sum over the
rational points `x` fixed by `Φ_m` of the traces of the stalk maps `ψ_{m,x}` on `K_x`. No
invertibility of `ψ` is assumed. -/
theorem trace_frobeniusCompactOperator_eq_sum [IsAlgClosed k] {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p)
    [IsProper Φ.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    {m : ℕ} (hm : 1 ≤ m) [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    trace (frobeniusCompactOperator ℓ ψ m) =
      ∑ x : FixedPoint Φ m, trace (Correspondence.graphStalkMap K (frobeniusIterate Φ m)
        (frobeniusCoefficientIterate ψ m) x.1 x.2) := by
  obtain ⟨k₁, _, _, _, _, _, hcard⟩ := exists_finiteField_natCard_eq_pow k₀ k (m := m) (by omega)
  exact (traceFormulaHolds_of_isModelFrobenius
    (hΦ.fieldChange (k₁ := k₁) hcard)).trace_frobeniusCompactOperator K ψ

end AlgebraicGeometry.ProEtale.CondensedRing
