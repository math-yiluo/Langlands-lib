/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.EpiMono
public import WeilConjectures.AlgebraicGeometry.PolynomialAffineSpace
public import WeilConjectures.TraceFormula.GenericQuotient
public import WeilConjectures.TraceFormula.ShriekTraceFunctionFiniteEtale
public import WeilConjectures.TraceFormula.ShriekTraceFunctionInduction
public import WeilConjectures.TraceFormula.WeilBaseChange

/-!

# The sheaf–function compatibility of the Weil lower shriek along open immersions

This file proves the sheaf–function compatibility `ProEtale.CondensedRing.ShriekTraceFunctionAt`
of the Weil lower shriek along an open immersion `j : X ⟶ Y`
(`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isOpenImmersion`). The proof is the same as
for closed immersions: for a point `ȳ` of `Y` of degree `n + 1`,

- if `ȳ = x̄ ≫ j`, compactly supported base change along the cartesian square `(𝟙, 𝟙, j, j)`
  (`j` is a monomorphism) reduces the compatibility at `ȳ` to the dimension-zero case for `𝟙_X`
  at `x̄`;
- otherwise `ȳ` lies on the reduced closed complement `W` of `X`
  (`ProEtale.CondensedRing.reducedCompl`), and `Rj_! K` restricts to zero on `W` by base change
  along the empty square `W ×_Y X = ∅` (`AlgebraicGeometry.isPullback_emptyOverTo`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Complement

variable {S : Scheme.{u}}

/-- The square of the empty scheme over two morphisms with disjoint images is cartesian. -/
lemma isPullback_emptyOverTo {X Y V : Over S} (f : X ⟶ Y) (j : V ⟶ Y)
    (h : Disjoint (Set.range f.left.base) (Set.range j.left.base)) :
    IsPullback (Scheme.emptyOverTo X) (Scheme.emptyOverTo V) f j := by
  have hE (s : PullbackCone f j) : IsEmpty s.pt.left :=
    Scheme.isEmpty_of_commSq ⟨by rw [← Over.comp_left, s.condition, Over.comp_left]⟩ h
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (Scheme.emptyOverTo_ext _ _)
    (fun s ↦ Over.homMk ((@isInitialOfIsEmpty _ (hE s)).to _)
      ((@isInitialOfIsEmpty _ (hE s)).hom_ext _ _))
    (fun s ↦ Over.OverMorphism.ext ((@isInitialOfIsEmpty _ (hE s)).hom_ext _ _))
    (fun s ↦ Over.OverMorphism.ext ((@isInitialOfIsEmpty _ (hE s)).hom_ext _ _))
    (fun s _ _ _ ↦ Over.OverMorphism.ext ((@isInitialOfIsEmpty _ (hE s)).hom_ext _ _)))

end Complement

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Open immersions**: the sheaf–function compatibility holds along an open immersion
`j : X ⟶ Y`. For a point `ȳ` of `Y` of degree `n + 1`: if `ȳ = x̄ ≫ j`, then
`t(Rj_! K; ȳ) = t(Lj^* Rj_! K; x̄)` by the stalks of pullbacks
(`ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUpperStar`), `= t(R𝟙_! L𝟙^* K; x̄)` by
compactly supported base change along the cartesian square `(𝟙, 𝟙, j, j)` (`j` is a
monomorphism), and
`= t(K; x̄)` by the dimension-zero case for `𝟙_X`; the sum on the right has the single term `x̄`.
Otherwise `ȳ` lies on the reduced closed complement `W`, and `Li^* Rj_! K = 0` by base change
along the empty square `W ×_Y X = ∅`. The hypothesis `_he` is not needed; it is kept for
uniformity with the other base cases. -/
theorem shriekTraceFunctionAt_of_isOpenImmersion {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    [IsOpenImmersion f.left] (_he : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf := by
  intro K n y
  by_cases hy : y.1.base default ∈ Set.range f.left.base
  · -- `ȳ = x̄ ≫ f`: base change along the cartesian square `(𝟙, 𝟙, f, f)`
    have : Mono f := Over.mono_of_mono_left f
    have hsub : Set.range y.1.base ⊆ Set.range f.left.base := by
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    obtain ⟨v, rfl⟩ := exists_frobeniusFixedPointsMap_eq eY hf y
      (IsOpenImmersion.lift f.left y.1 hsub) (IsOpenImmersion.lift_fac _ _ _)
    have hid : eX.hom ≫ 𝟙 X = 𝟙 X ≫ eX.hom := by simp
    have : IsFinite (𝟙 X : X ⟶ X).left := by
      rw [Over.id_left]
      infer_instance
    have : Etale (𝟙 X : X ⟶ X).left := by
      rw [Over.id_left]
      infer_instance
    rw [← weilStalkTraceAlternatingSum_weilUpperStar ℓ eY eX hf,
      weilStalkTraceAlternatingSum_weilUpperStar_weilLowerShriek ℓ ((mono_iff_isPullback f).1 ‹_›)
          hid
        hid hf hf,
      ShriekTraceFunctionAt.of_isFinite_of_etale ℓ eX eX hid _ n v]
    have hv : frobeniusFixedPointsMap eX eX hid n v = v :=
      Subtype.ext (by simp [frobeniusFixedPointsMap])
    refine (finsum_eq_single _ ⟨v, by simp⟩ fun x hx ↦
        (hx (by exact Subtype.ext (Subtype.ext (by simpa using x.2)))).elim).trans
      ((finsum_eq_single _ ⟨v, rfl⟩ fun x hx ↦
        (hx (by exact Subtype.ext (Subtype.ext ((cancel_mono f.left).1 x.2)))).elim).trans
        ?_).symm
    rw [weilStalkTraceAlternatingSum_weilUpperStar ℓ eX eX hid K n v, hv]
  · -- `ȳ` on the reduced closed complement `W`: base change along the empty square
    -- `∅ = W ×_Y X`
    have : IsEmpty {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1} :=
      ⟨fun x ↦ hy ⟨x.1.1.base default, congrArg (fun g ↦ g.base default) x.2⟩⟩
    rw [finsum_of_isEmpty]
    have hsub : (reducedComplι f).left.ker ≤ y.1.ker := by
      rw [Scheme.IdealSheafData.le_ker_iff_range_subset_support, Scheme.Hom.support_ker,
        (reducedComplι f).left.isClosedEmbedding.isClosed_range.closure_eq,
        range_reducedComplι]
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    have hW := reducedComplIso_hom_comp_reducedComplι hf
    obtain ⟨v, rfl⟩ := exists_frobeniusFixedPointsMap_eq eY hW y
      (IsClosedImmersion.lift (reducedComplι f).left y.1 hsub)
      (IsClosedImmersion.lift_fac _ _ _)
    have h₀ : (Iso.refl emptyOver).hom ≫ emptyOverTo X = emptyOverTo X ≫ eX.hom :=
      emptyOverTo_ext _ _
    have h₀' : (Iso.refl emptyOver).hom ≫ emptyOverTo (reducedCompl f) =
        emptyOverTo (reducedCompl f) ≫ (reducedComplIso hf).hom :=
      emptyOverTo_ext _ _
    rw [← weilStalkTraceAlternatingSum_weilUpperStar ℓ eY (reducedComplIso hf) hW,
      weilStalkTraceAlternatingSum_weilUpperStar_weilLowerShriek ℓ
        (isPullback_emptyOverTo f (reducedComplι f)
          ((range_reducedComplι f).symm ▸ disjoint_compl_right)) h₀ h₀' hf hW,
      shriekTraceFunctionAt_of_isEmpty ℓ (Iso.refl _) (reducedComplIso hf) h₀' _ n v]
    exact finsum_eq_zero_of_forall_eq_zero fun x ↦ isEmptyElim (x.1.1.base default)

end AlgebraicGeometry.ProEtale.CondensedRing
