/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.RealPurity

/-!
# Purity at an unramified boundary point

Let `j : U₀ ⟶ C₀` be a dense open immersion into a smooth geometrically connected curve over
`k₀ = 𝔽_q` and `ℱ` a lisse Weil sheaf on `U₀`, punctually `ι`-pure of weight `w`. If `ℱ` is
unramified at a closed point `x` of `C₀`, in the sense that `j_* ℱ` is lisse on an open
neighbourhood `V₀` of `x`, then the stalk `(j_* ℱ)_x̄` is `ι`-pure of weight `w`
(blueprint `corollary-unramified-boundary-point--2`, first clause): the restriction `(j_* ℱ)|_{V₀}`
is a lisse sheaf on the smooth geometrically connected curve `V₀` whose restriction to the dense
open `U₀ ∩ V₀` is `ℱ|_{U₀ ∩ V₀}`, pure of weight `w`, so it is pure of weight `w` on all of `V₀`
(`AlgebraicGeometry.WeilSheaf.IsLisse.isPunctuallyPureOfWeight_of_upperStar`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.isPureOfWeight_stalk_directImage`: the
  stalks of `j_* ℱ` at the points of `U₀`.
- `WeilSheaf.IsPunctuallyPureOfWeight.isPureOfWeight_stalk_directImage_of_isLisse`:
  purity at a boundary point near which `j_* ℱ` is lisse.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
  {ι : PadicAlgCl l →+* ℂ} {w : ℝ}

/-- At a point `j y` of the open `U₀`, the stalk of `j_* ℱ` is the stalk of `ℱ` at `y`, so it is
pure of weight `w` if `ℱ` is punctually pure of weight `w`. -/
theorem IsPunctuallyPureOfWeight.isPureOfWeight_stalk_directImage
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l U} (hw : F.IsPunctuallyPureOfWeight ι w) (y : U.finitePoints)
    (x : C.finitePoints) (hxy : j.base y.1 = x.1) :
    (((directImage j).obj F).stalk x).IsPureOfWeight ι
      ((C ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w := by
  obtain ⟨E⟩ := nonempty_equiv_stalk_directImage j F y x hxy
  have h := (hw y).of_equiv E
  rwa [Scheme.Hom.residueCard, degreeOver_eq_of_isOpenImmersion j, hxy,
    ← Scheme.Hom.residueCard] at h

/-- Blueprint `corollary-unramified-boundary-point--2` (first clause): Purity at an unramified
boundary point.

Let `j : U₀ ⟶ C₀` be a dense open immersion into a smooth geometrically connected curve and `ℱ`
a lisse Weil sheaf on `U₀`, punctually `ι`-pure of weight `w`. Let `x` be a closed point of `C₀`
at which `ℱ` is unramified: `j_* ℱ` is lisse on an open neighbourhood `i : X'₀ ⟶ C₀` of `x`.
Then the stalk `(j_* ℱ)_x̄` is `ι`-pure of weight `w`.

The lisse sheaf `i^* j_* ℱ` on the smooth geometrically connected curve `X'₀` restricts on the
dense open `U'₀ = U₀ ×_{C₀} X'₀` to the restriction of `ℱ`, which is pure of weight `w`; hence it
is pure of weight `w` on `X'₀`
(`AlgebraicGeometry.WeilSheaf.IsLisse.isPunctuallyPureOfWeight_of_upperStar`, by boundary
semicontinuity for it and for its dual). -/
theorem IsPunctuallyPureOfWeight.isPureOfWeight_stalk_directImage_of_isLisse
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [IsDominant j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l U}
    (hw : F.IsPunctuallyPureOfWeight ι w) (x : C.finitePoints) {X' : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of k₀))] (i : X' ⟶ C) [IsOpenImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] (hx : x.1 ∈ Set.range i.base)
    (hL : ((WeilSheaf.upperStar i).obj ((directImage j).obj F)).IsLisse) :
    (((directImage j).obj F).stalk x).IsPureOfWeight ι
      ((C ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w := by
  have : Smooth (C ↘ Spec (CommRingCat.of k₀)) :=
    SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have hjp : j ≫ C ↘ Spec (CommRingCat.of k₀) = U ↘ Spec (CommRingCat.of k₀) := comp_over j _
  have hip : i ≫ C ↘ Spec (CommRingCat.of k₀) = X' ↘ Spec (CommRingCat.of k₀) := comp_over i _
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := hjp ▸ inferInstance
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) := hip ▸ inferInstance
  have : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
  obtain ⟨y₀, hy₀⟩ := hx
  have : Nonempty X' := ⟨y₀⟩
  -- `X'` is a smooth geometrically connected curve
  have : SmoothOfRelativeDimension 1 (X' ↘ Spec (CommRingCat.of k₀)) :=
    hip ▸ (zero_add 1) ▸ (inferInstance :
      SmoothOfRelativeDimension (0 + 1) (i ≫ C ↘ Spec (CommRingCat.of k₀)))
  have : GeometricallyConnected (X' ↘ Spec (CommRingCat.of k₀)) := by
    have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected
      (C ↘ Spec (CommRingCat.of k₀))
    have := GeometricallyIrreducible.comp_of_isOpenImmersion i (C ↘ Spec (CommRingCat.of k₀))
    exact hip ▸ inferInstance
  -- the restriction `U' = U ×_C X' ⟶ X'` of `j`
  let U' := Limits.pullback j i
  let : U'.Over (Spec (CommRingCat.of k₀)) :=
    ⟨Limits.pullback.fst j i ≫ U ↘ Spec (CommRingCat.of k₀)⟩
  have : (Limits.pullback.fst j i).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : (Limits.pullback.snd j i).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change Limits.pullback.snd j i ≫ X' ↘ Spec (CommRingCat.of k₀) =
      Limits.pullback.fst j i ≫ U ↘ Spec (CommRingCat.of k₀)
    rw [← hip, ← hjp, ← Category.assoc, ← Limits.pullback.condition, Category.assoc]⟩
  have : IsDominant (Limits.pullback.snd j i) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Pullback.range_snd]
    exact j.denseRange.preimage i.isOpenEmbedding.isOpenMap
  -- the restriction of `i^* j_* ℱ` to `U'` is pure of weight `w`
  have hres : ((WeilSheaf.upperStar (Limits.pullback.snd j i)).obj ((WeilSheaf.upperStar i).obj
      ((directImage j).obj F))).IsPunctuallyPureOfWeight ι w := by
    intro z
    have hz : j.base ((Limits.pullback.fst j i).base z.1) =
        i.base ((Limits.pullback.snd j i).base z.1) := by
      rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
    have hz₁ := Scheme.Hom.map_mem_finitePoints (Limits.pullback.snd j i) z.2
    have hz₂ := Scheme.Hom.map_mem_finitePoints i hz₁
    have h₁ := hw.isPureOfWeight_stalk_directImage j
      ⟨(Limits.pullback.fst j i).base z.1, Scheme.Hom.map_mem_finitePoints _ z.2⟩ ⟨_, hz₂⟩ hz
    have h₂ := (isPureOfWeight_stalk_upperStar_iff i ((directImage j).obj F) ⟨_, hz₁⟩).2 h₁
    exact (isPureOfWeight_stalk_upperStar_iff (Limits.pullback.snd j i) _ z).2 h₂
  have hpure := hL.isPunctuallyPureOfWeight_of_upperStar (Limits.pullback.snd j i) hres
  have hy : y₀ ∈ X'.finitePoints := by
    rw [← Scheme.Hom.mem_finitePoints_iff_of_isIso i y₀, hy₀]
    exact x.2
  have key := (isPureOfWeight_stalk_upperStar_iff i _ ⟨_, hy⟩).1 (hpure ⟨_, hy⟩)
  have hx' : ∀ x' : C.finitePoints, x'.1 = x.1 →
      (((directImage j).obj F).stalk x').IsPureOfWeight ι
        ((C ↘ Spec (CommRingCat.of k₀)).residueCard x'.1) w →
      (((directImage j).obj F).stalk x).IsPureOfWeight ι
        ((C ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w := by
    rintro x' h hp
    obtain rfl := Subtype.ext h
    exact hp
  exact hx' ⟨i.base y₀, Scheme.Hom.map_mem_finitePoints i hy⟩ hy₀ key

end AlgebraicGeometry.WeilSheaf
