/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineOver
public import WeilConjectures.TraceFormula.BaseChange.LowerShriek

/-!

# The geometric fibre of the relative projective line

Let `k = 𝔽_q` be a finite field, `Ω ⊇ k` a field (in the applications `k̄`), `B` a scheme over
`Spec k` and `ȳ : Spec Ω ⟶ B` a geometric point over `Spec k`. The fibre of the base change
`ℙ¹_B ×_k Ω ⟶ B ×_k Ω` of the relative projective line at the rational point `ȳ' = (ȳ, 𝟙)` is the
projective line `ℙ¹_Ω = ℙ¹_k ×_k Ω` (`ProEtale.CondensedRing.projectiveLineFibre`), embedded by
`(t, ω) ↦ ((t, ȳ(ω)), ω)` (`ProEtale.CondensedRing.projectiveLineFibreMap`). If moreover
`ȳ ≫ g = σ ≫ ȳ` for an endomorphism `g` of `B` and an automorphism `σ` of `Spec Ω` inverse to
`Spec(y ↦ y ^ (q ^ N))`, the embedding intertwines the model Frobenius `F^N ×_k Ω` of `ℙ¹_Ω` with
the model Frobenius `(ℙ¹(g) ≫ F^N) ×_k Ω` of `ℙ¹_B ×_k Ω`. For a point `y` of degree `n + 1` for
an automorphism `e_B` this gives the fibre at `y` of the model-Frobenius setting attached to
`ℙ¹_B` with the automorphism `ℙ¹(e_B)`.

## Main definitions

- `ProEtale.CondensedRing.projectiveLineFibre`: the projective line `ℙ¹_Ω = ℙ¹_k ×_k Ω`.
- `ProEtale.CondensedRing.projectiveLineFibreFrobenius`: its model Frobenius `F^{n+1} ×_k Ω`.
- `ProEtale.CondensedRing.projectiveLineFibreMap`,
  `ProEtale.CondensedRing.projectiveLineFibreι`: the embedding `ℙ¹_Ω ⟶ ℙ¹_B ×_k Ω` of the fibre
  at a geometric point.

## Main statements

- `AlgebraicGeometry.Scheme.overProjectiveLineIso_pow`: `ℙ¹(e)^{n+1} = ℙ¹(e^{n+1})`.
- `ProEtale.CondensedRing.projectiveLineFibreι_comp`: the embedding intertwines the model
  Frobenii.
- `ProEtale.CondensedRing.isPullback_projectiveLineFibreι`: `ℙ¹_Ω` is the fibre of
  `ℙ¹_B ×_k k̄ ⟶ B ×_k k̄` at `y`.
- `ProEtale.CondensedRing.finite_fixedPoint_projectiveLineFibreFrobenius`: the model Frobenius of
  `ℙ¹_{k̄}` has finitely many fixed rational points.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- `ℙ¹` commutes with the powers of an automorphism: `ℙ¹(e)^{n+1} = ℙ¹(e^{n+1})`. -/
lemma overProjectiveLineIso_pow {S : Scheme.{u}} {B : Over S} (e : B ≅ B) (n : ℕ) :
    (overProjectiveLineIso e).pow (n + 1) = overProjectiveLineIso (e.pow (n + 1)) := by
  induction n with
  | zero => simp only [zero_add, Iso.pow_one]
  | succ n ih =>
    rw [Iso.pow_succ _ (n + 1), Iso.pow_succ e (n + 1), ih, overProjectiveLineIso_trans]

end Scheme

namespace ProEtale.CondensedRing

open Scheme ProjectiveSpace

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]

/-- The projective line `ℙ¹_Ω = ℙ¹_k ×_k Ω` over `Spec Ω`, the base change of `ℙ¹_k`. -/
noncomputable abbrev projectiveLineFibre : Over (Spec (.of Ω)) :=
  (geometricBaseChange k Ω).obj (overProjectiveLine (point k))

/-- `ℙ¹_Ω` is the base change of `ℙ¹_k` along `Spec Ω ⟶ Spec k`. -/
lemma isPullback_projectiveLineFibre_hom :
    IsPullback (geometricBaseChangeProj (overProjectiveLine (point k)))
      (projectiveLineFibre k Ω).hom (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  simpa [overProjectiveLine] using
    isPullback_geometricBaseChangeProj (Ω := Ω) (overProjectiveLine (point k))

instance : IsProper (projectiveLineFibre k Ω).hom :=
  MorphismProperty.of_isPullback (isPullback_projectiveLineFibre_hom k Ω) inferInstance

instance : SmoothOfRelativeDimension 1 (projectiveLineFibre k Ω).hom :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
    (isPullback_projectiveLineFibre_hom k Ω) inferInstance

section Frobenius

variable [Finite k]

/-- The model Frobenius `F^{n+1} ×_k Ω` of `ℙ¹_Ω`, the base change of the `#k ^ (n + 1)`-power
Frobenius of `ℙ¹_k`. -/
noncomputable abbrev projectiveLineFibreFrobenius (n : ℕ) :
    projectiveLineFibre k Ω ⟶ projectiveLineFibre k Ω :=
  baseChangeModelFrobenius Ω (overProjectiveLine (point k)) (n + 1) (𝟙 _)

/-- For `Ω` algebraically closed, the model Frobenius `F^{n+1} ×_k Ω` of `ℙ¹_Ω` is the model
Frobenius of a model of `ℙ¹_Ω` over the subfield `𝔽_{q^{n+1}}` of `Ω`. -/
theorem exists_isModelFrobenius_projectiveLineFibre [IsAlgClosed Ω] (n : ℕ) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₁ Ω)
      (X₁ : Scheme.{u}) (f₁ : X₁ ⟶ Spec (.of k₁)) (_ : LocallyOfFiniteType f₁)
      (p₁ : (projectiveLineFibre k Ω).left ⟶ X₁),
      Nat.card k₁ = Nat.card k ^ (n + 1) ∧
        IsModelFrobenius (projectiveLineFibreFrobenius k Ω n) f₁ p₁ :=
  exists_isModelFrobenius_modelFrobenius_id _ (Nat.succ_ne_zero n)

/-- For `Ω` algebraically closed, the model Frobenius `F^{n+1} ×_k Ω` of `ℙ¹_Ω` has finitely
many fixed rational points. -/
theorem finite_fixedPoint_projectiveLineFibreFrobenius [IsAlgClosed Ω] (n : ℕ) :
    Finite (FixedPoint (projectiveLineFibreFrobenius k Ω n) 1) := by
  have h := (isModelFrobenius_modelFrobenius_one (Ω := Ω)
    (overProjectiveLine (point k))).finite_fixedPoint (Nat.succ_ne_zero n)
  refine @Finite.of_equiv _ _ h (Equiv.subtypeEquivRight fun x ↦ ?_)
  rw [frobeniusIterate_one, ← modelFrobenius_id]

end Frobenius

/-! ### The embedding of the fibre at a geometric point -/

variable {k Ω} {B : Over (Spec (.of k))}

/-- The morphism `ℙ¹_Ω ⟶ ℙ¹_B`, `(t, ω) ↦ (t, ȳ(ω))`, attached to a geometric point
`ȳ : Spec Ω ⟶ B` over `Spec k`. -/
noncomputable def projectiveLineFibreToProjectiveLine (x : Spec (.of Ω) ⟶ B.left)
    (hx : x ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    (projectiveLineFibre k Ω).left ⟶ (overProjectiveLine B).left :=
  liftBaseChange (g := B.hom) ((projectiveLineFibre k Ω).hom ≫ x)
    (geometricBaseChangeProj (overProjectiveLine (point k))) (by
      rw [Category.assoc, hx]
      exact (isPullback_projectiveLineFibre_hom k Ω).w.symm)

/-- `ℙ¹_Ω ⟶ ℙ¹_B` lies over `ȳ : Spec Ω ⟶ B`. -/
@[reassoc (attr := simp)]
lemma projectiveLineFibreToProjectiveLine_proj (x : Spec (.of Ω) ⟶ B.left)
    (hx : x ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    projectiveLineFibreToProjectiveLine x hx ≫ (overProjectiveLineProj B).left =
      (projectiveLineFibre k Ω).hom ≫ x :=
  liftBaseChange_over _ _ _

/-- The composite `ℙ¹_Ω ⟶ ℙ¹_B ⟶ ℙ¹_k` is the projection of the base change. -/
@[reassoc (attr := simp)]
lemma projectiveLineFibreToProjectiveLine_map (x : Spec (.of Ω) ⟶ B.left)
    (hx : x ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    projectiveLineFibreToProjectiveLine x hx ≫ (overProjectiveLineMap (toPoint B)).left =
      geometricBaseChangeProj (overProjectiveLine (point k)) := by
  rw [overProjectiveLineMap_left, toPoint_left]
  exact liftBaseChange_map _ _ _

/-- The embedding `ℙ¹_Ω ⟶ ℙ¹_B ×_k Ω`, `(t, ω) ↦ ((t, ȳ(ω)), ω)`, of the fibre of
`ℙ¹_B ×_k Ω ⟶ B ×_k Ω` at the rational point attached to a geometric point `ȳ : Spec Ω ⟶ B`
over `Spec k`. -/
noncomputable def projectiveLineFibreMap (x : Spec (.of Ω) ⟶ B.left)
    (hx : x ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    projectiveLineFibre k Ω ⟶ (geometricBaseChange k Ω).obj (overProjectiveLine B) :=
  Over.homMk (pullback.lift (projectiveLineFibreToProjectiveLine x hx)
    (projectiveLineFibre k Ω).hom (by
      rw [← Over.w (overProjectiveLineProj B), ← Category.assoc,
        projectiveLineFibreToProjectiveLine_proj, Category.assoc, hx]))
    (pullback.lift_snd _ _ _)

/-- The composite of `ℙ¹_Ω ⟶ ℙ¹_B ×_k Ω` with the projection to `ℙ¹_B` is
`(t, ω) ↦ (t, ȳ(ω))`. -/
@[reassoc (attr := simp)]
lemma projectiveLineFibreMap_left_comp_proj (x : Spec (.of Ω) ⟶ B.left)
    (hx : x ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    (projectiveLineFibreMap x hx).left ≫ geometricBaseChangeProj (overProjectiveLine B) =
      projectiveLineFibreToProjectiveLine x hx := by
  simp [projectiveLineFibreMap, geometricBaseChangeProj]

/-- Let `σ` be an automorphism of `Spec Ω` inverse to `Spec(y ↦ y ^ (#k ^ N))` and `g` an
endomorphism of `B` with `ȳ ≫ g = σ ≫ ȳ`. The embedding `ℙ¹_Ω ⟶ ℙ¹_B ×_k Ω` of the fibre at `ȳ`
intertwines the model Frobenius `F^N ×_k Ω` of `ℙ¹_Ω` with the model Frobenius
`(ℙ¹(g) ≫ F^N) ×_k Ω` of `ℙ¹_B ×_k Ω`. -/
theorem projectiveLineFibreMap_comp [Finite k] {N : ℕ} {σ : Spec (.of Ω) ≅ Spec (.of Ω)}
    (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N)) (g : B ⟶ B) (x : Spec (.of Ω) ⟶ B.left)
    (hx : x ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hxg : x ≫ g.left = σ.hom ≫ x) :
    baseChangeModelFrobenius Ω (overProjectiveLine (point k)) N (𝟙 _) ≫
        projectiveLineFibreMap x hx =
      projectiveLineFibreMap x hx ≫
        baseChangeModelFrobenius Ω (overProjectiveLine B) N (overProjectiveLineMap g) := by
  ext1
  refine (isPullback_geometricBaseChangeProj (overProjectiveLine B)).hom_ext ?_ ?_
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
      projectiveLineFibreMap_left_comp_proj, modelFrobenius_left_comp_proj,
      projectiveLineFibreMap_left_comp_proj_assoc]
    refine (isPullback_overProjectiveLineMap (toPoint B)).hom_ext ?_ ?_
    · rw [Category.assoc, projectiveLineFibreToProjectiveLine_map, modelFrobenius_left_comp_proj,
        Category.assoc, ← Over.comp_left, Category.assoc,
        frobeniusIterate_comp_of_comp (comp_overFrobenius _).symm,
        ← overProjectiveLineMap_comp_assoc, comp_toPoint]
      simp
    · rw [Category.assoc, Category.assoc, projectiveLineFibreToProjectiveLine_proj,
        ← Over.comp_left, Category.assoc,
        frobeniusIterate_comp_of_comp (comp_overFrobenius _).symm,
        overProjectiveLineMap_proj_assoc, Over.comp_left, Over.comp_left,
        projectiveLineFibreToProjectiveLine_proj_assoc, ← Category.assoc x, hxg,
        comp_comp_frobeniusIterate_overFrobenius_left hσ, ← Category.assoc, Over.w]
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, Over.w, Over.w, Over.w,
      Over.w]

/-- The square

```
   ℙ¹_Ω ----------> ℙ¹_B ×_k Ω
    |                   |
    ↓                   ↓
  Spec Ω --- ȳ' ---> B ×_k Ω
```

of schemes is cartesian: `ℙ¹_Ω` is the fibre of `ℙ¹_B ×_k Ω ⟶ B ×_k Ω` at the rational point
`ȳ' = (ȳ, 𝟙)`. -/
lemma isPullback_projectiveLineFibreMap_left (x : Spec (.of Ω) ⟶ B.left)
    (hx : x ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    IsPullback (projectiveLineFibreMap x hx).left (projectiveLineFibre k Ω).hom
      ((geometricBaseChange k Ω).map (overProjectiveLineProj B)).left
      (geometricBaseChangePoint x hx).left := by
  have hfib : IsPullback (projectiveLineFibreToProjectiveLine x hx) (projectiveLineFibre k Ω).hom
      (overProjectiveLineProj B).left x := by
    refine IsPullback.of_right (h₁₂ := (overProjectiveLineMap (toPoint B)).left)
      (h₂₂ := B.hom) ?_ (projectiveLineFibreToProjectiveLine_proj x hx)
      (by simpa only [toPoint_left] using isPullback_overProjectiveLineMap (toPoint B))
    rw [projectiveLineFibreToProjectiveLine_map, hx]
    exact isPullback_projectiveLineFibre_hom k Ω
  have hw : (projectiveLineFibreMap x hx).left ≫
      ((geometricBaseChange k Ω).map (overProjectiveLineProj B)).left =
        (projectiveLineFibre k Ω).hom ≫ (geometricBaseChangePoint x hx).left := by
    refine (isPullback_geometricBaseChangeProj B).hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, geometricBaseChange_map_left_comp_proj,
        projectiveLineFibreMap_left_comp_proj_assoc, projectiveLineFibreToProjectiveLine_proj,
        geometricBaseChangePoint_left_comp_proj]
    · rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w]
      exact (Category.comp_id _).symm
  refine IsPullback.of_right ?_ hw
    (isPullback_geometricBaseChange_map_left (overProjectiveLineProj B)).flip
  rw [projectiveLineFibreMap_left_comp_proj, geometricBaseChangePoint_left_comp_proj]
  exact hfib

/-- The square

```
   ℙ¹_Ω ----------> ℙ¹_B ×_k Ω
    |                   |
    ↓                   ↓
  Spec Ω --- ȳ' ---> B ×_k Ω
```

over `Spec Ω` is cartesian: `ℙ¹_Ω` is the fibre of `ℙ¹_B ×_k Ω ⟶ B ×_k Ω` at the rational point
`ȳ' = (ȳ, 𝟙)`. -/
theorem isPullback_projectiveLineFibreMap (x : Spec (.of Ω) ⟶ B.left)
    (hx : x ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    IsPullback (projectiveLineFibreMap x hx) (toPoint (projectiveLineFibre k Ω))
      ((geometricBaseChange k Ω).map (overProjectiveLineProj B))
      (geometricBaseChangePoint x hx) :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (by
      simpa only [Over.comp_left, toPoint_left] using
        (isPullback_projectiveLineFibreMap_left x hx).w))
    (by
      simpa only [Over.forget_map, toPoint_left] using
        isPullback_projectiveLineFibreMap_left x hx)

variable [Finite k]

/-! ### Points of degree `n + 1` -/

/-- The embedding `ℙ¹_{k̄} ⟶ ℙ¹_B ×_k k̄`, `(t, ω) ↦ ((t, ȳ(ω)), ω)`, of the fibre of
`ℙ¹_B ×_k k̄ ⟶ B ×_k k̄` at a point `y` of degree `n + 1` for an automorphism `e_B` of `B`. -/
noncomputable def projectiveLineFibreι (eB : B ≅ B) {n : ℕ} (y : frobeniusFixedPoints eB (n + 1)) :
    projectiveLineFibre k (AlgebraicClosure k) ⟶
      (geometricBaseChange k (AlgebraicClosure k)).obj (overProjectiveLine B) :=
  projectiveLineFibreMap y.1 y.2.1

/-- The embedding `ℙ¹_{k̄} ⟶ ℙ¹_B ×_k k̄` of the fibre at a point `y` of degree `n + 1` intertwines
the model Frobenius `F^{n+1} ×_k k̄` of `ℙ¹_{k̄}` with the model Frobenius
`(ℙ¹(e_B)^{n+1} ≫ F^{n+1}) ×_k k̄` of `ℙ¹_B ×_k k̄`. -/
theorem projectiveLineFibreι_comp (eB : B ≅ B) {n : ℕ} (y : frobeniusFixedPoints eB (n + 1)) :
    projectiveLineFibreFrobenius k (AlgebraicClosure k) n ≫ projectiveLineFibreι eB y =
      projectiveLineFibreι eB y ≫ baseChangeModelFrobenius (AlgebraicClosure k)
        (overProjectiveLine B) (n + 1) ((overProjectiveLineIso eB).pow (n + 1)).hom := by
  rw [overProjectiveLineIso_pow, overProjectiveLineIso_hom]
  exact projectiveLineFibreMap_comp (geometricFrobeniusField_pow_inv n) _ _ _ y.2.2

/-- `ℙ¹_{k̄}` is the fibre of `ℙ¹_B ×_k k̄ ⟶ B ×_k k̄` at the rational point attached to a point
`y` of degree `n + 1`. -/
theorem isPullback_projectiveLineFibreι (eB : B ≅ B) {n : ℕ} (y : frobeniusFixedPoints eB (n + 1)) :
    IsPullback (projectiveLineFibreι eB y) (toPoint (projectiveLineFibre k (AlgebraicClosure k)))
      ((geometricBaseChange k (AlgebraicClosure k)).map (overProjectiveLineProj B))
      (geometricBaseChangePoint y.1 y.2.1) :=
  isPullback_projectiveLineFibreMap y.1 y.2.1

end ProEtale.CondensedRing

end AlgebraicGeometry
