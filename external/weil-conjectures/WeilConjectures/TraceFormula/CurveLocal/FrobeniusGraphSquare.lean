/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.SwapProduct
public import WeilConjectures.TraceFormula.TraceClass

/-!

# The fixed square of the Frobenius graph on the strictly local model

Let `c = (𝟙, Φ_m)` be the graph correspondence of the iterate `Φ_m` of the model Frobenius on the
curve `X`, with fixed locus `F`. Through the identification `X ×_k X ≅ X ⨯ X` interchanging the
factors (`ProEtale.CondensedRing.swapPullbackToProd`), the support map `c = (𝟙, Φ_m)` is the
transposed graph `(Φ_m, 𝟙)` of the classical model and the diagonal of `X ⨯ X` is the diagonal of
`X ×_k X`. This file deduces that the fixed square `ι ≫ c = d ≫ Δ` is, on underlying schemes, the
fixed square `ι ≫ graph = d ≫ diagonal` of the strictly local model at a fixed point
(`ProEtale.CondensedRing.Correspondence.isPullback_frobeniusLocalModel_graph`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Swap

variable {k : Type u} [Field k] (X : Over (Spec (.of k)))

/-- The transposed graph `(h, 𝟙) : X ⟶ X ×_k X` of an endomorphism `h`, followed by the
identification `X ×_k X ≅ X ⨯ X` interchanging the factors, is the support map `(𝟙, h)`. -/
lemma pullbackLift_swapPullbackToProd (h : X ⟶ X) (w : h.left ≫ X.hom = 𝟙 X.left ≫ X.hom) :
    pullback.lift h.left (𝟙 X.left) w ≫ swapPullbackToProd X = (prod.lift (𝟙 X) h).left := by
  refine (isPullback_prod_left X X).hom_ext ?_ ?_
  · rw [Category.assoc, swapPullbackToProd_fst, pullback.lift_snd, ← Over.comp_left,
      prod.lift_fst, Over.id_left]
  · rw [Category.assoc, swapPullbackToProd_snd, pullback.lift_fst, ← Over.comp_left,
      prod.lift_snd]

/-- The diagonal of `X ×_k X`, followed by the identification `X ×_k X ≅ X ⨯ X`, is the
diagonal of `X ⨯ X`. -/
lemma diagonal_swapPullbackToProd :
    pullback.diagonal X.hom ≫ swapPullbackToProd X = (diag X).left := by
  refine (isPullback_prod_left X X).hom_ext ?_ ?_
  · rw [Category.assoc, swapPullbackToProd_fst, pullback.diagonal_snd, ← Over.comp_left,
      diag, prod.lift_fst, Over.id_left]
  · rw [Category.assoc, swapPullbackToProd_snd, pullback.diagonal_fst, ← Over.comp_left,
      diag, prod.lift_snd, Over.id_left]

/-- A fixed square `ι ≫ (𝟙, h) = d ≫ Δ` of `X ⨯ X` is, through the identification
`X ×_k X ≅ X ⨯ X`, a cartesian square `ι ≫ (h, 𝟙) = d ≫ Δ` of `X ×_k X`. -/
lemma isPullback_pullbackLift_diagonal {F : Scheme.{u}} {ι d : F ⟶ X.left} (h : X ⟶ X)
    (w : h.left ≫ X.hom = 𝟙 X.left ≫ X.hom)
    (hpb : IsPullback ι d (prod.lift (𝟙 X) h).left (diag X).left) :
    IsPullback ι d (pullback.lift h.left (𝟙 X.left) w) (pullback.diagonal X.hom) :=
  hpb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (swapPullbackToProd X)).symm
    (by simp) (by simp)
    (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq,
      pullbackLift_swapPullbackToProd X h w])
    (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq,
      diagonal_swapPullbackToProd])

end Swap

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- The transposed graph of the strictly local model at a fixed point, followed by the
identification `X ×_k X ≅ X ⨯ X`, is the support map of the graph correspondence. -/
lemma frobeniusLocalModel_graph_swapPullbackToProd [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F) :
    (frobeniusLocalModel hΦ hm v F z).graph ≫ swapPullbackToProd X =
      (ofGraph K (frobeniusIterate Φ m) v).support.left :=
  pullbackLift_swapPullbackToProd X _ _

/-- The support map `(𝟙, h) : X ⟶ X ⨯ X` of a graph correspondence is a closed immersion: it is
a section of the separated first projection. -/
instance isClosedImmersion_ofGraph_support (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K) :
    IsClosedImmersion (ofGraph K h v).support.left := by
  have : IsClosedImmersion ((ofGraph K h v).support.left ≫ (prod.fst : X ⨯ X ⟶ X).left) := by
    rw [← Over.comp_left, support_fst]
    exact inferInstanceAs (IsClosedImmersion (𝟙 X.left))
  exact IsClosedImmersion.of_comp _ (prod.fst : X ⨯ X ⟶ X).left

/-- A point `z` of the fixed locus of a graph correspondence, followed by `d`, is the point
`z ≫ ι` of `X`. -/
lemma left_comp_ofGraph_d_left (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (F : (ofGraph K h v).FixedLocus) (z : RationalPoint F.F) :
    z.left ≫ F.d.left = (z ≫ F.ι).left := by
  simp [FixedLocus.d, ofGraph]

/-- The map `d` of the fixed locus of a graph correspondence is a closed immersion: it is the
inclusion `ι` of the fixed locus. -/
instance isClosedImmersion_ofGraph_d (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (F : (ofGraph K h v).FixedLocus) : IsClosedImmersion F.d.left := by
  simpa [FixedLocus.d, ofGraph] using F.isClosedImmersion_ι

/-- **The fixed square of the Frobenius graph is the fixed square of the strictly local model**:
on underlying schemes, the fixed locus `F` of `(𝟙, Φ_m)` is the fibre product of the transposed
graph `(Φ_m, 𝟙)` and the diagonal of `X ×_k X`. -/
theorem isPullback_frobeniusLocalModel_graph [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F) :
    IsPullback F.ι.left F.d.left (frobeniusLocalModel hΦ hm v F z).graph
      (pullback.diagonal (frobeniusLocalModel hΦ hm v F z).f) :=
  isPullback_pullbackLift_diagonal X (frobeniusIterate Φ m) _ (F.isPullback.map (Over.forget _))

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
