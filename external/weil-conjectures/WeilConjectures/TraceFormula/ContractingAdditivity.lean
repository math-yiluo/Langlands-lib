/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingClosedPiece
public import WeilConjectures.TraceFormula.ContractingOpenPiece
public import WeilConjectures.TraceFormula.PieceAdditivity

/-!

# Additivity of trace classes along a point with reduced fibre

Let `c = (c₁, c₂)` be an endocorrespondence of `(X, K)` and `y` a `k`-point of the fixed locus
such that the fibre `c₁⁻¹(x)`, `x = c₁(y)`, is the reduced point `y`. Then the closed point `{x}`
is `c`-invariant and the trace class of `c` is the sum of the trace classes of the induced
coefficient maps on the pieces `K^Z = Rx_* Lx^* K` and `K^U = j_! Lj^* K` of `K`
(`ProEtale.CondensedRing.Correspondence.traceClass_eq_add_of_isPullback`, blueprint
`proposition-additivity-trace-classes--2`, item 1 for `Z = {x}`).

This is `Correspondence.traceClass_eq_add_of_distTriang` for the open–closed triangle
`K^U ⟶ K ⟶ K^Z ⟶`.

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
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable (c : Correspondence ℓ K)

variable {c} in
/-- There is no morphism of degree `-1` from the class `Rc_! ℚ̄_ℓ` of the support of `c` to
`Rx_* A ⊠ D_X (j_! B)`, for `j` an open immersion missing `x = c₁(y)`, when the fibre
`c₁⁻¹(x)` is a `k`-point `y` with `c₂(y) = x`: by proper base change
`Lx^* Rc₁_! Lc₂^* (j_! B) ≅ Ly^* Lc₂^* (j_! B) = Lx^* j_! B = 0`. -/
lemma eq_zero_of_lowerShriek_support_of_isPullback {y : RationalPoint c.C}
    (hy : y ≫ c.c₁ = y ≫ c.c₂) (sq : IsPullback y (𝟙 (point k)) c.c₁ (y ≫ c.c₁))
    {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] (j : U ⟶ X) [IsOpenImmersion j.left]
    (hjx : Disjoint (Set.range j.left.base) (Set.range (y ≫ c.c₁).left.base))
    (A : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ : (boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ (y ≫ c.c₁)).obj A)
        (verdierDual ℓ
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B))) ⟦(-1 : ℤ)⟧) :
    φ = 0 := by
  refine eq_zero_of_lowerShriek_unit (y ≫ c.c₁) A _ _ ?_ φ
  rw [support_fst, support_snd]
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  refine IsZero.of_iso ?_
    (asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app _))
  rw [hy] at hjx
  exact (boundedConstructibleLowerShriek ℓ (𝟙 (point k))).map_isZero
    ((isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j (y ≫ c.c₂) hjx
      B).of_iso ((boundedConstructibleUpperStarComp _ ℓ y c.c₂).app _).symm)

/-- **Additivity of trace classes along the pieces of a point with reduced fibre** (blueprint
`proposition-additivity-trace-classes--2`, item 1, and `proposition-additivity-trace-classes--2`,
for the `c`-invariant closed subscheme `Z = {x}` of the rational point `x = c₁(y)` of a `k`-point
`y` of the fixed locus such that `c₁⁻¹(x)` is the reduced point `y`; Varshavsky, Prop. 1.5.10 after
SGA 5, III 4.13): the trace class of `u` is the sum of the trace classes of the induced
coefficient maps `u^Z = [x, y]_! u_Z` on `K^Z = Rx_* Lx^* K`, the proper pushforward of the
restricted coefficient map along `(x, y)`, and `u^U = [j]_! (u|_U)` on `K^U = j_! Lj^* K`. -/
theorem traceClass_eq_add_of_isPullback (F : c.FixedLocus) {y : RationalPoint c.C}
    (hy : y ≫ c.c₁ = y ≫ c.c₂) (sq : IsPullback y (𝟙 (point k)) c.c₁ (y ≫ c.c₁)) :
    c.traceClass F =
      F.traceClassWithCoeff _ (restrictedClosedPieceDiagram hy sq).pushforwardCoeff +
        F.traceClassWithCoeff _ (c.pointOpenPieceCoeff (y ≫ c.c₁)
          (preimage_pointComplOpens_le_of_isPullback hy sq)) := by
  have hjx := (isCompl_range_pointComplι (y ≫ c.c₁)).disjoint
  obtain ⟨δ, hT⟩ := exists_distTriang_pointComplι_rationalPoint (y ≫ c.c₁) K
  rw [add_comm]
  refine c.traceClass_eq_add_of_distTriang F hT
    (c.pointOpenPieceCoeff (y ≫ c.c₁) (preimage_pointComplOpens_le_of_isPullback hy sq))
    (restrictedClosedPieceDiagram hy sq).pushforwardCoeff ?_ ?_
    (eq_zero_of_lowerShriek_support_of_isPullback hy sq (pointComplι _) hjx _ _)
    (eq_zero_of_externalProduct_openPiece (pointComplι _) _ hjx _ _ K _)
    (eq_zero_of_externalProduct_closedPiece (pointComplι _) _ hjx _ _ K _)
    (eq_zero_of_externalProduct_shift_to_diag (pointComplι _) _ hjx _ _)
  · exact (pointOpenPieceCoeff_comp_map_counit (c := c) (y ≫ c.c₁)
      (preimage_pointComplOpens_le_of_isPullback hy sq)).symm
  · exact upperStar_map_unit_comp_restrictedClosedPieceCoeff (c := c) hy sq

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
