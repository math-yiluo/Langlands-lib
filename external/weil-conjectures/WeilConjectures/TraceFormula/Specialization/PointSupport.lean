/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-!

# Complexes supported at a rational point

Let `X` be a separated `k`-scheme of finite type and `x` a rational point of `X`. A bounded
constructible complex `C` on `X` whose restriction to the open complement `X ∖ {x}` vanishes is
the direct image of its stalk at `x`, `C ≅ Rx_* Lx^* C`; its global sections are therefore
`RΓ(X, C) ≅ Lx^* C`, and they detect vanishing
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_pointComplι_of_isZero_lowerStar`). This is
the case of a single rational point of the blueprint lemma `lemma-finite-support-global-sections--1`
(global sections detect complexes with finite support), used in the finite-support step of
Gabber's Künneth formula for nearby cycles.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

include ℓ in
/-- A complex `E` on the base point with `R(𝟙)_* E = 0` vanishes. -/
lemma isZero_of_isZero_boundedConstructibleLowerStar_id {E : Dᵇc((point
    k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (h : IsZero ((boundedConstructibleLowerStar ℓ (𝟙 (point k))).obj E)) : IsZero E := by
  set adj := boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 (point k))
  set u := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (X := point k)).app E
  have hu : u.hom = 0 := by
    rw [← (adj.homEquiv _ _).symm_apply_apply u.hom, ← (adj.homEquiv _ _).symm_apply_apply 0]
    congr 1
    exact h.eq_of_tgt _ _
  refine (IsZero.iff_id_eq_zero _).2 ?_
  have := u.inv_hom_id
  rw [hu, comp_zero] at this
  exact this.symm

include ℓ in
/-- **Global sections detect complexes supported at a rational point** (blueprint
`lemma-finite-support-global-sections--1`, for a single rational point): if the restriction of `C`
to the open complement `X ∖ {x}` of a rational point `x` vanishes, and `RΓ(X, C) = 0`, then
`C = 0`. -/
theorem isZero_of_isZero_upperStar_pointComplι_of_isZero_lowerStar (x : RationalPoint X)
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplι
        x)).obj C))
    (hΓ : IsZero ((boundedConstructibleLowerStar ℓ (toPoint X)).obj C)) : IsZero C := by
  set adj := boundedConstructibleUpperStarLowerStarAdjunction ℓ x
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : QuasiCompact (pointComplι x).left := inferInstanceAs (QuasiCompact (pointComplOpens x).ι)
  have hdisj : Disjoint (Set.range (pointComplι x).left.base) (Set.range x.left.base) :=
    (isCompl_range_pointComplι x).disjoint
  -- the unit `C ⟶ Rx_* Lx^* C` is an isomorphism
  have hη : IsIso (adj.unit.app C) := by
    refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl (Profinite.padicAlgClRingObj
        ℓ) ℓ x (pointComplι x)
      (isCompl_range_pointComplι x).symm _ ?_ ?_
    · have hT := isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ (pointComplι x) x
        hdisj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C)
      exact ⟨⟨hT.to_ _, hU.eq_of_src _ _, hT.eq_of_src _ _⟩⟩
    · have h := adj.left_triangle_components C
      have : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
          (adj.unit.app C) ≫
          adj.counit.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
              C)) := by
        rw [h]; exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  -- `RΓ(X, C) ≅ R(x ≫ a)_* Lx^* C = R(𝟙)_* Lx^* C`
  have hxa : x ≫ toPoint X = 𝟙 (point k) := by
    ext1
    simp
  have hE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C) := by
    refine isZero_of_isZero_boundedConstructibleLowerStar_id ℓ ?_
    refine IsZero.of_iso hΓ ?_
    exact eqToIso (by rw [hxa]) ≪≫
      ((boundedConstructibleLowerStarComp ℓ x (toPoint X)).app _).symm ≪≫
      (boundedConstructibleLowerStar ℓ (toPoint X)).mapIso (asIso (adj.unit.app C)).symm
  exact IsZero.of_iso ((boundedConstructibleLowerStar ℓ x).map_isZero hE) (asIso (adj.unit.app C))

end AlgebraicGeometry.ProEtale.CondensedRing
