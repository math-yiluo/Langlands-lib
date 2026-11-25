/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalizationFrobenius

/-!

# The open-piece Frobenius operator as the Frobenius of a coefficient map

In the setting of `WeilConjectures.TraceFormula.LocalizationFrobenius`, the operator `E_U` on
`RΓ_c(X, Rj_! Lj^* K)` is `RΓ_c(X, ψ_U) ∘ Φ^♯` for a Frobenius coefficient map
`ψ_U : LΦ^* Rj_! Lj^* K ⟶ Rj_! Lj^* K`, compatible with the counit `Rj_! Lj^* K ⟶ K` of the
localization triangle. The abstract shape of the computation is isolated first, for functors
between arbitrary categories.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.openPieceFrobeniusCoeff`: the coefficient map
  `ψ_U`.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusOpenPiece_eq`:
  `E_U = RΓ_c(X, ψ_U) ∘ Φ^♯`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.upperStar_map_counit_comp_str_hom`: the
  compatibility of `ψ_U` with the counit.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section PieceCoefficients

variable {CX D : Type*} [Category CX] [Category D] {aX : CX ⥤ D} {uΦ : CX ⥤ CX}
variable {CU : Type*} [Category CU] {aU : CU ⥤ D} {uΦU : CU ⥤ CU} {rj : CU ⥤ CX}

/-- The abstract shape of the open-piece operator: conjugated along `c : rj ⋙ aX ≅ aU`, the
operator `pΦU ≫ aU g` of a coefficient map `g` is `pΦ` followed by the image of
`bc ≫ rj g`, for a base change map `bc` compatible with the pullbacks:
```
aX (rj N) ──c──▶ aU N ──pΦU ≫ aU g──▶ aU N ──c⁻¹──▶ aX (rj N)
    ‖                                                  ‖
aX (rj N) ──pΦ──▶ aX (uΦ (rj N)) ──aX (bc ≫ rj g)──▶ aX (rj N)
```
-/
lemma openPiece_conj_eq_of_baseChange (pΦ : aX ⟶ uΦ ⋙ aX) (pΦU : aU ⟶ uΦU ⋙ aU) (c : rj ⋙ aX ≅ aU)
    (bc : rj ⋙ uΦ ⟶ uΦU ⋙ rj) (N : CU)
    (hB : pΦ.app (rj.obj N) ≫ aX.map (bc.app N) ≫ c.hom.app (uΦU.obj N) =
      c.hom.app N ≫ pΦU.app N) (g : uΦU.obj N ⟶ N) :
    c.hom.app N ≫ (pΦU.app N ≫ aU.map g) ≫ c.inv.app N =
      pΦ.app (rj.obj N) ≫ aX.map (bc.app N ≫ rj.map g) := by
  have hn := c.hom.naturality g
  dsimp at hn
  rw [← Category.assoc, ← Category.assoc, ← hB]
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app]
  simp

/-- `openPiece_conj_eq_of_baseChange` for a coefficient `ψ` given by its defining equation. -/
lemma openPiece_comp_eq_of_baseChange (pΦ : aX ⟶ uΦ ⋙ aX) (pΦU : aU ⟶ uΦU ⋙ aU) (c : rj ⋙ aX ≅ aU)
    (bc : rj ⋙ uΦ ⟶ uΦU ⋙ rj) (N : CU)
    (hB : pΦ.app (rj.obj N) ≫ aX.map (bc.app N) ≫ c.hom.app (uΦU.obj N) =
      c.hom.app N ≫ pΦU.app N) (g : uΦU.obj N ⟶ N) (ψ : uΦ.obj (rj.obj N) ⟶ rj.obj N)
    (hψ : ψ = bc.app N ≫ rj.map g) :
    c.hom.app N ≫ pΦU.app N ≫ aU.map g = (pΦ.app (rj.obj N) ≫ aX.map ψ) ≫ c.hom.app N := by
  rw [hψ, ← openPiece_conj_eq_of_baseChange pΦ pΦU c bc N hB g]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
end PieceCoefficients

section Frobenius

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace WeilBoundedConstructible

variable (ℓ) in
/-- The Frobenius coefficient `ψ_U : LΦ^* Rj_! Lj^* K ⟶ Rj_! Lj^* K` of the open piece: the
compact-support base change `LΦ^* Rj_! ⟶ Rj_! LΦ_U^*` along the cartesian square
`Φ_U ≫ j = j ≫ Φ`, followed by `Rj_!` of the Frobenius structure of `K|_U`. -/
noncomputable def openPieceFrobeniusCoeff (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) ⟶
      (boundedConstructibleLowerShriek ℓ j).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier) :=
  (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj)).app _ ≫
    (boundedConstructibleLowerShriek ℓ j).map
      ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K.carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map K.str.hom)

-- the open-piece operator unfolds to a long composite
omit [IsClosedImmersion i.left] in
/-- The operator `E_U` of the open piece is `RΓ_c(X, ψ_U) ∘ Φ^♯` on `RΓ_c(X, Rj_! Lj^* K)`. -/
lemma compactFrobeniusOpenPiece_eq (hj : ΦU ≫ j = j ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) :
    compactFrobeniusOpenPiece ℓ hj K =
      (compactPullback ℓ Φ).app
          ((boundedConstructibleLowerShriek ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              K.carrier)) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          (openPieceFrobeniusCoeff ℓ hj K) := by
  have h := openPiece_comp_eq_of_baseChange (compactPullback ℓ Φ) (compactPullback ℓ ΦU)
    (boundedConstructibleLowerShriekCompToPoint ℓ j)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj))
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)
    (compactPullback_app_comp_baseChange ℓ (isPullback_of_comp_eq_of_isOpenImmersion j hj)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier))
    ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map K.str.hom)
    (openPieceFrobeniusCoeff ℓ hj K) rfl
  rw [compactFrobeniusOpenPiece, compactFrobenius_weilUpperStar hj K,
    ← cancel_mono ((boundedConstructibleLowerShriekCompToPoint ℓ j).hom.app _),
    Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  simpa only [Category.assoc] using h

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsFinite ΦU.left] in
/-- The pullback along `Φ` of the counit `ε : Rj_! Lj^* K ⟶ K` is the compact-support base change
followed by `Rj_!` of the pullback comparison and the counit at `LΦ^* K` (blueprint
`def-exchange-projection` for the open immersion `j`). -/
lemma upperStar_map_counit_eq (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) =
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
          (isPullback_of_comp_eq_of_isOpenImmersion j hj)).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
        (boundedConstructibleLowerShriek ℓ j).map
          ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K) ≫
        (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K) := by
  have sq := isPullback_of_comp_eq_of_isOpenImmersion j hj
  have hC1 := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion ℓ sq
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
  have hEx := Adjunction.exchangeLeft_app_comp_map_counit_app
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.flip) K
  rw [← boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft
    (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq] at hEx
  have hn := (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
    j).hom.naturality ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K)
  rw [weilUpperStarComparison_hom_app_eq ℓ j hj sq.toCommSq.flip] at hn ⊢
  rw [boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl,
    counit_app_ofNatIsoRight_upperShriekIsoUpperStar,
    counit_app_ofNatIsoRight_upperShriekIsoUpperStar, Functor.map_comp, ← hC1]
  simp only [Category.assoc]
  rw [hEx, reassoc_of% hn]

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsFinite ΦU.left] in
/-- The Frobenius coefficient of the open piece is compatible with the counit
`ε : Rj_! Lj^* K ⟶ K`. -/
lemma upperStar_map_counit_comp_str_hom (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          K.carrier) ≫ K.str.hom =
      openPieceFrobeniusCoeff ℓ hj K ≫
        (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          K.carrier := by
  have hn := (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.naturality
    K.str.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [upperStar_map_counit_eq hj, openPieceFrobeniusCoeff]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
