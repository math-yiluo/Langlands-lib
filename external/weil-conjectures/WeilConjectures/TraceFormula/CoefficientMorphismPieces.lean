/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ClosedPieceFrobenius
public import WeilConjectures.TraceFormula.OpenPieceFrobenius

/-!

# The pieces of the localization triangle for a Frobenius coefficient morphism

Let `Φ` be a finite universal homeomorphism of `X`, `j : U ⟶ X` an open immersion and
`i : Z ⟶ X` a closed immersion onto the complement, both stable under `Φ`. For a bounded
constructible `K` and an arbitrary, not necessarily invertible, map `ψ : LΦ^* K ⟶ K`, this file
defines the endomorphisms `E_U` and `E_Z` of `RΓ_c(X, Rj_! Lj^* K)` and `RΓ_c(X, Ri_* Li^* K)`
induced by the restrictions of `ψ` to `U` and `Z`, writes them as `RΓ_c(X, ψ_U) ∘ Φ^♯` and
`RΓ_c(X, ψ_Z) ∘ Φ^♯` for coefficient maps `ψ_U`, `ψ_Z`, and shows that they are compatible with
the counit `Rj_! Lj^* K ⟶ K` and the unit `K ⟶ Ri_* Li^* K` of the localization triangle
(blueprint `lemma-additivity-open-subscheme-complement`).

This is the content of `WeilConjectures.TraceFormula.LocalizationFrobenius`,
`WeilConjectures.TraceFormula.OpenPieceFrobenius` and
`WeilConjectures.TraceFormula.ClosedPieceFrobenius` for `(K, ψ)` in place of a Weil object.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace CoefficientMorphism

-- the coherence of the pullbacks along `Φ_Z ≫ i = i ≫ Φ` is a long elaboration
omit [IsUniversalHomeomorphism ΦZ.left] [IsUniversalHomeomorphism Φ.left] in
/-- The operator `RΓ_c(ψ) ∘ Φ^♯` commutes with the pullback to a closed piece (blueprint
`lemma-additivity-open-subscheme-complement`): for a closed immersion `i` with `Φ_Z ≫ i = i ≫ Φ`,
`i^♯ ∘ RΓ_c(X, ψ) ∘ Φ^♯ = RΓ_c(Z, ψ|_Z) ∘ Φ_Z^♯ ∘ i^♯`. -/
theorem compactPullback_comp_comp_compactPullback (hi : ΦZ ≫ i = i ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    ((compactPullback ℓ Φ).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map ψ) ≫
        (compactPullback ℓ i).app K =
      (compactPullback ℓ i).app K ≫
        ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ≫
          (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
            ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K ≫
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map ψ)) := by
  have : IsProper (i ≫ Φ).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (ΦZ ≫ i).left := by
    rw [Over.comp_left]
    infer_instance
  exact frobenius_closedPiece_aux (compactPullback ℓ Φ) (compactPullback ℓ i)
    (compactPullback ℓ ΦZ) (compactPullback ℓ (i ≫ Φ)) (compactPullback ℓ (ΦZ ≫ i))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i Φ)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΦZ i) K
    (eqToHom (by rw [hi])) (compactPullback_comp_app ℓ i Φ K)
    (compactPullback_comp_app ℓ ΦZ i K) (compactPullback_app_congr ℓ hi K)
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K)
    (weilUpperStarComparison_hom_app ℓ ΦZ Φ i hi K) ψ _ rfl _ _ rfl rfl

variable (ℓ) in
/-- The operator `E_U` on `RΓ_c(X, Rj_! Lj^* K)` (blueprint
`lemma-additivity-open-subscheme-complement`): the operator `RΓ_c(U, ψ|_U) ∘ Φ_U^♯` of the
restriction of `ψ`, transported along `Ra_{X!} Rj_! ≅ Ra_{U!}`. -/
noncomputable def openPieceOperator (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) :=
  (boundedConstructibleLowerShriekCompToPoint ℓ j).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
    ((compactPullback ℓ ΦU).app ((boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint U)).map
        ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map ψ)) ≫
    (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)

variable (ℓ) in
/-- The operator `E_Z` on `RΓ_c(X, Ri_* Li^* K)` (blueprint
`lemma-additivity-open-subscheme-complement`): the operator `RΓ_c(Z, ψ|_Z) ∘ Φ_Z^♯` of the
restriction of `ψ`, transported along `Ra_{X!} Ri_* ≅ Ra_{Z!}`. -/
noncomputable def closedPieceOperator (hi : ΦZ ≫ i = i ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) :=
  (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ≫
    ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map ψ)) ≫
    (boundedConstructibleLowerStarCompToPoint ℓ i).inv.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)

-- the closed-piece operator unfolds to a long composite
omit [IsUniversalHomeomorphism ΦZ.left] [IsUniversalHomeomorphism Φ.left] in
/-- The square of the closed piece (blueprint `lemma-additivity-open-subscheme-complement`):
`E_Z ∘ RΓ_c(η) = RΓ_c(η) ∘ RΓ_c(ψ) ∘ Φ^♯` for the unit `η : K ⟶ Ri_* Li^* K`. -/
theorem comp_map_unit_eq_map_unit_comp_closedPieceOperator (hi : ΦZ ≫ i = i ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    ((compactPullback ℓ Φ).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map ψ) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K) =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K) ≫ closedPieceOperator ℓ hi K ψ := by
  have e := compactPullback_app_eq (ℓ := ℓ) i K
  have h : ((compactPullback ℓ Φ).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map ψ) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) =
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ≫
        ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ≫
          (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
            ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K ≫
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map ψ)) := by
    rw [← e]
    exact compactPullback_comp_comp_compactPullback hi K ψ
  rw [closedPieceOperator,
    ← cancel_mono ((boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)),
    Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

-- the open-piece operator unfolds to a long composite
omit [IsClosedImmersion i.left] in
/-- The square of the open piece (blueprint `lemma-additivity-open-subscheme-complement`, Step
2(a)): `RΓ_c(ε) ∘ E_U = RΓ_c(ψ) ∘ Φ^♯ ∘ RΓ_c(ε)` for the counit `ε : Rj_! Lj^* K ⟶ K`. -/
theorem openPieceOperator_comp_map_counit (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    openPieceOperator ℓ hj K ψ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) ≫
        ((compactPullback ℓ Φ).app K ≫
          (boundedConstructibleLowerShriek ℓ (toPoint X)).map
            ψ) := by
  have h := compToPoint_inv_app_comp_counit_comp_compactPullback ℓ j hj K
  have hn₁ := (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.naturality
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map ψ)
  have hn₂ := congrArg
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
    ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.naturality ψ)
  simp only [Functor.comp_map, Functor.comp_obj] at hn₁
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, Functor.comp_obj,
    Functor.id_obj] at hn₂
  rw [boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl] at hn₂ ⊢
  rw [openPieceOperator,
    ← cancel_epi ((boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, reassoc_of% h]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn₁, hn₂]

variable (ℓ) in
/-- The coefficient `ψ_U : LΦ^* Rj_! Lj^* K ⟶ Rj_! Lj^* K` of the open piece (blueprint
`lemma-additivity-open-subscheme-complement`): the compact-support base change
`LΦ^* Rj_! ⟶ Rj_! LΦ_U^*` along the cartesian square `Φ_U ≫ j = j ≫ Φ`, followed by `Rj_!` of the
restriction of `ψ` to `U`. -/
noncomputable def openPieceCoefficient (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ⟶
      (boundedConstructibleLowerShriek ℓ j).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) :=
  (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj)).app _ ≫
    (boundedConstructibleLowerShriek ℓ j).map
      ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map ψ)

-- the open-piece operator unfolds to a long composite
omit [IsClosedImmersion i.left] in
/-- The operator `E_U` of the open piece is `RΓ_c(X, ψ_U) ∘ Φ^♯` on `RΓ_c(X, Rj_! Lj^* K)`
(blueprint `lemma-additivity-open-subscheme-complement`). -/
lemma openPieceOperator_eq (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    openPieceOperator ℓ hj K ψ =
      (compactPullback ℓ Φ).app
          ((boundedConstructibleLowerShriek ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          (openPieceCoefficient ℓ hj K ψ) := by
  have h := openPiece_comp_eq_of_baseChange (compactPullback ℓ Φ) (compactPullback ℓ ΦU)
    (boundedConstructibleLowerShriekCompToPoint ℓ j)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj))
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
    (compactPullback_app_comp_baseChange ℓ (isPullback_of_comp_eq_of_isOpenImmersion j hj)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))
    ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map ψ)
    (openPieceCoefficient ℓ hj K ψ) rfl
  rw [openPieceOperator,
    ← cancel_mono ((boundedConstructibleLowerShriekCompToPoint ℓ j).hom.app _),
    Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  simpa only [Category.assoc] using h

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsFinite ΦU.left] in
/-- The coefficient of the open piece is compatible with the counit `ε : Rj_! Lj^* K ⟶ K`
(blueprint `lemma-additivity-open-subscheme-complement`). -/
lemma upperStar_map_counit_comp (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) ≫ ψ =
      openPieceCoefficient ℓ hj K ψ ≫
        (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K := by
  have hn := (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.naturality
    ψ
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [WeilBoundedConstructible.upperStar_map_counit_eq hj, openPieceCoefficient]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]

variable (ℓ) in
/-- The coefficient `ψ_Z : LΦ^* Ri_* Li^* K ⟶ Ri_* Li^* K` of the closed piece (blueprint
`lemma-additivity-open-subscheme-complement`): the adjoint of the restriction of `ψ` to `Z`, through
the pullback comparison and the counit of `Li^* ⊣ Ri_*`. -/
noncomputable def closedPieceCoefficient (hi : ΦZ ≫ i = i ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
      (boundedConstructibleLowerStar ℓ i).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) :=
  closedPieceCoeff
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi) _
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map ψ)

-- the closed-piece operator unfolds to a long composite
omit [IsUniversalHomeomorphism Φ.left] [IsUniversalHomeomorphism ΦZ.left] in
/-- The operator `E_Z` of the closed piece is `RΓ_c(X, ψ_Z) ∘ Φ^♯` on `RΓ_c(X, Ri_* Li^* K)`
(blueprint `lemma-additivity-open-subscheme-complement`). -/
lemma closedPieceOperator_eq (hi : ΦZ ≫ i = i ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    closedPieceOperator ℓ hi K ψ =
      (compactPullback ℓ Φ).app
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          (closedPieceCoefficient ℓ hi K ψ) := by
  rw [closedPieceOperator]
  exact closedPiece_conj_eq_closedPieceCoeff
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i)
    (compactPullback ℓ Φ) (compactPullback ℓ i) (compactPullback ℓ ΦZ)
    (boundedConstructibleLowerStarCompToPoint ℓ i) (compactPullback_app_eq (ℓ := ℓ) i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi)
    (WeilBoundedConstructible.compactPullback_comp_compactPullback_comparison hi)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map ψ)

omit [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦZ.left]
  [IsUniversalHomeomorphism ΦZ.left] [IsClosedImmersion i.left] in
/-- The coefficient of the closed piece is compatible with the unit `η : K ⟶ Ri_* Li^* K`
(blueprint `lemma-additivity-open-subscheme-complement`). -/
lemma upperStar_map_unit_comp_closedPieceCoefficient (hi : ΦZ ≫ i = i ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K) ≫ closedPieceCoefficient ℓ hi K ψ =
      ψ ≫ (boundedConstructibleUpperStarLowerStarAdjunction
        ℓ i).unit.app K :=
  closedPieceCoeff_unit_comm
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi) K ψ

end CoefficientMorphism

end AlgebraicGeometry.ProEtale.CondensedRing
