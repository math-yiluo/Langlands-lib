/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.InvariantPieceAdditivity

/-!

# Graded pieces of a correspondence and additivity along a finite filtration

Let `c = (c₁, c₂) : C ⟶ X × X` be an endocorrespondence of `(X, K)` with coefficient map
`u : Lc₂^* K ⟶ Rc₁^! K`.

* For a closed immersion `i : Z ⟶ X` with open complement `U` such that `c₂` maps
  `C_Z = c₁⁻¹(Z)` into `Z`, the coefficient map `u` determines unique coefficient maps on the two
  pieces `K_U = j_! Lj^* K` and `K_Z = Ri_* Li^* K` of the localization triangle
  `K_U ⟶ K ⟶ K_Z ⟶` compatible with `u`; they are the open piece coefficient `u_U` and the
  pushforward `u_Z` of the restriction `u_{|Z}` of `u` to `Z`, whose exceptional adjoint is
  `Rc_{1Z!} Lc_{2Z}^* Li^* K ≅ Li^* Rc₁_! Lc₂^* K --Li^* û--> Li^* K`, and `(u_U, u, u_Z)` is a
  morphism of the localization triangles under `Lc₂^*` and `Rc₁^!`
  (`ProEtale.CondensedRing.Correspondence.openPieceCoeff_closedPieceCoeff_spec`).
* For a finite filtration `0 = M₀ ⟶ M₁ ⟶ ⋯ ⟶ Mₙ` given by distinguished triangles
  `M_a ⟶ M_{a+1} ⟶ G_a ⟶`, with coefficient maps on the `M_a` and the graded pieces `G_a`
  forming morphisms of these triangles, the trace class of the coefficient map on `Mₙ` is the sum
  of the trace classes of the graded pieces, provided the corner morphism groups of
  `Correspondence.traceClass_eq_add_of_distTriang` vanish at each step
  (`ProEtale.CondensedRing.Correspondence.traceClassWithCoeff_eq_sum_of_distTriang`).

## Implementation details

* As in the rest of this API, the set-theoretic condition `c₁⁻¹(Z) ⊆ c₂⁻¹(Z)` is replaced by the
  scheme-theoretic factorisation `w₂ : i' ≫ c₂ = c_{2Z} ≫ i`.
* The general additivity statement assumes only a lift of the coefficient maps to the filtered
  derived category, which is not yet available. The vanishing hypotheses used here are much
  stronger and fail for typical filtrations.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

section Decomposition

variable {Z CZ : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType CZ.hom] [QuasiCompact CZ.hom] [IsSeparated CZ.hom]
  {i : Z ⟶ X} [IsClosedImmersion i.left] {i' : CZ ⟶ c.C} {c₁Z c₂Z : CZ ⟶ Z}

/-- Let `i : Z ⟶ X` be a closed immersion with open complement `U` such that `c₂` maps
`C_Z = c₁⁻¹(Z)` into `Z`. Then

1. the open piece coefficient `u_U` is the unique coefficient map on `K_U = j_! Lj^* K`
   compatible with `u` along the counit `K_U ⟶ K`;
2. the closed piece coefficient `u_Z = [i, i']_! u_{|Z}` is the unique coefficient map on
   `K_Z = Ri_* Li^* K` compatible with `u` along the unit `K ⟶ K_Z`;
3. the exceptional adjoint of the restriction `u_{|Z}` of `u` to the correspondence
   `c_Z : C_Z ⟶ Z × Z` is `Rc_{1Z!} Lc_{2Z}^* Li^* K ≅ Li^* Rc₁_! Lc₂^* K --Li^* û--> Li^* K`;
4. for every distinguished localization triangle `T = (K_U ⟶ K ⟶ K_Z ⟶)`, the maps
   `(u_U, u, u_Z)` form a morphism of triangles `Lc₂^* T ⟶ Rc₁^! T`. -/
theorem openPieceCoeff_closedPieceCoeff_spec (U : X.left.Opens)
    (hUi : IsCompl (Set.range (opensOverι U).left.base) (Set.range i.left.base))
    (sq : IsPullback i' c₁Z c.c₁ i) (w₂ : i' ≫ c.c₂ = c₂Z ≫ i) :
    (∀ v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
          (openPiece K U) ⟶ (boundedConstructibleUpperShriek ℓ c.c₁).obj (openPiece K U),
        v ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map
            ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
              (opensOverι U)).counit.app K) =
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
            ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
              (opensOverι U)).counit.app K) ≫ c.u ↔
        v = c.openPieceCoeff U (c.preimage_le_of_isPullback U hUi sq w₂)) ∧
    (∀ v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (boundedConstructibleUpperShriek ℓ c.c₁).obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)),
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) ≫ v =
          c.u ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) ↔
        v = (c.closedPieceDiagram sq w₂).pushforwardCoeff) ∧
    (haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq;
      ((boundedConstructibleUpperShriekAdjunction ℓ c₁Z).homEquiv _ _).symm
          (c.restrictClosed sq w₂).u =
        (boundedConstructibleLowerShriek ℓ c₁Z).map (upperStarIsoOfComm w₂ K).hom ≫
          inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K)) ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map
            (((boundedConstructibleUpperShriekAdjunction ℓ c.c₁).homEquiv _ _).symm c.u)) ∧
    ∀ δ, Triangle.mk
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          (opensOverι U)).counit.app K)
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) δ ∈ distTriang _ →
      ∃ φ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).mapTriangle.obj
          (Triangle.mk
            ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
              (opensOverι U)).counit.app K)
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) δ) ⟶
        (boundedConstructibleUpperShriek ℓ c.c₁).mapTriangle.obj
          (Triangle.mk
            ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
              (opensOverι U)).counit.app K)
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) δ),
        φ.hom₁ = c.openPieceCoeff U (c.preimage_le_of_isPullback U hUi sq w₂) ∧
          φ.hom₂ = c.u ∧ φ.hom₃ = (c.closedPieceDiagram sq w₂).pushforwardCoeff := by
  have h₂ := fun v ↦ (⟨c.eq_closedPieceCoeff_of_upperStar_map_unit_comp U hUi sq w₂ v,
    by rintro rfl; exact c.upperStar_map_unit_comp_closedPieceCoeff sq w₂⟩ :
      _ ↔ v = (c.closedPieceDiagram sq w₂).pushforwardCoeff)
  refine ⟨fun v ↦ ⟨c.eq_openPieceCoeff_of_comp_map_counit U hUi sq w₂ v, ?_⟩, h₂,
    homEquiv_symm_restrictedCoeffOfIsPullback sq w₂ K c.u, fun δ hT ↦ ?_⟩
  · rintro rfl
    exact c.openPieceCoeff_comp_map_counit U _
  obtain ⟨w, hw₂, hw₃⟩ := complete_distinguished_triangle_morphism _ _
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map_distinguished
      _ hT)
    ((boundedConstructibleUpperShriek ℓ c.c₁).map_distinguished _ hT)
    (c.openPieceCoeff U (c.preimage_le_of_isPullback U hUi sq w₂)) c.u
    (c.openPieceCoeff_comp_map_counit U _).symm
  have hw : w = (c.closedPieceDiagram sq w₂).pushforwardCoeff := (h₂ w).1 hw₂
  subst hw
  exact ⟨Triangle.homMk _ _ (c.openPieceCoeff U (c.preimage_le_of_isPullback U hUi sq w₂)) c.u
    (c.closedPieceDiagram sq w₂).pushforwardCoeff (c.openPieceCoeff_comp_map_counit U _).symm
    hw₂ hw₃, rfl, rfl, rfl⟩

end Decomposition

/-- Let `0 = M₀ ⟶ M₁ ⟶ ⋯ ⟶ Mₙ` be a finite filtration with graded pieces `G_a`, given by
distinguished triangles `M_a ⟶ M_{a+1} ⟶ G_a ⟶`, and let `v_a`, `w_a` be coefficient maps on the
support of `c` on `M_a` and `G_a` forming, at each step, a morphism of the triangles
`Lc₂^* (-)` and `Rc₁^! (-)`. If the corner morphism groups of
`Correspondence.traceClass_eq_add_of_distTriang` vanish at each step, then
`Tr_c(vₙ) = ∑_a Tr_c(w_a)`. -/
theorem traceClassWithCoeff_eq_sum_of_distTriang (F : c.FixedLocus) (n : ℕ)
    (M G : ℕ → Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (ι : ∀ a, M a ⟶ M (a + 1))
    (π : ∀ a, M (a + 1) ⟶ G a) (δ : ∀ a, G a ⟶ (M a) ⟦(1 : ℤ)⟧)
    (hT : ∀ a < n, Triangle.mk (ι a) (π a) (δ a) ∈ distTriang _) (hM : IsZero (M 0))
    (v : ∀ a, (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj (M a) ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj (M a))
    (w : ∀ a, (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj (G a) ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj (G a))
    (hv : ∀ a < n, (boundedConstructibleUpperStar _ ℓ c.c₂).map (ι a) ≫ v (a + 1) =
      v a ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map (ι a))
    (hw : ∀ a < n, (boundedConstructibleUpperStar _ ℓ c.c₂).map (π a) ≫ w a =
      v (a + 1) ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map (π a))
    (h₁ : ∀ a < n, ∀ φ : (boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
      (externalProduct ℓ (G a) (verdierDual ℓ (M a))) ⟦(-1 : ℤ)⟧, φ = 0)
    (h₂ : ∀ a < n, ∀ φ : externalProduct ℓ (M a) (verdierDual ℓ (M (a + 1))) ⟶
      (externalProduct ℓ (G a) (verdierDual ℓ (M a))) ⟦(-1 : ℤ)⟧, φ = 0)
    (h₃ : ∀ a < n, ∀ φ : externalProduct ℓ (M (a + 1)) (verdierDual ℓ (G a)) ⟶
      (externalProduct ℓ (G a) (verdierDual ℓ (M a))) ⟦(-1 : ℤ)⟧, φ = 0)
    (h₄ : ∀ a < n, ∀ φ : (externalProduct ℓ (M a) (verdierDual ℓ (G a))) ⟦(1 : ℤ)⟧ ⟶
      (boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X), φ = 0) :
    F.traceClassWithCoeff (M n) (v n) =
      ∑ a ∈ Finset.range n, F.traceClassWithCoeff (G a) (w a) := by
  induction n with
  | zero =>
    exact (c.withCoeff (M 0) (v 0)).traceClass_eq_zero_of_isZero _ (Functor.map_isZero _ hM)
  | succ n ih =>
    have hn := Nat.lt_succ_self n
    rw [Finset.sum_range_succ, ← ih (fun a ha ↦ hT a (ha.trans hn)) (fun a ha ↦ hv a (ha.trans hn))
      (fun a ha ↦ hw a (ha.trans hn)) (fun a ha ↦ h₁ a (ha.trans hn))
      (fun a ha ↦ h₂ a (ha.trans hn)) (fun a ha ↦ h₃ a (ha.trans hn))
      (fun a ha ↦ h₄ a (ha.trans hn))]
    exact (c.withCoeff (M (n + 1)) (v (n + 1))).traceClass_eq_add_of_distTriang
      (F.withCoeff _ _) (hT n hn) (v n) (w n) (hv n hn) (hw n hn) (h₁ n hn) (h₂ n hn)
      (h₃ n hn) (h₄ n hn)

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
