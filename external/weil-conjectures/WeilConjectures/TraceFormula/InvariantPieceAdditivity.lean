/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingAdditivity
public import WeilConjectures.TraceFormula.InvariantClosedPiece
public import WeilConjectures.TraceFormula.InvariantOpenPiece

/-!

# Additivity of trace classes along an invariant open–closed decomposition

Let `c = (c₁, c₂) : C ⟶ X × X` be an endocorrespondence of `(X, K)` with coefficient map `u`, and
let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. Suppose that `c₂` maps
the preimage `C_Z = c₁⁻¹(Z)` into `Z`; in particular `c₁⁻¹(Z) ⊆ c₂⁻¹(Z)`, i.e. `c₂⁻¹(U) ⊆ c₁⁻¹(U)`.
Then the trace class of `u` is the sum of the trace classes of the open piece coefficient
`u_U = [j]_! (u|_U)` on `K_U = j_! Lj^* K` and of the closed piece coefficient
`u_Z = [i, i']_! u_{|Z}` on `K_Z = Ri_* Li^* K`, the pushforward of the restriction of `u` to `Z`
(`ProEtale.CondensedRing.Correspondence.traceClass_eq_add_of_isClosedImmersion`, blueprint
`proposition-additivity-trace-classes`, item 2):
```
Tr_c(u) = Tr_c(u_U) + Tr_c(u_Z).
```
This generalizes `Correspondence.traceClass_eq_add_of_isPullback` from a rational point with
reduced fibre to an arbitrary closed subscheme. It is
`Correspondence.traceClass_eq_add_of_distTriang` for the open–closed triangle
`K_U ⟶ K ⟶ K_Z ⟶`, whose corner morphism groups vanish by support considerations;
the squares of the morphism of triangles are
`Correspondence.openPieceCoeff_comp_map_counit` and
`Correspondence.upperStar_map_unit_comp_closedPieceCoeff`.

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

/-! ### The corner terms of an open–closed decomposition -/

section Pieces

variable {U Z : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X)
  (hji : Disjoint (Set.range j.left.base) (Set.range i.left.base))
  (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (A : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

include hji

/-- The restriction to `U` of the dual of a complex pushed forward from `Z` vanishes:
`Lj^* D_X (Ri_* A) = 0` when `j` and `i` have disjoint ranges. -/
lemma isZero_upperStar_verdierDual_lowerStar_of_disjoint :
    IsZero ((boundedConstructibleUpperStar _ ℓ j).obj
      (verdierDual ℓ ((boundedConstructibleLowerStar ℓ i).obj A))) := by
  have := isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion
    ℓ j ((boundedConstructibleLowerStar ℓ i).obj A)
  exact (isZero_ihom_obj_of_isZero
    (isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ j i hji A) _).of_iso
    (asIso ((Functor.LaxMonoidal.ihomComparison (boundedConstructibleUpperStar _ ℓ j)
      ((boundedConstructibleLowerStar ℓ i).obj A)).app _))

/-- `j_! B ⊗ D_X (Ri_* A) = 0` when `j` and `i` have disjoint ranges. -/
lemma isZero_openImmersionLowerShriek_tensor_verdierDual_lowerStar_of_disjoint :
    IsZero ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B ⊗
      verdierDual ℓ ((boundedConstructibleLowerStar ℓ i).obj A)) := by
  have := NatIso.isIso_app_of_isIso (Functor.Monoidal.projectionMap
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (verdierDual ℓ ((boundedConstructibleLowerStar ℓ i).obj A))) B
  exact ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).map_isZero
    (isZero_tensorObj_of_isZero_left
      (isZero_upperStar_verdierDual_lowerStar_of_disjoint j i hji A) B)).of_iso
    ((β_ _ _) ≪≫ (asIso ((Functor.Monoidal.projectionMap
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j) _).app B)).symm)

/-- The corner `j_! B ⊠ D_X (Ri_* A)` has no morphism of any degree to `RΔ_* ω_X` when `j` and
`i` have disjoint ranges. -/
lemma eq_zero_of_externalProduct_shift_to_diag_of_disjoint
    (φ : (externalProduct ℓ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B)
        (verdierDual ℓ ((boundedConstructibleLowerStar ℓ i).obj A))) ⟦(1 : ℤ)⟧ ⟶
      (boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X)) :
    φ = 0 :=
  eq_zero_of_isZero_upperStar (diag X) (((shiftFunctor _ (1 : ℤ)).map_isZero
    ((isZero_openImmersionLowerShriek_tensor_verdierDual_lowerStar_of_disjoint j i hji B
      A).of_iso (diagUpperStarExternalProductIso ℓ _ _))).of_iso
    (((boundedConstructibleUpperStar _ ℓ (diag X)).commShiftIso (1 : ℤ)).app _)) φ

/-- There is no morphism of degree `-1` from `j_! B ⊠ D_X K` to `Ri_* A ⊠ D_X (j_! B')` when `j`
and `i` have disjoint ranges. -/
lemma eq_zero_of_externalProduct_openPiece_of_disjoint
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B' : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ : externalProduct ℓ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B)
        (verdierDual ℓ K) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ i).obj A)
        (verdierDual ℓ
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B'))) ⟦(-1 : ℤ)⟧) :
    φ = 0 :=
  eq_zero_of_shift (fun _ ↦ eq_zero_of_externalProduct (fun _ ↦ eq_zero_of_isZero_upperStar i
    (isZero_upperStar_lowerShriek_tensor_shift i _
      ((isZero_upperStar_lowerShriek_tensor i _
        (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j i hji B)).of_iso
        ((boundedConstructibleUpperStar _ ℓ i).mapIso
          ((boundedConstructibleLowerShriek ℓ _).mapIso
            (whiskerLeftIso _ (β_ _ _) ≪≫ (α_ _ _ _).symm))))) _) _) φ

/-- There is no morphism of degree `-1` from `K ⊠ D_X (Ri_* A)` to `Ri_* A' ⊠ D_X (j_! B)` when
`j` and `i` have disjoint ranges. -/
lemma eq_zero_of_externalProduct_closedPiece_of_disjoint
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (A' : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ : externalProduct ℓ K
        (verdierDual ℓ ((boundedConstructibleLowerStar ℓ i).obj A)) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ i).obj A')
        (verdierDual ℓ
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B))) ⟦(-1 : ℤ)⟧) :
    φ = 0 := by
  refine eq_zero_of_shift (fun _ ↦ eq_zero_of_externalProduct (fun _ ↦
    eq_zero_of_isZero_upperStar i (isZero_upperStar_lowerShriek_tensor_shift i _ ?_) _) _) φ
  exact (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map_isZero
    ((boundedConstructibleLowerShriek ℓ _).map_isZero
    ((isZero_tensorObj_of_isZero_right _ ((boundedConstructibleUpperStar _ ℓ _).map_isZero
      (isZero_openImmersionLowerShriek_tensor_verdierDual_lowerStar_of_disjoint j i hji B
        A))).of_iso
      ((α_ _ _ _).symm ≪≫ whiskerRightIso (β_ _ _) _ ≪≫ (α_ _ _ _) ≪≫
        whiskerLeftIso _ (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ _) _ _))))

omit hji in
/-- There is no morphism of degree `-1` from the class `Rs_! ℚ̄_ℓ` of a support
`s : C ⟶ X ⨯ X` to `Ri_* A ⊠ D_X N` as soon as `Li^* R(s ≫ p₁)_! L(s ≫ p₂)^* N = 0`. -/
lemma eq_zero_of_lowerShriek_unit_of_lowerStar {C : Over (Spec (.of k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom] (s : C ⟶ X ⨯ X)
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hz : IsZero ((boundedConstructibleUpperStar _ ℓ i).obj
      ((boundedConstructibleLowerShriek ℓ (s ≫ prod.fst)).obj
        ((boundedConstructibleUpperStar _ ℓ (s ≫ prod.snd)).obj N))))
    (φ : (boundedConstructibleLowerShriek ℓ s).obj (𝟙_ _) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ i).obj A)
        (verdierDual ℓ N)) ⟦(-1 : ℤ)⟧) :
    φ = 0 :=
  eq_zero_of_shift (fun _ ↦ eq_zero_of_externalProduct (fun _ ↦ eq_zero_of_isZero_upperStar i
    (isZero_upperStar_lowerShriek_tensor_shift i N (hz.of_iso
      ((boundedConstructibleUpperStar _ ℓ i).mapIso
        ((boundedConstructibleLowerShriek ℓ _).mapIso
          ((β_ _ _) ≪≫ asIso (boundedConstructibleExceptionalProjectionMorphism ℓ s _ _) ≪≫
            (boundedConstructibleLowerShriek ℓ s).mapIso ((λ_ _) ≪≫
              ((boundedConstructibleUpperStarComp _ ℓ s prod.snd).app N).symm)) ≪≫
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst).app _).symm)))) _) _) φ

end Pieces

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)
  {Z CZ : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType CZ.hom] [QuasiCompact CZ.hom] [IsSeparated CZ.hom]
  {i : Z ⟶ X} {i' : CZ ⟶ c.C} {c₁Z c₂Z : CZ ⟶ Z}

omit [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType CZ.hom] [QuasiCompact CZ.hom] [IsSeparated CZ.hom] in
/-- If `c₂` maps `C_Z = c₁⁻¹(Z)` into `Z`, then the complement `U` of `Z` satisfies
`c₂⁻¹(U) ⊆ c₁⁻¹(U)`. -/
lemma preimage_le_of_isPullback (U : X.left.Opens)
    (hUi : IsCompl (Set.range (opensOverι U).left.base) (Set.range i.left.base))
    (sq : IsPullback i' c₁Z c.c₁ i) (w₂ : i' ≫ c.c₂ = c₂Z ≫ i) :
    c.c₂.left ⁻¹ᵁ U ≤ c.c₁.left ⁻¹ᵁ U := by
  have hsq : IsPullback i'.left c₁Z.left c.c₁.left i.left := sq.map (Over.forget _)
  have hU : (U : Set X.left) = (Set.range i.left.base)ᶜ := by
    rw [← hUi.compl_eq, range_opensOverι]
    simp
  intro z hz
  simp only [Scheme.Hom.mem_preimage] at hz ⊢
  rw [← SetLike.mem_coe, hU] at hz ⊢
  intro ⟨p, hp⟩
  have hmem : z ∈ Set.range (pullback.fst c.c₁.left i.left) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨p, hp⟩
  obtain ⟨q, rfl⟩ := hmem
  refine hz ⟨c₂Z.left.base (hsq.isoPullback.inv.base q), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← w₂, Over.comp_left, Scheme.Hom.comp_apply]
  congr 1
  rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_fst]

/-- `Li^* Rc₁_! Lc₂^* (j_! B) = 0` when `c₂` maps `C_Z = c₁⁻¹(Z)` into `Z` and `j` misses `Z`: by
compact-support base change in the cartesian square `i' ≫ c₁ = c_{1Z} ≫ i` it is
`Rc_{1Z!} Li'^* Lc₂^* (j_! B) = Rc_{1Z!} Lc_{2Z}^* Li^* j_! B = 0`. -/
lemma isZero_upperStar_lowerShriek_upperStar_openImmersionLowerShriek
    (sq : IsPullback i' c₁Z c.c₁ i) (w₂ : i' ≫ c.c₂ = c₂Z ≫ i)
    {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] (j : U ⟶ X) [IsOpenImmersion j.left]
    (hji : Disjoint (Set.range j.left.base) (Set.range i.left.base))
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((boundedConstructibleUpperStar _ ℓ i).obj
      ((boundedConstructibleLowerShriek ℓ c.c₁).obj
        ((boundedConstructibleUpperStar _ ℓ c.c₂).obj
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B)))) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  refine IsZero.of_iso ?_
    (asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app _))
  have hrange : Disjoint (Set.range j.left.base) (Set.range (i' ≫ c.c₂).left.base) := by
    refine hji.mono_right ?_
    rw [w₂, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  exact (boundedConstructibleLowerShriek ℓ c₁Z).map_isZero
    ((isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j (i' ≫ c.c₂) hrange
      B).of_iso ((boundedConstructibleUpperStarComp _ ℓ i' c.c₂).app _).symm)

/-- There is no morphism of degree `-1` from the class `Rc_! ℚ̄_ℓ` of the support of `c` to
`Ri_* A ⊠ D_X (j_! B)` when `c₂` maps `C_Z = c₁⁻¹(Z)` into `Z`
(`isZero_upperStar_lowerShriek_upperStar_openImmersionLowerShriek`). -/
lemma eq_zero_of_lowerShriek_support_of_isClosedImmersion
    (sq : IsPullback i' c₁Z c.c₁ i) (w₂ : i' ≫ c.c₂ = c₂Z ≫ i)
    {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] (j : U ⟶ X) [IsOpenImmersion j.left]
    (hji : Disjoint (Set.range j.left.base) (Set.range i.left.base))
    (A : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ : (boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ i).obj A)
        (verdierDual ℓ
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B))) ⟦(-1 : ℤ)⟧) :
    φ = 0 := by
  refine eq_zero_of_lowerShriek_unit_of_lowerStar i A _ _ ?_ φ
  rw [support_fst, support_snd]
  exact c.isZero_upperStar_lowerShriek_upperStar_openImmersionLowerShriek sq w₂ j hji B

variable [IsClosedImmersion i.left]

/-- **Additivity of trace classes along an invariant open–closed decomposition** (blueprint
`proposition-additivity-trace-classes`, item 2; Varshavsky, Prop. 1.5.10): let `i : Z ⟶ X` be a
closed immersion with open complement `U`, and suppose that `c₂` maps `C_Z = c₁⁻¹(Z)` (the
cartesian square `i' ≫ c₁ = c_{1Z} ≫ i`) into `Z`, `i' ≫ c₂ = c_{2Z} ≫ i`. Then
`Tr_c(u) = Tr_c(u_U) + Tr_c(u_Z)`, where `u_U` is the open piece coefficient on `j_! Lj^* K` and
`u_Z = [i, i']_! u_{|Z}` the pushforward of the restriction `u_{|Z}` of `u` to the correspondence
`c_Z` on `(Z, Li^* K)`. -/
theorem traceClass_eq_add_of_isClosedImmersion (F : c.FixedLocus) (U : X.left.Opens)
    (hUi : IsCompl (Set.range (opensOverι U).left.base) (Set.range i.left.base))
    (sq : IsPullback i' c₁Z c.c₁ i) (w₂ : i' ≫ c.c₂ = c₂Z ≫ i) :
    c.traceClass F =
      F.traceClassWithCoeff _ (c.openPieceCoeff U (c.preimage_le_of_isPullback U hUi sq w₂)) +
        F.traceClassWithCoeff _ (c.closedPieceDiagram sq w₂).pushforwardCoeff := by
  have hji := hUi.disjoint
  obtain ⟨δ, hT⟩ := exists_distTriang_openImmersionLowerShriek_lowerStar (opensOverι U) i hUi K
  exact c.traceClass_eq_add_of_distTriang F hT
    (c.openPieceCoeff U (c.preimage_le_of_isPullback U hUi sq w₂))
    (c.closedPieceDiagram sq w₂).pushforwardCoeff
    (c.openPieceCoeff_comp_map_counit U _).symm
    (c.upperStar_map_unit_comp_closedPieceCoeff sq w₂)
    (c.eq_zero_of_lowerShriek_support_of_isClosedImmersion sq w₂ (opensOverι U) hji _ _)
    (eq_zero_of_externalProduct_openPiece_of_disjoint (opensOverι U) i hji _ _ K _)
    (eq_zero_of_externalProduct_closedPiece_of_disjoint (opensOverι U) i hji _ _ K _)
    (eq_zero_of_externalProduct_shift_to_diag_of_disjoint (opensOverι U) i hji _ _)


omit [IsClosedImmersion i.left] in
/-- No morphism `T ⟶ (Ri_* A)⟦n⟧` is nonzero when `Li^* T = 0`. -/
lemma eq_zero_of_isZero_upperStar_shift {T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (hT : IsZero ((boundedConstructibleUpperStar _ ℓ i).obj T))
    (A : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (n : ℤ)
    (φ : T ⟶ (shiftFunctor _ n).obj ((boundedConstructibleLowerStar ℓ i).obj A)) : φ = 0 := by
  have e := ((boundedConstructibleLowerStar ℓ i).commShiftIso n).app A
  rw [← cancel_mono e.inv, zero_comp]
  exact eq_zero_of_isZero_upperStar i hT _

/-- **Uniqueness of the open piece coefficient** (blueprint
`lemma-lift-correspondence-invariant-decomposition`): when `c₂` maps `C_Z = c₁⁻¹(Z)` into the
closed complement `Z` of `U`, the open piece coefficient `u_U` is the only coefficient map on
`K_U = j_! Lj^* K` compatible with `u` along the counit `ε : K_U ⟶ K`. -/
theorem eq_openPieceCoeff_of_comp_map_counit (U : X.left.Opens)
    (hUi : IsCompl (Set.range (opensOverι U).left.base) (Set.range i.left.base))
    (sq : IsPullback i' c₁Z c.c₁ i) (w₂ : i' ≫ c.c₂ = c₂Z ≫ i)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
        (openPiece K U) ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj (openPiece K U))
    (hv : v ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
            (opensOverι U)).counit.app K) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
            (opensOverι U)).counit.app K) ≫ c.u) :
    v = c.openPieceCoeff U (c.preimage_le_of_isPullback U hUi sq w₂) := by
  have key : ∀ g : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
      (openPiece K U) ⟶ (boundedConstructibleUpperShriek ℓ c.c₁).obj ((shiftFunctor _ (-1 : ℤ)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))), g = 0 := by
    intro g
    rw [← ((boundedConstructibleUpperShriekAdjunction ℓ c.c₁).homEquiv _ _).apply_symm_apply g,
      eq_zero_of_isZero_upperStar_shift
        (c.isZero_upperStar_lowerShriek_upperStar_openImmersionLowerShriek sq w₂ (opensOverι U)
          hUi.disjoint _) _ _
        (((boundedConstructibleUpperShriekAdjunction ℓ c.c₁).homEquiv _ _).symm g),
      Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  rw [← sub_eq_zero]
  obtain ⟨δ, hT⟩ := exists_distTriang_openImmersionLowerShriek_lowerStar (opensOverι U) i hUi K
  have hT' := (boundedConstructibleUpperShriek ℓ c.c₁).map_distinguished _
    (Pretriangulated.inv_rot_of_distTriang _ hT)
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ hT'
    (v - c.openPieceCoeff U (c.preimage_le_of_isPullback U hUi sq w₂)) (by
      change _ ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          (opensOverι U)).counit.app K) = 0
      rw [Preadditive.sub_comp, hv, openPieceCoeff_comp_map_counit, sub_self])
  rw [hg, key g, zero_comp]

/-- **Uniqueness of the closed piece coefficient** (blueprint
`lemma-lift-correspondence-invariant-decomposition`, `lemma-closed-piece-pushforward`): when `c₂`
maps `C_Z = c₁⁻¹(Z)` into `Z`, the closed piece coefficient `u_Z = [i, i']_! u_{|Z}` is the only
coefficient map on `K_Z = Ri_* Li^* K` compatible with `u` along the unit `η : K ⟶ K_Z`. -/
theorem eq_closedPieceCoeff_of_upperStar_map_unit_comp (U : X.left.Opens)
    (hUi : IsCompl (Set.range (opensOverι U).left.base) (Set.range i.left.base))
    (sq : IsPullback i' c₁Z c.c₁ i) (w₂ : i' ≫ c.c₂ = c₂Z ≫ i)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)))
    (hv : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) ≫ v =
      c.u ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)) :
    v = (c.closedPieceDiagram sq w₂).pushforwardCoeff := by
  have hz := c.isZero_upperStar_lowerShriek_upperStar_openImmersionLowerShriek sq w₂
    (opensOverι U) hUi.disjoint ((boundedConstructibleUpperStar _ ℓ (opensOverι U)).obj K)
  have hz' : IsZero ((boundedConstructibleUpperStar _ ℓ i).obj
      ((boundedConstructibleLowerShriek ℓ c.c₁).obj ((shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
          (openPiece K U))))) :=
    ((shiftFunctor _ (1 : ℤ)).map_isZero hz).of_iso
      ((boundedConstructibleUpperStar _ ℓ i).mapIso
          (((boundedConstructibleLowerShriek ℓ c.c₁).commShiftIso (1 : ℤ)).app _) ≪≫
        ((boundedConstructibleUpperStar _ ℓ i).commShiftIso (1 : ℤ)).app _)
  have key : ∀ g : (shiftFunctor _ (1 : ℤ)).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
        (openPiece K U)) ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)), g = 0 := by
    intro g
    rw [← ((boundedConstructibleUpperShriekAdjunction ℓ c.c₁).homEquiv _ _).apply_symm_apply g,
      eq_zero_of_isZero_upperStar i hz'
        (((boundedConstructibleUpperShriekAdjunction ℓ c.c₁).homEquiv _ _).symm g),
      Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  rw [← sub_eq_zero]
  obtain ⟨δ, hT⟩ := exists_distTriang_openImmersionLowerShriek_lowerStar (opensOverι U) i hUi K
  have hT' :=
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map_distinguished _ hT
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₃ _ hT'
    (v - (c.closedPieceDiagram sq w₂).pushforwardCoeff)
    ((Preadditive.comp_sub _ _ _).trans
      (sub_eq_zero.2 (hv.trans (c.upperStar_map_unit_comp_closedPieceCoeff sq w₂).symm)))
  refine hg.trans ?_
  have hg0 := key g
  simp only [hg0, comp_zero]

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
