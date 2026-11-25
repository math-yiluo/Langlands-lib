/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.TraceFormula.TraceClass

/-!

# Vanishing of the corner terms of an open–closed decomposition

Let `j : U ⟶ X` be an open immersion and `x` a rational point of `X` not in the image of `j`.
For `B` on `U` and `A` on the point, the open and closed pieces `K' = j_! B` and `K'' = Rx_* A`
(for instance `K' = j_! Lj^* K` and `K'' = Rx_* Lx^* K`) have disjoint supports. This file proves
the vanishing of the morphism groups on `X ⨯ X` used by the additivity of trace classes along the
open–closed triangle `K' ⟶ K ⟶ K'' ⟶` (blueprint `proposition-additivity-trace-classes--2`,
`proposition-additivity-trace-classes`):

* `K' ⊗ D_X K'' = 0`, so the corner `K' ⊠ D_X K''` (supported on `U ⨯ {x}`) has no morphism to
  `RΔ_* ω_X` in any degree (`ProEtale.CondensedRing.eq_zero_of_externalProduct_shift_to_diag`);
* there are no morphisms of degree `-1` to `K'' ⊠ D_X K'` (supported on `{x} ⨯ X` and built from
  `Rj_*`) from `K' ⊠ D_X K` and `K ⊠ D_X K''`
  (`ProEtale.CondensedRing.eq_zero_of_externalProduct_openPiece`,
  `ProEtale.CondensedRing.eq_zero_of_externalProduct_closedPiece`), nor from the class
  `R(𝟙, h)_! ℚ̄_ℓ` of the graph of an endomorphism `h` fixing `x`
  (`ProEtale.CondensedRing.eq_zero_of_lowerShriek_graph`).

The morphisms to `K'' ⊠ D_X K'` are computed through the Künneth–Verdier isomorphism
`K'' ⊠ D_X K' ≅ RHom(Lp₂^* K', Rp₁^! K'')`, the tensor–hom adjunction, the adjunction
`Rp₁_! ⊣ Rp₁^!` and `Lx^* ⊣ Rx_*`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Shifting a vanishing statement: no nonzero morphism `T ⟶ Z⟦-1⟧` if there is no nonzero
morphism `T⟦1⟧ ⟶ Z`. -/
lemma eq_zero_of_shift {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [HasShift 𝒞 ℤ]
    [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] {T Z : 𝒞}
    (h : ∀ ψ : T⟦(1 : ℤ)⟧ ⟶ Z, ψ = 0) (φ : T ⟶ Z⟦(-1 : ℤ)⟧) : φ = 0 := by
  apply (shiftFunctor 𝒞 (1 : ℤ)).map_injective
  rw [Functor.map_zero]
  have := h ((shiftFunctor 𝒞 (1 : ℤ)).map φ ≫ (shiftFunctorCompIsoId 𝒞 (-1 : ℤ) 1
    (neg_add_cancel 1)).hom.app Z)
  rwa [Preadditive.IsIso.comp_right_eq_zero] at this

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### Generalities -/

section General

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- No nonzero morphism `Y ⟶ L ⊠ D N` if there is no nonzero morphism `Rp₁_! (Lp₂^* N ⊗ Y) ⟶ L`:
the Künneth–Verdier isomorphism `L ⊠ D N ≅ RHom(Lp₂^* N, Rp₁^! L)`, the tensor–hom adjunction and
the adjunction `Rp₁_! ⊣ Rp₁^!`. -/
lemma eq_zero_of_externalProduct {T : Dᵇc((Y ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (h : ∀ ψ : (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj N ⊗ T) ⟶ L, ψ = 0)
    (φ : T ⟶ externalProduct ℓ L (verdierDual ℓ N)) : φ = 0 := by
  let e : (T ⟶ (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj N)).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) ≃
      ((boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj N ⊗ T) ⟶ L) :=
    ((ihom.adjunction _).homEquiv _ _).symm.trans
      ((boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : Y ⨯ X ⟶ Y)).homEquiv _ _).symm
  have key : φ ≫ kunnethVerdierMap ℓ L N = 0 := e.injective ((h _).trans (h _).symm)
  rwa [← cancel_mono (kunnethVerdierMap ℓ L N), zero_comp]

/-- No nonzero morphism `M ⟶ Rx_* A` if `Lx^* M = 0`. -/
lemma eq_zero_of_isZero_upperStar {P : Over (Spec (.of k))} [LocallyOfFiniteType P.hom]
    [QuasiCompact P.hom] [IsSeparated P.hom] (x : P ⟶ Y)
    {M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (hM : IsZero ((boundedConstructibleUpperStar _ ℓ x).obj M))
    {A : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : M ⟶ (boundedConstructibleLowerStar ℓ x).obj A) : ψ = 0 := by
  apply ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).homEquiv _ _).symm.injective
  exact hM.eq_of_src _ _

/-- `Lx^* Rp₁_! (W ⊗ Lp₁^* M) = 0` if `Lx^* M = 0`: the projection formula for `p₁` and the
monoidality of `Lx^*`. -/
lemma isZero_upperStar_lowerShriek_tensor {P : Over (Spec (.of k))} [LocallyOfFiniteType P.hom]
    [QuasiCompact P.hom] [IsSeparated P.hom] (x : P ⟶ Y)
    (W : Dᵇc((Y ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (hM : IsZero ((boundedConstructibleUpperStar _ ℓ x).obj M)) :
    IsZero ((boundedConstructibleUpperStar _ ℓ x).obj
      ((boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj
        (W ⊗ (boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj M))) :=
  (isZero_tensorObj_of_isZero_right _ hM).of_iso
    ((boundedConstructibleUpperStar _ ℓ x).mapIso
        (asIso (boundedConstructibleExceptionalProjectionMorphism ℓ
          (prod.fst : Y ⨯ X ⟶ Y) W M)).symm ≪≫
      (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ x) _ _).symm)

/-- Shifting the source of `Lx^* Rp₁_! (Lp₂^* N ⊗ -)` preserves vanishing. -/
lemma isZero_upperStar_lowerShriek_tensor_shift {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] (x : P ⟶ Y)
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {T : Dᵇc((Y ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (h : IsZero ((boundedConstructibleUpperStar _ ℓ x).obj
      ((boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj N ⊗ T)))) :
    IsZero ((boundedConstructibleUpperStar _ ℓ x).obj
      ((boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj N ⊗ T⟦(1 : ℤ)⟧))) :=
  ((shiftFunctor _ (1 : ℤ)).map_isZero h).of_iso
    ((boundedConstructibleUpperStar _ ℓ x).mapIso
        ((boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).mapIso
          ((((curriedTensor _).obj ((boundedConstructibleUpperStar _ ℓ
            (prod.snd : Y ⨯ X ⟶ X)).obj N)).commShiftIso (1 : ℤ)).app T) ≪≫
          ((boundedConstructibleLowerShriek ℓ
            (prod.fst : Y ⨯ X ⟶ Y)).commShiftIso
            (1 : ℤ)).app _) ≪≫
      ((boundedConstructibleUpperStar _ ℓ x).commShiftIso (1 : ℤ)).app _)

end General

/-! ### The pieces of a point and its complement -/

section Pieces

variable {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] (j : U ⟶ X) [IsOpenImmersion j.left] (x : RationalPoint X)
  (hjx : Disjoint (Set.range j.left.base) (Set.range x.left.base))
  (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (A : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)

include hjx

/-- The restriction to `U` of the dual of the closed piece vanishes: `Lj^* D_X (Rx_* A) = 0`. -/
lemma isZero_upperStar_verdierDual_lowerStar :
    IsZero ((boundedConstructibleUpperStar _ ℓ j).obj
      (verdierDual ℓ ((boundedConstructibleLowerStar ℓ x).obj A))) := by
  have := isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion
    ℓ j ((boundedConstructibleLowerStar ℓ x).obj A)
  exact (isZero_ihom_obj_of_isZero
    (isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ j x hjx A) _).of_iso
    (asIso ((Functor.LaxMonoidal.ihomComparison (boundedConstructibleUpperStar _ ℓ j)
      ((boundedConstructibleLowerStar ℓ x).obj A)).app _))

/-- The tensor product of the open piece with the dual of the closed piece vanishes:
`j_! B ⊗ D_X (Rx_* A) = 0`, by the projection formula for `j_!` and
`isZero_upperStar_verdierDual_lowerStar`. -/
lemma isZero_openImmersionLowerShriek_tensor_verdierDual_lowerStar :
    IsZero ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B ⊗
      verdierDual ℓ ((boundedConstructibleLowerStar ℓ x).obj A)) := by
  have := NatIso.isIso_app_of_isIso (Functor.Monoidal.projectionMap
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (verdierDual ℓ ((boundedConstructibleLowerStar ℓ x).obj A))) B
  exact ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).map_isZero
    (isZero_tensorObj_of_isZero_left (isZero_upperStar_verdierDual_lowerStar j x hjx A) B)).of_iso
    ((β_ _ _) ≪≫ (asIso ((Functor.Monoidal.projectionMap
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j) _).app B)).symm)


/-- The corner `j_! B ⊠ D_X (Rx_* A)`, supported on `U ⨯ {x}`, has no morphism of any degree to
`RΔ_* ω_X`. -/
lemma eq_zero_of_externalProduct_shift_to_diag
    (φ : (externalProduct ℓ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B)
        (verdierDual ℓ ((boundedConstructibleLowerStar ℓ x).obj A))) ⟦(1 : ℤ)⟧ ⟶
      (boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X)) :
    φ = 0 :=
  eq_zero_of_isZero_upperStar (diag X) (((shiftFunctor _ (1 : ℤ)).map_isZero
    ((isZero_openImmersionLowerShriek_tensor_verdierDual_lowerStar j x hjx B A).of_iso
      (diagUpperStarExternalProductIso ℓ _ _))).of_iso
    (((boundedConstructibleUpperStar _ ℓ (diag X)).commShiftIso (1 : ℤ)).app _)) φ

/-- There is no morphism of degree `-1` from `j_! B ⊠ D_X K` to `Rx_* A ⊠ D_X (j_! B')`. -/
lemma eq_zero_of_externalProduct_openPiece (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B' : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ : externalProduct ℓ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B)
        (verdierDual ℓ K) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ x).obj A)
        (verdierDual ℓ
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B'))) ⟦(-1 : ℤ)⟧) :
    φ = 0 :=
  eq_zero_of_shift (fun _ ↦ eq_zero_of_externalProduct (fun _ ↦ eq_zero_of_isZero_upperStar x
    (isZero_upperStar_lowerShriek_tensor_shift x _
      ((isZero_upperStar_lowerShriek_tensor x _
        (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j x hjx B)).of_iso
        ((boundedConstructibleUpperStar _ ℓ x).mapIso
          ((boundedConstructibleLowerShriek ℓ _).mapIso
            (whiskerLeftIso _ (β_ _ _) ≪≫ (α_ _ _ _).symm))))) _) _) φ

/-- There is no morphism of degree `-1` from `K ⊠ D_X (Rx_* A)` to `Rx_* A' ⊠ D_X (j_! B)`. -/
lemma eq_zero_of_externalProduct_closedPiece (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (A' : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ : externalProduct ℓ K
        (verdierDual ℓ ((boundedConstructibleLowerStar ℓ x).obj A)) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ x).obj A')
        (verdierDual ℓ
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B))) ⟦(-1 : ℤ)⟧) :
    φ = 0 := by
  refine eq_zero_of_shift (fun _ ↦ eq_zero_of_externalProduct (fun _ ↦
    eq_zero_of_isZero_upperStar x (isZero_upperStar_lowerShriek_tensor_shift x _ ?_) _) _) φ
  exact (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map_isZero
    ((boundedConstructibleLowerShriek ℓ _).map_isZero
    ((isZero_tensorObj_of_isZero_right _ ((boundedConstructibleUpperStar _ ℓ _).map_isZero
      (isZero_openImmersionLowerShriek_tensor_verdierDual_lowerStar j x hjx B A))).of_iso
      ((α_ _ _ _).symm ≪≫ whiskerRightIso (β_ _ _) _ ≪≫ (α_ _ _ _) ≪≫
        whiskerLeftIso _ (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ _) _ _))))


omit hjx in
/-- There is no morphism of degree `-1` from the class `Rs_! ℚ̄_ℓ` of a support
`s : C ⟶ X ⨯ X` to `Rx_* A ⊠ D_X N` as soon as `Lx^* R(s ≫ p₁)_! L(s ≫ p₂)^* N = 0`. -/
lemma eq_zero_of_lowerShriek_unit {C : Over (Spec (.of k))} [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (s : C ⟶ X ⨯ X)
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hz : IsZero ((boundedConstructibleUpperStar _ ℓ x).obj
      ((boundedConstructibleLowerShriek ℓ (s ≫ prod.fst)).obj
        ((boundedConstructibleUpperStar _ ℓ (s ≫ prod.snd)).obj N))))
    (φ : (boundedConstructibleLowerShriek ℓ s).obj (𝟙_ _) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ x).obj A)
        (verdierDual ℓ N)) ⟦(-1 : ℤ)⟧) :
    φ = 0 :=
  eq_zero_of_shift (fun _ ↦ eq_zero_of_externalProduct (fun _ ↦ eq_zero_of_isZero_upperStar x
    (isZero_upperStar_lowerShriek_tensor_shift x N (hz.of_iso
      ((boundedConstructibleUpperStar _ ℓ x).mapIso
        ((boundedConstructibleLowerShriek ℓ _).mapIso
          ((β_ _ _) ≪≫ asIso (boundedConstructibleExceptionalProjectionMorphism ℓ s _ _) ≪≫
            (boundedConstructibleLowerShriek ℓ s).mapIso ((λ_ _) ≪≫
              ((boundedConstructibleUpperStarComp _ ℓ s prod.snd).app N).symm)) ≪≫
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst).app _).symm)))) _) _) φ

/-- There is no morphism of degree `-1` from the class `R(𝟙, h)_! ℚ̄_ℓ` of the graph of an
endomorphism `h` fixing `x` to `Rx_* A ⊠ D_X (j_! B)`. -/
lemma eq_zero_of_lowerShriek_graph (h : X ⟶ X) (hx : x ≫ h = x)
    (φ : (boundedConstructibleLowerShriek ℓ (prod.lift (𝟙 X) h)).obj (𝟙_ _) ⟶
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ x).obj A)
        (verdierDual ℓ
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj B))) ⟦(-1 : ℤ)⟧) :
    φ = 0 := by
  refine eq_zero_of_lowerShriek_unit x A _ _ ?_ φ
  rw [prod.lift_fst, prod.lift_snd]
  refine (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j x hjx
    B).of_iso ((boundedConstructibleUpperStar _ ℓ x).mapIso
      ((boundedConstructibleLowerShriekId ℓ X).app _) ≪≫ ?_)
  refine ((boundedConstructibleUpperStarComp _ ℓ x h).app _).symm ≪≫ eqToIso ?_
  rw [hx]

end Pieces

end AlgebraicGeometry.ProEtale.CondensedRing
