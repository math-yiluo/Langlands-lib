/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineDiagonalGysin

/-!
# The second integral of the diagonal Gysin map

For `q : P = ℙ¹_S ⟶ S` and `W = ℙ¹_P = P ×_S P` with projections `a = W ↘ P` and `b = map q`,
the exchange of the factors `σ : W ⟶ W` (`AlgebraicGeometry.ProjectiveSpace.diagonalSwap`)
satisfies `σ ≫ a = b` and `σ ≫ b = a`. Transporting along `σ`, the trace along `b` of the kernel
adjunction (`CategoryTheory.Adjunction.kernelTraceA` for `e.symm`) becomes the trace along `a`
(`AlgebraicGeometry.Etale.homEquiv_comp_inv_kernelBaseChange_projectiveLineKernelSquareIso_symm`),
and the cycle class `δ` of the diagonal becomes `σ^* δ`. We deduce the second integral
hypothesis of `AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class` for the Gysin
map `AlgebraicGeometry.Etale.projectiveLineDiagonalGysin` from
`AlgebraicGeometry.Etale.projectiveLineTrace_diagonal_swap`
(`AlgebraicGeometry.Etale.projectiveLineDiagonalGysin_integral_snd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- The context of `ProjectiveLineKernelAssembly`,
-- so that the statements below are syntactically those of
-- `AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class`.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

attribute [local instance] leftDerivedUpperStarMonoidal _root_.DerivedCategory.braidedCategory'

section ProjectiveLine

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S]

set_option hygiene false in
/-- The projective line `P = ℙ¹_S`. -/
local notation "𝐏" => ℙ(Option (ULift.{u} (Fin 1)); S)

set_option hygiene false in
/-- The projective line `W = ℙ¹_P = P ×_S P` over `P = ℙ¹_S`. -/
local notation "𝐖" => ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S))

set_option hygiene false in
/-- The second projection `b = map q : W ⟶ P`. -/
local notation "𝐛" => ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) (𝐏 ↘ S)

set_option hygiene false in
/-- The diagonal `Δ : P ⟶ W`. -/
local notation "𝐝" => ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S

set_option hygiene false in
/-- The exchange of the factors `σ : W ⟶ W`. -/
local notation "𝐬" => ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S

set_option hygiene false in
/-- The object `τ = Λ_S(1)[2]`. -/
local notation "𝛕" => (tateObject Λ S 1)⟦(2 : ℤ)⟧

set_option hygiene false in
/-- The trace `Rq_* Lq^* τ ≅ Rq_* Λ_P(1)[2] ⟶ Λ_S` of the projective line, for `τ = Λ_S(1)[2]`. -/
local notation "𝐭" =>
  ((R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
    projectiveLineTrace Λ S :
      (R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
        ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕) ⟶ 𝟙_ _)

omit [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ S] in
/-- **Transport of `e` along the exchange of the factors.** Through `La^* ≅ Lσ^* Lb^*` and
`Lσ^* La^* ≅ Lb^*`, the pullback along `σ` of the inverse `Lq^* ⋙ Lb^* ≅ Lq^* ⋙ La^*` of `e` is
`e : Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_map_projectiveLineKernelSquareIso_inv_app
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 𝐛 (𝐖 ↘ 𝐏)
        (ProjectiveSpace.diagonalSwap_map _ S).symm).hom.app
        ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (L((𝐬)^*[ModuleCat.{u + 1} Λ])).map ((projectiveLineKernelSquareIso Λ S).inv.app K) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 (𝐖 ↘ 𝐏) 𝐛
        (ProjectiveSpace.diagonalSwap_over _ S).symm).inv.app
        ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K) =
      (projectiveLineKernelSquareIso Λ S).hom.app K := by
  have h₁ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} Λ) 𝐬 𝐛 (𝐏 ↘ S) (𝐖 ↘ 𝐏)
    (𝐛 ≫ (𝐏 ↘ S)) (𝐛 ≫ (𝐏 ↘ S)) (ProjectiveSpace.diagonalSwap_map _ S).symm rfl
    (ProjectiveSpace.isPullback_map _ (𝐏 ↘ S)).w K
  have h₂ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} Λ) 𝐬 (𝐖 ↘ 𝐏) (𝐏 ↘ S) 𝐛
    (𝐛 ≫ (𝐏 ↘ S)) (𝐛 ≫ (𝐏 ↘ S)) (ProjectiveSpace.diagonalSwap_over _ S).symm
    (ProjectiveSpace.isPullback_map _ (𝐏 ↘ S)).w rfl K
  rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏) (𝐏 ↘ S)
    (𝐛 ≫ (𝐏 ↘ S)) (ProjectiveSpace.isPullback_map _ (𝐏 ↘ S)).w).hom.app K), ← reassoc_of% h₁]
  simp only [projectiveLineKernelSquareIso, leftDerivedUpperStarCompSquareIso, Iso.trans_inv,
    Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% h₂, Iso.hom_inv_id_app, Category.comp_id]

omit [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ S] in
/-- **The trace along `b` is the trace along `a`, transported along `σ`.** For
`x : Lb^* Λ_P ⟶ La^* M`, the adjoint `Λ_P ⟶ Rb_* La^* M` of `x` followed by the inverse of the
base change map `Lq^* Rq_* M ⟶ Rb_* La^* M` is the adjoint `Λ_P ⟶ Ra_* Lb^* M` of
`La^* Λ_P ≅ Lσ^* Lb^* Λ_P ⟶ Lσ^* La^* M ≅ Lb^* M` followed by the inverse of the base change map
`Lq^* Rq_* M ⟶ Ra_* Lb^* M`. -/
theorem homEquiv_comp_inv_kernelBaseChange_projectiveLineKernelSquareIso_symm
    (M : _root_.DerivedCategory (Sheaf 𝐏.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (x : (L((𝐛)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⟶
      (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).obj M) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛).homEquiv _ _ x ≫
        inv (Adjunction.kernelBaseChange
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛)
          (projectiveLineKernelSquareIso Λ S).symm M) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏)).homEquiv _ _
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 𝐛 (𝐖 ↘ 𝐏)
              (ProjectiveSpace.diagonalSwap_map _ S).symm).hom.app (𝟙_ _) ≫
            (L((𝐬)^*[ModuleCat.{u + 1} Λ])).map x ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 (𝐖 ↘ 𝐏) 𝐛
              (ProjectiveSpace.diagonalSwap_over _ S).symm).inv.app M) ≫
        inv (Adjunction.kernelBaseChange
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏))
          (projectiveLineKernelSquareIso Λ S) M) := by
  have hx : (L((𝐛)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛).homEquiv _ _ x ≫
          inv (Adjunction.kernelBaseChange
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛)
            (projectiveLineKernelSquareIso Λ S).symm M)) ≫
        (projectiveLineKernelSquareIso Λ S).inv.app
          ((R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).obj M) ≫
        (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S)).counit.app M) =
        x := by
    rw [← Iso.symm_hom, ← Adjunction.map_kernelBaseChange_counit, ← Functor.map_comp_assoc,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (Adjunction.homEquiv_counit _ _ _ _).symm.trans
      ((Adjunction.homEquiv _ _ _).symm_apply_apply x)
  generalize (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛).homEquiv _ _ x ≫
    inv (Adjunction.kernelBaseChange
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛)
      (projectiveLineKernelSquareIso Λ S).symm M) = y at hx ⊢
  subst hx
  rw [IsIso.eq_comp_inv]
  apply (Adjunction.homEquiv _ _ _).symm.injective
  rw [Equiv.symm_apply_apply,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.map_kernelBaseChange_counit]
  have hy := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 𝐛 (𝐖 ↘ 𝐏)
    (ProjectiveSpace.diagonalSwap_map _ S).symm).hom.naturality y
  have hε := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 (𝐖 ↘ 𝐏) 𝐛
    (ProjectiveSpace.diagonalSwap_over _ S).symm).inv.naturality
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S)).counit.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hy hε
  simp only [Functor.map_comp, Category.assoc]
  simp only [hε, ← reassoc_of% hy,
    leftDerivedUpperStarComp_hom_app_map_projectiveLineKernelSquareIso_inv_app_assoc]


omit [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ S] in
/-- The form with units of
`AlgebraicGeometry.Etale.homEquiv_comp_inv_kernelBaseChange_projectiveLineKernelSquareIso_symm`:
`Λ_P ⟶ Rb_* Lb^* Λ_P ⟶ Rb_* La^* M ≅ Lq^* Rq_* M` is
`Λ_P ⟶ Ra_* La^* Λ_P ⟶ Ra_* Lb^* M ≅ Lq^* Rq_* M`, for the transport of `x` along `σ`. -/
@[reassoc]
theorem unit_app_comp_map_comp_inv_kernelBaseChange_projectiveLineKernelSquareIso_symm
    (M : _root_.DerivedCategory (Sheaf 𝐏.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (x : (L((𝐛)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⟶
      (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).obj M) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛).unit.app (𝟙_ _) ≫
      (R((𝐛)_*[ModuleCat.{u + 1} Λ])).map x ≫
        inv (Adjunction.kernelBaseChange
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛)
          (projectiveLineKernelSquareIso Λ S).symm M) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏)).unit.app (𝟙_ _) ≫
        (R(((𝐖 ↘ 𝐏))_*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 𝐛 (𝐖 ↘ 𝐏)
              (ProjectiveSpace.diagonalSwap_map _ S).symm).hom.app (𝟙_ _) ≫
            (L((𝐬)^*[ModuleCat.{u + 1} Λ])).map x ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 (𝐖 ↘ 𝐏) 𝐛
              (ProjectiveSpace.diagonalSwap_over _ S).symm).inv.app M) ≫
        inv (Adjunction.kernelBaseChange
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏))
          (projectiveLineKernelSquareIso Λ S) M) := by
  have h := homEquiv_comp_inv_kernelBaseChange_projectiveLineKernelSquareIso_symm Λ S M x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc, Category.assoc] at h
  exact h

/-- The transport along `σ` of the cycle class `Λ_W ⟶ Λ_W(1)[2] ≅ La^* Lq^* τ` of the diagonal,
read through `La^* Λ_P ≅ Lσ^* Lb^* Λ_P`, `Lσ^* La^* ≅ Lb^*` and `Lb^* Lq^* τ ≅ Λ_W(1)[2]`, is the
pullback `σ^* δ` of the cycle class `δ` of the diagonal. -/
lemma leftDerivedUpperStarComp_hom_app_map_cartierKummerCycleClass_diagonalSwap :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 𝐛 (𝐖 ↘ 𝐏)
        (ProjectiveSpace.diagonalSwap_map _ S).symm).hom.app (𝟙_ _) ≫
      (L((𝐬)^*[ModuleCat.{u + 1} Λ])).map (η (L((𝐛)^*[ModuleCat.{u + 1} Λ])) ≫
        cartierKummerCycleClass Λ 𝐝 (supportedTatePure_projectiveSpaceDiagonal_line Λ S) ≫
          (projectiveLineDiagonalTateIso Λ S).hom) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 (𝐖 ↘ 𝐏) 𝐛
        (ProjectiveSpace.diagonalSwap_over _ S).symm).inv.app
          ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕) ≫
      (L((𝐛)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
        (leftDerivedUpperStarTateTwoIso Λ 𝐛).hom =
      (leftDerivedUpperStarConstantComplexIso Λ (𝐖 ↘ 𝐏)).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ 𝐬).inv ≫
        (L((𝐬)^*[ModuleCat.{u + 1} Λ])).map
          (cartierKummerCycleClass Λ 𝐝 (supportedTatePure_projectiveSpaceDiagonal_line Λ S)) ≫
        (leftDerivedUpperStarTateTwoIso Λ 𝐬).hom := by
  have hc := congrArg Iso.hom (leftDerivedUpperStarConstantComplexIso_comp Λ 𝐬 𝐛 (𝐖 ↘ 𝐏)
    (ProjectiveSpace.diagonalSwap_map _ S).symm)
  have ht := congrArg Iso.hom (leftDerivedUpperStarTateTwoIso_comp (Λ := Λ) 𝐬 (𝐖 ↘ 𝐏) 𝐛
    (ProjectiveSpace.diagonalSwap_over _ S).symm)
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) 𝐬 (𝐖 ↘ 𝐏) 𝐛
    (ProjectiveSpace.diagonalSwap_over _ S).symm).inv.naturality
      (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hc ht
  simp only [Functor.comp_map] at hn
  have hT : (projectiveLineDiagonalTateIso Λ S).hom ≫
      (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
        (leftDerivedUpperStarTateTwoIso Λ (𝐖 ↘ 𝐏)).hom = 𝟙 _ := by
    simp [projectiveLineDiagonalTateIso]
  rw [hc, ← ht, ← leftDerivedUpperStarConstantComplexIso_hom_eq_η]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← reassoc_of% hn, Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Category.assoc, hT, Category.comp_id]
  rfl

/-- **The second integral of the diagonal Gysin map**, the hypothesis `hintB` of
`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class` for
`c = AlgebraicGeometry.Etale.projectiveLineDiagonalGysin`: the composite
`Λ_P ⟶ Rb_* Lb^* Λ_P ⟶ Rb_* Λ_W ⟶ Rb_* La^* Lq^* τ ⟶ Λ_P` of the cycle class of the diagonal
and the trace of `b` is the identity. Transported along the exchange of the factors `σ`, it is
`AlgebraicGeometry.Etale.projectiveLineTrace_diagonal_swap`. -/
theorem projectiveLineDiagonalGysin_integral_snd :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛).unit.app (𝟙_ _) ≫
      (R((𝐛)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐛)^*[ModuleCat.{u + 1} Λ])) ≫
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝).unit.app (𝟙_ _) ≫
          (R((𝐝)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐝)^*[ModuleCat.{u + 1} Λ]))) ≫
            projectiveLineDiagonalGysin Λ S)) ≫
      Adjunction.kernelTraceA (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛)
        (projectiveLineKernelSquareIso Λ S).symm _ 𝐭 = 𝟙 _ := by
  have hA := kernelTraceA_projectiveLineKernelSquareIso Λ S
  rw [Adjunction.kernelTraceA] at hA
  have hB := projectiveLineTrace_diagonal_swap Λ S
    (supportedTatePure_projectiveSpaceDiagonal_line Λ S)
  rw [Adjunction.homEquiv_unit, Category.assoc] at hB
  rw [unit_app_comp_map_η_comp_projectiveLineDiagonalGysin, Adjunction.kernelTraceA,
    unit_app_comp_map_comp_inv_kernelBaseChange_projectiveLineKernelSquareIso_symm_assoc, hA,
    ← Functor.map_comp_assoc]
  simp only [Category.assoc,
    leftDerivedUpperStarComp_hom_app_map_cartierKummerCycleClass_diagonalSwap]
  exact hB

end ProjectiveLine

end Etale

end AlgebraicGeometry
