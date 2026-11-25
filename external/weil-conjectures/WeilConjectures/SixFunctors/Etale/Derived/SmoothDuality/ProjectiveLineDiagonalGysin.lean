/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineDiagonalPurity
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineKernelAssembly
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# The Gysin map of the diagonal of the projective line

For `q : P = ℙ¹_S ⟶ S`, `W = ℙ¹_P = P ×_S P` with projections `a = W ↘ P`, `b = map q` and the
diagonal `Δ : P ⟶ W`, we construct the class `c : RΔ_* Λ_P ⟶ La^* Lq^* τ` (`τ = Λ_S(1)[2]`)
of `AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class`: the Gysin map of `Δ`

`RΔ_* Λ_P ≅ RΔ_! Λ_P ⟶ RΔ_! RΔ^! Λ_W(1)[2] ⟶ Λ_W(1)[2] ≅ La^* Lq^* τ`

given by the adjoint of the class with supports `AlgebraicGeometry.Etale.cartierKummerClass` of
the Cartier divisor `Δ` (purity holds by
`AlgebraicGeometry.Etale.supportedTatePure_projectiveSpaceDiagonal_line`). Its cycle class
`Λ_W ⟶ RΔ_* Λ_P ⟶ La^* Lq^* τ` is the cycle class
`AlgebraicGeometry.Etale.cartierKummerCycleClass` of the diagonal
(`AlgebraicGeometry.Etale.unit_app_comp_map_η_comp_projectiveLineDiagonalGysin`).

We then identify the trace `AlgebraicGeometry.Etale.projectiveLineKernelTrace` used by the
kernel adjunction along `a` with the trace of the projective line `W = ℙ¹_P ⟶ P`, by the base
change of the trace (`AlgebraicGeometry.Etale.projectiveLineTrace_baseChange`), and deduce the
first integral hypothesis of `AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class`
from `AlgebraicGeometry.Etale.projectiveLineTrace_diagonal`
(`AlgebraicGeometry.Etale.projectiveLineDiagonalGysin_integral_fst`).
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

section General

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The identification `Lf^* Λ_Y ≅ Λ_X` of the constant complexes is the unit comparison `η` of
the monoidal structure `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`. -/
lemma leftDerivedUpperStarConstantComplexIso_hom_eq_η {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftDerivedUpperStarConstantComplexIso Λ f).hom = η (L((f)^*[ModuleCat.{u + 1} Λ])) :=
  rfl

end General

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
/-- The object `τ = Λ_S(1)[2]`. -/
local notation "𝛕" => (tateObject Λ S 1)⟦(2 : ℤ)⟧

set_option hygiene false in
/-- The trace `Rq_* Lq^* τ ≅ Rq_* Λ_P(1)[2] ⟶ Λ_S` of the projective line, for `τ = Λ_S(1)[2]`. -/
local notation "𝐭" =>
  ((R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
    projectiveLineTrace Λ S :
      (R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
        ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕) ⟶ 𝟙_ _)

/-- The identification `Λ_W(1)[2] ≅ La^* Lq^* (Λ_S(1)[2])`. -/
noncomputable def projectiveLineDiagonalTateIso :
    (tateObject Λ 𝐖 1)⟦(2 : ℤ)⟧ ≅
      (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).obj ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕) :=
  ((L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)) ≪≫
    leftDerivedUpperStarTateTwoIso Λ (𝐖 ↘ 𝐏)).symm

/-- The auxiliary Gysin map of the diagonal `RΔ_* Λ_P ⟶ La^* Lq^* τ`: the adjoint
`LΔ^* Λ_W ⟶ RΔ^! Λ_W(1)[2]` of the class with supports of the diagonal
(`AlgebraicGeometry.Etale.cartierKummerClass`, read on `RΔ_! ≅ RΔ_*`), followed by
`RΔ_* RΔ^! ≅ RΔ_! RΔ^! ⟶ 𝟭` and `Λ_W(1)[2] ≅ La^* Lq^* τ`. Its cycle class is the
forgotten-supports Kummer class `AlgebraicGeometry.Etale.cartierKummerCycleClassAux` of the
diagonal; the Gysin map of the notes is its negative `projectiveLineDiagonalGysin`. -/
@[irreducible]
noncomputable def projectiveLineDiagonalGysinAux :
    (R((𝐝)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⟶
      (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).obj ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕) :=
  (R((𝐝)_*[ModuleCat.{u + 1} Λ])).map (inv (η (L((𝐝)^*[ModuleCat.{u + 1} Λ]))) ≫
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝).homEquiv _ _).symm
        (cartierKummerClass Λ 𝐝 (supportedTatePure_projectiveSpaceDiagonal_line Λ S) ≫
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) 𝐝).hom.app _)) ≫
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) 𝐝).inv.app _ ≫
      (rightDerivedUpperShriekAdjunction Λ 𝐝).counit.app _ ≫
        (projectiveLineDiagonalTateIso Λ S).hom

/-- **The Gysin map of the diagonal** `c : RΔ_* Λ_P ⟶ La^* Lq^* τ` with the sign of the notes:
the negative of `projectiveLineDiagonalGysinAux`, so that its cycle class is the cycle class
`δ = c₁(𝒪(Δ))` of the diagonal (`AlgebraicGeometry.Etale.cartierKummerCycleClass`,
`unit_app_comp_map_η_comp_projectiveLineDiagonalGysin`). -/
noncomputable def projectiveLineDiagonalGysin :
    (R((𝐝)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⟶
      (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).obj ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕) :=
  -projectiveLineDiagonalGysinAux Λ S

/-- The cycle class `Λ_W ⟶ RΔ_* LΔ^* Λ_W ≅ RΔ_* Λ_P ⟶ La^* Lq^* τ` of the auxiliary Gysin map of
the diagonal is the forgotten-supports Kummer class
`AlgebraicGeometry.Etale.cartierKummerCycleClassAux` of the diagonal. -/
theorem unit_app_comp_map_η_comp_projectiveLineDiagonalGysinAux :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝).unit.app (𝟙_ _) ≫
      (R((𝐝)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐝)^*[ModuleCat.{u + 1} Λ]))) ≫
        projectiveLineDiagonalGysinAux Λ S =
      cartierKummerCycleClassAux Λ 𝐝 (supportedTatePure_projectiveSpaceDiagonal_line Λ S) ≫
        (projectiveLineDiagonalTateIso Λ S).hom := by
  rw [projectiveLineDiagonalGysinAux, ← Functor.map_comp_assoc, IsIso.hom_inv_id_assoc,
    ← Category.assoc]
  erw [← Adjunction.homEquiv_unit]
  erw [Equiv.apply_symm_apply]
  rw [Category.assoc, Iso.hom_inv_id_app_assoc, cartierKummerCycleClassAux, Category.assoc]
  rfl

/-- The cycle class `Λ_W ⟶ RΔ_* LΔ^* Λ_W ≅ RΔ_* Λ_P ⟶ La^* Lq^* τ` of the Gysin map of the
diagonal is the cycle class `AlgebraicGeometry.Etale.cartierKummerCycleClass` of the diagonal:
the auxiliary statement, both sides negated. -/
theorem unit_app_comp_map_η_comp_projectiveLineDiagonalGysin :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝).unit.app (𝟙_ _) ≫
      (R((𝐝)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐝)^*[ModuleCat.{u + 1} Λ]))) ≫
        projectiveLineDiagonalGysin Λ S =
      cartierKummerCycleClass Λ 𝐝 (supportedTatePure_projectiveSpaceDiagonal_line Λ S) ≫
        (projectiveLineDiagonalTateIso Λ S).hom := by
  simp only [projectiveLineDiagonalGysin, cartierKummerCycleClass, Preadditive.comp_neg,
    Preadditive.neg_comp, unit_app_comp_map_η_comp_projectiveLineDiagonalGysinAux]

omit [Finite Λ] [HasKummerClass.IsNormalized Λ] in
/-- The isomorphism `e : Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` is compatible with the identifications
`La^* Lq^* τ ≅ Λ_W(1)[2] ≅ Lb^* Lq^* τ`. -/
@[reassoc]
lemma projectiveLineDiagonalTateIso_hom_comp_projectiveLineKernelSquareIso_hom_app :
    (projectiveLineDiagonalTateIso Λ S).hom ≫ (projectiveLineKernelSquareIso Λ S).hom.app 𝛕 ≫
      (L((𝐛)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
        (leftDerivedUpperStarTateTwoIso Λ 𝐛).hom = 𝟙 _ := by
  have hb := congrArg Iso.hom (leftDerivedUpperStarTateTwoIso_comp (Λ := Λ) 𝐛 (𝐏 ↘ S)
    (𝐛 ≫ (𝐏 ↘ S)) rfl)
  have ha := congrArg Iso.hom (leftDerivedUpperStarTateTwoIso_comp (Λ := Λ) (𝐖 ↘ 𝐏) (𝐏 ↘ S)
    (𝐛 ≫ (𝐏 ↘ S)) (ProjectiveSpace.isPullback_map _ (𝐏 ↘ S)).w)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at ha hb
  simp only [projectiveLineDiagonalTateIso, projectiveLineKernelSquareIso,
    leftDerivedUpperStarCompSquareIso, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv,
    Iso.trans_hom, NatTrans.comp_app, Category.assoc, hb, ← ha,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

omit [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ S] in
/-- The base change map of `e : Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` is the proper base change map of the
cartesian square `b ≫ q = a ≫ q`. -/
lemma kernelBaseChange_projectiveLineKernelSquareIso
    (M : _root_.DerivedCategory (Sheaf 𝐏.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Adjunction.kernelBaseChange
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏))
        (projectiveLineKernelSquareIso Λ S) M =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) (𝐏 ↘ S)).toCommSq).app M := by
  rw [Adjunction.kernelBaseChange_eq_mateEquiv_app]
  rfl

/-- **The trace along `a`.** The trace `Ra_* Lb^* Lq^* τ ⟶ Λ_P` of the kernel adjunction
(`CategoryTheory.Adjunction.kernelTraceA`, obtained from the trace of `q` by base change) is the
trace of the projective line `a : W = ℙ¹_P ⟶ P`, through `Lb^* Lq^* τ ≅ Λ_W(1)[2]`. -/
theorem kernelTraceA_projectiveLineKernelSquareIso :
    Adjunction.kernelTraceA (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏))
        (projectiveLineKernelSquareIso Λ S) _ 𝐭 =
      (R(((𝐖 ↘ 𝐏))_*[ModuleCat.{u + 1} Λ])).map
          ((L((𝐛)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
            (leftDerivedUpperStarTateTwoIso Λ 𝐛).hom) ≫
        projectiveLineTrace Λ 𝐏 := by
  have hn := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) (𝐏 ↘ S)).toCommSq).naturality
      (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom
  simp only [Functor.comp_map] at hn
  rw [Adjunction.kernelTraceA, IsIso.inv_comp_eq, kernelBaseChange_projectiveLineKernelSquareIso,
    Functor.map_comp, projectiveLineTrace_baseChange Λ (𝐏 ↘ S),
    ← leftDerivedUpperStarConstantComplexIso_hom_eq_η]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
  rw [reassoc_of% hn]

/-- **The first integral of the diagonal Gysin map**, the hypothesis `hintA` of
`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class` for
`c = AlgebraicGeometry.Etale.projectiveLineDiagonalGysin`: the composite
`Λ_P ⟶ Ra_* La^* Λ_P ⟶ Ra_* Λ_W ⟶ Ra_* La^* Lq^* τ ≅ Ra_* Lb^* Lq^* τ ⟶ Λ_P` of the cycle
class of the diagonal and the trace of `a` is the identity
(`AlgebraicGeometry.Etale.projectiveLineTrace_diagonal`). -/
theorem projectiveLineDiagonalGysin_integral_fst :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏)).unit.app (𝟙_ _) ≫
      (R(((𝐖 ↘ 𝐏))_*[ModuleCat.{u + 1} Λ])).map (η (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])) ≫
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝).unit.app (𝟙_ _) ≫
          (R((𝐝)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐝)^*[ModuleCat.{u + 1} Λ]))) ≫
            projectiveLineDiagonalGysin Λ S) ≫
        (projectiveLineKernelSquareIso Λ S).hom.app 𝛕) ≫
      Adjunction.kernelTraceA (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏))
        (projectiveLineKernelSquareIso Λ S) _ 𝐭 = 𝟙 _ := by
  rw [unit_app_comp_map_η_comp_projectiveLineDiagonalGysin,
    kernelTraceA_projectiveLineKernelSquareIso, ← Functor.map_comp_assoc]
  simp only [Category.assoc,
    projectiveLineDiagonalTateIso_hom_comp_projectiveLineKernelSquareIso_hom_app, Category.comp_id]
  rw [← leftDerivedUpperStarConstantComplexIso_hom_eq_η]
  refine Eq.trans ?_
    (projectiveLineTrace_diagonal Λ S (supportedTatePure_projectiveSpaceDiagonal_line Λ S))
  rw [Adjunction.homEquiv_unit, Category.assoc]
  rfl

end ProjectiveLine

end Etale

end AlgebraicGeometry
