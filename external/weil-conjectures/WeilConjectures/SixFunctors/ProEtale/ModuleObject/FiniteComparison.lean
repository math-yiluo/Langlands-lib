/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Profinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstantPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Comparison of the two models of pro-étale sheaves with finite coefficients

Let `T` be a finite commutative ring with the discrete topology and `X` a scheme. There are two
models of pro-étale sheaves of `T`-modules on `X`:

1. module objects over the coefficient ring `Λ_X = p_X^* T̲`, the pullback from the point of
   the condensed ring `T̲ = C(-, T)`, in the category of abelian sheaves on `X_proét`
   (`WeilConjectures.SixFunctors.ProEtale.ModuleObject`);
2. sheaves of `T`-modules, `Sheaf (ProEt.topology X) (ModuleCat R)` for the ring
   `R = ULift T` in the universe of the pro-étale coefficients, as in
   `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient`.

This file proves that they are equivalent (`ProEtale.finiteCoefficientModEquivalence`),
compatibly with the underlying abelian sheaves. The proof has three steps.

* `T̲` is the constant condensed ring `T`: a continuous map from a profinite set to the finite
  discrete `T` is locally constant (`Profinite.constRingSheafToContinuousMapRingObj`).
* `p_X^* = π_X^* ∘ p^*` sends the constant ring sheaf `T` on the point to the constant ring sheaf
  `T_X`, as ring objects: both pullbacks send constant sheaves to constant sheaves monoidally,
  the continuous functors `S ↦ Spec LC(S, ℤ)` and `V ↦ V ×_{Spec ℤ} X` preserving the terminal
  objects (`CategoryTheory.constantSheafToPullback`). Hence an isomorphism of ring objects
  `T_X ≅ Λ_X` (`ProEtale.constRingSheafToCondensedRingObj`).
* Module objects over the constant ring sheaf `T_X` are the sheaves of `T`-modules
  (`CategoryTheory.Sheaf.modConstRingSheafEquivalence`).

## Main definitions

* `ProEtale.constRingSheafToCondensedRingObj`: the isomorphism of ring objects `T_X ≅ Λ_X`.
* `ProEtale.finiteCoefficientModEquivalence`: the equivalence
  `Mod_{Λ_X} ≌ Sheaf (ProEt.topology X) (ModuleCat (ULift T))`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The ring `LC(*, ℤ)` of locally constant functions on the point is `ℤ`. -/
def locallyConstantPUnitRingEquiv :
    LocallyConstant (Profinite.of PUnit.{u + 1}) ℤ ≃+* ULift.{u} ℤ where
  toFun f := ULift.up (f PUnit.unit)
  invFun n := LocallyConstant.const _ n.down
  left_inv _ := LocallyConstant.ext fun _ ↦ rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The point `Spec LC(*, ℤ)` is terminal, being isomorphic to `Spec ℤ`. -/
noncomputable def isTerminalProfiniteToSchemePUnit :
    IsTerminal (profiniteToScheme.obj (Profinite.of PUnit.{u + 1})) :=
  specULiftZIsTerminal.ofIso
    (Scheme.Spec.mapIso locallyConstantPUnitRingEquiv.toCommRingCatIso.op)

/-- The image `Spec LC(*, ℤ)` of the point in the pro-étale site of `Spec ℤ` is terminal. -/
noncomputable def isTerminalProfiniteToProEtPUnit :
    IsTerminal (profiniteToProEt.obj (Profinite.of PUnit.{u + 1})) :=
  have : IsIso (toSpecZ (profiniteToScheme.obj (Profinite.of PUnit.{u + 1}))) :=
    isIso_of_isTerminal isTerminalProfiniteToSchemePUnit specULiftZIsTerminal _
  (Scheme.ProEt.isTerminalMkId specZ).ofIso
    (MorphismProperty.Over.isoMk
      (asIso (toSpecZ (profiniteToScheme.obj (Profinite.of PUnit.{u + 1}))))
      (Category.comp_id _)).symm

/-- The adjunction `p^* ⊣ p_*` between condensed abelian groups and abelian sheaves on
`(Spec ℤ)_proét` is monoidal, for the strong monoidal structure of `p^*`. -/
instance isMonoidal_pointUpperStarLowerStarAdjunction :
    @Adjunction.IsMonoidal _ _ _ _ _ _ _ _ pointUpperStarLowerStarAdjunction.{u}
      Functor.Monoidal.toOplaxMonoidal _ := by
  let := pointUpperStarLowerStarAdjunction.{u}.leftAdjointOplaxMonoidal
  exact (inferInstance : pointUpperStarLowerStarAdjunction.{u}.IsMonoidal)

/-- The pullback `p^*` from the point sends constant sheaves to constant sheaves: the monoidal
isomorphism `c_{Spec ℤ} ≅ c_* ⋙ p^*` of `CategoryTheory.constantSheafToPullback`. -/
noncomputable def constantSheafToPointUpperStar :
    constantSheaf (Scheme.ProEt.topology specZ.{u}) Ab.{u + 1} ⟶
      constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ pointUpperStar :=
  constantSheafToPullback (Scheme.ProEt.isTerminalMkId specZ) isTerminalProfiniteToProEtPUnit
    pointUpperStarLowerStarAdjunction Profinite.isTerminalPUnit

instance : IsIso constantSheafToPointUpperStar.{u} := by
  dsimp only [constantSheafToPointUpperStar]
  infer_instance

instance : NatTrans.IsMonoidal constantSheafToPointUpperStar.{u} := by
  dsimp only [constantSheafToPointUpperStar]
  infer_instance

variable (X : Scheme.{u})

/-- The pullback `π_X^*` along `π_X : X ⟶ Spec ℤ` sends constant sheaves to constant sheaves:
the monoidal isomorphism `c_X ≅ c_{Spec ℤ} ⋙ π_X^*` of `CategoryTheory.constantSheafToPullback`. -/
noncomputable def constantSheafToUpperStarToSpecZ :
    constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⟶
      constantSheaf (Scheme.ProEt.topology specZ.{u}) Ab.{u + 1} ⋙ (toSpecZ X)^*[Ab.{u + 1}] :=
  have := Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  constantSheafToPullback (Scheme.ProEt.isTerminalMkId X)
    ((Scheme.ProEt.isTerminalMkId X).ofIso (overPullbackObjMkIdIso (toSpecZ X)).symm)
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)) (Scheme.ProEt.isTerminalMkId specZ)

instance : IsIso (constantSheafToUpperStarToSpecZ X) := by
  dsimp only [constantSheafToUpperStarToSpecZ]
  infer_instance

instance : NatTrans.IsMonoidal (constantSheafToUpperStarToSpecZ X) := by
  dsimp only [constantSheafToUpperStarToSpecZ]
  infer_instance

variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- For a finite discrete ring `T`, the comparison `T_X ⟶ Λ_X = p_X^* T̲` from the constant ring
sheaf `T` on `X_proét` to the pullback of the condensed ring `T̲ = C(-, T)`: the composite
```
T_X ≅ π_X^* T_{Spec ℤ} ≅ π_X^* p^* T_* ≅ π_X^* p^* T̲ = p_X^* T̲
```
of the comparisons `constantSheafToUpperStarToSpecZ`, `constantSheafToPointUpperStar` for
constant sheaves and the identification `T_* ≅ T̲` of
`Profinite.constRingSheafToContinuousMapRingObj`. -/
noncomputable def constRingSheafToCondensedRingObj :
    Sheaf.constRingSheaf (Scheme.ProEt.topology X) (ULift.{u + 1} T) ⟶
      condensedRingObj (Profinite.continuousMapRingObj T) X :=
  (constantSheafToUpperStarToSpecZ X).app (AddCommGrpCat.of (ULift.{u + 1} T)) ≫
    (toSpecZ X)^*[Ab.{u + 1}].map
      (constantSheafToPointUpperStar.app (AddCommGrpCat.of (ULift.{u + 1} T))) ≫
    (upperStarFromPoint X).map (Profinite.constRingSheafToContinuousMapRingObj T)

instance : IsIso (constRingSheafToCondensedRingObj X T) := by
  dsimp only [constRingSheafToCondensedRingObj]
  infer_instance

/-- The comparison `T_X ⟶ Λ_X` is a morphism of ring objects. -/
instance : IsMonHom (constRingSheafToCondensedRingObj X T) := by
  let R := AddCommGrpCat.of (ULift.{u + 1} T)
  let cX := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let cS := constantSheaf (Scheme.ProEt.topology specZ.{u}) Ab.{u + 1}
  let cP := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let π := (toSpecZ X)^*[Ab.{u + 1}]
  have hA : @IsMonHom _ _ _ _ _ (cX.monObjObj R) (π.monObjObj (cS.obj R))
      ((constantSheafToUpperStarToSpecZ X).app R) :=
    IsMonHom.of_eq _ rfl (Functor.monObjObj_comp cS π R)
      (hf := NatTrans.isMonHom_app (constantSheafToUpperStarToSpecZ X) R)
  have hB : @IsMonHom _ _ _ _ _ (cS.monObjObj R) (pointUpperStar.monObjObj (cP.obj R))
      (constantSheafToPointUpperStar.app R) :=
    IsMonHom.of_eq _ rfl (Functor.monObjObj_comp cP pointUpperStar R)
      (hf := NatTrans.isMonHom_app constantSheafToPointUpperStar R)
  have hκ : @IsMonHom _ _ _ _ _ (cP.monObjObj R) _
      (Profinite.constRingSheafToContinuousMapRingObj T) :=
    IsMonHom.of_eq _ (Functor.monObjObj_comp (Functor.const _) (presheafToSheaf _ _) R).symm rfl
  have hD : @IsMonHom _ _ _ _ _
      (π.monObjObj (pointUpperStar.obj (cP.obj R))) _
      ((upperStarFromPoint X).map (Profinite.constRingSheafToContinuousMapRingObj T)) :=
    IsMonHom.of_eq _ (Functor.monObjObj_comp pointUpperStar π (cP.obj R)) rfl
  have hC : @IsMonHom _ _ _ _ _ (π.monObjObj (cS.obj R))
      (π.monObjObj (pointUpperStar.obj (cP.obj R))) (π.map (constantSheafToPointUpperStar.app R)) :=
    @Functor.map.instIsMonHom _ _ _ _ _ _ π _ _ _ _ _ _ hB
  have : @IsMonHom _ _ _ _ _ (cX.monObjObj R) _ (constRingSheafToCondensedRingObj X T) :=
    @instIsMonHomComp _ _ _ _ _ _ (cX.monObjObj R) (π.monObjObj (cS.obj R))
      ((upperStarFromPoint X).monObjObj _) _ _ hA
      (@instIsMonHomComp _ _ _ _ _ _ (π.monObjObj (cS.obj R))
        (π.monObjObj (pointUpperStar.obj (cP.obj R))) ((upperStarFromPoint X).monObjObj _) _ _
        hC hD)
  exact IsMonHom.of_eq (h₁ := cX.monObjObj R) _
    (Functor.monObjObj_comp (Functor.const _) (presheafToSheaf _ _) R) rfl

section CommRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The two models of pro-étale sheaves with finite coefficients agree.** For a finite
discrete commutative ring `T`, module objects over the coefficient ring `Λ_X = p_X^* T̲` in
abelian sheaves on `X_proét` are the sheaves of `T`-modules on `X_proét`: restriction of
scalars along the isomorphism of ring objects `T_X ≅ Λ_X`
(`ProEtale.constRingSheafToCondensedRingObj`), followed by the identification of modules over
the constant ring sheaf `T_X` with sheaves of `T`-modules
(`CategoryTheory.Sheaf.modConstRingSheafEquivalence`). The underlying abelian sheaf is
preserved (`ProEtale.finiteCoefficientModEquivalence_functor_comp_sheafCompose`). -/
noncomputable def finiteCoefficientModEquivalence :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) X) ≌
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T)) :=
  (Mod.comapEquivalenceOfIsIso (constRingSheafToCondensedRingObj X T)).trans
    (Sheaf.modConstRingSheafEquivalence _ (ULift.{u + 1} T))

/-- The equivalence `finiteCoefficientModEquivalence` keeps the underlying abelian sheaf. -/
lemma finiteCoefficientModEquivalence_functor_comp_sheafCompose :
    (finiteCoefficientModEquivalence X T).functor ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) Ab.{u + 1}) =
      Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) X) :=
  rfl

end CommRing

end AlgebraicGeometry.ProEtale
