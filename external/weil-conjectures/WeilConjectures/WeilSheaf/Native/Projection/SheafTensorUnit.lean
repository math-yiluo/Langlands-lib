/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationSheafTensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.DisjointUnion
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation

/-! # Tensor generators and the units of pullback adjunctions

The adjoints of the two pullback tensor comparisons have the same formula on pure
 tensors: tensor the two adjunction units, then apply the pushforward tensor map.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On the relative-tensor quotient, the ordinary pullback tensor comparison is the
inverse tensorator of the pullback of the underlying sheaves. -/
@[reassoc]
lemma map_tensorπ_adicUpperStarTensorLeftIso_hom (M N : AdicSheaf l Y) :
    (upperStar (WeilCoefficients.{u} l) f).map (Mod.tensorπ M N) ≫
        ((adicUpperStarTensorLeftIso l f N).hom.app M).hom =
      δ (upperStar (WeilCoefficients.{u} l) f) M.X N.X ≫
        Mod.tensorπ ((adicUpperStar l f).obj M) ((adicUpperStar l f).obj N) := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := upperStar (WeilCoefficients.{u} l) f)
        (adicUpperStarRingHom l f)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (adicUpperStar l f))
  have h := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom
    (adicUpperStarRingHom l f)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f) _ _) M N
  rw [Functor.Monoidal.inv_μ] at h
  exact h

/-- The adjoint of the ordinary relative pullback tensor comparison, evaluated on
pure tensors, is the tensor of the units followed by the pushforward tensor map. -/
lemma tensorπ_homEquiv_adicUpperStarTensorLeftIso (M N : AdicSheaf l Y) :
    Mod.tensorπ M N ≫
        ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _
          ((adicUpperStarTensorLeftIso l f N).hom.app M)).hom =
      ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).unit.app M.X ⊗ₘ
        (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).unit.app N.X) ≫
      μ (lowerStar (WeilCoefficients.{u} l) f)
        ((adicUpperStar l f).obj M).X ((adicUpperStar l f).obj N).X ≫
      (lowerStar (WeilCoefficients.{u} l) f).map
        (Mod.tensorπ ((adicUpperStar l f).obj M) ((adicUpperStar l f).obj N)) := by
  rw [Adjunction.homEquiv_unit, Mod.comp_hom', adicLowerStar_map_hom,
    adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom]
  rw [← (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).unit_naturality_assoc,
    ← Functor.map_comp, map_tensorπ_adicUpperStarTensorLeftIso_hom, Functor.map_comp]
  rw [Adjunction.unit_app_tensor_comp_map_δ_assoc]
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The adjoint of the condensed pullback tensor comparison on pure tensors. -/
@[reassoc]
lemma tensorObjπ_homEquiv_δ
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Mod.tensorObjπ M N ≫
        ((upperStarLowerStarAdjunction Λ f).homEquiv _ _
          (δ (upperStar Λ f) M N)).hom =
      (((upperStarLowerStarAdjunction Λ f).unit.app M).hom ⊗ₘ
        ((upperStarLowerStarAdjunction Λ f).unit.app N).hom) ≫
      μ (ProEtale.lowerStar Ab.{u + 1} f)
        ((upperStar Λ f).obj M).X ((upperStar Λ f).obj N).X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map
        (Mod.tensorObjπ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N)) := by
  rw [upperStarLowerStarAdjunction_homEquiv_hom]
  rw [← (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit_naturality_assoc,
    ← Functor.map_comp, map_tensorObjπ_upperStarUnitHom_δ_hom,
    Functor.map_comp, Functor.map_comp]
  rw [Adjunction.unit_app_tensor_comp_map_δ_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_assoc,
    upperStarLowerStarAdjunction_unit_app_hom,
    upperStarLowerStarAdjunction_unit_app_hom, tensorHom_comp_tensorHom_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
