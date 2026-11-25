/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius

/-!
# Tensor product and internal hom over the constant `ℓ`-adic sheaf

The constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` is a *commutative* sheaf of rings
(`AlgebraicGeometry.ProEtale.adicConstantSheaf.isCommMonObj`), so sheaves of
`ℚ̄_ℓ,X`-modules have a tensor product `⊗_{ℚ̄_ℓ,X}` and an internal hom
`𝓗om_{ℚ̄_ℓ,X}` (`AlgebraicGeometry.ProEtale.AdicSheaf.ihom`), right adjoint to the tensor
product (`CategoryTheory.Mod.ihomAdjunction`). The pushforward along an isomorphism `e` commutes
with the internal hom (`AlgebraicGeometry.ProEtale.adicLowerStarCompIhomIso`): this gives the
Weil structure of the internal hom of two Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

instance (X : Scheme.{u}) : IsCommMonObj (adicConstantSheaf l X).obj where
  mul_comm := by
    refine NatTrans.ext (funext fun U ↦ ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ ?_)
    exact congrArg ULift.up (mul_comm t.down s.down)

/-- **The constant `ℓ`-adic sheaf is a commutative sheaf of rings.** -/
instance adicConstantSheaf.isCommMonObj (X : Scheme.{u}) :
    IsCommMonObj (adicConstantSheaf l X) where
  mul_comm := Sheaf.tensor_hom_ext (by
    rw [Functor.map_comp, ← Category.assoc, Functor.LaxBraided.braided, Category.assoc,
      adicConstantSheaf_μ_comp_map_mul']
    exact IsCommMonObj.mul_comm (adicConstantSheaf l X).obj)

instance (X : Scheme.{u}) (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    PreservesColimitsOfSize.{u + 1, u + 1} (MonoidalCategory.tensorLeft M) :=
  inferInstance

instance (X : Scheme.{u}) (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    PreservesColimitsOfSize.{u + 1, u + 1} (MonoidalCategory.tensorRight M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

namespace AdicSheaf

/-- The internal hom `𝓗om_{ℚ̄_ℓ,X}(M, -)` of sheaves of `ℚ̄_ℓ,X`-modules, right adjoint to
`- ⊗_{ℚ̄_ℓ,X} M`. -/
noncomputable abbrev ihom {X : Scheme.{u}} (M : AdicSheaf l X) : AdicSheaf l X ⥤ AdicSheaf l X :=
  Mod.ihom M

end AdicSheaf

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

lemma adicConstantSheafToLowerStar_eq [IsIso g] :
    adicConstantSheafToLowerStar l g = (adicConstantSheafLowerStarIso l (asIso g)).inv :=
  rfl

instance [IsIso g] : IsIso (adicConstantSheafToLowerStar l g) := by
  rw [adicConstantSheafToLowerStar_eq]
  infer_instance

variable (l) in
/-- The pushforward of sheaves of `ℚ̄_ℓ`-modules along an automorphism commutes with the
internal hom: `g_* 𝓗om(M, N) ≅ 𝓗om(g_* M, g_* N)`. -/
noncomputable def adicLowerStarCompIhomIso (g : X ⟶ X) [IsIso g] (M : AdicSheaf l X) :
    (g)_*ᵃ[l] ⋙ AdicSheaf.ihom ((g)_*ᵃ[l].obj M) ≅ AdicSheaf.ihom M ⋙ (g)_*ᵃ[l] :=
  haveI : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence :=
    isEquivalence_adicLowerStar l g
  Mod.mapModComapCompIhomIso (adicConstantSheafToLowerStar l g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M

variable (l) in
/-- The pushforward of sheaves of `ℚ̄_ℓ`-modules along an automorphism commutes with the
tensor product: `g_* (P ⊗ M) ≅ g_* P ⊗ g_* M`. -/
noncomputable def adicLowerStarTensorLeftIso (g : X ⟶ X) [IsIso g] (M : AdicSheaf l X) :
    Mod.tensorLeft M ⋙ (g)_*ᵃ[l] ≅ (g)_*ᵃ[l] ⋙ Mod.tensorLeft ((g)_*ᵃ[l].obj M) :=
  haveI : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence :=
    isEquivalence_adicLowerStar l g
  Mod.tensorLeftCompMapModComapIso (adicConstantSheafToLowerStar l g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M

end AlgebraicGeometry.ProEtale
