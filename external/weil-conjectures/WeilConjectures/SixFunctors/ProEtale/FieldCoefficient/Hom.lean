/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.GeometricFrobenius

/-!
# Tensor product and internal hom over the constant sheaf

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Hom`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

The constant sheaf `Λ_X` is a *commutative* sheaf of rings
(`AlgebraicGeometry.ProEtale.fieldConstantSheaf.isCommMonObj`), so sheaves of
`Λ_X`-modules have a tensor product `⊗_{Λ_X}` and an internal hom
`𝓗om_{Λ_X}` (`AlgebraicGeometry.ProEtale.FieldSheaf.ihom`), right adjoint to the tensor
product (`CategoryTheory.Mod.ihomAdjunction`). The pushforward along an isomorphism `e` commutes
with the internal hom (`AlgebraicGeometry.ProEtale.fieldLowerStarCompIhomIso`): this gives the
Weil structure of the internal hom of two Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

instance (X : Scheme.{u}) : IsCommMonObj (fieldConstantSheaf Λ X).obj where
  mul_comm := by
    refine NatTrans.ext (funext fun U ↦ ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ ?_)
    exact congrArg ULift.up (mul_comm t.down s.down)

/-- **The constant sheaf is a commutative sheaf of rings.** -/
instance fieldConstantSheaf.isCommMonObj (X : Scheme.{u}) :
    IsCommMonObj (fieldConstantSheaf Λ X) where
  mul_comm := Sheaf.tensor_hom_ext (by
    rw [Functor.map_comp, ← Category.assoc, Functor.LaxBraided.braided, Category.assoc,
      fieldConstantSheaf_μ_comp_map_mul']
    exact IsCommMonObj.mul_comm (fieldConstantSheaf Λ X).obj)

instance (X : Scheme.{u}) (M : Sheaf (Scheme.ProEt.topology X) (FieldCoefficients.{u} Λ)) :
    PreservesColimitsOfSize.{u + 1, u + 1} (MonoidalCategory.tensorLeft M) :=
  inferInstance

instance (X : Scheme.{u}) (M : Sheaf (Scheme.ProEt.topology X) (FieldCoefficients.{u} Λ)) :
    PreservesColimitsOfSize.{u + 1, u + 1} (MonoidalCategory.tensorRight M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

namespace FieldSheaf

/-- The internal hom `𝓗om_{Λ_X}(M, -)` of sheaves of `Λ_X`-modules, right adjoint to
`- ⊗_{Λ_X} M`. -/
noncomputable abbrev ihom {X : Scheme.{u}} (M : FieldSheaf Λ X) : FieldSheaf Λ X ⥤ FieldSheaf Λ X :=
  Mod.ihom M

end FieldSheaf

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

omit [IsUltrametricDist Λ] in
lemma fieldConstantSheafToLowerStar_eq [IsIso g] :
    fieldConstantSheafToLowerStar Λ g = (fieldConstantSheafLowerStarIso Λ (asIso g)).inv :=
  rfl

instance [IsIso g] : IsIso (fieldConstantSheafToLowerStar Λ g) := by
  rw [fieldConstantSheafToLowerStar_eq]
  infer_instance

variable (Λ) in
/-- The pushforward of sheaves of `Λ`-modules along an automorphism commutes with the
internal hom: `g_* 𝓗om(M, N) ≅ 𝓗om(g_* M, g_* N)`. -/
noncomputable def fieldLowerStarCompIhomIso (g : X ⟶ X) [IsIso g] (M : FieldSheaf Λ X) :
    (g)_*ᶠ[Λ] ⋙ FieldSheaf.ihom ((g)_*ᶠ[Λ].obj M) ≅ FieldSheaf.ihom M ⋙ (g)_*ᶠ[Λ] :=
  haveI : (Mod.mapModComap (G := (g)_*[FieldCoefficients.{u} Λ])
      (fieldConstantSheafToLowerStar Λ g)).IsEquivalence :=
    isEquivalence_fieldLowerStar Λ g
  Mod.mapModComapCompIhomIso (fieldConstantSheafToLowerStar Λ g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M

variable (Λ) in
/-- The pushforward of sheaves of `Λ`-modules along an automorphism commutes with the
tensor product: `g_* (P ⊗ M) ≅ g_* P ⊗ g_* M`. -/
noncomputable def fieldLowerStarTensorLeftIso (g : X ⟶ X) [IsIso g] (M : FieldSheaf Λ X) :
    Mod.tensorLeft M ⋙ (g)_*ᶠ[Λ] ≅ (g)_*ᶠ[Λ] ⋙ Mod.tensorLeft ((g)_*ᶠ[Λ].obj M) :=
  haveI : (Mod.mapModComap (G := (g)_*[FieldCoefficients.{u} Λ])
      (fieldConstantSheafToLowerStar Λ g)).IsEquivalence :=
    isEquivalence_fieldLowerStar Λ g
  Mod.tensorLeftCompMapModComapIso (fieldConstantSheafToLowerStar Λ g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M

end AlgebraicGeometry.ProEtale
