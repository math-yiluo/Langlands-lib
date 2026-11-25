/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom

/-!
# Coherence of the internal hom of `ℓ`-adic sheaves

The internal hom `𝓗om_{ℚ̄_ℓ,X}(M, N)` of sheaves of `ℚ̄_ℓ,X`-modules is `ℚ̄_ℓ`-linear in both
variables (`AlgebraicGeometry.ProEtale.AdicSheaf.ihom_map_smul`,
`AlgebraicGeometry.ProEtale.AdicSheaf.ihomMap_smul_app`). Its compatibility with the pushforward
along an automorphism `g` (`AlgebraicGeometry.ProEtale.adicLowerStarCompIhomIso`) is natural in
the first variable and compatible with `𝓗om(ℚ̄_ℓ,X, -) ≅ 𝟭`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

namespace AdicSheaf

lemma tensorRight_map_smul (c : ULift.{u + 1} (PadicAlgCl l)) (P : AdicSheaf l X)
    (Y : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    (Mod.tensorRight _ Y).map (smul c P) = smul c _ :=
  Mod.hom_ext _ _ (by simp [MonoidalLinear.smul_whiskerRight]; rfl)

lemma tensorRightMap_smul_app (c : ULift.{u + 1} (PadicAlgCl l)) (M P : AdicSheaf l X) :
    (Mod.tensorRightMap _ (smul c M).hom).app P = smul c _ :=
  Mod.hom_ext _ _ (by simp [MonoidalLinear.whiskerLeft_smul]; rfl)

/-- The tensor product of sheaves of `ℚ̄_ℓ,X`-modules is `ℚ̄_ℓ`-linear in the first variable. -/
lemma tensorLeft_map_smul (M P : AdicSheaf l X) (c : ULift.{u + 1} (PadicAlgCl l)) :
    (Mod.tensorLeft M).map (smul c P) = smul c _ := by
  refine Mod.tensorLeft_hom_ext M P ?_
  rw [Mod.tensorLeftπ_naturality, tensorRight_map_smul, smul_comp]

/-- The tensor product of sheaves of `ℚ̄_ℓ,X`-modules is `ℚ̄_ℓ`-linear in the second variable. -/
lemma tensorLeftMap_smul_app (M P : AdicSheaf l X) (c : ULift.{u + 1} (PadicAlgCl l)) :
    (Mod.tensorLeftMap (smul c M)).app P = smul c _ := by
  refine Mod.tensorLeft_hom_ext M P ?_
  rw [Mod.tensorLeftπ_tensorLeftMap_app, tensorRightMap_smul_app, smul_comp]

/-- The internal hom of sheaves of `ℚ̄_ℓ,X`-modules is `ℚ̄_ℓ`-linear in the second variable. -/
lemma ihom_map_smul (M N : AdicSheaf l X) (c : ULift.{u + 1} (PadicAlgCl l)) :
    (Mod.ihom M).map (smul c N) = smul c _ := by
  refine Mod.ihom_hom_ext ?_
  rw [tensorLeft_map_smul]
  exact ((Mod.ihomAdjunction M).counit.naturality _).trans (smul_comp _ _).symm

/-- The internal hom of sheaves of `ℚ̄_ℓ,X`-modules is `ℚ̄_ℓ`-linear in the first variable. -/
lemma ihomMap_smul_app (M N : AdicSheaf l X) (c : ULift.{u + 1} (PadicAlgCl l)) :
    (Mod.ihomMap (smul c M)).app N = smul c _ := by
  refine Mod.ihom_hom_ext ?_
  rw [Mod.tensorLeft_map_ihomMap_app_counit, tensorLeftMap_smul_app, tensorLeft_map_smul,
    smul_comp]

end AdicSheaf

variable (l)

/-- The compatibility `g_* 𝓗om(M, N) ≅ 𝓗om(g_* M, g_* N)` of the pushforward along an
automorphism with internal homs is natural in `M`. -/
lemma adicLowerStarCompIhomIso_inv_app_comp_ihomMap (g : X ⟶ X) [IsIso g]
    {M M' : AdicSheaf l X} (f : M ⟶ M') (N : AdicSheaf l X) :
    (adicLowerStarCompIhomIso l g M').inv.app N ≫
        (Mod.ihomMap ((g)_*ᵃ[l].map f)).app ((g)_*ᵃ[l].obj N) =
      (g)_*ᵃ[l].map ((Mod.ihomMap f).app N) ≫ (adicLowerStarCompIhomIso l g M).inv.app N :=
  haveI : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence := isEquivalence_adicLowerStar l g
  Mod.mapModComapCompIhomIso_inv_app_comp_ihomMap (adicConstantSheafToLowerStar l g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) f N

/-- The compatibility `g_* 𝓗om(M, N) ≅ 𝓗om(g_* M, g_* N)` of the pushforward along an
automorphism with internal homs is compatible with `𝓗om(ℚ̄_ℓ,X, -) ≅ 𝟭` and
`g_* ℚ̄_ℓ,X ≅ ℚ̄_ℓ,X`. -/
lemma map_ihomRegularIso_inv_app_comp_adicLowerStarCompIhomIso_inv_app (e : X ≅ X)
    (N : AdicSheaf l X) :
    (e.hom)_*ᵃ[l].map (Mod.ihomRegularIso.inv.app N) ≫
        (adicLowerStarCompIhomIso l e.hom (AdicSheaf.unit l X)).inv.app N =
      Mod.ihomRegularIso.inv.app ((e.hom)_*ᵃ[l].obj N) ≫
        (Mod.ihomMap (adicLowerStarUnitIso l e).hom).app ((e.hom)_*ᵃ[l].obj N) :=
  haveI : (Mod.mapModComap (G := (e.hom)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l e.hom)).IsEquivalence := isEquivalence_adicLowerStar l e.hom
  Mod.map_ihomRegularIso_inv_app_comp_mapModComapCompIhomIso_inv_app
    (adicConstantSheafToLowerStar l e.hom) (fun _ _ ↦ Functor.LaxBraided.braided _ _)
    (adicLowerStarUnitIso l e) (by
      rw [adicLowerStarUnitIso_hom_hom]
      exact (IsIso.inv_eq_of_hom_inv_id (adicConstantSheafLowerStarIso l e).inv_hom_id).symm) N

end AlgebraicGeometry.ProEtale
