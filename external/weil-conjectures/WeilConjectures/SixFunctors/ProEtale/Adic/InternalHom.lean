/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-!
# The internal hom of `ℚ̄_ℓ,X`-modules is local

The internal hom `𝓗om_{ℚ̄_ℓ,X}(M, N)` of sheaves of `ℚ̄_ℓ,X`-modules is the equalizer of
`[M, N] ⇉ [ℚ̄_ℓ,X ⊗ M, N]` (`AlgebraicGeometry.ProEtale.AdicSheaf.ihomIsoIhom'`). Pullback along a
weakly étale morphism `g` commutes with the internal hom of sheaves and with equalizers, so it
commutes with `𝓗om_{ℚ̄_ℓ}` (`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso`):
`g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Sheaf.symmetricCategory

namespace AdicSheaf

/-- The internal hom of sheaves of `ℚ̄_ℓ,X`-modules is the equalizer
`Hom_A(M, N) ⟶ [M, N] ⇉ [A ⊗ M, N]`. -/
noncomputable def ihomIsoIhom' {X : Scheme.{u}} (M : AdicSheaf l X) :
    ihom M ≅ Mod.ihom' (adicConstantSheaf l X) M :=
  (Mod.ihomAdjunction M).rightAdjointUniq (Mod.ihom'Adjunction _ M)

end AdicSheaf

variable {V X : Scheme.{u}} (g : V ⟶ X) [WeaklyEtale g]

/-- The ring isomorphism `ℚ̄_ℓ,V ≅ g^* ℚ̄_ℓ,X` along which `g^*` acts on modules. -/
noncomputable abbrev adicUpperStarRingIso : adicConstantSheaf l V ⟶
    (g)^*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) :=
  inv (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).homEquiv _ _).symm
    (adicConstantSheafToLowerStar l g))

lemma adicUpperStar_eq : (g)^*ᵃ[l] = (g)^*[WeilCoefficients.{u} l].mapMod _ ⋙
    Mod.comap (adicUpperStarRingIso g) := rfl

variable (l) in
/-- **The pullback along a weakly étale morphism commutes with `𝓗om_{ℚ̄_ℓ}`**:
`g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)`, naturally in `N`. -/
noncomputable def adicUpperStarIhomIso (M : AdicSheaf l X) :
    AdicSheaf.ihom M ⋙ (g)^*ᵃ[l] ≅ (g)^*ᵃ[l] ⋙ AdicSheaf.ihom ((g)^*ᵃ[l].obj M) :=
  have := isIso_ihomComparison_upperStar (WeilCoefficients.{u} l) g
  have (N : AdicSheaf l X) : PreservesLimit (parallelPair (Mod.homModPre (Mod.act M.X) N)
      (Mod.homModB _ M N)) ((g)^*[WeilCoefficients.{u} l].mapMod _ ⋙
        Mod.comap (adicUpperStarRingIso g)) :=
    inferInstanceAs (PreservesLimit _ (g)^*ᵃ[l])
  Functor.isoWhiskerRight (AdicSheaf.ihomIsoIhom' M) (g)^*ᵃ[l] ≪≫
    NatIso.ofComponents (F := Mod.ihom' _ M ⋙ (g)^*ᵃ[l])
      (G := (g)^*ᵃ[l] ⋙ Mod.ihom' _ ((g)^*ᵃ[l].obj M)) (fun N ↦
      have := Mod.isIso_mapIhom'Hom (g)^*[WeilCoefficients.{u} l] (adicUpperStarRingIso g) M N
      asIso (Mod.mapIhom'Hom (g)^*[WeilCoefficients.{u} l] (adicUpperStarRingIso g) M N))
      (fun f ↦ Mod.mapIhom'Hom_naturality _ _ M f) ≪≫
    Functor.isoWhiskerLeft (g)^*ᵃ[l] (AdicSheaf.ihomIsoIhom' ((g)^*ᵃ[l].obj M)).symm

end AlgebraicGeometry.ProEtale
