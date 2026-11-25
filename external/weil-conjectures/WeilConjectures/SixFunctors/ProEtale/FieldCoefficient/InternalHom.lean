/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-!
# The internal hom of `Λ_X`-modules is local

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

The internal hom `𝓗om_{Λ_X}(M, N)` of sheaves of `Λ_X`-modules is the equalizer of
`[M, N] ⇉ [Λ_X ⊗ M, N]` (`AlgebraicGeometry.ProEtale.FieldSheaf.ihomIsoIhom'`). Pullback along a
weakly étale morphism `g` commutes with the internal hom of sheaves and with equalizers, so it
commutes with `𝓗om_{Λ}` (`AlgebraicGeometry.ProEtale.fieldUpperStarIhomIso`):
`g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

attribute [local instance] Sheaf.symmetricCategory

namespace FieldSheaf

/-- The internal hom of sheaves of `Λ_X`-modules is the equalizer
`Hom_A(M, N) ⟶ [M, N] ⇉ [A ⊗ M, N]`. -/
noncomputable def ihomIsoIhom' {X : Scheme.{u}} (M : FieldSheaf Λ X) :
    ihom M ≅ Mod.ihom' (fieldConstantSheaf Λ X) M :=
  (Mod.ihomAdjunction M).rightAdjointUniq (Mod.ihom'Adjunction _ M)

end FieldSheaf

variable {V X : Scheme.{u}} (g : V ⟶ X) [WeaklyEtale g]

/-- The ring isomorphism `Λ_V ≅ g^* Λ_X` along which `g^*` acts on modules. -/
noncomputable abbrev fieldUpperStarRingIso : fieldConstantSheaf Λ V ⟶
    (g)^*[FieldCoefficients.{u} Λ].obj (fieldConstantSheaf Λ X) :=
  inv (((upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).homEquiv _ _).symm
    (fieldConstantSheafToLowerStar Λ g))

lemma fieldUpperStar_eq : (g)^*ᶠ[Λ] = (g)^*[FieldCoefficients.{u} Λ].mapMod _ ⋙
    Mod.comap (fieldUpperStarRingIso g) := rfl

variable (Λ) in
/-- **The pullback along a weakly étale morphism commutes with `𝓗om_{Λ}`**:
`g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)`, naturally in `N`. -/
noncomputable def fieldUpperStarIhomIso (M : FieldSheaf Λ X) :
    FieldSheaf.ihom M ⋙ (g)^*ᶠ[Λ] ≅ (g)^*ᶠ[Λ] ⋙ FieldSheaf.ihom ((g)^*ᶠ[Λ].obj M) :=
  have := isIso_ihomComparison_upperStar (FieldCoefficients.{u} Λ) g
  have (N : FieldSheaf Λ X) : PreservesLimit (parallelPair (Mod.homModPre (Mod.act M.X) N)
      (Mod.homModB _ M N)) ((g)^*[FieldCoefficients.{u} Λ].mapMod _ ⋙
        Mod.comap (fieldUpperStarRingIso g)) :=
    inferInstanceAs (PreservesLimit _ (g)^*ᶠ[Λ])
  Functor.isoWhiskerRight (FieldSheaf.ihomIsoIhom' M) (g)^*ᶠ[Λ] ≪≫
    NatIso.ofComponents (F := Mod.ihom' _ M ⋙ (g)^*ᶠ[Λ])
      (G := (g)^*ᶠ[Λ] ⋙ Mod.ihom' _ ((g)^*ᶠ[Λ].obj M)) (fun N ↦
      have := Mod.isIso_mapIhom'Hom (g)^*[FieldCoefficients.{u} Λ] (fieldUpperStarRingIso g) M N
      asIso (Mod.mapIhom'Hom (g)^*[FieldCoefficients.{u} Λ] (fieldUpperStarRingIso g) M N))
      (fun f ↦ Mod.mapIhom'Hom_naturality _ _ M f) ≪≫
    Functor.isoWhiskerLeft (g)^*ᶠ[Λ] (FieldSheaf.ihomIsoIhom' ((g)^*ᶠ[Λ].obj M)).symm

end AlgebraicGeometry.ProEtale
