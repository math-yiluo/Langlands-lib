/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleExtendScalarsBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit

/-!
# The pushforward of `ℓ`-adic sheaves commutes with direct sums

For a quasi-compact quasi-separated morphism of schemes `f : X ⟶ Y`, the pushforward `f_*` of
`ℓ`-adic sheaves on the small pro-étale sites commutes with direct sums
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_adicLowerStar`), and direct sums
of injective `ℓ`-adic sheaves are `f_*`-acyclic
(`AlgebraicGeometry.ProEtale.rightAcyclic_adicLowerStar_sigma_of_injective`).

Both statements are reduced to the corresponding ones for abelian sheaves
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_lowerStar`,
`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit_discrete`) through the underlying
abelian sheaf functor `AdicSheaf.toAb`, which commutes with `f_*`, preserves colimits and
injective objects, reflects isomorphisms and computes the higher direct images
(`AlgebraicGeometry.ProEtale.rightDerivedAdicLowerStarToAbIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime]

/-- The underlying abelian sheaf functor on sheaves of `ℚ̄_ℓ`-modules is a left adjoint: the
forgetful functor `ModuleCat ℚ̄_ℓ ⥤ Ab` is restriction of scalars along `ℤ ⟶ ℚ̄_ℓ`, left adjoint to
coextension of scalars. -/
instance isLeftAdjoint_weilCoefficientsForgetAb (X : Scheme.{u}) :
    (weilCoefficientsForgetAb l X).IsLeftAdjoint := by
  have hleft : (forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
    have : (ModuleCat.restrictScalars.{u + 1}
        (Int.castRingHom (ULift.{u + 1} (PadicAlgCl l)))).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} (PadicAlgCl l)))).isLeftAdjoint
    exact inferInstanceAs (ModuleCat.restrictScalars.{u + 1}
      (Int.castRingHom (ULift.{u + 1} (PadicAlgCl l))) ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  let adj := Adjunction.ofIsLeftAdjoint (forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1})
  have : PreservesLimitsOfSize.{u, u + 1}
      (forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1}).rightAdjoint :=
    adj.rightAdjoint_preservesLimits
  have : (ProEt.topology X).HasSheafCompose
      (forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1}).rightAdjoint :=
    hasSheafCompose_of_preservesLimitsOfSize _
  exact (sheafComposeAdjunction (ProEt.topology X) adj).isLeftAdjoint

/-- The underlying abelian sheaf of `ℓ`-adic sheaves commutes with direct sums. -/
instance preservesColimitsOfShape_discrete_toAb (X : Scheme.{u}) (B : Type) :
    PreservesColimitsOfShape (Discrete B) (AdicSheaf.toAb l X) := by
  unfold AdicSheaf.toAb
  infer_instance

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- For a quasi-compact quasi-separated morphism `f`, the pushforward `f_*` of `ℓ`-adic sheaves
on the small pro-étale sites commutes with direct sums. -/
theorem preservesColimitsOfShape_discrete_adicLowerStar (B : Type) :
    PreservesColimitsOfShape (Discrete B) (f)_*ᵃ[l] := by
  have := preservesColimitsOfShape_discrete_lowerStar f B
  have : PreservesColimitsOfShape (Discrete B) ((f)_*ᵃ[l] ⋙ AdicSheaf.toAb l Y) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete B)
      (AdicSheaf.toAb l X ⋙ (f)_*[Ab.{u + 1}]))
  have : ReflectsColimitsOfShape (Discrete B) (AdicSheaf.toAb l Y) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (AdicSheaf.toAb l Y)

/-- For a quasi-compact quasi-separated morphism `f`, a direct sum of injective `ℓ`-adic sheaves
is `f_*`-acyclic. -/
lemma rightAcyclic_adicLowerStar_sigma_of_injective {B : Type} (S : B → AdicSheaf l X)
    [∀ b, Injective (S b)] : ((f)_*ᵃ[l]).rightAcyclic (∐ S) :=
  rightAcyclic_adicLowerStar_of_rightAcyclic_toAb l f
    (rightAcyclic_lowerStar_of_isColimit_discrete f
      (isColimitOfPreserves (AdicSheaf.toAb l X) (colimit.isColimit (Discrete.functor S)))
      fun ⟨b⟩ ↦ have := (AdicSheaf.toAb l X).injective_obj (S b)
        ((f)_*[Ab.{u + 1}]).rightAcyclic_of_injective ((AdicSheaf.toAb l X).obj (S b)))

end AlgebraicGeometry.ProEtale
