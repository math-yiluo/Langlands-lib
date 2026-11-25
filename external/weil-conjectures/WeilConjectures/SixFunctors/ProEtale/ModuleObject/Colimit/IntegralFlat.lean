/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# **(Pull)** for the inclusion `𝒪_E ⟶ E`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `X`
a scheme. The coefficient ring `E_X = p_X^* E̲` is flat over `𝒪_{E,X} = p_X^* 𝒪̲_E`: the extension
of scalars along the inclusion `ProEtale.padicIntegersToPadicSubfield X ℓ E : 𝒪_{E,X} ⟶ E_X` is
exact (`ProEtale.preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield`, in
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`).

Consequently the comparison **(Pull)** `ProEtale.CondensedRing.derivedPullIso` applies to the
inclusion `𝒪̲_E ⟶ E̲`, and restricts to bounded constructible complexes:
`Lf^*_{𝒪_E} ⋙ (E ⊗ᴸ_{𝒪_E} -) ≅ (E ⊗ᴸ_{𝒪_E} -) ⋙ Lf^*_E`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : Y ⟶ X)

/-- **(Pull)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E`:
`Lf^*_{𝒪_E} ⋙ (E ⊗ᴸ_{𝒪_E} -) ≅ (E ⊗ᴸ_{𝒪_E} -) ⋙ Lf^*_E`, the restriction of
`ProEtale.CondensedRing.derivedPullIso` (which applies since `E_X` is flat over `𝒪_{E,X}`) along
the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarExtendScalarsIso :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ f ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleExtendScalarsCompatibility Y.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedPullIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleExtendScalarsCompatibility X.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

end AlgebraicGeometry.ProEtale.CondensedRing
