/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsGlobal

/-!
# The closed inverse image of abelian sheaves preserves limits

The abelian version of `AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_of_isCompl`:
abelian groups are the modules over `ULift ℤ`
(`AlgebraicGeometry.ProEtale.uliftIntModuleToAb`, an equivalence), and the pullback `g^*` of
pro-étale sheaves commutes with this change of coefficients
(`AlgebraicGeometry.ProEtale.sheafComposeInverseCompUpperStarIso`), being the left adjoint of
the direct image, which commutes with it on the nose.

- `AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_ab_of_isCompl`: for `X`
  quasi-compact and quasi-separated and `i : Z ⟶ X` a closed immersion with quasi-compact open
  complement, the pullback `i^*` of abelian pro-étale sheaves preserves all small limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Modules over `ULift ℤ` are abelian groups: restriction of scalars to `ℤ` followed by the
forgetful functor, an equivalence of categories. -/
noncomputable abbrev uliftIntModuleToAb : ModuleCat.{u + 1} (ULift.{u + 1} ℤ) ⥤ Ab.{u + 1} :=
  ModuleCat.restrictScalars (ULift.ringEquiv (R := ℤ)).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}

variable (X : Scheme.{u})

/-- Pro-étale sheaves of `ULift ℤ`-modules are abelian pro-étale sheaves. -/
noncomputable abbrev sheafComposeUliftIntModuleToAb :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ⥤
      Sheaf (ProEt.topology X) Ab.{u + 1} :=
  sheafCompose (ProEt.topology X) uliftIntModuleToAb.{u}

instance : (sheafComposeUliftIntModuleToAb X).IsEquivalence := by
  let e := uliftIntModuleToAb.{u}.asEquivalence
  have : (sheafComposeUliftIntModuleToAb X).EssSurj := ⟨fun P ↦
    ⟨(sheafCompose (ProEt.topology X) e.inverse).obj P,
      ⟨ObjectProperty.isoMk _ (Functor.isoWhiskerLeft P.obj e.counitIso)⟩⟩⟩
  exact {}

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- The pullback of abelian pro-étale sheaves is the pullback of sheaves of `ULift ℤ`-modules:
the conjugate of the identity `g_* ⋙ S = S ⋙ g_*` of direct images, `S` the identification of
sheaves of `ULift ℤ`-modules with abelian sheaves. -/
noncomputable def sheafComposeInverseCompUpperStarIso :
    (sheafComposeUliftIntModuleToAb X).inv ⋙
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)] ≅
      (g)^*[Ab.{u + 1}] ⋙ (sheafComposeUliftIntModuleToAb Y).inv :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (sheafComposeUliftIntModuleToAb Y).asEquivalence.symm.toAdjunction)
    ((sheafComposeUliftIntModuleToAb X).asEquivalence.symm.toAdjunction.comp
      (upperStarLowerStarAdjunction _ g))).symm (Iso.refl _)

/-- The pullback of abelian pro-étale sheaves preserves the limits that the pullback of sheaves
of `ULift ℤ`-modules preserves. -/
lemma preservesLimitsOfSize_upperStar_ab_of_moduleCat
    [PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)])] :
    PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[Ab.{u + 1}]) := by
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      ((g)^*[Ab.{u + 1}] ⋙ (sheafComposeUliftIntModuleToAb Y).inv) :=
    preservesLimits_of_natIso (sheafComposeInverseCompUpperStarIso g)
  exact preservesLimits_of_reflects_of_preserves _ (sheafComposeUliftIntModuleToAb Y).inv

/-- **The closed inverse image of abelian sheaves preserves limits**: for `X` quasi-compact and
quasi-separated and `i : Z ⟶ X` a closed immersion with quasi-compact open complement `j`, the
pullback `i^*` of abelian pro-étale sheaves preserves all small limits. -/
theorem preservesLimitsOfSize_upperStar_ab_of_isCompl {X Z U : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesLimitsOfSize.{u + 1, u + 1} ((i)^*[Ab.{u + 1}]) :=
  have := preservesLimitsOfSize_upperStar_of_isCompl (R := ULift.{u + 1} ℤ) i j hij
  preservesLimitsOfSize_upperStar_ab_of_moduleCat i

end AlgebraicGeometry.ProEtale
