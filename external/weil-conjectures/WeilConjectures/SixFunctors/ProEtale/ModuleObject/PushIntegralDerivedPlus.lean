/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralUnderived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Bounded below derived pushforward commutes with `E ⊗_{𝒪_E} -`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`f : X ⟶ Y` a quasi-compact quasi-separated morphism of schemes. The base change morphism
`E_Y ⊗ R⁺f_* K ⟶ R⁺f_*(E_X ⊗ K)` of the bounded below derived pushforwards of module objects,
attached to the underived comparison (Push) for the inclusion `𝒪̲_E ⟶ E̲`, is an isomorphism
(`ProEtale.CondensedRing.isIso_rightDerivedFunctorPlusBaseChange_pushHom_padicIntegers`), and so
is the induced morphism `E_Y ⊗ R^q f_* M ⟶ R^q f_*(E_X ⊗ M)` of higher direct images
(`ProEtale.CondensedRing.isIso_rightDerivedBaseChange_pushHom_padicIntegers`).

Indeed (Push) is an isomorphism
(`ProEtale.CondensedRing.isIso_pushHom_padicIntegersRingObjToContinuousMapRingObj`), the extension
of scalars is exact, and it sends injective `𝒪_{E,X}`-modules to `f_*`-acyclic `E_X`-modules:
their underlying abelian sheaves are `f_*`-acyclic
(`ProEtale.rightAcyclic_lowerStar_extendScalars_of_injective`), and the higher direct images of an
`E_X`-module are computed on its underlying abelian sheaf, `E_X` being flat over `ℤ`
(`ProEtale.CondensedRing.isIso_rightDerivedLowerStarPlusForget`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Forget

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

omit [IsCommMonObj Λ] in
/-- If `Λ_X` is flat, a `Λ_X`-module object is `f_*`-acyclic as soon as its underlying abelian
sheaf is. -/
lemma rightAcyclic_lowerStar_of_rightAcyclic_forget
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : ((f)_*[Ab.{u + 1}]).rightAcyclic M.X) :
    ((f)_*⟦Λ⟧).rightAcyclic M := fun q ↦ by
  have : IsIso (Functor.rightDerivedBaseChange (lowerStarForgetIso Λ f).inv (q + 1)) := by
    rw [show (lowerStarForgetIso Λ f).inv = (Iso.refl _ :
      (f)_*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y) ≅
        Mod.forget (condensedRingObj Λ X) ⋙ (f)_*[Ab.{u + 1}]).hom from rfl]
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    have := isIso_rightDerivedLowerStarPlusForget Λ f
    have : IsIso ((rightDerivedLowerStarPlusForget Λ f).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) := inferInstance
    unfold rightDerivedLowerStarPlusForget at this
    infer_instance
  have hz : IsZero ((Mod.forget (condensedRingObj Λ Y)).obj
      ((((f)_*⟦Λ⟧).rightDerived (q + 1)).obj M)) :=
    (h q).of_iso
      ((asIso (Functor.rightDerivedBaseChange (lowerStarForgetIso Λ f).inv (q + 1))).app M)
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  exact (Mod.forget (condensedRingObj Λ Y)).map_injective
    (by rw [CategoryTheory.Functor.map_id, Functor.map_zero, hz])

end Forget

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}}
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **(Push) for `𝒪_E ⟶ E` on bounded below derived categories**: for a quasi-compact
quasi-separated `f`, the base change morphism `E_Y ⊗ R⁺f_* K ⟶ R⁺f_*(E_X ⊗ K)` attached to the
underived comparison (Push) is an isomorphism. -/
instance isIso_rightDerivedFunctorPlusBaseChange_pushHom_padicIntegers :
    IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f)) :=
  have : IsIso (pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f) :=
    NatIso.isIso_of_isIso_app _
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (asIso (pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f))
    fun I _ ↦ rightAcyclic_lowerStar_of_rightAcyclic_forget _ f
      (rightAcyclic_lowerStar_extendScalars_of_injective ℓ E f I)

/-- **(Push) for `𝒪_E ⟶ E` on higher direct images**: for a quasi-compact quasi-separated `f`,
the base change morphism `E_Y ⊗ R^q f_* M ⟶ R^q f_*(E_X ⊗ M)` is an isomorphism. -/
instance isIso_rightDerivedBaseChange_pushHom_padicIntegers (q : ℕ) :
    IsIso (Functor.rightDerivedBaseChange
      (pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f) q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [Functor.rightDerivedBaseChange_app]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
