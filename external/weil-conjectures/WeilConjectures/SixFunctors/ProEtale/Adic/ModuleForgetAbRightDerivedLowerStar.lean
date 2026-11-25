/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar

/-!
# Underlying abelian sheaves of derived direct images of sheaves of modules

Let `Λ` be a commutative ring which is flat over `ℤ` (for instance `ULift ℤ_ℓ`) and
`f : X ⟶ Y` a morphism of schemes. Taking underlying abelian sheaves of pro-étale sheaves of
`Λ`-modules commutes with the derived direct images:
```
Hᵠ(Rf_* F[0])_ab ≅ Hᵠ(Rf_* F_ab[0])
```
(`AlgebraicGeometry.ProEtale.sheafComposeForget₂HomologyRightDerivedLowerStarIso`). The point is
that the forgetful functor has the exact left adjoint `A ↦ (Λ ⊗[ℤ] A)^#`, `Λ` being flat over
`ℤ`, so that it preserves injective objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Module.Flat ℤ Λ]

/-- The sheafified free `Λ`-module functor on pro-étale abelian sheaves preserves
monomorphisms, `Λ` being flat over `ℤ`. -/
instance preservesMonomorphisms_sheafExtendScalarsAb (X : Scheme.{u}) :
    (Sheaf.extendScalarsAb (ProEt.topology X) Λ).PreservesMonomorphisms := by
  have := Functor.preservesMonomorphisms_whiskeringRight_obj (C := X.ProEtᵒᵖ)
    (ModuleCat.extendScalarsAb Λ)
  exact inferInstanceAs (Sheaf.composeAndSheafify _ _).PreservesMonomorphisms

/-- The underlying abelian sheaf of an injective pro-étale sheaf of `Λ`-modules is injective,
`Λ` being flat over `ℤ`. -/
instance preservesInjectiveObjects_sheafCompose_forget₂ (X : Scheme.{u}) :
    (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Sheaf.extendScalarsAbAdjunction (ProEt.topology X) Λ)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pushforward of pro-étale sheaves of `Λ`-modules commutes with taking underlying abelian
sheaves, strictly. -/
noncomputable def lowerStarCompSheafComposeForget₂Iso :
    (f)_*[ModuleCat.{u + 1} Λ] ⋙
        sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ≅
      sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ⋙
        (f)_*[Ab.{u + 1}] :=
  Iso.refl _

/-- The base change morphism `(R⁺f_* K)_ab ⟶ R⁺f_*(K_ab)` for pro-étale sheaves of
`Λ`-modules. -/
noncomputable def rightDerivedLowerStarSheafComposeForget₂ :
    ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ⋙
        (sheafCompose (ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).mapDerivedCategoryPlus ⟶
      (sheafCompose (ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).mapDerivedCategoryPlus ⋙
        ((f)_*[Ab.{u + 1}]).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (lowerStarCompSheafComposeForget₂Iso Λ f).hom

/-- The comparison `(R⁺f_* K)_ab ⟶ R⁺f_*(K_ab)` is an isomorphism, the underlying abelian
sheaves of injective sheaves of `Λ`-modules being injective. -/
instance isIso_rightDerivedLowerStarSheafComposeForget₂ :
    IsIso (rightDerivedLowerStarSheafComposeForget₂ Λ f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun _ _ ↦ Functor.rightAcyclic_of_injective _

/-- `(Rᵠf_* F)_ab ≅ Rᵠf_*(F_ab)` for pro-étale sheaves of `Λ`-modules, for the classical right
derived functors. -/
noncomputable def rightDerivedLowerStarSheafComposeForget₂Iso (q : ℕ) :
    ((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q ⋙
        sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ≅
      sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ⋙
        ((f)_*[Ab.{u + 1}]).rightDerived q :=
  have : IsIso
      (Functor.rightDerivedBaseChange (lowerStarCompSheafComposeForget₂Iso Λ f).hom q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarCompSheafComposeForget₂Iso Λ f).hom) :=
      isIso_rightDerivedLowerStarSheafComposeForget₂ Λ f
    infer_instance
  asIso (Functor.rightDerivedBaseChange (lowerStarCompSheafComposeForget₂Iso Λ f).hom q)

/-- **Cohomology sheaves of derived direct images of sheaves of `Λ`-modules, as abelian
sheaves**: for a pro-étale sheaf of `Λ`-modules `F` on `X` (`Λ` flat over `ℤ`), the underlying
abelian sheaf of `Hᵠ(Rf_* F[0])` is `Hᵠ(Rf_* F_ab[0])`, computed for abelian sheaves. -/
noncomputable def sheafComposeForget₂HomologyRightDerivedLowerStarIso
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).obj
        ((DerivedCategory.homologyFunctor _ q).obj
          (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
      (DerivedCategory.homologyFunctor _ q).obj (((f)_*[Ab.{u + 1}]).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).obj F))) :=
  (sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso F q) ≪≫
    (rightDerivedLowerStarSheafComposeForget₂Iso Λ f q).app F ≪≫
    (((f)_*[Ab.{u + 1}]).homologyRightDerivedFunctorObjSingleFunctorIso _ q).symm

end AlgebraicGeometry.ProEtale
