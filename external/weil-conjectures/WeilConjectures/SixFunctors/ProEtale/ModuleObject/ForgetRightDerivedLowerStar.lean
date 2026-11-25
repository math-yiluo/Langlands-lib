/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Derived pushforward of module objects on the underlying abelian sheaves

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The pushforward
`(f)_*⟦Λ⟧` of module objects over `Λ_X = condensedRingObj Λ X` is the pushforward of the
underlying abelian sheaves (`ProEtale.CondensedRing.lowerStar_comp_forget`). If `Λ_X` is flat as
an abelian sheaf, i.e. tensoring with `Λ_X` is left exact, the same holds for the derived
pushforwards:
```
R((f)_*⟦Λ⟧) ⋙ D(forget) ≅ D(forget) ⋙ R((f)_*[Ab])
```
on the unbounded derived categories
(`ProEtale.CondensedRing.rightDerivedLowerStarCompMapDerivedCategoryForgetIso`), and the base
change morphism of the bounded below derived pushforwards is an isomorphism
(`ProEtale.CondensedRing.isIso_rightDerivedLowerStarPlusForget`).

The point is that the forgetful functor `Mod_{Λ_X} ⥤ Sh(X_proét, Ab)` is right adjoint to the
free module functor `Λ_X ⊗ -` (`CategoryTheory.Mod.freeForgetAdjunction`), which is exact when
`Λ_X` is flat. Hence the forgetful functor preserves K-injective complexes and injective objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Flat

variable (X : Scheme.{u}) [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

instance : (Mod.free (condensedRingObj Λ X)).Additive :=
  (Mod.freeForgetAdjunction (condensedRingObj Λ X)).left_adjoint_additive

instance : PreservesFiniteColimits (Mod.free (condensedRingObj Λ X)) :=
  have := (Mod.freeForgetAdjunction (condensedRingObj Λ X)).leftAdjoint_preservesColimits
  inferInstance

/-- The free module functor `Λ_X ⊗ -` is exact when `Λ_X` is flat. -/
instance : PreservesFiniteLimits (Mod.free (condensedRingObj Λ X)) := by
  have : PreservesFiniteLimits
      (Mod.free (condensedRingObj Λ X) ⋙ Mod.forget (condensedRingObj Λ X)) :=
    inferInstanceAs (PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X)))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget (condensedRingObj Λ X))

/-- The forgetful functor from module objects over a flat `Λ_X` preserves K-injective complexes,
being right adjoint to the exact free module functor. -/
instance : (Mod.forget (D := Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)).PreservesKInjectiveComplexes :=
  (Mod.freeForgetAdjunction (condensedRingObj Λ X)).preservesKInjectiveComplexes

/-- The forgetful functor from module objects over a flat `Λ_X` preserves injective objects,
being right adjoint to the free module functor, which preserves monomorphisms. -/
instance : (Mod.forget (D := Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)).PreservesInjectiveObjects :=
  have : (Mod.free (condensedRingObj Λ X)).PreservesMonomorphisms := ⟨fun f _ ↦
    (Mod.forget (D := Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)).mono_of_mono_map
      ((tensorLeft (condensedRingObj Λ X)).map_mono f)⟩
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Mod.freeForgetAdjunction (condensedRingObj Λ X))

end Flat

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

/-- **The derived pushforward of module objects commutes with forgetting to abelian sheaves**:
if `Λ_X` is flat, then `(Rf_* K)_ab ≅ Rf_*(K_ab)` on the unbounded derived categories. -/
noncomputable def rightDerivedLowerStarCompMapDerivedCategoryForgetIso :
    R((f)_*⟦Λ⟧) ⋙ (Mod.forget (condensedRingObj Λ Y)).mapDerivedCategory ≅
      (Mod.forget (condensedRingObj Λ X)).mapDerivedCategory ⋙ R((f)_*[Ab.{u + 1}]) :=
  (Functor.isoWhiskerRight
      (Mod.forget (condensedRingObj Λ X)).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    (Functor.rightDerivedFunctorCompIso (Mod.forget (condensedRingObj Λ X)) _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) :
        Mod.forget (condensedRingObj Λ X) ⋙ (f)_*[Ab.{u + 1}] ≅
          (f)_*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y)) ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm

/-- The base change morphism `(R⁺f_* K)_ab ⟶ R⁺f_*(K_ab)` comparing the bounded below derived
pushforward of module objects with that of the underlying abelian sheaves. -/
noncomputable def rightDerivedLowerStarPlusForget :
    R+((f)_*⟦Λ⟧) ⋙ (Mod.forget (condensedRingObj Λ Y)).mapDerivedCategoryPlus ⟶
      (Mod.forget (condensedRingObj Λ X)).mapDerivedCategoryPlus ⋙
        R+((f)_*[Ab.{u + 1}]) :=
  Functor.rightDerivedFunctorPlusBaseChange (Iso.refl _ :
    (f)_*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y) ≅
      Mod.forget (condensedRingObj Λ X) ⋙ (f)_*[Ab.{u + 1}]).hom

/-- If `Λ_X` is flat, the comparison `(R⁺f_* K)_ab ⟶ R⁺f_*(K_ab)` is an isomorphism, the
underlying abelian sheaves of injective module objects being injective. -/
instance isIso_rightDerivedLowerStarPlusForget :
    IsIso (rightDerivedLowerStarPlusForget Λ f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun _ hI ↦
      have := (Mod.forget (condensedRingObj Λ X)).injective_obj_of_injective hI
      Functor.rightAcyclic_of_injective _

/-- If `Λ_X` is flat, `(R⁺f_* K)_ab ≅ R⁺f_*(K_ab)` on the bounded below derived categories. -/
noncomputable def rightDerivedLowerStarPlusForgetIso :
    R+((f)_*⟦Λ⟧) ⋙ (Mod.forget (condensedRingObj Λ Y)).mapDerivedCategoryPlus ≅
      (Mod.forget (condensedRingObj Λ X)).mapDerivedCategoryPlus ⋙
        R+((f)_*[Ab.{u + 1}]) :=
  asIso (rightDerivedLowerStarPlusForget Λ f)

end AlgebraicGeometry.ProEtale.CondensedRing
