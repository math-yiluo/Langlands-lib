/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar

/-!
# Derived pushforward of `ℓ`-adic sheaves on the underlying sheaves

Let `g : Z ⟶ Y` be a morphism of schemes. The pushforward `g_*` of sheaves of modules over the
constant `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.adicLowerStar`) is the pushforward of the
underlying sheaves of `ℚ̄_ℓ`-modules. This file shows that the same holds for the total derived
pushforwards: `Rg_* (M.X) ≅ (Rg_* M).X`
(`AlgebraicGeometry.ProEtale.mapDerivedCategoryForgetCompRightDerivedLowerStarIso`).

The point is that the forgetful functor from sheaves of `ℚ̄_ℓ,X`-modules to sheaves of
`ℚ̄_ℓ`-modules preserves K-injective complexes: it is right adjoint to the free functor
`ℚ̄_ℓ,X ⊗ -`, which is exact since every sheaf of modules over the field `ℚ̄_ℓ` is flat
(`AlgebraicGeometry.ProEtale.flat_sheaf_weilCoefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- Every pro-étale sheaf of `ℚ̄_ℓ`-modules is flat: it is the sheafification of its underlying
presheaf, whose values are vector spaces over the field `ℚ̄_ℓ`. -/
lemma flat_sheaf_weilCoefficients {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) : ObjectProperty.flat F := by
  have : EssentiallySmall.{u + 1} (Scheme.ProEt X) :=
    essentiallySmall_of_small_of_locallySmall _
  exact ObjectProperty.prop_of_iso _
    (asIso ((sheafificationAdjunction (Scheme.ProEt.topology X) _).counit.app F))
    (GrothendieckTopology.flat_presheafToSheaf_obj _ _ F.obj
      fun _ ↦ (ModuleCat.flat_iff_flat _).2 inferInstance)

instance (X : Scheme.{u}) : (Mod.free (adicConstantSheaf l X)).Additive :=
  (Mod.freeForgetAdjunction (adicConstantSheaf l X)).left_adjoint_additive

instance (X : Scheme.{u}) : PreservesFiniteColimits (Mod.free (adicConstantSheaf l X)) :=
  have := (Mod.freeForgetAdjunction (adicConstantSheaf l X)).leftAdjoint_preservesColimits
  inferInstance

/-- The free functor `ℚ̄_ℓ,X ⊗ -` to sheaves of `ℚ̄_ℓ,X`-modules is exact. -/
instance (X : Scheme.{u}) : PreservesFiniteLimits (Mod.free (adicConstantSheaf l X)) := by
  have : PreservesFiniteLimits (Mod.free (adicConstantSheaf l X) ⋙ AdicSheaf.forget X) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).1 (flat_sheaf_weilCoefficients _)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget X)

/-- The forgetful functor from sheaves of `ℚ̄_ℓ,X`-modules to sheaves of `ℚ̄_ℓ`-modules preserves
K-injective complexes, being right adjoint to the exact free functor. -/
instance (X : Scheme.{u}) : (AdicSheaf.forget (l := l) X).PreservesKInjectiveComplexes :=
  (Mod.freeForgetAdjunction (adicConstantSheaf l X)).preservesKInjectiveComplexes

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

variable (l) in
/-- The total derived pushforward of sheaves of `ℚ̄_ℓ,Z`-modules is the derived pushforward of
the underlying sheaves: `Rg_* (K.X) ≅ (Rg_* K).X`, since the pushforward of sheaves of
`ℚ̄_ℓ,Z`-modules is the pushforward of the underlying sheaves. -/
noncomputable def mapDerivedCategoryForgetCompRightDerivedLowerStarIso :
    (AdicSheaf.forget Z).mapDerivedCategory ⋙ ((g)_*[WeilCoefficients.{u} l]).rightDerivedFunctor ≅
      ((g)_*ᵃ[l]).rightDerivedFunctor ⋙ (AdicSheaf.forget Y).mapDerivedCategory :=
  Functor.isoWhiskerRight (AdicSheaf.forget Z).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    (Functor.rightDerivedFunctorCompIso (AdicSheaf.forget Z) _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) :
        AdicSheaf.forget Z ⋙ (g)_*[WeilCoefficients.{u} l] ≅ (g)_*ᵃ[l] ⋙ AdicSheaf.forget Y) ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _

end AlgebraicGeometry.ProEtale
