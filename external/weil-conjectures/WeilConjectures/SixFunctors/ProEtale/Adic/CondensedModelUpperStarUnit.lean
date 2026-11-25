/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelScalars

/-!
# Pullbacks of the unit in the two models of ℓ-adic sheaves

The comparison of the pullbacks of the two models is compatible with the identifications `g^*
ℚ̄_ℓ ≅ ℚ̄_ℓ` of the units.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

open MonObj

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- A monoid isomorphism `φ : M ≅ B` identifies the regular `B`-module, viewed as an `M`-module
along `φ`, with the regular `M`-module. -/
noncomputable def comapRegularIso {M B : C} [MonObj M] [MonObj B] (φ : M ≅ B)
    [IsMonHom φ.hom] : (comap φ.hom).obj (regular B) ≅ regular M :=
  isoMk φ.symm (by
    change (φ.hom ▷ B ≫ μ[B]) ≫ φ.inv = M ◁ φ.inv ≫ μ[M]
    rw [Category.assoc, ← cancel_mono φ.hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.assoc, IsMonHom.mul_hom, tensorHom_def', Category.assoc,
      ← whiskerLeft_comp_assoc,
      Iso.inv_hom_id, whiskerLeft_id, Category.id_comp])

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The unit `ℓ`-adic sheaf corresponds to the unit module object over `Λ_X`. -/
noncomputable def adicSheafEquivCondensedModTensorUnitIso :
    (adicSheafEquivCondensedMod l X).functor.obj (AdicSheaf.unit l X) ≅
      𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  Mod.comapRegularIso (condensedRingObjIsoForgetAb l X)

variable {l X} {Y : Scheme.{u}}

/-- The adjoint `ℚ̄_ℓ,X ⟶ f_* ℚ̄_ℓ,Y` of the unit comparison of the pullback of
`ℓ`-adic sheaves is
the canonical morphism. -/
lemma adicUpperStarLowerStarAdjunction_unit_app_unit_comp_map_adicUpperStarUnitIso_hom_hom
    (f : Y ⟶ X) :
    ((adicUpperStarLowerStarAdjunction l f).unit.app (AdicSheaf.unit l X) ≫
      (f)_*ᵃ[l].map (adicUpperStarUnitIso l f).hom).hom = adicConstantSheafToLowerStar l f := by
  rw [Mod.comp_hom', adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom,
    adicLowerStar_map_hom, adicUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
  exact ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **The pullback compatibility of the two models is compatible with the units.** -/
theorem upperStar_map_inv_comp_adicUpperStarCompCondensedModIso_inv_app_unit (f : Y ⟶ X) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
        (adicSheafEquivCondensedModTensorUnitIso l X).inv ≫
      (adicUpperStarCompCondensedModIso l f).inv.app (AdicSheaf.unit l X) ≫
      (adicSheafEquivCondensedMod l Y).functor.map (adicUpperStarUnitIso l f).hom ≫
      (adicSheafEquivCondensedModTensorUnitIso l Y).hom =
      (Functor.Monoidal.εIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)).inv := by
  have nat := (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      f).unit.naturality
    (adicSheafEquivCondensedModTensorUnitIso l X).inv
  have U := unit_app_comp_map_conjugateIsoEquiv_symm_inv_app (adicUpperStarLowerStarAdjunction l f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
    (adicSheafEquivCondensedMod l X) (adicSheafEquivCondensedMod l Y)
    (adicLowerStarCompCondensedModIso l f) (condensedModInverseCompAdicLowerStarIso l f)
    (fun b ↦ by
      rw [condensedModInverseCompAdicLowerStarIso]
      exact inverseCompIso_hom_app _ _ _ b) (AdicSheaf.unit l X)
  have dn := (adicLowerStarCompCondensedModIso l f).hom.naturality (adicUpperStarUnitIso l f).hom
  simp only [Functor.id_map, Functor.comp_map] at nat dn
  have key : (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f).unit.app
        (𝟙_ _) ≫
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
          (adicSheafEquivCondensedModTensorUnitIso l X).inv ≫
        (adicUpperStarCompCondensedModIso l f).inv.app (AdicSheaf.unit l X) ≫
        (adicSheafEquivCondensedMod l Y).functor.map (adicUpperStarUnitIso l f).hom ≫
        (adicSheafEquivCondensedModTensorUnitIso l Y).hom) =
      (adicSheafEquivCondensedModTensorUnitIso l X).inv ≫
        (adicSheafEquivCondensedMod l X).functor.map
          ((adicUpperStarLowerStarAdjunction l f).unit.app (AdicSheaf.unit l X) ≫
            (f)_*ᵃ[l].map (adicUpperStarUnitIso l f).hom) ≫
        (adicLowerStarCompCondensedModIso l f).hom.app (AdicSheaf.unit l Y) ≫
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).map
          (adicSheafEquivCondensedModTensorUnitIso l Y).hom := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% nat]
    erw [reassoc_of% U]
    rw [reassoc_of% dn]
  apply ((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f).homEquiv
    _ _).injective
  apply Mod.hom_ext
  rw [CondensedRing.homEquiv_εIso_inv_hom, Adjunction.homEquiv_unit, key, Mod.comp_hom',
    Mod.comp_hom', Mod.comp_hom', adicLowerStarCompCondensedModIso_hom_app_hom,
    CondensedRing.lowerStar_map_hom]
  have h₁ : (adicSheafEquivCondensedModTensorUnitIso l X).inv.hom =
      (condensedRingObjIsoForgetAb l X).hom := rfl
  have h₂ : ((adicSheafEquivCondensedMod l X).functor.map
      ((adicUpperStarLowerStarAdjunction l f).unit.app (AdicSheaf.unit l X) ≫
        (f)_*ᵃ[l].map (adicUpperStarUnitIso l f).hom)).hom =
      (weilCoefficientsForgetAb l X).map
        ((adicUpperStarLowerStarAdjunction l f).unit.app (AdicSheaf.unit l X) ≫
          (f)_*ᵃ[l].map (adicUpperStarUnitIso l f).hom).hom := rfl
  have h₃ : (adicSheafEquivCondensedModTensorUnitIso l Y).hom.hom =
      (condensedRingObjIsoForgetAb l Y).inv := rfl
  rw [h₁, h₂, h₃,
      adicUpperStarLowerStarAdjunction_unit_app_unit_comp_map_adicUpperStarUnitIso_hom_hom,
    ]
  erw [Category.id_comp]
  rw [← Category.assoc, ← condensedPushforwardHom_comp_map_condensedRingObjIsoForgetAb_hom,
    Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

lemma adicSheafEquivCondensedModTensorUnitIso_hom_hom :
    (adicSheafEquivCondensedModTensorUnitIso l X).hom.hom =
      (condensedRingObjIsoForgetAb l X).inv := rfl

lemma adicSheafEquivCondensedModTensorUnitIso_inv_hom :
    (adicSheafEquivCondensedModTensorUnitIso l X).inv.hom =
      (condensedRingObjIsoForgetAb l X).hom := rfl

end AlgebraicGeometry.ProEtale
