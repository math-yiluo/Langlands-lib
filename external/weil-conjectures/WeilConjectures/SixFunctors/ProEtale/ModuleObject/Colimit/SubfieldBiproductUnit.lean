/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsBiproductUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsBasis
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldExtendRestrictBiproduct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteCondensed

/-!
# The basis decomposition of `Res (F ⊗ᴸ K)` on bounded constructible complexes

For finite subextensions `E ≤ F` and an `E`-basis `b` of `F`, the maps
`K ⟶ Res (F_X ⊗ᴸ K)`, `m ↦ bᵢ ⊗ m` (the unit of extension and restriction of scalars followed by
multiplication by `bᵢ`) exhibit `Res (F_X ⊗ᴸ K)` as the direct sum of `d` copies of `K`.

The proof goes in three steps:
* on the condensed rings, the map `E̲ᵈ ⟶ F̲`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism
  (`Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`), and so
  is its pullback `E_Xᵈ ⟶ F_X` along `p_X^*`
  (`ProEtale.isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`);
* hence the maps `M ⟶ Res (F_X ⊗ M)`, `m ↦ bᵢ ⊗ m`, decompose `Res (F_X ⊗ M)` for every
  `E_X`-module `M` (`CategoryTheory.Mod.isIso_biproductDesc_extendUnit_smul`), and the same holds
  on the derived category, extension of scalars being exact
  (`CategoryTheory.Mod.isIso_biproductDesc_derivedUnit_smul`);
* the bounded constructible complexes form a full subcategory.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

section Basis

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- If `E_Xᵈ ⟶ F_X`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism, then for every `E_X`-module `M` the
maps `M ⟶ Res (F_X ⊗ M)`, `m ↦ bᵢ ⊗ m`, exhibit `Res (F_X ⊗ M)` as `Mᵈ`. -/
theorem isIso_biproductDesc_extendRestrictScalarsSubfield_unit_smul (X : Scheme.{u}) {d : ℕ}
    (b : Fin d → F)
    (hb : IsIso (biproduct.desc fun i : Fin d ↦ padicSubfieldRingObjMap X ℓ h ≫
      Mod.globalSmul (padicSubfieldConstRingHom ℓ F X (b i)).hom (Mod.regular _)))
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :
    IsIso (biproduct.desc fun i : Fin d ↦
      (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h)).unit.app M ≫
        (Mod.comap (padicSubfieldRingObjMap X ℓ h)).map
          (b i • 𝟙 ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj M))) := by
  simp only [Mod.linearOfRingHom_smul_id]
  exact Mod.isIso_biproductDesc_extendUnit_smul _
    (fun i ↦ (padicSubfieldConstRingHom ℓ F X (b i)).hom) hb M

/-- If `E_Xᵈ ⟶ F_X`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism, then for every complex `K` in the
derived category of `E_X`-modules, the maps `K ⟶ Res (F_X ⊗ᴸ K)`, `m ↦ bᵢ ⊗ m`, exhibit
`Res (F_X ⊗ᴸ K)` as `Kᵈ`. -/
theorem isIso_biproductDesc_derivedExtendRestrictScalarsSubfield_unit_smul (X : Scheme.{u})
    {d : ℕ} (b : Fin d → F)
    (hb : IsIso (biproduct.desc fun i : Fin d ↦ padicSubfieldRingObjMap X ℓ h ≫
      Mod.globalSmul (padicSubfieldConstRingHom ℓ F X (b i)).hom (Mod.regular _)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))) :
    IsIso (biproduct.desc fun i : Fin d ↦
      (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h)).unit.app K ≫
        (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory.map
          (b i • 𝟙 ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctor.obj
            K))) :=
  Mod.isIso_biproductDesc_derivedUnit_smul _ b
    (isIso_biproductDesc_extendRestrictScalarsSubfield_unit_smul ℓ h X b hb) K
end Basis

/-- On bounded constructible complexes, the maps `K ⟶ Res (F_X ⊗ᴸ K)`, `m ↦ bᵢ ⊗ m`, are the maps
of the unbounded derived category: they exhibit `Res (F_X ⊗ᴸ K)` as `Kᵈ` as soon as they do on
the underlying complexes. -/
theorem isIso_biproductDesc_boundedConstructibleExtendRestrictScalarsSubfield_unit_smul
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] {d : ℕ} (b : Fin d → F)
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧)
    (hK : IsIso (biproduct.desc fun i : Fin d ↦
      (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h)).unit.app
          K.obj ≫
        (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory.map
          (b i • 𝟙 ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctor.obj
            K.obj)))) :
    IsIso (biproduct.desc fun i : Fin d ↦
      (boundedConstructibleExtendRestrictScalarsSubfieldAdjunction X ℓ h).unit.app K ≫
        (boundedConstructibleRestrictScalarsSubfield X ℓ h).map
          (b i • 𝟙 ((boundedConstructibleExtendScalarsSubfield X ℓ h).obj K))) := by
  have G := Adjunction.isIso_biproductDesc_restrictFullyFaithful_unit_smul_iff
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h))
    (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K)
    (fun K ↦ boundedConstructible_restrictScalarsSubfield_obj X ℓ h K.obj K.property) b K
  unfold boundedConstructibleExtendRestrictScalarsSubfieldAdjunction
    boundedConstructibleExtendScalarsSubfieldCompatibility
    boundedConstructibleRestrictScalarsSubfieldCompatibility
    boundedConstructibleRestrictScalarsSubfield boundedConstructibleExtendScalarsSubfield
    constructibleExtendScalars
  with_reducible_and_instances exact G.2 hK

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts in
/-- For finite subextensions `E ≤ F`, there is a family `b : Fin d → F` (an `E`-basis of `F`)
such that for every scheme `X` and every bounded constructible `E_X`-complex `K`, the maps
`K ⟶ Res (F_X ⊗ᴸ K)` given by the unit followed by multiplication by `bᵢ` exhibit
`Res (F_X ⊗ᴸ K)` as the direct sum of `d` copies of `K`. -/
theorem exists_isIso_biproductDesc_unit_smul :
    ∃ (d : ℕ) (b : Fin d → F), ∀ (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
      (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧),
      IsIso (biproduct.desc fun i : Fin d ↦
        (boundedConstructibleExtendRestrictScalarsSubfieldAdjunction X ℓ h).unit.app K ≫
          (boundedConstructibleRestrictScalarsSubfield X ℓ h).map
            (b i • 𝟙 ((boundedConstructibleExtendScalarsSubfield X ℓ h).obj K))) := by
  have H := Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul.{u} ℓ h
  obtain ⟨d, b, hb⟩ := H
  refine ⟨d, b, fun X _ K ↦ ?_⟩
  have h₁ : IsIso (biproduct.desc fun i : Fin d ↦ padicSubfieldRingObjMap X ℓ h ≫
      Mod.globalSmul (padicSubfieldConstRingHom ℓ F X (b i)).hom (Mod.regular _)) :=
    ProEtale.isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul X ℓ h b hb
  have h₂ := isIso_biproductDesc_derivedExtendRestrictScalarsSubfield_unit_smul ℓ h X b h₁ K.obj
  have h₃ :=
    isIso_biproductDesc_boundedConstructibleExtendRestrictScalarsSubfield_unit_smul ℓ h X b K h₂
  with_reducible exact h₃

end AlgebraicGeometry.ProEtale.CondensedRing
