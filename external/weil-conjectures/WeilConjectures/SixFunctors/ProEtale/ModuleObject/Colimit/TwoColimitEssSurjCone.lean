/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.CategoryTheory.Triangulated.FunctorCone
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars

/-!
# Descent of bounded constructible `ℚ̄_ℓ`-complexes: the cone step

Let `ℓ` be a prime and `X` a scheme. A complex `K ∈ D(ℚ̄_ℓ,X)` *descends* to a finite
subextension (`ProEtale.descendsToPadicSubfield X ℓ K`) if `K ≅ T^X_{E,Ω} K_E` for some finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and some bounded constructible `K_E ∈ D(E_X)`.

This property is closed under isomorphisms and shifts, and, on a topologically noetherian `X`
and assuming **(Hom)**-surjectivity, under extensions: if `K' ⟶ K ⟶ K'' ⟶ K'[1]` is
distinguished and `K'`, `K''` descend, then so does `K`
(`ProEtale.descendsToPadicSubfield_obj₂`, the cone step of blueprint
`lemma-descent-finite-coefficient-field--2`). Indeed, the connecting morphism
`K'' ⟶ K'[1]`, transported, descends by (Hom) to some `δ_H` over a common finite subextension
`H`, and the cone of `δ_H` is bounded constructible and descends `K` by TR3 and the five lemma
(`CategoryTheory.Functor.exists_distinguished_iso_obj₂_of_iso`).

The extensions of scalars being exact, their left derived functors are isomorphic to the
triangulated functors `Functor.mapDerivedCategory`
(`Functor.leftDerivedFunctorIsoMapDerivedCategory`), through which they commute with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-- If `ε ≫ m ≫ θ = β₁⁻¹ ≫ F g ≫ β₂` for isomorphisms `β₁ : F X ≅ A`, `β₂ : F Y ≅ B`,
`ε : A ≅ P`, `θ : Q ≅ B`, then `F (g ≫ s) = (β₁ ≪≫ ε) ≫ m ≫ (θ ≪≫ β₂⁻¹ ≪≫ F s)` for every
isomorphism `s : Y ≅ Z`. -/
private lemma CategoryTheory.Functor.map_comp_hom_eq_of_eq_inv_comp {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) {X Y Z : C} {A B P Q : D} (g : X ⟶ Y) (s : Y ≅ Z)
    (β₁ : F.obj X ≅ A) (β₂ : F.obj Y ≅ B) (ε : A ≅ P) (m : P ⟶ Q) (θ : Q ≅ B)
    (h : ε.hom ≫ m ≫ θ.hom = β₁.inv ≫ F.map g ≫ β₂.hom) :
    F.map (g ≫ s.hom) = (β₁ ≪≫ ε).hom ≫ m ≫ (θ ≪≫ β₂.symm ≪≫ F.mapIso s).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% h]
  simp

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- A complex `K ∈ D(ℚ̄_ℓ,X)` *descends to a finite subextension* if `K ≅ T^X_{E,Ω} K_E` for some
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and some bounded constructible `K_E ∈ D(E_X)`. -/
def descendsToPadicSubfield :
    ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicAlgClRingObj X ℓ))) :=
  fun K ↦ ∃ (E : FiniteIntermediateField ℓ)
    (K' : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))),
    boundedConstructible _ K' ∧ Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K' ≅ K)

instance : (descendsToPadicSubfield X ℓ).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨E, K', hK', ⟨e'⟩⟩ ↦ ⟨E, K', hK', ⟨e' ≪≫ e⟩⟩

/-- The derived extension of scalars `T^X_{E,Ω}` is isomorphic to the triangulated functor
induced by the exact extension of scalars on complexes. -/
noncomputable abbrev derivedExtendScalarsToPadicAlgClIsoMapDerivedCategory
    (E : FiniteIntermediateField ℓ) :
    derivedExtendScalarsToPadicAlgCl X ℓ E ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory :=
  Functor.leftDerivedFunctorIsoMapDerivedCategory _

/-- The derived extension of scalars `T^X_{E,F}` is isomorphic to the triangulated functor
induced by the exact extension of scalars on complexes. -/
noncomputable abbrev derivedExtendScalarsSubfieldIsoMapDerivedCategory
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    derivedExtendScalarsSubfield X ℓ h ≅
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory :=
  Functor.leftDerivedFunctorIsoMapDerivedCategory _

/-- Descent is stable under the shifts: `T^X_{E,Ω}` commutes with the shifts, and bounded
constructible complexes are stable under the shifts. -/
instance [TopologicalSpace.NoetherianSpace X] :
    (descendsToPadicSubfield X ℓ).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ ⟨E, K', hK', ⟨e⟩⟩ ↦ ⟨E, K'⟦n⟧,
    (boundedConstructible _).le_shift n K' hK',
    ⟨Functor.commShiftObjIsoOfIso (derivedExtendScalarsToPadicAlgClIsoMapDerivedCategory X ℓ E)
      n K' ≪≫ (shiftFunctor _ n).mapIso e⟩⟩⟩

/-- A complex descending to `E` descends to every finite subextension `H ⊇ E`, through the
transitivity `T^X_{E,H} ⋙ T^X_{H,Ω} ≅ T^X_{E,Ω}`. -/
lemma exists_iso_derivedExtendScalarsToPadicAlgCl_obj_of_le {E H : FiniteIntermediateField ℓ}
    (h : E ≤ H)
    (K' : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))) (hK' : boundedConstructible _ K') :
    boundedConstructible _ ((derivedExtendScalarsSubfield X ℓ h).obj K') ∧
      Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ H).obj
        ((derivedExtendScalarsSubfield X ℓ h).obj K') ≅
          (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K') :=
  ⟨ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K' hK',
    ⟨(derivedExtendScalarsCompIso X ℓ h).app K'⟩⟩

/-- **The cone step** of blueprint `lemma-descent-finite-coefficient-field--2`: on a
topologically noetherian scheme, assuming (Hom)-surjectivity `hHom`, if `K' ⟶ K ⟶ K'' ⟶ K'[1]`
is distinguished in `D(ℚ̄_ℓ,X)` and `K'`, `K''` descend to finite subextensions, then so does
`K`. -/
theorem descendsToPadicSubfield_obj₂ [TopologicalSpace.NoetherianSpace X]
    (hHom : ∀ {E F : FiniteIntermediateField ℓ}
      (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ E))),
      boundedConstructible _ K →
      ∀ (L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ F))),
      boundedConstructible _ L →
      ∀ (f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K ⟶
        (derivedExtendScalarsToPadicAlgCl X ℓ F).obj L),
      ∃ (H : FiniteIntermediateField ℓ) (hE : E ≤ H) (hF : F ≤ H)
        (g : (derivedExtendScalarsSubfield X ℓ hE).obj K ⟶
          (derivedExtendScalarsSubfield X ℓ hF).obj L),
        f = (derivedExtendScalarsCompIso X ℓ hE).inv.app K ≫
          (derivedExtendScalarsToPadicAlgCl X ℓ H).map g ≫
            (derivedExtendScalarsCompIso X ℓ hF).hom.app L)
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicAlgClRingObj X ℓ))))
    (hT : T ∈ distTriang _) (h₁ : descendsToPadicSubfield X ℓ T.obj₁)
    (h₃ : descendsToPadicSubfield X ℓ T.obj₃) : descendsToPadicSubfield X ℓ T.obj₂ := by
  obtain ⟨E, a, ha, ⟨ea⟩⟩ := h₁
  obtain ⟨F, c, hc, ⟨ec⟩⟩ := h₃
  let θ : T.obj₁⟦(1 : ℤ)⟧ ≅ (derivedExtendScalarsToPadicAlgCl X ℓ E).obj (a⟦(1 : ℤ)⟧) :=
    (shiftFunctor _ (1 : ℤ)).mapIso ea.symm ≪≫ (Functor.commShiftObjIsoOfIso
      (derivedExtendScalarsToPadicAlgClIsoMapDerivedCategory X ℓ E) (1 : ℤ) a).symm
  obtain ⟨H, hF, hE, g, hg⟩ := hHom c hc (a⟦(1 : ℤ)⟧)
    ((boundedConstructible _).le_shift (1 : ℤ) a ha) (ec.hom ≫ T.mor₃ ≫ θ.hom)
  let s : (derivedExtendScalarsSubfield X ℓ hE).obj (a⟦(1 : ℤ)⟧) ≅
      ((derivedExtendScalarsSubfield X ℓ hE).obj a)⟦(1 : ℤ)⟧ :=
    Functor.commShiftObjIsoOfIso (derivedExtendScalarsSubfieldIsoMapDerivedCategory X ℓ hE)
      (1 : ℤ) a
  obtain ⟨b, f, g', hfg, ⟨eb⟩⟩ := Functor.exists_distinguished_iso_obj₂_of_iso
    (derivedExtendScalarsToPadicAlgClIsoMapDerivedCategory X ℓ H) T hT (g ≫ s.hom)
    ((derivedExtendScalarsCompIso X ℓ hF).app c ≪≫ ec)
    (θ ≪≫ ((derivedExtendScalarsCompIso X ℓ hE).app (a⟦(1 : ℤ)⟧)).symm ≪≫
      (derivedExtendScalarsToPadicAlgCl X ℓ H).mapIso s)
    (Functor.map_comp_hom_eq_of_eq_inv_comp _ g s ((derivedExtendScalarsCompIso X ℓ hF).app c)
      ((derivedExtendScalarsCompIso X ℓ hE).app (a⟦(1 : ℤ)⟧)) ec T.mor₃ θ hg)
  refine ⟨H, b, ?_, ⟨eb⟩⟩
  exact (boundedConstructible _).ext_of_isTriangulatedClosed₂ _ hfg
    (ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ _ a ha)
    (ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ _ c hc)

end AlgebraicGeometry.ProEtale
