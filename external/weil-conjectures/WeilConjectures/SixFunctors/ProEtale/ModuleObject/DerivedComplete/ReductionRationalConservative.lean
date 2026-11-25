/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralAcyclic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndDerived

/-!
# An `𝒪_E`-complex with vanishing reduction and vanishing rationalization is zero

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and
residue field `𝔽_E`, and `X` a scheme. For `C₀ ∈ D(X_proét, 𝒪_E)`, if both `𝔽_E ⊗ᴸ_{𝒪_E} C₀` and
`ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} C₀)` vanish, then `C₀ = 0`
(`AlgebraicGeometry.ProEtale.CondensedRing.isZero_of_isZero_extendScalars_residueField_padicAlgCl`;
a variant with the first derived reduction is
`AlgebraicGeometry.ProEtale.CondensedRing.isZero_of_isZero_derivedReduction_of_isZero_padicAlgCl`).

Indeed:
1. the derived extension of scalars `ℚ̄_ℓ ⊗ᴸ_E -` is faithful
   (`AlgebraicGeometry.ProEtale.faithful_derivedExtendScalarsToPadicAlgCl`), hence reflects zero
   objects, so `E ⊗ᴸ_{𝒪_E} C₀ = 0`;
2. as the reduction `𝔽_E ⊗ᴸ_{𝒪_E} C₀` vanishes, `ℓ` acts invertibly on `C₀`
   (`AlgebraicGeometry.ProEtale.isIso_zsmul_id_of_isZero_derivedReduction`), hence on every
   cohomology object `Hⁿ(C₀)`;
3. the extension of scalars `E ⊗_{𝒪_E} -` is exact, so `0 = Hⁿ(E ⊗ᴸ_{𝒪_E} C₀) ≅ E ⊗_{𝒪_E} Hⁿ(C₀)`,
   and the underlying abelian sheaf of `E ⊗_{𝒪_E} M` is the sequential colimit
   `colim(M --ℓ--> M --ℓ--> ⋯)`
   (`AlgebraicGeometry.ProEtale.isColimitPadicIntegersExtendScalarsCocone`).
   When `ℓ` acts invertibly on `M`, the powers of `ℓ⁻¹` form a cocone `M` under this sequence
   whose first leg is the identity, so `𝟙 M` factors through the colimit
   (`CategoryTheory.Mod.isZero_of_isColimit_smulSequence_of_isIso`). Hence `Hⁿ(C₀) = 0` for every
   `n`, and `C₀ = 0`.
-/

@[expose] public section

universe v u


open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- A faithful functor preserving zero morphisms reflects zero objects. -/
lemma Functor.isZero_of_isZero_obj_of_faithful {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful]
    {Y : C} (h : IsZero (F.obj Y)) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero]
  refine F.zero_of_map_zero _ ?_
  rw [Functor.map_id]
  exact h.eq_of_src _ _

namespace Mod

variable {C : Type*} [Category.{v} C] [Preadditive C]

/-- If `n` acts invertibly on `X`, an object with a zero colimit cocone over the sequence
`X --n--> X --n--> ⋯` is zero: the powers of `n⁻¹` form a cocone `X` under the sequence whose first
leg is `𝟙 X`, so `𝟙 X` factors through the zero colimit. -/
lemma isZero_of_isColimit_smulSequence_of_isIso {X : C} {n : ℕ} [IsIso (n • 𝟙 X)]
    {t : Cocone (smulSequence X n)} (ht : IsColimit t) (h : IsZero t.pt) : IsZero X := by
  let c (k : ℕ) : X ⟶ X := Nat.rec (𝟙 X) (fun _ f ↦ f ≫ inv (n • 𝟙 X)) k
  have hc (k : ℕ) : n • c (k + 1) = c k := by
    rw [← Category.comp_id (c (k + 1)), ← Preadditive.comp_nsmul]
    exact (Category.assoc _ _ _).trans ((c k ≫= IsIso.inv_hom_id _).trans (Category.comp_id _))
  have h0 : c 0 = 𝟙 X := rfl
  rw [IsZero.iff_id_eq_zero, ← h0]
  exact ((ht.fac (smulSequenceCocone n c hc) 0).symm.trans
    ((t.ι.app 0) ≫= h.eq_of_src _ _)).trans comp_zero

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {X : Scheme.{u}}

-- The instance arguments of `Functor.leftDerivedFunctorIsoMapDerivedCategory` for the extension
-- of scalars along `𝒪_{E,X} ⟶ E_X` take long to unify.
/-- **Conservativity of reduction and rationalization, via `derivedReduction`**: an
`𝒪_E`-complex `C₀` on `X_proét` whose first derived reduction and rationalization
`ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} C₀)` both vanish is zero. -/
theorem isZero_of_isZero_derivedReduction_of_isZero_padicAlgCl
    (C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (h₁ : IsZero ((derivedReduction X ℓ E.1).obj C₀))
    (h₂ : IsZero ((Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          X)).leftDerivedFunctor.obj C₀))) :
    IsZero C₀ := by
  have hE : IsZero ((Mod.extendScalars (coefficientMap
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj C₀) := by
    have := (Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).isLeftAdjoint
    exact (derivedExtendScalarsToPadicAlgCl X ℓ E).isZero_of_isZero_obj_of_faithful h₂
  have hℓ := isIso_zsmul_id_of_isZero_derivedReduction X ℓ E C₀ h₁
  refine DerivedCategory.isZero_of_forall_isZero_homology _ fun n ↦ ?_
  let F := Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)
  have hF : IsZero ((DerivedCategory.homologyFunctor _ n).obj (F.mapDerivedCategory.obj C₀)) :=
    (DerivedCategory.homologyFunctor _ n).map_isZero
      (hE.of_iso (F.leftDerivedFunctorIsoMapDerivedCategory.app C₀).symm)
  have hM : IsZero (F.obj ((DerivedCategory.homologyFunctor _ n).obj C₀)) :=
    hF.of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app C₀)
  have : IsIso (ℓ • 𝟙 ((DerivedCategory.homologyFunctor _ n).obj C₀).X) := by
    have h := (DerivedCategory.homologyFunctor _ n ⋙ Mod.forget _).map_isIso ((ℓ : ℤ) • 𝟙 C₀)
    rwa [Functor.map_zsmul, CategoryTheory.Functor.map_id, natCast_zsmul] at h
  have hX := Mod.isZero_of_isColimit_smulSequence_of_isIso
    (isColimitPadicIntegersExtendScalarsCocone ℓ E X ((DerivedCategory.homologyFunctor _ n).obj C₀))
    ((Mod.forget _).map_isZero hM)
  exact (Mod.forget _).isZero_of_isZero_obj_of_faithful hX

/-- **Conservativity of reduction and rationalization**: an `𝒪_E`-complex `C₀` on `X_proét` whose
reduction `𝔽_E ⊗ᴸ_{𝒪_E} C₀` and rationalization `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} C₀)` both vanish is
zero. -/
theorem isZero_of_isZero_extendScalars_residueField_padicAlgCl
    (C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (h₁ : IsZero ((Mod.extendScalars (coefficientMap
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj C₀))
    (h₂ : IsZero ((Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          X)).leftDerivedFunctor.obj C₀))) :
    IsZero C₀ :=
  isZero_of_isZero_derivedReduction_of_isZero_padicAlgCl ℓ E C₀
    ((residueFieldModuleSheaf X ℓ E.1).mapDerivedCategory.map_isZero h₁) h₂

end AlgebraicGeometry.ProEtale.CondensedRing
