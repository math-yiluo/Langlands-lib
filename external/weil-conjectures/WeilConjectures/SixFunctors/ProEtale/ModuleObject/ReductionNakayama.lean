/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleNakayama
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.IsZeroOfIsIsoZSMul
public import WeilConjectures.CategoryTheory.Sites.SheafModuleZSMul

/-!

# Derived Nakayama for bounded constructible `𝒪_E`-complexes

Let `X` be a noetherian scheme and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`. A morphism of
bounded constructible `𝒪_E`-complexes on `X_proét` is an isomorphism as soon as its first derived
reduction `K ↦ K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` is one (`ProEtale.isIso_of_isIso_derivedReduction_map`,
blueprint `lemma-reduction-derived-nakayama`).

The mapping cone `C` of such a morphism is bounded constructible, and its derived reduction
vanishes. A bounded complex whose derived extension of scalars vanishes and whose cohomology
objects satisfy the abelian Nakayama lemma is zero
(`CategoryTheory.Mod.isZero_of_isZero_leftDerivedFunctor_extendScalars`), and the cohomology
sheaves of `C` are constructible `𝒪_{E,X}`-modules, for which the abelian Nakayama lemma holds
(`ProEtale.isZero_of_isConstructibleModuleObject_of_isZero_extendScalars`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The derived extension of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` inverts every morphism which the
derived reduction `ProEtale.derivedReduction` inverts: regarding an `𝔽_{E,X}`-module object as a
sheaf of `𝔽_E`-modules is exact and reflects isomorphisms. -/
lemma isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (f : K ⟶ L)
    (h : IsIso ((derivedReduction X ℓ E).map f)) :
    IsIso ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map f) := by
  rw [DerivedCategory.isIso_iff] at h ⊢
  intro n
  have hn : IsIso (((residueFieldModuleSheaf X ℓ E).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor _ n).map
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map f)) := h n
  have h' : IsIso ((residueFieldModuleSheaf X ℓ E).map ((DerivedCategory.homologyFunctor _ n).map
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map f))) :=
    (NatIso.isIso_map_iff
      ((residueFieldModuleSheaf X ℓ E).mapDerivedCategoryHomologyFunctorIso n) _).2 hn
  exact isIso_of_reflects_iso _ (residueFieldModuleSheaf X ℓ E)

/-- The shift structure on the derived extension of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` induced
by its right adjoint, the derived restriction of scalars. -/
noncomputable instance commShift_leftDerivedFunctor_extendScalars_residueField :
    (Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.CommShift ℤ :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (padicIntegersToResidueField X ℓ E)).leftAdjointCommShift ℤ

/-- The derived extension of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` is a triangulated functor, being
left adjoint to the triangulated derived restriction of scalars. -/
instance isTriangulated_leftDerivedFunctor_extendScalars_residueField :
    (Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.IsTriangulated :=
  have := (Mod.derivedExtendMapDerivedCategoryAdjunction
    (padicIntegersToResidueField X ℓ E)).commShift_of_rightAdjoint ℤ
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (padicIntegersToResidueField X ℓ E)).isTriangulated_leftAdjoint

variable [IsNoetherian X]

/-- Blueprint `lemma-reduction-derived-nakayama` (section `chap-The-pro-etale-site`): a morphism
between derived complete `𝒪_{E,X}`-complexes is an isomorphism whenever its first derived
reduction `K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` is one. Here it is proved for bounded constructible
`𝒪_E`-complexes on a noetherian scheme. -/
theorem isIso_of_isIso_derivedReduction_map
    {K L : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (φ : K ⟶ L)
    (h : IsIso ((derivedReduction X ℓ E).map ((boundedConstructible _).ι.map φ))) :
    IsIso φ := by
  have := isTriangulated_boundedConstructible_padicIntegersRingObj X ℓ E
  suffices IsIso ((boundedConstructible _).ι.map φ) from
    isIso_of_reflects_iso φ (boundedConstructible _).ι
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle ((boundedConstructible _).ι.map φ)
  have hC : boundedConstructible _ C :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT K.property L.property
  have hF := (Mod.extendScalars
    (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_distinguished _ hT
  have hiso := isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map X ℓ E _ h
  have hz :
      IsZero ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ hF).2 hiso
  have hCz : IsZero C :=
    Mod.isZero_of_isZero_leftDerivedFunctor_extendScalars _ (IsConstructibleModuleObject _)
      (fun M hM hM' ↦ isZero_of_isConstructibleModuleObject_of_isZero_extendScalars ℓ E M hM hM')
      C hC.1 hC.2 hz
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hCz

/-- A bounded constructible `𝒪_E`-complex on a noetherian scheme on which `ℓⁿ` acts invertibly,
`n ≠ 0`, is zero: `ℓ` acts by zero on its first derived reduction, which therefore vanishes, so
`K = 0` by derived Nakayama (`isIso_of_isIso_derivedReduction_map`). -/
theorem isZero_of_isIso_pow_zsmul_id {n : ℕ} (hn : n ≠ 0)
    {K : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hK : IsIso (((ℓ : ℤ) ^ n) • 𝟙 K.obj)) : IsZero K := by
  have hK₁ : IsZero ((derivedReduction X ℓ E).obj K.obj) := by
    refine DerivedCategory.isZero_of_isIso_zsmul_id
      (Sheaf.zsmul_id_eq_zero_of_intCast_eq_zero ?_) (m := (ℓ : ℤ) ^ n) ?_
    · rw [Int.cast_pow, Int.cast_natCast, natCast_eq_zero_residueFieldCoeff, zero_pow hn]
    · have : (derivedReduction X ℓ E).Additive := inferInstanceAs (Functor.Additive (_ ⋙ _))
      rw [← (derivedReduction X ℓ E).map_id, ← Functor.map_zsmul]
      infer_instance
  have := isIso_of_isIso_derivedReduction_map X ℓ E (0 : K ⟶ K) (hK₁.isIso hK₁ _)
  exact IsZero.of_mono_zero K K

end AlgebraicGeometry.ProEtale
