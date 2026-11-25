/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Exact
public import WeilConjectures.WeilSheaf.FieldCoefficientTriangulated
public import WeilConjectures.WeilSheaf.Localization

/-!
# The forgetful functor of `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)` is exact

The extensions of scalars `ℚ̄_ℓ ⊗_E - : D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)` are triangulated,
and their compatibilities `ℚ̄_ℓ ⊗_F (F ⊗_E -) ≅ ℚ̄_ℓ ⊗_E -` commute with the shifts. Hence the
comparison functor `AlgebraicGeometry.WeilComplexTwoColimit.toWeilComplex` from the `2`-colimit
is triangulated (`CategoryTheory.StageSystem.descFunctor_isTriangulated`), and so is the
forgetful functor `For : D^b_{c,W}(X, ℚ̄_ℓ) ⥤ D^b_c(X̄, ℚ̄_ℓ)`
(`AlgebraicGeometry.WeilComplexTwoColimit.forgetBoundedConstructibleAdic`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))] [Fact (ringChar k₀ ≠ l)]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

namespace FieldWeilComplex

section ToAdic

variable {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ] [NormedField Λ']
  [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ'] [FiniteDimensional ℚ_[l] Λ]
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'} (he : Continuous e)
  (hc : Continuous (algebraMap ℚ_[l] Λ)) {e' : Λ' →ₐ[ℚ_[l]] PadicAlgCl l} (he' : Continuous e')
  (hc' : Continuous (algebraMap ℚ_[l] Λ'))

/-- The extension of scalars `D^b_{c,W}(X, Λ) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)` commutes with the shifts. -/
noncomputable instance extendScalarsToAdic_commShift :
    (FieldWeilComplex.extendScalarsToAdic he' hc' k₀ X).CommShift ℤ := by
  dsimp only [FieldWeilComplex.extendScalarsToAdic]
  exact ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- The extension of scalars `D^b_{c,W}(X, Λ) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)` is triangulated. -/
instance extendScalarsToAdic_isTriangulated :
    (FieldWeilComplex.extendScalarsToAdic he' hc' k₀ X).IsTriangulated := by
  dsimp only [FieldWeilComplex.extendScalarsToAdic]
  exact ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

/-- The compatibility `ℚ̄_ℓ ⊗_{Λ'} (Λ' ⊗_Λ -) ≅ ℚ̄_ℓ ⊗_Λ -` commutes with the shifts. -/
instance extendScalarsCompExtendScalarsToAdicIso_commShift :
    NatTrans.CommShift
      (FieldWeilComplex.extendScalarsCompExtendScalarsToAdicIso he hc he' hc' k₀ X).hom ℤ :=
  ObjectProperty.natTransCommShift_liftFullSubcategory _ _ _ _ _ _
    (Functor.mapDerivedCategoryCompNatIso
      (ProEtaleFieldWeilSheaf.extendScalarsCompExtendScalarsToAdicIso he hc he' hc' k₀ X)).hom _
    (fun _ ↦ rfl)

end ToAdic

noncomputable instance toWeilComplex_commShift (E : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] E] : (FieldWeilComplex.toWeilComplex k₀ X E).CommShift ℤ := by
  dsimp only [FieldWeilComplex.toWeilComplex]
  infer_instance

instance toWeilComplex_isTriangulated (E : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] E] : (FieldWeilComplex.toWeilComplex k₀ X E).IsTriangulated := by
  dsimp only [FieldWeilComplex.toWeilComplex]
  infer_instance

noncomputable instance cocone_T_commShift {E F : FiniteIntermediateField l} (h : E ≤ F) :
    ((FieldWeilComplex.cocone k₀ X).T h).CommShift ℤ :=
  inferInstanceAs (((stageSystem (l := l) k₀ X).T h).CommShift ℤ)

noncomputable instance cocone_Φ_commShift (E : FiniteIntermediateField l) :
    ((FieldWeilComplex.cocone k₀ X).Φ E).CommShift ℤ :=
  inferInstanceAs ((FieldWeilComplex.toWeilComplex k₀ X E.1).CommShift ℤ)

instance cocone_iso_commShift {E F : FiniteIntermediateField l} (h : E ≤ F) :
    NatTrans.CommShift ((FieldWeilComplex.cocone k₀ X).iso h).hom ℤ :=
  extendScalarsCompExtendScalarsToAdicIso_commShift k₀ X (e' := F.1.val)
    (he := continuous_inclusion_finiteIntermediateField h)
    (hc := continuous_algebraMap_intermediateField _) (he' := continuous_subtype_val)
    (hc' := continuous_algebraMap_intermediateField _)

end FieldWeilComplex

namespace WeilComplexTwoColimit

/-- The comparison functor `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E) ⥤ WeilComplex k₀ l X`
commutes with the shifts. -/
noncomputable instance toWeilComplex_commShift : (toWeilComplex (l := l) k₀ X).CommShift ℤ :=
  StageSystem.descFunctor_commShift _ _ _

/-- The comparison functor `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E) ⥤ WeilComplex k₀ l X`
is triangulated. -/
instance toWeilComplex_isTriangulated : (toWeilComplex (l := l) k₀ X).IsTriangulated :=
  StageSystem.descFunctor_isTriangulated _ _ _

/-- Blueprint `definition-weil-structure`: the exact forgetful functor
`For : D^b_{c,W}(X, ℚ̄_ℓ) ⥤ D^b_c(X̄, ℚ̄_ℓ)` of the `2`-colimit model, `(E, K) ↦ For(ℚ̄_ℓ ⊗_E K)`,
with values in `D^b_c(X̄, ℚ̄_ℓ)`; followed by the inclusion of `D^b_c(X̄, ℚ̄_ℓ)` it is
`AlgebraicGeometry.WeilComplexTwoColimit.forget`. -/
noncomputable def forgetBoundedConstructibleAdic :
    WeilComplexTwoColimit k₀ l X ⥤ (ProEtale.DerivedCategory.boundedConstructibleAdic l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory :=
  toWeilComplex (l := l) k₀ X ⋙ WeilComplex.forgetBoundedConstructibleAdic k₀ l X

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
lemma forgetBoundedConstructibleAdic_comp_ι :
    forgetBoundedConstructibleAdic k₀ X ⋙ ObjectProperty.ι _ =
      WeilComplexTwoColimit.forget (k₀ := k₀) (l := l) (X := X) :=
  rfl

noncomputable instance : (forgetBoundedConstructibleAdic (l := l) k₀ X).CommShift ℤ := by
  dsimp only [forgetBoundedConstructibleAdic]
  infer_instance

/-- Blueprint `definition-weil-structure`: the forgetful functor
`For : D^b_{c,W}(X, ℚ̄_ℓ) ⥤ D^b_c(X̄, ℚ̄_ℓ)` is exact. -/
instance forgetBoundedConstructibleAdic_isTriangulated :
    (forgetBoundedConstructibleAdic (l := l) k₀ X).IsTriangulated := by
  dsimp only [forgetBoundedConstructibleAdic]
  infer_instance

end WeilComplexTwoColimit

end AlgebraicGeometry
