/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import WeilConjectures.CategoryTheory.StageSystem.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleTwoColimit
public import WeilConjectures.WeilSheaf.FieldCoefficientTriangulated

/-!
# The standard `t`-structure on `D^b_c(X, ℚ̄_ℓ) = 2-colim_E D^b_c(X, E)`

On a locally Noetherian scheme `X`, the bounded constructible derived categories `D^b_c(X, E)` are
triangulated and stable under the canonical truncations, so they carry the induced standard
`t`-structure. The extensions of scalars `F ⊗_E -` are triangulated and `t`-exact, and the
associativity constraints commute with the shifts. Hence the common-stage category
`D^b_c(X, ℚ̄_ℓ)` (`AlgebraicGeometry.ProEtale.DerivedCategory.ConstructibleTwoColimit`) is
triangulated and carries the induced `t`-structure
(`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitTStructure`), whose heart is
the constructible heart `Sh_c(X, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitTStructure_heart`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Triangulated

namespace AlgebraicGeometry.ProEtale

namespace DerivedCategory

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- `D^b_c(X, Λ)` is a triangulated subcategory of `D(X_proét, Λ)`. -/
instance isTriangulated_boundedFieldConstructible :
    (boundedFieldConstructible Λ X).IsTriangulated := by
  have : (fieldConstructibleSheaf Λ X).IsClosedUnderKernels := inferInstance
  have : (fieldConstructibleSheaf Λ X).IsClosedUnderCokernels := inferInstance
  have : (fieldConstructibleSheaf Λ X).IsClosedUnderExtensions := inferInstance
  have : (fieldConstructibleSheaf Λ X).ContainsZero := inferInstance
  dsimp only [boundedFieldConstructible]
  infer_instance

/-- `D^b_c(X, Λ)` is stable under the canonical truncations, so it inherits the standard
`t`-structure. -/
instance hasInducedTStructure_boundedFieldConstructible :
    (boundedFieldConstructible Λ X).HasInducedTStructure
      _root_.DerivedCategory.TStructure.t :=
  .mk' fun _ hK n ↦ ⟨boundedFieldConstructible_truncLE hK n, boundedFieldConstructible_truncGE hK n⟩

-- the instance search through the derived category of `Λ_X`-modules is slow
noncomputable instance : HasShift (boundedFieldConstructible Λ X).FullSubcategory ℤ :=
  inferInstance

-- the instance search through the derived category of `Λ_X`-modules is slow
noncomputable instance : Preadditive (boundedFieldConstructible Λ X).FullSubcategory :=
  inferInstance

-- the instance search through the derived category of `Λ_X`-modules is slow
instance : HasZeroObject (boundedFieldConstructible Λ X).FullSubcategory :=
  inferInstance

-- the instance search through the derived category of `Λ_X`-modules is slow
instance (n : ℤ) : (shiftFunctor (boundedFieldConstructible Λ X).FullSubcategory n).Additive :=
  inferInstance

-- the instance search through the derived category of `Λ_X`-modules is slow
noncomputable instance : Pretriangulated (boundedFieldConstructible Λ X).FullSubcategory :=
  inferInstance

-- the instance search through the derived category of `Λ_X`-modules is slow
instance : IsTriangulated (boundedFieldConstructible Λ X).FullSubcategory :=
  inferInstance

section Transition


variable {l : ℕ} [Fact l.Prime] {Λ₁ Λ₂ Λ₃ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁]
  [NormedField Λ₂] [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃]
  [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂] [Algebra ℚ_[l] Λ₃] [FiniteDimensional ℚ_[l] Λ₂]
  [FiniteDimensional ℚ_[l] Λ₃] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  (he₁ : Continuous e₁) (he₂ : Continuous e₂) (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁))
  (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂))

/-- The extension of scalars `D^b_c(X, Λ₁) ⥤ D^b_c(X, Λ₂)` commutes with the shifts. -/
noncomputable instance boundedFieldConstructibleExtendScalars_commShift :
    (boundedFieldConstructibleExtendScalars he₁ hc₁ X).CommShift ℤ := by
  dsimp only [boundedFieldConstructibleExtendScalars]
  exact ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- The extension of scalars `D^b_c(X, Λ₁) ⥤ D^b_c(X, Λ₂)` is additive. -/
instance boundedFieldConstructibleExtendScalars_additive :
    (boundedFieldConstructibleExtendScalars he₁ hc₁ X).Additive := by
  dsimp only [boundedFieldConstructibleExtendScalars]
  exact ObjectProperty.liftFullSubcategory_additive _ _ _ _

/-- The extension of scalars `D^b_c(X, Λ₁) ⥤ D^b_c(X, Λ₂)` is triangulated. -/
instance boundedFieldConstructibleExtendScalars_isTriangulated :
    (boundedFieldConstructibleExtendScalars he₁ hc₁ X).IsTriangulated := by
  dsimp only [boundedFieldConstructibleExtendScalars]
  exact ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

/-- The associativity constraint `Λ₃ ⊗_{Λ₂} (Λ₂ ⊗_{Λ₁} -) ≅ Λ₃ ⊗_{Λ₁} -` of the extensions of
scalars of `D^b_c` commutes with the shifts. -/
instance boundedFieldConstructibleExtendScalarsCompIso_commShift :
    NatTrans.CommShift (boundedFieldConstructibleExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).hom ℤ :=
  ObjectProperty.natTransCommShift_liftFullSubcategory _ _ _ _ _ _
    (Functor.mapDerivedCategoryCompNatIso
      (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).symm).hom _ (fun _ ↦ rfl)

end Transition

section TwoColimit

open PadicAlgCl

variable (l : ℕ) [Fact l.Prime]

noncomputable instance boundedFieldConstructibleStageSystem_T_commShift
    {E F : FiniteIntermediateField l} (h : E ≤ F) :
    ((boundedFieldConstructibleStageSystem l X).T h).CommShift ℤ := by
  dsimp only [boundedFieldConstructibleStageSystem]
  infer_instance

instance boundedFieldConstructibleStageSystem_T_isTriangulated
    {E F : FiniteIntermediateField l} (h : E ≤ F) :
    ((boundedFieldConstructibleStageSystem l X).T h).IsTriangulated := by
  dsimp only [boundedFieldConstructibleStageSystem]
  infer_instance

instance boundedFieldConstructibleStageSystem_T_additive
    {E F : FiniteIntermediateField l} (h : E ≤ F) :
    ((boundedFieldConstructibleStageSystem l X).T h).Additive := by
  dsimp only [boundedFieldConstructibleStageSystem]
  infer_instance

instance boundedFieldConstructibleStageSystem_assoc_commShift
    {E F G : FiniteIntermediateField l} (h : E ≤ F) (h' : F ≤ G) :
    NatTrans.CommShift ((boundedFieldConstructibleStageSystem l X).assoc h h').hom ℤ :=
  boundedFieldConstructibleExtendScalarsCompIso_commShift X
    (continuous_inclusion_finiteIntermediateField' l h)
    (continuous_inclusion_finiteIntermediateField' l h')
    (continuous_algebraMap_intermediateField' l _) (continuous_algebraMap_intermediateField' l _)

instance : HasZeroObject (ConstructibleTwoColimit l X) := by
  dsimp only [ConstructibleTwoColimit]
  infer_instance

instance (n : ℤ) : (shiftFunctor (ConstructibleTwoColimit l X) n).Additive := by
  dsimp only [ConstructibleTwoColimit]
  infer_instance

/-- The common-stage category `D^b_c(X, ℚ̄_ℓ)` is pretriangulated, the distinguished triangles
being the triangles isomorphic to the images of distinguished triangles of a finite stage. -/
noncomputable instance : Pretriangulated (ConstructibleTwoColimit l X) :=
  StageSystem.PairCategory.pretriangulated (S := boundedFieldConstructibleStageSystem l X)

/-- The common-stage category `D^b_c(X, ℚ̄_ℓ)` is triangulated. -/
instance : IsTriangulated (ConstructibleTwoColimit l X) :=
  StageSystem.PairCategory.isTriangulated (S := boundedFieldConstructibleStageSystem l X)

/-- The standard `t`-structure on the common-stage category
`D^b_c(X, ℚ̄_ℓ) = 2-colim_E D^b_c(X, E)`, induced by the standard `t`-structures of the finite
stages `D^b_c(X, E)`, the transition functors being `t`-exact. Its halves are
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitLE` and
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitGE`. -/
noncomputable def constructibleTwoColimitTStructure : TStructure (ConstructibleTwoColimit l X) :=
  (boundedFieldConstructibleStageSystem l X).tStructure
    (fun E ↦ (boundedFieldConstructible E.1 X).tStructure _root_.DerivedCategory.TStructure.t)
    (fun h n K hK ↦ boundedFieldConstructibleLE_T h n K hK)
    (fun h n K hK ↦ boundedFieldConstructibleGE_T h n K hK)

lemma constructibleTwoColimitTStructure_le (n : ℤ) :
    (constructibleTwoColimitTStructure X l).le n = constructibleTwoColimitLE l X n :=
  rfl

lemma constructibleTwoColimitTStructure_ge (n : ℤ) :
    (constructibleTwoColimitTStructure X l).ge n = constructibleTwoColimitGE l X n :=
  rfl

/-- The heart of the standard `t`-structure on `D^b_c(X, ℚ̄_ℓ)` is the constructible heart
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitHeart`, which is the
`2`-colimit of the constructible hearts of the finite stages
(`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitHeartEquiv`). -/
theorem constructibleTwoColimitTStructure_heart :
    (constructibleTwoColimitTStructure X l).heart = constructibleTwoColimitHeart l X :=
  rfl

/-- The constructible heart `Sh_c(X, ℚ̄_ℓ)` is an abelian category, being the heart of a
`t`-structure on a triangulated category. -/
noncomputable instance abelian_constructibleTwoColimitHeart :
    Abelian (constructibleTwoColimitHeart l X).FullSubcategory :=
  letI := (constructibleTwoColimitTStructure X l).hasHeartFullSubcategory
  (constructibleTwoColimitTStructure X l).abelianHeart
    (constructibleTwoColimitTStructure X l).heart.FullSubcategory

end TwoColimit


end DerivedCategory

end AlgebraicGeometry.ProEtale
