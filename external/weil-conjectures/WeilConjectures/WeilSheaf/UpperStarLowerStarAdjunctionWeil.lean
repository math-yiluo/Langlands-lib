/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.AdjunctionUnitLocal
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.UpperStarLowerStar
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
public import WeilConjectures.WeilSheaf.UpperStarId

/-!
# Composition of pullbacks and pushforwards of Weil sheaves

The pushforward of Weil sheaves is left exact, and pushforwards compose. (The composition of
pullbacks, `AlgebraicGeometry.WeilSheaf.upperStarCompIso`, is in
`WeilConjectures.WeilSheaf.UpperStarId`.)

## Main definitions

- `AlgebraicGeometry.WeilSheaf.lowerStarCompIso`: `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- Let `L ⊣ R` be an adjunction whose right adjoint is a composite `R ≅ R₂ ⋙ R₁` of right
adjoints of `L₁ ⊣ R₁` and `L₂ ⊣ R₂`. If the unit of `L₁ ⊣ R₁` is invertible at `X` and the unit
of `L₂ ⊣ R₂` is invertible at `L₁ X`, then the unit of `L ⊣ R` is invertible at `X`. -/
lemma isIso_unit_app_of_iso_comp {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) (X : C) [IsIso (adj₁.unit.app X)] [IsIso (adj₂.unit.app (L₁.obj X))] :
    IsIso (adj.unit.app X) := by
  set adj' := (adj₁.comp adj₂).ofNatIsoRight e
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj adj' X
  have h₁ := adj'.homEquiv_id X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id,
    Adjunction.comp_unit_app] at h₁
  have : IsIso (adj'.unit.app X) := by
    rw [← h₁]
    infer_instance
  rw [← h] at this
  exact IsIso.of_isIso_comp_right _ (R.map ((adj.leftAdjointUniq adj').hom.app X))

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)]

section

variable [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

omit [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
/-- The pullback of Weil sheaves is the pullback of pro-étale Weil sheaves. -/
noncomputable def upperStarCompιIso :
    WeilSheaf.upperStar φ ⋙ (WeilSheaf.objectProperty k₀ l X).ι ≅
      (WeilSheaf.objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ :=
  ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The pushforward of Weil sheaves is the pushforward of pro-étale Weil sheaves. -/
noncomputable def lowerStarCompιIso :
    WeilSheaf.lowerStar φ ⋙ (WeilSheaf.objectProperty k₀ l Y).ι ≅
      (WeilSheaf.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The pushforward of Weil sheaves is left exact. -/
instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteLimits (WeilSheaf.lowerStar (k₀ := k₀) (l := l) φ) :=
  preservesFiniteLimits_of_comp_ι _ (ProEtaleWeilSheaf.lowerStar k₀ l φ) (lowerStarCompιIso φ)

end

variable [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (ψ : Y ⟶ Z) [ψ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact ψ] [QuasiSeparated ψ]
  [LocallyOfFiniteType ψ] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]

/-- The composition isomorphism `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*` of pushforwards of Weil sheaves. -/
noncomputable def lowerStarCompIso :
    WeilSheaf.lowerStar φ ⋙ WeilSheaf.lowerStar ψ ≅
      WeilSheaf.lowerStar (k₀ := k₀) (l := l) (φ ≫ ψ) :=
  ((WeilSheaf.objectProperty k₀ l Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (lowerStarCompιIso ψ) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (lowerStarCompιIso φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.lowerStarCompIso k₀ l φ ψ) ≪≫
      (lowerStarCompιIso (φ ≫ ψ)).symm)

end WeilSheaf

end AlgebraicGeometry
