/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTrivial
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek

/-!

# The projection formula of a proper morphism

Let `f : X ⟶ Y` be a proper morphism of separated `k`-schemes of finite type. Through the
identification `Rf_! ≅ Rf_*` (`boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl`), the
exceptional projection morphism `PF_f : Rf_! T ⊗ M ⟶ Rf_! (T ⊗ Lf^* M)` of bounded constructible
`ℚ̄_ℓ`-complexes is the projection morphism of `Lf^* ⊣ Rf_*`
(`boundedConstructibleExceptionalProjectionMorphism_comp_lowerShriekIsoLowerStar`,
blueprint `prop-sf-pf-coherence`).

The proof follows the definition of `Rf_! ≅ Rf_*`: the lower shriek is compared with that of the
trivial compactification `X ⟶[𝟙] X ⟶[f] Y`, which intertwines the exceptional projection
morphisms
(`boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp`),
and for the trivial compactification the statement is the abstract
`CategoryTheory.Adjunction.trivialOpen_exceptionalProjection_comp`, the extension by zero
`(𝟙 X)_! ≅ 𝟭` being conjugate to the identity isomorphism `L(𝟙 X)^* ≅ 𝟭`.

## Implementation notes

As in `WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion`, the coefficient ring is
written `_` wherever it is determined by the bounded constructible complexes, and the projection of
the monoidal structure is the preferred tensor product.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- see the implementation notes of `WeilConjectures.TraceFormula.KunnethVerdierOpen`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- The inverse of the composition isomorphism of the trivial compactification `(𝟙, f)` of a
proper morphism is the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` at `Lf^*`. -/
lemma leftDerivedUpperStarCompactificationIso_ofIsProper_inv_app
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompactificationIso Λ (Compactification.ofIsProper f)).inv.app M =
      (leftDerivedUpperStarId Λ X).hom.app (L((f)^*⟦Λ⟧).obj M) := by
  have h := leftDerivedUpperStarComp_id_left_app Λ f M
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ (𝟙 X) f).hom.app M), h]
  simp only [leftDerivedUpperStarCompactificationIso, Iso.trans_inv, NatTrans.comp_app,
    eqToIso.inv, eqToHom_app]
  exact Iso.hom_inv_id_app_assoc _ _ _

end General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) [IsProper f.left]

/-- The inverse of the composition isomorphism `Lf^* ≅ Lf^* ⋙ L(𝟙 X)^*` of the trivial
compactification `(𝟙, f)` of a proper `f`, on bounded constructible complexes, is the identity
isomorphism `L(𝟙 X)^* ≅ 𝟭`. -/
lemma ι_map_upperStarId_hom_app_ofIsProper (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructible _).ι.map
      ((boundedConstructibleUpperStarId _ ℓ X).hom.app
        ((boundedConstructibleUpperStar _ ℓ (Compactification.ofIsProper f.left).overG).obj B)) =
      (leftDerivedUpperStarOverCompactificationIso _
        (Compactification.ofIsProper f.left)).inv.app B.obj := by
  rw [leftDerivedUpperStarOverCompactificationIso,
    leftDerivedUpperStarCompactificationIso_ofIsProper_inv_app, ObjectProperty.ι_map]
  exact boundedConstructibleUpperStarId_hom_app_hom _ ℓ (X := X) _

/-- **The projection formula of the trivial compactification** `(𝟙, f)` of a proper morphism:
through `Rf_!^{(𝟙, f)} ≅ Rf_*`, the exceptional projection morphism is the projection morphism of
`Lf^* ⊣ Rf_*`. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_ofIsProper
    (T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ
          (Compactification.ofIsProper f.left)).obj T ⊗ M)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ
          (Compactification.ofIsProper f.left)).obj
            (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj M))
        (exceptionalProjectionMorphismOfCompactification _
          (Compactification.ofIsProper f.left) T.obj M.obj) ≫
      (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ f).hom.app
        (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj M) =
      (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ f).hom.app T ▷ M ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).projectionMorphism T M := by
  rw [homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ
    (Compactification.ofIsProper f.left) T M _ (ι_map_upperStarId_hom_app_ofIsProper ℓ f M)]
  simp only [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  erw [Category.comp_id, Category.comp_id]
  exact Adjunction.trivialOpen_exceptionalProjection_comp
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
      (Compactification.ofIsProper f.left).overI)
    (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso _ ℓ f)
    (fun W ↦ (boundedConstructibleUpperStarId _ ℓ X).hom.app W)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (Compactification.ofIsProper f.left).overG)
    (fun W ↦ boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_counit f ℓ W)
    (fun X' Y' ↦ boundedConstructibleUpperStarId_hom_app_tensor_δ ℓ X X' Y') T M

/-- **The exceptional projection morphism of a proper morphism is the projection morphism of
`Lf^* ⊣ Rf_*`** (blueprint `prop-sf-pf-coherence`): through `Rf_! ≅ Rf_*`, the exceptional
projection morphism `PF_f : Rf_! T ⊗ M ⟶ Rf_! (T ⊗ Lf^* M)` is the projection morphism
`Rf_* T ⊗ M ⟶ Rf_* (T ⊗ Lf^* M)`. -/
theorem boundedConstructibleExceptionalProjectionMorphism_comp_lowerShriekIsoLowerStar
    (T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ f T M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app
          (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj M) =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app T ▷ M ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).projectionMorphism T M := by
  have h := homMk_exceptionalProjectionMorphismOfCompactification_ofIsProper ℓ f T M
  rw [boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, comp_whiskerRight]
  have h₁ := reassoc_of%
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp
      ℓ (compactificationOverField f) (.ofIsProper f.left) T M)
  refine (h₁ _).symm.trans ?_
  rw [h]

end AlgebraicGeometry.ProEtale.CondensedRing
