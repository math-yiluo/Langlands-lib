/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.TraceFormula.PointNormalizationClass

/-!

# Point normalization of the trace class: the point `τ`

For the diagonal correspondence over the base point, the morphism `τ : ℚ̄_ℓ ⟶ LΔ^* RΔ_! ℚ̄_ℓ`
through which the coevaluation factors (`Correspondence.pointTau`) is a section of the counit
of `LΔ^* ⊣ RΔ_!` (`Correspondence.pointTau_comp_counit`). The fixed square of the diagonal
correspondence has identities as horizontal maps, and compact-support base change in such a
square is the counit of `LΔ^* ⊣ RΔ_!` followed by the unit of `L(𝟙)^* ⊣ R(𝟙)_!`
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_unit_of_id`), by its description as a
mate of the composition isomorphisms (blueprint `proposition-composition-base-change-rf-shriek`,
clause (4)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section IdentitySquare

variable {X P : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- **Compact-support base change in a square with identity horizontal maps**: for the cartesian
square `𝟙 ≫ Δ = 𝟙 ≫ Δ` of a proper monomorphism `Δ`, the base change `LΔ^* RΔ_! ⟶ R(𝟙)_! L(𝟙)^*`
at the unit is the counit of `LΔ^* ⊣ RΔ_!` followed by the unit of `L(𝟙)^* ⊣ R(𝟙)_!`. -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_unit_of_id (Δ : X ⟶ P)
    [IsProper Δ.left] (sq : IsPullback (𝟙 X) (𝟙 X) Δ Δ) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app (𝟙_ _) =
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ Δ).counit.app (𝟙_ _) ≫
        (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 X)).unit.app
          (𝟙_ _) := by
  have h := unit_mateEquiv_symm
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 X))
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ Δ)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ sq.w).hom (𝟙_ _)
  rw [← boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ sq] at h
  have hsq : (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ sq.w).hom = 𝟙 _ := by
    simp [boundedConstructibleLowerShriekSquareIso_padicAlgCl]
  rw [hsq, NatTrans.id_app] at h
  erw [Category.comp_id] at h
  apply ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ Δ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.right_triangle_components, Category.id_comp]
  exact h.symm

variable (X) in
/-- The unit of `L(𝟙)^* ⊣ R(𝟙)_!` followed by `R(𝟙)_! ≅ 𝟭` is the inverse of `L(𝟙)^* ≅ 𝟭`. -/
lemma upperStarLowerShriekAdjunction_id_unit_app (x : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 X)).unit.app x ≫
        (boundedConstructibleLowerShriekId ℓ X).hom.app _ =
      (boundedConstructibleUpperStarId _ ℓ X).inv.app x := by
  have h := unit_conjugateEquiv
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleUpperStarId _ ℓ X).inv x
  have hu := Adjunction.homEquiv_ofNatIsoRight_apply
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X)).symm
    (𝟙 ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).obj x))
  simp only [Adjunction.homEquiv_unit, Iso.symm_hom] at hu
  erw [CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at hu
  rw [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl, hu,
    boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  exact h.trans (by simp [Adjunction.id])

variable (X) in
/-- The unit of `R(𝟙)_! ⊣ R(𝟙)^!` followed by `R(𝟙)^! ≅ 𝟭` is the inverse of `R(𝟙)_! ≅ 𝟭`. -/
lemma upperShriekAdjunction_id_unit_app (x : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X)).unit.app x ≫
        (boundedConstructibleUpperShriekId ℓ X).hom.app _ =
      (boundedConstructibleLowerShriekId ℓ X).inv.app x := by
  have h := unit_conjugateEquiv
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleLowerShriekId ℓ X).inv x
  exact h.trans (by simp [Adjunction.id])

/-- The point `τ` of an identity square is a section of the counit of `LΔ^* ⊣ RΔ_!`, for maps
`ι`, `d` equal to the identity. -/
lemma tau_comp_counit_of_id (Δ : X ⟶ P) [IsProper Δ.left] {ι d : X ⟶ X} (hι : ι = 𝟙 X)
    (hd : d = 𝟙 X) [IsProper ι.left] (sq : IsPullback ι d Δ Δ)
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)] :
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ι)).hom ≫
      (boundedConstructibleUpperShriekAdjunction ℓ d).unit.app _ ≫
      (eqToIso (congrArg (fun g : X ⟶ X ↦ boundedConstructibleUpperShriek
          ℓ g) hd) ≪≫
        boundedConstructibleUpperShriekId ℓ X).hom.app _ ≫
      (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).inv.app (𝟙_ _) ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ Δ).counit.app (𝟙_ _) =
    𝟙 _ := by
  subst hι hd
  have h₁ := boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_unit_of_id ℓ Δ sq
  have h₂ := upperStarLowerShriekAdjunction_id_unit_app ℓ X (𝟙_ _)
  have h₃ := upperShriekAdjunction_id_unit_app ℓ X
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).obj (𝟙_ _))
  have h₄ := boundedConstructibleUpperStarId_hom_app_unit ℓ X
  have key : (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).inv.app (𝟙_ _) ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ Δ).counit.app (𝟙_ _) =
      (boundedConstructibleLowerShriekId ℓ X).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).obj (𝟙_ _)) ≫
        (boundedConstructibleUpperStarId _ ℓ X).hom.app (𝟙_ _) := by
    rw [← cancel_epi ((asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).hom.app
      (𝟙_ _)), Iso.hom_inv_id_app_assoc, asIso_hom, h₁, Category.assoc, reassoc_of% h₂,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
  simp only [eqToIso_refl, Iso.refl_trans, key]
  erw [reassoc_of% h₃]
  rw [Iso.inv_hom_id_app_assoc, h₄, Iso.hom_inv_id]

end IdentitySquare

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.Correspondence

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- The point `τ : ℚ̄_ℓ ⟶ LΔ^* RΔ_! ℚ̄_ℓ` of the diagonal correspondence over the base point is a
section of the counit of `LΔ^* ⊣ RΔ_!`. -/
lemma pointTau_comp_counit (v : K ⟶ K) :
    pointTau v ≫ (pointDiagAdj ℓ k).counit.app (𝟙_ _) = 𝟙 _ := by
  have : IsProper (fixedLocusOfEnd v).ι.left := inferInstanceAs (IsProper (𝟙 (point k).left))
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (fixedLocusOfEnd v).isPullback
  simp only [pointTau, Category.assoc]
  exact tau_comp_counit_of_id ℓ (diag (point k)) (ι := (fixedLocusOfEnd v).ι)
    (d := (fixedLocusOfEnd v).d) rfl (fixedLocusOfEnd_d v) (fixedLocusOfEnd v).isPullback

end AlgebraicGeometry.ProEtale.CondensedRing.Correspondence
