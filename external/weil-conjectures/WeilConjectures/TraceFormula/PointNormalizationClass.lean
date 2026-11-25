/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ClassTransport
public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.TraceFormula.PointNormalizationReduction

/-!

# Point normalization of the trace class: the class of the identity

The image under `LΔ^*` of the uncurried class `[1] : Lp₂^* K ⊗ RΔ_! ℚ̄_ℓ ⟶ Rp₁^! K` of the
identity of `K`, read through `LΔ^* Rp₁^! K ⟶ K` (the comparison
`ζ : LΔ^* ⟶ Rp₁_!` of `CategoryTheory.Verdier.transportζ` followed by the counit of
`Rp₁_! ⊣ Rp₁^!`), is the counit of `LΔ^* ⊣ RΔ_!` at the unit, read through
`LΔ^* Lp₂^* K ≅ K` (`ProEtale.CondensedRing.Correspondence.pointClass_transport`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace Correspondence

variable {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}

section ClassTransport

variable (ℓ k) in
/-- The adjunction `LΔ^* ⊣ RΔ_!` of the diagonal of the base point. -/
noncomputable abbrev pointDiagAdj :=
  boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (diag (point k))

omit [Fact (ringChar k).Prime] in
lemma prod_fst_diag_point :
    (prod.fst : point k ⨯ point k ⟶ point k) ≫ diag (point k) = 𝟙 _ :=
  prod.hom_ext (by simp) (by simpa using toPoint_ext _ _)

variable (ℓ k) in
/-- `LΔ^*` is an equivalence over the base point, with inverse `Lp₁^*`: `Δ ≫ p₁ = 𝟙` and
`p₁ ≫ Δ = 𝟙`. -/
noncomputable def pointDiagUpperStarEquivalence :
    Dᵇc((point k ⨯ point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ≌
      Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  CategoryTheory.Equivalence.mk (boundedConstructibleUpperStar _ ℓ (diag (point k)))
    (boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    ((boundedConstructibleUpperStarId _ ℓ _).symm ≪≫
      eqToIso (congrArg (fun g : point k ⨯ point k ⟶ point k ⨯ point k ↦
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
          prod_fst_diag_point.symm) ≪≫
      boundedConstructibleUpperStarComp _ ℓ _ _)
    ((boundedConstructibleUpperStarComp _ ℓ _ _).symm ≪≫
      eqToIso (congrArg (fun g : point k ⟶ point k ↦
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) diag_point_fst) ≪≫
      boundedConstructibleUpperStarId _ ℓ _)

instance : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
    (diag (point k))).IsEquivalence :=
  (pointDiagUpperStarEquivalence ℓ k).isEquivalence_functor

instance (Z : Dᵇc((point k ⨯ point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((pointDiagAdj ℓ k).unit.app Z) :=
  inferInstance

variable (ℓ k) in
/-- `RΔ_! ⋙ Rp₁_! ≅ R(Δ ≫ p₁)_! = R(𝟙)_! ≅ 𝟭`. -/
noncomputable def pointLowerShriekιΦ :
    boundedConstructibleLowerShriek ℓ (diag (point k)) ⋙
        boundedConstructibleLowerShriek ℓ
          (prod.fst : point k ⨯ point k ⟶ point k) ≅ 𝟭 _ :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (diag (point k)) prod.fst).symm ≪≫
    eqToIso (congrArg (fun g : point k ⟶ point k ↦ boundedConstructibleLowerShriek
      ℓ g) diag_point_fst) ≪≫
    boundedConstructibleLowerShriekId ℓ (point k)

variable (ℓ k) in
/-- `Rp₁^! ⋙ RΔ^! ≅ R(Δ ≫ p₁)^! = R(𝟙)^! ≅ 𝟭`. -/
noncomputable def pointUpperShriekιΨ :
    boundedConstructibleUpperShriek ℓ
          (prod.fst : point k ⨯ point k ⟶ point k) ⋙
        boundedConstructibleUpperShriek ℓ (diag (point k)) ≅
      𝟭 _ :=
  (boundedConstructibleUpperShriekComp_padicAlgCl ℓ (diag (point k)) prod.fst).symm ≪≫
    eqToIso (congrArg (fun g : point k ⟶ point k ↦ boundedConstructibleUpperShriek
      ℓ g) diag_point_fst) ≪≫
    boundedConstructibleUpperShriekId ℓ (point k)

lemma eqToHom_counit_point {u₁ u₂ : point k ⟶ point k} (h : u₁ = u₂)
    (d : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ u₁).map
        ((eqToIso (congrArg (fun g : point k ⟶ point k ↦ boundedConstructibleUpperShriek
          ℓ g) h)).hom.app d) ≫
      (eqToIso (congrArg (fun g : point k ⟶ point k ↦ boundedConstructibleLowerShriek
          ℓ g) h)).hom.app _ ≫
      (boundedConstructibleUpperShriekAdjunction ℓ u₂).counit.app d =
    (boundedConstructibleUpperShriekAdjunction ℓ u₁).counit.app d := by
  subst h
  simp

lemma pointUpperShriekιΨ_conj (K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (pointLowerShriekιΦ ℓ k).inv.app _ ≫
      (boundedConstructibleLowerShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k)).map
        ((boundedConstructibleUpperShriekAdjunction ℓ (diag (point k))).counit.app
          ((boundedConstructibleUpperShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj K)) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ
        (prod.fst : point k ⨯ point k ⟶ point k)).counit.app K =
    (pointUpperShriekιΨ ℓ k).hom.app K := by
  have h := Verdier.conjugate_counit_aux
    ((boundedConstructibleUpperShriekAdjunction ℓ (diag (point k))).comp
      (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : point k ⨯ point k ⟶ point k)))
    (boundedConstructibleUpperShriekAdjunction ℓ (diag (point k) ≫ prod.fst))
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 (point k)))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (diag (point k)) prod.fst).symm
    (eqToIso (congrArg (fun g : point k ⟶ point k ↦ boundedConstructibleLowerShriek
      ℓ g) diag_point_fst))
    (eqToIso (congrArg (fun g : point k ⟶ point k ↦ boundedConstructibleUpperShriek
      ℓ g) diag_point_fst))
    (boundedConstructibleLowerShriekId ℓ (point k)) (eqToHom_counit_point diag_point_fst) K
  simp only [Adjunction.comp_counit_app] at h
  simp only [pointLowerShriekιΦ, pointUpperShriekιΨ, Iso.trans_inv, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
  convert h using 2 <;> rfl

lemma pointClass_coeff :
    diagUnitCoeff ℓ (K := K) diag_point_snd diag_point_fst.symm ≫
      (pointUpperShriekιΨ ℓ k).hom.app K = (diagUpperStarProjIso ℓ prod.snd (by simp) K).hom := by
  have h := Verdier.coeff_cancel_aux
    ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) prod.snd).inv.app K)
    (eqToHom (by rw [diag_point_snd]))
    ((boundedConstructibleUpperStarId _ ℓ (point k)).hom.app K)
    ((boundedConstructibleUpperShriekId ℓ (point k)).app K)
    (eqToHom (by rw [← diag_point_fst]))
    ((eqToIso (congrArg (fun g : point k ⟶ point k ↦ boundedConstructibleUpperShriek
      ℓ g) diag_point_fst)).hom.app K)
    (by simp)
    ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ (diag (point k)) prod.fst).app K)
  convert h using 2 <;> first
    | simp only [diagUnitCoeff, pointUpperShriekιΨ, diagUpperStarProjIso, Iso.trans_hom,
        Iso.symm_hom, NatTrans.comp_app, Iso.app_hom, Iso.app_inv, eqToIso.hom]
    | simp only [Functor.comp_obj]

variable (K) in
/-- The transport of the class of the identity along `LΔ^*`. -/
lemma pointClass_transport
    (hbraid : Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (diag (point k)))
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : point k ⨯ point k ⟶ point k)).obj K)
        ((boundedConstructibleLowerShriek ℓ (diag (point k))).obj (𝟙_ _)) ≫
      (boundedConstructibleUpperStar _ ℓ (diag (point k))).map (β_ _ _).hom =
      (β_ _ _).hom ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (diag (point k))) _ _) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (diag (point k))) _ _ ≫
      (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
        (uncurry (diagUnitClass ℓ (K := K) diag_point_snd diag_point_fst.symm)) ≫
      Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k) _ ≫
      (boundedConstructibleUpperShriekAdjunction ℓ
        (prod.fst : point k ⨯ point k ⟶ point k)).counit.app K =
    _ ◁ (pointDiagAdj ℓ k).counit.app (𝟙_ _) ≫ (ρ_ _).hom ≫
      (diagUpperStarProjIso ℓ prod.snd (by simp) K).hom := by
  rw [← pointClass_coeff, uncurry_diagUnitClass]
  have h := Verdier.transport_class (S := Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (P := Dᵇc((point k ⨯ point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (F := boundedConstructibleUpperStar _ ℓ (diag (point k)))
    (G := boundedConstructibleLowerShriek ℓ (diag (point k)))
    (S₁ := boundedConstructibleLowerShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (H := boundedConstructibleUpperShriek ℓ (diag (point k)))
    (B₁ := boundedConstructibleUpperShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
    (boundedConstructibleUpperShriekAdjunction ℓ (diag (point k)))
    (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (pointUpperShriekιΨ ℓ k) (fun K ↦ by exact pointUpperShriekιΨ_conj K)
    (fun T M ↦ boundedConstructibleExceptionalProjectionMorphism ℓ (diag (point k)) T M)
    (fun T M ↦ by exact upperStar_map_exceptionalProjection_comp_counit ℓ (diag (point k)) T M)
    (by exact hbraid)
    (diagUnitCoeff ℓ (K := K) diag_point_snd diag_point_fst.symm)
  convert h using 3
  rfl

end ClassTransport

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
