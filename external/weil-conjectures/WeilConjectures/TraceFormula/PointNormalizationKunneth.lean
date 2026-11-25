/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PointNormalizationClass

/-!

# Point normalization of the trace class: the Künneth side

The comparison `ζ : LΔ^* ⟶ Rp₁_!` of `CategoryTheory.Verdier.transportζ` for the diagonal of the
base point is compatible with the tensor structure of `LΔ^*` and the projection morphism of `p₁`
(`ProEtale.CondensedRing.Correspondence.pointDiag_μ_transportζ`), by the composition and
identity clauses of the coherence of the projection formula (blueprint `prop-sf-pf-coherence`).

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

section

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

variable (X) in
/-- The identity clause of the coherence of the projection formula, through
`R(𝟙)_! ≅ 𝟭`. -/
lemma exceptionalProjection_id' (T M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ (𝟙 X) T M ≫
        (boundedConstructibleLowerShriekId ℓ X).hom.app _ ≫
        T ◁ (boundedConstructibleUpperStarId _ ℓ X).hom.app M =
      (boundedConstructibleLowerShriekId ℓ X).hom.app T ▷ M := by
  rw [boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  exact exceptionalProjection_id ℓ X T M

/-- The identity clause of the coherence of the projection formula, for a morphism `g` equal to
the identity. -/
lemma exceptionalProjection_of_eq_id {g : X ⟶ X} (hg : g = 𝟙 X)
    (T M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ g T M ≫
        eqToHom (congrArg (fun g' : X ⟶ X ↦ (boundedConstructibleLowerShriek
          ℓ g').obj
            (T ⊗ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj M)) hg) ≫
        (boundedConstructibleLowerShriekId ℓ X).hom.app _ ≫
        T ◁ (eqToHom (congrArg (fun g : X ⟶ X ↦ (boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ g).obj M) hg) ≫
            (boundedConstructibleUpperStarId _ ℓ X).hom.app M) =
      (eqToHom (congrArg (fun g : X ⟶ X ↦ (boundedConstructibleLowerShriek
          ℓ g).obj T) hg) ≫
            (boundedConstructibleLowerShriekId ℓ X).hom.app T) ▷ M := by
  -- `subst` on the statement with `eqToIso` of functors makes the kernel time out
  subst hg
  simp only [eqToHom_refl, Category.id_comp]
  exact exceptionalProjection_id' X T M

end

namespace Correspondence

variable (ℓ k) in
/-- `L(Δ ≫ p₁)^* = L(𝟙)^* ≅ 𝟭` over the base point, componentwise. -/
noncomputable def pointDiagFstUpperStarIso :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ eqToIso (congrArg (fun g : point k ⟶ point k ↦
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj M)
        diag_point_fst) ≪≫ (boundedConstructibleUpperStarId _ ℓ (point k)).app M)
    (fun {M M'} b ↦ by
      simp only [Iso.trans_hom, eqToIso.hom, Iso.app_hom, Category.assoc]
      rw [reassoc_of% (upperStar_map_comp_eqToHom_of_eq (ℓ := ℓ) diag_point_fst b)]
      have h := (boundedConstructibleUpperStarId _ ℓ (point k)).hom.naturality b
      simp only [Functor.id_map] at h
      rw [h, Functor.id_map])

/-- **`ζ` is compatible with the projection morphisms** over the base point:
`μ ≫ ζ_{W ⊗ Lp₁^* M} = (ζ_W ⊗ (LΔ^* Lp₁^* M ≅ M)) ≫ PF^!_{p₁, W, M}`. -/
lemma pointDiag_μ_transportζ (W : Dᵇc((point k ⨯ point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (diag (point k))) W
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj M) ≫
      Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k) _ =
    (Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k) W ⊗ₘ
        (diagUpperStarProjIso ℓ prod.fst (by simp) M).hom) ≫
      boundedConstructibleExceptionalProjectionMorphism ℓ
        (prod.fst : point k ⨯ point k ⟶ point k) W M := by
  have h := Verdier.transportζ_projection
    (F := boundedConstructibleUpperStar _ ℓ (diag (point k)))
    (G := boundedConstructibleLowerShriek ℓ (diag (point k)))
    (S₁ := boundedConstructibleLowerShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (L := boundedConstructibleLowerShriek ℓ
      (diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k)))
    (I := boundedConstructibleUpperStar _ ℓ
      (diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k)))
    (A₁ := boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (diag (point k)) prod.fst)
    (eqToIso (congrArg (fun g : point k ⟶ point k ↦ boundedConstructibleLowerShriek
      ℓ g) diag_point_fst) ≪≫
        boundedConstructibleLowerShriekId ℓ (point k))
    (boundedConstructibleUpperStarComp _ ℓ (diag (point k)) prod.fst)
    (pointDiagFstUpperStarIso ℓ k)
    (by simp only [pointLowerShriekιΦ])
    (fun T M ↦ boundedConstructibleExceptionalProjectionMorphism ℓ
      (diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k)) T M)
    (fun W M ↦ boundedConstructibleExceptionalProjectionMorphism ℓ
      (prod.fst : point k ⨯ point k ⟶ point k) W M)
    (fun T N ↦ boundedConstructibleExceptionalProjectionMorphism ℓ (diag (point k)) T N)
    (fun T N ↦ by exact upperStar_map_exceptionalProjection_comp_counit ℓ (diag (point k)) T N)
    (fun T M ↦ by exact exceptionalProjection_comp ℓ (diag (point k)) prod.fst T M)
    (fun T M ↦ by
      simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
        pointDiagFstUpperStarIso, NatIso.ofComponents_hom_app, Iso.app_hom, Category.assoc]
      exact exceptionalProjection_of_eq_id diag_point_fst T M)
    (fun f M ↦ by
      exact boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ _ f M)
    W M
  convert h using 2 <;> rfl

/-- **The transport of the exceptional Künneth map along `LΔ^*`** over the base point, for the
symmetry `LΔ^*` at `(Lp₁^* K, Lp₂^* ω)` (`hbraid`) and a description `hX` of the base change
part. -/
lemma pointKunneth_transport (K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {φ : dualizingComplex' ℓ (point k) ⟶ 𝟙_ _}
    (hbraid : Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (diag (point k)))
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj K)
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : point k ⨯ point k ⟶ point k)).obj
          (dualizingComplex' ℓ (point k))) ≫
      (boundedConstructibleUpperStar _ ℓ (diag (point k))).map (β_ _ _).hom =
      (β_ _ _).hom ≫ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (diag (point k)))
        _ _)
    (hX : Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : point k ⨯ point k ⟶ point k)).obj
          (dualizingComplex' ℓ (point k))) ≫
        (prodBaseChangeIso ℓ (point k) (point k)).hom.app (dualizingComplex' ℓ (point k)) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint (point k))).map
          ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint (point k))).counit.app
            (𝟙_ _)) ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint (point k)))).inv =
      (diagUpperStarProjIso ℓ prod.snd (by simp) _).hom ≫ φ) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (diag (point k)))
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj K)
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : point k ⨯ point k ⟶ point k)).obj
          (dualizingComplex' ℓ (point k))) ≫
      (boundedConstructibleUpperStar _ ℓ (diag (point k))).map (exceptionalKunnethMap ℓ K) ≫
      Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
        ((boundedConstructibleUpperShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj K) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ
        (prod.fst : point k ⨯ point k ⟶ point k)).counit.app K =
    ((diagUpperStarProjIso ℓ prod.fst (by simp) K).hom ⊗ₘ
      (diagUpperStarProjIso ℓ prod.snd (by simp) _).hom) ≫ K ◁ φ ≫ (ρ_ K).hom := by
  have h := Verdier.transport_kunneth
    (F := boundedConstructibleUpperStar _ ℓ (diag (point k)))
    (G := boundedConstructibleLowerShriek ℓ (diag (point k)))
    (S₁ := boundedConstructibleLowerShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (B₁ := boundedConstructibleUpperShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (A₁ := boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
    (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : point k ⨯ point k ⟶ point k))
    (boundedConstructibleExceptionalProjectionMorphism ℓ
      (prod.fst : point k ⨯ point k ⟶ point k)
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : point k ⨯ point k ⟶ point k)).obj
        (dualizingComplex' ℓ (point k))) K)
    ((prodBaseChangeIso ℓ (point k) (point k)).hom.app (dualizingComplex' ℓ (point k)))
    ((boundedConstructibleUpperStar _ ℓ (toPoint (point k))).map
      ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint (point k))).counit.app (𝟙_ _)))
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint (point k)))).inv
    (diagUpperStarProjIso ℓ prod.fst (by simp) K).hom
    (diagUpperStarProjIso ℓ prod.snd (by simp) _).hom φ hbraid
    (pointDiag_μ_transportζ _ K) hX
  convert h using 3
  rfl

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
