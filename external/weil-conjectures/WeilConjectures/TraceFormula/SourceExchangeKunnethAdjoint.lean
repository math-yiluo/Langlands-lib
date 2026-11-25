/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeKunnethSquare
public import WeilConjectures.TraceFormula.SourceExchangeKunnethUnit

/-!

# The Künneth map through the unit, and the evaluation against the exceptional Künneth adjoint

Two identities for the exceptional Künneth part of identity (a) of the trace-class source
exchange (blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 3):

- `ProEtale.CondensedRing.prodLowerStarExternalProduct_comp_inv_app`: the Künneth map `Π_f` of
  `q = f × f`, read through `Rq_* ≅ Rq_!`, is the unit of `Lq^* ⊣ Rq_!` followed by `Rq_!` of the
  tensor structure of `Lq^*` and the transported counits;
- `ProEtale.CondensedRing.exceptionalProjection_comp_exceptionalKunnethAdjoint`: the projection
  formula for `p_X` followed by the exceptional Künneth adjoint applies base change in the product
  square and the counit of `Ra_Z! ⊣ Ra_Z^!`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Braiding

variable {X Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The tensor symmetry of an external product, `M ⊠ N ≅ Lp_Z^* N ⊗ Lp_X^* M`, with the external
product in its source (so that it composes with maps out of `M ⊠ N` without unfolding
`ProEtale.CondensedRing.externalProduct`). -/
noncomputable def externalProductBraiding (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ M N ≅ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Z ⟶ Z)).obj N ⊗
      (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Z ⟶ X)).obj M :=
  β_ _ _

end Braiding

section Evaluation

variable {X Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- An abstract evaluation of a projection formula against its inverse: for maps `pf` natural in
both variables, the composite of `pf`, a functor applied to a whiskered map through an
isomorphism `b`, the inverse of `pf` and maps whiskered on the right, is computed by
whiskering. -/
lemma _root_.CategoryTheory.MonoidalCategory.comp_map_comp_inv_comp_whiskerRight_eq
    {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [MonoidalCategory 𝒞] [MonoidalCategory 𝒟]
    (L : 𝒟 ⥤ 𝒞) (P : 𝒞 ⥤ 𝒟) {S T W : 𝒟} {M' K A₁ A₂ : 𝒞} (e : M' ⟶ K) (c : S ⟶ T)
    (pfS' : L.obj S ⊗ M' ⟶ L.obj (S ⊗ P.obj M')) (pfS : L.obj S ⊗ K ⟶ L.obj (S ⊗ P.obj K))
    (pfT : L.obj T ⊗ K ⟶ L.obj (T ⊗ P.obj K)) [IsIso pfT]
    (hr : (L.obj S ◁ e) ≫ pfS = pfS' ≫ L.map (S ◁ P.map e))
    (hl : (L.map c ▷ K) ≫ pfT = pfS ≫ L.map (c ▷ P.obj K)) (b : W ≅ T ⊗ P.obj K)
    (g₁ : L.obj T ⟶ A₁) (g₂ : A₁ ⟶ A₂) (g₃ : A₂ ⟶ 𝟙_ 𝒞) :
    pfS' ≫ L.map ((S ◁ P.map e) ≫ (c ▷ P.obj K) ≫ b.inv) ≫ L.map b.hom ≫ inv pfT ≫
      (g₁ ▷ K) ≫ (g₂ ▷ K) ≫ (g₃ ▷ K) ≫ (λ_ K).hom =
    ((L.map c ≫ g₁ ≫ g₂ ≫ g₃) ▷ M') ≫ (𝟙_ 𝒞 ◁ e) ≫ (λ_ K).hom := by
  rw [← L.map_comp_assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    L.map_comp_assoc, ← reassoc_of% hr, ← reassoc_of% hl, IsIso.hom_inv_id_assoc]
  simp only [← comp_whiskerRight_assoc]
  rw [whisker_exchange_assoc]

/-- The projection formula for `p_X` followed by the exceptional Künneth adjoint: for maps
`c : S ⟶ Lp_Z^* ω_Z` and `e : M' ⟶ K`, it applies `c`, base change in the product square, the
counit of `Ra_Z! ⊣ Ra_Z^!` and then `e`. -/
theorem exceptionalProjection_comp_exceptionalKunnethAdjoint
    (S : Dᵇc((X ⨯ Z).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {M' K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (e : M' ⟶ K)
    (c : S ⟶ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Z ⟶ Z)).obj
      (dualizingComplex' ℓ Z)) :
    boundedConstructibleExceptionalProjectionMorphism ℓ (prod.fst : X ⨯ Z ⟶ X) S M' ≫
      (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Z ⟶ X)).map
        ((S ◁ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Z ⟶ X)).map e) ≫
          (c ▷ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Z ⟶ X)).obj K) ≫
          (externalProductBraiding ℓ K (dualizingComplex' ℓ Z)).inv) ≫
      exceptionalKunnethAdjoint ℓ K =
    (((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Z ⟶ X)).map c ≫
        (prodBaseChangeIso ℓ X Z).hom.app (dualizingComplex' ℓ Z) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).counit.app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv) ▷ M') ≫
      (𝟙_ _ ◁ e) ≫ (λ_ K).hom := by
  have h := MonoidalCategory.comp_map_comp_inv_comp_whiskerRight_eq
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Z ⟶ X))
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Z ⟶ X)) e c
    (boundedConstructibleExceptionalProjectionMorphism ℓ (prod.fst : X ⨯ Z ⟶ X) S M')
    (boundedConstructibleExceptionalProjectionMorphism ℓ (prod.fst : X ⨯ Z ⟶ X) S K)
    (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Z ⟶ X)).app
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Z ⟶ Z)).obj
        (dualizingComplex' ℓ Z))).app K)
    (boundedConstructibleExceptionalProjectionMorphism_natural_right ℓ _ S _)
    (boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ _ c _)
    (externalProductBraiding ℓ K (dualizingComplex' ℓ Z))
    ((prodBaseChangeIso ℓ X Z).hom.app (dualizingComplex' ℓ Z))
    ((boundedConstructibleUpperStar _ ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).counit.app (𝟙_ _)))
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv
  exact h

end Evaluation

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- For an adjunction `F ⊣ G` with `F` monoidal and an isomorphism `G' ≅ G`, the transpose of the
tensor structure of `F` followed by `c₁ ⊗ c₂` is, through the braidings, the unit of the
transported adjunction `F ⊣ G'` followed by `G'` of the tensor structure and the whiskerings of
`c₁ = u₁ ≫ u₂ ≫ u₃ ≫ v` and `c₂` in the exchanged order. -/
lemma _root_.CategoryTheory.Adjunction.homEquiv_μIso_inv_tensorHom_comp_inv_app
    {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [MonoidalCategory 𝒞] [MonoidalCategory 𝒟]
    [BraidedCategory 𝒞] [BraidedCategory 𝒟] {F : 𝒞 ⥤ 𝒟} [F.Monoidal] {G G' : 𝒟 ⥤ 𝒞}
    (adj : F ⊣ G) (ι : G' ≅ G) {A B : 𝒞}
    (hδ : F.map (β_ A B).hom ≫ Functor.OplaxMonoidal.δ F B A =
      Functor.OplaxMonoidal.δ F A B ≫ (β_ (F.obj A) (F.obj B)).hom)
    {X₁ X₂ Z Y₁ Y₂ : 𝒟} (c₁ : F.obj A ⟶ Y₁) (c₂ : F.obj B ⟶ Y₂) (u₁ : F.obj A ⟶ X₁)
    (u₂ : X₁ ⟶ X₂) (u₃ : X₂ ⟶ Z) (v : Z ⟶ Y₁) (hc : u₁ ≫ u₂ ≫ u₃ ≫ v = c₁) :
    adj.homEquiv _ _ ((Functor.Monoidal.μIso F A B).inv ≫ (c₁ ⊗ₘ c₂)) ≫
      ι.inv.app (Y₁ ⊗ Y₂) =
    (β_ A B).hom ≫ (adj.ofNatIsoRight ι.symm).unit.app (B ⊗ A) ≫
      G'.map (Functor.OplaxMonoidal.δ F B A ≫ (F.obj B ◁ (u₁ ≫ u₂ ≫ u₃))) ≫
      G'.map ((F.obj B ◁ v) ≫ (c₂ ▷ Y₁) ≫ (β_ Y₁ Y₂).inv) := by
  subst hc
  rw [← (adj.ofNatIsoRight ι.symm).homEquiv_id (B ⊗ A), Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id, Adjunction.homEquiv_unit, Iso.symm_hom, Category.assoc,
    Category.assoc, ← G'.map_comp, ← ι.inv.naturality, ← adj.unit_naturality_assoc,
    ← G.map_comp_assoc]
  rw [Functor.Monoidal.μIso_inv, Category.assoc, reassoc_of% hδ,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← tensorHom_def'_assoc,
    ← BraidedCategory.braiding_naturality_assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc,
    Category.assoc]

/-- The Künneth map `Π_f` of `q = f × f`, read through `Rq_* ≅ Rq_!`, is the unit of
`Lq^* ⊣ Rq_!` followed by `Rq_!` of the tensor structure of `Lq^*` and the transported counits,
written with the factors exchanged. -/
theorem prodLowerStarExternalProduct_comp_inv_app (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    prodLowerStarExternalProduct ℓ f f K N ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
        (externalProduct ℓ K N) =
    (externalProductBraiding ℓ _ _).hom ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (prod.map f f)).unit.app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar ℓ f).obj N) ⊗
          (boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar ℓ f).obj K)) ≫
      (boundedConstructibleLowerShriek ℓ (prod.map f f)).map
        (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ (prod.map f f))
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar ℓ f).obj N))
            ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar ℓ f).obj K)) ≫
          (_ ◁ ((boundedConstructibleUpperStarComp _ ℓ (prod.map f f) prod.fst).inv.app
              ((boundedConstructibleLowerStar ℓ f).obj K) ≫
            eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
              ((boundedConstructibleLowerStar ℓ f).obj K)) (prod.map_fst f f)) ≫
            ((boundedConstructibleUpperStarComp _ ℓ (prod.fst : X ⨯ X ⟶ X) f).hom.app
              ((boundedConstructibleLowerStar ℓ f).obj K) :
                _ ⟶ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj
                  ((boundedConstructibleUpperStar _ ℓ f).obj
                    ((boundedConstructibleLowerStar ℓ f).obj K)))))) ≫
      (boundedConstructibleLowerShriek ℓ (prod.map f f)).map
        ((_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).map
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K :
              (boundedConstructibleUpperStar _ ℓ f).obj
                ((boundedConstructibleLowerStar ℓ f).obj K) ⟶ K)) ≫
          (prodUpperStarCounit ℓ (prod.map_snd f f) N ▷ _) ≫
          (externalProductBraiding ℓ K N).inv) := by
  have h := Adjunction.homEquiv_μIso_inv_tensorHom_comp_inv_app
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map f f))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f))
    (boundedConstructibleUpperStar_map_braiding_hom_δ ℓ (prod.map f f)
      ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
        ((boundedConstructibleLowerStar ℓ f).obj K))
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
        ((boundedConstructibleLowerStar ℓ f).obj N)))
    (prodUpperStarCounit ℓ (prod.map_fst f f) K) (prodUpperStarCounit ℓ (prod.map_snd f f) N)
    ((boundedConstructibleUpperStarComp _ ℓ (prod.map f f) prod.fst).inv.app
      ((boundedConstructibleLowerStar ℓ f).obj K))
    (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
      ((boundedConstructibleLowerStar ℓ f).obj K)) (prod.map_fst f f)))
    ((boundedConstructibleUpperStarComp _ ℓ (prod.fst : X ⨯ X ⟶ X) f).hom.app
      ((boundedConstructibleLowerStar ℓ f).obj K))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K)) rfl
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
