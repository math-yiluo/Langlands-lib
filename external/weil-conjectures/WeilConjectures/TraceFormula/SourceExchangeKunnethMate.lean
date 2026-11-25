/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeKunnethSquare

/-!

# The mate of the Künneth square of a proper morphism

For a proper morphism `f : X ⟶ Y` and `q = f × f`, the mate of the composition isomorphism of
the non-cartesian square `q ≫ p₁' = p₁ ≫ f` (for `Lf^* ⊣ Rf_!` and `Lq^* ⊣ Rq_!`), followed by
the transported counit of `q ≫ p₂' = p₂ ≫ f`, is the compact-support base change `Ex_!` of the
cartesian square `(f × 1) ≫ p₁' = p_X ≫ f` followed by `Rp_X!` of the base change of the
cartesian square `(1 × f) ≫ p_Y = p₂ ≫ f` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3). The proof factors
`q = (1 × f) ≫ (f × 1)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The pasting computation behind
`upperStar_map_unit_comp_squareIso_comp_counit_comp_prodUpperStarCounit`, stated for abstract
categories, adjunctions `Fs ⊣ Fl`, `Qs ⊣ Ql`, `Hs ⊣ Hl` and squares `sqW`, `sqW₁` so that it can be
applied without unfolding the six functors: if `sqW` factors through `sqW₁` (`h₁`) and the adjoint
of `c` through `Ql` factors through `Hl` (`h₂`), then the mate of `sqW` followed by `c` is the
mate of `sqW₁` followed by `Z`. -/
lemma _root_.CategoryTheory.mateEquiv_symm_app_comp_map_comp_eq {𝒜 ℬ 𝒞 𝒟 ℰ : Type*}
    [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟] [Category ℰ] {Fs : 𝒟 ⥤ ℰ}
    {Fl : ℰ ⥤ 𝒟} (adjF : Fs ⊣ Fl) {Qs : 𝒜 ⥤ ℬ} {Ql : ℬ ⥤ 𝒜} (adjQ : Qs ⊣ Ql) {Hs : 𝒜 ⥤ 𝒞}
    {Hl : 𝒞 ⥤ 𝒜} (adjH : Hs ⊣ Hl) (P₁' : 𝒜 ⥤ 𝒟) (P₁ : ℬ ⥤ ℰ) (PX : 𝒞 ⥤ ℰ) (Gl : ℬ ⥤ 𝒞)
    (sqW : Ql ⋙ P₁' ⟶ P₁ ⋙ Fl) (sqW₁ : Hl ⋙ P₁' ⟶ PX ⋙ Fl) (ex : P₁' ⋙ Fs ⟶ Hs ⋙ PX)
    (hex : ex = (mateEquiv adjH adjF).symm sqW₁) (T : 𝒜) (B : ℬ) (c : Qs.obj T ⟶ B) {N : 𝒜}
    (φ₁ : Ql.obj B ⟶ N) (φ₂ : N ⟶ Hl.obj (Gl.obj B)) {M : ℰ} (ψ₁ : PX.obj (Gl.obj B) ⟶ M)
    (ψ₂ : M ⟶ P₁.obj B) (Z : Hs.obj T ⟶ Gl.obj B)
    (h₁ : sqW.app B = P₁'.map (φ₁ ≫ φ₂) ≫ sqW₁.app (Gl.obj B) ≫ Fl.map (ψ₁ ≫ ψ₂))
    (h₂ : adjQ.unit.app T ≫ Ql.map c ≫ φ₁ ≫ φ₂ = adjH.unit.app T ≫ Hl.map Z) :
    Fs.map (P₁'.map (adjQ.unit.app T)) ≫ Fs.map (sqW.app (Qs.obj T)) ≫
        adjF.counit.app (P₁.obj (Qs.obj T)) ≫ P₁.map c =
      ex.app T ≫ PX.map Z ≫ ψ₁ ≫ ψ₂ := by
  subst hex
  have hn := sqW.naturality c
  have hc := adjF.counit.naturality (P₁.map c)
  have hs := sqW₁.naturality Z
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn hc hs
  rw [← hc, ← Fs.map_comp_assoc, ← Fs.map_comp_assoc, Category.assoc, ← hn, h₁,
    ← P₁'.map_comp_assoc, ← P₁'.map_comp_assoc, Category.assoc, h₂,
    P₁'.map_comp_assoc, reassoc_of% hs]
  simp [mateEquiv]

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left]
set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

-- matching the mate square unfolds the restricted `ℚ̲̄_ℓ`-functors, which is expensive
/-- **The mate of the Künneth square** (blueprint `theorem-proper-pushforward-lefschetz-verdier--1`,
Step 3): for `T = Lp₂'^* Rf_* B`, the mate `Lf^* Rp₁'_! T ⟶ Rp₁_! Lq^* T` of the composition
isomorphism of `q ≫ p₁' = p₁ ≫ f`, followed by the transported counit
`Lq^* Lp₂'^* Rf_* B ⟶ Lp₂^* B`, is `Ex_!` of the cartesian square `(f × 1) ≫ p₁' = p_X ≫ f`,
followed by `Rp_X!` of `L(f × 1)^* Lp₂'^* Rf_* B ≅ Lp_Y^* Rf_! B ⟶ R(1 × f)_! Lp₂^* B` (the base
change `Ex_!` of the cartesian square `(1 × f) ≫ p_Y = p₂ ≫ f`) and `Rp_X! R(1 × f)_! ≅ Rp₁_!`. -/
theorem upperStar_map_unit_comp_squareIso_comp_counit_comp_prodUpperStarCounit
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar 𝐐 ℓ f).map
        ((boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (prod.map f f)).unit.app
            ((boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar ℓ f).obj B)))) ≫
      (boundedConstructibleUpperStar 𝐐 ℓ f).map
        ((boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app
          ((boundedConstructibleUpperStar 𝐐 ℓ (prod.map f f)).obj
            ((boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar ℓ f).obj B))) :
          _ ⟶ (boundedConstructibleLowerShriek ℓ f).obj
            ((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj
              ((boundedConstructibleUpperStar 𝐐 ℓ (prod.map f f)).obj
                ((boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
                  ((boundedConstructibleLowerStar ℓ f).obj B))))) ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).counit.app _ ≫
      (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X)).map
        (prodUpperStarCounit ℓ (prod.map_snd f f) B) =
    ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
        (IsPullback.of_prod_fst_with_id f Y).flip).app
        ((boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj B)) :
        (boundedConstructibleUpperStar 𝐐 ℓ f).obj ((boundedConstructibleLowerShriek ℓ
          (prod.fst : Y ⨯ Y ⟶ Y)).obj ((boundedConstructibleUpperStar 𝐐 ℓ
            (prod.snd : Y ⨯ Y ⟶ Y)).obj ((boundedConstructibleLowerStar ℓ f).obj B))) ⟶
        (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj
          ((boundedConstructibleUpperStar 𝐐 ℓ (prod.map f (𝟙 Y))).obj
            ((boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar ℓ f).obj B)))) ≫
      (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
        ((boundedConstructibleUpperStarComp 𝐐 ℓ (prod.map f (𝟙 Y)) prod.snd).inv.app
            ((boundedConstructibleLowerStar ℓ f).obj B) ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar 𝐐 ℓ r).obj
            ((boundedConstructibleLowerStar ℓ f).obj B)) (by simp)) ≫
          (boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : X ⨯ Y ⟶ Y)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B) ≫
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
            (IsPullback.of_prod_snd_with_id f X)).app B) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (prod.map (𝟙 X) f) prod.fst).inv.app
        ((boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : X ⨯ X ⟶ X)).obj B) ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj
        ((boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : X ⨯ X ⟶ X)).obj B)) (by simp)) := by
  have : IsProper (prod.map f (𝟙 Y)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id f Y).map (Over.forget _))
      (inferInstanceAs (IsProper f.left))
  have : IsProper (prod.map (𝟙 X) f).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_snd_with_id f X).map (Over.forget _))
      (inferInstanceAs (IsProper f.left))
  have hq : prod.map (𝟙 X) f ≫ prod.map f (𝟙 Y) = prod.map f f := by simp
  apply mateEquiv_symm_app_comp_map_comp_eq
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f)
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (prod.map f f))
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (prod.map f (𝟙 Y)))
    _ _ _ (boundedConstructibleLowerShriek ℓ (prod.map (𝟙 X) f))
    _ _ _ (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ
      (IsPullback.of_prod_fst_with_id f Y).flip)
  case h₁ =>
    exact boundedConstructibleLowerShriekSquareIso_padicAlgCl_hom_app_comp ℓ
      hq (by simp) (prod.map_fst f f)
      (IsPullback.of_prod_fst_with_id f Y).flip.w
      ((boundedConstructibleUpperStar 𝐐 ℓ (prod.snd : X ⨯ X ⟶ X)).obj B)
  case h₂ =>
    exact unit_comp_lowerShriek_map_prodUpperStarCounit ℓ hq
      (IsPullback.of_prod_snd_with_id f X) (by simp) (prod.map_snd f f) B

end AlgebraicGeometry.ProEtale.CondensedRing
