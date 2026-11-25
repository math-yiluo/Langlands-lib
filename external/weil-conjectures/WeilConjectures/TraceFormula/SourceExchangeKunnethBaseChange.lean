/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeKunnethMate
public import WeilConjectures.TraceFormula.SourceExchangeKunnethUnit

/-!

# Base change along the Künneth square of a proper morphism

For a proper morphism `f : X ⟶ Y` and `q = f × f : X × X ⟶ Y × Y`, the base change along the
non-cartesian square `q ≫ p₁' = p₁ ≫ f` (the mate of its composition isomorphism) is compared
with the compact-support base changes of the product squares of `X` and `Y` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3). This is the base-change input of the
exceptional Künneth part of identity (a) of the trace-class source exchange
(`ProEtale.CondensedRing.unit_comp_lowerShriek_map_prodBaseChangeIso`). The comparison goes
through the factorization `q = (1 × f) ≫ (f × 1)` and the cartesian squares
`(f × 1) ≫ p₁' = p_X ≫ f` and `(1 × f) ≫ p_Y = p₂ ≫ f`, using the pasting laws of `Ex_!`
(blueprint `proposition-composition-base-change-rf-shriek`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

/-- A diagram chase for two pasted base-change squares, expressed in abstract functors. -/
private lemma CategoryTheory.Functor.comp_baseChangeIso_of_paste
    {CS CX CY CP CW CV : Type*}
    [Category CS] [Category CX] [Category CY] [Category CP] [Category CW] [Category CV]
    (fU : CY ⥤ CX) (fL : CX ⥤ CY) (aYL : CY ⥤ CS) (aYU : CS ⥤ CY)
    (aXL : CX ⥤ CS) (aXU : CS ⥤ CX) (p₁YL : CV ⥤ CY) (p₂YU : CY ⥤ CV)
    (p₁XL : CW ⥤ CX) (p₂XU : CX ⥤ CW) (pXL : CP ⥤ CX) (pYU : CY ⥤ CP)
    (hU : CV ⥤ CP) (gL : CW ⥤ CP)
    (aU : aXU ≅ aYU ⋙ fU) (aL : aXL ≅ fL ⋙ aYL)
    (pU : pYU ≅ p₂YU ⋙ hU) (pL : p₁XL ≅ gL ⋙ pXL)
    (s₁ : p₁YL ⋙ fU ⟶ hU ⋙ pXL) (s₃ : fL ⋙ pYU ⟶ p₂XU ⋙ gL)
    (β : aYL ⋙ aXU ⟶ pYU ⋙ pXL)
    (γX : p₂XU ⋙ p₁XL ≅ aXL ⋙ aXU) (γY : p₂YU ⋙ p₁YL ≅ aYL ⋙ aYU)
    (B : CX) {R : CY} (i : R ⟶ fL.obj B)
    (hV : γX.inv.app B = aXU.map (aL.hom.app B) ≫ β.app (fL.obj B) ≫
      pXL.map (s₃.app B) ≫ pL.inv.app (p₂XU.obj B))
    (hH : β.app (fL.obj B) = aU.hom.app (aYL.obj (fL.obj B)) ≫
      fU.map (γY.inv.app (fL.obj B)) ≫ s₁.app (p₂YU.obj (fL.obj B)) ≫
      pXL.map (pU.inv.app (fL.obj B))) :
    (s₁.app (p₂YU.obj R) ≫
      pXL.map (pU.inv.app R ≫ pYU.map i ≫ s₃.app B) ≫
      pL.inv.app (p₂XU.obj B)) ≫ γX.hom.app B =
    fU.map (γY.hom.app R) ≫ aU.inv.app (aYL.obj R) ≫
      aXU.map (aYL.map i ≫ aL.inv.app B) := by
  have nY := γY.inv.naturality i
  have n₁ := s₁.naturality (p₂YU.map i)
  have nC := aU.hom.naturality (aYL.map i)
  have nC' := pU.inv.naturality i
  simp only [Functor.comp_map, Functor.comp_obj] at nY n₁ nC nC'
  rw [← cancel_mono (γX.inv.app B)]
  simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  rw [hV, hH]
  simp only [Functor.map_comp, Category.assoc]
  have c₁ : aXU.map (aL.inv.app B) ≫ aXU.map (aL.hom.app B) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have c₂ : fU.map (γY.hom.app R) ≫ fU.map (aYU.map (aYL.map i)) ≫
      fU.map (γY.inv.app (fL.obj B)) = fU.map (p₁YL.map (p₂YU.map i)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, nY, Iso.hom_inv_id_app_assoc]
  have c₃ : pXL.map (hU.map (p₂YU.map i)) ≫ pXL.map (pU.inv.app (fL.obj B)) =
      pXL.map (pU.inv.app R) ≫ pXL.map (pYU.map i) := by
    rw [← Functor.map_comp, ← Functor.map_comp, nC']
  simp only [reassoc_of% c₁]
  rw [reassoc_of% nC, Iso.inv_hom_id_app_assoc, reassoc_of% c₂, reassoc_of% n₁, reassoc_of% c₃]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

section Pasting

variable {S P W V : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

/-- The compact-support base changes of the product squares of `X` and `Y` (here abstract
cartesian squares over a base `S`) are compatible along a proper `f : X ⟶ Y`: pasting the
cartesian squares `h ≫ p₁' = p_X ≫ f` and `g ≫ p_Y = p₂ ≫ f` with the product squares,
`Ex_!` of the square of `X` is read off from `Ex_!` of the square of `Y`. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_prod_paste (aX : X ⟶ S) (aY : Y ⟶ S)
    (hA : f ≫ aY = aX)
    {pX : P ⟶ X} {pY : P ⟶ Y} {p₁ p₂ : W ⟶ X} {p₁' p₂' : V ⟶ Y} {g : W ⟶ P} {h : P ⟶ V}
    (hp : g ≫ pX = p₁) (hpY : h ≫ p₂' = pY) (sqY : IsPullback p₂' p₁' aY aY)
    (sqXY : IsPullback pY pX aY aX) (sqX : IsPullback p₂ p₁ aX aX) (s₁ : IsPullback h pX p₁' f)
    (s₃ : IsPullback p₂ g f pY) (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (γY : boundedConstructibleUpperStar _ ℓ p₂' ⋙ boundedConstructibleLowerShriek ℓ p₁' ≅
      boundedConstructibleLowerShriek ℓ aY ⋙ boundedConstructibleUpperStar _ ℓ aY)
    (hγY : γY.inv = boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY)
    (γX : boundedConstructibleUpperStar _ ℓ p₂ ⋙ boundedConstructibleLowerShriek ℓ p₁ ≅
      boundedConstructibleLowerShriek ℓ aX ⋙ boundedConstructibleUpperStar _ ℓ aX)
    (hγX : γX.inv = boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqX) :
    (((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₁).app
        ((boundedConstructibleUpperStar _ ℓ p₂').obj
          ((boundedConstructibleLowerStar ℓ f).obj B)) :
      (boundedConstructibleUpperStar _ ℓ f).obj ((boundedConstructibleLowerShriek ℓ p₁').obj
        ((boundedConstructibleUpperStar _ ℓ p₂').obj
          ((boundedConstructibleLowerStar ℓ f).obj B))) ⟶
      (boundedConstructibleLowerShriek ℓ pX).obj ((boundedConstructibleUpperStar _ ℓ h).obj
        ((boundedConstructibleUpperStar _ ℓ p₂').obj
          ((boundedConstructibleLowerStar ℓ f).obj B)))) ≫
      (boundedConstructibleLowerShriek ℓ pX).map
        ((boundedConstructibleUpperStarComp _ ℓ h p₂').inv.app
            ((boundedConstructibleLowerStar ℓ f).obj B) ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
            ((boundedConstructibleLowerStar ℓ f).obj B)) hpY) ≫
          (boundedConstructibleUpperStar _ ℓ pY).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B) ≫
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₃).app B) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g pX).inv.app
        ((boundedConstructibleUpperStar _ ℓ p₂).obj B) ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj
        ((boundedConstructibleUpperStar _ ℓ p₂).obj B)) hp)) ≫
      γX.hom.app B =
    (boundedConstructibleUpperStar _ ℓ f).map
        (γY.hom.app ((boundedConstructibleLowerStar ℓ f).obj B) :
          (boundedConstructibleLowerShriek ℓ p₁').obj ((boundedConstructibleUpperStar _ ℓ p₂').obj
            ((boundedConstructibleLowerStar ℓ f).obj B)) ⟶
          (boundedConstructibleUpperStar _ ℓ aY).obj ((boundedConstructibleLowerShriek ℓ aY).obj
            ((boundedConstructibleLowerStar ℓ f).obj B))) ≫
      (boundedConstructibleUpperStarComp _ ℓ f aY).inv.app _ ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
        ((boundedConstructibleLowerShriek ℓ aY).obj
          ((boundedConstructibleLowerStar ℓ f).obj B))) hA) ≫
      (boundedConstructibleUpperStar _ ℓ aX).map
        ((boundedConstructibleLowerShriek ℓ aY).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).inv.app B ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj B) hA)) := by
  subst hA hp hpY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Functor.comp_baseChangeIso_of_paste
    (boundedConstructibleUpperStar _ ℓ f) (boundedConstructibleLowerShriek ℓ f)
    (boundedConstructibleLowerShriek ℓ aY) (boundedConstructibleUpperStar _ ℓ aY)
    (boundedConstructibleLowerShriek ℓ (f ≫ aY))
    (boundedConstructibleUpperStar _ ℓ (f ≫ aY))
    (boundedConstructibleLowerShriek ℓ p₁') (boundedConstructibleUpperStar _ ℓ p₂')
    (boundedConstructibleLowerShriek ℓ (g ≫ pX)) (boundedConstructibleUpperStar _ ℓ p₂)
    (boundedConstructibleLowerShriek ℓ pX) (boundedConstructibleUpperStar _ ℓ (h ≫ p₂'))
    (boundedConstructibleUpperStar _ ℓ h) (boundedConstructibleLowerShriek ℓ g)
    (boundedConstructibleUpperStarComp _ ℓ f aY)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY)
    (boundedConstructibleUpperStarComp _ ℓ h p₂')
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g pX)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₁)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₃)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqXY) γX γY B
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B)
  · rw [hγX]
    exact boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert ℓ s₃ sqXY B
  · rw [hγY]
    exact boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ s₁ sqY _

end Pasting

/-- An abstract chain of identities for an adjunction `L ⊣ R`: an identity
`U ≫ R θ = φ ≫ η ≫ R ε` is obtained from identities for the transpose of `U` (a mate), a pasting
of base changes and a unit compatibility. -/
lemma _root_.CategoryTheory.Adjunction.comp_map_eq_comp_unit_comp_map_of_mate {𝒞 𝒟 ℰ : Type*}
    [Category 𝒞] [Category 𝒟] [Category ℰ] {L : 𝒟 ⥤ 𝒞} {R : 𝒞 ⥤ 𝒟} (adj : L ⊣ R)
    (GX : ℰ ⥤ 𝒞) (GY : ℰ ⥤ 𝒟) {A A₁ O' : 𝒟} {Bo C₁ O I : 𝒞} {Q₀ Q₁ Q₂ Q₃ Q₄ : ℰ}
    {u₁ : A ⟶ A₁} {u₂ : A₁ ⟶ R.obj Bo} {c : Bo ⟶ C₁} {β : C₁ ⟶ GX.obj Q₃} {k : Q₃ ⟶ Q₄}
    {t₂ : GX.obj Q₄ ⟶ O} {φ₁ : A ⟶ GY.obj Q₀} {ρ₁ : Q₀ ⟶ Q₁} {ρ₂ : Q₁ ⟶ Q₂} {ρ₃ : Q₂ ⟶ Q₃}
    {e' : GY.obj Q₄ ⟶ O'} {εf : L.obj O' ⟶ O} {m : L.obj A ⟶ C₁} {ι₁ : L.obj (GY.obj Q₀) ⟶ I}
    {ι₂ : I ⟶ GX.obj Q₀}
    (hM : L.map u₁ ≫ L.map u₂ ≫ adj.counit.app Bo ≫ c = m)
    (hP : m ≫ β = L.map φ₁ ≫ ι₁ ≫ ι₂ ≫ GX.map (ρ₁ ≫ ρ₂ ≫ ρ₃))
    (hU : L.map (GY.map (ρ₁ ≫ ρ₂ ≫ ρ₃ ≫ k)) ≫ L.map e' ≫ εf =
      (ι₁ ≫ ι₂) ≫ GX.map (ρ₁ ≫ ρ₂ ≫ ρ₃ ≫ k) ≫ t₂) :
    (u₁ ≫ u₂) ≫ R.map (c ≫ β ≫ GX.map k ≫ t₂) =
      (φ₁ ≫ GY.map (ρ₁ ≫ ρ₂ ≫ ρ₃ ≫ k) ≫ e') ≫ adj.unit.app O' ≫ R.map εf := by
  apply (adj.homEquiv _ _).symm.injective
  have hM' := hM =≫ (β ≫ GX.map k ≫ t₂)
  simp only [Category.assoc] at hM'
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality_assoc, Adjunction.counit_naturality, Functor.comp_obj,
    Adjunction.left_triangle_components_assoc]
  rw [hM', reassoc_of% hP]
  simp only [Functor.map_comp, Category.assoc] at hU ⊢
  rw [hU]

omit [IsProper f.left] in
/-- The identification `Lf^* La_Y^* ≅ La_X^*` (for `f ≫ a_Y = a_X`) is compatible with the unit
isomorphisms of the monoidal functors `La_Y^*`, `La_X^*` and `Lf^*`. -/
lemma upperStar_map_upperStar_map_comp_εIso_inv {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (aX : X ⟶ S)
    (aY : Y ⟶ S) (hA : f ≫ aY = aX) {V : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (v : V ⟶ 𝟙_ _) :
    (boundedConstructibleUpperStar _ ℓ f).map ((boundedConstructibleUpperStar _ ℓ aY).map v) ≫
      (boundedConstructibleUpperStar _ ℓ f).map
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ aY)).inv ≫
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ f)).inv =
    ((boundedConstructibleUpperStarComp _ ℓ f aY).inv.app V ≫
        eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj V) hA)) ≫
      (boundedConstructibleUpperStar _ ℓ aX).map v ≫
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ aX)).inv := by
  subst hA
  have hu := boundedConstructibleUpperStarComp_hom_app_unit ℓ f aY
  have hn := (boundedConstructibleUpperStarComp _ ℓ f aY).inv.naturality v
  simp only [Functor.comp_map] at hn
  rw [← hu, eqToHom_refl, Category.comp_id, ← reassoc_of% hn, Iso.inv_hom_id_app_assoc]

/-- **Base change along the Künneth square of a proper morphism** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3): the unit of `Lq^* ⊣ Rq_!` for
`q = f × f`, followed by the composition isomorphism of `q ≫ p₁' = p₁ ≫ f`, the transported counit,
the compact-support base change of the product square of `X` and the counit of `Ra_X! ⊣ Ra_X^!`, is
the compact-support base change of the product square of `Y` followed by
`Ra_Y! Rf_* ω_X ≅ Ra_X! ω_X`, the counit of `Ra_X! ⊣ Ra_X^!` and the unit `𝟙 ⟶ Rf_! 𝟙`. -/
theorem unit_comp_lowerShriek_map_prodBaseChangeIso :
    ((boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (prod.map f f)).unit.app
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar ℓ f).obj (dualizingComplex' ℓ X)))) ≫
      ((boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app _ :
        _ ⟶ (boundedConstructibleLowerShriek ℓ f).obj
          ((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj
            ((boundedConstructibleUpperStar _ ℓ (prod.map f f)).obj
              ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
                ((boundedConstructibleLowerStar ℓ f).obj (dualizingComplex' ℓ X))))))) ≫
    (boundedConstructibleLowerShriek ℓ f).map
      ((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X)).map
          (prodUpperStarCounit ℓ (prod.map_snd f f) (dualizingComplex' ℓ X)) ≫
        (prodBaseChangeIso ℓ X X).hom.app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).counit.app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv) =
    ((prodBaseChangeIso ℓ Y Y).hom.app
        ((boundedConstructibleLowerStar ℓ f).obj (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleUpperStar _ ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriek ℓ (toPoint Y)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
              (dualizingComplex' ℓ X)) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (toPoint Y)).inv.app
            (dualizingComplex' ℓ X) ≫
          eqToHom (by rw [comp_toPoint]; rfl) ≫
          (boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).counit.app (𝟙_ _)) ≫
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint Y))).inv) ≫
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app (𝟙_ _) ≫
    (boundedConstructibleLowerShriek ℓ f).map
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ f)).inv := by
  apply Adjunction.comp_map_eq_comp_unit_comp_map_of_mate
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f)
    (boundedConstructibleUpperStar _ ℓ (toPoint X)) (boundedConstructibleUpperStar _ ℓ (toPoint Y))
  case hM =>
    have h := upperStar_map_unit_comp_squareIso_comp_counit_comp_prodUpperStarCounit ℓ f
      (dualizingComplex' ℓ X)
    convert h using 1
  case hP =>
    have h := boundedConstructibleLowerShriekBaseChange_padicAlgCl_prod_paste ℓ f (toPoint X)
      (toPoint Y) (comp_toPoint f)
      (by simp) (by simp) (isPullback_prod_toPoint Y Y) (isPullback_prod_toPoint X Y)
      (isPullback_prod_toPoint X X) (IsPullback.of_prod_fst_with_id f Y).flip
      (IsPullback.of_prod_snd_with_id f X) (dualizingComplex' ℓ X) (prodBaseChangeIso ℓ Y Y) rfl
      (prodBaseChangeIso ℓ X X) rfl
    exact h
  case hU =>
    have h := upperStar_map_upperStar_map_comp_εIso_inv ℓ f (toPoint X) (toPoint Y)
      (comp_toPoint f)
      ((boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
            (dualizingComplex' ℓ X)) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (toPoint Y)).inv.app
          (dualizingComplex' ℓ X) ≫
        eqToHom (by rw [comp_toPoint]; rfl) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).counit.app (𝟙_ _))
    exact h

/-- An abstract chain of identities in monoidal categories: through a functor `F`, a map
`U ▷ M` followed by `P` and `F` of an evaluation `θ` is rewritten, given the naturality of `P`
in `θ`, a factorization of `U ≫ F θ`, the unit compatibility of `P₁` and a triangle identity. -/
lemma _root_.CategoryTheory.Functor.whiskerRight_comp_map_comp_eq {𝒳 𝒟 : Type*} [Category 𝒳]
    [Category 𝒟] [MonoidalCategory 𝒳] [MonoidalCategory 𝒟] (F : 𝒳 ⥤ 𝒟) {R M' K N : 𝒳}
    {A B₁ B₂ M : 𝒟} {U : A ⟶ F.obj R} {θ : R ⟶ 𝟙_ 𝒳} {e : M' ⟶ K}
    {P : F.obj R ⊗ M ⟶ F.obj (R ⊗ M')} {P₁ : F.obj (𝟙_ 𝒳) ⊗ M ⟶ F.obj (𝟙_ 𝒳 ⊗ M')}
    {φ₁ : A ⟶ B₁} {φ₂ : B₁ ⟶ B₂} {ε' : B₂ ⟶ 𝟙_ 𝒟} {η₁ : 𝟙_ 𝒟 ⟶ F.obj N}
    {ε₂ : N ⟶ 𝟙_ 𝒳} {ηM : M ⟶ F.obj M'} {r : F.obj K ⟶ M}
    (hP : P ≫ F.map (θ ▷ M') = (F.map θ ▷ M) ≫ P₁)
    (hB : U ≫ F.map θ = (φ₁ ≫ φ₂ ≫ ε') ≫ η₁ ≫ F.map ε₂)
    (hU : ((η₁ ≫ F.map ε₂) ▷ M) ≫ P₁ ≫ F.map (λ_ M').hom = (λ_ M).hom ≫ ηM)
    (hT : ηM ≫ F.map e ≫ r = 𝟙 M) :
    (U ▷ M) ≫ P ≫ F.map ((θ ▷ M') ≫ (𝟙_ 𝒳 ◁ e) ≫ (λ_ K).hom) ≫ r =
      ((φ₁ ≫ φ₂) ▷ M) ≫ (ε' ▷ M) ≫ (λ_ M).hom := by
  have hU' := hU =≫ (F.map e ≫ r)
  simp only [Category.assoc, hT, Category.comp_id, comp_whiskerRight] at hU'
  have hB' : (U ▷ M) ≫ (F.map θ ▷ M) = ((φ₁ ≫ φ₂ ≫ ε') ▷ M) ≫ ((η₁ ≫ F.map ε₂) ▷ M) := by
    rw [← comp_whiskerRight, hB, comp_whiskerRight]
  rw [leftUnitor_naturality]
  simp only [F.map_comp, Category.assoc, reassoc_of% hP, reassoc_of% hB', hU', comp_whiskerRight]

/-- The triangle identity for `Lf^* ⊣ Rf_!` read through `Rf_! ≅ Rf_*`: the unit at `Rf_* K`
followed by `Rf_!` of the counit of `Lf^* ⊣ Rf_*` is `Rf_* K ≅ Rf_! K` inverted. -/
lemma unit_app_comp_lowerShriek_map_counit_app_comp_hom_app :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app
        ((boundedConstructibleLowerStar ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K :
          (boundedConstructibleUpperStar _ ℓ f).obj ((boundedConstructibleLowerStar ℓ f).obj K) ⟶
            K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K = 𝟙 _ := by
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  have hn := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K)
  rw [← reassoc_of% hn, Iso.inv_hom_id_app]
  rw [Category.comp_id]
  exact (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).right_triangle_components K

/-- The final step of the exceptional Künneth part of identity (a): after the projection
formula for `f`, the base change along the Künneth square and the unit compatibility of the
projection formula turn `Rf_!` of the evaluation into the evaluation on `Y`. -/
theorem whiskerRight_unit_square_comp_exceptionalProjection :
    (((boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
            (prod.map f f)).unit.app
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar ℓ f).obj (dualizingComplex' ℓ X)))) ≫
        ((boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app _ :
          _ ⟶ (boundedConstructibleLowerShriek ℓ f).obj
            ((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj
              ((boundedConstructibleUpperStar _ ℓ (prod.map f f)).obj
                ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
                  ((boundedConstructibleLowerStar ℓ f).obj (dualizingComplex' ℓ X))))))) ▷
          (boundedConstructibleLowerStar ℓ f).obj K) ≫
      boundedConstructibleExceptionalProjectionMorphism ℓ f _ _ ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X)).map
            (prodUpperStarCounit ℓ (prod.map_snd f f) (dualizingComplex' ℓ X)) ≫
          (prodBaseChangeIso ℓ X X).hom.app (dualizingComplex' ℓ X) ≫
          (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
            ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).counit.app (𝟙_ _)) ≫
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv) ▷ _) ≫
        (𝟙_ _ ◁ ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K :
          (boundedConstructibleUpperStar _ ℓ f).obj ((boundedConstructibleLowerStar ℓ f).obj K) ⟶
            K)) ≫
        (λ_ K).hom) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K =
    (((prodBaseChangeIso ℓ Y Y).hom.app
        ((boundedConstructibleLowerStar ℓ f).obj (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleUpperStar _ ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriek ℓ (toPoint Y)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
              (dualizingComplex' ℓ X)) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (toPoint Y)).inv.app
            (dualizingComplex' ℓ X) ≫
          eqToHom (by rw [comp_toPoint]; rfl) ≫
          (boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).counit.app (𝟙_ _))) ▷ _) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint Y))).inv ▷ _) ≫
    (λ_ _).hom := by
  have hP := (boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ f
    ((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X)).map
        (prodUpperStarCounit ℓ (prod.map_snd f f) (dualizingComplex' ℓ X)) ≫
      (prodBaseChangeIso ℓ X X).hom.app (dualizingComplex' ℓ X) ≫
      (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
        ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).counit.app (𝟙_ _)) ≫
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv)
    ((boundedConstructibleLowerStar ℓ f).obj K)).symm
  have hB := unit_comp_lowerShriek_map_prodBaseChangeIso ℓ f
  have hU := whiskerRight_unit_comp_exceptionalProjection_tensorUnit ℓ f
    ((boundedConstructibleLowerStar ℓ f).obj K)
  have hT := unit_app_comp_lowerShriek_map_counit_app_comp_hom_app ℓ f K
  apply Functor.whiskerRight_comp_map_comp_eq (boundedConstructibleLowerShriek ℓ f)
  case hP => exact hP
  case hB => exact hB
  case hU => exact hU
  case hT => exact hT

end AlgebraicGeometry.ProEtale.CondensedRing
