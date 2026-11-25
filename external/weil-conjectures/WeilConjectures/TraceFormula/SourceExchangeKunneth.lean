/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeBaseChange
public import WeilConjectures.TraceFormula.SourceExchangeKunnethAux
public import WeilConjectures.TraceFormula.SourceExchangeProjection

/-!

# The kernel pushforward and the Künneth–Verdier isomorphisms

Identity (a) of the trace-class source exchange (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3): `κ_Y ∘ ρ_f = Φ ∘ Rq_* κ_X`
(`ProEtale.CondensedRing.kernelPushforward_comp_kunnethVerdierMap`). Both sides are compared
through their test maps (`classTest`). The test map of `κ` is the evaluation followed by the
adjoint of the exceptional Künneth map (`ProEtale.CondensedRing.classTest_kunnethVerdierMap`);
the evaluation part is `ProEtale.CondensedRing.evaluation_comp_prodLowerStarExternalProduct`,
and the exceptional Künneth part is
`ProEtale.CondensedRing.lowerShriek_map_trace_comp_exceptionalKunnethAdjoint`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Test

variable {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (M : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- The test map of the Künneth–Verdier map: the evaluation of `D_S M` against `Lp₂^* M`
followed by the adjoint of the exceptional Künneth map. -/
lemma classTest_kunnethVerdierMap :
    classTest ℓ M (kunnethVerdierMap ℓ M M) =
      (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).map
          ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
            (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
              (prod.snd : S ⨯ S ⟶ S)) _ _) ≫
            (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).map
              ((ihom.ev M).app (dualizingComplex' ℓ S)))) ≫
        exceptionalKunnethAdjoint ℓ M := by
  have h : kunnethVerdierPairing ℓ M M =
      ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
          (prod.snd : S ⨯ S ⟶ S)) _ _) ≫
        (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).map
          ((ihom.ev M).app (dualizingComplex' ℓ S)))) ≫
      ((boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : S ⨯ S ⟶ S)).homEquiv
        (externalProduct ℓ M (dualizingComplex' ℓ S)) M) (exceptionalKunnethAdjoint ℓ M) := by
    simp only [kunnethVerdierPairing, exceptionalKunnethMap, Category.assoc]
    rfl
  simp only [classTest, kunnethVerdierMap, uncurry_curry]
  refine (congrArg ((boundedConstructibleUpperShriekAdjunction ℓ
    (prod.fst : S ⨯ S ⟶ S)).homEquiv _ _).symm h).trans ?_
  exact Adjunction.homEquiv_symm_comp_homEquiv _ _ _

end Test

/-- The left projection morphism of a proper morphism after a unit. -/
lemma leftProjection_lowerShriek_unit_app {A B : Over (Spec (.of k))} [LocallyOfFiniteType A.hom]
    [QuasiCompact A.hom] [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated B.hom] (g : A ⟶ B) [IsProper g.left]
    (M W : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ◁ ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app W ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
          ((boundedConstructibleUpperStar _ ℓ g).obj W)) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ g) M
        ((boundedConstructibleUpperStar _ ℓ g).obj W) =
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app (M ⊗ W) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj (M ⊗ W)) ≫
      (boundedConstructibleLowerShriek ℓ g).map
        (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ g) M W) :=
  Verdier.leftProjection_unit_app (boundedConstructibleUpperStar _ ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleExceptionalProjection ℓ g)
    (fun T M ↦ upperStar_map_exceptionalProjection_comp_counit ℓ g T M)
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ ℓ g A B)
    (fun _ _ ↦ boundedConstructible_braiding_hom_braiding_hom _ _) M W

lemma _root_.CategoryTheory.Functor.map_whiskerLeft_comp_braiding_comp {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] [MonoidalCategory 𝒞] [MonoidalCategory 𝒟] [BraidedCategory 𝒟] (F : 𝒟 ⥤ 𝒞)
    (A : 𝒟) {W W' : 𝒟} (t : W ⟶ W') (M : 𝒞) (pf : ∀ V : 𝒟, F.obj (V ⊗ A) ⟶ F.obj V ⊗ M)
    (hpf : F.map (t ▷ A) ≫ pf W' = pf W ≫ (F.map t ▷ M)) {T Z : 𝒞} (b : F.obj W' ⟶ T)
    (rest : T ⊗ M ⟶ Z) :
    F.map (A ◁ t) ≫ F.map (β_ A W').hom ≫ pf W' ≫ (b ▷ M) ≫ rest =
      F.map (β_ A W).hom ≫ pf W ≫ ((F.map t ≫ b) ▷ M) ≫ rest := by
  rw [← F.map_comp_assoc, BraidedCategory.braiding_naturality_right, F.map_comp_assoc,
    reassoc_of% hpf, MonoidalCategory.comp_whiskerRight_assoc]

section ExceptionalKunneth

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

-- the compactly supported direct images are unfolded in the defeq checks
/-- The adjoint of the exceptional Künneth map precomposed with a map `t : N ⟶ ω_Y` in the second
factor: the counit of `Ra_Y! ⊣ Ra_Y^!` is precomposed with `Ra_Y! t`. -/
lemma lowerShriek_map_whiskerLeft_comp_exceptionalKunnethAdjoint
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj
        ℓ⟧}
    (t : N ⟶ dualizingComplex' ℓ Y) :
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M ◁
          (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map t) ≫
      exceptionalKunnethAdjoint ℓ M =
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map (β_ _ _).hom ≫
      inv (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N)).app M) ≫
      (((prodBaseChangeIso ℓ X Y).hom.app N ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriek ℓ (toPoint Y)).map t ≫
            (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _))) ▷ M) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv ▷ M) ≫
      (λ_ M).hom := by
  have hpf : (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map t ▷
        (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M) ≫
      inv (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
          (dualizingComplex' ℓ Y))).app M) =
      inv (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N)).app M) ≫
      ((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map t) ▷ M) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
    exact (boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ _ _ M).symm
  have hbc := (prodBaseChangeIso ℓ X Y).hom.naturality t
  simp only [Functor.comp_map] at hbc
  unfold exceptionalKunnethAdjoint externalProduct
  refine (Functor.map_whiskerLeft_comp_braiding_comp
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M)
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map t) M
    (fun V ↦ inv (((boundedConstructibleExceptionalProjection ℓ
        (prod.fst : X ⨯ Y ⟶ X)).app V).app M))
    hpf _ _).trans ?_
  rw [hbc]
  simp only [Category.assoc, Functor.map_comp, MonoidalCategory.comp_whiskerRight]

/-- The trace `τ_f` of a proper morphism followed by the counit of `Ra_Y! ⊣ Ra_Y^!` is the counit
of `Ra_X! ⊣ Ra_X^!` through `Rf_* ≅ Rf_!` and `R(f ≫ a_Y)_! ≅ Ra_Y! Rf_!` (the pasted counit of
`a_X = f ≫ a_Y`). -/
lemma lowerShriek_map_lowerStarDualizingComplexTrace_comp_counit (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructibleLowerShriek ℓ (toPoint Y)).map (lowerStarDualizingComplexTrace ℓ f) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _) =
    (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
          (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (toPoint Y)).inv.app
        (dualizingComplex' ℓ X) ≫
      eqToHom (by rw [comp_toPoint]; rfl) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).counit.app (𝟙_ _) := by
  have h : lowerStarDualizingComplexTrace ℓ f =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app _ ≫
        lowerShriekDualizingComplexTrace ℓ f := rfl
  rw [h, Functor.map_comp, Category.assoc,
    lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit]

end ExceptionalKunneth

section KernelPushforward

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

-- the compactly supported direct images are unfolded in the defeq checks
/-- The base-change core of the exceptional Künneth part of identity (a) (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3): the projection formula for `p₁'`,
compact-support base change in the product square of `Y` and the pasted counit of `a_X = f ≫ a_Y`
agree, through `Π_f`, `Rq_* ≅ Rq_!`, the composition law of `q ≫ p₁' = p₁ ≫ f` and `Rf_! ≅ Rf_*`,
with `Rf_!` of the projection formula for `p₁`, base change in the product square of `X` and the
counit of `a_X`. -/
theorem lowerShriek_exceptionalKunneth_baseChange :
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map (β_ _ _).hom ≫
      inv (((boundedConstructibleExceptionalProjection ℓ (prod.fst : Y ⨯ Y ⟶ Y)).app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj (dualizingComplex' ℓ X)))).app
        ((boundedConstructibleLowerStar ℓ f).obj K)) ≫
      (((prodBaseChangeIso ℓ Y Y).hom.app
          ((boundedConstructibleLowerStar ℓ f).obj (dualizingComplex' ℓ X)) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint Y)).map
          ((boundedConstructibleLowerShriek ℓ (toPoint Y)).map
              ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
                (dualizingComplex' ℓ X)) ≫
            (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (toPoint Y)).inv.app
              (dualizingComplex' ℓ X) ≫
            eqToHom (by rw [comp_toPoint]; rfl) ≫
            (boundedConstructibleUpperShriekAdjunction ℓ (toPoint X)).counit.app (𝟙_ _))) ▷
        (boundedConstructibleLowerStar ℓ f).obj K) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint Y))).inv ▷ _) ≫
      (λ_ _).hom =
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        (prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
          (externalProduct ℓ K (dualizingComplex' ℓ X))) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app
        (externalProduct ℓ K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek ℓ f).map (exceptionalKunnethAdjoint ℓ K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K :=
  by
  have : IsProper (prod.map f (𝟙 Y)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id f Y).map (Over.forget _))
      (inferInstanceAs (IsProper f.left))
  have : IsProper (prod.map (𝟙 X) f).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_snd_with_id f X).map (Over.forget _))
      (inferInstanceAs (IsProper f.left))
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (isPullback_prod_toPoint Y Y)
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (isPullback_prod_toPoint X X)
  unfold exceptionalKunnethAdjoint prodBaseChangeIso prodLowerStarExternalProduct externalProduct
  simp only [Iso.symm_hom, asIso_inv]
  have hg := lowerShriek_exceptionalKunneth_baseChange_generic ℓ (toPoint X) (toPoint Y) f prod.fst
    prod.snd prod.fst prod.snd (prod.fst : X ⨯ Y ⟶ X) prod.snd (prod.map f (𝟙 Y))
    (prod.map (𝟙 X) f) (prod.map f f) (IsPullback.of_prod_fst_with_id f Y).flip
    (IsPullback.of_prod_snd_with_id f X) (isPullback_prod_toPoint Y Y) (isPullback_prod_toPoint X X)
    (by simp) (by simp) (by ext <;> simp) (comp_toPoint f) (prod.map_fst f f) (prod.map_snd f f) K
  refine Eq.trans ?_ (hg.trans ?_)
  · rfl
  · rfl

/-- **The exceptional Künneth adjoint commutes with a proper pushforward** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3): through `Π_f`, `Rq_* ≅ Rq_!`, the
composition law of the square `q ≫ p₁' = p₁ ≫ f` and `Rf_! ≅ Rf_*`, the adjoint of the exceptional
Künneth map of `Rf_* K` precomposed with the trace `τ_f` is `Rf_*` of that of `K`. -/
theorem lowerShriek_map_trace_comp_exceptionalKunnethAdjoint :
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar ℓ f).obj K) ◁
          (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
            (lowerStarDualizingComplexTrace ℓ f)) ≫
      exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar ℓ f).obj K) =
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        (prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
          (externalProduct ℓ K (dualizingComplex' ℓ X))) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app
        (externalProduct ℓ K (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleLowerShriek ℓ f).map (exceptionalKunnethAdjoint ℓ K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K :=
  by
  refine (lowerShriek_map_whiskerLeft_comp_exceptionalKunnethAdjoint ℓ _ _).trans ?_
  rewrite [lowerShriek_map_lowerStarDualizingComplexTrace_comp_counit ℓ f]
  exact lowerShriek_exceptionalKunneth_baseChange ℓ f K

omit [IsProper f.left] in
/-- The transported counits of `q = f × f` are compatible with the multiplication `μ_f`. -/
theorem upperStar_map_tensorMap_comp_prodUpperStarCounit
    (B₁ B₂ B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (e : B₁ ⊗ B₂ ⟶ B) :
    (boundedConstructibleUpperStar _ ℓ (prod.map f f)).map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
            ((boundedConstructibleLowerStar ℓ f).obj B₁)
            ((boundedConstructibleLowerStar ℓ f).obj B₂) ≫
          (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
            (lowerStarTensorMap ℓ f B₁ B₂ ≫ (boundedConstructibleLowerStar ℓ f).map e)) ≫
      prodUpperStarCounit ℓ (prod.map_snd f f) B =
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ (prod.map f f)) _ _ ≫
      (prodUpperStarCounit ℓ (prod.map_snd f f) B₁ ⊗ₘ prodUpperStarCounit ℓ (prod.map_snd f f) B₂) ≫
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)) B₁ B₂ ≫
      (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map e :=
  by
  have hnat : ∀ {M M' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (g : M ⟶ M'),
      (boundedConstructibleUpperStar _ ℓ (prod.map f f)).map
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map g) ≫
        ((boundedConstructibleUpperStarComp _ ℓ (prod.map f f) prod.snd).inv.app M' ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar _ ℓ u).obj M')
            (prod.map_snd f f)) ≫
          (boundedConstructibleUpperStarComp _ ℓ (prod.snd : X ⨯ X ⟶ X) f).hom.app M') =
      ((boundedConstructibleUpperStarComp _ ℓ (prod.map f f) prod.snd).inv.app M ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar _ ℓ u).obj M)
            (prod.map_snd f f)) ≫
          (boundedConstructibleUpperStarComp _ ℓ (prod.snd : X ⨯ X ⟶ X) f).hom.app M) ≫
        (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map
          ((boundedConstructibleUpperStar _ ℓ f).map g) := by
    intro M M' g
    have h₁ := (boundedConstructibleUpperStarComp _ ℓ (prod.map f f) prod.snd).inv.naturality g
    have h₃ := (boundedConstructibleUpperStarComp _ ℓ (prod.snd : X ⨯ X ⟶ X) f).hom.naturality g
    simp only [Functor.comp_map] at h₁ h₃
    rw [reassoc_of% h₁, upperStar_map_comp_eqToHom_congrArg_assoc ℓ _ (prod.map_snd f f) g, h₃]
    simp only [Category.assoc]
  exact Adjunction.map_μ_comp_homEquiv_comp _ _ _ _
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f) _ hnat
    (fun M₁ M₂ ↦ by
      simp only [Category.assoc]
      exact upperStarComp_square_tensor_δ ℓ (prod.map_snd f f) M₁ M₂) _
    (fun B ↦ by simp only [prodUpperStarCounit, Category.assoc]) B₁ B₂ B e

/-- The evaluation part of identity (a) (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3): `Π_f` and `μ_f` are adjoint to the
counits of `f`. -/
theorem evaluation_comp_prodLowerStarExternalProduct :
    (α_ _ _ _).inv ≫ ((β_ ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K))
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K))).hom ▷ _) ≫ (α_ _ _ _).hom ≫
      (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
        ((boundedConstructibleLowerStar ℓ f).obj K)
        ((boundedConstructibleLowerStar ℓ f).obj (verdierDual ℓ K))) ≫
      (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
        (lowerStarTensorMap ℓ f K (verdierDual ℓ K) ≫
          (boundedConstructibleLowerStar ℓ f).map ((ihom.ev K).app (dualizingComplex' ℓ X)))) ≫
      prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
        (externalProduct ℓ K (dualizingComplex' ℓ X)) =
    (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
        ((boundedConstructibleLowerStar ℓ f).obj K) ◁
      (prodLowerStarExternalProduct ℓ f f K (verdierDual ℓ K) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
          (externalProduct ℓ K (verdierDual ℓ K))) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ (prod.map f f))
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K))
        (externalProduct ℓ K (verdierDual ℓ K)) ≫
      (boundedConstructibleLowerShriek ℓ (prod.map f f)).map
        ((prodUpperStarCounit ℓ (prod.map_snd f f) K ▷ _) ≫
          (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
          (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
            (prod.snd : X ⨯ X ⟶ X)) _ _) ≫
          (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map
            ((ihom.ev K).app (dualizingComplex' ℓ X)))) :=
  by
  unfold prodLowerStarExternalProduct
  refine Verdier.comp_homEquiv_comp_eq_whiskerLeft_homEquiv_comp_leftProjection _ _ _ _
    (fun M W ↦ leftProjection_lowerShriek_unit_app ℓ (prod.map f f) M W) _ _ _ _ _ _ _ _ ?_
  simp only [Functor.Monoidal.μIso_inv]
  exact Functor.OplaxMonoidal.map_evaluation_comp_δ _
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ ℓ (prod.map f f) A B)
    _ _ _ _ _ _ _ _ (upperStar_map_tensorMap_comp_prodUpperStarCounit ℓ f _ _ _ _)

end KernelPushforward

end AlgebraicGeometry.ProEtale.CondensedRing
