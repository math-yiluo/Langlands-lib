/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleSquareCoherence
public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.TraceFormula.SourceExchangeLeftTranspose
public import WeilConjectures.TraceFormula.SourceExchangeRightTranspose

/-!

# The base-change core of the exceptional Künneth part of the source exchange

The base-change core of the exceptional Künneth part of the source exchange
(blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 3), for a proper `f : X ⟶ Y`, in
a generic form (`ProEtale.CondensedRing.lowerShriek_exceptionalKunneth_baseChange_generic`). It is
proved by transposing both sides along `Lf^* ⊣ Rf_*` (`sourceExchange_leftTranspose`,
`sourceExchange_rightTranspose`) and comparing them on `X × Y` (`sourceExchange_coreTail`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section CoreAbstract

variable {𝒲 𝒰 : Type*} [Category 𝒲] [Category 𝒰] [MonoidalCategory 𝒲] [MonoidalCategory 𝒰]
  (G : 𝒲 ⥤ 𝒰) [G.Monoidal] {L : 𝒰 ⥤ 𝒲} (adj : G ⊣ L)
  (pf : ∀ (T : 𝒰) (M : 𝒲), L.obj T ⊗ M ⟶ L.obj (T ⊗ G.obj M))

/-- The projection morphism after a unit, for a projection morphism adjoint to the counit. -/
lemma Adjunction.unit_whiskerRight_comp_projection
    (hcounit : ∀ (T : 𝒰) (M : 𝒲), G.map (pf T M) ≫ adj.counit.app (T ⊗ G.obj M) =
      Functor.OplaxMonoidal.δ G (L.obj T) M ≫ adj.counit.app T ▷ G.obj M) (A M : 𝒲) :
    adj.unit.app A ▷ M ≫ pf (G.obj A) M =
      adj.unit.app (A ⊗ M) ≫ L.map (Functor.OplaxMonoidal.δ G A M) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hcounit]
  have h₁ := Functor.OplaxMonoidal.δ_natural_left G (adj.unit.app A) M
  have h₂ := adj.counit.naturality (Functor.OplaxMonoidal.δ G A M)
  simp only [Functor.comp_map, Functor.id_map] at h₂
  rw [← reassoc_of% h₁, ← MonoidalCategory.comp_whiskerRight, adj.left_triangle_components,
    MonoidalCategory.id_whiskerRight, Category.comp_id, h₂]
  simp

/-- The abstract form of the core identity of the base-change part of the source exchange. -/
lemma Adjunction.comp_tensorHom_eq_unit_comp_map_comp_inv_projection
    (hcounit : ∀ (T : 𝒰) (M : 𝒲), G.map (pf T M) ≫ adj.counit.app (T ⊗ G.obj M) =
      Functor.OplaxMonoidal.δ G (L.obj T) M ≫ adj.counit.app T ▷ G.obj M)
    (hnatl : ∀ {T T' : 𝒰} (x : T ⟶ T') (M : 𝒲),
      L.map x ▷ M ≫ pf T' M = pf T M ≫ L.map (x ▷ G.obj M))
    (hnatr : ∀ (T : 𝒰) {M M' : 𝒲} (y : M ⟶ M'),
      L.obj T ◁ y ≫ pf T M' = pf T M ≫ L.map (T ◁ G.map y))
    {V V' A M M' B : 𝒲} {T₀ T : 𝒰} (g₁ : V ⟶ V') (g₂ : V' ⟶ A ⊗ M)
    (φ₁ : G.obj V ⟶ T₀) (φ₂ : T₀ ⟶ T ⊗ G.obj M')
    [IsIso (pf T M')] (x : G.obj A ⟶ T) (y : M ⟶ M') (e : L.obj T ⟶ B) (z : A ⟶ B)
    (h₁ : φ₁ ≫ φ₂ = G.map (g₁ ≫ g₂) ≫ Functor.OplaxMonoidal.δ G A M ≫ (x ⊗ₘ G.map y))
    (h₂ : adj.unit.app A ≫ L.map x ≫ e = z) :
    g₁ ≫ g₂ ≫ (z ⊗ₘ y) =
      adj.unit.app V ≫ L.map φ₁ ≫ L.map φ₂ ≫ inv (pf T M') ≫ (e ▷ M') := by
  rw [← L.map_comp_assoc, h₁, ← Category.assoc g₁ g₂]
  have hu := adj.unit.naturality (g₁ ≫ g₂)
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [L.map_comp, L.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hu,
    ← reassoc_of% (Adjunction.unit_whiskerRight_comp_projection G adj pf hcounit A M)]
  rw [MonoidalCategory.tensorHom_def x (G.map y), L.map_comp, Category.assoc,
    ← reassoc_of% (hnatl x M),
    ← reassoc_of% (hnatr T y), IsIso.hom_inv_id_assoc, MonoidalCategory.whisker_exchange,
    ← h₂, MonoidalCategory.tensorHom_def]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]

/-- The abstract form of the tensor part of the core identity. -/
lemma Functor.OplaxMonoidal.comp_δ_tensorHom_comp_braiding {𝒱 𝒲 𝒰 : Type*} [Category 𝒱]
    [Category 𝒲] [Category 𝒰] [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [MonoidalCategory 𝒰]
    [BraidedCategory 𝒱] [BraidedCategory 𝒲] [BraidedCategory 𝒰] (H : 𝒱 ⥤ 𝒲) (R : 𝒲 ⥤ 𝒰)
    (RH : 𝒱 ⥤ 𝒰) [H.OplaxMonoidal] [R.OplaxMonoidal] [RH.OplaxMonoidal]
    (hbraidH : ∀ A B : 𝒱, H.map (β_ A B).hom ≫ Functor.OplaxMonoidal.δ H B A =
      Functor.OplaxMonoidal.δ H A B ≫ (β_ (H.obj A) (H.obj B)).hom)
    (hbraidR : ∀ A B : 𝒲, R.map (β_ A B).hom ≫ Functor.OplaxMonoidal.δ R B A =
      Functor.OplaxMonoidal.δ R A B ≫ (β_ (R.obj A) (R.obj B)).hom)
    (u : ∀ X : 𝒱, R.obj (H.obj X) ⟶ RH.obj X)
    (hu : ∀ P Q : 𝒱, u (P ⊗ Q) ≫ Functor.OplaxMonoidal.δ RH P Q =
      R.map (Functor.OplaxMonoidal.δ H P Q) ≫ Functor.OplaxMonoidal.δ R _ _ ≫ (u P ⊗ₘ u Q))
    {P Q : 𝒱} {A₁ B₁ : 𝒰} {C : 𝒲} (a : RH.obj P ⟶ A₁) (b : RH.obj Q ⟶ B₁)
    (c : A₁ ⟶ R.obj C) (y : H.obj P ⟶ C) (hc : u P ≫ a ≫ c = R.map y) :
    (u (P ⊗ Q) ≫ Functor.OplaxMonoidal.δ RH P Q ≫ (a ⊗ₘ b)) ≫ ((β_ A₁ B₁).hom ≫ (B₁ ◁ c)) =
      R.map (H.map (β_ P Q).hom ≫ Functor.OplaxMonoidal.δ H Q P) ≫
        Functor.OplaxMonoidal.δ R _ _ ≫ ((u Q ≫ b) ⊗ₘ R.map y) := by
  rw [hbraidH, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (hbraidR _ _), reassoc_of% hu, ← hc]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [BraidedCategory.braiding_naturality_assoc]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc, MonoidalCategory.whiskerLeft_comp]

/-- The abstract form of the tail of the core identity: the projection morphism of a composite
`r ≫ z` and the compact-support base change of a vertically pasted rectangle. -/
lemma map_comp_inv_projection_comp_eq_of_comp {𝒰 𝒲 𝒳 : Type*} [Category 𝒰] [Category 𝒲]
    [Category 𝒳] [MonoidalCategory 𝒰] [MonoidalCategory 𝒲] [MonoidalCategory 𝒳]
    {Lr : 𝒰 ⥤ 𝒲} {Lz : 𝒲 ⥤ 𝒳} {Lrz : 𝒰 ⥤ 𝒳} (c : Lrz ≅ Lr ⋙ Lz) {Gr : 𝒲 ⥤ 𝒰} {Gz : 𝒳 ⥤ 𝒲}
    {Grz : 𝒳 ⥤ 𝒰} (uc : Grz ≅ Gz ⋙ Gr)
    (pfr : ∀ (T : 𝒰) (M : 𝒲), Lr.obj T ⊗ M ⟶ Lr.obj (T ⊗ Gr.obj M))
    (pfz : ∀ (T : 𝒲) (M : 𝒳), Lz.obj T ⊗ M ⟶ Lz.obj (T ⊗ Gz.obj M))
    (pfrz : ∀ (T : 𝒰) (M : 𝒳), Lrz.obj T ⊗ M ⟶ Lrz.obj (T ⊗ Grz.obj M))
    [∀ T M, IsIso (pfr T M)] [∀ T M, IsIso (pfz T M)] [∀ T M, IsIso (pfrz T M)]
    (hcomp : ∀ T M, pfrz T M ≫ Lrz.map (T ◁ uc.hom.app M) =
      (c.hom.app T ▷ M) ≫ pfz (Lr.obj T) M ≫ Lz.map (pfr T (Gz.obj M)) ≫
        c.inv.app (T ⊗ Gr.obj (Gz.obj M)))
    (hnatz : ∀ {T T' : 𝒲} (t : T ⟶ T') (M : 𝒳),
      Lz.map t ▷ M ≫ pfz T' M = pfz T M ≫ Lz.map (t ▷ Gz.obj M))
    {V₀ V₁ : 𝒲} {E₀ T : 𝒰} {K D₁ D₂ D₃ Z₀ : 𝒳} {B : 𝒲} (ψ₁ : V₀ ⟶ V₁) (ψ : V₁ ⟶ Lr.obj E₀)
    (bE : E₀ ⟶ T ⊗ Grz.obj K) (exB : Lr.obj T ⟶ B) (exZ₁ : Lz.obj B ⟶ D₁) (exZ₂ : D₁ ⟶ D₂)
    (e₃ : D₂ ⟶ D₃) (e₂₃ : D₁ ⟶ D₃) (exX : Lrz.obj T ⟶ D₂) (rest : D₃ ⊗ K ⟶ Z₀)
    (h₂₃ : e₂₃ = exZ₂ ≫ e₃) (hX : exX = c.hom.app T ≫ Lz.map exB ≫ exZ₁ ≫ exZ₂) :
    Lz.map (ψ₁ ≫ ψ ≫ Lr.map (bE ≫ (T ◁ uc.hom.app K)) ≫ inv (pfr T (Gz.obj K)) ≫
        (exB ▷ Gz.obj K)) ≫ inv (pfz B K) ≫ (exZ₁ ▷ K) ≫ (e₂₃ ▷ K) ≫ rest =
      Lz.map (ψ₁ ≫ ψ) ≫ c.inv.app E₀ ≫ Lrz.map bE ≫ inv (pfrz T K) ≫ (exX ▷ K) ≫ (e₃ ▷ K) ≫
        rest := by
  have hinv : inv (pfrz T K) = Lrz.map (T ◁ uc.hom.app K) ≫ c.hom.app _ ≫
      Lz.map (inv (pfr T (Gz.obj K))) ≫ inv (pfz (Lr.obj T) K) ≫ (c.inv.app T ▷ K) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [reassoc_of% (hcomp T K)]
    simp [← MonoidalCategory.comp_whiskerRight]
  have hn : inv (pfz (Lr.obj T) K) ≫ (Lz.map exB ▷ K) =
      Lz.map (exB ▷ Gz.obj K) ≫ inv (pfz B K) := by
    rw [IsIso.inv_comp_eq, ← reassoc_of% (hnatz exB K), IsIso.hom_inv_id, Category.comp_id]
  have hc := c.inv.naturality bE
  have hc' := c.inv.naturality (T ◁ uc.hom.app K)
  simp only [Functor.comp_map] at hc hc'
  rw [hinv, hX, h₂₃]
  simp only [Functor.map_comp, Category.assoc, MonoidalCategory.comp_whiskerRight]
  rw [← reassoc_of% hc, ← reassoc_of% hc']
  erw [Iso.inv_hom_id_app_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc (c.inv.app T) (c.hom.app T), Iso.inv_hom_id_app,
    MonoidalCategory.id_whiskerRight, Category.id_comp, reassoc_of% hn]

end CoreAbstract

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Core

variable {P X Y W U V : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  (aY : Y ⟶ P) (f : X ⟶ Y) [IsProper f.left] (p₂ : U ⟶ X) (π₁ π₂ : V ⟶ Y)
  (zX : W ⟶ X) (h : W ⟶ V) (r : U ⟶ W) [IsProper r.left]
  (hA : IsPullback h zX π₁ f) (hB : IsPullback p₂ r f (h ≫ π₂))
  (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

omit [IsProper f.left] [IsProper r.left] in
/-- The tensor part of the core identity: `Π_f` transposed along `h` and `r`. -/
lemma sourceExchange_T1 [IsProper (r ≫ h).left] (wq₁ : (r ≫ h) ≫ π₁ = (r ≫ zX) ≫ f)
    (wq₂ : (r ≫ h) ≫ π₂ = p₂ ≫ f) :
    ((boundedConstructibleUpperStarComp _ ℓ r h).inv.app
        ((boundedConstructibleUpperStar _ ℓ π₁).obj ((boundedConstructibleLowerStar ℓ f).obj K) ⊗
          (boundedConstructibleUpperStar _ ℓ π₂).obj ((boundedConstructibleLowerStar ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ≫
      (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (r ≫ h)) _ _).inv ≫
      (prodUpperStarCounit ℓ wq₁ K ⊗ₘ prodUpperStarCounit ℓ wq₂
        ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ≫
      ((β_ _ _).hom ≫ (_ ◁ (boundedConstructibleUpperStarComp _ ℓ r zX).hom.app K)) =
    (boundedConstructibleUpperStar _ ℓ r).map
        ((boundedConstructibleUpperStar _ ℓ h).map (β_ _ _).hom ≫
          Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ h) _ _) ≫
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ r) _ _ ≫
      (((boundedConstructibleUpperStarComp _ ℓ r h).inv.app
          ((boundedConstructibleUpperStar _ ℓ π₂).obj ((boundedConstructibleLowerStar ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ≫
        prodUpperStarCounit ℓ wq₂ ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ⊗ₘ
        (boundedConstructibleUpperStar _ ℓ r).map (prodUpperStarCounit ℓ hA.w K)) :=
  by
  have hc : (boundedConstructibleUpperStarComp _ ℓ r h).inv.app _ ≫ prodUpperStarCounit ℓ wq₁ K ≫
      (boundedConstructibleUpperStarComp _ ℓ r zX).hom.app K =
      (boundedConstructibleUpperStar _ ℓ r).map (prodUpperStarCounit ℓ hA.w K) := by
    rw [← Category.assoc, upperStarComp_inv_app_comp_prodUpperStarCounit_left ℓ wq₁ hA.w,
      Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  simp only [Functor.Monoidal.μIso_inv]
  exact Functor.OplaxMonoidal.comp_δ_tensorHom_comp_braiding _ _ _
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ ℓ h A B)
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ ℓ r A B) _
    (fun P Q ↦ boundedConstructibleUpperStarComp_inv_app_tensor_δ ℓ r h P Q) _ _ _ _ hc

/-- The unit part of the core identity: the compact-support base change of the square
`r ≫ (h ≫ π₂) = p₂ ≫ f` read through the transported counit. -/
lemma sourceExchange_T2 [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB)]
    [IsProper (r ≫ h).left] (wq₂ : (r ≫ h) ≫ π₂ = p₂ ≫ f) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app
        ((boundedConstructibleUpperStar _ ℓ h).obj ((boundedConstructibleUpperStar _ ℓ π₂).obj
          ((boundedConstructibleLowerStar ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))) ≫
      (boundedConstructibleLowerShriek ℓ r).map
        ((boundedConstructibleUpperStarComp _ ℓ r h).inv.app
          ((boundedConstructibleUpperStar _ ℓ π₂).obj ((boundedConstructibleLowerStar ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ≫
        prodUpperStarCounit ℓ wq₂ ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ≫
      (inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB)).app
        ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)) =
    (boundedConstructibleUpperStarComp _ ℓ h π₂).inv.app
        ((boundedConstructibleLowerStar ℓ f).obj
          ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ≫
      (boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
          ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) :=
  by
  have hu := (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.naturality
    ((boundedConstructibleUpperStarComp _ ℓ h π₂).inv.app ((boundedConstructibleLowerStar ℓ f).obj
      ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))
  simp only [Functor.id_map, Functor.comp_map] at hu
  have hE := homEquiv_prodUpperStarCounit ℓ hB.w.symm
    ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))
  have hP := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper ℓ hB
    ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))
  rw [upperStarComp_inv_app_comp_prodUpperStarCounit_right ℓ wq₂ hB.w.symm, Functor.map_comp,
    Category.assoc, ← reassoc_of% hu]
  refine whisker_eq _ ?_
  rw [Adjunction.homEquiv_unit] at hE
  have hP' : (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB).app
      ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)) =
      (boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app _) ≫
      (boundedConstructibleBaseChange ℓ hB.toCommSq).app _ ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app _ := by
    rw [← reassoc_of% hP, Iso.hom_inv_id_app, Category.comp_id]
  have hσ := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.naturality
    (prodUpperStarCounit ℓ hB.w.symm ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))
  rw [NatIso.isIso_inv_app, ← Category.assoc, IsIso.comp_inv_eq, hP',
    ← (boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).map_comp_assoc, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  exact (congrArg (_ ≫ ·) hσ.symm).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) hE))

/-- The core identity on `X × Y` of the base-change part of the source exchange. -/
theorem sourceExchange_coreZ [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB)]
    [IsProper (r ≫ h).left] (wq₁ : (r ≫ h) ≫ π₁ = (r ≫ zX) ≫ f)
    (wq₂ : (r ≫ h) ≫ π₂ = p₂ ≫ f) :
    (boundedConstructibleUpperStar _ ℓ h).map
        (β_ ((boundedConstructibleUpperStar _ ℓ π₁).obj
            ((boundedConstructibleLowerStar ℓ f).obj K))
          ((boundedConstructibleUpperStar _ ℓ π₂).obj ((boundedConstructibleLowerStar ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))).hom ≫
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ h) _ _ ≫
      (((boundedConstructibleUpperStarComp _ ℓ h π₂).inv.app
          ((boundedConstructibleLowerStar ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ≫
        (boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ⊗ₘ
        prodUpperStarCounit ℓ hA.w K) =
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app _ ≫
      (boundedConstructibleLowerShriek ℓ r).map
        ((boundedConstructibleUpperStarComp _ ℓ r h).inv.app _ ≫
          (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (r ≫ h)) _ _).inv ≫
          (prodUpperStarCounit ℓ wq₁ K ⊗ₘ prodUpperStarCounit ℓ wq₂
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ≫
      (boundedConstructibleLowerShriek ℓ r).map
        ((β_ _ _).hom ≫ (_ ◁ (boundedConstructibleUpperStarComp _ ℓ r zX).hom.app K)) ≫
      inv (((boundedConstructibleExceptionalProjection ℓ r).app
        ((boundedConstructibleUpperStar _ ℓ p₂).obj
          ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))).app
        ((boundedConstructibleUpperStar _ ℓ zX).obj K)) ≫
      ((inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB)).app
        ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)) ▷
        (boundedConstructibleUpperStar _ ℓ zX).obj K) :=
  Adjunction.comp_tensorHom_eq_unit_comp_map_comp_inv_projection _
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r)
    (fun T M ↦ ((boundedConstructibleExceptionalProjection ℓ r).app T).app M)
    (fun T M ↦ upperStar_map_exceptionalProjection_comp_counit ℓ r T M)
    (fun x M ↦ boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ r x M)
    (fun T _ _ y ↦ boundedConstructibleExceptionalProjectionMorphism_natural_right ℓ r T y)
    _ _ _ _ _ _ _ _ (sourceExchange_T1 ℓ aY f p₂ π₁ π₂ zX h r hA K wq₁ wq₂)
    (sourceExchange_T2 ℓ aY f p₂ π₂ h r hB wq₂)

omit [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] [IsProper f.left]
  [IsProper r.left] in
/-- The compact-support base change of the vertically pasted rectangle `sqX`, inverted. -/
lemma sourceExchange_inv_baseChange_paste (sqY : IsPullback π₂ π₁ aY aY)
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB)]
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hA.paste_horiz sqY))]
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (hB.paste_vert (hA.paste_horiz sqY)))] (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (hB.paste_vert (hA.paste_horiz sqY)))).app M =
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r zX).hom.app
        ((boundedConstructibleUpperStar _ ℓ p₂).obj M) ≫
      (boundedConstructibleLowerShriek ℓ zX).map
        ((inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB)).app M) ≫
      (inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hA.paste_horiz sqY))).app
        ((boundedConstructibleLowerShriek ℓ f).obj M) ≫
      (boundedConstructibleUpperStar _ ℓ (f ≫ aY)).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).inv.app M) := by
  have hP := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert ℓ hB
    (hA.paste_horiz sqY) M
  simp only [NatIso.isIso_inv_app]
  apply IsIso.inv_eq_of_hom_inv_id
  rw [hP]
  simp [← Functor.map_comp]

-- the compactly supported direct images are unfolded in the defeq checks
/-- The tail of the core identity: the left side through `Rh_*`, `Rr_!` and the projection
formulas is the transported test map of the exceptional Künneth adjoint of `K`. -/
theorem sourceExchange_coreTail (sqY : IsPullback π₂ π₁ aY aY)
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB)]
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hA.paste_horiz sqY))]
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (hB.paste_vert (hA.paste_horiz sqY)))]
    [IsProper (r ≫ h).left] (wq₁ : (r ≫ h) ≫ π₁ = (r ≫ zX) ≫ f)
    (wq₂ : (r ≫ h) ≫ π₂ = p₂ ≫ f) :
    (boundedConstructibleLowerShriek ℓ zX).map
        ((boundedConstructibleUpperStar _ ℓ h).map
          (β_ ((boundedConstructibleUpperStar _ ℓ π₁).obj
              ((boundedConstructibleLowerStar ℓ f).obj K))
            ((boundedConstructibleUpperStar _ ℓ π₂).obj ((boundedConstructibleLowerStar ℓ f).obj
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))).hom ≫
        Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ h) _ _ ≫
        (((boundedConstructibleUpperStarComp _ ℓ h π₂).inv.app
            ((boundedConstructibleLowerStar ℓ f).obj
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ≫
          (boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ⊗ₘ
          prodUpperStarCounit ℓ hA.w K)) ≫
      inv (((boundedConstructibleExceptionalProjection ℓ zX).app
        ((boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).obj
          ((boundedConstructibleLowerShriek ℓ f).obj
          ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))).app K) ≫
      ((inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hA.paste_horiz sqY))).app
          ((boundedConstructibleLowerShriek ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ▷ K) ≫
      ((boundedConstructibleUpperStar _ ℓ (f ≫ aY)).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).inv.app
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)) ≫
            (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ aY)).counit.app (𝟙_ _)) ▷ K) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (f ≫ aY))).inv ▷ K) ≫
      (λ_ K).hom =
    (boundedConstructibleLowerShriek ℓ zX).map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app _ ≫
          (boundedConstructibleLowerShriek ℓ r).map
            ((boundedConstructibleUpperStarComp _ ℓ r h).inv.app _ ≫
              (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (r ≫ h)) _ _).inv ≫
              (prodUpperStarCounit ℓ wq₁ K ⊗ₘ prodUpperStarCounit ℓ wq₂
                ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r zX).inv.app _ ≫
      (boundedConstructibleLowerShriek ℓ (r ≫ zX)).map (β_ _ _).hom ≫
      inv (((boundedConstructibleExceptionalProjection ℓ (r ≫ zX)).app
        ((boundedConstructibleUpperStar _ ℓ p₂).obj
          ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))).app K) ≫
      ((inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
          (hB.paste_vert (hA.paste_horiz sqY)))).app
        ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)) ▷ K) ≫
      ((boundedConstructibleUpperStar _ ℓ (f ≫ aY)).map
        ((boundedConstructibleUpperShriekAdjunction ℓ (f ≫ aY)).counit.app (𝟙_ _)) ▷ K) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (f ≫ aY))).inv ▷ K) ≫
      (λ_ K).hom := by
  have hz := sourceExchange_coreZ ℓ aY f p₂ π₁ π₂ zX h r hA hB K wq₁ wq₂
  have hz' : (boundedConstructibleLowerShriek ℓ zX).map
        ((boundedConstructibleUpperStar _ ℓ h).map
          (β_ ((boundedConstructibleUpperStar _ ℓ π₁).obj
              ((boundedConstructibleLowerStar ℓ f).obj K))
            ((boundedConstructibleUpperStar _ ℓ π₂).obj ((boundedConstructibleLowerStar ℓ f).obj
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))).hom ≫
        Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ h) _ _ ≫
        (((boundedConstructibleUpperStarComp _ ℓ h π₂).inv.app
            ((boundedConstructibleLowerStar ℓ f).obj
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ≫
          (boundedConstructibleUpperStar _ ℓ (h ≫ π₂)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
              ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) ⊗ₘ
          prodUpperStarCounit ℓ hA.w K)) = _ := congrArg _ hz
  simp only [hz']
  exact map_comp_inv_projection_comp_eq_of_comp
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r zX)
    (boundedConstructibleUpperStarComp _ ℓ r zX)
    (fun T M ↦ ((boundedConstructibleExceptionalProjection ℓ r).app T).app M)
    (fun T M ↦ ((boundedConstructibleExceptionalProjection ℓ zX).app T).app M)
    (fun T M ↦ ((boundedConstructibleExceptionalProjection ℓ (r ≫ zX)).app T).app M)
    (fun T M ↦ exceptionalProjection_comp ℓ r zX T M)
    (fun t M ↦ boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ zX t M)
    _ _ _ _ _ _ _ _ _ _ (Functor.map_comp _ _ _)
    (sourceExchange_inv_baseChange_paste ℓ aY f p₂ π₁ π₂ zX h r hA hB sqY _)

end Core

section Generic

variable {P X Y W U V : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

-- the compactly supported direct images are unfolded in the defeq checks
/-- The generic form of `lowerShriek_exceptionalKunneth_baseChange`. -/
theorem lowerShriek_exceptionalKunneth_baseChange_generic
    (aX : X ⟶ P) (aY : Y ⟶ P) (f : X ⟶ Y) [IsProper f.left] (p₁ p₂ : U ⟶ X) (π₁ π₂ : V ⟶ Y)
    (zX : W ⟶ X) (zY : W ⟶ Y) (h : W ⟶ V) [IsProper h.left] (r : U ⟶ W) [IsProper r.left]
    (q : U ⟶ V) [IsProper q.left]
    (hA : IsPullback h zX π₁ f) (hB : IsPullback p₂ r f zY)
    (sqY : IsPullback π₂ π₁ aY aY) (sqX : IsPullback p₂ p₁ aX aX)
    (hzY : h ≫ π₂ = zY) (hp₁ : r ≫ zX = p₁) (hq : r ≫ h = q) (haX : f ≫ aY = aX)
    (wq₁ : q ≫ π₁ = p₁ ≫ f) (wq₂ : q ≫ π₂ = p₂ ≫ f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY)]
    [IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqX)] :
    (boundedConstructibleLowerShriek ℓ π₁).map (β_ _ _).hom ≫
      inv (((boundedConstructibleExceptionalProjection ℓ π₁).app
        ((boundedConstructibleUpperStar _ ℓ π₂).obj
          ((boundedConstructibleLowerStar ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))))).app
        ((boundedConstructibleLowerStar ℓ f).obj K)) ≫
      (((inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY)).app
          ((boundedConstructibleLowerStar ℓ f).obj
            ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))) ≫
        (boundedConstructibleUpperStar _ ℓ aY).map
          ((boundedConstructibleLowerShriek ℓ aY).map
              ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
                ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))) ≫
            (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).inv.app
              ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _)) ≫
            eqToHom (by rw [haX] : (boundedConstructibleLowerShriek ℓ (f ≫ aY)).obj
              ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _)) =
              (boundedConstructibleLowerShriek ℓ aX).obj
                ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))) ≫
            (boundedConstructibleUpperShriekAdjunction ℓ aX).counit.app (𝟙_ _))) ▷
        (boundedConstructibleLowerStar ℓ f).obj K) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ aY)).inv ▷ _) ≫
      (λ_ _).hom =
    (boundedConstructibleLowerShriek ℓ π₁).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).homEquiv _ _
          ((Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ q) _ _).inv ≫
            (prodUpperStarCounit ℓ wq₁ K ⊗ₘ prodUpperStarCounit ℓ wq₂
              ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))))) ≫
      (boundedConstructibleLowerShriek ℓ π₁).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ q).inv.app _) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wq₁).hom.app _ ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriek ℓ p₁).map (β_ _ _).hom ≫
          inv (((boundedConstructibleExceptionalProjection ℓ p₁).app
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _)))).app K) ≫
          ((inv (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqX)).app
            ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _)) ▷ K) ≫
          ((boundedConstructibleUpperStar _ ℓ aX).map
            ((boundedConstructibleUpperShriekAdjunction ℓ aX).counit.app (𝟙_ _)) ▷ K) ≫
          ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ aX)).inv ▷ K) ≫
          (λ_ K).hom) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K :=
  by
  subst hzY hp₁ hq haX
  have : IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB) :=
    isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hB
  have : IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hA.paste_horiz sqY)) :=
    isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ _
  have : IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (hB.paste_vert (hA.paste_horiz sqY))) :=
    isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ _
  simp only [eqToHom_refl, Category.id_comp]
  apply ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  simp only [sourceExchange_leftTranspose ℓ aY f π₁ π₂ zX h hA K sqY,
    sourceExchange_rightTranspose ℓ aY f p₂ π₁ π₂ zX h r hA K wq₁ wq₂]
  exact congrArg (_ ≫ ·) (sourceExchange_coreTail ℓ aY f p₂ π₁ π₂ zX h r hA hB K sqY wq₁ wq₂)

end Generic

end AlgebraicGeometry.ProEtale.CondensedRing
