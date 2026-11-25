/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeRestrictionTensorEvaluation

/-! # Pointwise evaluation compatibility of native open tensor models

Source: Stacks 0GL1, 07A4; support-open-tensor steps 5--6.
(blueprint: lem-coef-native-open-tensor-gamma-evaluation-component).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

private theorem exactFactorsh_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have h₁ : (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso D).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  have h₃ : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  simp only [h₁, h₂, h₃]
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id,
    F.mapDerivedCategory.map_id, Category.id_comp]

private theorem exactAdjunction_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory = a.mapExactDerivedCategory := by
  let b := a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    R.rightDerivedFunctorIsoMapDerivedCategory
  have hb (X : HomotopyCategory C (.up ℤ)) :
      b.unit.app (DerivedCategory.Qh.obj X) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
        R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app X) := by
    have h₁ := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
        R.rightDerivedFunctorUnit X
    have h₃ := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((L.mapHomotopyCategory (.up ℤ)).obj X)
    have h₄ := R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
      (L.mapDerivedCategoryFactorsh.hom.app X)
    dsimp at h₁ h₃ h₄
    simp only [b, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc]
    rw [← reassoc_of% h₄]
    erw [reassoc_of% h₁]
    rw [reassoc_of% h₃, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have ha (K : CochainComplex C ℤ) :
      a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
    unfold Adjunction.mapExactDerivedCategory
    rw [Adjunction.localization_unit_app]
    simp only [Iso.symm_hom, CatCommSq.iso, Category.assoc]
    rw [← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K))).mp
  have h := hb ((HomotopyCategory.quotient _ _).obj K)
  erw [exactFactorsh_hom L K,
    exactFactorsh_hom R ((L.mapHomologicalComplex (.up ℤ)).obj K),
    Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  exact h.trans (ha K).symm

private theorem unit_square_of_inverse
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) (ρ : P ⋙ T ≅ R ⋙ F) (M : A)
    (h : R.map (a.unit.app M) ≫ χ.app (P.obj M) =
      b.unit.app (R.obj M) ≫ G.map (ρ.inv.app M)) :
    R.map (a.unit.app M) ≫ χ.app (P.obj M) ≫ G.map (ρ.hom.app M) =
      b.unit.app (R.obj M) := by
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id_app]
  erw [G.map_id, Category.comp_id]

private theorem counit_square_of_inverse
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) (ρ : P ⋙ T ≅ R ⋙ F) (H : B)
    (h : F.map (χ.app H) ≫ b.counit.app (T.obj H) =
      ρ.inv.app (Q.obj H) ≫ T.map (a.counit.app H)) :
    ρ.hom.app (Q.obj H) ≫ F.map (χ.app H) ≫ b.counit.app (T.obj H) =
      T.map (a.counit.app H) := by
  rw [h, Iso.hom_inv_id_app_assoc]

private theorem projection_inverse_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (μA : TA ⋙ R ⟶ R.prod R ⋙ TC) (μB : TB ⋙ T ⟶ T.prod T ⋙ TD)
    (χ : Q ⋙ R ⟶ T ⋙ G) (ρ : P ⋙ T ⟶ R ⋙ F)
    (θ : TB ⋙ Q ≅ Q.prod Q ⋙ TA) (ψ : TD ⋙ G ≅ G.prod G ⋙ TC)
    (hu : ∀ M, R.map (a.unit.app M) ≫ χ.app (P.obj M) ≫
      G.map (ρ.app M) = b.unit.app (R.obj M))
    (hc : ∀ H, ρ.app (Q.obj H) ≫ F.map (χ.app H) ≫
      b.counit.app (T.obj H) = T.map (a.counit.app H))
    (ht : ∀ H N, R.map (θ.hom.app (H, N)) ≫ μA.app (Q.obj H, Q.obj N) ≫
        TC.map (Prod.mkHom (χ.app H) (χ.app N)) =
      χ.app (TB.obj (H, N)) ≫ G.map (μB.app (H, N)) ≫
        ψ.hom.app (T.obj H, T.obj N))
    (M : A) (N : B)
    (γ : P.obj (TA.obj (M, Q.obj N)) ⟶ TB.obj (P.obj M, N))
    (δ : F.obj (TC.obj (R.obj M, G.obj (T.obj N))) ⟶ TD.obj (F.obj (R.obj M), T.obj N))
    (hγ : a.homEquiv _ _ γ =
      TA.map (Prod.mkHom (a.unit.app M) (𝟙 _)) ≫ θ.inv.app (P.obj M, N))
    (hδ : b.homEquiv _ _ δ =
      TC.map (Prod.mkHom (b.unit.app (R.obj M)) (𝟙 _)) ≫
        ψ.inv.app (F.obj (R.obj M), T.obj N)) :
    ρ.app (TA.obj (M, Q.obj N)) ≫
        F.map (μA.app (M, Q.obj N) ≫ TC.map (Prod.mkHom (𝟙 _) (χ.app N))) ≫ δ =
      T.map γ ≫ μB.app (P.obj M, N) ≫ TD.map (Prod.mkHom (ρ.app M) (𝟙 _)) := by
  let H := TB.obj (P.obj M, N)
  let q := μB.app (P.obj M, N) ≫ TD.map (Prod.mkHom (ρ.app M) (𝟙 _))
  let τ := TA.map (Prod.mkHom (a.unit.app M) (𝟙 (Q.obj N))) ≫
    θ.inv.app (P.obj M, N)
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at *
  have hi : μA.app (Q.obj (P.obj M), Q.obj N) ≫
        TC.map (Prod.mkHom (χ.app (P.obj M)) (χ.app N)) ≫
        ψ.inv.app (T.obj (P.obj M), T.obj N) =
      R.map (θ.inv.app (P.obj M, N)) ≫ χ.app H ≫ G.map (μB.app (P.obj M, N)) := by
    apply (cancel_epi (R.map (θ.hom.app (P.obj M, N)))).1
    simp only [← R.map_comp_assoc, Iso.hom_inv_id_app, R.map_id, Category.id_comp]
    rw [reassoc_of% ht]
    simp only [Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hn := ψ.inv.naturality (Prod.mkHom (ρ.app M) (𝟙 (T.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [G.map_id] at hn
  have hμ := μA.naturality (Prod.mkHom (a.unit.app M) (𝟙 (Q.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hμ
  simp only [R.map_id] at hμ
  have htau : (μA.app (M, Q.obj N) ≫ TC.map (Prod.mkHom (𝟙 _) (χ.app N))) ≫
        b.homEquiv _ _ δ = R.map τ ≫ χ.app H ≫ G.map q := by
    erw [hδ, ← hu M]
    simp only [Category.assoc, ← TC.map_comp_assoc, prod_comp,
      Category.id_comp]
    erw [Category.comp_id]
    rw [show Prod.mkHom (R.map (a.unit.app M) ≫ χ.app (P.obj M) ≫
        G.map (ρ.app M)) (χ.app N) =
      Prod.mkHom (R.map (a.unit.app M)) (𝟙 (R.obj (Q.obj N))) ≫
        Prod.mkHom (χ.app (P.obj M)) (χ.app N) ≫
          Prod.mkHom (G.map (ρ.app M)) (𝟙 (G.obj (T.obj N))) by
      ext <;> simp]
    erw [TC.map_comp, TC.map_comp, ← Category.assoc, ← Category.assoc, ← hμ]
    simp only [Category.assoc]
    erw [hn, reassoc_of% hi]
    simp only [τ, q, R.map_comp, G.map_comp, Category.assoc]
  have hγ' : γ = P.map τ ≫ a.counit.app H := by
    have hγ0 : a.homEquiv _ _ γ = τ := hγ
    rw [← hγ0]
    exact ((a.homEquiv _ _).symm_apply_apply γ).symm
  have hδ' : δ = F.map (b.homEquiv _ _ δ) ≫ b.counit.app _ :=
    ((b.homEquiv _ _).symm_apply_apply δ).symm
  erw [hδ', ← F.map_comp_assoc, htau]
  simp only [F.map_comp, Category.assoc]
  erw [← Category.assoc, ← ρ.naturality τ]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  erw [b.counit.naturality q]
  dsimp only [Functor.comp_map, Functor.id_map]
  erw [reassoc_of% hc H, ← T.map_comp_assoc, ← hγ']

private theorem forward_of_inverse
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {X Y : A} {M N : B} (f : X ≅ Y) (g : M ≅ N)
    (q : R.obj X ⟶ M) (r : R.obj Y ⟶ N)
    (h : r ≫ g.inv = R.map f.inv ≫ q) :
    q ≫ g.hom = R.map f.hom ≫ r := by
  apply (cancel_mono g.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]

section ModelSquare
attribute [local instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

private theorem model_gamma_square
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (R₀ : Sheaf J CommRingCat.{max c v r})
    (A : SemilinearSections.Closed.{c, v, r} J R₀)
    (TA : SemilinearSections.Models.{c, v, r} J R₀ A)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C') (R₁ : Sheaf J' CommRingCat.{max c v r})
    (A' : SemilinearSections.Closed.{c, v, r} J' R₁)
    (TA' : SemilinearSections.Models.{c, v, r} J' R₁ A')
    (P : SemilinearSections.Mod.{c, v, max c v r} J' R₁ ⥤
      SemilinearSections.Mod.{c, v, max c v r} J R₀)
    (Q : SemilinearSections.Mod.{c, v, max c v r} J R₀ ⥤
      SemilinearSections.Mod.{c, v, max c v r} J' R₁)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (a : P ⊣ Q) (H : C ⥤ C')
    (sectionPull : ∀ (N : SemilinearSections.Mod.{c, v, max c v r} J R₀) (V : Cᵒᵖ),
      N.val.obj V → (Q.obj N).val.obj (H.op.obj V))
    (O : OpenTensorModel J R₀ A TA J' R₁ A' TA' P Q a H sectionPull)
    {D : Type c} [Category.{v} D] [EssentiallySmall.{max c v r} D]
    (K : GrothendieckTopology D) (S₀ : Sheaf K CommRingCat.{max c v r})
    (B : SemilinearSections.Closed.{c, v, r} K S₀)
    (TB : SemilinearSections.Models.{c, v, r} K S₀ B)
    {D' : Type c} [Category.{v} D'] [EssentiallySmall.{max c v r} D']
    (K' : GrothendieckTopology D') (S₁ : Sheaf K' CommRingCat.{max c v r})
    (B' : SemilinearSections.Closed.{c, v, r} K' S₁)
    (TB' : SemilinearSections.Models.{c, v, r} K' S₁ B')
    (F : SemilinearSections.Mod.{c, v, max c v r} K' S₁ ⥤
      SemilinearSections.Mod.{c, v, max c v r} K S₀)
    (G : SemilinearSections.Mod.{c, v, max c v r} K S₀ ⥤
      SemilinearSections.Mod.{c, v, max c v r} K' S₁)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (b : F ⊣ G) (I : D ⥤ D')
    (sectionPull' : ∀ (N : SemilinearSections.Mod.{c, v, max c v r} K S₀) (V : Dᵒᵖ),
      N.val.obj V → (G.obj N).val.obj (I.op.obj V))
    (On : OpenTensorModel K S₀ B TB K' S₁ B' TB' F G b I sectionPull')
    (R : DerivedCategory (SemilinearSections.Mod.{c, v, max c v r} J' R₁) ⥤
      DerivedCategory (SemilinearSections.Mod.{c, v, max c v r} K' S₁))
    (T : DerivedCategory (SemilinearSections.Mod.{c, v, max c v r} J R₀) ⥤
      DerivedCategory (SemilinearSections.Mod.{c, v, max c v r} K S₀))
    (α : P.mapDerivedCategory ⋙ T ≅ R ⋙ F.mapDerivedCategory)
    (χ : Q.mapDerivedCategory ⋙ R ≅ T ⋙ G.mapDerivedCategory)
    (μ : A'.tensor ⋙ R ≅ R.prod R ⋙ B'.tensor)
    (ν : A.tensor ⋙ T ≅ T.prod T ⋙ B.tensor)
    (hu : ∀ M, R.map (a.mapExactDerivedCategory.unit.app M) ≫
      χ.hom.app (P.mapDerivedCategory.obj M) ≫ G.mapDerivedCategory.map (α.hom.app M) =
        b.mapExactDerivedCategory.unit.app (R.obj M))
    (hc : ∀ N, α.hom.app (Q.mapDerivedCategory.obj N) ≫
      F.mapDerivedCategory.map (χ.hom.app N) ≫
        b.mapExactDerivedCategory.counit.app (T.obj N) =
          T.map (a.mapExactDerivedCategory.counit.app N))
    (ht : ∀ M N, R.map (O.restriction.hom.app (M, N)) ≫
      μ.hom.app (Q.mapDerivedCategory.obj M, Q.mapDerivedCategory.obj N) ≫
        B'.tensor.map (Prod.mkHom (χ.hom.app M) (χ.hom.app N)) =
      χ.hom.app (A.tensor.obj (M, N)) ≫ G.mapDerivedCategory.map (ν.hom.app (M, N)) ≫
        On.restriction.hom.app (T.obj M, T.obj N))
    (M : DerivedCategory (SemilinearSections.Mod.{c, v, max c v r} J' R₁))
    (N : DerivedCategory (SemilinearSections.Mod.{c, v, max c v r} J R₀)) :
    T.map (O.gamma.hom.app (M, N)) ≫
        α.hom.app (A'.tensor.obj (M, Q.mapDerivedCategory.obj N)) ≫
        F.mapDerivedCategory.map (μ.hom.app (M, Q.mapDerivedCategory.obj N)) ≫
        F.mapDerivedCategory.map (B'.tensor.map (Prod.mkHom (𝟙 _) (χ.hom.app N))) =
      ν.hom.app (P.mapDerivedCategory.obj M, N) ≫
        B.tensor.map (Prod.mkHom (α.hom.app M) (𝟙 _)) ≫
        On.gamma.hom.app (R.obj M, T.obj N) := by
  have he := projection_inverse_square a.mapExactDerivedCategory b.mapExactDerivedCategory
    A'.tensor A.tensor B'.tensor B.tensor μ.hom ν.hom χ.hom α.hom
    O.restriction On.restriction hu hc ht M N
    (O.gamma.inv.app (M, N)) (On.gamma.inv.app (R.obj M, T.obj N))
    (O.gamma_inverse M N) (On.gamma_inverse (R.obj M) (T.obj N))
  let qL := ν.hom.app (P.mapDerivedCategory.obj M, N) ≫
    B.tensor.map (Prod.mkHom (α.hom.app M) (𝟙 (T.obj N)))
  let qR := α.hom.app (A'.tensor.obj (M, Q.mapDerivedCategory.obj N)) ≫
    F.mapDerivedCategory.map (μ.hom.app (M, Q.mapDerivedCategory.obj N) ≫
      B'.tensor.map (Prod.mkHom (𝟙 (R.obj M)) (χ.hom.app N)))
  have he' : qR ≫ On.gamma.inv.app (R.obj M, T.obj N) =
      T.map (O.gamma.inv.app (M, N)) ≫ qL := by
    simpa only [qL, qR, Category.assoc] using he
  have hf := forward_of_inverse T (O.gamma.app (M, N))
    (On.gamma.app (R.obj M, T.obj N)) qL qR he'
  simpa only [qL, qR, F.mapDerivedCategory.map_comp, Category.assoc, Iso.app_hom,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj] using hf.symm

end ModelSquare

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite evaluation equation for one fixed degree and one fixed pair of derived
objects. It is the pointwise generator-and-descent calculation used to assemble
`GammaEvaluation`; exact evaluation preserves the open unit, restriction comparison,
total summands, and K-flat pullback, while bilinearity and tensor descent extend the
same equality from generators to the displayed derived pair.
Source: Stacks 0GL1 and 07A4, support-open-tensor steps 5--6.
(blueprint: lem-coef-native-open-tensor-gamma-evaluation-component).
-/
theorem nativeOpenTensorGammaEvaluation_component {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z)
    (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors)
    (On : ∀ n : ℕ, FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors n)
    (n : ℕ) (U : coefficientSequenceDerived.{u, u} l E X)
    (L : coefficientSequenceDerived.{u, u} l E Z) :
    (coefficientSequenceDerivedEvaluation.{u, u} l E Z n).map
        ((systemGamma l E j SX.toCoefficientDerivedSystemTensors
          SZ.toCoefficientDerivedSystemTensors O).hom.app (U, L)) ≫
      (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j n).hom.app
          (SX.systemClosed.tensor.obj (U,
            (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) j).obj L)) ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).mapDerivedCategory.map
        ((SX.evaluationTensor n).hom.app (U,
          (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j).obj L)) ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).mapDerivedCategory.map
        ((SX.finiteClosed n).tensor.map (Prod.mkHom (𝟙 _)
          ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j n).hom.app L))) =
    (SZ.evaluationTensor n).hom.app
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj U, L) ≫
      (SZ.finiteClosed n).tensor.map (Prod.mkHom
        ((ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app U) (𝟙 _)) ≫
      (finiteGamma l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors n (On n)).hom.app
          ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj U,
        (coefficientSequenceDerivedEvaluation.{u, u} l E Z n).obj L) := by
  let := ProEtale.VaryingRing.extensionAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  let := ProEtale.VaryingRing.extensionLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  let := ProEtale.VaryingRing.extensionColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  let := ProEtale.VaryingRing.pullAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  let := ProEtale.VaryingRing.pullLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  let := ProEtale.VaryingRing.pullColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  let := ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j
  let := ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j
  let := ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j
  let := proEtaleRingModulePullback_additive j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  let := proEtaleRingModulePullback_preservesFiniteLimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  let := proEtaleRingModulePullback_preservesFiniteColimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  let R₀ := compactSupportSystemLevel l E
  let q₀ := compactSupportSystemQuotient l E
  let P := ProEtale.VaryingRing.J R₀ q₀ j
  let Q := ProEtale.VaryingRing.G R₀ q₀ j
  let F := (ProEtale.StrictTower.moduleJ (R₀ n) j).mapDerivedCategory
  let G := (ProEtale.StrictTower.modulePullback (R₀ n) j).mapDerivedCategory
  let R := ProEtale.VaryingRing.ev R₀ q₀ X n
  let T := ProEtale.VaryingRing.ev R₀ q₀ Z n
  let a := SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (ProEtale.VaryingRing.moduleJAdj R₀ q₀ j)
  let b := SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (ProEtale.StrictTower.moduleJAdj (R₀ n) j)
  let α := ProEtale.VaryingRing.evalJ R₀ q₀ j n
  let χ := ProEtale.VaryingRing.evalG R₀ q₀ j n
  have ha : ProEtale.VaryingRing.jAdj R₀ q₀ j = a :=
    exactAdjunction_eq (ProEtale.VaryingRing.moduleJAdj R₀ q₀ j)
  have hb : ProEtale.VaryingRing.levelJAdj R₀ j n = b :=
    exactAdjunction_eq (ProEtale.StrictTower.moduleJAdj (R₀ n) j)
  have hu (M) : R.map (a.unit.app M) ≫ χ.hom.app (P.obj M) ≫
      G.map (α.hom.app M) = b.unit.app (R.obj M) := by
    have h := unit_mateEquiv_symm (ProEtale.VaryingRing.jAdj R₀ q₀ j)
      (ProEtale.VaryingRing.levelJAdj R₀ j n) χ.hom M
    change R.map ((ProEtale.VaryingRing.jAdj R₀ q₀ j).unit.app M) ≫
      χ.hom.app (P.obj M) =
      (ProEtale.VaryingRing.levelJAdj R₀ j n).unit.app (R.obj M) ≫
        G.map (α.inv.app M) at h
    rw [ha, hb] at h
    exact unit_square_of_inverse a b χ.hom α M h
  have hc (H) : α.hom.app (Q.obj H) ≫ F.map (χ.hom.app H) ≫
      b.counit.app (T.obj H) = T.map (a.counit.app H) := by
    have h := mateEquiv_counit_symm (ProEtale.VaryingRing.jAdj R₀ q₀ j)
      (ProEtale.VaryingRing.levelJAdj R₀ j n) χ.hom H
    change F.map (χ.hom.app H) ≫
      (ProEtale.VaryingRing.levelJAdj R₀ j n).counit.app (T.obj H) =
      α.inv.app (Q.obj H) ≫ T.map ((ProEtale.VaryingRing.jAdj R₀ q₀ j).counit.app H) at h
    rw [ha, hb] at h
    exact counit_square_of_inverse a b χ.hom α H h
  let μ := SX.evaluationTensor n
  let ν := SZ.evaluationTensor n
  let ht := nativeRestrictionTensorEvaluation l E j SX SZ O n (On n)
  -- Use the model parameters already elaborated in O and On. Re-elaborating the
  -- specialization expands the large coefficient-site instances repeatedly.
  -- This constructs an ordinary application, which the kernel checks in full.
  run_tac Lean.Elab.Tactic.withMainContext do
    let get (name : Lean.Name) : Lean.Elab.Tactic.TacticM Lean.Expr := do
      return (← Lean.Meta.getLocalDeclFromUserName name).toExpr
    let O ← get `O
    let On := Lean.mkApp (← get `On) (← get `n)
    let tO ← Lean.Meta.whnf (← Lean.Meta.inferType O)
    let tOn ← Lean.Meta.whnf (← Lean.Meta.inferType On)
    let .const _ levels := tO.getAppFn | Lean.throwError "open model expected"
    unless tO.isAppOf ``OpenTensorModel && tOn.isAppOf ``OpenTensorModel do
      Lean.throwError "open model parameters unavailable"
    let mut args := tO.getAppArgs.push O ++ tOn.getAppArgs.push On
    for name in #[`R, `T, `α, `χ, `μ, `ν, `hu, `hc, `ht, `U, `L] do
      args := args.push (← get name)
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst ``model_gamma_square levels) args)
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures.CoefSupportOpenTensor
