/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRepresentativeCurrying
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Naturality on K-flat ordinary tensor representatives

The normalization condition determines the representative comparison by its
tensor--Hom transpose when both representative inputs are K-flat.  This is the
K-flat part of the ordinary naturality argument.

Source: Stacks 06YU, 0FPT; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-data`.
(blueprint: lem-sf-native-weil-tensor-ringed-derived-square-ordinary-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The ordinary tensor-Hom adjunction, with its precomposition mate. -/
private noncomputable def tensor_model_adj
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (ordinaryTensorBifunctor l Y) ⊣₂ (ordinaryIhomBifunctor l Y) where
  adj P := Mod.ihomAdjunction P
  unit_whiskerRight_map {P P'} f := by
    apply NatTrans.ext
    funext Q
    exact (unit_conjugateEquiv (Mod.ihomAdjunction P') (Mod.ihomAdjunction P)
      (Mod.tensorLeftMap f) Q).symm

/-- Naturality of inverse transposition in both tensor inputs. -/
private theorem tensor_model_uncurry_naturality
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H)
    {K K' L L' W : D} (f : K' ⟶ K) (g : L' ⟶ L)
    (v : L ⟶ H.obj (op K, W)) :
    (S.transpose L' K' W).symm (g ≫ v ≫ H.map (Prod.mkHom f.op (𝟙 W))) =
      S.tensor.map (Prod.mkHom g f) ≫ (S.transpose L K W).symm v := by
  let := S.monoidal
  change (MonoidalCategory.tensorRight K').map
      (g ≫ v ≫ H.map (Prod.mkHom f.op (𝟙 W))) ≫ (S.adjunction K').counit.app W =
    S.tensor.map (Prod.mkHom g f) ≫
      (MonoidalCategory.tensorRight K).map v ≫ (S.adjunction K).counit.app W
  simp only [Functor.map_comp, Category.assoc]
  rw [S.evaluation_naturality K K' W f]
  change (MonoidalCategory.whiskerRight g K') ≫
      (MonoidalCategory.whiskerRight v K') ≫
      (MonoidalCategory.whiskerLeft (H.obj (op K, W)) f) ≫
      (S.adjunction K).counit.app W =
    (MonoidalCategory.tensorHom g f) ≫ (MonoidalCategory.whiskerRight v K) ≫
      (S.adjunction K).counit.app W
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]

/-- Normalization identifies the transpose of every actual map to a K-injective. -/
private theorem tensor_model_normalized_map
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (model : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (hn : NativeAdjunctionNormalization
      (ordinaryIhomBifunctor l Y) (ordinaryTensorBifunctor l Y)
      (fun P ↦ Mod.ihomAdjunction P) H R S (NativeOrdinaryKFlat l Y) model)
    (P Q I : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
    (hP : NativeOrdinaryKFlat l Y P) (hQ : NativeOrdinaryKFlat l Y Q)
    (hI : I.IsKInjective) (a : ordinaryTensorTotal l Y P Q ⟶ I) :
    (model P Q hP).hom ≫ DerivedCategory.Q.map a =
      (S.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj I)).symm
        (DerivedCategory.Q.map
          (NativeCurrying.internalHomEquiv (tensor_model_adj l Y) P I Q a) ≫
            (R.model P I hI).inv) := by
  let φ := NativeCurrying.internalHomEquiv (tensor_model_adj l Y) P I Q a
  obtain ⟨ψ, hψ, he⟩ := hn P Q I hP hQ hI φ
  have hψa : ψ = a := by
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    rw [hψ p q n hpq]
    have hu := NativeCurrying.uncurry_component (tensor_model_adj l Y) P Q I φ p q n hpq
    simpa only [φ, Equiv.symm_apply_apply, tensor_model_adj] using hu.symm
  simpa only [hψa] using he

-- Keep the supplied names of the quantified K-flat hypotheses, which occur only in the proof.
set_option linter.unusedVariables false in
/-- A normalized one-K-flat ordinary tensor model is natural on K-flat inputs.

The proof compares both sides after applying the specified product-total Hom
representatives.  The componentwise uncurrying equation in
`NativeAdjunctionNormalization` identifies their transposes, and the
tensor--Hom adjunction then cancels the common transpose.  Both Q and Q' are
assumed K-flat here; the extension to arbitrary second inputs is a separate
resolution argument. -/
theorem native_ordinary_tensor_model_naturality_kflat
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (model : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (_hnormalization : NativeAdjunctionNormalization
      (ordinaryIhomBifunctor l Y) (ordinaryTensorBifunctor l Y)
      (fun P ↦ Mod.ihomAdjunction P) H R S
      (NativeOrdinaryKFlat l Y) model) :
    ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P)
      (hP' : NativeOrdinaryKFlat l Y P')
      (hQ : NativeOrdinaryKFlat l Y Q)
      (hQ' : NativeOrdinaryKFlat l Y Q')
      (f : P ⟶ P') (g : Q ⟶ Q'),
      S.tensor.map
          (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
          (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
          (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g
            (ordinaryTensorBifunctor l Y) (.up ℤ)) := by
  classical
  intro P Q P' Q' hP hP' hQ hQ' f g
  let : Abelian.HasKInjectiveResolutions (ProEtale.AdicSheaf l Y) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  obtain ⟨I, hI, a, _, ha⟩ :=
    Abelian.HasKInjectiveResolutions.exists_isKInjective (ordinaryTensorTotal l Y P' Q')
  let := ha
  let t := HomologicalComplex.mapBifunctorMap f g (ordinaryTensorBifunctor l Y) (.up ℤ)
  let φ := NativeCurrying.internalHomEquiv (tensor_model_adj l Y) P' I Q' a
  have hc := NativeCurrying.internalHomEquiv_naturality (tensor_model_adj l Y)
    f g (𝟙 I) a
  simp only [Category.comp_id, CochainComplex.bifunctorHomMapRight_id] at hc
  change NativeCurrying.internalHomEquiv (tensor_model_adj l Y) P I Q (t ≫ a) =
    g ≫ φ ≫ CochainComplex.bifunctorHomMapLeft
      (H := ordinaryIhomBifunctor l Y) (Y := I) f at hc
  have hr := R.naturality P P' I I hI hI f (𝟙 I)
  rw [DerivedCategory.Q.map_id I] at hr
  simp only [CochainComplex.bifunctorHomMapRight_id, Category.comp_id] at hr
  have hr' : DerivedCategory.Q.map
      (CochainComplex.bifunctorHomMapLeft (H := ordinaryIhomBifunctor l Y) (Y := I) f) ≫
        (R.model P I hI).inv =
      (R.model P' I hI).inv ≫
        H.map (Prod.mkHom (DerivedCategory.Q.map f).op (𝟙 (DerivedCategory.Q.obj I))) := by
    apply (cancel_mono (R.model P I hI).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hr, Iso.inv_hom_id_assoc]
  have hc' : DerivedCategory.Q.map
      (NativeCurrying.internalHomEquiv (tensor_model_adj l Y) P I Q (t ≫ a)) ≫
        (R.model P I hI).inv =
      DerivedCategory.Q.map g ≫ (DerivedCategory.Q.map φ ≫ (R.model P' I hI).inv) ≫
        H.map (Prod.mkHom (DerivedCategory.Q.map f).op (𝟙 (DerivedCategory.Q.obj I))) := by
    rw [hc]
    simp only [Functor.map_comp, Category.assoc]
    rw [hr']
  have hsource := tensor_model_normalized_map l Y H R S model _hnormalization
    P Q I hP hQ hI (t ≫ a)
  have htarget := tensor_model_normalized_map l Y H R S model _hnormalization
    P' Q' I hP' hQ' hI a
  have : IsIso (DerivedCategory.Q.map a) := inferInstance
  apply (cancel_mono (DerivedCategory.Q.map a)).1
  rw [Category.assoc, htarget]
  rw [Category.assoc, ← Functor.map_comp, hsource, hc']
  exact (tensor_model_uncurry_naturality S (DerivedCategory.Q.map f)
    (DerivedCategory.Q.map g) (DerivedCategory.Q.map φ ≫ (R.model P' I hI).inv)).symm

end AlgebraicGeometry.ProEtaleWeilSheaf
