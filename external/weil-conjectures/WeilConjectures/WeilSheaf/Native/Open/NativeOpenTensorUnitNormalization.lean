/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.CategoryTheory.SixFunctors.OpenTensorUnitTotalization
import WeilConjectures.CategoryTheory.OpenTensorPresentation.OpenTensorUnitLocalization
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorCanonicalData

/-! # Derived unit normalization for the native open tensor

Source: Stacks 0GL1 and 0E8I, native open tensor proof step 7
(blueprint: new-lem-sf-native-open-tensor-unit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorMap
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorModel
  AlgebraicGeometry.ProEtaleWeilSheaf.tensor
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf
private theorem normalization_of_pinned_presentation
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    [HasCountableCoproducts A] [HasCountableCoproducts B]
    (E0 : A ⥤ B) (R0 : B ⥤ A) [E0.Additive] [R0.Additive]
    [PreservesFiniteLimits E0] [PreservesFiniteColimits E0]
    [PreservesFiniteLimits R0] [PreservesFiniteColimits R0]
    (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B)
    [F.Additive] [∀ M, (F.obj M).Additive] [G.Additive] [∀ M, (G.obj M).Additive]
    (sheafA0 : A → A → A) (sheafB0 : B → B → B)
    (mapA0 : ∀ {M M' : A}, (M ⟶ M') → ∀ N, sheafA0 M N ⟶ sheafA0 M' N)
    (TA0 : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB0 : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA0 : ∀ (P T : CochainComplex A ℤ) (p q n : ℤ), p + q = n →
      (sheafA0 (P.X p) (T.X q) ⟶ ((TA0.obj P).obj T).X n))
    (iB0 : ∀ (P T : CochainComplex B ℤ) (p q n : ℤ), p + q = n →
      (sheafB0 (P.X p) (T.X q) ⟶ ((TB0.obj P).obj T).X n))
    (hSA0 : sheafA0 = fun M N ↦ (F.obj M).obj N)
    (hSB0 : sheafB0 = fun M N ↦ (G.obj M).obj N)
    (hTA0 : TA0 = F.map₂CochainComplex) (hTB0 : TB0 = G.map₂CochainComplex)
    (hmapA0 : HEq @mapA0 (fun {M M' : A} (f : M ⟶ M') N ↦ (F.map f).app N))
    (hiA0 : HEq iA0 (fun (P T : CochainComplex A ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T F (.up ℤ) p q n h))
    (hiB0 : HEq iB0 (fun (P T : CochainComplex B ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T G (.up ℤ) p q n h))
    (DA0 : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB0 : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA0 : CochainComplex A ℤ → Prop) (flatB0 : CochainComplex B ℤ → Prop)
    (modelA0 : ∀ P T, flatA0 P → flatA0 T →
      (DA0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA0.obj P).obj T)))
    (modelB0 : ∀ P T, flatB0 P → flatB0 T →
      (DB0.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB0.obj P).obj T)))
    (adj : E0 ⊣ R0)
    (sheafGamma0 : ∀ M N, sheafB0 (E0.obj M) N ≅
      E0.obj (sheafA0 M (R0.obj N)))
    (sheafRestriction0 : ∀ M N, R0.obj (sheafB0 M N) ≅
      sheafA0 (R0.obj M) (R0.obj N))
    (hsheaf : ∀ M N, HEq (adj.homEquiv _ _ (sheafGamma0 M N).inv)
      (mapA0 (adj.unit.app M) (R0.obj N) ≫
        (sheafRestriction0 (E0.obj M) N).inv))
    (hnat : ∀ P P' T (hP : flatA0 P) (hP' : flatA0 P') (hT : flatA0 T) (f : P ⟶ P'),
      DA0.map (Prod.mkHom (DerivedCategory.Q.map f) (𝟙 (DerivedCategory.Q.obj T))) ≫
        (modelA0 P' T hP' hT).hom =
      (modelA0 P T hP hT).hom ≫ DerivedCategory.Q.map ((TA0.map f).app T))
    (hA : ∀ M : DerivedCategory A,
      ∃ P : CochainComplex A ℤ, flatA0 P ∧ Nonempty (DerivedCategory.Q.obj P ≅ M))
    (hB : ∀ N : DerivedCategory B,
      ∃ T : CochainComplex B ℤ, flatB0 T ∧ Nonempty (DerivedCategory.Q.obj T ≅ N))
    (rho : DB0 ⋙ R0.mapDerivedCategory ≅
      R0.mapDerivedCategory.prod R0.mapDerivedCategory ⋙ DA0)
    (gamma : E0.mapDerivedCategory.prod (𝟭 _) ⋙ DB0 ≅
      (𝟭 _).prod R0.mapDerivedCategory ⋙ DA0 ⋙ E0.mapDerivedCategory)
    (c : OpenTensorPresentation A B)
    (_hc :
      HEq c.E E0 ∧ HEq c.R R0 ∧
      HEq c.SA (Functor.uncurry.obj F) ∧ HEq c.SB (Functor.uncurry.obj G) ∧
      HEq c.TA TA0 ∧ HEq c.TB TB0 ∧
      HEq c.DA DA0 ∧ HEq c.DB DB0 ∧ HEq c.flatA flatA0 ∧ HEq c.flatB flatB0 ∧
      HEq c.modelA modelA0 ∧ HEq c.modelB modelB0 ∧
      HEq c.iA iA0 ∧ HEq c.iB iB0 ∧
      HEq c.sheafGamma sheafGamma0 ∧ HEq c.gamma gamma ∧
      HEq c.sheafRestriction sheafRestriction0 ∧ HEq c.restriction rho) :
    OpenTensorUnitNormalization E0.mapDerivedCategory R0.mapDerivedCategory
      DA0 DB0 adj.mapExactDerivedCategory rho gamma := by
  subst sheafA0
  subst sheafB0
  subst TA0
  subst TB0
  have hmapA0 := eq_of_heq hmapA0
  subst mapA0
  have hiA0 := eq_of_heq hiA0
  subst iA0
  have hiB0 := eq_of_heq hiB0
  subst iB0
  rcases c with @⟨E, R, eadd, radd, elim, ecolim, rlim, rcolim, SA, SB, TA, TB,
    DA, DB, flatA, flatB, hE, hR, modelA, modelB, iA, iB, sheafGamma, totalGamma,
    summands, sheafRestriction, totalRestriction, restriction_summands, restriction,
    restriction_model, gamma', model⟩
  dsimp only at _hc
  rcases _hc with ⟨he, hr, hsa, hsb, hta, htb, hda, hdb, hfa, hfb, hma, hmb,
    hia, hib, hsg, hg, hsr, hres⟩
  have he := eq_of_heq he
  subst E
  have hr := eq_of_heq hr
  subst R
  have hsa := eq_of_heq hsa
  subst SA
  have hsb := eq_of_heq hsb
  subst SB
  have hta := eq_of_heq hta
  subst TA
  have htb := eq_of_heq htb
  subst TB
  have hda := eq_of_heq hda
  subst DA
  have hdb := eq_of_heq hdb
  subst DB
  have hfa := eq_of_heq hfa
  subst flatA
  have hfb := eq_of_heq hfb
  subst flatB
  have hma := eq_of_heq hma
  subst modelA
  have hmb := eq_of_heq hmb
  subst modelB
  have hia := eq_of_heq hia
  subst iA
  have hib := eq_of_heq hib
  subst iB
  have hsg := eq_of_heq hsg
  subst sheafGamma
  have hg := eq_of_heq hg
  subst gamma
  have hsr := eq_of_heq hsr
  subst sheafRestriction
  have hres := eq_of_heq hres
  subst rho
  let c' : OpenTensorPresentation A B :=
    { E := E0
      R := R0
      e_add := eadd
      r_add := radd
      e_lim := elim
      e_colim := ecolim
      r_lim := rlim
      r_colim := rcolim
      SA := Functor.uncurry.obj F
      SB := Functor.uncurry.obj G
      TA := F.map₂CochainComplex
      TB := G.map₂CochainComplex
      DA := DA0
      DB := DB0
      flatA := flatA0
      flatB := flatB0
      hE := hE
      hR := hR
      modelA := modelA0
      modelB := modelB0
      iA := (fun (P T : CochainComplex A ℤ) p q n h ↦
        HomologicalComplex.ιMapBifunctor P T F (.up ℤ) p q n h)
      iB := (fun (P T : CochainComplex B ℤ) p q n h ↦
        HomologicalComplex.ιMapBifunctor P T G (.up ℤ) p q n h)
      sheafGamma := sheafGamma0
      totalGamma := totalGamma
      summands := summands
      sheafRestriction := sheafRestriction0
      totalRestriction := totalRestriction
      restriction_summands := restriction_summands
      restriction := restriction
      restriction_model := restriction_model
      gamma := gamma'
      model := model }
  apply c'.unit_normalization adj
  · intro P T _ _
    exact openTensorUnitTotalization (E0) (R0)
      F G
      adj sheafGamma0 sheafRestriction0 (fun M N ↦ eq_of_heq (hsheaf M N))
      totalGamma totalRestriction summands restriction_summands P T
  · intro P T hP hT
    exact hnat P _ _ hP (hR _ (hE P hP)) (hR T hT)
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)
  · exact hA
  · exact hB

private theorem first_naturality_from_both
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    (Q : A ⥤ B) (T : A ⥤ A ⥤ A) (D : B × B ⥤ B) (flat : A → Prop)
    (e : ∀ P N, flat P → flat N → (D.obj (Q.obj P, Q.obj N) ≅ Q.obj ((T.obj P).obj N)))
    (h : ∀ P P' N N' (hP : flat P) (hP' : flat P') (hN : flat N) (hN' : flat N')
      (f : P ⟶ P') (g : N ⟶ N'),
      D.map (Prod.mkHom (Q.map f) (Q.map g)) ≫ (e P' N' hP' hN').hom =
        (e P N hP hN).hom ≫ Q.map ((T.map f).app N ≫ (T.obj P').map g))
    (P P' N : A) (hP : flat P) (hP' : flat P') (hN : flat N) (f : P ⟶ P') :
    D.map (Prod.mkHom (Q.map f) (𝟙 (Q.obj N))) ≫ (e P' N hP' hN).hom =
      (e P N hP hN).hom ≫ Q.map ((T.map f).app N) := by
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h P P' N N hP hP' hN hN f (𝟙 N)

section ModelNaturality
attribute [local irreducible] nativeTensorTotal

private theorem native_model_first_naturality
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (P P' T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) (hP' : NativeIsKFlat k₀ l X P')
    (hT : NativeIsKFlat k₀ l X T) (f : P ⟶ P') :
    (nativeDerivedTensor k₀ l X).map
        (Prod.mkHom (DerivedCategory.Q.map f) (𝟙 (DerivedCategory.Q.obj T))) ≫
      (nativeOpenTensorModel k₀ l X P' T hP' hT).hom =
    (nativeOpenTensorModel k₀ l X P T hP hT).hom ≫
      DerivedCategory.Q.map (((nativeTensorTotal k₀ l X).map f).app T) := by
  simpa only [nativeOpenTensorModel] using
    first_naturality_from_both DerivedCategory.Q (nativeTensorTotal k₀ l X)
      (nativeDerivedTensor k₀ l X) (NativeIsKFlat k₀ l X)
      (native_normalized_tensor_models k₀ l X).choose
      (native_normalized_tensor_models k₀ l X).choose_spec.1 P P' T hP hP' hT f

end ModelNaturality

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

private theorem native_presentation_unit_normalization
    (E0 : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    (R0 : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [E0.Additive] [R0.Additive]
    [PreservesFiniteLimits E0] [PreservesFiniteColimits E0]
    [PreservesFiniteLimits R0] [PreservesFiniteColimits R0]
    (adj : E0 ⊣ R0)
    (sg : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
      tensor k₀ l Z N (E0.obj M) ≅ E0.obj (tensor k₀ l U (R0.obj N) M))
    (sr : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      R0.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R0.obj N) (R0.obj M))
    (hs : ∀ M N, HEq (adj.homEquiv _ _ (sg M N).inv)
      ((tensorFunctor k₀ l U (R0.obj N)).map (adj.unit.app M) ≫
        (sr (E0.obj M) N).inv))
    (rho : nativeDerivedTensor k₀ l Z ⋙ R0.mapDerivedCategory ≅
      R0.mapDerivedCategory.prod R0.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l U)
    (gamma : E0.mapDerivedCategory.prod (𝟭 _) ⋙ nativeDerivedTensor k₀ l Z ≅
      (𝟭 _).prod R0.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l U ⋙ E0.mapDerivedCategory)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (hc :
      HEq c.E E0 ∧ HEq c.R R0 ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafGamma sg ∧ HEq c.gamma gamma ∧
      HEq c.sheafRestriction sr ∧ HEq c.restriction rho) :
    OpenTensorUnitNormalization E0.mapDerivedCategory R0.mapDerivedCategory
      (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
      adj.mapExactDerivedCategory rho gamma := by
  obtain ⟨hSA, hmap, hTA, hIA⟩ := native_open_tensor_canonical_data k₀ l U
  obtain ⟨hSB, _, hTB, hIB⟩ := native_open_tensor_canonical_data k₀ l Z
  refine normalization_of_pinned_presentation E0 R0
    (nativeTensorBifunctor k₀ l U).flip (nativeTensorBifunctor k₀ l Z).flip
    (fun M N ↦ tensor k₀ l U N M) (fun M N ↦ tensor k₀ l Z N M)
    (fun {M M'} (f : M ⟶ M') N ↦ (tensorFunctor k₀ l U N).map f)
    (nativeTensorTotal k₀ l U) (nativeTensorTotal k₀ l Z)
    (nativeOpenTensorInsertion k₀ l U) (nativeOpenTensorInsertion k₀ l Z)
    hSA hSB hTA hTB hmap hIA hIB
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    (NativeIsKFlat k₀ l U) (NativeIsKFlat k₀ l Z)
    (nativeOpenTensorModel k₀ l U) (nativeOpenTensorModel k₀ l Z)
    adj sg sr hs ?_
    (native_two_sided_kflat_representatives k₀ l U)
    (native_two_sided_kflat_representatives k₀ l Z) rho gamma c ?_
  · exact native_model_first_naturality k₀ l U
  · simpa only [nativeOpenSheafTensor] using hc

/-- The supplied native presentation satisfies the derived unit transpose equation.

Source: Stacks 0GL1 and 0E8I; the localized representative squares and the
open-unit transpose. The proof totalizes the sheaf inverse-unit equation on
summands, applies the specified K-flat models, and descends the resulting
identity through the exact derived localization.
(blueprint: new-lem-sf-native-open-tensor-unit-normalization). -/
theorem native_open_tensor_unit_normalization (s : NativeOpenTensorData k₀ l j)
    (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
      (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
    (gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (_hc :
      HEq c.E (extensionByZero k₀ l j) ∧ HEq c.R (upperStar k₀ l j) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafGamma s.sheafGamma ∧ HEq c.gamma gamma ∧
      HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction rho) :
    OpenTensorUnitNormalization
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    s.adj.mapExactDerivedCategory rho gamma := by
  exact native_presentation_unit_normalization k₀ l
    (extensionByZero k₀ l j) (upperStar k₀ l j) s.adj
    s.sheafGamma s.sheafRestriction s.sheaf_inverse rho gamma c _hc

end AlgebraicGeometry.ProEtaleWeilSheaf
