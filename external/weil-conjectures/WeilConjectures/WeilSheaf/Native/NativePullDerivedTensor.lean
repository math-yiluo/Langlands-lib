/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
import WeilConjectures.WeilSheaf.Native.NativePullSheafTensor
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

public import WeilConjectures.WeilSheaf.Native.NativeUpperStarKFlat
public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorPresentation
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorCanonicalData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorFullKFlatLocalization
import WeilConjectures.WeilSheaf.Native.NativeNormalizedTensorModels
import Mathlib.CategoryTheory.Localization.Prod

/-!
# The native derived pullback of Weil complexes and the tensor product

For an arbitrary morphism `p : Z ⟶ Y` of separated `k₀`-schemes of finite type, the derived
pullback `p^*` of native Weil complexes commutes with the native derived tensor product:
`p^*(A ⊗ T) ≅ p^* A ⊗ p^* T`, naturally in `A` and `T`
(`AlgebraicGeometry.ProEtaleWeilSheaf.exists_nativePullDerivedTensor`). On K-flat complexes it is
the localization of the totalization of the balanced sheaf comparison
`p^*(M ⊗ N) ≅ p^* M ⊗ p^* N` (`AlgebraicGeometry.ProEtaleWeilSheaf.native_pull_sheaf_tensor`):
the pullback preserves native K-flatness
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar_mapHomologicalComplex_obj`), and
the native derived tensor product is computed on K-flat complexes, which form a localizing
subcategory (`AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_full_kflat_localization`).

This is the comparison `μ` of the projection map of `D(p^*) ⊣ Rp_*`
(`AlgebraicGeometry.ProEtaleWeilSheaf.NativeProjectionTensorComparison`); for an open immersion
it is `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_derived_tensor`.

## Main statements

- `CategoryTheory.exists_derivedRestriction_of_total`: a total comparison of the tensor products
  of complexes descends to the derived categories, along the localization of the K-flat
  complexes.
- `AlgebraicGeometry.ProEtaleWeilSheaf.exists_nativePullDerivedTensor`: the native derived
  pullback/tensor comparison, with its sheaf and representative normalizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u a b

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The derived comparison `rho` is the localization, on K-flat complexes, of the total comparison
`t` of the tensor products of complexes, under the K-flat models of the derived tensor products.
This is `OpenTensorRestrictionNormalization` for the components of `t`. -/
def TotalRestrictionNormalization
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA : ∀ P T, flatA P → flatA T →
      (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA.obj P).obj T)))
    (modelB : ∀ P T, flatB P → flatB T →
      (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB.obj P).obj T)))
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA)
    (rho : DB ⋙ R.mapDerivedCategory ≅ R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA) :
    Prop :=
  OpenTensorRestrictionNormalization R TA TB DA DB flatA flatB hR modelA modelB
    (fun P T ↦ t.app (P, T)) rho

/-- A total comparison `R (P ⊗ T) ≅ R P ⊗ R T` of the tensor products of complexes, natural on
all complexes, descends to the derived categories along the localization of the K-flat complexes:
there is a natural isomorphism `R (K ⊗ L) ≅ R K ⊗ R L` of derived categories which, on K-flat
complexes, is the localization of the total comparison under the chosen K-flat models of the two
derived tensor products. -/
theorem exists_derivedRestriction_of_total
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA : ∀ P T, flatA P → flatA T →
      (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA.obj P).obj T)))
    (modelB : ∀ P T, flatB P → flatB T →
      (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB.obj P).obj T)))
    (hnA : ∀ P P' T T' (hP : flatA P) (hP' : flatA P')
      (hT : flatA T) (hT' : flatA T') (f : P ⟶ P') (g : T ⟶ T'),
      DA.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelA P' T' hP' hT').hom =
        (modelA P T hP hT).hom ≫ DerivedCategory.Q.map
          (((TA.map f).app T) ≫ (TA.obj P').map g))
    (hnB : ∀ P P' T T' (hP : flatB P) (hP' : flatB P')
      (hT : flatB T) (hT' : flatB T') (f : P ⟶ P') (g : T ⟶ T'),
      DB.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelB P' T' hP' hT').hom =
        (modelB P T hP hT).hom ≫ DerivedCategory.Q.map
          (((TB.map f).app T) ≫ (TB.obj P').map g))
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA)
    [((ObjectProperty.ι flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso B (.up ℤ)).inverseImage (ObjectProperty.ι flatB))] :
    ∃ rho : DB ⋙ R.mapDerivedCategory ≅ R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA,
      TotalRestrictionNormalization R TA TB DA DB flatA flatB hR modelA modelB t rho := by
  let iB := ObjectProperty.ι flatB
  let qB := iB ⋙ DerivedCategory.Q
  let WB := (HomologicalComplex.quasiIso B (.up ℤ)).inverseImage iB
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let rf := R.mapDerivedCategoryFactors
  let mB : qB.prod qB ⋙ DB ≅ iB.prod iB ⋙ Functor.uncurry.obj TB ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun PT ↦ modelB _ _ PT.1.property PT.2.property)
      (fun {PT PT'} fg ↦ hnB _ _ _ _ PT.1.property PT'.1.property
        PT.2.property PT'.2.property fg.1.hom fg.2.hom)
  let mA : ((iB ⋙ Rc) ⋙ DerivedCategory.Q).prod ((iB ⋙ Rc) ⋙ DerivedCategory.Q) ⋙ DA ≅
      (iB ⋙ Rc).prod (iB ⋙ Rc) ⋙ Functor.uncurry.obj TA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents
      (fun PT ↦ modelA _ _ (hR _ PT.1.property) (hR _ PT.2.property))
      (fun {PT PT'} fg ↦ hnA _ _ _ _ (hR _ PT.1.property) (hR _ PT'.1.property)
        (hR _ PT.2.property) (hR _ PT'.2.property) (Rc.map fg.1.hom) (Rc.map fg.2.hom))
  let gg : qB.prod qB ⋙ (DB ⋙ R.mapDerivedCategory) ≅
      qB.prod qB ⋙ (R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA) :=
    Functor.isoWhiskerRight mB R.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (iB.prod iB ⋙ Functor.uncurry.obj TB) rf ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (iB.prod iB) t) DerivedCategory.Q ≪≫
      mA.symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (Functor.isoWhiskerLeft iB rf).symm
          (Functor.isoWhiskerLeft iB rf).symm) DA
  let ff := Localization.fullyFaithfulWhiskeringLeft (qB.prod qB) (WB.prod WB)
    (DerivedCategory A)
  let rho := ff.preimageIso gg
  refine ⟨rho, ?_⟩
  unfold TotalRestrictionNormalization
  intro P T hP hT
  have h := NatTrans.congr_app (ff.map_preimage gg.hom) (⟨P, hP⟩, ⟨T, hT⟩)
  change rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) =
    gg.hom.app (⟨P, hP⟩, ⟨T, hT⟩) at h
  rw [h]
  dsimp only [gg, mB, mA, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_inv, Iso.symm_hom,
    NatIso.prod_hom, NatTrans.prod, Iso.refl_hom, NatTrans.id_app,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  dsimp only [iB, qB, Rc, rf, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj, Functor.id_obj, ObjectProperty.ι_obj]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  simp

/-- The total comparison `t : R (P ⊗ T) ≅ R P ⊗ R T` of the tensor products of complexes is the
sheaf comparison `sheaf : R (M ⊗ N) ≅ R M ⊗ R N` on each summand, inserted by `iA` and `iB`. -/
def TotalComparisonSummands
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Preadditive A] [Preadditive B]
    (R : B ⥤ A) [R.Additive]
    (SA : A → A → A) (SB : B → B → B)
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA : ∀ P T (p q n : ℤ), p + q = n → (SA (P.X p) (T.X q) ⟶ ((TA.obj P).obj T).X n))
    (iB : ∀ P T (p q n : ℤ), p + q = n → (SB (P.X p) (T.X q) ⟶ ((TB.obj P).obj T).X n))
    (sheaf : ∀ M N, R.obj (SB M N) ≅ SA (R.obj M) (R.obj N))
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA) : Prop :=
  ∀ P T (p q n : ℤ) (h : p + q = n),
    R.map (iB P T p q n h) ≫ (t.app (P, T)).hom.f n =
      (sheaf (P.X p) (T.X q)).hom ≫ iA ((R.mapHomologicalComplex (.up ℤ)).obj P)
        ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n h

end CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

-- the total and derived comparisons are matched with the canonical insertions
/-- **Derived restriction of the native tensor product** (blueprint:
`fix-prop-projection-formula`, the comparison `Lf^*(K ⊗ L) ≅ Lf^* K ⊗ Lf^* L` entering the
projection map). Let `R` be an exact functor from pro-étale Weil sheaves on `Y` to those on `Z`
which preserves coproducts and native K-flatness, with a balanced comparison
`r : R (M ⊗ N) ≅ R M ⊗ R N`. Then there are

* the totalization `t : R (P ⊗ T) ≅ R P ⊗ R T` of `r` on complexes, equal to `r` on each
  summand;
* a natural isomorphism `R (A ⊗ T) ≅ R A ⊗ R T` of native derived categories, which on K-flat
  complexes is the localization of `t`.

For `R` the pullback along any morphism of `k₀`-schemes, the hypotheses are
`AlgebraicGeometry.ProEtaleWeilSheaf.native_pull_sheaf_tensor` and
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar_mapHomologicalComplex_obj`. The
functor is kept abstract so that no operation is unfolded. -/
theorem exists_nativeDerivedRestrictionTensor
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesColimitsOfSize.{0, 0} R]
    (r : nativeOpenSheafTensor k₀ l Y ⋙ R ≅ R.prod R ⋙ nativeOpenSheafTensor k₀ l Z)
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T)) :
    ∃ (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
        (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
      (rho : nativeDerivedTensor k₀ l Y ⋙ R.mapDerivedCategory ≅
        R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l Z),
      TotalComparisonSummands R (fun M N ↦ tensor k₀ l Z N M) (fun M N ↦ tensor k₀ l Y N M)
        (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
        (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y)
        (fun M N ↦ r.app (M, N)) t ∧
      TotalRestrictionNormalization R (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
        (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
        (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
        (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y) t rho := by
  obtain ⟨-, -, hTZ, hιZ⟩ := native_open_tensor_canonical_data k₀ l Z
  obtain ⟨-, -, hTY, hιY⟩ := native_open_tensor_canonical_data k₀ l Y
  obtain ⟨t, ht⟩ := NativeRestrictionDescentProof.restriction_total_with_insertions R
    (nativeTensorBifunctor k₀ l Z).flip (nativeTensorBifunctor k₀ l Y).flip
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y) hTZ hTY hιZ hιY r
  have : ((ObjectProperty.ι (NativeIsKFlat k₀ l Y)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeIsKFlat k₀ l Y))) :=
    native_open_tensor_full_kflat_localization k₀ l Y
  obtain ⟨rho, hrho⟩ := exists_derivedRestriction_of_total R
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (by
      intro P P' T T' hP hP' hT hT' f g
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l Z).choose_spec.1
        P P' T T' hP hP' hT hT' f g)
    (by
      intro P P' T T' hP hP' hT hT' f g
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l Y).choose_spec.1
        P P' T T' hP hP' hT hT' f g) t
  exact ⟨t, rho, ht, hrho⟩

end AlgebraicGeometry.ProEtaleWeilSheaf

set_option maxRecDepth 4000

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison


open CategoryTheory CategoryTheory.Limits Opposite

namespace NativeRestrictionDescentProof

/-- Descent of a total comparison for an exact functor `R` along full K-flat
localizations, retaining the representative square. This is
`restriction_derived_representative` without the extension functor.

Source: Stacks 06YN; fully faithful precomposition with a localization
(blueprint: fix-prop-projection-formula).
Proof: on K-flat representatives compose the target model, the exact-derived factor of
`R`, the total comparison and the inverse source models; the product localization
descends this, and the inverse pairs cancel. -/
theorem exact_derived_representative
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA : ∀ P T, flatA P → flatA T →
      (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA.obj P).obj T)))
    (modelB : ∀ P T, flatB P → flatB T →
      (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB.obj P).obj T)))
    (hnA : ∀ P P' T T' (hP : flatA P) (hP' : flatA P')
      (hT : flatA T) (hT' : flatA T') (f : P ⟶ P') (g : T ⟶ T'),
      DA.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelA P' T' hP' hT').hom =
        (modelA P T hP hT).hom ≫ DerivedCategory.Q.map
          (((TA.map f).app T) ≫ (TA.obj P').map g))
    (hnB : ∀ P P' T T' (hP : flatB P) (hP' : flatB P')
      (hT : flatB T) (hT' : flatB T') (f : P ⟶ P') (g : T ⟶ T'),
      DB.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelB P' T' hP' hT').hom =
        (modelB P T hP hT).hom ≫ DerivedCategory.Q.map
          (((TB.map f).app T) ≫ (TB.obj P').map g))
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA)
    [((ObjectProperty.ι flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso B (.up ℤ)).inverseImage (ObjectProperty.ι flatB))] :
    ∃ rho : DB ⋙ R.mapDerivedCategory ≅ R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA,
      OpenTensorRestrictionNormalization R TA TB DA DB flatA flatB hR modelA modelB
        (fun P T ↦ t.app (P, T)) rho := by
  let iB := ObjectProperty.ι flatB
  let qB := iB ⋙ DerivedCategory.Q
  let WB := (HomologicalComplex.quasiIso B (.up ℤ)).inverseImage iB
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let rf := R.mapDerivedCategoryFactors
  let mB : qB.prod qB ⋙ DB ≅ iB.prod iB ⋙ Functor.uncurry.obj TB ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun PT ↦ modelB _ _ PT.1.property PT.2.property)
      (fun {PT PT'} fg ↦ hnB _ _ _ _ PT.1.property PT'.1.property
        PT.2.property PT'.2.property fg.1.hom fg.2.hom)
  let mA : ((iB ⋙ Rc) ⋙ DerivedCategory.Q).prod ((iB ⋙ Rc) ⋙ DerivedCategory.Q) ⋙ DA ≅
      (iB ⋙ Rc).prod (iB ⋙ Rc) ⋙ Functor.uncurry.obj TA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents
      (fun PT ↦ modelA _ _ (hR _ PT.1.property) (hR _ PT.2.property))
      (fun {PT PT'} fg ↦ hnA _ _ _ _ (hR _ PT.1.property) (hR _ PT'.1.property)
        (hR _ PT.2.property) (hR _ PT'.2.property) (Rc.map fg.1.hom) (Rc.map fg.2.hom))
  let gg : qB.prod qB ⋙ (DB ⋙ R.mapDerivedCategory) ≅
      qB.prod qB ⋙ (R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA) :=
    Functor.isoWhiskerRight mB R.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (iB.prod iB ⋙ Functor.uncurry.obj TB) rf ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (iB.prod iB) t) DerivedCategory.Q ≪≫
      mA.symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (Functor.isoWhiskerLeft iB rf).symm
          (Functor.isoWhiskerLeft iB rf).symm) DA
  let ff := Localization.fullyFaithfulWhiskeringLeft (qB.prod qB) (WB.prod WB)
    (DerivedCategory A)
  let rho := ff.preimageIso gg
  refine ⟨rho, ?_⟩
  intro P T hP hT
  have h := NatTrans.congr_app (ff.map_preimage gg.hom) (⟨P, hP⟩, ⟨T, hT⟩)
  change rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) =
    gg.hom.app (⟨P, hP⟩, ⟨T, hT⟩) at h
  rw [h]
  dsimp only [gg, mB, mA, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_inv, Iso.symm_hom,
    NatIso.prod_hom, NatTrans.prod, Iso.refl_hom, NatTrans.id_app,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  dsimp only [iB, qB, Rc, rf, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj, Functor.id_obj, ObjectProperty.ι_obj]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  simp

end NativeRestrictionDescentProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

section

attribute [local irreducible] upperStar nativeTensorTotal nativeDerivedTensor NativeIsKFlat
  nativeOpenTensorModel nativeOpenTensorInsertion

/-- The summand normalization of a total pullback/tensor comparison `t`: on every
homogeneous summand it is the balanced sheaf comparison `r` followed by the insertion.
Source: Stacks 012Z (blueprint: fix-prop-projection-formula). -/
def NativePullTensorSummands
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z) [R.PreservesZeroMorphisms]
    (r : nativeOpenSheafTensor k₀ l Y ⋙ R ≅ R.prod R ⋙ nativeOpenSheafTensor k₀ l Z)
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) : Prop :=
  ∀ P T (a c n : ℤ) (h : a + c = n),
    R.map (nativeOpenTensorInsertion k₀ l Y P T a c n h) ≫ (t.app (P, T)).hom.f n =
      (r.app (P.X a, T.X c)).hom ≫ nativeOpenTensorInsertion k₀ l Z
        ((R.mapHomologicalComplex (.up ℤ)).obj P)
        ((R.mapHomologicalComplex (.up ℤ)).obj T) a c n h

/-- The representative normalization of a derived pullback/tensor comparison `mu`: it is
exactly `OpenTensorRestrictionNormalization` for the native tensor models, the native
K-flat predicates and the total comparison `t`, as produced by
`NativeRestrictionDescentProof.restriction_derived_representative`.
Source: Stacks 06YN (blueprint: fix-prop-projection-formula). -/
def NativePullDerivedNormalization
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
    (mu : nativeDerivedTensor k₀ l Y ⋙ R.mapDerivedCategory ≅
      R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l Z) : Prop :=
  OpenTensorRestrictionNormalization R (nativeTensorTotal k₀ l Z)
    (nativeTensorTotal k₀ l Y) (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR (nativeOpenTensorModel k₀ l Z)
    (nativeOpenTensorModel k₀ l Y) (fun P T ↦ t.app (P, T)) mu

set_option backward.isDefEq.respectTransparency false in
-- Keep the exact functor abstract while assembling totalization and descent.
private theorem pullAbstract
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesColimitsOfSize.{0, 0} R]
    (r : nativeOpenSheafTensor k₀ l Y ⋙ R ≅ R.prod R ⋙ nativeOpenSheafTensor k₀ l Z)
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T)) :
    ∃ (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
        (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
      (mu : nativeDerivedTensor k₀ l Y ⋙ R.mapDerivedCategory ≅
        R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l Z),
      NativePullTensorSummands k₀ l R r t ∧
      NativePullDerivedNormalization k₀ l R hR t mu := by
  obtain ⟨_, _, hTA, hιA⟩ := native_open_tensor_canonical_data k₀ l Z
  obtain ⟨_, _, hTB, hιB⟩ := native_open_tensor_canonical_data k₀ l Y
  obtain ⟨t, ht⟩ := NativeRestrictionDescentProof.restriction_total_with_insertions R
    (nativeTensorBifunctor k₀ l Z).flip (nativeTensorBifunctor k₀ l Y).flip
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y)
    hTA hTB hιA hιB r
  have : ((ObjectProperty.ι (NativeIsKFlat k₀ l Y)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeIsKFlat k₀ l Y))) :=
    native_open_tensor_full_kflat_localization k₀ l Y
  obtain ⟨mu, hmu⟩ := NativeRestrictionDescentProof.exact_derived_representative R
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y) (nativeDerivedTensor k₀ l Z)
    (nativeDerivedTensor k₀ l Y) (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (by
      intro P P' T T' hP hP' hT hT' f g
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l Z).choose_spec.1
        P P' T T' hP hP' hT hT' f g)
    (by
      intro P P' T T' hP hP' hT hT' f g
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l Y).choose_spec.1
        P P' T T' hP hP' hT hT' f g) t
  exact ⟨t, mu, ht, hmu⟩

end

section

attribute [local irreducible] nativeTensorTotal nativeDerivedTensor NativeIsKFlat
  nativeOpenTensorModel nativeOpenTensorInsertion

/-- The derived balanced pullback/tensor comparison along an arbitrary morphism, given
that pullback preserves native two-sided K-flatness.

Source: Stacks 07A4, 06YN, 012Z (blueprint: fix-prop-projection-formula).
Proof: the balanced sheaf comparison `r` of `native_pull_sheaf_tensor` totalizes to a
chain isomorphism `t` with the prescribed summands (`restriction_total_with_insertions`;
pullback is a left adjoint, so it preserves coproducts). On native K-flat representatives,
which pullback preserves by `hR`, compose the normalized tensor models with `t`; the full
K-flat localization descends this to `mu`, with the representative square
`OpenTensorRestrictionNormalization`. -/
theorem native_pull_derived_tensor_of_kflat
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z (((upperStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj T)) :
    ∃ (r : nativeOpenSheafTensor k₀ l Y ⋙ upperStar k₀ l p ≅
        (upperStar k₀ l p).prod (upperStar k₀ l p) ⋙ nativeOpenSheafTensor k₀ l Z)
      (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙
          (upperStar k₀ l p).mapHomologicalComplex (.up ℤ) ≅
        ((upperStar k₀ l p).mapHomologicalComplex (.up ℤ)).prod
          ((upperStar k₀ l p).mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
      (mu : nativeDerivedTensor k₀ l Y ⋙ nativeOpenPull k₀ l p ≅
        (nativeOpenPull k₀ l p).prod (nativeOpenPull k₀ l p) ⋙ nativeDerivedTensor k₀ l Z),
      (∀ M N, HEq ((r.hom.app (M, N)).hom.f)
        ((ProEtale.adicUpperStarTensorLeftIso l
          (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))
            N.carrier).hom.app M.carrier)) ∧
      NativePullTensorSummands k₀ l (upperStar k₀ l p) r t ∧
      NativePullDerivedNormalization k₀ l (upperStar k₀ l p) hR t mu := by
  have : (upperStar k₀ l p).IsLeftAdjoint :=
    (upperStarLowerStarAdjunction k₀ l p).isLeftAdjoint
  obtain ⟨r, hr⟩ := native_pull_sheaf_tensor k₀ l p
  obtain ⟨t, mu, ht, hmu⟩ := pullAbstract k₀ l (upperStar k₀ l p) r hR
  exact ⟨r, t, mu, hr, ht, hmu⟩

end

end AlgebraicGeometry.ProEtaleWeilSheaf
