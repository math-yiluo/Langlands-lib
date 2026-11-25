/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorFullKFlatLocalization
public import WeilConjectures.WeilSheaf.Native.NativePullSheafTensor
public import WeilConjectures.WeilSheaf.Native.NativePullKFlat
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorCanonicalData
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorPresentation

/-!
# The native derived pullback–tensor comparison

For a morphism `g : Z ⟶ Y` of `k₀`-schemes we construct the comparison
`g^*(M ⊗ N) ≅ g^* M ⊗ g^* N` of native derived tensor products of pro-étale Weil sheaves,
following the open-immersion case:

- `nativePullSheafTensor g`: the sheaf-level comparison, whose underlying map of `ℓ`-adic
  sheaves is `ProEtale.adicUpperStarTensorLeftIso`;
- `nativePullTotalTensor g`: its totalization on cochain complexes, with summand formula
  `nativePullTotalTensor_summand`;
- `nativePullTensor g`: the derived comparison, and `nativePullTensor_normalization`, stating
  that on native K-flat representatives it is the localization of `nativePullTotalTensor g`.

The only input specific to `g` beyond the open case is K-flat preservation,
`nativeIsKFlat_upperStar_obj` (Stacks 06YW).
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

-- Use Mathlib's Grothendieck instance on module categories, as the native tensor files do;
-- the project shortcut would make the kernel unfold the coefficient categories.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

namespace NativeRestrictionDescentProof

/-- The constant zero functor, used as a placeholder extension in a descent input. -/
private abbrev zeroFunctor (A B : Type*) [Category* A] [Category* B] [Preadditive B]
    [HasZeroObject B] : A ⥤ B :=
  (Functor.const A).obj 0

private lemma isZero_zeroFunctor (A B : Type*) [Category* A] [Category* B] [Preadditive B]
    [HasZeroObject B] : IsZero (zeroFunctor A B) :=
  Functor.isZero _ (fun _ ↦ isZero_zero _)

private instance (A B : Type*) [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [HasZeroObject B] : (zeroFunctor A B).Additive where
  map_add {_ _ _ _} := (isZero_zero B).eq_of_src _ _

private instance (A B : Type*) [Category* A] [Category* B] [Preadditive B]
    [HasZeroObject B] : PreservesFiniteLimits (zeroFunctor A B) where
  preservesFiniteLimits J _ _ :=
    Functor.preservesLimitsOfShape_of_isZero _ (isZero_zeroFunctor A B) J

private instance (A B : Type*) [Category* A] [Category* B] [Preadditive B]
    [HasZeroObject B] : PreservesFiniteColimits (zeroFunctor A B) where
  preservesFiniteColimits J _ _ :=
    Functor.preservesColimitsOfShape_of_isZero _ (isZero_zeroFunctor A B) J

/-- A descent input with only the restriction functor and the tensor data; the extension,
the sheaf tensors and their comparisons are zero placeholders. -/
private abbrev restrictionOnlyInput
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop) :
    OpenTensorDescentInput A B :=
  { E := zeroFunctor A B
    R := R
    e_add := inferInstance
    r_add := inferInstance
    e_lim := inferInstance
    e_colim := inferInstance
    r_lim := inferInstance
    r_colim := inferInstance
    e_zero := inferInstance
    r_zero := inferInstance
    SA := zeroFunctor (A × A) A
    SB := zeroFunctor (B × B) B
    TA := TA
    TB := TB
    DA := DA
    DB := DB
    flatA := flatA
    flatB := flatB }

/-- The family of components of a natural total restriction comparison `t`, in the form used
by `OpenTensorRestrictionNormalization`. -/
def totalFamily {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    (R : B ⥤ A) [R.Additive]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA) (P T : CochainComplex B ℤ) :
    (R.mapHomologicalComplex (.up ℤ)).obj ((TB.obj P).obj T) ≅
      (TA.obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj T) :=
  t.app (P, T)

/-- The summand formula for a total restriction comparison `t` along `R`: on the summand
`R(P^p ⊗ T^q)` of `R Tot(P ⊗ T)` in degree `n = p + q`, the comparison `t` is the sheaf
comparison `r` followed by the summand insertion `iA`. -/
def RestrictionTotalSummands {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [Abelian B] (R : B ⥤ A) [R.Additive] (SA : A × A ⥤ A) (SB : B × B ⥤ B)
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA : ∀ P T (p q n : ℤ), p + q = n → (SA.obj (P.X p, T.X q) ⟶ ((TA.obj P).obj T).X n))
    (iB : ∀ P T (p q n : ℤ), p + q = n → (SB.obj (P.X p, T.X q) ⟶ ((TB.obj P).obj T).X n))
    (r : SB ⋙ R ≅ R.prod R ⋙ SA)
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA) : Prop :=
  ∀ P T (p q n : ℤ) (h : p + q = n),
    R.map (iB P T p q n h) ≫ (t.app (P, T)).hom.f n =
      (r.app (P.X p, T.X q)).hom ≫
        iA ((R.mapHomologicalComplex (.up ℤ)).obj P) ((R.mapHomologicalComplex (.up ℤ)).obj T)
          p q n h

/-- A sheaf restriction/tensor comparison totalizes with the prescribed summands, for sheaf
tensors, total tensors and insertions equal to the canonical ones (Stacks 012Z).
Proof: this repackages `restriction_total_with_insertions`. -/
theorem exists_restrictionTotalSummands
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [Abelian B] [HasCountableCoproducts A] [HasCountableCoproducts B]
    (R : B ⥤ A) [R.Additive] [PreservesColimitsOfSize.{0, 0} R]
    (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B)
    [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [∀ M, (G.obj M).PreservesZeroMorphisms]
    (SA : A × A ⥤ A) (SB : B × B ⥤ B)
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA : ∀ P T (p q n : ℤ), p + q = n → (SA.obj (P.X p, T.X q) ⟶ ((TA.obj P).obj T).X n))
    (iB : ∀ P T (p q n : ℤ), p + q = n → (SB.obj (P.X p, T.X q) ⟶ ((TB.obj P).obj T).X n))
    (hSA : SA = Functor.uncurry.obj F) (hSB : SB = Functor.uncurry.obj G)
    (hTA : TA = F.map₂CochainComplex) (hTB : TB = G.map₂CochainComplex)
    (hiA : HEq iA (fun (P T : CochainComplex A ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T F (.up ℤ) p q n h))
    (hiB : HEq iB (fun (P T : CochainComplex B ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T G (.up ℤ) p q n h))
    (r : SB ⋙ R ≅ R.prod R ⋙ SA) :
    ∃ t, RestrictionTotalSummands R SA SB TA TB iA iB r t := by
  subst hSA hSB
  exact restriction_total_with_insertions R F G TA TB iA iB hTA hTB hiA hiB r

/-- Descent of a total restriction comparison along the full K-flat localization, for an
arbitrary additive exact functor `R`: on K-flat representatives the derived comparison is the
localization of the given total comparison `t`.

Source: Stacks 06YN; fully faithful precomposition with a localization.
Proof: apply `restriction_derived_representative` to a descent input whose extension and
sheaf data are zero placeholders; these do not enter its conclusion. -/
theorem restriction_derived_normalization
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
    (hnA : ∀ P P' T T' (hP : flatA P) (hP' : flatA P') (hT : flatA T) (hT' : flatA T')
      (f : P ⟶ P') (g : T ⟶ T'),
      DA.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelA P' T' hP' hT').hom =
        (modelA P T hP hT).hom ≫ DerivedCategory.Q.map (((TA.map f).app T) ≫ (TA.obj P').map g))
    (hnB : ∀ P P' T T' (hP : flatB P) (hP' : flatB P') (hT : flatB T) (hT' : flatB T')
      (f : P ⟶ P') (g : T ⟶ T'),
      DB.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelB P' T' hP' hT').hom =
        (modelB P T hP hT).hom ≫ DerivedCategory.Q.map (((TB.map f).app T) ≫ (TB.obj P').map g))
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA)
    [((ObjectProperty.ι flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso B (.up ℤ)).inverseImage (ObjectProperty.ι flatB))] :
    ∃ rho : DB ⋙ R.mapDerivedCategory ≅ R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA,
      OpenTensorRestrictionNormalization R TA TB DA DB flatA flatB hR modelA modelB
        (totalFamily R TA TB t) rho :=
  restriction_derived_representative (restrictionOnlyInput R TA TB DA DB flatA flatB)
    { modelA := modelA
      modelB := modelB
      iA := fun _ _ _ _ _ _ ↦ 0
      iB := fun _ _ _ _ _ _ ↦ 0
      sheafGamma := fun _ _ ↦ Iso.refl _
      sheafRestriction := fun _ _ ↦ R.mapZeroObject }
    hR hnA hnB t

/-- The derived restriction comparison obtained by descending a total comparison `t` along the
K-flat localization; see `restrictionDerivedOfTotal_normalization`. -/
def restrictionDerivedOfTotal
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
    (hnA : ∀ P P' T T' (hP : flatA P) (hP' : flatA P') (hT : flatA T) (hT' : flatA T')
      (f : P ⟶ P') (g : T ⟶ T'),
      DA.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelA P' T' hP' hT').hom =
        (modelA P T hP hT).hom ≫ DerivedCategory.Q.map (((TA.map f).app T) ≫ (TA.obj P').map g))
    (hnB : ∀ P P' T T' (hP : flatB P) (hP' : flatB P') (hT : flatB T) (hT' : flatB T')
      (f : P ⟶ P') (g : T ⟶ T'),
      DB.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelB P' T' hP' hT').hom =
        (modelB P T hP hT).hom ≫ DerivedCategory.Q.map (((TB.map f).app T) ≫ (TB.obj P').map g))
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA)
    [((ObjectProperty.ι flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso B (.up ℤ)).inverseImage (ObjectProperty.ι flatB))]
    : DB ⋙ R.mapDerivedCategory ≅ R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA :=
  (restriction_derived_normalization R TA TB DA DB flatA flatB hR modelA modelB hnA hnB t).choose

/-- On K-flat representatives, `restrictionDerivedOfTotal` is the localization of the total
comparison `t`. -/
theorem restrictionDerivedOfTotal_normalization
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
    (hnA : ∀ P P' T T' (hP : flatA P) (hP' : flatA P') (hT : flatA T) (hT' : flatA T')
      (f : P ⟶ P') (g : T ⟶ T'),
      DA.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelA P' T' hP' hT').hom =
        (modelA P T hP hT).hom ≫ DerivedCategory.Q.map (((TA.map f).app T) ≫ (TA.obj P').map g))
    (hnB : ∀ P P' T T' (hP : flatB P) (hP' : flatB P') (hT : flatB T) (hT' : flatB T')
      (f : P ⟶ P') (g : T ⟶ T'),
      DB.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelB P' T' hP' hT').hom =
        (modelB P T hP hT).hom ≫ DerivedCategory.Q.map (((TB.map f).app T) ≫ (TB.obj P').map g))
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA)
    [((ObjectProperty.ι flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso B (.up ℤ)).inverseImage (ObjectProperty.ι flatB))]
    : OpenTensorRestrictionNormalization R TA TB DA DB flatA flatB hR modelA modelB
      (totalFamily R TA TB t)
      (restrictionDerivedOfTotal R TA TB DA DB flatA flatB hR modelA modelB hnA hnB t) :=
  (restriction_derived_normalization R TA TB DA DB flatA flatB hR modelA modelB hnA hnB
    t).choose_spec

end NativeRestrictionDescentProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

attribute [local irreducible] upperStar nativeTensorTotal nativeDerivedTensor NativeIsKFlat
  nativeOpenTensorModel nativeOpenTensorInsertion

/-- The balanced sheaf comparison `g^*(M ⊗ N) ≅ g^* M ⊗ g^* N` of pro-étale Weil sheaves,
chosen from `native_pull_sheaf_tensor`; its underlying map is
`ProEtale.adicUpperStarTensorLeftIso` (see `nativePullSheafTensor_hom_app_hom_f`).
Source: Stacks 07A4. -/
def nativePullSheafTensor :
    nativeOpenSheafTensor k₀ l Y ⋙ upperStar k₀ l g ≅
      (upperStar k₀ l g).prod (upperStar k₀ l g) ⋙ nativeOpenSheafTensor k₀ l Z :=
  (native_pull_sheaf_tensor k₀ l g).choose

/-- The underlying map of `ℓ`-adic sheaves of `nativePullSheafTensor` is the canonical
pullback–tensor comparison `ProEtale.adicUpperStarTensorLeftIso`. -/
theorem nativePullSheafTensor_hom_app_hom_f (M N : ProEtaleWeilSheaf k₀ l Y) :
    HEq (((nativePullSheafTensor k₀ l g).hom.app (M, N)).hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
          N.carrier).hom.app M.carrier) :=
  (native_pull_sheaf_tensor k₀ l g).choose_spec M N

/-- Pullback along `g` preserves native K-flat complexes (`nativeIsKFlat_upperStar_obj`),
restated with the coefficient instances used by the native tensor operations. -/
theorem nativeIsKFlat_mapHomologicalComplex_upperStar_obj
    (T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hT : NativeIsKFlat k₀ l Y T) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj T) := by
  have h := nativeIsKFlat_upperStar_obj k₀ l g
  -- The statement of `nativeIsKFlat_upperStar_obj` uses the project's shortcut instance
  -- `ModuleCat.isGrothendieckAbelian_of_commRing`; replace it by Mathlib's, syntactically.
  generalize ModuleCat.isGrothendieckAbelian_of_commRing (ULift.{u + 1} (PadicAlgCl l)) = p at h
  obtain rfl : p = instIsGrothendieckAbelianModuleCat (ULift.{u + 1} (PadicAlgCl l)) :=
    Subsingleton.elim _ _
  exact h T hT

/-- The totalization of `nativePullSheafTensor` exists, with the prescribed summands
(Stacks 012Z). -/
theorem exists_nativePullTotalTensor :
    ∃ t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙
          (upperStar k₀ l g).mapHomologicalComplex (.up ℤ) ≅
        ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).prod
            ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj (nativeTensorTotal k₀ l Z),
      NativeRestrictionDescentProof.RestrictionTotalSummands (upperStar k₀ l g)
        (nativeOpenSheafTensor k₀ l Z) (nativeOpenSheafTensor k₀ l Y)
        (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
        (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y)
        (nativePullSheafTensor k₀ l g) t :=
  have : (upperStar k₀ l g).IsLeftAdjoint := (upperStarLowerStarAdjunction k₀ l g).isLeftAdjoint
  NativeRestrictionDescentProof.exists_restrictionTotalSummands (upperStar k₀ l g)
    (nativeTensorBifunctor k₀ l Z).flip (nativeTensorBifunctor k₀ l Y).flip
    (nativeOpenSheafTensor k₀ l Z) (nativeOpenSheafTensor k₀ l Y)
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y) rfl rfl
    (native_open_tensor_canonical_data k₀ l Z).2.2.1
    (native_open_tensor_canonical_data k₀ l Y).2.2.1
    (native_open_tensor_canonical_data k₀ l Z).2.2.2
    (native_open_tensor_canonical_data k₀ l Y).2.2.2 (nativePullSheafTensor k₀ l g)

/-- The total complex comparison `g^* Tot(P ⊗ T) ≅ Tot(g^* P ⊗ g^* T)` obtained by
totalizing `nativePullSheafTensor` (Stacks 012Z); see `nativePullTotalTensor_summands`. -/
def nativePullTotalTensor :
    Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙
        (upperStar k₀ l g).mapHomologicalComplex (.up ℤ) ≅
      ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).prod
          ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z) :=
  (exists_nativePullTotalTensor k₀ l g).choose

/-- Each summand of `nativePullTotalTensor` is the sheaf comparison `nativePullSheafTensor`
followed by the native summand insertion `nativeOpenTensorInsertion`. -/
theorem nativePullTotalTensor_summands :
    NativeRestrictionDescentProof.RestrictionTotalSummands (upperStar k₀ l g)
      (nativeOpenSheafTensor k₀ l Z) (nativeOpenSheafTensor k₀ l Y)
      (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
      (nativeOpenTensorInsertion k₀ l Z) (nativeOpenTensorInsertion k₀ l Y)
      (nativePullSheafTensor k₀ l g) (nativePullTotalTensor k₀ l g) :=
  (exists_nativePullTotalTensor k₀ l g).choose_spec

variable [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The native K-flat models are natural in both K-flat representatives. -/
theorem nativeOpenTensorModel_naturality (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (P P' T T' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) (hP' : NativeIsKFlat k₀ l X P')
    (hT : NativeIsKFlat k₀ l X T) (hT' : NativeIsKFlat k₀ l X T')
    (f : P ⟶ P') (f' : T ⟶ T') :
    (nativeDerivedTensor k₀ l X).map
        (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map f')) ≫
        (nativeOpenTensorModel k₀ l X P' T' hP' hT').hom =
      (nativeOpenTensorModel k₀ l X P T hP hT).hom ≫ DerivedCategory.Q.map
        (((nativeTensorTotal k₀ l X).map f).app T ≫
          ((nativeTensorTotal k₀ l X).obj P').map f') := by
  unfold nativeOpenTensorModel
  exact (native_normalized_tensor_models k₀ l X).choose_spec.1 P P' T T' hP hP' hT hT' f f'

-- Keeping the restriction functor abstract keeps the kernel from unfolding `upperStar`.
/-- The derived comparison descending a total restriction/tensor comparison `t` of native total
tensors along an additive exact functor `R` preserving native K-flatness. -/
def nativeRestrictionDerivedTensor
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) :
    nativeDerivedTensor k₀ l Y ⋙ R.mapDerivedCategory ≅
      R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l Z :=
  have := native_open_tensor_full_kflat_localization k₀ l Y
  NativeRestrictionDescentProof.restrictionDerivedOfTotal R
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (nativeOpenTensorModel_naturality k₀ l Z) (nativeOpenTensorModel_naturality k₀ l Y) t

/-- The native derived pullback–tensor comparison `g^*(M ⊗ᴸ N) ≅ g^* M ⊗ᴸ g^* N` of
pro-étale Weil complexes, for any morphism `g` of `k₀`-schemes: the descent of
`nativePullTotalTensor` along the K-flat localization. On native K-flat representatives it is the
localization of `nativePullTotalTensor` under the models `nativeOpenTensorModel`
(`NativeRestrictionDescentProof.restrictionDerivedOfTotal_normalization`).
Source: Stacks 07A4, 06YN, 06YW. -/
def nativePullTensor :
    nativeDerivedTensor k₀ l Y ⋙ nativeOpenPull k₀ l g ≅
      (nativeOpenPull k₀ l g).prod (nativeOpenPull k₀ l g) ⋙ nativeDerivedTensor k₀ l Z :=
  nativeRestrictionDerivedTensor k₀ l (upperStar k₀ l g)
    (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g) (nativePullTotalTensor k₀ l g)

end AlgebraicGeometry.ProEtaleWeilSheaf
