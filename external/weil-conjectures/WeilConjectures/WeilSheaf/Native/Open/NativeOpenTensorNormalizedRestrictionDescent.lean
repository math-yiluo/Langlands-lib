/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorSheafComparisons
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorCanonicalData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorFullKFlatLocalization
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.Localization.Prod

/-! # Normalized native open tensor restriction descent

Source: Stacks 0GL1, 06YN and 012Z; native open tensor proof steps 3--6.
(blueprint: lem-sf-native-open-tensor-restriction-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 4000

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace NativeRestrictionDescentProof

/-- Composing the two partial maps of a total bifunctor complex gives `mapBifunctorMap`. -/
theorem map₂CochainComplex_map_comp_map {D₁ D₂ D₃ : Type*}
    [Category* D₁] [Category* D₂] [Category* D₃]
    [HasZeroMorphisms D₁] [HasZeroMorphisms D₂] [Preadditive D₃]
    (F : D₁ ⥤ D₂ ⥤ D₃) [F.PreservesZeroMorphisms]
    [∀ M, (F.obj M).PreservesZeroMorphisms]
    [∀ (P : CochainComplex D₁ ℤ) (C : CochainComplex D₂ ℤ),
      HomologicalComplex.HasMapBifunctor P C F (.up ℤ)]
    {P P' : CochainComplex D₁ ℤ} {C C' : CochainComplex D₂ ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    ((F.map₂CochainComplex.map a).app C) ≫ (F.map₂CochainComplex.obj P').map b =
      HomologicalComplex.mapBifunctorMap a b F (.up ℤ) := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp [HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc]

/-- A natural sheaf restriction/tensor comparison totalizes, with its prescribed summands.

Source: Stacks 012Z; the comparison `HomologicalComplex.mapBifunctorComparison`.
Proof: the comparison of total complexes induced by the components of `r` is natural
in both complexes and invertible; its summand formula is the defining one. -/
theorem restriction_total_comparison
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [Abelian B] [HasCountableCoproducts A] [HasCountableCoproducts B]
    (R : B ⥤ A) [R.Additive] [PreservesColimitsOfSize.{0, 0} R]
    (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B)
    [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [∀ M, (G.obj M).PreservesZeroMorphisms]
    (r : Functor.uncurry.obj G ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj F) :
    ∃ e : Functor.uncurry.obj G.map₂CochainComplex ⋙ R.mapHomologicalComplex (.up ℤ) ≅
        (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj F.map₂CochainComplex,
      ∀ P T (p q n : ℤ) (h : p + q = n),
        R.map (HomologicalComplex.ιMapBifunctor P T G (.up ℤ) p q n h) ≫
            (e.app (P, T)).hom.f n =
          (r.app (P.X p, T.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
            ((R.mapHomologicalComplex (.up ℤ)).obj P)
            ((R.mapHomologicalComplex (.up ℤ)).obj T) F (.up ℤ) p q n h := by
  let τ : (Functor.postcompose₂.obj R).obj G ⟶
      (((Functor.whiskeringLeft₂ A).obj R).obj R).obj F :=
    { app M :=
        { app N := r.hom.app (M, N)
          naturality N N' b := by
            simpa using r.hom.naturality (Prod.mkHom (𝟙 M) b) }
      naturality M M' a := by
        ext N
        simpa using r.hom.naturality (Prod.mkHom a (𝟙 N)) }
  have hτ (M : B) (N : B) : IsIso ((τ.app M).app N) :=
    inferInstanceAs (IsIso (r.hom.app (M, N)))
  let e : Functor.uncurry.obj G.map₂CochainComplex ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj F.map₂CochainComplex :=
    NatIso.ofComponents
      (fun PT ↦ asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) PT.1 PT.2))
      (by
        intro PT PT' fg
        dsimp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
          Functor.prod_obj, asIso_hom]
        rw [map₂CochainComplex_map_comp_map, map₂CochainComplex_map_comp_map]
        exact HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) fg.1 fg.2)
  refine ⟨e, fun P T p q n h ↦ ?_⟩
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX τ (.up ℤ) P T p q n h

/-- The totalization of `restriction_total_comparison`, stated for recorded total
functors and insertions equal to the canonical ones. -/
theorem restriction_total_with_insertions
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [Abelian B] [HasCountableCoproducts A] [HasCountableCoproducts B]
    (R : B ⥤ A) [R.Additive] [PreservesColimitsOfSize.{0, 0} R]
    (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B)
    [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [∀ M, (G.obj M).PreservesZeroMorphisms]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA : ∀ (P T : CochainComplex A ℤ) (p q n : ℤ), p + q = n →
      ((F.obj (P.X p)).obj (T.X q) ⟶ ((TA.obj P).obj T).X n))
    (iB : ∀ (P T : CochainComplex B ℤ) (p q n : ℤ), p + q = n →
      ((G.obj (P.X p)).obj (T.X q) ⟶ ((TB.obj P).obj T).X n))
    (hTA : TA = F.map₂CochainComplex) (hTB : TB = G.map₂CochainComplex)
    (hiA : HEq iA (fun (P T : CochainComplex A ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T F (.up ℤ) p q n h))
    (hiB : HEq iB (fun (P T : CochainComplex B ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T G (.up ℤ) p q n h))
    (r : Functor.uncurry.obj G ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj F) :
    ∃ e : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
        (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj TA,
      ∀ P T (p q n : ℤ) (h : p + q = n),
        R.map (iB P T p q n h) ≫ (e.app (P, T)).hom.f n =
          (r.app (P.X p, T.X q)).hom ≫ iA ((R.mapHomologicalComplex (.up ℤ)).obj P)
            ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n h := by
  subst TA
  subst TB
  obtain rfl := eq_of_heq hiA
  obtain rfl := eq_of_heq hiB
  exact restriction_total_comparison R F G r

attribute [local instance] OpenTensorDescentInput.e_add OpenTensorDescentInput.r_add
  OpenTensorDescentInput.e_lim OpenTensorDescentInput.e_colim
  OpenTensorDescentInput.r_lim OpenTensorDescentInput.r_colim
  OpenTensorDescentInput.e_zero OpenTensorDescentInput.r_zero

/-- Descent of a total restriction comparison along the full K-flat localizations,
retaining every representative square.

Source: Stacks 06YN; fully faithful precomposition with a localization.
Proof: on K-flat representatives compose the ambient model, the restriction factor,
the total comparison, the inverse open model and the inverse restriction factors;
the product localization descends this, and the inverse pairs cancel. -/
theorem restriction_derived_representative
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    (hR : ∀ T, c.flatB T → c.flatA ((c.R.mapHomologicalComplex (.up ℤ)).obj T))
    (hnA : ∀ P P' T T' (hP : c.flatA P) (hP' : c.flatA P')
      (hT : c.flatA T) (hT' : c.flatA T') (f : P ⟶ P') (g : T ⟶ T'),
      c.DA.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (m.modelA P' T' hP' hT').hom =
        (m.modelA P T hP hT).hom ≫ DerivedCategory.Q.map
          (((c.TA.map f).app T) ≫ (c.TA.obj P').map g))
    (hnB : ∀ P P' T T' (hP : c.flatB P) (hP' : c.flatB P')
      (hT : c.flatB T) (hT' : c.flatB T') (f : P ⟶ P') (g : T ⟶ T'),
      c.DB.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (m.modelB P' T' hP' hT').hom =
        (m.modelB P T hP hT).hom ≫ DerivedCategory.Q.map
          (((c.TB.map f).app T) ≫ (c.TB.obj P').map g))
    (t : Functor.uncurry.obj c.TB ⋙ c.R.mapHomologicalComplex (.up ℤ) ≅
      (c.R.mapHomologicalComplex (.up ℤ)).prod (c.R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj c.TA)
    [((ObjectProperty.ι c.flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso B (.up ℤ)).inverseImage (ObjectProperty.ι c.flatB))] :
    ∃ rho : c.DB ⋙ c.R.mapDerivedCategory ≅
        c.R.mapDerivedCategory.prod c.R.mapDerivedCategory ⋙ c.DA,
      OpenTensorRestrictionNormalization c.R c.TA c.TB c.DA c.DB
        c.flatA c.flatB hR m.modelA m.modelB (fun P T ↦ t.app (P, T)) rho := by
  let iB := ObjectProperty.ι c.flatB
  let qB := iB ⋙ DerivedCategory.Q
  let WB := (HomologicalComplex.quasiIso B (.up ℤ)).inverseImage iB
  let Rc := c.R.mapHomologicalComplex (.up ℤ)
  let rf := c.R.mapDerivedCategoryFactors
  let mB : qB.prod qB ⋙ c.DB ≅ iB.prod iB ⋙ Functor.uncurry.obj c.TB ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun PT ↦ m.modelB _ _ PT.1.property PT.2.property)
      (fun {PT PT'} fg ↦ hnB _ _ _ _ PT.1.property PT'.1.property
        PT.2.property PT'.2.property fg.1.hom fg.2.hom)
  let mA : ((iB ⋙ Rc) ⋙ DerivedCategory.Q).prod ((iB ⋙ Rc) ⋙ DerivedCategory.Q) ⋙ c.DA ≅
      (iB ⋙ Rc).prod (iB ⋙ Rc) ⋙ Functor.uncurry.obj c.TA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents
      (fun PT ↦ m.modelA _ _ (hR _ PT.1.property) (hR _ PT.2.property))
      (fun {PT PT'} fg ↦ hnA _ _ _ _ (hR _ PT.1.property) (hR _ PT'.1.property)
        (hR _ PT.2.property) (hR _ PT'.2.property) (Rc.map fg.1.hom) (Rc.map fg.2.hom))
  let gg : qB.prod qB ⋙ (c.DB ⋙ c.R.mapDerivedCategory) ≅
      qB.prod qB ⋙ (c.R.mapDerivedCategory.prod c.R.mapDerivedCategory ⋙ c.DA) :=
    Functor.isoWhiskerRight mB c.R.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (iB.prod iB ⋙ Functor.uncurry.obj c.TB) rf ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (iB.prod iB) t) DerivedCategory.Q ≪≫
      mA.symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (Functor.isoWhiskerLeft iB rf).symm
          (Functor.isoWhiskerLeft iB rf).symm) c.DA
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

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

section

attribute [local irreducible] extensionByZero upperStar nativeTensorTotal
  nativeDerivedTensor NativeIsKFlat nativeOpenTensorModel nativeOpenTensorInsertion

-- Keep the exact operations as parameters while comparing tensor components.
private def restrictionInput
    (E : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [E.Additive] [R.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [E.PreservesZeroMorphisms] [R.PreservesZeroMorphisms] :
    OpenTensorDescentInput (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z) :=
  { E := E
    R := R
    SA := nativeOpenSheafTensor k₀ l U
    SB := nativeOpenSheafTensor k₀ l Z
    TA := nativeTensorTotal k₀ l U
    TB := nativeTensorTotal k₀ l Z
    DA := nativeDerivedTensor k₀ l U
    DB := nativeDerivedTensor k₀ l Z
    flatA := NativeIsKFlat k₀ l U
    flatB := NativeIsKFlat k₀ l Z }

set_option backward.isDefEq.respectTransparency false in
-- This assembly combines totalization, localization and the fixed-model square.
private theorem restrictionAbstract
    (E : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [E.Additive] [R.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [E.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    [PreservesColimitsOfSize.{0, 0} R]
    (r : nativeOpenSheafTensor k₀ l Z ⋙ R ≅ R.prod R ⋙ nativeOpenSheafTensor k₀ l U)
    (hR : ∀ T, NativeIsKFlat k₀ l Z T →
      NativeIsKFlat k₀ l U ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (m : OpenTensorDescentModels (restrictionInput k₀ l E R))
    (hA : HEq m.modelA (nativeOpenTensorModel k₀ l U))
    (hB : HEq m.modelB (nativeOpenTensorModel k₀ l Z))
    (hiA : HEq m.iA (nativeOpenTensorInsertion k₀ l U))
    (hiB : HEq m.iB (nativeOpenTensorInsertion k₀ l Z))
    (hr : ∀ M N, HEq (m.sheafRestriction M N) (r.app (M, N))) :
    Nonempty (OpenTensorRestrictionDescentData (restrictionInput k₀ l E R) m) := by
  -- Derive zero preservation directly, avoiding search through the tensor constructions.
  have : (nativeTensorBifunctor k₀ l U).flip.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : ∀ M, ((nativeTensorBifunctor k₀ l U).flip.obj M).PreservesZeroMorphisms :=
    fun M ↦ Functor.preservesZeroMorphisms_of_additive _
  have : (nativeTensorBifunctor k₀ l Z).flip.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : ∀ M, ((nativeTensorBifunctor k₀ l Z).flip.obj M).PreservesZeroMorphisms :=
    fun M ↦ Functor.preservesZeroMorphisms_of_additive _
  obtain ⟨_, _, hTA, hιA⟩ := native_open_tensor_canonical_data k₀ l U
  obtain ⟨_, _, hTB, hιB⟩ := native_open_tensor_canonical_data k₀ l Z
  let c := restrictionInput k₀ l E R
  obtain ⟨t, ht⟩ := NativeRestrictionDescentProof.restriction_total_with_insertions R
    (nativeTensorBifunctor k₀ l U).flip (nativeTensorBifunctor k₀ l Z).flip
    c.TA c.TB m.iA m.iB hTA hTB (hiA.trans hιA) (hiB.trans hιB) r
  have : ((ObjectProperty.ι c.flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage (ObjectProperty.ι c.flatB)) :=
    native_open_tensor_full_kflat_localization k₀ l Z
  obtain ⟨rho, hrho⟩ := NativeRestrictionDescentProof.restriction_derived_representative
    c m hR
    (by
      rw [eq_of_heq hA]
      intro P P' T T' hP hP' hT hT' f g
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l U).choose_spec.1
        P P' T T' hP hP' hT hT' f g)
    (by
      rw [eq_of_heq hB]
      intro P P' T T' hP hP' hT hT' f g
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l Z).choose_spec.1
        P P' T T' hP hP' hT hT' f g) t
  refine ⟨{ hR := hR
            total := fun P T ↦ t.app (P, T)
            rho := rho
            summands := fun P T p q n h ↦ ?_
            model := hrho }⟩
  rw [eq_of_heq (hr (P.X p) (T.X q))]
  exact ht P T p q n h

private theorem restrictionInput_eq :
    restrictionInput k₀ l (extensionByZero k₀ l j) (upperStar k₀ l j) =
      nativeOpenTensorDescentInput k₀ l j := rfl

omit [IsOpenImmersion j]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
private theorem restriction_components_abstract
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    (e : ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) ⋙
          WeilSheaf.frobeniusPullback k₀ l U ≅
      WeilSheaf.frobeniusPullback k₀ l Z ⋙ ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
    (hR : R = Endofunctor.IsoAlgebra.mapOfNatIso e)
    (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      R.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R.obj N) (R.obj M))
    (hrho : ∀ M N, HEq ((rho M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)) :
    ∀ M N, HEq ((sheafRestrictionIso_abstract k₀ l j R e hR rho hrho).app (M, N))
      (rho M N) := fun _ _ ↦ HEq.rfl

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
private theorem native_restriction_components (s : NativeOpenTensorData k₀ l j) :
    ∀ M N, HEq ((sheafRestrictionIso k₀ l j s).app (M, N))
      (s.sheafRestriction M N) :=
  restriction_components_abstract k₀ l j (upperStar k₀ l j)
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l j (comp_over j _))
    (upperStar_eq_transport k₀ l j) s.sheafRestriction s.restriction_forget

-- Replace the native input by the abstract one before the assembly.
private theorem restrictionAbstract_of_eq
    (E : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [E.Additive] [R.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [E.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    [PreservesColimitsOfSize.{0, 0} R]
    (r : nativeOpenSheafTensor k₀ l Z ⋙ R ≅ R.prod R ⋙ nativeOpenSheafTensor k₀ l U)
    (hR : ∀ T, NativeIsKFlat k₀ l Z T →
      NativeIsKFlat k₀ l U ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (c : OpenTensorDescentInput (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (hc : restrictionInput k₀ l E R = c) (m : OpenTensorDescentModels c)
    (hA : HEq m.modelA (nativeOpenTensorModel k₀ l U))
    (hB : HEq m.modelB (nativeOpenTensorModel k₀ l Z))
    (hiA : HEq m.iA (nativeOpenTensorInsertion k₀ l U))
    (hiB : HEq m.iB (nativeOpenTensorInsertion k₀ l Z))
    (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      R.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R.obj N) (R.obj M))
    (hrr : ∀ M N, HEq (r.app (M, N)) (rho M N))
    (hr : HEq m.sheafRestriction rho) :
    Nonempty (OpenTensorRestrictionDescentData c m) := by
  subst hc
  exact restrictionAbstract k₀ l E R r hR m hA hB hiA hiB (fun M N ↦ by
    rw [eq_of_heq hr]
    exact (hrr M N).symm)

end

/-- Totalize the balanced restriction comparison and descend it to the derived category.

Source: Stacks Project, sites-cohomology.tex, Lemma pullback-tensor-product,
K-flat resolutions (Tag 06YS), and homology.tex, associated simple complex (Tag 012Z).
(blueprint: lem-sf-native-open-tensor-restriction-descent)

Proof: use the supplied representative models, summand insertions and sheaf
comparisons. The six equalities in hm identify each with the actual native
function, so all the native model naturality and sheaf-map properties transfer.
The preservation field is the given restriction property of s.

Then s.restriction_forget identifies the underlying map with the canonical
balanced pullback tensor comparison. That comparison is natural in both sheaves;
faithfulness of forgetting Frobenius proves the same naturality for the specified
Weil map. Restriction preserves coproducts and is additive, so apply these maps
and their inverses in every bidegree and sum over p+q=n. Naturality with the two
differentials, including the sign (-1)^p on the second one, gives a chain
isomorphism. Its composite with the image of each actual insertion is the given
sheaf map followed by the target insertion, yielding the first conclusion.
Use the flat-term equivariant K-flat resolutions on the twisted action site.
The hypothesis s.restriction_kflat keeps restriction inside the resolving
subcategory. On pairs of representatives compose inverse native tensor models,
Q of the total comparison, and the exact-derived restriction factors, obtaining
an isomorphism between the restrictions of the two derived bifunctors.
The models are natural by nativeDerivedTensor_models.choose_spec. Fully faithful
restriction to the resolving representatives descends this comparison and its
inverse, including naturality, to all derived inputs. Cancelling the model
isomorphisms gives exactly OpenTensorRestrictionNormalization. This constructs
rho rather than asserting that an arbitrary isomorphism has the normalization.
Retain the same comparison with exactly the native functor types and its
heterogeneous equality to the generic comparison.
The zero and empty cases use the same coproduct maps. -/
theorem native_open_tensor_restriction_descent (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m) :
    Nonempty (NativeOpenTensorRestrictionDescentData k₀ l j s m) := by
  have : (upperStar k₀ l j).IsLeftAdjoint :=
    (upperStarLowerStarAdjunction k₀ l j).isLeftAdjoint
  obtain ⟨d⟩ := restrictionAbstract_of_eq k₀ l (extensionByZero k₀ l j) (upperStar k₀ l j)
    (sheafRestrictionIso k₀ l j s) s.restriction_kflat (nativeOpenTensorDescentInput k₀ l j)
    (restrictionInput_eq k₀ l j) m hm.modelA hm.modelB hm.iA hm.iB s.sheafRestriction
    (native_restriction_components k₀ l j s) hm.sheafRestriction
  exact ⟨{ component := d, compatible := hm, rho := d.rho, rho_compatible := HEq.rfl }⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
