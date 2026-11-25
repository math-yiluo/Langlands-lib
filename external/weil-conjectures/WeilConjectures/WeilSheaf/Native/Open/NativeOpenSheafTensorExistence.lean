/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenRestrictionTensor
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenSheafProjectionTensor

/-! # The native sheaf open tensor calculation

Source: Stacks 0E8I and 03DJ; equivariant refinement, steps 1--4 of
lem-sf-native-open-derived-tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorBifunctor

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

private theorem quasiIso_square_iff
    {C : Type*} [Category C] [Preadditive C] [CategoryWithHomology C]
    {K L K' L' : CochainComplex C ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ≅ K') (b : L ≅ L') (h : f ≫ b.hom = a.hom ≫ g) :
    QuasiIso f ↔ QuasiIso g := by
  rw [← quasiIso_iff_comp_right f b.hom, h, quasiIso_iff_comp_left a.hom g]

private abbrev firstTest {C : Type*} [Category C] [Preadditive C] [CategoryWithHomology C]
    (H : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (P : CochainComplex C ℤ) : Prop :=
  ∀ {Q Q' : CochainComplex C ℤ} (s : Q ⟶ Q'), QuasiIso s → QuasiIso ((H.obj P).map s)

private abbrev secondTest {C : Type*} [Category C] [Preadditive C] [CategoryWithHomology C]
    (H : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (P : CochainComplex C ℤ) : Prop :=
  ∀ {Q Q' : CochainComplex C ℤ} (s : Q ⟶ Q'), QuasiIso s → QuasiIso ((H.map s).app P)

private theorem secondTest_flip_iff
    {A : Type*} [Category A] [Preadditive A] [CategoryWithHomology A]
    [HasCountableCoproducts A]
    (H : A ⥤ A ⥤ A) [H.PreservesZeroMorphisms]
    [∀ M, (H.obj M).PreservesZeroMorphisms] (P : CochainComplex A ℤ) :
    secondTest H.map₂CochainComplex P ↔ firstTest H.flip.map₂CochainComplex P := by
  have h {Q Q' : CochainComplex A ℤ} (f : Q ⟶ Q') :
      QuasiIso ((H.map₂CochainComplex.map f).app P) ↔
        QuasiIso ((H.flip.map₂CochainComplex.obj P).map f) := by
    exact (quasiIso_square_iff _ _
      (HomologicalComplex.mapBifunctorFlipIso Q P H (.up ℤ))
      (HomologicalComplex.mapBifunctorFlipIso Q' P H (.up ℤ))
      (HomologicalComplex.mapBifunctorFlipIso_hom_naturality f (𝟙 P) H (.up ℤ))).symm
  constructor
  · intro hP Q Q' f hf
    exact h f |>.mp (hP f hf)
  · intro hP Q Q' f hf
    exact h f |>.mpr (hP f hf)

private theorem firstTest_transfer
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [CategoryWithHomology A] [CategoryWithHomology B]
    [HasCountableCoproducts A] [HasCountableCoproducts B]
    (E : A ⥤ B) [E.Additive] [E.PreservesHomology] [E.ReflectsIsomorphisms]
    [PreservesColimitsOfSize.{0, 0} E]
    (R : B ⥤ A) [R.Additive] [R.PreservesHomology]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    (e : ∀ (M : A) (N : B),
      E.obj ((H.obj M).obj (R.obj N)) ≅ (H'.obj (E.obj M)).obj N)
    (hn : ∀ {M M' : A} {N N' : B} (a : M ⟶ M') (b : N ⟶ N'),
      E.map ((H.map a).app (R.obj N) ≫ (H.obj M').map (R.map b)) ≫
          (e M' N').hom =
        (e M N).hom ≫ (H'.map (E.map a)).app N ≫ (H'.obj (E.obj M')).map b) :
    (∀ P, firstTest H.map₂CochainComplex P →
      firstTest H'.map₂CochainComplex ((E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ T, secondTest H'.map₂CochainComplex T →
      secondTest H.map₂CochainComplex ((R.mapHomologicalComplex (.up ℤ)).obj T)) := by
  let F := H ⋙ (Functor.whiskeringLeft B A A).obj R
  have : F.PreservesZeroMorphisms := SheafOfModules.precompose_preservesZero H R
  have : ∀ M, (F.obj M).PreservesZeroMorphisms :=
    SheafOfModules.precompose_obj_preservesZero H R
  have : ∀ (P : CochainComplex A ℤ) (T : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P T F (.up ℤ) :=
    SheafOfModules.precompose_hasTotal H R
  let tau : (Functor.postcompose₂.obj E).obj F ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H' :=
    SheafOfModules.bifunctorIsoOfComponents _ _ e (by
      intro M M' N N' a b
      change E.map ((H.map a).app (R.obj N)) ≫
          E.map ((H.obj M').map (R.map b)) ≫ (e M' N').hom = _
      rw [← Category.assoc, ← E.map_comp]
      exact hn a b)
  let ec := E.mapHomologicalComplex (.up ℤ)
  let rc := R.mapHomologicalComplex (.up ℤ)
  let gamma := SheafOfModules.comparisonPrecomposeIso E R H H' tau
  constructor
  · intro P hP Q Q' f hf
    have := hf
    have hr : QuasiIso (rc.map f) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology f R
    have ht := hP (rc.map f) hr
    have := ht
    have he : QuasiIso (ec.map ((H.map₂CochainComplex.obj P).map (rc.map f))) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology _ E
    apply (quasiIso_square_iff _ _ (gamma P Q) (gamma P Q') ?_).mp he
    have hn := SheafOfModules.comparisonPrecomposeIso_map₂_natural E R H H' tau (𝟙 P) f
    erw [H.map₂CochainComplex.map_id, NatTrans.id_app, Category.id_comp,
      (E.mapHomologicalComplex (.up ℤ)).map_id, H'.map₂CochainComplex.map_id,
      NatTrans.id_app, Category.id_comp] at hn
    exact hn
  · intro T hT P P' f hf
    have := hf
    have he : QuasiIso (ec.map f) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology f E
    have ht := hT (ec.map f) he
    have h : QuasiIso (ec.map ((H.map₂CochainComplex.map f).app (rc.obj T))) := by
      apply (quasiIso_square_iff _ _ (gamma P T) (gamma P' T) ?_).mpr ht
      have hn := SheafOfModules.comparisonPrecomposeIso_map₂_natural E R H H' tau f (𝟙 T)
      erw [(R.mapHomologicalComplex (.up ℤ)).map_id,
        (H.map₂CochainComplex.obj P').map_id, Category.comp_id,
        (H'.map₂CochainComplex.obj _).map_id, Category.comp_id] at hn
      exact hn
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ E).mp h

private theorem firstTest_transfer_natural
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [CategoryWithHomology A] [CategoryWithHomology B]
    [HasCountableCoproducts A] [HasCountableCoproducts B]
    (E : A ⥤ B) [E.Additive] [E.PreservesHomology] [E.ReflectsIsomorphisms]
    [PreservesColimitsOfSize.{0, 0} E]
    (R : B ⥤ A) [R.Additive] [R.PreservesHomology]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    (gamma : E.prod (𝟭 B) ⋙ Functor.uncurry.obj H' ≅
      (𝟭 A).prod R ⋙ Functor.uncurry.obj H ⋙ E) :
    (∀ P, firstTest H.map₂CochainComplex P →
      firstTest H'.map₂CochainComplex ((E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ T, secondTest H'.map₂CochainComplex T →
      secondTest H.map₂CochainComplex ((R.mapHomologicalComplex (.up ℤ)).obj T)) := by
  apply firstTest_transfer E R H H' (fun M N ↦ (gamma.app (M, N)).symm)
  intro M M' N N' a b
  simpa only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    Functor.comp_map, Functor.prod_map, Functor.id_map,
    Functor.uncurry_obj_map, Iso.symm_hom, Iso.app_inv, Category.assoc] using
      gamma.inv.naturality (Prod.mkHom a b)

private theorem firstTest_transfer_natural_right
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [CategoryWithHomology A] [CategoryWithHomology B]
    [HasCountableCoproducts A] [HasCountableCoproducts B]
    (E : A ⥤ B) [E.Additive] [E.PreservesHomology] [E.ReflectsIsomorphisms]
    [PreservesColimitsOfSize.{0, 0} E]
    (R : B ⥤ A) [R.Additive] [R.PreservesHomology]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    (gamma : (𝟭 B).prod E ⋙ Functor.uncurry.obj H' ≅
      R.prod (𝟭 A) ⋙ Functor.uncurry.obj H ⋙ E) :
    (∀ P, firstTest H.flip.map₂CochainComplex P →
      firstTest H'.flip.map₂CochainComplex ((E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ T, secondTest H'.flip.map₂CochainComplex T →
      secondTest H.flip.map₂CochainComplex ((R.mapHomologicalComplex (.up ℤ)).obj T)) := by
  apply firstTest_transfer E R H.flip H'.flip (fun M N ↦ (gamma.app (N, M)).symm)
  intro M M' N N' a b
  have h := gamma.inv.naturality (Prod.mkHom b a)
  change E.map ((H.map (R.map b)).app M ≫ (H.obj (R.obj N')).map a) ≫
      (gamma.inv.app (N', M')) = gamma.inv.app (N, M) ≫
        ((H'.map b).app (E.obj M) ≫ (H'.obj N').map (E.map a)) at h
  rw [← (H.map (R.map b)).naturality a,
    ← (H'.map b).naturality (E.map a)] at h
  simpa only [Functor.flip_map_app, Functor.flip_obj_map,
    Iso.symm_hom, Iso.app_inv, Category.assoc] using h

private theorem twoSidedTest_transfer
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [CategoryWithHomology A] [CategoryWithHomology B]
    [HasCountableCoproducts A] [HasCountableCoproducts B]
    (E : A ⥤ B) [E.Additive] [E.PreservesHomology] [E.ReflectsIsomorphisms]
    [PreservesColimitsOfSize.{0, 0} E]
    (R : B ⥤ A) [R.Additive] [R.PreservesHomology]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    (gamma : E.prod (𝟭 B) ⋙ Functor.uncurry.obj H' ≅
      (𝟭 A).prod R ⋙ Functor.uncurry.obj H ⋙ E)
    (gammaRight : (𝟭 B).prod E ⋙ Functor.uncurry.obj H' ≅
      R.prod (𝟭 A) ⋙ Functor.uncurry.obj H ⋙ E) :
    (∀ P, (firstTest H.map₂CochainComplex P ∧ secondTest H.map₂CochainComplex P) →
      firstTest H'.map₂CochainComplex ((E.mapHomologicalComplex (.up ℤ)).obj P) ∧
        secondTest H'.map₂CochainComplex ((E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ T, (firstTest H'.map₂CochainComplex T ∧ secondTest H'.map₂CochainComplex T) →
      firstTest H.map₂CochainComplex ((R.mapHomologicalComplex (.up ℤ)).obj T) ∧
        secondTest H.map₂CochainComplex ((R.mapHomologicalComplex (.up ℤ)).obj T)) := by
  have ht := firstTest_transfer_natural E R H H' gamma
  have ht' := firstTest_transfer_natural_right E R H H' gammaRight
  constructor
  · intro P hP
    refine ⟨ht.1 P hP.1, ?_⟩
    exact (secondTest_flip_iff H' _).mpr
      (ht'.1 P ((secondTest_flip_iff H P).mp hP.2))
  · intro T hT
    refine ⟨?_, ht.2 T hT.2⟩
    exact (secondTest_flip_iff H.flip _).mp
      (ht'.2 T ((secondTest_flip_iff H'.flip T).mpr hT.1))

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

private def openAdjunction : extensionByZero k₀ l j ⊣ upperStar k₀ l j := by
  apply Endofunctor.IsoAlgebra.mapOfNatIsoLeftAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l _)
    (ProEtale.adicUpperStarLowerStarAdjunction l _)
    _ _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
  intro K
  exact ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    _ K

omit [Fact (ringChar k₀ ≠ l)] in
private theorem openAdjunction_unit (M : ProEtaleWeilSheaf k₀ l U) :
    ((openAdjunction k₀ l j).unit.app M).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier := by
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
private theorem openAdjunction_counit (N : ProEtaleWeilSheaf k₀ l Z) :
    ((openAdjunction k₀ l j).counit.app N).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier := by
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
private theorem openAdjunction_unit_iso : IsIso (openAdjunction k₀ l j).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)
  have : IsIso (F.map ((openAdjunction k₀ l j).unit.app M)) := by
    change IsIso (((openAdjunction k₀ l j).unit.app M).hom.f)
    rw [openAdjunction_unit]
    infer_instance
  exact isIso_of_reflects_iso _ F

private theorem nativeIsKFlat_iff_tests
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    NativeIsKFlat k₀ l X P ↔
      firstTest (nativeTensorBifunctor k₀ l X).flip.map₂CochainComplex P ∧
        secondTest (nativeTensorBifunctor k₀ l X).flip.map₂CochainComplex P :=
  Iff.rfl

private theorem nativeKFlat_transfer
    (E : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    [E.Additive] [E.PreservesHomology] [E.ReflectsIsomorphisms]
    [PreservesColimitsOfSize.{0, 0} E]
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [R.Additive] [R.PreservesHomology]
    (gamma : E.prod (𝟭 (ProEtaleWeilSheaf k₀ l Z)) ⋙ nativeOpenSheafTensor k₀ l Z ≅
      (𝟭 (ProEtaleWeilSheaf k₀ l U)).prod R ⋙ nativeOpenSheafTensor k₀ l U ⋙ E)
    (gammaRight : (𝟭 (ProEtaleWeilSheaf k₀ l Z)).prod E ⋙ nativeOpenSheafTensor k₀ l Z ≅
      R.prod (𝟭 (ProEtaleWeilSheaf k₀ l U)) ⋙ nativeOpenSheafTensor k₀ l U ⋙ E) :
    (∀ P, NativeIsKFlat k₀ l U P → NativeIsKFlat k₀ l Z
      ((E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ T, NativeIsKFlat k₀ l Z T → NativeIsKFlat k₀ l U
      ((R.mapHomologicalComplex (.up ℤ)).obj T)) := by
  let H := (nativeTensorBifunctor k₀ l U).flip
  let H' := (nativeTensorBifunctor k₀ l Z).flip
  have ht := twoSidedTest_transfer E R H H' gamma gammaRight
  constructor
  · intro P hP
    apply (nativeIsKFlat_iff_tests k₀ l Z _).mpr
    exact ht.1 P ((nativeIsKFlat_iff_tests k₀ l U P).mp hP)
  · intro T hT
    apply (nativeIsKFlat_iff_tests k₀ l U _).mpr
    exact ht.2 T ((nativeIsKFlat_iff_tests k₀ l Z T).mp hT)

variable
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

attribute [local irreducible] NativeIsKFlat

set_option linter.unusedSectionVars false

/-- The normalized sheaf adjunction and balanced tensor comparisons, with
preservation of categorical two-sided K-flatness.

Source: Stacks 0E8I, 03DJ, 03D8; steps 1--4 of the native open tensor argument
(blueprint: lem-sf-native-open-sheaf-tensor-existence).

Proof: Identify the geometric open site with the slice. Its coefficient sheaf is
the restriction of the ambient coefficient sheaf: both are the same locally
finite coefficient functions. Lift the extension/restriction adjunction to Weil
sheaves. On local sections the unit is x maps to [x] and the counit is [x] maps
to x; Frobenius reindexes the same factoring objects, so both maps intertwine
the Weil structures. Invertibility of the lifted unit is proved separately in the assembling
theorem, using faithful conservative forgetting. The restriction/tensor comparison is
the balanced map taking x tensor y to x|U tensor y|U. The open tensor comparison
takes [x] tensor y to [x tensor y|U]. Its inverse is the transpose of tensoring
with the open unit, followed by inverse restriction/tensor comparison. Check
balancing, inverse identities, naturality, and Frobenius equivariance on pure
tensors. Apply these maps in each bidegree and take direct sums; both differential
composites on degree (p,q) are dx tensor y + (-1)^p x tensor dy. This gives the
natural chain comparison. For a K-flat P on the open, restrict an arbitrary
ambient quasi-isomorphism, tensor with P, and extend; exactness and the chain
comparison show that extension preserves K-flatness. For a K-flat ambient T,
extend a quasi-isomorphism on the open and tensor with T. The chain comparison
identifies this with extension of its tensor with restriction of T. Restrict
back, using the invertible open unit, to reflect the quasi-isomorphism. Symmetry
gives the other tensor variable in each test. Thus the recorded two-sided
categorical K-flat predicates are preserved; no boundedness or flat-term
assumption is imposed on these tests. -/
theorem native_open_sheaf_tensor_existence :
    ∃ (adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j)
      (sheafRestriction : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
        (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
          tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M))
      (sheafGamma : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
        tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) ≅
          (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M)),
      (∀ M, (adj.unit.app M).hom.f =
        (ProEtale.adicOpenImmersionLowerShriekAdjunction l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier) ∧
      (∀ N, (adj.counit.app N).hom.f =
        (ProEtale.adicOpenImmersionLowerShriekAdjunction l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier) ∧
      (∀ M N, HEq ((sheafRestriction M N).hom.hom.f)
        ((ProEtale.adicUpperStarTensorLeftIso l
          (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)) ∧
      (∀ M N, HEq (adj.homEquiv _ _ ((sheafGamma M N).inv))
        ((tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
          (sheafRestriction ((extensionByZero k₀ l j).obj M) N).inv)) ∧
      (∀ P, NativeIsKFlat k₀ l U P → NativeIsKFlat k₀ l Z
        (((extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ T, NativeIsKFlat k₀ l Z T → NativeIsKFlat k₀ l U
        (((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).obj T)) := by
  let adj := openAdjunction k₀ l j
  have hu := openAdjunction_unit k₀ l j
  have hc := openAdjunction_counit k₀ l j
  have : IsIso adj.unit := openAdjunction_unit_iso k₀ l j
  let E := extensionByZero k₀ l j
  let R := upperStar k₀ l j
  have : E.Full := adj.fullyFaithfulLOfIsIsoUnit.full
  have : E.Faithful := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have : E.IsLeftAdjoint := adj.isLeftAdjoint
  obtain ⟨rho, hrho⟩ := native_open_restriction_tensor k₀ l j
  obtain ⟨pointwiseGamma, hgamma, ⟨gamma⟩, ⟨gammaRight⟩⟩ :=
    native_open_sheaf_projection_tensor k₀ l j adj hu hc rho hrho
  have ht := nativeKFlat_transfer k₀ l E R gamma gammaRight
  exact ⟨adj, rho, pointwiseGamma, hu, hc, hrho, hgamma, ht.1, ht.2⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
