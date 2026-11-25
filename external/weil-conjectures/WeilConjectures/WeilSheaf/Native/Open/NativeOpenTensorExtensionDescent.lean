/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorSheafComparisons
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenSheafProjectionTensor
import WeilConjectures.SixFunctors.NativeExtensionDescentProof.NativeOpenTensorTotalComparison
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorCanonicalData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorFullKFlatLocalization
import WeilConjectures.SixFunctors.NativeExtensionDescentProof.NativeOpenTensorDerivedRepresentative

/-! # Normalized native open tensor extension descent

Source: Stacks 0GL1, 06YN and 012Z; native open tensor proof steps 3--6.
(blueprint: lem-sf-native-open-tensor-extension-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero
  AlgebraicGeometry.ProEtaleWeilSheaf.upperStar
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorTotal
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeIsKFlat
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorModel
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorInsertion

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace NativeExtensionDescentProof

private theorem sheafComparison
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    (E : A ⥤ B) (R : B ⥤ A) (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B)
    (adj : E ⊣ R)
    (r : Functor.uncurry.obj G ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj F)
    (g : ∀ M N, (G.obj (E.obj M)).obj N ≅ E.obj ((F.obj M).obj (R.obj N)))
    (hg : ∀ M N, adj.homEquiv _ _ (g M N).inv =
      (F.map (adj.unit.app M)).app (R.obj N) ≫ r.inv.app (E.obj M, N)) :
    ∃ e : E.prod (𝟭 _) ⋙ Functor.uncurry.obj G ≅
      (𝟭 _).prod R ⋙ Functor.uncurry.obj F ⋙ E,
      ∀ M N, e.app (M, N) = g M N := by
  let δ := NativeOpenProjectionProof.restrictionCurried F G r
  let p := adj.projectionMap R F G δ.hom
  have hp (M : A) (N : B) : (p.app M).app N = (g M N).inv := by
    rw [Adjunction.projectionMap_app_app]
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact (hg M N).symm
  have hi (M : A) (N : B) : IsIso ((p.app M).app N) := by
    rw [hp]
    infer_instance
  have (M : A) : IsIso (p.app M) := NatIso.isIso_of_isIso_app _
  have : IsIso p := NatIso.isIso_of_isIso_app _
  let q := Functor.uncurry.mapIso (asIso p)
  let e : E.prod (𝟭 _) ⋙ Functor.uncurry.obj G ≅
      (𝟭 _).prod R ⋙ Functor.uncurry.obj F ⋙ E :=
    NatIso.ofComponents (fun MN ↦ (q.app MN).symm) (by
      intro MN MN' fg
      have h := q.inv.naturality fg
      dsimp [Functor.whiskeringLeft₂, Functor.postcompose₂] at h
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.prod_map, Functor.prod_obj,
        Functor.id_map, Functor.id_obj, Functor.uncurry_obj_map,
        Iso.app_hom, Iso.symm_hom, Iso.app_inv,
        Functor.map_comp, Category.assoc] using h)
  refine ⟨e, fun M N ↦ ?_⟩
  apply Iso.ext_inv
  exact hp M N

-- Transport the insertion equation before specializing to the large native operations.
private theorem totalWithInsertions
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [Abelian B] [HasCountableCoproducts A] [HasCountableCoproducts B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    [PreservesColimitsOfSize.{0, 0} E]
    (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B)
    [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [∀ M, (G.obj M).PreservesZeroMorphisms]
    (SA : A → A → A) (SB : B → B → B)
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA : ∀ (P T : CochainComplex A ℤ) (p q n : ℤ), p + q = n →
      (SA (P.X p) (T.X q) ⟶ ((TA.obj P).obj T).X n))
    (iB : ∀ (P T : CochainComplex B ℤ) (p q n : ℤ), p + q = n →
      (SB (P.X p) (T.X q) ⟶ ((TB.obj P).obj T).X n))
    (hSA : SA = fun M N ↦ (F.obj M).obj N)
    (hSB : SB = fun M N ↦ (G.obj M).obj N)
    (hTA : TA = F.map₂CochainComplex) (hTB : TB = G.map₂CochainComplex)
    (hiA : HEq iA (fun (P T : CochainComplex A ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T F (.up ℤ) p q n h))
    (hiB : HEq iB (fun (P T : CochainComplex B ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T G (.up ℤ) p q n h))
    (g : E.prod (𝟭 _) ⋙ Functor.uncurry.obj G ≅
      (𝟭 _).prod R ⋙ Functor.uncurry.obj F ⋙ E)
    (g0 : ∀ M N, SB (E.obj M) N ≅ E.obj (SA M (R.obj N)))
    (hg : ∀ M N, HEq (g.app (M, N)) (g0 M N)) :
    ∃ e : (E.mapHomologicalComplex (.up ℤ)).prod (𝟭 _) ⋙ Functor.uncurry.obj TB ≅
        (𝟭 _).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj TA ⋙ E.mapHomologicalComplex (.up ℤ),
      ∀ P T (p q n : ℤ) (h : p + q = n),
        iB ((E.mapHomologicalComplex (.up ℤ)).obj P) T p q n h ≫
            (e.app (P, T)).hom.f n =
          (g0 (P.X p) (T.X q)).hom ≫
            E.map (iA P ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n h) := by
  subst SA
  subst SB
  subst TA
  subst TB
  have hiA := eq_of_heq hiA
  subst iA
  have hiB := eq_of_heq hiB
  subst iB
  obtain ⟨e, he⟩ := native_open_tensor_total_comparison E R F G g
  refine ⟨e, fun P T p q n h ↦ ?_⟩
  have hh := he P T p q n h
  have hg' := eq_of_heq (hg (P.X p) (T.X q))
  rw [hg'] at hh
  exact hh

end NativeExtensionDescentProof

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

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
private theorem sheafAbstract
    (E : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    (adj : E ⊣ R)
    (r : nativeOpenSheafTensor k₀ l Z ⋙ R ≅
      R.prod R ⋙ nativeOpenSheafTensor k₀ l U)
    (rho : ∀ M N, R.obj (tensor k₀ l Z N M) ≅
      tensor k₀ l U (R.obj N) (R.obj M))
    (hr : ∀ M N, HEq (r.app (M, N)) (rho M N))
    (g : ∀ M N, tensor k₀ l Z N (E.obj M) ≅
      E.obj (tensor k₀ l U (R.obj N) M))
    (hg : ∀ M N, HEq (adj.homEquiv _ _ (g M N).inv)
      ((tensorFunctor k₀ l U (R.obj N)).map (adj.unit.app M) ≫
        (rho (E.obj M) N).inv)) :
    ∃ e : E.prod (𝟭 _) ⋙ nativeOpenSheafTensor k₀ l Z ≅
        (𝟭 _).prod R ⋙ nativeOpenSheafTensor k₀ l U ⋙ E,
      ∀ M N, e.app (M, N) = g M N := by
  exact NativeExtensionDescentProof.sheafComparison E R
    (nativeTensorBifunctor k₀ l U).flip (nativeTensorBifunctor k₀ l Z).flip
    adj r g (by
      intro M N
      have hh := eq_of_heq (hg M N)
      have hr' := eq_of_heq (hr (E.obj M) N)
      rw [← hr'] at hh
      exact hh)

-- Keep exact operations as parameters while comparing their tensor components.
private def inputAbstract
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

private def modelsAbstract
    (E : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [E.Additive] [R.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [E.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    (g : ∀ M N, tensor k₀ l Z N (E.obj M) ≅ E.obj (tensor k₀ l U (R.obj N) M))
    (r : ∀ M N, R.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R.obj N) (R.obj M)) :
    OpenTensorDescentModels (inputAbstract k₀ l E R) :=
  { modelA := nativeOpenTensorModel k₀ l U
    modelB := nativeOpenTensorModel k₀ l Z
    iA := nativeOpenTensorInsertion k₀ l U
    iB := nativeOpenTensorInsertion k₀ l Z
    sheafGamma := g
    sheafRestriction := r }

private theorem modelsAbstract_compatible
    (E : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [E.Additive] [R.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [E.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    (g : ∀ M N, tensor k₀ l Z N (E.obj M) ≅ E.obj (tensor k₀ l U (R.obj N) M))
    (r : ∀ M N, R.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R.obj N) (R.obj M)) :
    let m := modelsAbstract k₀ l E R g r
    HEq m.modelA (nativeOpenTensorModel k₀ l U) ∧
    HEq m.modelB (nativeOpenTensorModel k₀ l Z) ∧
    HEq m.iA (nativeOpenTensorInsertion k₀ l U) ∧
    HEq m.iB (nativeOpenTensorInsertion k₀ l Z) ∧
    HEq m.sheafGamma g ∧ HEq m.sheafRestriction r :=
  ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

private theorem input_eq :
    inputAbstract k₀ l (extensionByZero k₀ l j) (upperStar k₀ l j) =
      nativeOpenTensorDescentInput k₀ l j := rfl

omit [Fact (ringChar k₀ ≠ l)]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
private theorem models_cast_compatible
    (c c' : OpenTensorDescentInput (ProEtaleWeilSheaf k₀ l U)
      (ProEtaleWeilSheaf k₀ l Z)) (h : c = c') (m : OpenTensorDescentModels c) :
    let m' : OpenTensorDescentModels c' := h ▸ m
    HEq m'.modelA m.modelA ∧ HEq m'.modelB m.modelB ∧
    HEq m'.iA m.iA ∧ HEq m'.iB m.iB ∧
    HEq m'.sheafGamma m.sheafGamma ∧ HEq m'.sheafRestriction m.sheafRestriction := by
  cases h
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

private def nativeModels (s : NativeOpenTensorData k₀ l j) :
    OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j) :=
  input_eq k₀ l j ▸ modelsAbstract k₀ l (extensionByZero k₀ l j) (upperStar k₀ l j)
    s.sheafGamma s.sheafRestriction

private theorem nativeModels_compatible (s : NativeOpenTensorData k₀ l j) :
    NativeOpenTensorModelsCompatibility k₀ l j s (nativeModels k₀ l j s) := by
  have h := modelsAbstract_compatible k₀ l (extensionByZero k₀ l j)
    (upperStar k₀ l j) s.sheafGamma s.sheafRestriction
  have hc := models_cast_compatible k₀ l _ _ (input_eq k₀ l j)
    (modelsAbstract k₀ l (extensionByZero k₀ l j) (upperStar k₀ l j)
      s.sheafGamma s.sheafRestriction)
  exact ⟨hc.1.trans h.1, hc.2.1.trans h.2.1, hc.2.2.1.trans h.2.2.1,
    hc.2.2.2.1.trans h.2.2.2.1, hc.2.2.2.2.1.trans h.2.2.2.2.1,
    hc.2.2.2.2.2.trans h.2.2.2.2.2⟩

private def castExtension
    {c c' : OpenTensorDescentInput (ProEtaleWeilSheaf k₀ l U)
      (ProEtaleWeilSheaf k₀ l Z)} (h : c = c') {m : OpenTensorDescentModels c}
    (d : OpenTensorExtensionDescentData c m) :
    OpenTensorExtensionDescentData c' (h ▸ m) := by
  cases h
  exact d

omit [Fact (ringChar k₀ ≠ l)]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] in
private theorem castExtension_gamma
    {c c' : OpenTensorDescentInput (ProEtaleWeilSheaf k₀ l U)
      (ProEtaleWeilSheaf k₀ l Z)} (h : c = c') {m : OpenTensorDescentModels c}
    (d : OpenTensorExtensionDescentData c m) :
    HEq (castExtension k₀ l h d).gamma d.gamma := by
  cases h
  exact HEq.rfl

set_option backward.isDefEq.respectTransparency false in
-- This assembly combines totalization, two localizations and the fixed-model square.
private theorem extensionAbstract
    (E : ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l Z)
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    [E.Additive] [R.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [E.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    (adj : E ⊣ R)
    (r : nativeOpenSheafTensor k₀ l Z ⋙ R ≅
      R.prod R ⋙ nativeOpenSheafTensor k₀ l U)
    (rho : ∀ M N, R.obj (tensor k₀ l Z N M) ≅
      tensor k₀ l U (R.obj N) (R.obj M))
    (hr : ∀ M N, HEq (r.app (M, N)) (rho M N))
    (sg : ∀ M N, tensor k₀ l Z N (E.obj M) ≅
      E.obj (tensor k₀ l U (R.obj N) M))
    (hs : ∀ M N, HEq (adj.homEquiv _ _ (sg M N).inv)
      ((tensorFunctor k₀ l U (R.obj N)).map (adj.unit.app M) ≫
        (rho (E.obj M) N).inv))
    (hE : ∀ P, NativeIsKFlat k₀ l U P →
      NativeIsKFlat k₀ l Z ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hR : ∀ T, NativeIsKFlat k₀ l Z T →
      NativeIsKFlat k₀ l U ((R.mapHomologicalComplex (.up ℤ)).obj T)) :
    ∃ (gamma : E.mapDerivedCategory.prod (𝟭 _) ⋙ nativeDerivedTensor k₀ l Z ≅
        (𝟭 _).prod R.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l U ⋙
          E.mapDerivedCategory)
      (d : OpenTensorExtensionDescentData (inputAbstract k₀ l E R)
        (modelsAbstract k₀ l E R sg rho)),
      HEq d.gamma gamma := by
  have : E.IsLeftAdjoint := ⟨R, ⟨adj⟩⟩
  obtain ⟨g, hg⟩ := sheafAbstract k₀ l E R adj r rho hr sg hs
  have : (nativeTensorBifunctor k₀ l U).flip.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : ∀ M, ((nativeTensorBifunctor k₀ l U).flip.obj M).PreservesZeroMorphisms :=
    fun M ↦ Functor.preservesZeroMorphisms_of_additive _
  have : (nativeTensorBifunctor k₀ l Z).flip.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : ∀ M, ((nativeTensorBifunctor k₀ l Z).flip.obj M).PreservesZeroMorphisms :=
    fun M ↦ Functor.preservesZeroMorphisms_of_additive _
  have hA := native_open_tensor_canonical_data k₀ l U
  have hB := native_open_tensor_canonical_data k₀ l Z
  obtain ⟨t', ht⟩ := NativeExtensionDescentProof.totalWithInsertions E R
    (nativeTensorBifunctor k₀ l U).flip (nativeTensorBifunctor k₀ l Z).flip
    (fun M N ↦ tensor k₀ l U N M) (fun M N ↦ tensor k₀ l Z N M)
    (nativeTensorTotal k₀ l U) (nativeTensorTotal k₀ l Z)
    (nativeOpenTensorInsertion k₀ l U) (nativeOpenTensorInsertion k₀ l Z)
    hA.1 hB.1 hA.2.2.1 hB.2.2.1 hA.2.2.2 hB.2.2.2 g sg (fun M N ↦ heq_of_eq (hg M N))
  let c := inputAbstract k₀ l E R
  let m := modelsAbstract k₀ l E R sg rho
  have : ((ObjectProperty.ι c.flatA) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage (ObjectProperty.ι c.flatA)) :=
    native_open_tensor_full_kflat_localization k₀ l U
  have : ((ObjectProperty.ι c.flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage (ObjectProperty.ι c.flatB)) :=
    native_open_tensor_full_kflat_localization k₀ l Z
  obtain ⟨gamma, hm⟩ :=
    NativeExtensionDescentProof.native_open_tensor_derived_representative c m hE hR
    (by
      intro P P' T T' hP hP' hT hT' f g
      dsimp only [c, inputAbstract, m, modelsAbstract]
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l U).choose_spec.1
        P P' T T' hP hP' hT hT' f g)
    (by
      intro P P' T T' hP hP' hT hT' f g
      dsimp only [c, inputAbstract, m, modelsAbstract]
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l Z).choose_spec.1
        P P' T T' hP hP' hT hT' f g) t'
  let d : OpenTensorExtensionDescentData (inputAbstract k₀ l E R)
      (modelsAbstract k₀ l E R sg rho) := {
    hE := hE
    hR := hR
    total := fun P T ↦ t'.app (P, T)
    gamma := gamma
    summands := by
      intro P T p q n h
      have hι := ht P T p q n h
      change nativeOpenTensorInsertion k₀ l Z
          ((E.mapHomologicalComplex (.up ℤ)).obj P) T p q n h ≫ (t'.app (P, T)).hom.f n =
        (sg (P.X p) (T.X q)).hom ≫
          E.map (nativeOpenTensorInsertion k₀ l U P
            ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n h)
      exact hι
    model := hm }
  exact ⟨d.gamma, d, HEq.rfl⟩

private theorem nativePacket (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hc : NativeOpenTensorModelsCompatibility k₀ l j s m)
    (g : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j)
    (d : OpenTensorExtensionDescentData (nativeOpenTensorDescentInput k₀ l j) m)
    (hd : HEq d.gamma g) : Nonempty (NativeOpenTensorExtensionDescentData k₀ l j s) :=
  ⟨{ models := m, component := d, compatible := hc, gamma := g, gamma_compatible := hd }⟩

/-- Totalize the specified sheaf projection map and descend that map to the derived category.

Source: Stacks Project, sites-cohomology.tex, Lemma j-shriek-and-tensor (Tag 0GL1),
K-flat resolutions (Tag 06YS), and homology.tex, associated simple complex (Tag 012Z).
(blueprint: lem-sf-native-open-tensor-extension-descent)

Proof: first record the actual native representative models, summand insertions
and the sheaf comparisons of s. Transport across the unique zero-morphism
structures if necessary, retaining heterogeneous equality to each native
function. The preservation fields are the given properties of s.

Then the inverse-unit equation in s identifies the inverse sheaf comparison
with the adjoint transpose of tensor of the unit followed by inverse restriction.
The underlying restriction map is the balanced pullback tensor comparison, so it
is natural. Naturality of the adjunction and of tensor then gives naturality of
the sheaf projection map in both arguments. Apply this map and its inverse in
each bidegree (p,q). Exact additive extension preserves the countable coproducts
of the total complex, and the degree-zero comparison commutes with both signed
differentials. The resulting chain isomorphism has precisely the displayed
summand formula. Use equivariant K-flat resolutions, constructed on the twisted
action site, to restrict the localized calculation to resolving representatives.
Extension and restriction preserve these representatives by s.extension_kflat
and s.restriction_kflat. Compose Q of the chain map with the inverse source model,
the target model, and the exact-derived factorization isomorphisms. Naturality of
nativeOpenTensorModel follows from nativeDerivedTensor_models.choose_spec.
Fully faithful restriction to the resolving representatives descends this natural
isomorphism to the ambient derived categories. Its representative square is the
second conclusion. There is no choice of a previously fixed derived comparison;
the descent constructs gamma. Retain this same comparison with exactly the
native functor types and its heterogeneous equality to the generic comparison.
Zero complexes and the empty open have the same construction, with zero summands. -/
theorem native_open_tensor_extension_descent (s : NativeOpenTensorData k₀ l j) :
    Nonempty (NativeOpenTensorExtensionDescentData k₀ l j s) := by
  obtain ⟨gamma, d, hd⟩ := extensionAbstract k₀ l
    (extensionByZero k₀ l j) (upperStar k₀ l j) s.adj
    (sheafRestrictionIso k₀ l j s) s.sheafRestriction
    (native_restriction_components k₀ l j s) s.sheafGamma s.sheaf_inverse
    s.extension_kflat s.restriction_kflat
  exact nativePacket k₀ l j s (nativeModels k₀ l j s)
    (nativeModels_compatible k₀ l j s) gamma (castExtension k₀ l (input_eq k₀ l j) d)
    ((castExtension_gamma k₀ l (input_eq k₀ l j) d).trans hd)

end AlgebraicGeometry.ProEtaleWeilSheaf
