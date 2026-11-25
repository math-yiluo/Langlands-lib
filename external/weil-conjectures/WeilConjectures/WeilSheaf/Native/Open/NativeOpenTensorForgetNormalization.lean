/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorUnitNormalization
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorRestrictionForget
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryOpenTensorSupport

/-! # Forgetting normalization for the native open tensor

Source: Stacks 0GL1 and 0E8I, native open tensor proof step 8
(blueprint: new-lem-sf-native-open-tensor-forget-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
universe u a b d
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem openTensor_comp_two_ids
    {C D : Type a} [Category.{b} C] [Category.{b} D]
    (G : C ⥤ D) {X : C} {Y : D} (f : Y ⟶ G.obj X) :
    f ≫ 𝟙 (G.obj X) ≫ G.map (𝟙 X) = f := by
  simp only [Functor.map_id, Category.comp_id]

private def openTensor_unitSquare
    {A B A' B' : Type a} [Category.{b} A] [Category.{b} B]
    [Category.{b} A'] [Category.{b} B']
    {E : A ⥤ B} {R : B ⥤ A} {E' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : E ⊣ R) (adj' : E' ⊣ R') (FA : A ⥤ A') (FB : B ⥤ B')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R') : Prop :=
  ∀ X, FA.map (adj.unit.app X) ≫ eR.hom.app (E.obj X) ≫
    R'.map (eE.hom.app X) = adj'.unit.app (FA.obj X)

private theorem openTensor_forget_homEquiv
    {A B A' B' : Type a} [Category.{b} A] [Category.{b} B]
    [Category.{b} A'] [Category.{b} B']
    {E : A ⥤ B} {R : B ⥤ A} {E' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : E ⊣ R) (adj' : E' ⊣ R') (FA : A ⥤ A') (FB : B ⥤ B')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (hu : openTensor_unitSquare adj adj' FA FB eE eR)
    (X : A) (Y : B) (f : E.obj X ⟶ Y) :
    adj'.homEquiv _ _ (eE.inv.app X ≫ FB.map f) =
      FA.map (adj.homEquiv _ _ f) ≫ eR.hom.app Y := by
  rw [adj'.homEquiv_unit, ← hu X, adj.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R'.map_comp_assoc]
  rw [Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [Functor.map_id, Category.id_comp]
  exact congrArg (fun z ↦ FA.map (adj.unit.app X) ≫ z) (eR.hom.naturality f).symm

private theorem openTensor_forget_of_unit
    {A B A' B' : Type a} [Category.{b} A] [Category.{b} B]
    [Category.{b} A'] [Category.{b} B']
    {E : A ⥤ B} {R : B ⥤ A} {E' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : E ⊣ R) (adj' : E' ⊣ R') (FA : A ⥤ A') (FB : B ⥤ B')
    {TA : A × A ⥤ A} {TB : B × B ⥤ B}
    {TA' : A' × A' ⥤ A'} {TB' : B' × B' ⥤ B'}
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (tA : TA ⋙ FA ≅ FA.prod FA ⋙ TA')
    (tB : TB ⋙ FB ≅ FB.prod FB ⋙ TB')
    (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (rho' : TB' ⋙ R' ≅ R'.prod R' ⋙ TA')
    (gamma : E.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod R ⋙ TA ⋙ E)
    (gamma' : E'.prod (𝟭 B') ⋙ TB' ≅ (𝟭 A').prod R' ⋙ TA' ⋙ E')
    (hu : openTensor_unitSquare adj adj' FA FB eE eR)
    (hr : ∀ M N,
      FA.map (rho.hom.app (M, N)) ≫ tA.hom.app (R.obj M, R.obj N) ≫
        TA'.map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) =
      eR.hom.app (TB.obj (M, N)) ≫ R'.map (tB.hom.app (M, N)) ≫
        rho'.hom.app (FB.obj M, FB.obj N))
    (hg : OpenTensorUnitNormalization E R TA TB adj rho gamma)
    (hg' : OpenTensorUnitNormalization E' R' TA' TB' adj' rho' gamma') :
    OpenTensorForgetNormalization E R E' R' FA FB TA TB TA' TB' eE eR tA tB
      gamma gamma' := by
  have hrinv (M N : B) :
      FA.map (rho.inv.app (M, N)) ≫ eR.hom.app (TB.obj (M, N)) ≫
        R'.map (tB.hom.app (M, N)) =
      tA.hom.app (R.obj M, R.obj N) ≫
        TA'.map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) ≫
          rho'.inv.app (FB.obj M, FB.obj N) := by
    apply (cancel_mono (rho'.hom.app (FB.obj M, FB.obj N))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hr M N]
    simp only [← FA.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    simp only [Functor.comp_obj, Functor.prod_obj, Category.comp_id]
  intro M N
  let X := TA.obj (M, R.obj N)
  let q := tA.hom.app (M, R.obj N) ≫ TA'.map (Prod.mkHom (𝟙 _) (eR.hom.app N))
  let p := tB.hom.app (E.obj M, N) ≫ TB'.map (Prod.mkHom (eE.hom.app M) (𝟙 _))
  have hn : FA.map (TA.map (Prod.mkHom (adj.unit.app M) (𝟙 (R.obj N)))) ≫
      tA.hom.app (R.obj (E.obj M), R.obj N) =
      tA.hom.app (M, R.obj N) ≫
        TA'.map (Prod.mkHom (FA.map (adj.unit.app M)) (𝟙 _)) := by
    simpa using tA.hom.naturality (Prod.mkHom (adj.unit.app M) (𝟙 (R.obj N)))
  have hrn : rho'.inv.app (FB.obj (E.obj M), FB.obj N) ≫
      R'.map (TB'.map (Prod.mkHom (eE.hom.app M) (𝟙 (FB.obj N)))) =
      TA'.map (Prod.mkHom (R'.map (eE.hom.app M)) (𝟙 _)) ≫
        rho'.inv.app (E'.obj (FA.obj M), FB.obj N) := by
    simpa using (rho'.inv.naturality
      (Prod.mkHom (eE.hom.app M) (𝟙 (FB.obj N)))).symm
  simp only [OpenTensorUnitNormalization, Functor.comp_obj, Functor.prod_obj,
    Functor.id_obj] at hg hg'
  have hi : eE.inv.app X ≫ FB.map (gamma.inv.app (M, N)) ≫ p =
      E'.map q ≫ gamma'.inv.app (FA.obj M, FB.obj N) := by
    apply (adj'.homEquiv _ _).injective
    rw [← Category.assoc (eE.inv.app X), adj'.homEquiv_naturality_right,
      openTensor_forget_homEquiv adj adj' FA FB eE eR hu]
    dsimp only [X, Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
    rw [hg M N, adj'.homEquiv_naturality_left, hg' (FA.obj M) (FB.obj N)]
    dsimp only [p, q]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hrinv (E.obj M) N, hrn, reassoc_of% hn]
    simp only [← TA'.map_comp_assoc]
    congr 2
    apply congrArg TA'.map
    ext <;> simp [hu M]
  have hi' : FB.map (gamma.inv.app (M, N)) ≫ p =
      eE.hom.app X ≫ E'.map q ≫ gamma'.inv.app (FA.obj M, FB.obj N) := by
    calc
      _ = eE.hom.app X ≫ (eE.inv.app X ≫ FB.map (gamma.inv.app (M, N)) ≫ p) := by
        simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      _ = _ := by rw [hi]
  apply (cancel_epi (FB.map (gamma.inv.app (M, N)))).1
  simp only [← FB.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  have hi'' := congrArg
    (fun z ↦ z ≫ gamma'.hom.app (FA.obj M, FB.obj N)) hi'
  simp only [p, q, X, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Category.comp_id] at hi''
  exact hi''.symm

private theorem openTensor_ordinary_of_support
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    {E : A ⥤ B} {R : B ⥤ A} (adj : E ⊣ R)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (hu : ∀ M, IsIso (adj.unit.app M))
    (hs : ∀ M N, IsIso (adj.counit.app (TB.obj (E.obj M, N)))) :
    ∃ gamma : E.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod R ⋙ TA ⋙ E,
      OpenTensorUnitNormalization E R TA TB adj rho gamma := by
  let t : (𝟭 A).prod R ⋙ TA ⋙ E ⟶ E.prod (𝟭 B) ⋙ TB :=
    { app := fun MN ↦ (adj.homEquiv _ _).symm
        (TA.map (Prod.mkHom (adj.unit.app MN.1) (𝟙 _)) ≫
          rho.inv.app (E.obj MN.1, MN.2))
      naturality := by
        intro MN MN' f
        apply (adj.homEquiv _ _).injective
        dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map,
          Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        have hn := rho.inv.naturality (Prod.mkHom (E.map f.1) f.2)
        dsimp only [Functor.comp_map, Functor.prod_map] at hn
        rw [Category.assoc, ← hn]
        simp only [← TA.map_comp_assoc]
        congr 2
        ext
        · exact adj.unit.naturality f.1
        · simp }
  have ht (MN : A × B) : IsIso (t.app MN) := by
    dsimp only [t]
    rw [adj.homEquiv_counit]
    have := hu MN.1
    have := hs MN.1 MN.2
    have : IsIso (Prod.mkHom (adj.unit.app MN.1) (𝟙 (R.obj MN.2))) :=
      (isIso_prod_iff A A).mpr ⟨hu MN.1, inferInstance⟩
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨(asIso t).symm, ?_⟩
  intro M N
  exact (adj.homEquiv _ _).apply_symm_apply _

section ExactSquares

variable {A B A' B' : Type a} [Category.{b} A] [Category.{b} B]
  [Category.{b} A'] [Category.{b} B'] [Abelian A] [Abelian B]
  [Abelian A'] [Abelian B'] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  [HasDerivedCategory.{d} A'] [HasDerivedCategory.{d} B']
  {E : A ⥤ B} {R : B ⥤ A} {E' : A' ⥤ B'} {R' : B' ⥤ A'}
  (FA : A ⥤ A') (FB : B ⥤ B')
  [E.Additive] [R.Additive] [E'.Additive] [R'.Additive] [FA.Additive] [FB.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [PreservesFiniteLimits FA] [PreservesFiniteColimits FA]
  [PreservesFiniteLimits FB] [PreservesFiniteColimits FB]

private theorem openTensor_exact_unit_fac (adj : E ⊣ R) (K : CochainComplex A ℤ) :
    adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have hu : adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        R.mapDerivedCategory.map (E.mapDerivedCategoryFactors.inv.app K) := by
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    rfl
  rw [hu]
  simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  exact Category.comp_id _

private theorem openTensor_exact_unit_isIso (adj : E ⊣ R)
    (hu : ∀ M, IsIso (adj.unit.app M)) (X : DerivedCategory A) :
    IsIso (adj.mapExactDerivedCategory.unit.app X) := by
  have hQ (K : CochainComplex A ℤ) :
      IsIso (adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K)) := by
    have hK : IsIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
      have : ∀ n : ℤ,
          IsIso (((adj.mapHomologicalComplex (.up ℤ)).unit.app K).f n) :=
        fun n ↦ hu (K.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have : IsIso (adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K)) := by
      rw [openTensor_exact_unit_fac adj K]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (R.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K))
  exact (NatTrans.isIso_app_iff_of_iso adj.mapExactDerivedCategory.unit
    (DerivedCategory.Q.objObjPreimageIso X)).mp (hQ (DerivedCategory.Q.objPreimage X))

private def openTensor_complex_square (e : E ⋙ FB ≅ FA ⋙ E')
    (K : CochainComplex A ℤ) :
    (FB.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj K) ≅
      (E'.mapHomologicalComplex (.up ℤ)).obj ((FA.mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ e.app (K.X n))
    (fun n m _ ↦ (e.hom.naturality (K.d n m)).symm)

private theorem openTensor_exact_square_fac (e : E ⋙ FB ≅ FA ⋙ E')
    (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      E'.mapDerivedCategory.map (FA.mapDerivedCategoryFactors.hom.app K) ≫
      E'.mapDerivedCategoryFactors.hom.app ((FA.mapHomologicalComplex (.up ℤ)).obj K) =
    FB.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
      FB.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map (openTensor_complex_square FA FB e K).hom := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso E FB).inv.app
    (DerivedCategory.Q.obj K))).1
  rw [Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  all_goals rfl

private theorem openTensor_exact_forget_unit
    (adj : E ⊣ R) (adj' : E' ⊣ R')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (hu : openTensor_unitSquare adj adj' FA FB eE eR) :
    openTensor_unitSquare adj.mapExactDerivedCategory adj'.mapExactDerivedCategory
      FA.mapDerivedCategory FB.mapDerivedCategory
      (CategoryTheory.Functor.mapDerivedCategorySquareIso eE)
      (CategoryTheory.Functor.mapDerivedCategorySquareIso eR) := by
  let eD := Functor.mapDerivedCategorySquareIso eE
  let rD := Functor.mapDerivedCategorySquareIso eR
  have h :
      Functor.whiskerRight adj.mapExactDerivedCategory.unit FA.mapDerivedCategory ≫
        Functor.whiskerLeft E.mapDerivedCategory rD.hom ≫
          Functor.whiskerRight eD.hom R'.mapDerivedCategory =
      Functor.whiskerLeft FA.mapDerivedCategory adj'.mapExactDerivedCategory.unit := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    apply (cancel_mono (R'.mapDerivedCategory.map
      (E'.mapDerivedCategory.map (FA.mapDerivedCategoryFactors.hom.app K)) ≫
      R'.mapDerivedCategory.map (E'.mapDerivedCategoryFactors.hom.app
        ((FA.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      R'.mapDerivedCategoryFactors.hom.app
        ((E'.mapHomologicalComplex (.up ℤ)).obj
          ((FA.mapHomologicalComplex (.up ℤ)).obj K)))).1
    simp only [Category.assoc]
    rw [← R'.mapDerivedCategory.map_comp_assoc, ← R'.mapDerivedCategory.map_comp_assoc,
      Category.assoc (eD.hom.app _), openTensor_exact_square_fac FA FB eE K]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% rD.hom.naturality (E.mapDerivedCategoryFactors.hom.app K)]
    have hn := R'.mapDerivedCategoryFactors.hom.naturality
      (openTensor_complex_square FA FB eE K).hom
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    rw [reassoc_of% openTensor_exact_square_fac FB FA eR
      ((E.mapHomologicalComplex (.up ℤ)).obj K)]
    simp only [← FA.mapDerivedCategory.map_comp_assoc]
    rw [openTensor_exact_unit_fac adj K]
    rw [reassoc_of% FA.mapDerivedCategoryFactors.hom.naturality
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app K)]
    rw [← reassoc_of% adj'.mapExactDerivedCategory.unit.naturality
      (FA.mapDerivedCategoryFactors.hom.app K)]
    rw [openTensor_exact_unit_fac adj'
      ((FA.mapHomologicalComplex (.up ℤ)).obj K)]
    congr 1
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    congr 1
    ext n
    exact hu (K.X n)
  intro X
  exact congrArg (fun q ↦ q.app X) h

end ExactSquares

end CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

private theorem native_open_forget_unit (s : NativeOpenTensorData k₀ l j) :
    openTensor_unitSquare s.adj.mapExactDerivedCategory
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j
          (Spec (CommRingCat.of k₀))))).mapExactDerivedCategory
      (nativeForget k₀ l U) (nativeForget k₀ l Z)
      (nativeOpenForgetExtension k₀ l j) (nativeOpenForgetPull k₀ l j) := by
  let adj' := ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  let FA := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)
  let FB := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  let eE : extensionByZero k₀ l j ⋙ FB ≅ FA ⋙
      ProEtale.adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let eR : upperStar k₀ l j ⋙ FA ≅ FB ⋙ ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have hu : openTensor_unitSquare s.adj adj' FA FB eE eR := by
    intro X
    change (s.adj.unit.app X).hom.f ≫ 𝟙 _ ≫
      (ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))).map
          (𝟙 _) = adj'.unit.app X.carrier
    exact (openTensor_comp_two_ids
      (ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
      (X := (ProEtale.adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))).obj
          X.carrier) (s.adj.unit.app X).hom.f).trans (s.unit_forget X)
  have heE : CategoryTheory.Functor.mapDerivedCategorySquareIso eE =
      nativeOpenForgetExtension k₀ l j := by rfl
  have heR : CategoryTheory.Functor.mapDerivedCategorySquareIso eR =
      nativeOpenForgetPull k₀ l j := by rfl
  have h := openTensor_exact_forget_unit FA FB s.adj adj' eE eR hu
  rw [heE, heR] at h
  exact h

variable
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The native derived open tensor presentation admits the prescribed ordinary
forgetting comparison data.

Source: Stacks 0GL1, 0E8I and 015F; forgetting the normalized representative
squares through the exact open functors identifies them with the ordinary
unit-normalized squares. The proof uses the fixed tensor comparisons, the
ordinary open tensor theorem, and the Frobenius resolution theorem.
(blueprint: new-lem-sf-native-open-tensor-forget-normalization). -/
theorem native_open_tensor_forget_normalization (s : NativeOpenTensorData k₀ l j)
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
    Nonempty (OpenTensorForgetData
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (nativeForget k₀ l U) (nativeForget k₀ l Z)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor
    (nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor
    (nativeOpenForgetExtension k₀ l j) (nativeOpenForgetPull k₀ l j)
    (nativeDerivedClosedComparison k₀ l U).tensorComparison
    (nativeDerivedClosedComparison k₀ l Z).tensorComparison
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapExactDerivedCategory
      rho gamma) := by
  have hg := native_open_tensor_unit_normalization k₀ l j s rho gamma c _hc
  rcases _hc with ⟨_, hR, hSA, hSB, hTA, hTB, hDA, hDB, hfA, hfB,
    hmA, hmB, hiA, hiB, _, _, hsr, hr⟩
  obtain ⟨rho', hrho⟩ := native_open_tensor_restriction_forget k₀ l j s rho c
    ⟨hR, hSA, hSB, hTA, hTB, hDA, hDB, hfA, hfB, hmA, hmB, hiA, hiB, hsr, hr⟩
  let adj' := ProEtale.adicOpenImmersionLowerShriekAdjunction l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  obtain ⟨gamma', hg'⟩ := openTensor_ordinary_of_support adj'.mapExactDerivedCategory
    (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor
    (nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor rho'
    (openTensor_exact_unit_isIso adj' (fun _ ↦ inferInstance))
    (native_ordinary_open_tensor_support k₀ l j)
  have huD := native_open_forget_unit k₀ l j s
  refine ⟨{
    restriction := rho'
    restriction_compatibility := hrho
    gamma' := gamma'
    inverse_unit := hg'
    compatibility := ?_ }⟩
  exact openTensor_forget_of_unit s.adj.mapExactDerivedCategory adj'.mapExactDerivedCategory
    (nativeForget k₀ l U) (nativeForget k₀ l Z)
    (nativeOpenForgetExtension k₀ l j) (nativeOpenForgetPull k₀ l j)
    (nativeDerivedClosedComparison k₀ l U).tensorComparison
    (nativeDerivedClosedComparison k₀ l Z).tensorComparison rho rho' gamma gamma'
    huD hrho hg hg'

end AlgebraicGeometry.ProEtaleWeilSheaf
