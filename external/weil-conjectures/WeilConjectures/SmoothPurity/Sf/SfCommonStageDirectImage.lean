/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackIdentity
import WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageAdjunction
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Common-stage direct image and its induced Weil structure

Source: Bhatt--Scholze 6.8.14(2), 6.8.15; blueprint derived-direct-image convention
(blueprint: prose-03-02).
The existing integral tower construction is reexported. Its rational/common-stage
extension is characterized by the derived inverse-image adjunction. Taking fixed pairs
uses the mate of the normalized Frobenius pullback square, not a derived category of pairs.
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

namespace DirectImageAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u₁ v₁ u₂ v₂
variable {I : Type w} [Preorder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
  {S : StageSystem C} {T : StageSystem D} (L : S.Morphism T)
  (R : ∀ i, D i ⥤ C i) (a : ∀ i, L.Φ i ⊣ R i)
  (b : ∀ {i j : I} (h : i ≤ j), R i ⋙ S.T h ≅ T.T h ⋙ R j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : D i),
    (L.Φ j).map ((b h).hom.app K) ≫ (a j).counit.app ((T.T h).obj K) =
      (L.β h).inv.app ((R i).obj K) ≫ (T.T h).map ((a i).counit.app K))

include hb

private theorem mateUnit {i j : I} (h : i ≤ j) (K : C i) :
    (S.T h).map ((a i).unit.app K) ≫ (b h).hom.app ((L.Φ i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R j).map ((L.β h).inv.app K) := by
  apply ((a j).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hb]
  have hn := (L.β h).inv.naturality ((a i).unit.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at hn
  rw [reassoc_of% hn]
  rw [← (T.T h).map_comp, (a i).left_triangle_components, (T.T h).map_id]
  simp only [Category.comp_id]
  rw [(a j).counit_naturality, ← Category.assoc,
    (a j).left_triangle_components ((S.T h).obj K)]
  exact (Category.id_comp _).symm

private theorem mateCoherence {i j k : I} (h : i ≤ j) (h' : j ≤ k) (K : D i) :
    (S.T h').map ((b h).hom.app K) ≫ (b h').hom.app ((T.T h).obj K) ≫
      (R k).map ((T.assoc h h').hom.app K) =
    (S.assoc h h').hom.app ((R i).obj K) ≫ (b (h.trans h')).hom.app K := by
  apply ((a k).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [(a k).counit_naturality, reassoc_of% (hb h' ((T.T h).obj K))]
  have hn := (L.β h').inv.naturality ((b h).hom.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at hn
  rw [reassoc_of% hn]
  rw [← (T.T h').map_comp_assoc, hb, (T.T h').map_comp]
  have ht := (T.assoc h h').hom.naturality ((a i).counit.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at ht
  simp only [Category.assoc]
  rw [ht]
  have hc := L.coh_inv h h' ((R i).obj K)
  have hc' : (L.β h').inv.app ((S.T h).obj ((R i).obj K)) ≫
      (T.T h').map ((L.β h).inv.app ((R i).obj K)) ≫
      (T.assoc h h').hom.app ((L.Φ i).obj ((R i).obj K)) =
      (L.Φ k).map ((S.assoc h h').hom.app ((R i).obj K)) ≫
        (L.β (h.trans h')).inv.app ((R i).obj K) := by
    rw [← cancel_epi ((L.Φ k).map ((S.assoc h h').inv.app ((R i).obj K)))]
    rw [reassoc_of% hc]
    simp only [Iso.inv_hom_id_app, Category.comp_id,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hc', hb]

private def mateFamily : T.Morphism S where
  Φ := R
  β := b
  coh := mateCoherence L R a b hb

private def mateFamilyUnit : StageSystem.Morphism.Hom (StageSystem.Morphism.id S)
    (L.comp (mateFamily L R a b hb)) where
  τ i := (a i).unit
  comm {i j} h K := by
    simp only [StageSystem.Morphism.id_β_hom_app, StageSystem.Morphism.comp_β_hom_app]
    change (S.T h).map ((a i).unit.app K) ≫
      ((b h).hom.app ((L.Φ i).obj K) ≫ (R j).map ((L.β h).hom.app K)) =
      𝟙 _ ≫ (a j).unit.app ((S.T h).obj K)
    rw [Category.id_comp]
    rw [← Category.assoc, mateUnit L R a b hb, Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    change (a j).unit.app ((S.T h).obj K) ≫
      (R j).map (𝟙 ((L.Φ j).obj ((S.T h).obj K))) = _
    rw [(R j).map_id]
    exact Category.comp_id _

private def mateFamilyCounit : StageSystem.Morphism.Hom
    ((mateFamily L R a b hb).comp L) (StageSystem.Morphism.id T) where
  τ i := (a i).counit
  comm {i j} h K := by
    simp only [StageSystem.Morphism.id_β_hom_app, StageSystem.Morphism.comp_β_hom_app]
    change (T.T h).map ((a i).counit.app K) ≫ 𝟙 _ =
      ((L.β h).hom.app ((R i).obj K) ≫ (L.Φ j).map ((b h).hom.app K)) ≫
        (a j).counit.app ((T.T h).obj K)
    rw [Category.comp_id, Category.assoc, hb, Iso.hom_inv_id_app_assoc]

end DirectImageAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def descendStageAdjunction
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {C' : I → Type*} [∀ i, Category (C' i)]
    {S : StageSystem C} {T : StageSystem C'}
    (L : S.Morphism T) (R : T.Morphism S) (a : ∀ i, L.Φ i ⊣ R.Φ i)
    (η : StageSystem.Morphism.Hom (StageSystem.Morphism.id S) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id T))
    (hη : ∀ i, η.τ i = (a i).unit) (hε : ∀ i, ε.τ i = (a i).counit) :
    L.functor ⊣ R.functor where
  unit := StageSystem.Morphism.functorIdIso.inv ≫
    StageSystem.Morphism.descNatTrans η ≫ (L.functorCompIso R).hom
  counit := (R.functorCompIso L).inv ≫
    StageSystem.Morphism.descNatTrans ε ≫ StageSystem.Morphism.functorIdIso.hom
  left_triangle_components X := by
    simp only [NatTrans.comp_app, StageSystem.Morphism.functorIdIso_inv_app,
      StageSystem.Morphism.functorIdIso_hom_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app,
      Category.id_comp, Category.comp_id, StageSystem.Morphism.descNatTrans_app,
      hη, hε, StageSystem.Morphism.functor_map_ι]
    change (T.ι X.stage).map ((L.Φ X.stage).map ((a X.stage).unit.app X.obj)) ≫
      (T.ι X.stage).map ((a X.stage).counit.app ((L.Φ X.stage).obj X.obj)) = _
    rw [← CategoryTheory.Functor.map_comp]
    change (T.ι X.stage).map _ =
      𝟙 ((T.ι X.stage).obj ((L.Φ X.stage).obj X.obj))
    calc
      _ = (T.ι X.stage).map (𝟙 ((L.Φ X.stage).obj X.obj)) :=
        congrArg ((T.ι X.stage).map) ((a X.stage).left_triangle_components X.obj)
      _ = _ := (T.ι X.stage).map_id _
  right_triangle_components X := by
    simp only [NatTrans.comp_app, StageSystem.Morphism.functorIdIso_inv_app,
      StageSystem.Morphism.functorIdIso_hom_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app,
      Category.id_comp, Category.comp_id, StageSystem.Morphism.descNatTrans_app,
      hη, hε, StageSystem.Morphism.functor_map_ι]
    change (S.ι X.stage).map ((a X.stage).unit.app ((R.Φ X.stage).obj X.obj)) ≫
      (S.ι X.stage).map ((R.Φ X.stage).map ((a X.stage).counit.app X.obj)) = _
    rw [← CategoryTheory.Functor.map_comp]
    change (S.ι X.stage).map _ =
      𝟙 ((S.ι X.stage).obj ((R.Φ X.stage).obj X.obj))
    calc
      _ = (S.ι X.stage).map (𝟙 ((R.Φ X.stage).obj X.obj)) :=
        congrArg ((S.ι X.stage).map) ((a X.stage).right_triangle_components X.obj)
      _ = _ := (S.ι X.stage).map_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalStageAdjunction_descends
    (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X))
    (R : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (hΦ : L.Φ = (fun E ↦ rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f))
    (hβ : ∀ (E F : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ F)
      (K : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y),
      HEq ((L.β h).app K) (commonStagePullbackComparison l Ω f ⟨E, K⟩ F h))
    (a : ∀ E, L.Φ E ⊣ R.Φ E)
    (η : StageSystem.Morphism.Hom (StageSystem.Morphism.id _) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id _))
    (hη : ∀ E, η.τ E = (a E).unit) (hε : ∀ E, ε.τ E = (a E).counit) :
    (commonStageDerivedPullback l Ω f).IsLeftAdjoint := by
  have hF : L.functor = commonStageDerivedPullback l Ω f := by
    apply (commonStageDerivedPullback_existsUnique l Ω f).unique
      (y₁ := L.functor)
    · rcases L with ⟨Φ, β, coh⟩
      dsimp only at hΦ
      subst Φ
      constructor
      · intro P
        rfl
      · intro P Q F hP hQ k
        apply heq_of_eq
        change StageSystem.PairCategory.mkHom
          (X := commonStagePullbackObject l Ω f P)
          (Y := commonStagePullbackObject l Ω f Q) F hP hQ
          ((β hP).hom.app P.obj ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
              f).map k ≫ (β hQ).inv.app Q.obj) = _
        have hp := congrArg Iso.hom (eq_of_heq (hβ P.stage F hP P.obj))
        have hq := congrArg Iso.inv (eq_of_heq (hβ Q.stage F hQ Q.obj))
        dsimp only [Iso.app_hom, Iso.app_inv] at hp hq
        rw [hp, hq]
    · exact (commonStageDerivedPullback_existsUnique l Ω
        f).exists.choose_spec
  have h := (descendStageAdjunction L R a η ε hη hε).isLeftAdjoint
  rwa [hF] at h

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

end WeilConjectures
