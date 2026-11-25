/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! Multiplication normalization of the ordinary scalar/tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory
namespace WeilConjectures.PurCompactSupport
attribute [local implicit_reducible]
  Functor.map₂HomologicalComplex pbcDerivedRestrict
attribute [local instance 100000] coefficientSiteSmall coefficientRingSheafify
  coefficientAbSheafify coefficientAbLocallyBijective

attribute [local irreducible] scalarTensor tensorIdentity scalarOrdinaryTensor
  scalarTensorTotal CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  SheafOfModules.monoidalCategory SheafOfModules.tensorObjIsoSheafification
  AlgebraicGeometry.Scheme.reductionDerivedChange
  CategoryTheory.Functor.mapDerivedCategory HasDerivedCategory.standard
  pbcComplexCounit

private def restrictionUnit {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 _ :=
  (restrictIdentity_existsUnique R).exists.choose

private def ordinaryUnit {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    𝟭 _ ≅ pbcExtend (𝟙 R) :=
  (conjugateIsoEquiv (pbcScalarAdjunction (𝟙 R)) Adjunction.id).symm
    (restrictionUnit R)

private theorem ordinaryUnit_hom {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryUnit R).hom.app M).val.app U x = pbcTensorSection (𝟙 R) M U 1 x := by
  have h := conjugateEquiv_adjunction_id_symm (pbcScalarAdjunction (𝟙 R))
    (restrictionUnit R).hom M
  change (ordinaryUnit R).hom.app M = _ at h
  rw [h]
  change ((restrictionUnit R).hom.app _).val.app U
    (((pbcScalarAdjunction (𝟙 R)).unit.app M).val.app U x) = _
  have hr := (restrictIdentity_existsUnique R).exists.choose_spec
  change ∀ M U x, ((restrictionUnit R).hom.app M).val.app U x = x at hr
  rw [hr]
  exact (pbcScalarAdjunction_exists (𝟙 R)).exists.choose_spec M U x

attribute [local irreducible] ordinaryUnit

private theorem ordinaryUnit_tensor {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (M N : pbcModules X R) :
    (ordinaryUnit R).hom.app (((proEtaleOrdinaryTensor X R).obj M).obj N) ≫
        (scalarOrdinaryTensor (𝟙 R) M N).hom =
      ((proEtaleOrdinaryTensor X R).map ((ordinaryUnit R).hom.app M)).app N ≫
        ((proEtaleOrdinaryTensor X R).obj _).map ((ordinaryUnit R).hom.app N) := by
  apply tensorPair_ext R M N
  intro U x y
  change (scalarOrdinaryTensor (𝟙 R) M N).hom.val.app U
    (((ordinaryUnit R).hom.app _).val.app U (proEtaleTensorPair X R M N U x y)) = _
  rw [ordinaryUnit_hom]
  have hμ := (scalarOrdinaryTensor_existsUnique (𝟙 R)).exists.choose_spec M N U 1 x y
  simp only [scalarOrdinaryTensor]
  rw [hμ]
  have hm := tensorPair_map R ((ordinaryUnit R).hom.app M)
    ((ordinaryUnit R).hom.app N) U x y
  dsimp only [Functor.id_obj] at hm
  have he := congrArg₂ (proEtaleTensorPair X R
    ((pbcExtend (𝟙 R)).obj M) ((pbcExtend (𝟙 R)).obj N) U)
    (ordinaryUnit_hom R M U x) (ordinaryUnit_hom R N U y)
  exact he.symm.trans hm.symm

private theorem ordinaryUnit_total {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (pbcModules X R) ℤ) :
    HomologicalComplex.mapBifunctorMap
        ((NatTrans.mapHomologicalComplex (ordinaryUnit R).hom (.up ℤ)).app P)
        ((NatTrans.mapHomologicalComplex (ordinaryUnit R).hom (.up ℤ)).app Q)
        (proEtaleOrdinaryTensor X R) (.up ℤ) ≫ scalarTensorTotal (𝟙 R) P Q =
      (NatTrans.mapHomologicalComplex (ordinaryUnit R).hom (.up ℤ)).app
        (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor X R)) := by
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := proEtaleTensorPreadditive X R
  have h (M N : pbcModules X R) :
      ((ordinaryUnit R).hom.app M ⊗ₘ (ordinaryUnit R).hom.app N) ≫
        (scalarOrdinaryTensor (𝟙 R) M N).inv =
      (ordinaryUnit R).hom.app (M ⊗ N) := by
    rw [← cancel_mono (scalarOrdinaryTensor (𝟙 R) M N).hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.id_obj,
      proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor,
      MonoidalCategory.tensorHom_def] using (ordinaryUnit_tensor R M N).symm
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [proEtaleOrdinaryTensor]
  simp only [HomologicalComplex.comp_f, scalarTensorTotal, tensorPullbackTotal,
    HomologicalComplex.ι_mapBifunctorMap_assoc, tensorPullbackTotalComponent,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_obj_X,
    Functor.id_obj]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  change ((ordinaryUnit R).hom.app (P.X i) ▷ _) ≫
    (_ ◁ (ordinaryUnit R).hom.app (Q.X j)) ≫
    (scalarOrdinaryTensor (𝟙 R) (P.X i) (Q.X j)).inv ≫
    (pbcExtend (𝟙 R)).map (CochainComplex.ιMapBifunctor P Q _ i j n hij) = _
  rw [← MonoidalCategory.tensorHom_def_assoc, ← Category.assoc, h]
  exact ((ordinaryUnit R).hom.naturality
    (CochainComplex.ιMapBifunctor P Q _ i j n hij)).symm

private theorem derivedId_fac {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A]
    (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryIdIso A).hom.app
        (DerivedCategory.Q.obj P) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P) := by
  let κ := DerivedCategory.quotientCompQhIso A
  have h := congr_app (congrArg Iso.hom
    (Functor.mapDerivedCategoryIdIso_factorsh A))
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at h
  rw [Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app] at h
  dsimp only [Functor.id_obj] at h
  simp only [Category.assoc] at h
  have hn := (Functor.mapDerivedCategoryIdIso A).hom.naturality
    (κ.hom.app P)
  simp only [Functor.id_map] at hn
  apply (cancel_epi ((𝟭 A).mapDerivedCategory.map (κ.hom.app P))).1
  have hf : ((𝟭 A).mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl
  rw [hf] at h
  erw [hn, h]
  erw [DerivedCategory.quotientCompQhIso_hom_naturality]
  dsimp only [κ]
  erw [DerivedCategory.Qh.map_id]
  change (𝟭 A).mapDerivedCategory.map (κ.hom.app P) ≫
      (𝟭 A).mapDerivedCategoryFactors.hom.app P ≫
        κ.inv.app (((𝟭 A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          𝟙 _ ≫ κ.hom.app (((𝟭 A).mapHomologicalComplex (.up ℤ)).obj P) ≫ 𝟙 _ =
    (𝟭 A).mapDerivedCategory.map (κ.hom.app P) ≫
      (𝟭 A).mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _
  rw [Category.id_comp, Iso.inv_hom_id_app_assoc]
  rfl

private theorem exactTrivialization_fac {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {U : A ⥤ A} [U.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits U]
    [CategoryTheory.Limits.PreservesFiniteColimits U]
    (e : U ≅ 𝟭 A) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app
        (DerivedCategory.Q.obj P) =
      U.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P ≫
            (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P) := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [derivedId_fac, ← Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
  rw [Functor.map_comp, Category.assoc]

private theorem derivedUnit_complex {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P : CochainComplex (pbcModules X R) ℤ)
    (hp : proEtaleFlatRepresentatives X R P) :
    (tensorIdentity R).inv.app (DerivedCategory.Q.obj P) ≫ pbcComplexCounit (𝟙 R) P =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ordinaryUnit R).hom (.up ℤ)).app P) := by
  let ρ := Functor.mapDerivedCategoryNatIso (restrictionUnit R) ≪≫
    Functor.mapDerivedCategoryIdIso (pbcModules X R)
  have hρ (T : CochainComplex (pbcModules X R) ℤ) :=
    exactTrivialization_fac (restrictionUnit R) T
  have hunit : (tensorIdentity R).inv.app (DerivedCategory.Q.obj P) =
      (pbcDerivedScalarAdjunction (𝟙 R)).unit.app (DerivedCategory.Q.obj P) ≫
        ρ.hom.app ((pbcDerivedExtend (𝟙 R)).obj (DerivedCategory.Q.obj P)) := by
    unfold tensorIdentity
    exact conjugateEquiv_adjunction_id_symm (pbcDerivedScalarAdjunction (𝟙 R))
      ρ.hom (DerivedCategory.Q.obj P)
  have he := ρ.hom.naturality (pbcComplexCounit (𝟙 R) P)
  simp only [Functor.id_map] at he
  rw [hunit, Category.assoc, ← he]
  rw [show ρ.hom.app (DerivedCategory.Q.obj _) = _ from hρ _]
  have hn := (pbcDerivedScalarAdjunction_exists (𝟙 R)).exists.choose_spec P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1)
  change (pbcDerivedScalarAdjunction (𝟙 R)).unit.app _ ≫ _ ≫ _ = _ at hn
  erw [reassoc_of% hn, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f, Functor.mapHomologicalComplex_obj_X]
  erw [Category.comp_id]
  unfold ordinaryUnit
  exact (conjugateEquiv_adjunction_id_symm (pbcScalarAdjunction (𝟙 R))
    (restrictionUnit R).hom (P.X n)).symm

private theorem identity_tensor_unit {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (a : ProEtaleTensorModel X R) :
    Functor.whiskerLeft a.tensor (tensorIdentity R).inv ≫
        (scalarTensor (𝟙 R) a a).hom =
      Functor.whiskerRight
        (NatTrans.prod (tensorIdentity R).inv (tensorIdentity R).inv) a.tensor := by
  obtain ⟨ff⟩ := tensorRepresentatives_fullyFaithful R R
  apply ff.map_injective
  apply NatTrans.ext
  funext Z
  obtain ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩ := Z
  obtain ⟨hp', hq', hμ⟩ :=
    (scalarTensor_existsUnique (𝟙 R) a a).exists.choose_spec P Q hp hq
  rw [← scalarTensor] at hμ
  let uP := (NatTrans.mapHomologicalComplex (ordinaryUnit R).hom (.up ℤ)).app P
  let uQ := (NatTrans.mapHomologicalComplex (ordinaryUnit R).hom (.up ℤ)).app Q
  let T := CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor X R)
  have hT := tensorTotal_flatRepresentatives R P Q hp hq
  have := scalarComplexCounit_isIso (𝟙 R) P hp
  have := scalarComplexCounit_isIso (𝟙 R) Q hq
  have : IsIso (Prod.mkHom (pbcComplexCounit (𝟙 R) P) (pbcComplexCounit (𝟙 R) Q)) :=
    ⟨⟨Prod.mkHom (inv (pbcComplexCounit (𝟙 R) P))
      (inv (pbcComplexCounit (𝟙 R) Q)), by ext <;> simp, by ext <;> simp⟩⟩
  change (tensorIdentity R).inv.app (a.tensor.obj (DerivedCategory.Q.obj P,
      DerivedCategory.Q.obj Q)) ≫ (scalarTensor (𝟙 R) a a).hom.app _ =
    a.tensor.map (Prod.mkHom ((tensorIdentity R).inv.app (DerivedCategory.Q.obj P))
      ((tensorIdentity R).inv.app (DerivedCategory.Q.obj Q)))
  apply (cancel_epi (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩))).1
  apply (cancel_mono (a.tensor.map
    (Prod.mkHom (pbcComplexCounit (𝟙 R) P) (pbcComplexCounit (𝟙 R) Q)))).1
  have hn := (tensorIdentity R).inv.naturality
    (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩))
  dsimp only [Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj,
    Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex] at hn
  change a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      (tensorIdentity R).inv.app (a.tensor.obj (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) =
    (tensorIdentity R).inv.app (DerivedCategory.Q.obj T) ≫
      (pbcDerivedExtend (𝟙 R)).map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) at hn
  have ht : (NatTrans.mapHomologicalComplex (ordinaryUnit R).hom (.up ℤ)).app T ≫
      @inv _ _ _ _ (scalarTensorTotal (𝟙 R) P Q) (scalarTensorTotal_isIso (𝟙 R) P Q) =
        HomologicalComplex.mapBifunctorMap uP uQ (proEtaleOrdinaryTensor X R) (.up ℤ) := by
    rw [← ordinaryUnit_total R P Q, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hr := a.representative.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk uP) (ObjectProperty.homMk uQ) :
      (⟨P, hp⟩, ⟨Q, hq⟩) ⟶ (⟨_, hp'⟩, ⟨_, hq'⟩))
  dsimp only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
    Functor.uncurry_obj_map, Functor.map₂HomologicalComplex] at hr
  rw [SheafOfModules.CanonicalTensorPullbackProof.tensorMap_factor] at hr
  change DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap uP uQ (proEtaleOrdinaryTensor X R) (.up ℤ)) ≫
      a.representative.hom.app (⟨_, hp'⟩, ⟨_, hq'⟩) =
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      a.tensor.map (Prod.mkHom (DerivedCategory.Q.map uP) (DerivedCategory.Q.map uQ)) at hr
  simp only [Category.assoc]
  rw [reassoc_of% hn, hμ]
  rw [reassoc_of% (derivedUnit_complex R T hT)]
  rw [← Functor.map_comp_assoc, ht, hr]
  rw [← a.tensor.map_comp]
  congr 2
  ext
  · exact (derivedUnit_complex R P hp).symm
  · exact (derivedUnit_complex R Q hq).symm

/-- Identity scalar balancing preserves the multiplication unit.
Source: current blueprint proposition-six-operations-change-coefficients, final paragraph;
the flat-representative normalization of scalarTensor.
(blueprint: lem-sf-integral-scalar-tensor-identity)

Proof: take flat-term K-flat representatives P and Q. The identity scalar
restriction is the identity on sections, so its conjugate tensorIdentity is
multiplication r tensor x ↦ rx. The inverse balancing map sends
(r tensor x) tensor (s tensor y) to rs tensor (x tensor y).
Both displayed composites therefore send this generator to rx tensor sy.
The same formula holds degreewise on signed total tensors, since the scalars
have degree zero. The universal derived counits give the equality on the
localized representatives. Naturality transports it along representative
isomorphisms to arbitrary K and M. Zero objects and the empty site use the
same calculation. -/
theorem scalarTensor_identity {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel X R) (K M : DerivedCategory (pbcModules X R)) :
    (scalarTensor (𝟙 R) a a).inv.app (K, M) ≫
        (tensorIdentity R).hom.app (a.tensor.obj (K, M)) =
      a.tensor.map (Prod.mkHom ((tensorIdentity R).hom.app K)
        ((tensorIdentity R).hom.app M)) := by
  have h := congrArg (fun z ↦ z.app (K, M)) (identity_tensor_unit R a)
  change (tensorIdentity R).inv.app (a.tensor.obj (K, M)) ≫
    (scalarTensor (𝟙 R) a a).hom.app (K, M) =
      a.tensor.map (Prod.mkHom ((tensorIdentity R).inv.app K)
        ((tensorIdentity R).inv.app M)) at h
  apply (cancel_epi ((scalarTensor (𝟙 R) a a).hom.app (K, M))).1
  simp only [Iso.hom_inv_id_app_assoc]
  apply (cancel_epi ((tensorIdentity R).inv.app (a.tensor.obj (K, M)))).1
  rw [← Category.assoc, h, ← a.tensor.map_comp]
  simp

end WeilConjectures.PurCompactSupport
