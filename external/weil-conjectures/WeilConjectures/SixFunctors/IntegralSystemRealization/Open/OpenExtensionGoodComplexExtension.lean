/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionZeroCompletion
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.Ringed.RingedSiteEquivalenceTensor
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenFlatResolution

/-! # Goodness of completed open extension

Source: Stacks Tags 03DI, 03DJ, 0E8I and 0G7E.
(blueprint: lem-sf-open-extension-good-complex-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] SheafOfModules.monoidalCategory HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

private def inverseTensorComparison
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (e : C ≌ D)
    (t : MonoidalCategory.tensor C ⋙ e.functor ≅
      e.functor.prod e.functor ⋙ MonoidalCategory.tensor D) :
    MonoidalCategory.tensor D ⋙ e.inverse ≅
      e.inverse.prod e.inverse ⋙ MonoidalCategory.tensor C := by
  let a : (MonoidalCategory.tensor D ⋙ e.inverse) ⋙ e.functor ≅
      MonoidalCategory.tensor D :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.counitIso ≪≫
      Functor.rightUnitor _
  let b : (e.inverse.prod e.inverse ⋙ MonoidalCategory.tensor C) ⋙ e.functor ≅
      MonoidalCategory.tensor D :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ t ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod e.counitIso e.counitIso)
        (MonoidalCategory.tensor D)
  exact Functor.fullyFaithfulCancelRight e.functor (a ≪≫ b.symm)

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Completed coefficient open extension preserves the K-flat, flat-term class.
Source: Stacks 03DI, 03DJ, 0E8I and 0G7E; the ringed-slice transport step.
(blueprint: lem-sf-open-extension-good-complex-extension).

Proof: identify the actual completed coefficient open extension with the literal
ringed-slice extension using the pro-etale slice presentation. The ringed-slice
flat-resolution theorem preserves independent-coefficient K-flatness and each
term's site-flatness; transport these predicates through the presentation
equivalences and the termwise natural isomorphism. The construction is valid for
the empty and identity opens and for unbounded complexes.
-/
theorem openExtension_goodComplex_extension {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    integralOperationsGoodComplex l E Y
      (((PurCompactSupport.openExtension
        (PurCompactSupport.completed l E) j).mapHomologicalComplex
         (.up ℤ)).obj P.obj) := by
  let W := ProEt.mk j
  let RV := (PurCompactSupport.completed l E).ring Y
  let RU := (PurCompactSupport.completed l E).ring X
  let RI := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj RV
  let cU := (PurCompactSupport.completed l E).pull j
  let R := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV
  let S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RI
  let G : X.ProEt ⥤ Y.ProEt := MorphismProperty.Over.map ⊤ W.prop
  have : G.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    ProEt.isContinuous_overMap W.prop
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).IsContinuous
      (ProEt.topology Y) (ProEt.topology X) := ProEt.isContinuous_overPullback j
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j W.prop trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let c₀ := ((proEtaleSheafAdjunction j CommRingCat.{u + 1}).leftAdjointUniq b).app RV
  let c : S ≅ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (ProEt.topology Y)).obj R :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c₀
  have : (ProEt.sliceEquiv Y W).inverse.IsDenseSubsite
      (ProEt.topology X) ((ProEt.topology Y).over W) := ProEt.sliceDense Y W
  obtain ⟨q, hq⟩ := ProEt.module_transport ((ProEt.topology Y).over W)
    (ProEt.topology X) (ProEt.sliceEquiv Y W) (R.over W) S c
  let ψ : R ⟶ ((proEtaleBaseChange j).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X)).obj S :=
    ⟨Functor.whiskerRight
      ((proEtaleSheafAdjunction j CommRingCat.{u + 1}).unit.app RV).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ (proEtaleBaseChange j).op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext V
    have hc := Adjunction.unit_leftAdjointUniq_hom_app
      (proEtaleSheafAdjunction j CommRingCat.{u + 1}) b RV
    exact congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (f.hom.app V)) hc.symm
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (c.hom.hom.app V)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun t ↦ t.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (c.hom.hom.app ((proEtaleBaseChange j).op.obj (G.op.obj V)))
      (R.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app V ≫ R.obj.map (𝟙 (G.op.obj V)) = c.hom.hom.app V
    rw [R.obj.map_id]
    exact Category.comp_id (c.hom.hom.app V)
  let d := SheafOfModules.pushforwardPushforwardAdj a c.hom ψ H₁ H₂
  let z := proEtaleModuleInverseImageAdjunction j RV
  let z' : proEtaleModuleInverseImage j RV ⊣ SheafOfModules.pushforward.{u + 1} ψ :=
    z.ofNatIsoRight (SheafOfModules.pushforwardCongr (by
      simp [ψ, proEtaleRingDirectImageMap]))
  let e := z'.leftAdjointUniq d
  let t : SheafOfModules.overFunctor.{u + 1} R W ⋙ q.functor ≅
      SheafOfModules.pushforward.{u + 1} c.hom :=
    Functor.fullyFaithfulCancelRight (SheafOfModules.forget S) (eqToIso (by
      change SheafOfModules.overFunctor R W ⋙ (q.functor ⋙ SheafOfModules.forget S) = _
      rw [hq]
      rfl))
  let eraw : proEtaleModuleInverseImage j RV ≅
      SheafOfModules.overFunctor R W ⋙ q.functor := e ≪≫ t.symm
  let L := SheafOfModules.localizedModuleExtension.{u} RV W
  have : L.Additive := SheafOfModules.localizedModuleExtension_additive.{u} RV W
  let al := SheafOfModules.localizedModuleAdjunctionIndependent.{u} RV W
  let ar : q.inverse ⋙ L ⊣ proEtaleModuleInverseImage j RV :=
    (q.symm.toAdjunction.comp al).ofNatIsoRight eraw.symm
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso cU
  let eqc := proEtaleScalarEquivalence X rc
  let directIso : eqc.functor ⋙ proEtaleRingModuleDirectImage j RV RI (Iso.refl _) ≅
      proEtaleRingModuleDirectImage j RV RU cU :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl))) (by
        intro M N f
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        rfl)
  let pullIso := (proEtaleRingModulePullbackAdjunction j RV RU cU).leftAdjointUniq
    ((z.comp eqc.symm.toAdjunction).ofNatIsoRight directIso)
  let ap : eqc.functor ⋙ q.inverse ⋙ L ⊣ proEtaleRingModulePullback j RV RU cU :=
    (eqc.toAdjunction.comp ar).ofNatIsoRight pullIso.symm
  let extIso : PurCompactSupport.openExtension (PurCompactSupport.completed l E) j ≅
      eqc.functor ⋙ q.inverse ⋙ L :=
    (Adjunction.ofIsRightAdjoint (proEtaleRingModulePullback j RV RU cU)).leftAdjointUniq ap
  let := SheafOfModules.isMonoidal_W_independentCoefficients RU
  let := SheafOfModules.isMonoidal_W_independentCoefficients RI
  let := SheafOfModules.isMonoidal_W_independentCoefficients (RV.over W)
  let := SheafOfModules.monoidalCategory RU
  let := SheafOfModules.monoidalCategory RI
  let : MonoidalCategory (SheafOfModules.{u + 1} (R.over W)) :=
    SheafOfModules.monoidalCategory (RV.over W)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients RU
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients RU
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients RI
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients RI
  let : (MonoidalCategory.curriedTensor
      (SheafOfModules.{u + 1} (R.over W))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients (RV.over W)
  let : ∀ N : SheafOfModules.{u + 1} (R.over W),
      ((MonoidalCategory.curriedTensor _).obj N).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (RV.over W)
  have : eqc.functor.Additive := inferInstanceAs (SheafOfModules.restrictScalars rc.hom).Additive
  have : q.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : (CategoryTheory.Equivalence.refl (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  have : (CategoryTheory.Equivalence.refl (C := X.ProEt)).inverse.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  obtain ⟨ts⟩ := SheafOfModules.pushforward_equivalence_tensor_iso
    (ProEt.topology X) (ProEt.topology X) (CategoryTheory.Equivalence.refl (C := X.ProEt))
    RU RI cU
  have h₁ := sfCbcKFlatTransport eqc.functor ts P.obj P.property.1
  have hf₁ (i : ℤ) := sfCbcFlatTransport eqc.functor ts (P.obj.X i)
    ((exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso RU (P.obj.X i)) (P.property.2 i))
  let F := SheafOfModules.pushforward.{u + 1} (F := (ProEt.sliceEquiv Y W).inverse)
    (J := ProEt.topology X) (K := (ProEt.topology Y).over W)
    (R := R.over W) (S := S) c.hom
  let et : q.functor ≅ F :=
    Functor.fullyFaithfulCancelRight (SheafOfModules.forget S) (eqToIso hq)
  have : (ProEt.sliceEquiv Y W).symm.functor.IsContinuous
      (ProEt.topology X) ((ProEt.topology Y).over W) :=
    inferInstanceAs ((ProEt.sliceEquiv Y W).inverse.IsContinuous _ _)
  have : (ProEt.sliceEquiv Y W).symm.inverse.IsContinuous
      ((ProEt.topology Y).over W) (ProEt.topology X) :=
    inferInstanceAs ((ProEt.sliceEquiv Y W).functor.IsContinuous _ _)
  obtain ⟨tq₀⟩ := SheafOfModules.pushforward_equivalence_tensor_iso
    (ProEt.topology X) ((ProEt.topology Y).over W) (ProEt.sliceEquiv Y W).symm
    (RV.over W) RI c₀
  let tq : MonoidalCategory.tensor _ ⋙ q.functor ≅
      q.functor.prod q.functor ⋙ MonoidalCategory.tensor _ :=
    Functor.isoWhiskerLeft _ et ≪≫ tq₀ ≪≫
      Functor.isoWhiskerRight (NatIso.prod et.symm et.symm) _
  let ti := inverseTensorComparison q tq
  let P₁ := (eqc.functor.mapHomologicalComplex (.up ℤ)).obj P.obj
  let P₂ := (q.inverse.mapHomologicalComplex (.up ℤ)).obj P₁
  have h₂ := sfCbcKFlatTransport q.inverse ti P₁ h₁
  have hf₂ (i : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := (ProEt.topology Y).over W) (R := RV.over W) (P₂.X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (RV.over W) (P₂.X i)).symm
      (sfCbcFlatTransport q.inverse ti (P₁.X i) (hf₁ i))
  have hk := (SheafOfModules.ringedOpen_preserves_flat_resolution.{u + 1, u, u + 1}
    RV W).1 P₂ h₂
  have hf := (SheafOfModules.ringedOpen_preserves_flat_resolution.{u + 1, u, u + 1}
    RV W).2.1 P₂ hf₂
  let ec := NatIso.mapHomologicalComplex extIso (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (F := eqc.functor) (G := q.inverse ⋙ L)
      (Iso.refl _) (.up ℤ)).symm ≪≫
    Functor.isoWhiskerLeft (eqc.functor.mapHomologicalComplex (.up ℤ))
      (Functor.mapHomologicalComplexCompIso (F := q.inverse) (G := L)
        (Iso.refl _) (.up ℤ)).symm
  exact ⟨SheafOfModules.kFlat_iso_independent RV (ec.app P.obj).symm hk,
    fun i ↦ SheafOfModules.flatOnSite_of_iso RV
      ((HomologicalComplex.eval _ _ i).mapIso (ec.app P.obj)).symm (hf i)⟩

end WeilConjectures.IntegralSystemRealization
