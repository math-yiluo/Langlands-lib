/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomNaturality
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
import all WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomEvaluation
import all WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryTensorInverseEvaluation
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRelativeTensorIdentification
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.AlgebraicGeometry.Adic.AdicModuleHomComparisonCore
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Symmetry of the evaluation-normalized canonical ordinary comparison

Source: Stacks 03EK and 03EO; inverse Hom mates and pure tensor generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures

set_option maxHeartbeats 2000000 in
-- The lifted pushforward presentation requires substantial definitional reduction.
private theorem smallSite_counit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u + 1})
    (N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (SheafOfModules.SmallSite.equivalence J R).counitIso.hom.app N = 𝟙 N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change N.val.map (𝟙 U) m = m
  exact ConcreteCategory.congr_hom (N.val.map_id U) m

private theorem composite_counit_map
    {B C D : Type*} [Category B] [Category C] [Category D]
    (A : B ≌ D) (E : C ≌ D) (M : C) :
    E.functor.map ((A.trans E.symm).counitIso.hom.app M) =
      E.counitIso.hom.app (A.functor.obj (A.inverse.obj (E.functor.obj M))) ≫
        A.counitIso.hom.app (E.functor.obj M) := by
  simp only [CategoryTheory.Equivalence.trans, CategoryTheory.Equivalence.symm,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Functor.map_comp]
  rw [← E.counit_app_functor]
  erw [E.inverse.map_id, E.functor.map_id, Category.comp_id]
  exact E.counit_naturality (A.counitIso.hom.app (E.functor.obj M))

section Ringed
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

-- Compare the explicit sheaf and module category presentations.
private theorem left_uncurry_pure
    (P Q I : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I) (V : Cᵒᵖ)
    (x : P.val.obj V) (y : Q.val.obj V) :
    (((SheafOfModules.tensorHomAdjunction R P).homEquiv Q I).symm f).val.app V
        (CochainPullback.moduleTmul P Q V x y) =
      ((f.val.app V y).app (op (Over.mk (𝟙 V.unop)))) x := by
  delta SheafOfModules.tensorHomAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  let e := SheafOfModules.tensorHomEquiv (R := R) P Q I
  let e' := PresheafOfModules.homObjEquiv (R := R.obj) P.val Q.val I.val
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have he := congrArg SheafOfModules.Hom.val (e.apply_symm_apply f)
  change e' (adj.homEquiv _ I
    ((SheafOfModules.tensorObjIsoSheafification P Q).inv ≫ e.symm f)) = f.val at he
  have he' := e'.eq_symm_apply.mpr he
  rw [Adjunction.homEquiv_unit] at he'
  exact congrArg (fun k ↦ k.app V (x ⊗ₜ[R.obj.obj V] y)) he'

-- Compare the explicit sheaf and module category presentations.
private theorem right_uncurry_pure
    (P Q I : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I) (V : Cᵒᵖ)
    (x : P.val.obj V) (y : Q.val.obj V) :
    ((β_ Q P).hom ≫
      ((SheafOfModules.tensorHomAdjunction R P).homEquiv Q I).symm f).val.app V
        (CochainPullback.moduleTmul Q P V y x) =
      ((f.val.app V y).app (op (Over.mk (𝟙 V.unop)))) x := by
  exact (congrArg
    (fun z ↦ (((SheafOfModules.tensorHomAdjunction R P).homEquiv Q I).symm f).val.app V z)
    (CochainPullback.moduleTmul_braiding Q P V y x)).trans
      (left_uncurry_pure R P Q I f V x y)
end Ringed

namespace AlgebraicGeometry.ProEtale
variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

private theorem native_uncurry_pure (P Q I : AdicSheaf l Y)
    (f : Q ⟶ (AdicSheaf.ihom P).obj I) (V : Y.ProEtᵒᵖ)
    (y : Q.X.obj.obj V) (x : P.X.obj.obj V) :
    adicComparisonEval P I V (f.hom.hom.app V y) x =
      (((Mod.ihomAdjunction P).homEquiv Q I).symm f).hom.hom.app V
        (adicComparisonTmul Q P V y x) := by
  have h := Mod.uncurryHom_eq f
  have hh := congrArg (fun k ↦ k.hom.app V (sectionPair Q.X P.X V y x)) h
  simp only [Mod.uncurryHom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, ModuleCat.comp_apply, ← tensorHom_id] at hh
  erw [sectionPair_map] at hh
  simpa only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply, adicComparisonEval, adicComparisonTmul, sectionPair] using hh

private theorem native_unit_pure (P Q : AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
    (y : Q.X.obj.obj V) (x : P.X.obj.obj V) :
    adicComparisonEval P ((Mod.tensorLeft P).obj Q) V
        ((((Mod.ihomAdjunction P).homEquiv Q _ (𝟙 _)).hom.hom.app V y)) x =
      adicComparisonTmul Q P V y x := by
  have h := native_uncurry_pure P Q ((Mod.tensorLeft P).obj Q)
    ((Mod.ihomAdjunction P).homEquiv Q _ (𝟙 _)) V y x
  simpa using h


private def canonicalInverseHom (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : AdicModuleHomComparisonCore l Y) :
    Functor.uncurry.obj (ProEtaleWeilSheaf.ordinaryIhomBifunctor l Y) ⋙
        (NativeFrobenius.equivalence Y l).inverse ≅
      (NativeFrobenius.equivalence Y l).inverse.op.prod
        (NativeFrobenius.equivalence Y l).inverse ⋙
          Functor.uncurry.obj
            (SheafOfModules.homFunctor (R := NativeFrobenius.ring Y l)) :=
  HomComparison.inverseHomComparison (NativeFrobenius.equivalence Y l)
    (Functor.uncurry.obj (ProEtaleWeilSheaf.ordinaryIhomBifunctor l Y))
    (Functor.uncurry.obj (SheafOfModules.homFunctor (R := NativeFrobenius.ring Y l)))
    (NatIso.ofComponents
      (fun MN ↦ NativeFrobenius.homComparison Y l H MN.1.unop MN.2)
      (fun fg ↦ NativeFrobenius.homComparison_naturality Y l H fg.1.unop fg.2))

-- Compare the explicit sheaf and module category presentations.
private theorem canonical_inverseHom_evaluation
    (H : AdicModuleHomComparisonCore l Y) (P I : AdicSheaf l Y)
    (V : Y.ProEtᵒᵖ) (z : ((AdicSheaf.ihom P).obj I).X.obj.obj V)
    (x : P.X.obj.obj V) :
    ((((canonicalInverseHom l Y H).hom.app (op P, I)).val.app
        (op (AsSmall.up.obj V.unop)) z).app
          (op (Over.mk (𝟙 (AsSmall.up.obj V.unop))))) x =
      adicComparisonEval P I V z x := by
  exact ProEtaleWeilSheaf.inverse_comparison_evaluation l Y H P I V z x

-- Compare the explicit sheaf and module category presentations.
private theorem canonical_inverse_tensor_pure
    (H : AdicModuleHomComparisonCore l Y)
    (d : ProEtaleWeilSheaf.OrdinaryRingedTensorUnderivedData l Y
      (WeilFrobeniusAction.topology Y) (NativeFrobenius.ring Y l)
      (NativeFrobenius.equivalence Y l).symm (canonicalInverseHom l Y H))
    (P Q : AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
    (y : Q.X.obj.obj V) (x : P.X.obj.obj V) :
    (d.underived P Q).inv.val.app (op (AsSmall.up.obj V.unop))
      (CochainPullback.moduleTmul
        ((NativeFrobenius.equivalence Y l).inverse.obj Q)
        ((NativeFrobenius.equivalence Y l).inverse.obj P)
        (op (AsSmall.up.obj V.unop)) y x) =
      adicComparisonTmul Q P V y x := by
  let R := NativeFrobenius.ring Y l
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  let _ := SheafOfModules.symmetricCategory R
  have ht := d.uncurry P Q ((Mod.tensorLeft P).obj Q)
    ((Mod.ihomAdjunction P).homEquiv Q _ (𝟙 _))
  simp only [Equiv.symm_apply_apply] at ht
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht
  have hv := congrArg (fun f ↦ f.val.app (op (AsSmall.up.obj V.unop))
    (CochainPullback.moduleTmul
      ((NativeFrobenius.equivalence Y l).inverse.obj Q)
      ((NativeFrobenius.equivalence Y l).inverse.obj P)
      (op (AsSmall.up.obj V.unop)) y x)) ht
  have hv := hv.trans (right_uncurry_pure R
    ((NativeFrobenius.equivalence Y l).inverse.obj P)
    ((NativeFrobenius.equivalence Y l).inverse.obj Q)
    ((NativeFrobenius.equivalence Y l).inverse.obj ((Mod.tensorLeft P).obj Q))
    ((NativeFrobenius.equivalence Y l).inverse.map
        ((Mod.ihomAdjunction P).homEquiv Q _ (𝟙 _)) ≫
      (canonicalInverseHom l Y H).hom.app (op P, (Mod.tensorLeft P).obj Q))
    (op (AsSmall.up.obj V.unop)) x y)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hv
  change (d.underived P Q).inv.val.app (op (AsSmall.up.obj V.unop))
      (CochainPullback.moduleTmul
        ((NativeFrobenius.equivalence Y l).inverse.obj Q)
        ((NativeFrobenius.equivalence Y l).inverse.obj P)
        (op (AsSmall.up.obj V.unop)) y x) =
    ((((canonicalInverseHom l Y H).hom.app (op P, (Mod.tensorLeft P).obj Q)).val.app
      (op (AsSmall.up.obj V.unop))
      (((Mod.ihomAdjunction P).homEquiv Q _ (𝟙 _)).hom.hom.app V y)).app
        (op (Over.mk (𝟙 (AsSmall.up.obj V.unop))))) x at hv
  exact hv.trans ((canonical_inverseHom_evaluation H P ((Mod.tensorLeft P).obj Q)
    V (((Mod.ihomAdjunction P).homEquiv Q _ (𝟙 _)).hom.hom.app V y) x).trans
      (native_unit_pure P Q V y x))

private theorem native_swap_pure (P Q : AdicSheaf l Y)
    (s : (Mod.tensorLeft Q).obj P ⟶ (Mod.tensorLeft P).obj Q)
    (hs : Mod.tensorπ P Q ≫ s.hom = (β_ P.X Q.X).hom ≫ Mod.tensorπ Q P)
    (V : Y.ProEtᵒᵖ) (x : P.X.obj.obj V) (y : Q.X.obj.obj V) :
    s.hom.hom.app V (adicComparisonTmul P Q V x y) =
      adicComparisonTmul Q P V y x := by
  have h := congrArg (fun f ↦ f.hom.app V (sectionPair P.X Q.X V x y)) hs
  change s.hom.hom.app V (adicComparisonTmul P Q V x y) =
    (Mod.tensorπ Q P).hom.app V
      ((β_ P.X Q.X).hom.hom.app V (sectionPair P.X Q.X V x y)) at h
  rw [sectionPair_braiding] at h
  exact h

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf
open ProEtale

private theorem pure_tensor_ext
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (M N L : RingedTensorModules.{u, u, u} J R)
    {f g : (SheafOfModules.monoidalCategory R).tensorObj M N ⟶ L}
    (h : ∀ V x y, f.val.app V (CochainPullback.moduleTmul M N V x y) =
      g.val.app V (CochainPullback.moduleTmul M N V x y)) : f = g := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  apply (adj.homEquiv (M.val ⊗ N.val) L).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h V x y

-- Compare the explicit canonical functors and tensor instances.
/-- The normalized canonical inverse comparison preserves the actual balanced swap.
Source: Stacks 03EK and 03EO; evaluation on the identity slice and pure tensors.
(blueprint: new-sf-canonical-ordinary-tensor-symmetry).

Proof: inverse Hom transport evaluated on the identity slice is native evaluation,
by the forward evaluation identity and the equivalence counit formula. Apply the
mate equation to the adjunct of the identity of the old relative tensor. This
computes the inverse comparison on pure tensors. The ordinary quotient comparison
and its standard braiding give a balanced swap. Both sides of its comparison
square agree on pure tensors, so sheafification and tensor extensionality give the
square. All statements are underived and allow zero modules and the empty site.
-/
theorem canonical_ordinary_tensor_symmetry
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : AdicModuleHomComparisonCore l Y) :
    let E := NativeFrobenius.equivalence Y l
    let R := NativeFrobenius.ring Y l
    let h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) ⋙ E.functor ≅
        E.functor.op.prod E.functor ⋙ Functor.uncurry.obj (ordinaryIhomBifunctor l Y) :=
      NatIso.ofComponents
        (fun MN ↦ NativeFrobenius.homComparison Y l H MN.1.unop MN.2)
        (fun fg ↦ NativeFrobenius.homComparison_naturality Y l H fg.1.unop fg.2)
    let K := HomComparison.inverseHomComparison E
      (Functor.uncurry.obj (ordinaryIhomBifunctor l Y))
      (Functor.uncurry.obj (SheafOfModules.homFunctor (R := R))) h
    ∀ (d : OrdinaryRingedTensorUnderivedData l Y (WeilFrobeniusAction.topology Y)
        R E.symm K) (P Q : AdicSheaf l Y),
      ∃ s : ((ordinaryTensorBifunctor l Y).obj Q).obj P ⟶
          ((ordinaryTensorBifunctor l Y).obj P).obj Q,
        (letI := SheafOfModules.isMonoidal_W_independentCoefficients R
         letI := SheafOfModules.monoidalCategory R
         letI := SheafOfModules.symmetricCategory R
         E.inverse.map s ≫ (d.underived P Q).hom =
           (d.underived Q P).hom ≫ (β_ (E.inverse.obj P) (E.inverse.obj Q)).hom) ∧
        Mod.tensorπ P Q ≫ s.hom = (β_ P.X Q.X).hom ≫ Mod.tensorπ Q P := by
  dsimp only
  intro d P Q
  let E := NativeFrobenius.equivalence Y l
  let R := NativeFrobenius.ring Y l
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  let _ := SheafOfModules.symmetricCategory R
  obtain ⟨b, hb⟩ := ordinary_relative_tensor_identification l Y
  let s := (b Q P).hom ≫ (β_ P Q).hom ≫ (b P Q).inv
  have hbinv : Mod.tensorObjπ Q P ≫ (b P Q).inv.hom = Mod.tensorπ Q P := by
    rw [← hb P Q, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id]
    rfl
  have hs : Mod.tensorπ P Q ≫ s.hom = (β_ P.X Q.X).hom ≫ Mod.tensorπ Q P := by
    change Mod.tensorπ P Q ≫
      ((b Q P).hom.hom ≫ (β_ P Q).hom.hom ≫ (b P Q).inv.hom) = _
    simp only [← Category.assoc, hb Q P, Mod.braiding_hom_hom,
      Mod.tensorObjπ_braidingHomX]
    rw [Category.assoc, hbinv]
  refine ⟨s, ?_, hs⟩
  have hsq : (d.underived Q P).inv ≫ E.inverse.map s =
      (β_ (E.inverse.obj P) (E.inverse.obj Q)).hom ≫ (d.underived P Q).inv := by
    apply pure_tensor_ext R (E.inverse.obj P) (E.inverse.obj Q) _
    intro V x y
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    let W := op (AsSmall.down.obj V.unop)
    have h1 := canonical_inverse_tensor_pure H d Q P W x y
    have h2 := canonical_inverse_tensor_pure H d P Q W y x
    have hβ := CochainPullback.moduleTmul_braiding
      (E.inverse.obj P) (E.inverse.obj Q) V x y
    change s.hom.hom.app W
      ((d.underived Q P).inv.val.app V
        (CochainPullback.moduleTmul (E.inverse.obj P) (E.inverse.obj Q) V x y)) = _
    calc
      _ = s.hom.hom.app W (adicComparisonTmul P Q W x y) :=
        congrArg (fun z ↦ s.hom.hom.app W z) h1
      _ = adicComparisonTmul Q P W y x := native_swap_pure P Q s hs W x y
      _ = (d.underived P Q).inv.val.app V
          (CochainPullback.moduleTmul (E.inverse.obj Q) (E.inverse.obj P) V y x) := h2.symm
      _ = _ := congrArg (fun z ↦ (d.underived P Q).inv.val.app V z) hβ.symm
  apply (cancel_epi (d.underived Q P).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hsq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
