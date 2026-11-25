/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorIdentification
import all WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import all WeilConjectures.WeilSheaf.DerivedHom
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.Algebra.Homology.BifunctorHomCone
import all WeilConjectures.Algebra.Homology.BifunctorHomComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement

/-! # Native total tensor models from the canonical localization tensor

Source: Stacks Tags 06YS, 06YT and 0FPT.
(blueprint: lem-sf-native-ordinary-tensor-representatives).
-/

@[expose] public section
set_option autoImplicit false
universe u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

namespace GenericOrdinaryTensor
variable {C : Type a} [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{b} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] {R : C} [MonObj R] [IsCommMonObj R]
  [HasDerivedCategory.{b} (Mod C R)]

local instance : HasLimitsOfSize.{b, b} C := inferInstance
local instance : HasColimitsOfSize.{b, b} C := inferInstance
local instance : HasLimitsOfSize.{b, b} (Mod C R) := inferInstance
local instance : HasColimitsOfSize.{b, b} (Mod C R) := inferInstance

private noncomputable abbrev ordinaryBifunctor : Mod C R ⥤ Mod C R ⥤ Mod C R where
  obj P := Mod.tensorLeft P
  map f := Mod.tensorLeftMap f
  map_id P := Mod.tensorLeftMap_id P
  map_comp f g := Mod.tensorLeftMap_comp f g

private instance : (ordinaryBifunctor (C := C) (R := R)).Additive where
  map_add := by
    intro P Q f g
    exact Mod.tensorLeftMap_add f g

private instance (P : Mod C R) : ((ordinaryBifunctor (C := C) (R := R)).obj P).Additive :=
  inferInstanceAs (Mod.tensorLeft P).Additive

private instance ordinaryHasTotal (P Q : CochainComplex (Mod C R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q ordinaryBifunctor (.up ℤ) := inferInstance

private instance gradedHasTensor (X Y : GradedObject ℤ (Mod C R)) :
    X.HasTensor Y := inferInstance

private instance flippedHasTotal (P Q : CochainComplex (Mod C R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Mod C R)).flip (.up ℤ) :=
  inferInstance

private noncomputable abbrev ordinaryTotal (P Q : CochainComplex (Mod C R) ℤ) :=
  CochainComplex.mapBifunctor P Q ordinaryBifunctor

private abbrev ordinaryFlat (P : CochainComplex (Mod C R) ℤ) : Prop :=
  ∀ N : CochainComplex (Mod C R) ℤ, N.Acyclic → (ordinaryTotal P N).Acyclic

private def ordinarySigned
    (swap : ∀ P Q : CochainComplex (Mod C R) ℤ, ordinaryTotal P Q ≅ ordinaryTotal Q P) :
    Prop :=
  ∀ (P Q : CochainComplex (Mod C R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
    Mod.tensorπ (Q.X q) (P.X p) ≫
        (HomologicalComplex.ιMapBifunctor P Q ordinaryBifunctor
          (.up ℤ) p q n hpq).hom ≫ ((swap P Q).hom.f n).hom =
      (p * q).negOnePow •
        ((β_ (Q.X q).X (P.X p).X).hom ≫ Mod.tensorπ (P.X p) (Q.X q) ≫
          (HomologicalComplex.ιMapBifunctor Q P ordinaryBifunctor
            (.up ℤ) q p n hqp).hom)

private instance nativeTensorRightColimits (X : Mod C R) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Mod C R)).flip.obj X) :=
  preservesColimitsOfShape_of_natIso (F := tensorLeft X)
    (NatIso.ofComponents (fun Z ↦ β_ X Z) (by intros; simp [curriedTensor]))

private noncomputable def ordinaryBicomplexIso (P Q : CochainComplex (Mod C R) ℤ) :
    (((ordinaryBifunctor).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj Q ≅
      ((((curriedTensor (Mod C R)).flip.mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj P).obj Q) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ PrecompositionAux.tensorComponent (Q.X q) (P.X p)) (by
        intro q q' h
        exact ((PrecompositionAux.tensorIso (P.X p)).hom.naturality (Q.d q q')).symm))
    (by
      intro p p' h
      apply HomologicalComplex.Hom.ext
      funext q
      exact (NatTrans.congr_app (OrdinaryModuleHom.tensorRightIso_naturality (P.d p p'))
        (Q.X q)).symm)

private noncomputable def ordinaryTotalIso (P Q : CochainComplex (Mod C R) ℤ) :
    ordinaryTotal P Q ≅ Q ⊗ P :=
  HomologicalComplex₂.total.mapIso (ordinaryBicomplexIso P Q) (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso Q P
      (curriedTensor (Mod C R)) (.up ℤ)

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory (Mod C R)] in
private theorem ordinaryTotalIso_ι_private (P Q : CochainComplex (Mod C R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor P Q (ordinaryBifunctor)
        (.up ℤ) p q n hpq ≫ (ordinaryTotalIso P Q).hom.f n =
      (p * q).negOnePow • ((PrecompositionAux.tensorComponent (Q.X q) (P.X p)).hom ≫
        HomologicalComplex.ιTensorObj Q P q p n (by omega)) := by
  simp only [ordinaryTotalIso, Iso.trans_hom, HomologicalComplex.comp_f,
    ← Category.assoc]
  change (_ ≫ (HomologicalComplex₂.total.map (ordinaryBicomplexIso P Q).hom
    (.up ℤ)).f n) ≫ _ = _
  rw [HomologicalComplex₂.ιTotal_map]
  dsimp only [ordinaryBicomplexIso, HomologicalComplex.Hom.isoOfComponents]
  change ((PrecompositionAux.tensorComponent (Q.X q) (P.X p)).hom ≫
    HomologicalComplex.ιMapBifunctor P Q
      (curriedTensor (Mod C R)).flip (.up ℤ) p q n hpq) ≫ _ = _
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  simp only [Units.smul_def, Preadditive.comp_zsmul, mul_comm p q]
  rfl

/-- Public export of the private `ordinaryTotalIso_ι_private`
(used by `import all` importers; linter.privateModule). -/
alias ordinaryTotalIso_ι := ordinaryTotalIso_ι_private

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory (Mod C R)] in
private theorem ordinaryTotalIso_naturality
    {P Q P' Q' : CochainComplex (Mod C R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f g (ordinaryBifunctor) (.up ℤ) ≫
        (ordinaryTotalIso P' Q').hom =
      (ordinaryTotalIso P Q).hom ≫ (g ⊗ₘ f) := by
  have hc (p q : ℤ) :
      (Mod.tensorLeftMap (f.f p)).app (Q.X q) ≫
          (Mod.tensorLeft (P'.X p)).map (g.f q) ≫
            (PrecompositionAux.tensorComponent (Q'.X q) (P'.X p)).hom =
        (PrecompositionAux.tensorComponent (Q.X q) (P.X p)).hom ≫ (g.f q ⊗ₘ f.f p) := by
    have h₁ : (Mod.tensorLeftMap (f.f p)).app (Q.X q) ≫
        (PrecompositionAux.tensorComponent (Q.X q) (P'.X p)).hom =
      (PrecompositionAux.tensorComponent (Q.X q) (P.X p)).hom ≫ Q.X q ◁ f.f p :=
        NatTrans.congr_app (OrdinaryModuleHom.tensorRightIso_naturality (f.f p)) (Q.X q)
    have h₂ : (Mod.tensorLeft (P'.X p)).map (g.f q) ≫
        (PrecompositionAux.tensorComponent (Q'.X q) (P'.X p)).hom =
      (PrecompositionAux.tensorComponent (Q.X q) (P'.X p)).hom ≫ g.f q ▷ P'.X p :=
        (PrecompositionAux.tensorIso (P'.X p)).hom.naturality (g.f q)
    rw [h₂, ← Category.assoc, h₁, Category.assoc, ← tensorHom_def']
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have hι : HomologicalComplex.ιTensorObj Q P q p n (by omega) ≫ (g ⊗ₘ f).f n =
      (g.f q ⊗ₘ f.f p) ≫ HomologicalComplex.ιTensorObj Q' P' q p n (by omega) := by
    change HomologicalComplex.ιMapBifunctor Q P (curriedTensor (Mod C R))
        (.up ℤ) q p n (by change q + p = n; omega) ≫
          (HomologicalComplex.mapBifunctorMap g f (curriedTensor (Mod C R)) (.up ℤ)).f n = _
    rw [HomologicalComplex.ι_mapBifunctorMap]
    change (g.f q ▷ P.X p) ≫ (Q'.X q ◁ f.f p) ≫ _ = _
    rw [← Category.assoc, ← MonoidalCategory.tensorHom_def]
  simp only [HomologicalComplex.comp_f, ← Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [Category.assoc, ordinaryTotalIso_ι_private, Units.smul_def,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, hι]
  simpa only [ordinaryBifunctor, Category.assoc] using
    congrArg (fun k ↦ ((p * q).negOnePow : ℤ) •
      (k ≫ HomologicalComplex.ιTensorObj Q' P' q p n (by omega))) (hc p q)

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory (Mod C R)] in
private theorem ordinaryKFlat (P : CochainComplex (Mod C R) ℤ) (hP : ordinaryFlat P) :
    (HomotopyCategory.quasiIso (Mod C R) (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ _).obj P) := by
  apply RingedDerivedNative.kFlat_of_acyclic P
  intro N hN n
  exact (hP N hN n).of_iso (ordinaryTotalIso P N)

private noncomputable def ordinaryModel (P Q : CochainComplex (Mod C R) ℤ) (hP : ordinaryFlat P) :
    DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
      DerivedCategory.Q.obj (ordinaryTotal P Q) := by
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q Q P) :=
    RingedDerivedNative.localization_isIso_mu Q P (Or.inr (ordinaryKFlat P hP))
  exact asIso (Functor.LaxMonoidal.μ DerivedCategory.Q Q P) ≪≫
    DerivedCategory.Q.mapIso (ordinaryTotalIso P Q).symm

private theorem ordinaryModel_naturality_private (P Q P' Q' : CochainComplex (Mod C R) ℤ)
    (hP : ordinaryFlat P) (hP' : ordinaryFlat P')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫
        (ordinaryModel P' Q' hP').hom =
      (ordinaryModel P Q hP).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap f g (ordinaryBifunctor) (.up ℤ)) := by
  have hi : (g ⊗ₘ f) ≫ (ordinaryTotalIso P' Q').inv =
      (ordinaryTotalIso P Q).inv ≫
        HomologicalComplex.mapBifunctorMap f g (ordinaryBifunctor) (.up ℤ) := by
    apply (cancel_epi (ordinaryTotalIso P Q).hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← ordinaryTotalIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Q Q' P' ≫
      DerivedCategory.Q.map (ordinaryTotalIso P' Q').inv) =
    (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
      DerivedCategory.Q.map (ordinaryTotalIso P Q).inv) ≫ _
  rw [← Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc,
    ← Functor.map_comp, hi, Functor.map_comp, Category.assoc]

/-- Public export of the private `ordinaryModel_naturality_private`
(used by `import all` importers; linter.privateModule). -/
alias ordinaryModel_naturality := ordinaryModel_naturality_private

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory (Mod C R)] in
private theorem ordinaryTotalIso_inv_ι (P Q : CochainComplex (Mod C R) ℤ)
    (p q n : ℤ) (hqp : q + p = n) :
    HomologicalComplex.ιTensorObj Q P q p n hqp ≫
        (ordinaryTotalIso P Q).inv.f n =
      (p * q).negOnePow • ((PrecompositionAux.tensorComponent (Q.X q) (P.X p)).inv ≫
        HomologicalComplex.ιMapBifunctor P Q (ordinaryBifunctor)
          (.up ℤ) p q n (by change p + q = n; omega)) := by
  simp only [ordinaryTotalIso, Iso.trans_inv, HomologicalComplex.comp_f,
    ← Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorFlipIso_inv]
  simp only [Units.smul_def, Preadditive.zsmul_comp]
  dsimp only [HomologicalComplex₂.total.mapIso]
  rw [HomologicalComplex₂.ιTotal_map]
  simp only [mul_comm p q]
  rfl

private noncomputable def ordinarySwap (P Q : CochainComplex (Mod C R) ℤ) :
    ordinaryTotal P Q ≅ ordinaryTotal Q P :=
  ordinaryTotalIso P Q ≪≫ (β_ Q P) ≪≫ (ordinaryTotalIso Q P).symm

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory (Mod C R)] in
private theorem ordinarySwap_ι (P Q : CochainComplex (Mod C R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor P Q (ordinaryBifunctor)
        (.up ℤ) p q n hpq ≫ (ordinarySwap P Q).hom.f n =
      (p * q).negOnePow • ((PrecompositionAux.tensorComponent (Q.X q) (P.X p)).hom ≫
        (β_ (Q.X q) (P.X p)).hom ≫ (PrecompositionAux.tensorComponent (P.X p) (Q.X q)).inv ≫
          HomologicalComplex.ιMapBifunctor Q P (ordinaryBifunctor)
            (.up ℤ) q p n (by change q + p = n; omega)) := by
  simp only [ordinarySwap, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.comp_f,
    ← Category.assoc]
  rw [ordinaryTotalIso_ι_private]
  simp only [Units.smul_def, Preadditive.zsmul_comp, Category.assoc]
  have hb : HomologicalComplex.ιTensorObj Q P q p n (by omega) ≫
      (β_ Q P).hom.f n ≫ (ordinaryTotalIso Q P).inv.f n =
      (((q * p).negOnePow : ℤ) • ((β_ (Q.X q) (P.X p)).hom ≫
        HomologicalComplex.ιTensorObj P Q p q n hpq)) ≫
          (ordinaryTotalIso Q P).inv.f n :=
    CochainComplex.Monoidal.ι_braiding_hom_assoc (K := Q) (L := P) q p n (by omega) _
  rw [hb]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [ordinaryTotalIso_inv_ι]
  simp only [Units.smul_def, Preadditive.comp_zsmul, mul_comm q p, smul_smul,
    ← Units.val_mul, Int.units_mul_self, mul_one]

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory (Mod C R)] in
private theorem ordinarySwap_signed_private :
    ordinarySigned (ordinarySwap (C := C) (R := R)) := by
  intro P Q p q n hpq hqp
  have hi : Mod.tensorObjπ (P.X p) (Q.X q) ≫
      (PrecompositionAux.tensorComponent (P.X p) (Q.X q)).inv.hom =
        Mod.tensorπ (P.X p) (Q.X q) := by
    rw [← PrecompositionAux.tensorComponent_π, Category.assoc, ← Mod.comp_hom',
      Iso.hom_inv_id, Mod.id_hom', Category.comp_id]
  change Mod.tensorπ (Q.X q) (P.X p) ≫
    (HomologicalComplex.ιMapBifunctor P Q (ordinaryBifunctor)
      (.up ℤ) p q n hpq ≫ (ordinarySwap P Q).hom.f n).hom = _
  rw [ordinarySwap_ι]
  simp only [Units.smul_def, Mod.zsmul_hom, Mod.comp_hom', Preadditive.comp_zsmul,
    ← Category.assoc]
  rw [PrecompositionAux.tensorComponent_π]
  rw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX]
  simp only [Category.assoc]
  rw [← Category.assoc (Mod.tensorObjπ (P.X p) (Q.X q)), hi]

/-- Public export of the private `ordinarySwap_signed_private`
(used by `import all` importers; linter.privateModule). -/
alias ordinarySwap_signed := ordinarySwap_signed_private

private theorem ordinaryModel_braiding_private (P Q : CochainComplex (Mod C R) ℤ)
    (hP : ordinaryFlat P) (hQ : ordinaryFlat Q) :
    letI := RingedDerivedNative.derivedSymmetric (A := Mod C R)
    (β_ (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)).hom ≫
        (ordinaryModel Q P hQ).hom =
      (ordinaryModel P Q hP).hom ≫ DerivedCategory.Q.map (ordinarySwap P Q).hom := by
  let := RingedDerivedNative.derivedSymmetric (A := Mod C R)
  let := RingedDerivedNative.localizationLaxBraided (A := Mod C R)
  change _ ≫ (Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫
      DerivedCategory.Q.map (ordinaryTotalIso Q P).inv) =
    (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
      DerivedCategory.Q.map (ordinaryTotalIso P Q).inv) ≫ _
  simp only [ordinarySwap, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← DerivedCategory.Q.map_comp_assoc, Iso.inv_hom_id,
    DerivedCategory.Q.map_id, Category.id_comp, ← Category.assoc]
  rw [← Functor.LaxBraided.braided]
  exact Category.assoc _ _ _

/-- Public export of the private `ordinaryModel_braiding_private`
(used by `import all` importers; linter.privateModule). -/
alias ordinaryModel_braiding := ordinaryModel_braiding_private

end GenericOrdinaryTensor

end AlgebraicGeometry.ProEtaleWeilSheaf
