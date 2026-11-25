/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex
public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryKFlatLocalization
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison

/-! # The normalized inverse binary forgetting square

Source: Stacks 06YU, 0FPT; direct native tensor transport on representatives.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory DerivedCategory.Q instCategoryDerivedCategory
  nativeWeilRingedMonoidal nativeWeilRingedTensorModel NativeOrdinaryKFlat NativeTensorKFlat
  nativeRingedAssociatorComplex nativeRingedTripleLeft nativeRingedTripleRight
  nativeWeilRingedTensorComplexModel

-- Elaborate the explicit binary comparison without unfolding localization structures.
/-- The inverse native binary model square under ordinary canonical normalization.
Source: Stacks 06YU, 0FPT
(blueprint: lem-sf-native-weil-ringed-forget-binary).
Proof: rewrite the supplied representative square by its normalized ordinary
model. Invert the native model and the canonical localization tensorator, then
compose with the signed total comparison. -/
theorem nativeRingedTensorModel_forget_binary
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q))
    (b : NativeWeilTensorRingedBridge k₀ l X)
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (ordinaryModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (_ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P),
          (MonoidalCategory.tensor _).obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj
              (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q))
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P)
    (hmodel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
        (_hQ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q),
        HEq (ordinaryModel P Q hP).hom
          (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
            DerivedCategory.Q.map (κ P Q).inv))
    (t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ MonoidalCategory.tensor _)
    (hforget : (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P),
    (nativeForget k₀ l X).map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
            (CochainComplex.mapBifunctor P Q T)) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        (MonoidalCategory.tensor _).map
          (X := ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q),
            (nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))
          (Y := (DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
            DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)))
          (Prod.mkHom
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app Q)
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ordinaryModel
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (native_weil_tensor_forget_kflat k₀ l X T chain P hP)).hom))
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q) :
    letI := nativeWeilRingedMonoidal b SB
    let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
    let V := U.mapHomologicalComplex (.up ℤ)
    let F := nativeForget k₀ l X
    let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
    let qA := DerivedCategory.Q (C := ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    letI : Functor.LaxMonoidal qA := inferInstance
    let ε := U.mapDerivedCategoryFactors
    let c (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
        V.obj (nativeTensorComplex T P Q) ≅ V.obj P ⊗ V.obj Q :=
      chain Q P ≪≫ κ (V.obj Q) (V.obj P)
      let := nativeOrdinaryKFlat_isIso_mu l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber κ (V.obj P) (V.obj Q)
        (Or.inr (native_weil_tensor_forget_kflat k₀ l X T chain Q hQ))
      F.map (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).inv ≫
          t.hom.app (q.obj P, q.obj Q) ≫ (ε.hom.app P ⊗ₘ ε.hom.app Q) =
        ε.hom.app (nativeTensorComplex T P Q) ≫ qA.map (c P Q).hom ≫
          inv (Functor.LaxMonoidal.μ qA (V.obj P) (V.obj Q)) := by
  classical
  letI := nativeWeilRingedMonoidal b SB
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let V := U.mapHomologicalComplex (.up ℤ)
  let F := nativeForget k₀ l X
  let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
  let qA := DerivedCategory.Q (C := ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  letI : Functor.LaxMonoidal qA := inferInstance
  let ε := U.mapDerivedCategoryFactors
  let c (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
      V.obj (nativeTensorComplex T P Q) ≅ V.obj P ⊗ V.obj Q :=
    chain Q P ≪≫ κ (V.obj Q) (V.obj P)
  have hflat (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P) :=
    native_weil_tensor_forget_kflat k₀ l X T chain P hP
  let := nativeOrdinaryKFlat_isIso_mu l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber κ (V.obj P) (V.obj Q)
    (Or.inr (hflat Q hQ))
  let i := nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ
  have h := hforget Q P hQ
  have hm := eq_of_heq (hmodel (V.obj Q) (V.obj P) (hflat Q hQ) (hflat P hP))
  rw [hm] at h
  change F.map i.hom ≫ ε.hom.app (nativeTensorComplex T P Q) ≫
      qA.map (chain Q P).hom =
    t.hom.app (q.obj P, q.obj Q) ≫ (ε.hom.app P ⊗ₘ ε.hom.app Q) ≫
      Functor.LaxMonoidal.μ qA (V.obj P) (V.obj Q) ≫
        qA.map (κ (V.obj Q) (V.obj P)).inv at h
  simpa only [c, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] using
    inverseModel_square F i (ε.hom.app (nativeTensorComplex T P Q))
      (qA.map (chain Q P).hom) (qA.mapIso (κ (V.obj Q) (V.obj P)))
      (t.hom.app (q.obj P, q.obj Q) ≫ (ε.hom.app P ⊗ₘ ε.hom.app Q))
      (Functor.LaxMonoidal.μ qA (V.obj P) (V.obj Q))
      (by simpa only [Category.assoc, Functor.mapIso_inv] using h)

end AlgebraicGeometry.ProEtaleWeilSheaf
