/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorRepresentatives
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

/-! # Retaining the canonical localization normalization of ordinary tensor models

Source: Stacks 06YS, 06YT, 0FPT. The tensor model is the existing explicit
localization tensorator, followed by the inverse signed total comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Retain the summand formula and the localization tensorator of the canonical model.

Source: Stacks 06YS, 06YT, 0FPT; ordinary tensor transport, step 1.
(blueprint: lem-sf-native-ordinary-canonical-tensor-representatives).

Proof: use the already constructed ordinaryModel, ordinarySwap and ordinaryTotalIso.
Their naturality, signed swap and braiding equations are the existing proved ones.
Precompose ordinaryTotalIso_ι with the balanced quotient tensorπ; tensorComponent_π
identifies the remaining underived comparison with tensorObjπ. The formula for the
derived model is its definition, so it also holds on pairs of K-flat complexes.
No associator identity is inferred from an arbitrarily chosen adjunction. -/
theorem native_ordinary_canonical_tensor_representatives (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    ∃ β : SymmetricCategory (DerivedCategory (ProEtale.AdicSheaf l Y)),
    ∃ model : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      NativeOrdinaryKFlat l Y P →
        (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
          DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q)),
    ∃ swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      ordinaryTensorTotal l Y P Q ≅ ordinaryTensorTotal l Y Q P,
      (∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P) (hP' : NativeOrdinaryKFlat l Y P')
        (f : P ⟶ P') (g : Q ⟶ Q'),
        (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
          (model P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g (ordinaryTensorBifunctor l Y) (.up ℤ))) ∧
      NativeOrdinarySignedSwap l Y swap ∧
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P) (hQ : NativeOrdinaryKFlat l Y Q),
        (β.toBraidedCategory.braiding (DerivedCategory.Q.obj Q)
            (DerivedCategory.Q.obj P)).hom ≫ (model Q P hQ).hom =
          (model P Q hP).hom ≫ DerivedCategory.Q.map (swap P Q).hom) ∧
    (∃ κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
        ordinaryTensorTotal l Y P Q ≅ Q ⊗ P,
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
        Mod.tensorπ (Q.X q) (P.X p) ≫
            (HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
              (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
          (p * q).negOnePow •
            (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) ∧
      ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P) (_hQ : NativeOrdinaryKFlat l Y Q),
        HEq (model P Q hP).hom
          (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
            DerivedCategory.Q.map (κ P Q).inv)) := by
  refine ⟨RingedDerivedNative.derivedSymmetric, GenericOrdinaryTensor.ordinaryModel,
    GenericOrdinaryTensor.ordinarySwap, GenericOrdinaryTensor.ordinaryModel_naturality,
    GenericOrdinaryTensor.ordinarySwap_signed, GenericOrdinaryTensor.ordinaryModel_braiding,
    GenericOrdinaryTensor.ordinaryTotalIso, ?_, ?_⟩
  · intro P Q p q n hpq hqp
    change Mod.tensorπ (Q.X q) (P.X p) ≫
      (HomologicalComplex.ιMapBifunctor P Q
        (GenericOrdinaryTensor.ordinaryBifunctor) (.up ℤ) p q n hpq ≫
          (GenericOrdinaryTensor.ordinaryTotalIso P Q).hom.f n).hom = _
    rw [GenericOrdinaryTensor.ordinaryTotalIso_ι]
    simp only [Units.smul_def, Mod.zsmul_hom, Mod.comp_hom', Preadditive.comp_zsmul,
      ← Category.assoc, PrecompositionAux.tensorComponent_π]
  · intro P Q hP hQ
    rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
