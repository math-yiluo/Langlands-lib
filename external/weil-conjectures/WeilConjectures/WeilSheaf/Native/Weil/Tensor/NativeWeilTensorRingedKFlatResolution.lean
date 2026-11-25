/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedChainData
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.WeilSheaf.Constant

/-! # Native K-flat resolutions

The native acyclic-test K-flat predicate is resolving: every complex admits a
quasi-isomorphism from a complex satisfying the predicate.  This is the density
input for the localization equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]

set_option synthInstance.maxSize 4096 in
/-- The normalized native tensor admits functorial K-flat replacements.
Source: Stacks 06YS, the unbounded K-flat replacement construction.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-resolution)

Use the functorial flat resolution on the ringed presentation, whose sum total
is K-flat. Conjugate its resolution functor and augmentation by the additive
native equivalence. The normalized total-tensor comparison transports the
acyclic-test K-flat property back to native complexes; exactness of the inverse
equivalence transports the quasi-isomorphism. Functoriality, rather than a strict
fraction calculus on complexes, supplies the subsequent localization argument.
-/
theorem native_weil_tensor_ringed_kflat_resolution
    (b : NativeWeilTensorRingedBridge k₀ l X) (adj : T ⊣₂ ihomBifunctor k₀ l X) :
    ∃ (ρ : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ ⥤
        CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (ε : ρ ⟶ 𝟭 _),
      (∀ K, NativeTensorKFlat k₀ l X T (ρ.obj K)) ∧ (∀ K, QuasiIso (ε.app K)) := by
  classical
  let A := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  let : HasLimitsOfSize.{0, 0} A :=
    hasLimitsOfSizeShrink.{0, 0, u + 1, u + 1} A
  let : HasColimitsOfSize.{0, 0} A :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} A
  let : ∀ (Y Z : GradedObject ℤ A), Y.HasTensor Z := fun _ _ ↦ inferInstance
  let : ∀ (V W Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt V W Y Z :=
    fun _ _ _ _ ↦ inferInstance
  let : ∀ (W Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor W Y Z :=
    fun _ _ _ ↦ inferInstance
  let : ∀ (W Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ W Y Z :=
    fun _ _ _ ↦ inferInstance
  let : MonoidalClosed A := SheafOfModules.monoidalClosed_kfi (R := b.R)
  let : MonoidalPreadditive A := SheafOfModules.monoidalPreadditive_kfi b.R
  let (M : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    SheafOfModules.cochainTensorLeftPreservesColimits b.R M
  let (M : A) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    SheafOfModules.cochainTensorRightPreservesColimits b.R M
  let : Abelian.HasFunctorialFlatResolution A :=
    SheafOfModules.hasFunctorialFlatResolution_kfi b.R
  let : HasExactColimitsOfShape ℤ A := SheafOfModules.hasExactColimits_int_kfi b.R
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution A).some.reduced
  have flat (K : CochainComplex A ℤ)
      (hK : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K) :
      CochainComplex.IsKFlatIndependentCoefficients (R := b.R) K := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic] at hK
    intro Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (Z ⊗ K)).mp
        (hK _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mpr hZ)).2
  obtain ⟨U⟩ := native_weil_tensor_ringed_underived_data b T adj
  let sign (p q : ℤ) {Y Z : A} (f : Y ⟶ Z) : Y ⟶ Z :=
    letI : AddCommGroup (Y ⟶ Z) := Preadditive.homGroup Y Z
    ZSMul.zsmul ((p * q).negOnePow : ℤ) f
  obtain ⟨c⟩ := native_weil_tensor_ringed_chain_data b T adj U sign
    (fun _ _ _ _ _ ↦ rfl)
  let e := b.native.mapHomologicalComplex (.up ℤ)
  let ρ := e.functor ⋙ Λ.resolutionFunctor ⋙ e.inverse
  let ε : ρ ⟶ 𝟭 _ :=
    Functor.whiskerRight (Functor.whiskerLeft e.functor Λ.resolutionNatTrans) e.inverse ≫
      e.unitIso.inv
  refine ⟨ρ, ε, ?_, ?_⟩
  · intro K N hN
    let R := Λ.resolutionFunctor.obj (e.functor.obj K)
    have hR := flat R (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le _)
    have ht := hR (e.functor.obj N) (hN.map b.native.functor)
    let t := coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R
    let i := c.chain (ρ.obj K) N ≪≫
      t.mapIso ((Iso.refl (e.functor.obj N)).prod (e.counitIso.app R))
    have hm : (e.functor.obj (CochainComplex.mapBifunctor (ρ.obj K) N T)).Acyclic :=
      fun n ↦ (ht n).of_iso i.symm
    have hu := hm.map b.native.inverse
    exact fun n ↦ (hu n).of_iso (e.unitIso.app _).symm
  · intro K
    dsimp only [ε, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    have : QuasiIso (Λ.resolutionNatTrans.app (e.functor.obj K)) := inferInstance
    have : QuasiIso (e.inverse.map (Λ.resolutionNatTrans.app (e.functor.obj K))) :=
      inferInstanceAs (QuasiIso ((b.native.inverse.mapHomologicalComplex (.up ℤ)).map
        (Λ.resolutionNatTrans.app (e.functor.obj K))))
    infer_instance

end AlgebraicGeometry.ProEtaleWeilSheaf
