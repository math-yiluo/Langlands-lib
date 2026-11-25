/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Balanced association for the finite coefficient-extension models

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures
section ScalarAssociation
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  {R S T : Sheaf J CommRingCat.{max c v r}} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
  (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
  (B : SemilinearSections.ScalarData.{c, v, max c v r} g)
  (D : SemilinearSections.ScalarData.{c, v, max c v r} h)

private theorem tensorSection_smul {f : R ⟶ S}
    (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (b : S.obj.obj U) (x : M.val.obj U) :
    (toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} f M).presheaf).app U
        (b ⊗ₜ[R.obj.obj U, (f.hom.app U).hom] x) =
      b • (show (SheafOfModules.changeOfRings.{v, c, max c v r} f M).val.obj U from (toSheafify J
        (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} f M).presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (f.hom.app U).hom] x)) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{max c v r}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} f M)
  have h := (η.app U).hom.map_smul b
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (f.hom.app U).hom] x)
  change (toSheafify J
      (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} f M).presheaf).app U
        ((b * 1) ⊗ₜ[R.obj.obj U, (f.hom.app U).hom] x) =
      b • (show (SheafOfModules.changeOfRings.{v, c, max c v r} f M).val.obj U from
        (toSheafify J
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} f M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (f.hom.app U).hom] x)) at h
  simpa only [mul_one] using h

private theorem scalarSection_eq_unit {f : R ⟶ S}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
    (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x =
      @id ((A.model.E.obj M).val.obj U)
        ((A.ordinaryAdjunction.unit.app M).val.app U x) := by
  unfold SemilinearSections.scalarExtensionSection
  rw [← A.unit_section M U x]
  erw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl]
  rfl

end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

variable (A : CoefficientExtensionSystems l E L ι W)

/-- Balanced association between iterated and direct finite scalar extension.
Source: integral operations; Stacks 03EK, 03D7
(blueprint: stage3-pur-finite-extension-association).
Proof: compose the ordinary extension/restriction adjunctions. Their right adjoints
are the same restriction along the composite ring map. Uniqueness of the left
adjoint gives a natural isomorphism. Its unit equation identifies its value on
unit tensors. Linearity then gives the stated formula for arbitrary coefficients. -/
theorem coefficientExtensionFiniteAssociation_exists :
    Nonempty (CoefficientExtensionAssociationData l E L ι W A) := by
  classical
  have hd (n : ℕ) :=
    integralScalarReduction_obj l E L ι W n
  have hm (n : ℕ) :=
    fun {M N} (f : M ⟶ N) ↦ integralScalarReduction_map l E L ι W n f
  let (n : ℕ) : (integralScalarReduction l E L ι W n).Additive :=
    integralScalarReduction_additive l E L ι W n
  have ho (n : ℕ) :=
    (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
      (integralScalarRho l E L ι W n)).choose_spec.choose_spec
      (integralScalarReduction l E L ι W n) (hd n) (hm n)
  let ad (n : ℕ) := (ho n).choose
  let ar (n : ℕ) := (scalarReductionExtension_adjunction l E W n).choose
  let ρ (n : ℕ) : SemilinearSections.res (integralScalarQuotientSheafMap l E L ι W n) ⋙
      scalarReductionRestriction l E W n ≅
      SemilinearSections.res (integralScalarRho l E L ι W n) :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App
          ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom
          ((integralScalarQuotientSheafMap l E L ι W n).hom.app U).hom
          ((integralScalarRho l E L ι W n).hom.app U).hom rfl
          (M.val.obj U)).symm) (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  let adj (n : ℕ) := ((ar n).comp (A.levels n).ordinaryAdjunction).ofNatIsoRight (ρ n)
  let a (n : ℕ) := (adj n).leftAdjointUniq (ad n)
  refine ⟨⟨a, ?_⟩⟩
  intro n M U z b x
  have hu := (adj n).unit_leftAdjointUniq_hom_app (ad n) M
  have hx := congrArg (fun f ↦ (f.val.app U) x) hu
  dsimp only [adj, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app] at hx
  change ((a n).hom.app M).val.app U
      (((A.levels n).ordinaryAdjunction.unit.app
        ((scalarReductionExtension l E W n).obj M)).val.app U
          (((ar n).unit.app M).val.app U x)) =
    ((ad n).unit.app M).val.app U x at hx
  have ht := (ho n).choose_spec M ((integralScalarReduction l E L ι W n).obj M)
    (eqToHom (hd n M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at ht
  have he : (integralScalarReductionIso l E L ι W n).inv.app M =
      eqToHom (hd n M).symm := by
    dsimp only [integralScalarReductionIso, eqToIso.inv]
    rw [eqToHom_app]
  have hu' : ((ad n).unit.app M).val.app U x =
      integralScalarTensorSection l E L ι W n M U 1 x := by
    unfold integralScalarTensorSection
    rw [he]
    exact ht
  have hmul : integralScalarTensorSection l E L ι W n M U
      (((integralScalarQuotientSheafMap l E L ι W n).hom.app U) z * b) x =
      (((integralScalarQuotientSheafMap l E L ι W n).hom.app U) z * b) •
        integralScalarTensorSection l E L ι W n M U 1 x := by
    unfold integralScalarTensorSection
    rw [tensorSection_smul.{t + 1, t, max u (t + 1)} (f := integralScalarRho l E L ι W n)]
    exact (((integralScalarReductionIso l E L ι W n).inv.app M).val.app U).hom.map_smul _ _
  rw [hmul, ← hu']
  rw [scalarSection_eq_unit]
  rw [map_smul]
  have hs := (((A.levels n).ordinaryAdjunction.unit.app
    ((scalarReductionExtension l E W n).obj M)).val.app U).hom.map_smul z
      (((ar n).unit.app M).val.app U x)
  change ((A.levels n).ordinaryAdjunction.unit.app
      ((scalarReductionExtension l E W n).obj M)).val.app U
        (z • @id (((scalarReductionExtension l E W n).obj M).val.obj U)
          (((ar n).unit.app M).val.app U x)) =
    ((integralScalarQuotientSheafMap l E L ι W n).hom.app U z) •
      @id (((A.levels n).model.E.obj
        ((scalarReductionExtension l E W n).obj M)).val.obj U)
        (((A.levels n).ordinaryAdjunction.unit.app
          ((scalarReductionExtension l E W n).obj M)).val.app U
            (((ar n).unit.app M).val.app U x)) at hs
  rw [hs]
  dsimp only [id]
  erw [map_smul, hx, smul_smul, mul_comm]

end WeilConjectures
