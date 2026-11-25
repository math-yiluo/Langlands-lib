/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import WeilConjectures.AlgebraicGeometry.ResidueLayerTensor.ResidueLayerTensorComparison
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueCoefficientIso
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ULift

/-! # Vanishing of an integral scalar residue layer

This is the support clause of the residue-layer argument.  It isolates the
finite-residue scalar-extension and interval comparison from the constructibility
clause of the parent theorem.
Source: Stacks, sites-modules, lemma-tensor-product-locally-constant; proetale,
lemma-constructible-serre; parent finite-filtration argument.
(blueprint: lem-sf-integral-scalar-residue-layer-vanishing).

Proof: the quotient of two consecutive powers of the target uniformizer is the
finite target residue field.  Multiplication by the appropriate power of the
uniformizer identifies the quotient with that residue field; cancellation in the
DVR proves injectivity.  The coefficient map factors through the source residue
field.  Balanced tensor associativity identifies the resulting layer complex with
finite-field scalar extension of the source residue reduction.  Exact finite-field
scalar extension preserves the given finite local models, and restriction to the
finite quotient ring preserves those models.  Derived homology agrees with the
homology of the K-flat representative.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
namespace IntegralScalarResidueVanishing

open CategoryTheory.Functor

-- The full finite-field theorem has a downstream import back to this module.
-- Use its exactness argument on the concrete, lower-level sheaf extension instead.
private noncomputable def residueFieldMap
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') : adicLisseConstantRing Y (ULift.{u + 1} k) ⟶
      adicLisseConstantRing Y (ULift.{u + 1} k') :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))

private theorem scalarUnit_naturality
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    (proEtaleModuleScalarUnit Y k) ≫
        ((adicLisseForget Y).map (residueFieldMap Y (k := k) (k' := k') f)).hom =
      Functor.whiskerRight
        ((Functor.const Y.ProEtᵒᵖ).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))
        (forget₂ CommRingCat RingCat) ≫ proEtaleModuleScalarUnit Y k' := by
  ext U b
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).symm U) b

private noncomputable def restrictionEncodingIso
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    pbcRestrict (residueFieldMap Y (k := k) (k' := k') f) ⋙ proEtaleModuleRestriction Y k ≅
      proEtaleModuleRestriction Y k' ⋙
        sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} f)) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := (((pbcRestrict (residueFieldMap Y (k := k) (k' := k') f) ⋙
        proEtaleModuleRestriction Y k).obj M).obj.obj U)
    let Q := (((proEtaleModuleRestriction Y k' ⋙
        sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1}
            (RingHom.ulift.{u + 1, u + 1} f))).obj M).obj.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[ULift.{u + 1} k] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    change (((residueFieldMap Y (k := k) (k' := k') f).hom.app U).hom
      (((proEtaleModuleScalarUnit Y k).app U).hom b)) •
        (show M.val.obj U from m) =
      (((proEtaleModuleScalarUnit Y k').app U).hom ((RingHom.ulift.{u + 1, u + 1} f) b)) •
        (show M.val.obj U from m)
    exact congrArg (fun a ↦ a • (show M.val.obj U from m))
      (ConcreteCategory.congr_hom (congr_app (scalarUnit_naturality Y f) U) b)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

private noncomputable def scalarExtensionEncodingIso
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    pbcExtend (residueFieldMap Y (k := k) (k' := k') f) ⋙ proEtaleModuleRestriction Y k' ≅
      proEtaleModuleRestriction Y k ⋙
        Sheaf.composeAndSheafify (ProEt.topology Y)
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (RingHom.ulift.{u + 1, u + 1} f)) := by
  let E := proEtaleModuleEncoding Y k
  let E' := proEtaleModuleEncoding Y k'
  let L := Sheaf.composeAndSheafify (ProEt.topology Y)
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (RingHom.ulift.{u + 1, u + 1} f))
  let R := sheafCompose (ProEt.topology Y)
    (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} f))
  let adj := E.toAdjunction.comp
    ((Sheaf.adjunction (ProEt.topology Y)
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (RingHom.ulift.{u + 1, u + 1} f))).comp E'.symm.toAdjunction)
  let eR : E'.functor ⋙ R ⋙ E.inverse ≅
      pbcRestrict (residueFieldMap Y (k := k) (k' := k') f) :=
    (isoWhiskerRight (restrictionEncodingIso Y (k := k) (k' := k') f).symm E.inverse) ≪≫
      isoWhiskerLeft _ E.unitIso.symm
  let adj' := adj.ofNatIsoRight eR
  let e := (pbcScalarAdjunction (residueFieldMap Y (k := k) (k' := k') f)).leftAdjointUniq adj'
  exact isoWhiskerRight e E'.functor ≪≫
    isoWhiskerLeft (E.functor ⋙ L) E'.counitIso

private theorem scalarExtension_exact
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    PreservesFiniteLimits (pbcExtend (residueFieldMap Y (k := k) (k' := k') f)) ∧
      PreservesFiniteColimits (pbcExtend (residueFieldMap Y (k := k) (k' := k') f)) := by
  have := proEtaleModuleRestriction_isEquivalence Y k
  have := proEtaleModuleRestriction_isEquivalence Y k'
  have hflat : (RingHom.ulift.{u + 1, u + 1} f).Flat := by
    let := (RingHom.ulift.{u + 1, u + 1} f).toAlgebra
    change Module.Flat (ULift.{u + 1} k) (ULift.{u + 1} k')
    exact Module.Flat.of_free
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u + 1} hflat
  let L := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (RingHom.ulift.{u + 1, u + 1} f)
  have : PreservesFiniteLimits ((Functor.whiskeringRight Y.ProEtᵒᵖ _ _).obj L) := by
    constructor
    intro J _ _
    infer_instance
  have : PreservesFiniteLimits (Sheaf.composeAndSheafify (ProEt.topology Y) L) := by
    unfold Sheaf.composeAndSheafify
    have := comp_preservesFiniteLimits
      ((Functor.whiskeringRight Y.ProEtᵒᵖ _ _).obj L)
      (presheafToSheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} k')))
    exact comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (pbcExtend (residueFieldMap Y (k := k) (k' := k') f) ⋙ proEtaleModuleRestriction Y k') :=
    preservesFiniteLimits_of_natIso (scalarExtensionEncodingIso Y (k := k) (k' := k') f).symm
  have : (pbcExtend (residueFieldMap Y (k := k) (k' := k') f)).IsLeftAdjoint :=
    (pbcScalarAdjunction (residueFieldMap Y (k := k) (k' := k') f)).isLeftAdjoint
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves
    (pbcExtend (residueFieldMap Y (k := k) (k' := k') f))
      (proEtaleModuleRestriction Y k'), inferInstance⟩

end IntegralScalarResidueVanishing
end AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

set_option linter.unusedVariables false in
/-- The out-of-interval vanishing part of the residue-layer estimate.
Source: Stacks, sites-modules, lemma-tensor-product-locally-constant; proetale,
lemma-constructible-serre; parent finite-filtration argument.
(blueprint: lem-sf-integral-scalar-residue-layer-vanishing). -/
theorem integralScalarResidueLayer_vanishing
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (r s : ℤ) (hrs : r ≤ s)
    (h₁ : intrinsicFiniteTorsionConstructible l E 1 (by omega) Y
      ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)))
    (hbound : ∀ i : ℤ,
      i ∈ proEtaleCohomologicalSupport
        ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)) →
      r ≤ i ∧ i ≤ s) (n : ℕ)
    (F : Fin (n + 1 + 1) → Submodule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1)))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))
    (hF : F = fun (j : Fin (n + 1 + 1)) ↦ (Ideal.span ({ULift.up ((Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l L (n + 1)))
        (Padic.coefficientExtensionUniformizer l L))} :
          Set (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))) ^ ((j : ℕ))) :
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
    ∀ (j : Fin (n + 1)) (i : ℤ),
      ((i < r ∨ s < i) → IsZero
        ((filteredCoefficientTensorComplex Y B
          (completedIntegralCommRingSheafUnrestricted l E Y)
          (integralScalarRho l E L ι Y n) P.obj
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology i)) := by
  clear h₁ hrs
  let p := completedIntegralCommRingProjectionUnrestricted l E Y 0
  let f := integralScalarQuotientSheafMap l E L ι Y 0
  let F₀ := pbcExtend p
  let C := (F₀.mapHomologicalComplex (.up ℤ)).obj P.obj
  have := integralReductionChangeOfRingsAdditive l E Y D hl 0
  let K := (integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)
  let e : K ≅ DerivedCategory.Q.obj C :=
    (integralDerivedReduction l E Y D hl 0).mapIso
        ((DerivedCategory.quotientCompQhIso _).symm.app P.obj) ≪≫
      integralDerivedReductionKFlatIso l E Y D hl 0 P.obj P.property.1 ≪≫
      DerivedCategory.Qh.mapIso
        (((integralReductionChangeOfRings l E Y D hl 0).mapHomotopyCategoryFactors
          (.up ℤ)).app P.obj) ≪≫
      (DerivedCategory.quotientCompQhIso _).app C
  have hC (i : ℤ) (hi : i < r ∨ s < i) : IsZero (C.homology i) := by
    have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
      by_contra hn
      have hb := hbound i hn
      omega
    exact hz.of_iso (((DerivedCategory.homologyFunctor _ i).mapIso e) ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app C).symm
  have hf : f = IntegralScalarResidueVanishing.residueFieldMap Y
      (k := Padic.coefficientExtensionRing l E 1)
      (k' := Padic.coefficientExtensionRing l L 1)
      (integralScalarQuotientMap l E L ι 0) := by
    rfl
  let G := pbcExtend f
  have hexact := IntegralScalarResidueVanishing.scalarExtension_exact Y
    (k := Padic.coefficientExtensionRing l E 1)
    (k' := Padic.coefficientExtensionRing l L 1)
    (integralScalarQuotientMap l E L ι 0)
  have : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (pbcExtend f)
    rw [hf]
    exact hexact.1
  have : PreservesFiniteColimits G := by
    change PreservesFiniteColimits (pbcExtend f)
    rw [hf]
    exact hexact.2
  dsimp only
  intro j i hi
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
  let b := integralScalarResidueProjection l L Y n
  let V := ModuleCat.of B ((F j.castSucc) ⧸ (F j.succ).comap (F j.castSucc).subtype)
  obtain ⟨eV⟩ := integralScalarResidueCoefficientIso (l := l) (L := L) (Y := Y) n F hF j
  obtain ⟨eP⟩ := ResidueLayerTensor.comparison Y B
    (integralScalarRho l E L ι Y n) b p f
    (integralScalarResidue_triangle l E Y L ι n) V eV P.obj
  let H := pbcRestrict b
  let C' := (G.mapHomologicalComplex (.up ℤ)).obj C
  let eH := (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso eP ≪≫
    (C'.sc i).mapHomologyIso H ≪≫ H.mapIso ((C.sc i).mapHomologyIso G)
  exact (H.map_isZero (G.map_isZero (hC i hi))).of_iso eH

end WeilConjectures
