/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralScalarData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SmoothPurity.Supporting.ConnectedAdicIntegralBasis
import all WeilConjectures.Algebra.Homology.SmoothPurity.BasedTensorEvaluation
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Finite free sections and tensor comparison at the geometric point

Source: Bhatt--Scholze, Lemma 4.2.12 (p. 30), Lemma 6.8.2(1) (pp. 58--59),
and the explicit finite-basis calculation in the DAG; Stacks, Tag 03EK
(blueprint: lem-weil-point-finite-free-sections-tensor).

The data structure spells out all clauses of the assertion. Finite products represent
finite direct sums. Tensor factors are written in the order used by change of rings,
namely scalar tensor section. All coefficient maps and sheafified tensors are the
published constructions. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] limit
section PublicTypes
attribute [local irreducible] completedScalarRelativeDegree integralScalarIntegerInclusion
attribute [local irreducible] Padic.coefficientExtensionIntegers

/-- The final object s to s of the small pro-etale site, with the presheaf variance.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeFinal (k : Type t) [Field k] :=
  op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of k))))

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation at the final object, transported by the displayed constant-value ring
identification. No sectionwise tensor assertion is part of this definition.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeEvaluation
    (e : Padic.coefficientExtensionIntegers l E ≃+*
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
        (pointFiniteFreeFinal k)) :=
  SheafOfModules.evaluation.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))
      (pointFiniteFreeFinal k) ⋙ ModuleCat.restrictScalars e.toRingHom

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ordinary module scalar extension, using the recorded inclusion of valuation rings.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeModuleTensor :=
  ModuleCat.extendScalars.{u, u, max u (t + 1)} (integralScalarIntegerInclusion l E L ι)

/-- Forget commutativity in the actual completed coefficient inclusion.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeRingMap :
    completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)) ⟶
      completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k)) :=
  (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat RingCat)).map
      (completedCoefficientMap l E L ι (Spec (.of k)))

/-- Restriction of scalars along the canonical completed coefficient inclusion.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeRestriction :=
  SheafOfModules.restrictScalars.{max u (t + 1)} (pointFiniteFreeRingMap k l E L ι)

/-- The scalar-extension evaluation functor keeps zero maps.
Source: Stacks 03EK (blueprint: lem-weil-point-finite-free-sections-tensor). -/
instance pointEvaluation_zero
    (e : Padic.coefficientExtensionIntegers l L ≃+*
      (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k))).obj.obj
        (pointFiniteFreeFinal k)) :
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
      pointFiniteFreeEvaluation k l L e).PreservesZeroMorphisms where
  map_zero F G := by
    change ((pointFiniteFreeEvaluation k l L e).map
      ((completedOrdinaryScalarExtension l E L ι (Spec (.of k))).map (0 : F ⟶ G))) = 0
    set_option backward.isDefEq.respectTransparency false in
      rw [Functor.map_zero]
    rfl

end PublicTypes
end WeilConjectures
end

@[expose] public noncomputable section
universe a w v c
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max a w}]
  [HasSheafify J AddCommGrpCat.{max a w}]

variable (A B : Type a) [CommRing A] [CommRing B]
  (R S : Sheaf J CommRingCat.{w}) (one : Cᵒᵖ)
  (f : A →+* B) (φ : R ⟶ S) (d : ℕ)

set_option hygiene false in
local notation "rR" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option hygiene false in
local notation "rS" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
set_option hygiene false in
local notation "ringMap" => (sheafCompose J (forget₂ CommRingCat RingCat)).map φ

variable (O : SheafOfModules.{max a w} rR ⥤ SheafOfModules.{max a w} rS) [O.Additive]
  (τ : ∀ (F : SheafOfModules.{max a w} rR) (U : Cᵒᵖ),
    S.obj.obj U → F.val.obj U → (O.obj F).val.obj U)
  (cE : ∀ U : Cᵒᵖ, A → R.obj.obj U) (cL : ∀ U : Cᵒᵖ, B → S.obj.obj U)
  (qE : (A ≃+* R.obj.obj one) → Prop) (qL : (B ≃+* S.obj.obj one) → Prop)

end WeilConjectures
end

@[expose] public noncomputable section
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

local instance pointFiniteFreeUnitHSMul
    (F : integralTowerModules l E (Spec (.of k))) (U : (Spec (.of k)).ProEtᵒᵖ) :
    HSMul ((SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))).val.obj U)
      (F.val.obj U) (F.val.obj U) :=
  inferInstanceAs (HSMul
    ((completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj U)
    (F.val.obj U) (F.val.obj U))

set_option backward.isDefEq.respectTransparency false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The complete assertion: normalized coefficient identifications, a common global
basis, local tensor coordinates, the unique linear natural comparison, exactness,
and its unbounded termwise complex comparison. Each field is a clause of the node.
The inverse formulas fix every coordinate isomorphism, rather than postulating an
unrelated abstract isomorphism. The choice of basis is confined to these coordinates.
Source: Bhatt--Scholze 4.2.12 and 6.8.2(1), Stacks 03EK; DAG statement
(blueprint: lem-weil-point-finite-free-sections-tensor). -/
structure PointFiniteFreeSectionsTensorData where
  coefficientE : Padic.coefficientExtensionIntegers l E ≃+*
    (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
      (pointFiniteFreeFinal k)
  coefficientL : Padic.coefficientExtensionIntegers l L ≃+*
    (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k))).obj.obj
      (pointFiniteFreeFinal k)
  constantE : ∀ a, coefficientE a =
    integralScalarConstant l E (Spec (.of k)) (pointFiniteFreeFinal k) a
  constantL : ∀ a, coefficientL a =
    integralScalarConstant l L (Spec (.of k)) (pointFiniteFreeFinal k) a
  quotientE : ∀ n a,
    (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
      (pointFiniteFreeFinal k) (coefficientE a) =
        integralScalarFiniteConstant l E (Spec (.of k)) n (pointFiniteFreeFinal k) a
  quotientL : ∀ n a,
    (completedIntegralCommRingProjectionUnrestricted l L (Spec (.of k)) n).hom.app
      (pointFiniteFreeFinal k) (coefficientL a) =
        integralScalarFiniteConstant l L (Spec (.of k)) n (pointFiniteFreeFinal k) a
  coefficient_compatibility : ∀ a,
    (completedCoefficientMap l E L ι (Spec (.of k))).hom.app (pointFiniteFreeFinal k)
      (coefficientE a) = coefficientL (integralScalarIntegerInclusion l E L ι a)
  basis : Fin (completedScalarRelativeDegree l E L ι) → Padic.coefficientExtensionIntegers l L
  integral_basis : Function.Bijective
    (fun a : Fin (completedScalarRelativeDegree l E L ι) →
        Padic.coefficientExtensionIntegers l E ↦
      ∑ i, integralScalarIntegerInclusion l E L ι (a i) * basis i)
  sheafBasis :
    (pointFiniteFreeRestriction k l E L ι).obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k)))) ≅
      ∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))))
  sheafBasis_inverse : ∀ U x,
    sheafBasis.inv.val.app U x = ∑ i,
      (pointFiniteFreeRingMap k l E L ι).hom.app U
        ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
          SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))) i).val.app U x) *
        integralScalarConstant l L (Spec (.of k)) U (basis i)
  coordinates : ∀ F : integralTowerModules l E (Spec (.of k)),
    (pointFiniteFreeRestriction k l E L ι).obj
        ((completedOrdinaryScalarExtension l E L ι (Spec (.of k))).obj F) ≅
      ∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F)
  coordinates_tensor : ∀ (F : integralTowerModules l E (Spec (.of k))) U a n i,
    (Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app U
      ((coordinates F).hom.val.app U
        (completedScalarTensorSection l E L ι (Spec (.of k)) F U a n)) =
      ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))) i).val.app U
            (sheafBasis.hom.val.app U a)) • n
  coordinates_inverse : ∀ (F : integralTowerModules l E (Spec (.of k))) U x,
    (coordinates F).inv.val.app U x = ∑ i,
      completedScalarTensorSection l E L ι (Spec (.of k)) F U
        (integralScalarConstant l L (Spec (.of k)) U (basis i))
        ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app U x)
  comparison :
    pointFiniteFreeEvaluation k l E coefficientE ⋙ pointFiniteFreeModuleTensor.{t, u} l E L ι ≅
      completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
        pointFiniteFreeEvaluation k l L coefficientL
  comparison_tensor : ∀ (F : integralTowerModules l E (Spec (.of k))) a n,
    comparison.hom.app F
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E, integralScalarIntegerInclusion l E L ι] n) =
      completedScalarTensorSection l E L ι (Spec (.of k)) F (pointFiniteFreeFinal k)
        (coefficientL a) n
  comparison_coordinates : ∀ (F : integralTowerModules l E (Spec (.of k)))
    (n : Fin (completedScalarRelativeDegree l E L ι) →
      (pointFiniteFreeEvaluation k l E coefficientE).obj F) i,
    (Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app
        (pointFiniteFreeFinal k)
      ((coordinates F).hom.val.app (pointFiniteFreeFinal k)
        (comparison.hom.app F (∑ j,
          basis j ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion l E L ι] n j))) = n i
  comparison_inverse : ∀ (F : integralTowerModules l E (Spec (.of k))) x,
    comparison.inv.app F x = ∑ i,
      basis i ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        integralScalarIntegerInclusion l E L ι]
        (@id ((pointFiniteFreeEvaluation k l E coefficientE).obj F)
          ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app
            (pointFiniteFreeFinal k)
              ((coordinates F).hom.val.app (pointFiniteFreeFinal k) x)))
  comparison_unique : ∀ (F : integralTowerModules l E (Spec (.of k)))
    (f : ((pointFiniteFreeEvaluation k l E coefficientE ⋙
      pointFiniteFreeModuleTensor.{t, u} l E L ι).obj F) ⟶
      ((completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
        pointFiniteFreeEvaluation k l L coefficientL).obj F)),
    (∀ a n, f (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
      integralScalarIntegerInclusion l E L ι] n) =
        completedScalarTensorSection l E L ι (Spec (.of k)) F (pointFiniteFreeFinal k)
          (coefficientL a) n) → f = comparison.hom.app F
  sheaf_additive : (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).Additive
  sheaf_limits : PreservesFiniteLimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
  sheaf_colimits : PreservesFiniteColimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
  module_additive : (pointFiniteFreeModuleTensor.{t, u} l E L ι).Additive
  module_limits : PreservesFiniteLimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)
  module_colimits : PreservesFiniteColimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)
  restriction_detects_exactness : ∀ S : ShortComplex (integralTowerModules l L (Spec (.of k))),
    S.Exact ↔ (S.map (pointFiniteFreeRestriction k l E L ι)).Exact
  complexes :
    (pointFiniteFreeEvaluation k l E coefficientE ⋙
      pointFiniteFreeModuleTensor.{t, u} l E L ι).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
      pointFiniteFreeEvaluation k l L coefficientL).mapHomologicalComplex (ComplexShape.up ℤ)
  complexes_hom : ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) j,
    (complexes.hom.app K).f j = comparison.hom.app (K.X j)
  complexes_inv : ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) j,
    (complexes.inv.app K).f j = comparison.inv.app (K.X j)

end WeilConjectures
end

noncomputable section
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] limit

attribute [local irreducible] completedScalarChangeData completedCoefficientMap
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
attribute [local irreducible] integralScalarConstant completedOrdinaryScalarExtension
attribute [local irreducible] completedScalarTensorSection
attribute [local irreducible] SheafOfModules.basedTensorProductSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L] [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

section ScalarTransport
universe rA rR
variable {A B : Type rA} {R S : Type rR}
  [CommRing A] [CommRing B] [CommRing R] [CommRing S]

end ScalarTransport

section Normalize
universe w c v
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {R S : Sheaf J CommRingCat.{w}}
end Normalize

section CoreAssembly
universe aG wG cG vG
variable {C : Type cG} [Category.{vG} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max aG wG} RingCat.{max aG wG})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max aG wG}]
  [HasSheafify J AddCommGrpCat.{max aG wG}]

end CoreAssembly

end WeilConjectures

end
