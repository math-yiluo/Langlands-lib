/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Rationalization of coefficient-module complexes

Source: blueprint main-20261015, `lemma-perfect-complexes-geometric-point`, final paragraph;
Stacks Tags 0539, 00HD, 00CX, 015F and 04VG
(blueprint: lem-weil-coefficient-complex-rationalization).

The aliases below use Mathlib's coefficient-first convention for the ordinary tensor.
They allow arbitrary module sizes above the coefficient size. All maps are specified
on generators before localization; no resolution or boundedness is involved.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Ordinary integral scalar tensor, using the existing restricted field inclusion.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable abbrev coefficientComplexIntegralTensor :=
  ModuleCat.extendScalars.{u, u, max u v} (integralScalarIntegerInclusion l E L ι)

/-- Ordinary fraction-field tensor, with the recorded valuation subring.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable abbrev coefficientComplexRationalize :=
  ModuleCat.extendScalars.{u, u, max u v} (Padic.coefficientExtensionIntegers l E).subtype

/-- Ordinary field scalar tensor along the specified coefficient inclusion.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable abbrev coefficientComplexFieldTensor :=
  ModuleCat.extendScalars.{u, u, max u v} ι.toRingHom

private theorem coefficientTensorAdditive {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars.{u, u, max u v} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

attribute [local instance] coefficientTensorAdditive

private theorem coefficientTensorLimits {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max u v} f) := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  have hex : ∀ C : ShortComplex (ModuleCat.{max u v} R), C.Exact →
      (C.map (ModuleCat.extendScalars f)).Exact := by
    intro C hC
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
    exact Module.Flat.lTensor_exact S hC
  have h := ((Functor.exact_tfae (ModuleCat.extendScalars.{u, u, max u v} f)).out 2 4).mp
    hex
  exact h.1

private theorem coefficientIntegerFlat {S : Type u} [CommRing S] [IsDomain S]
    (f : Padic.coefficientExtensionIntegers l E →+* S) (hf : Function.Injective f) :
    f.Flat := by
  let : Algebra (Padic.coefficientExtensionIntegers l E) S := f.toAlgebra
  let : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) :=
    (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.2.1
  let : Module.IsTorsionFree (Padic.coefficientExtensionIntegers l E) S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hf
  exact inferInstanceAs (Module.Flat (Padic.coefficientExtensionIntegers l E) S)

/-- Exactness of all four coefficient tensors, without finiteness conditions on modules.
Source: blueprint coefficient-point paragraph; Stacks 0539 and 00HD
(blueprint: lem-weil-coefficient-complex-rationalization).
Proof: O_E and O_L are valuation rings, with fraction fields E and L. Their inclusions
make O_L and E torsion-free over O_E, and L torsion-free over O_L and over E.
Apply lem-trf-valuation-torsionfree-flat to each, then lem-weil-pbc-flat-tensor-exact.
Surjectivity follows by lifting pure tensors. Tensor maps add on generators. Exactness
and additivity preserve kernels, cokernels, zero objects and finite biproducts, hence
finite limits and colimits. This is steps 1 and 2 of the node's proof.
-/
theorem coefficientComplexTensors_exact :
    ((coefficientComplexIntegralTensor.{u, v} l E L ι).Additive ∧
      PreservesFiniteLimits (coefficientComplexIntegralTensor.{u, v} l E L ι) ∧
      PreservesFiniteColimits (coefficientComplexIntegralTensor.{u, v} l E L ι)) ∧
    ((coefficientComplexRationalize.{u, v} l E).Additive ∧
      PreservesFiniteLimits (coefficientComplexRationalize.{u, v} l E) ∧
      PreservesFiniteColimits (coefficientComplexRationalize.{u, v} l E)) ∧
    ((coefficientComplexRationalize.{u, v} l L).Additive ∧
      PreservesFiniteLimits (coefficientComplexRationalize.{u, v} l L) ∧
      PreservesFiniteColimits (coefficientComplexRationalize.{u, v} l L)) ∧
    ((coefficientComplexFieldTensor.{u, v} l E L ι).Additive ∧
      PreservesFiniteLimits (coefficientComplexFieldTensor.{u, v} l E L ι) ∧
      PreservesFiniteColimits (coefficientComplexFieldTensor.{u, v} l E L ι)) := by
  have hι : Function.Injective (integralScalarIntegerInclusion l E L ι) := by
    intro a b h
    apply Subtype.ext
    exact ι.injective (congrArg Subtype.val h)
  have hB := coefficientTensorLimits.{u, v} _ (coefficientIntegerFlat l E _ hι)
  have hE := coefficientTensorLimits.{u, v} _
    (coefficientIntegerFlat l E _ (Padic.coefficientExtensionIntegers l E).subtype_injective)
  have hL := coefficientTensorLimits.{u, v} _
    (coefficientIntegerFlat l L _ (Padic.coefficientExtensionIntegers l L).subtype_injective)
  have hfield : ι.toRingHom.Flat := by
    let : Algebra E L := ι.toRingHom.toAlgebra
    exact inferInstanceAs (Module.Flat E L)
  have hF := coefficientTensorLimits.{u, v} _ hfield
  exact ⟨⟨inferInstance, hB, inferInstance⟩, ⟨inferInstance, hE, inferInstance⟩,
    ⟨inferInstance, hL, inferInstance⟩, ⟨inferInstance, hF, inferInstance⟩⟩

/-- Kernel preservation. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexIntegralLimits :
    PreservesFiniteLimits (coefficientComplexIntegralTensor.{u, v} l E L ι) :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).1.2.1

/-- Cokernel preservation. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexIntegralColimits :
    PreservesFiniteColimits (coefficientComplexIntegralTensor.{u, v} l E L ι) :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).1.2.2

/-- Additivity of rationalization. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexRationalAdditive :
    (coefficientComplexRationalize.{u, v} l E).Additive :=
  (coefficientComplexTensors_exact.{u, v} l E E (AlgHom.id (Padic l) E)).2.1.1

/-- Kernel preservation by rationalization. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexRationalLimits :
    PreservesFiniteLimits (coefficientComplexRationalize.{u, v} l E) :=
  (coefficientComplexTensors_exact.{u, v} l E E (AlgHom.id (Padic l) E)).2.1.2.1

/-- Cokernel preservation by rationalization. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexRationalColimits :
    PreservesFiniteColimits (coefficientComplexRationalize.{u, v} l E) :=
  (coefficientComplexTensors_exact.{u, v} l E E (AlgHom.id (Padic l) E)).2.1.2.2

/-- Additivity of field extension. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexFieldAdditive :
    (coefficientComplexFieldTensor.{u, v} l E L ι).Additive :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).2.2.2.1

/-- Kernel preservation by field extension. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexFieldLimits :
    PreservesFiniteLimits (coefficientComplexFieldTensor.{u, v} l E L ι) :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).2.2.2.2.1

/-- Cokernel preservation by field extension. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexFieldColimits :
    PreservesFiniteColimits (coefficientComplexFieldTensor.{u, v} l E L ι) :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).2.2.2.2.2

/-- The standard localization, at arbitrary coefficient-module size.
Source: Stacks 05RU (blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexModuleDerived (R : Type u) [Ring R] :
    HasDerivedCategory (ModuleCat.{max u v} R) := HasDerivedCategory.standard _

private theorem scalarComp_hom_tmul {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (P : ModuleCat.{max u v} R) (b : T) (n : P) :
    (ModuleCat.extendScalarsComp f g).hom.app P (b ⊗ₜ[R, g.comp f] n) =
      b ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) := by
  have h := ModuleCat.extendScalarsComp_hom_app_one_tmul f g P n
  change ((ModuleCat.extendScalarsComp f g).hom.app P).hom _ = _ at h
  change ((ModuleCat.extendScalarsComp f g).hom.app P).hom _ = _
  calc
    _ = ((ModuleCat.extendScalarsComp f g).hom.app P).hom
        (b • ((1 : T) ⊗ₜ[R, g.comp f] n)) := by
          rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    _ = b • ((ModuleCat.extendScalarsComp f g).hom.app P).hom
        ((1 : T) ⊗ₜ[R, g.comp f] n) := map_smul _ _ _
    _ = _ := by
      rw [h]
      change (b * 1) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) = _
      rw [mul_one]

private theorem scalarComp_inv_tmul {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (P : ModuleCat.{max u v} R) (a : S) (b : T) (n : P) :
    (ModuleCat.extendScalarsComp f g).inv.app P
      (b ⊗ₜ[S, g] (a ⊗ₜ[R, f] n)) =
      (b * g a) ⊗ₜ[R, g.comp f] n := by
  apply (ConcreteCategory.bijective_of_isIso
    ((ModuleCat.extendScalarsComp f g).hom.app P)).1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app, ModuleCat.id_apply,
    scalarComp_hom_tmul]
  let : Algebra S T := g.toAlgebra
  rw [show a ⊗ₜ[R, f] n = a • ((1 : S) ⊗ₜ[R, f] n) from
    (ModuleCat.ExtendScalars.smul_tmul f a 1 n).trans (by rw [mul_one]) |>.symm]
  erw [← TensorProduct.smul_tmul]
  change (g a * b) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) = _
  rw [mul_comm]

private theorem scalarDouble_hom_ext {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (P : ModuleCat.{max u v} R) (X : ModuleCat.{max u v} T)
    (α β : (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj P) ⟶ X)
    (h : ∀ n : P, α ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n)) =
      β ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n))) : α = β := by
  apply ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro n
  exact h n

private noncomputable def coefficientModuleBeta :
    coefficientComplexIntegralTensor.{u, v} l E L ι ⋙
        coefficientComplexRationalize.{u, v} l L ≅
      coefficientComplexRationalize.{u, v} l E ⋙
        coefficientComplexFieldTensor.{u, v} l E L ι :=
  (ModuleCat.extendScalarsComp (integralScalarIntegerInclusion l E L ι)
    (Padic.coefficientExtensionIntegers l L).subtype).symm ≪≫
  ModuleCat.extendScalarsComp (Padic.coefficientExtensionIntegers l E).subtype ι.toRingHom

/-- The uniquely normalized ordinary module comparison.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization).
Proof: for C = O_L or E identify (C tensor N) tensor L with L tensor N by
multiplying the two coefficient factors. The inverse inserts 1 as the inner factor.
Both maps are additive and balanced twice, are L-linear, and their composites are the
identity on pure tensors. Compose the inverse E-comparison with the O_L-comparison.
The formula determines the result by tensor generation and commutes with all module
maps. This is steps 3 and 4 of the node's proof; no element of N is divided.
-/
theorem coefficientComplexBeta_existsUnique :
    ∃! β : coefficientComplexIntegralTensor.{u, v} l E L ι ⋙
        coefficientComplexRationalize.{u, v} l L ≅
      coefficientComplexRationalize.{u, v} l E ⋙
        coefficientComplexFieldTensor.{u, v} l E L ι,
      ∀ (P : ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : P),
        β.hom.app P
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            (Padic.coefficientExtensionIntegers l L).subtype]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion l E L ι] n)) =
          (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
            ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              (Padic.coefficientExtensionIntegers l E).subtype] n) := by
  have hformula : ∀ (P : ModuleCat.{max u v}
        (Padic.coefficientExtensionIntegers l E))
      (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : P),
      (coefficientModuleBeta.{u, v} l E L ι).hom.app P
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
          (Padic.coefficientExtensionIntegers l L).subtype]
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion l E L ι] n)) =
        (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
          ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            (Padic.coefficientExtensionIntegers l E).subtype] n) := by
    intro P a b n
    dsimp only [coefficientModuleBeta, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    rw [ModuleCat.comp_apply, scalarComp_inv_tmul]
    exact scalarComp_hom_tmul _ _ P (b * (a : L)) n
  refine ⟨coefficientModuleBeta.{u, v} l E L ι, hformula, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply scalarDouble_hom_ext
  intro n
  exact (hβ P 1 1 n).trans (hformula P 1 1 n).symm

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (κ : L →ₐ[Padic l] M)

/-- Restriction of a composite inclusion is the composite integer map.
Source: blueprint coefficient-point paragraph, tower clause
(blueprint: lem-weil-coefficient-complex-rationalization).
Proof: both maps send an integer a to kappa(iota(a)). Subtype extensionality and
ring-map extensionality give equality. This is the coefficient-map part of step 7. -/
theorem coefficientComplexIntegerComp :
    (integralScalarIntegerInclusion l L M κ).comp
      (integralScalarIntegerInclusion l E L ι) =
    integralScalarIntegerInclusion l E M (κ.comp ι) := by
  ext x
  rfl

/-- The integral tensor associator is Mathlib's scalar associator, with the actual
composite integer inclusion. Its forward map multiplies the coefficient factors.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexIntegralAssoc :
    coefficientComplexIntegralTensor.{u, v} l E L ι ⋙
      coefficientComplexIntegralTensor.{u, v} l L M κ ≅
    coefficientComplexIntegralTensor.{u, v} l E M (κ.comp ι) :=
  (ModuleCat.extendScalarsComp (integralScalarIntegerInclusion l E L ι)
    (integralScalarIntegerInclusion l L M κ)).symm ≪≫
  eqToIso (congrArg (ModuleCat.extendScalars.{u, u, max u v})
    (coefficientComplexIntegerComp l E L ι M κ))

private theorem deriveCoefficientTower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category D₀] [Category D₁] [Category D₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian D₀] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ D₂)
    (Q : C₀ ⥤ D₀) (R : C₁ ⥤ D₁) (V : D₀ ⥤ D₁) (W : D₁ ⥤ D₂)
    (I : C₀ ⥤ C₂) (J : D₀ ⥤ D₂)
    [F.Additive] [G.Additive] [H.Additive] [Q.Additive] [R.Additive]
    [V.Additive] [W.Additive] [I.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (a : F ⋙ G ≅ I) (b : I ⋙ H ≅ Q ⋙ J) (c : G ⋙ H ≅ R ⋙ W)
    (d : F ⋙ R ≅ Q ⋙ V) (e : V ⋙ W ≅ J)
    (h : Functor.isoWhiskerRight a H ≪≫ b =
      Functor.isoWhiskerLeft F c ≪≫ Functor.isoWhiskerRight d W ≪≫
        Functor.isoWhiskerLeft Q e) (K : DerivedCategory C₀) :
    H.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso F G ≪≫
          Functor.mapDerivedCategoryNatIso a).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso b).hom.app K =
      (Functor.mapDerivedCategorySquareIso c).hom.app (F.mapDerivedCategory.obj K) ≫
        W.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso d).hom.app K) ≫
        (Functor.mapDerivedCategoryCompIso V W ≪≫
          Functor.mapDerivedCategoryNatIso e).hom.app (Q.mapDerivedCategory.obj K) := by
  have hm := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom) h
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hm
  have ha := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a H
  have hc := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F c
  have hd := Functor.mapDerivedCategoryNatIso_isoWhiskerRight d W
  have he := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft Q e
  have hF := Functor.mapDerivedCategoryCompIso_assoc F G H
  have hR := Functor.mapDerivedCategoryCompIso_assoc F R W
  have hQ := Functor.mapDerivedCategoryCompIso_assoc Q V W
  have ht :
      Functor.whiskerRight
        (Functor.mapDerivedCategoryCompIso F G ≪≫
          Functor.mapDerivedCategoryNatIso a).hom H.mapDerivedCategory ≫
        (Functor.mapDerivedCategorySquareIso b).hom =
      Functor.whiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso c).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom
          W.mapDerivedCategory ≫
        Functor.whiskerLeft Q.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso V W ≪≫
            Functor.mapDerivedCategoryNatIso e).hom := by
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (F ⋙ G) H).inv ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).inv
        H.mapDerivedCategory)).mp
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
    simp only [← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id_assoc]
    rw [← reassoc_of% ha, Iso.inv_hom_id_assoc]
    rw [← reassoc_of% hF]
    simp only [← Functor.whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]
    simp only [Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
    rw [← reassoc_of% hc, reassoc_of% hR]
    simp only [← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id_assoc]
    simp only [Functor.whiskerRight_comp, Category.assoc]
    rw [← reassoc_of% hd, ← reassoc_of% hQ]
    simp only [← Functor.whiskerLeft_comp_assoc, Iso.inv_hom_id,
      Functor.whiskerLeft_id', Category.id_comp]
    rw [← he, reassoc_of% hm]
  exact congr_app ht K

end WeilConjectures

namespace WeilConjectures

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

end WeilConjectures

namespace WeilConjectures

end WeilConjectures
