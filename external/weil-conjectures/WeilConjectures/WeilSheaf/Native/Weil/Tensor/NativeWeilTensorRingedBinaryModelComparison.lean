/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex
public import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison

/-! # Binary native tensor models and the transported counit

Source: Stacks 06YN, 06YU, 0FPT. Transport the explicit chain models through localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  nativeWeilRingedTensorModel NativeTensorKFlat nativeRingedAssociatorComplex
  nativeRingedTripleLeft nativeRingedTripleRight
  nativeWeilRingedTensorComplexModel

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)
  [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
  (SB : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
  (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)

/-- The counit tensor comparison for the native transported monoidal structure.
Source: Mathlib monoidal transport
(blueprint: lem-sf-native-weil-ringed-binary-model-comparison). -/
def nativeRingedTensorComparison :
    let := SB.monoidal
    letI := nativeWeilRingedMonoidal b SB
    MonoidalCategory.tensor (DerivedCategory (ProEtaleWeilSheaf k₀ l X)) ⋙
        (nativeWeilRingedDerivedEquivalence b).functor ≅
      (nativeWeilRingedDerivedEquivalence b).functor.prod
        (nativeWeilRingedDerivedEquivalence b).functor ⋙
          MonoidalCategory.tensor (DerivedCategory
            (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)) := by
  let := SB.monoidal
  exact transportedTensorComparison (nativeWeilRingedDerivedEquivalence b)

/-- The native transported counit comparison satisfies associativity.
Source: Mathlib monoidal transport
(blueprint: lem-sf-native-weil-ringed-binary-model-comparison). -/
theorem nativeRingedTensorComparison_associativity
    (P Q N : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    let := SB.monoidal
    letI := nativeWeilRingedMonoidal b SB
    let E := nativeWeilRingedDerivedEquivalence b
    let μ := nativeRingedTensorComparison b SB
    μ.hom.app (P ⊗ Q, N) ≫ (μ.hom.app (P, Q) ▷ E.functor.obj N) ≫
        (α_ (E.functor.obj P) (E.functor.obj Q) (E.functor.obj N)).hom =
      E.functor.map (α_ P Q N).hom ≫ μ.hom.app (P, Q ⊗ N) ≫
        (E.functor.obj P ◁ μ.hom.app (Q, N)) := by
  let := SB.monoidal
  exact transportedTensorComparison_associativity (nativeWeilRingedDerivedEquivalence b) P Q N

/-- The explicit binary model is compatible with the transported counit comparison.
Source: Stacks 0FPT; definition of the native derived tensor model
(blueprint: lem-sf-native-weil-ringed-binary-model-comparison).

Proof: expand the preimage isomorphism, use full faithfulness to map its inverse,
and cancel the adjacent counit and localization-factor inverse pairs. -/
theorem nativeRingedTensorModel_binary
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hQ : NativeTensorKFlat k₀ l X T Q) :
    let := SB.monoidal
    letI := nativeWeilRingedMonoidal b SB
    let E := nativeWeilRingedDerivedEquivalence b
    let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
    let τ := b.native.functor.mapDerivedCategoryFactors
    let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
    let qB := DerivedCategory.Q
      (C := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
    let μ := nativeRingedTensorComparison b SB
    E.functor.map (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).inv ≫
        μ.hom.app (q.obj P, q.obj Q) ≫ (τ.hom.app P ⊗ₘ τ.hom.app Q) =
      τ.hom.app (nativeTensorComplex T P Q) ≫ qB.map (A.chain Q P).hom ≫
        (cB.tensorIso (Ec.obj P) (Ec.obj Q) (Or.inr (A.flat Q hQ))).hom := by
  let := SB.monoidal
  letI := nativeWeilRingedMonoidal b SB
  let E := nativeWeilRingedDerivedEquivalence b
  let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
  let τ := b.native.functor.mapDerivedCategoryFactors
  let qB := DerivedCategory.Q
    (C := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
  let ci := cB.tensorIso (Ec.obj P) (Ec.obj Q) (Or.inr (A.flat Q hQ))
  simp only [nativeWeilRingedTensorModel, nativeWeilRingedTensorComplexModel,
    Functor.preimageIso_inv, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Iso.prod]
  rw [Functor.map_preimage]
  simp only [Functor.mapIso_inv, CoefficientClosedStructure.tensor, tensor_map,
    Category.assoc]
  change τ.hom.app (nativeTensorComplex T P Q) ≫ qB.map (A.chain Q P).hom ≫
      ci.hom ≫ (τ.inv.app P ⊗ₘ τ.inv.app Q) ≫
      E.counitIso.inv.app _ ≫ E.counitIso.hom.app _ ≫
      (τ.hom.app P ⊗ₘ τ.hom.app Q) = _
  simp only [Iso.inv_hom_id_app_assoc, tensorHom_comp_tensorHom,
    Iso.inv_hom_id_app]
  erw [id_tensorHom_id, Category.comp_id]

end AlgebraicGeometry.ProEtaleWeilSheaf
