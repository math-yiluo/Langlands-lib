/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeData
/-! # Normalization hypotheses for the scalar tensor representative
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-internal) -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]
structure CoefficientScalarTensorRepresentativeHypotheses (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z) where
  hgenerator : ∀ (M : ModuleRingedComparison.internalModules R Z) (V : Z.ProEtᵒᵖ)
      (s : (condensedRingObj S Z).obj.obj V) (x : M.X.obj.obj V),
    (d.o.hom.app M).val.app V
        (InternalAbelianSheafModule.internalScalarGenerator.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Z) (coefficientMap a Z) M V s x) =
      coefficientSectionScalarPure a Z d.b
        ((ModuleRingedComparison.equivalence R Z).functor.obj M) V s x
  hscalar : ∀ (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z)
      (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
        (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z)
      ((ModuleRingedComparison.equivalence R Z).functor.obj (P.X n))) →
    (ModuleRingedComparison.derivedEquivalence S Z).functor.map
        (coefficientInternalScalarComplex a Z P) ≫
      (ModuleRingedComparison.equivalence S Z).functor.mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d.o (.up ℤ)).hom.app P) =
    d.p.hom.app (DerivedCategory.Q.obj P) ≫
      d.b.derived.map
        ((ModuleRingedComparison.equivalence R Z).functor.mapDerivedCategoryFactors.hom.app P) ≫
      SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        d.b.extension d.b.extension_additive d.b.derived d.b.counit
        (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
          (.up ℤ)).obj P)
  hmonoidal : ∀ (M N : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
      (s : (ModuleRingedComparison.ring S Z).obj.obj V)
      (x : M.val.obj V) (y : N.val.obj V),
    (d.m.toOplaxMonoidal.δ M N).val.app V
        (coefficientSectionScalarPure a Z d.b (M ⊗ N) V s
          (ModuleRingedComparison.sectionPureTensor R Z M N V x y)) =
      ModuleRingedComparison.sectionPureTensor S Z (d.b.extension.obj M)
        (d.b.extension.obj N) V
        (coefficientSectionScalarPure a Z d.b M V s x)
        (coefficientSectionScalarPure a Z d.b N V 1 y)
  htensor : ∀ M N : DerivedCategory (ModuleRingedComparison.internalModules R Z),
    (ModuleRingedComparison.derivedEquivalence S Z).functor.map
        (((internalScalarTensorComparison a Z).app M).app N) ≫
      (ModuleRingedComparison.tensorComparison S Z).hom.app
        ((internalScalarExtension a Z).obj M, (internalScalarExtension a Z).obj N) ≫
      (ModuleRingedComparison.tensor S Z).map (Prod.mkHom (d.p.hom.app M) (d.p.hom.app N)) =
    d.p.hom.app (((derivedTensor R Z).obj M).obj N) ≫
      d.b.derived.map ((ModuleRingedComparison.tensorComparison R Z).hom.app (M, N)) ≫
      d.t.hom.app ((ModuleRingedComparison.derivedEquivalence R Z).functor.obj M,
        (ModuleRingedComparison.derivedEquivalence R Z).functor.obj N)
end AlgebraicGeometry.ProEtale.CondensedRing
