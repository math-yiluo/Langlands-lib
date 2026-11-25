/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeEquation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeInternal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeTransport
/-! # Tensor representatives under coefficient scalar reconstruction

Source: Stacks Project, Tags 03EK, 03EL, 06YY, 07A4 and 07A6;
steps 1--3 of `lem-sfb-coefficient-scalar-tensor-realization`.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap internalScalarExtension
  coefficientInternalScalarComplex coefficientSectionScalarPure coefficientSectionScalarTotal
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor derivedTensor
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
  Localization.Monoidal.tensorBifunctor
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]
/-- The signed scalar tensor equation follows from the ordinary generator normalization,
the scalar comparison on complexes, and the identification of the derived tensorator.
Only the representative equation is asserted; no scalar pair or comparison is constructed.

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL; Cohomology on Sites,
Tags 07A4 and 07A6; step 3 of coefficient scalar section realization.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative).

Proof: first take two internal complexes whose reconstructed terms are flat and whose
reconstructions are K-flat. Precompose the two ordinary scalar tensor comparisons with
the balanced tensor coprojections and the scalar extension units. The generator formula
for o and the generator formula for m identify these maps with the scalar-unit normalized
internal tensorator. Balanced tensor universality and the sheafification adjunction give
the equality of ordinary maps. In bidegree (i,j), this is the same equation, and both
complex tensor differentials use the same Koszul signs. The coproduct universal property
therefore gives equality of their signed total maps. Scalar extension preserves these
coproducts by its specified ordinary adjunction. Apply localization. The defining
bifunctor-derived square for internalScalarTensorComparison and the fixed qTensor
normalization identify its internal representative. Substitute hscalar for each scalar
comparison and htensor for the derived tensorator comparison. Cancel the adjacent
comparison isomorphisms to obtain the displayed section square on reconstructed pairs.
For arbitrary section complexes P and Q, apply the inverse exact section equivalence
termwise. Its counit gives chain isomorphisms back to P and Q, and section reconstruction
preserves and reflects flatness and K-flatness. Apply the equation already proved to the
internal pair and use naturality of qTensor, the scalar computation map and signed
totalization to transport it along these counit isomorphisms. This proves the equation
for all the stated unbounded complexes, including zero complexes and the zero ring. -/
theorem coefficientScalarTensorRepresentative (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    (o : Mod.extendScalars (coefficientMap a Z) ⋙
        (ModuleRingedComparison.equivalence S Z).functor ≅
      (ModuleRingedComparison.equivalence R Z).functor ⋙ b.extension)
    (p : internalScalarExtension a Z ⋙
        (ModuleRingedComparison.derivedEquivalence S Z).functor ≅
      (ModuleRingedComparison.derivedEquivalence R Z).functor ⋙ b.derived)
    (m : b.extension.Monoidal)
    (t : ModuleRingedComparison.tensor R Z ⋙ b.derived ≅
      b.derived.prod b.derived ⋙ ModuleRingedComparison.tensor S Z)
    (hgenerator :
      (∀ (M : ModuleRingedComparison.internalModules R Z) (V : Z.ProEtᵒᵖ)
            (s : (condensedRingObj S Z).obj.obj V) (x : M.X.obj.obj V),
          (o.hom.app M).val.app V
              (InternalAbelianSheafModule.internalScalarGenerator.{u + 1, u + 1, u}
                (Scheme.ProEt.topology Z)
                (coefficientMap a Z) M V s x) =
            coefficientSectionScalarPure a Z b
              ((ModuleRingedComparison.equivalence R Z).functor.obj M) V s x))
    (hscalar :
      (∀ (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
            (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z)
            (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
              (.up ℤ)).obj P) →
          (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
            (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z)
            ((ModuleRingedComparison.equivalence R Z).functor.obj (P.X n))) →
          (ModuleRingedComparison.derivedEquivalence S Z).functor.map
              (coefficientInternalScalarComplex a Z P) ≫
            (ModuleRingedComparison.equivalence S Z).functor.mapDerivedCategoryFactors.hom.app
              (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) =
          p.hom.app (DerivedCategory.Q.obj P) ≫
            b.derived.map
              ((ModuleRingedComparison.equivalence R Z).functor.mapDerivedCategoryFactors.hom.app
                P) ≫
            SheafOfModules.scalarPairComplexComparison
              (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
              (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
              b.extension b.extension_additive b.derived
              b.counit (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
                (.up ℤ)).obj P)))
    (hmonoidal :
      (∀ (M N : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
            (s : (ModuleRingedComparison.ring S Z).obj.obj V)
            (x : M.val.obj V) (y : N.val.obj V),
          (m.toOplaxMonoidal.δ M N).val.app V
              (coefficientSectionScalarPure a Z b (M ⊗ N) V s
                (ModuleRingedComparison.sectionPureTensor R Z M N V x y)) =
            ModuleRingedComparison.sectionPureTensor S Z (b.extension.obj M) (b.extension.obj N) V
              (coefficientSectionScalarPure a Z b M V s x)
              (coefficientSectionScalarPure a Z b N V 1 y)))
    (htensor :
      ∀ M N : DerivedCategory (ModuleRingedComparison.internalModules R Z),
          (ModuleRingedComparison.derivedEquivalence S Z).functor.map
              (((internalScalarTensorComparison a Z).app M).app N) ≫
            (ModuleRingedComparison.tensorComparison S Z).hom.app
              ((internalScalarExtension a Z).obj M, (internalScalarExtension a Z).obj N) ≫
            (ModuleRingedComparison.tensor S Z).map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
          p.hom.app (((derivedTensor R Z).obj M).obj N) ≫
            b.derived.map ((ModuleRingedComparison.tensorComparison R Z).hom.app (M, N)) ≫
            t.hom.app ((ModuleRingedComparison.derivedEquivalence R Z).functor.obj M,
              (ModuleRingedComparison.derivedEquivalence R Z).functor.obj N))
    :
    (∀ (P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z) P →
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z) Q →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z) (P.X n)) →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z) (Q.X n)) →
        b.derived.map ((ModuleRingedComparison.qTensor R Z).app (P, Q)) ≫
          SheafOfModules.scalarPairComplexComparison
            (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
            (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
            b.extension b.extension_additive b.derived
            b.counit ((ModuleRingedComparison.totalTensor R Z).obj (P, Q)) ≫
          DerivedCategory.Q.map (coefficientSectionScalarTotal a Z b m P Q) =
        t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (ModuleRingedComparison.tensor S Z).map (Prod.mkHom
            (SheafOfModules.scalarPairComplexComparison
            (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
            (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
            b.extension b.extension_additive b.derived
              b.counit P)
            (SheafOfModules.scalarPairComplexComparison
            (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
            (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
            b.extension b.extension_additive b.derived
              b.counit Q)) ≫
          (ModuleRingedComparison.qTensor S Z).app
            ((b.extension.mapHomologicalComplex (.up ℤ)).obj P,
              (b.extension.mapHomologicalComplex (.up ℤ)).obj Q)) := by
  let d : CoefficientScalarTensorRepresentativeBasicData a Z :=
    { b := b
      o := o
      p := p
      m := m
      t := t }
  let h : CoefficientScalarTensorRepresentativeHypotheses a Z d :=
    { hgenerator := hgenerator
      hscalar := hscalar
      hmonoidal := hmonoidal
      htensor := htensor }
  simpa only [coefficientScalarTensorRepresentativeEquation] using
    (coefficientScalarTensorRepresentative_transport a Z d
      (coefficientScalarTensorRepresentative_internal a Z d h))

end AlgebraicGeometry.ProEtale.CondensedRing
