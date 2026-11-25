/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization

/-! # Canonical DVR quotient and open comparison interfaces

Source: Stacks Tags 0A0E, 093M and 09BP; blueprint fix-prop-coherence,
strict augmentation comparison and completed open factor.

The coefficient and completion model structures package the canonical comparison
maps and their normalizations. `openQuotientKoszulCompleteness` asserts their existence,
the DVR free resolutions, and preservation of quotient completeness by open extension.
The declarations are reexported unchanged by the original assembly module.
(blueprint: def-sf-open-quotient-koszul-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Fix the additive coefficient size without altering the pro-etale site sizes.
Source: Stacks Tag 03DA (blueprint: lem-sf-open-quotient-koszul-completeness). -/
instance (priority := 2200) openDvrAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, 0} T

/-- Use the existing locally bijective criterion in that same coefficient size.
Source: Stacks Tag 03DA (blueprint: lem-sf-open-quotient-koszul-completeness). -/
instance (priority := 2200) openDvrAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, 0} T

/-- The unchanged small pro-etale site in its natural object universe.
Source: Stacks 09A5 (blueprint: lem-sf-open-quotient-koszul-completeness). -/
instance (priority := 2300) openDvrEssentiallySmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The two-term complex [R -- t^(n+1) --> R] in degrees -1 and 0.
Source: Stacks Tag 093M; arithmetic verification in Step 1
(blueprint: lem-sf-open-quotient-koszul-completeness). -/
def openDvrResolution (n : ℕ) :
    CochainComplex (ModuleCat (Padic.coefficientExtensionIntegers l E)) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).map
      (ModuleCat.ofHom ((LinearMap.lsmul (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l E))
          (Padic.coefficientExtensionUniformizer l E ^ (n + 1)))))

/-- The canonical finite and completed coefficient identifications, with their actions.
All coefficient comparisons are fixed by constant sections and quotient projections.
Source: Stacks Tags 093M and 09BT; Steps 1--3
(blueprint: lem-sf-open-quotient-koszul-completeness). -/
structure OpenDvrCoefficientModel
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) where
  /-- At each level the constant sheaf is identified with continuous component functions. -/
  finite : ∀ n : ℕ, integralCoefficientSheaf.{u, u} l E T n ≅ completedAdicFiniteRing T d n
  /-- The comparison sends each local constant scalar to that same constant function. -/
  finite_constants : ∀ (n : ℕ) (V : T.ProEtᵒᵖ)
      (a : Padic.coefficientExtensionIntegers l E),
    (finite n).hom.hom.app V ((adicLisseConstantUnit T
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).app V
      (ULift.up (Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l E (n + 1)) a))) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app V
          (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a))
  /-- All quotient maps are respected, before taking the limit. -/
  finite_transition : ∀ n : ℕ,
    integralCoefficientSheafTransition.{u, u} l E T n ≫ (finite n).hom =
      (finite (n + 1)).hom ≫ completedAdicFiniteStep T d n
  /-- The completed comparison is an isomorphism of commutative ring sheaves. -/
  completed : completedAdicCommRing T d ≅ completedIntegralCommRingSheafUnrestricted.{u, u} l E T
  /-- It is precisely the comparison induced by the entire finite quotient diagram. -/
  completed_projection : ∀ n : ℕ,
    (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      completed.hom ≫
        limit.π (integralCoefficientSheafSystem.{u, u} l E T) (op n) ≫ (finite n).hom =
      completedAdicProjection T d n
  /-- Transport is actual scalar restriction along this canonical coefficient map. -/
  modules : scalarReductionSource.{u, u} l E T ≌ CompletedAdicModules T d
  modules_functor : modules.functor = SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      completed.hom)
  [additive : modules.functor.Additive]
  [inverse_additive : modules.inverse.Additive]

attribute [instance] OpenDvrCoefficientModel.additive OpenDvrCoefficientModel.inverse_additive

/-- The ordinary unbounded derived coefficient equivalence of the canonical ring comparison.
Source: Stacks Tag 05RT; Step 3
(blueprint: lem-sf-open-quotient-koszul-completeness). -/
abbrev OpenDvrCoefficientModel.derived
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) :
    DerivedCategory (scalarReductionSource.{u, u} l E T) ≌
      DerivedCategory (CompletedAdicModules T d) := C.modules.mapDerivedCategory

/-- Its simultaneous transport of strict towers, before derived inverse limit.
Source: Stacks Tag 0941; Step 3
(blueprint: lem-sf-open-quotient-koszul-completeness). -/
abbrev OpenDvrCoefficientModel.towers
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) :
    coefficientSequenceRestrictedDerived.{u, u} l E T ⥤ DerivedCategory (CompletedAdicTowers T d) :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj C.modules.functor).mapDerivedCategory

/-- Exact simultaneous scalar transport before localization.
Source: Stacks Tag 0941 (blueprint: lem-sf-open-quotient-koszul-completeness). -/
abbrev OpenDvrCoefficientModel.ordinaryTowers
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj C.modules.functor

/-- Scalar transport on one complex.
Source: Stacks Tag 05RT (blueprint: lem-sf-open-quotient-koszul-completeness). -/
abbrev OpenDvrCoefficientModel.complexes
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) :=
  C.modules.functor.mapHomologicalComplex (.up ℤ)

/-- Scalar transport on a complex of strict towers.
Source: Stacks Tag 0941 (blueprint: lem-sf-open-quotient-koszul-completeness). -/
abbrev OpenDvrCoefficientModel.towerComplexes
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) :=
  C.ordinaryTowers.mapHomologicalComplex (.up ℤ)

/-- The simultaneous quotient augmentation and its actual adjunction unit.
The comparisons live in derived categories of strict towers, not just at evaluations.
Source: Stacks Tags 0A0E and 0941; Steps 3--7
(blueprint: lem-sf-open-quotient-koszul-completeness). -/
structure OpenDvrCompletionModel
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) (S : CoefficientDerivedSystemCalculus.{u, u} l E T)
    (hd : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal) where
  /-- The two quotient tower functors are canonically identified. -/
  tower : C.derived.functor ⋙ completedAdicReduction T d ≅
    S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T ⋙ C.towers
  /-- The total-limit comparison is the canonical one under the coefficient equivalence. -/
  rlim : C.towers ⋙ reconstructionRlim T d ≅
    coefficientConstantTowerLimit.{u, u} l E T ⋙ C.derived.functor
  /-- The total-limit comparison extends the ordinary projection-normalized comparison. -/
  limit_model : ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
    ∃ σ : ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).obj
          (C.towerComplexes.obj I) ≅
        C.complexes.obj
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I),
      (∀ (i : ℤ) (n : ℕ),
        σ.hom.f i ≫ C.modules.functor.map (limit.π (I.X i) (op n)) =
          limit.π ((C.towerComplexes.obj I).X i) (op n)) ∧
      C.derived.functor.map
          (derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit I) =
        C.modules.functor.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map σ.inv ≫
          reconstructionRlimComparison T d (C.towerComplexes.obj I) ≫
          (reconstructionRlim T d).map
            (C.ordinaryTowers.mapDerivedCategoryFactors.inv.app I) ≫
          rlim.hom.app (DerivedCategory.Q.obj I)
  /-- The same strict tensor augmentation, before taking total derived inverse limit. -/
  representative : ∀ (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      (_hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (Q.X i)) →
    ∃ (B : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ)
      (a : ((Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _).mapHomologicalComplex
        (.up ℤ)).obj Q ⟶ B)
      (κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj B ≅
        unrestrictedIntegralComplexTower.{u, u} l E T Q)
      (e : (S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T).obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj B)
      (τ : ((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
          (C.complexes.obj Q) ≅ C.towerComplexes.obj B),
      (∀ (i : ℤ) (n : ℕ),
        (reconstructionOrdinaryUnit T d).app (C.modules.functor.obj (Q.X i)) ≫
            limit.π ((completedAdicOrdinaryTower T d).obj
              (C.modules.functor.obj (Q.X i))) (op n) ≫ (τ.hom.f i).app (op n) =
          C.modules.functor.map ((a.f i).app (op n))) ∧
      ((completedAdicReduction T d).map
          (C.modules.functor.mapDerivedCategoryFactors.hom.app Q) ≫
          reconstructionReductionComplexCounit T d (C.complexes.obj Q) ≫
          DerivedCategory.Q.map τ.hom =
        tower.hom.app (DerivedCategory.Q.obj Q) ≫ C.towers.map e.hom ≫
          C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B) ∧
      (∀ n : ℕ, HEq
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app (op n) ≫
          κ.hom.app (op n)) (unrestrictedTowerUnit.{u, u} l E T Q n)) ∧
      (C.derived.functor.map (S.adjunction.unit.app (DerivedCategory.Q.obj Q)) ≫
          C.derived.functor.map ((coefficientConstantTowerLimit.{u, u} l E T).map e.hom) =
        C.derived.functor.map (DerivedCategory.Q.map
          (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
              lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
              ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
                (.up ℤ)).map a) ≫
          derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B))
  /-- The quotient completion unit is the actual semilinear reduction/limit unit. -/
  unit : ∀ P : DerivedCategory (scalarReductionSource.{u, u} l E T),
    (reconstructionCompletionUnit T d).app (C.derived.functor.obj P) ≫
        (reconstructionRlim T d).map (tower.hom.app P) ≫
          rlim.hom.app ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
            (S.reduction.obj P)) =
      C.derived.functor.map (S.adjunction.unit.app P)
  /-- This is the specified Koszul-to-quotient comparison from the recorded reconstruction. -/
  koszul_unit : ∀ P : DerivedCategory (scalarReductionSource.{u, u} l E T),
    (reconstructionKoszulDerivedUnit T d 1
        (fun _ ↦ Padic.coefficientExtensionUniformizer l E)).app (C.derived.functor.obj P) ≫
      (koszulReconstruction T d 1 (fun _ ↦ Padic.coefficientExtensionUniformizer l E)
        hd).choose.hom.app (C.derived.functor.obj P) ≫
      (reconstructionRlim T d).map (tower.hom.app P) ≫
      rlim.hom.app ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
            (S.reduction.obj P)) =
        C.derived.functor.map (S.adjunction.unit.app P)
  /-- The same equation for the intrinsic Koszul fibre and its specified comparison. -/
  intrinsic_unit : ∀ P : DerivedCategory (scalarReductionSource.{u, u} l E T),
    completedAdicIntrinsicUnit T d 1 (fun _ ↦ Padic.coefficientExtensionUniformizer l E)
        (C.derived.functor.obj P) ≫
      (reconstructionKoszulIntrinsicComparison T d 1
        (fun _ ↦ Padic.coefficientExtensionUniformizer l E)
        (C.derived.functor.obj P)).choose.inv ≫
      (koszulReconstruction T d 1 (fun _ ↦ Padic.coefficientExtensionUniformizer l E)
        hd).choose.hom.app (C.derived.functor.obj P) ≫
      (reconstructionRlim T d).map (tower.hom.app P) ≫
      rlim.hom.app ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
        (S.reduction.obj P)) = C.derived.functor.map (S.adjunction.unit.app P)
  /-- Quotient Roos completeness is equivalent to invertibility of the intrinsic Koszul unit. -/
  complete_iff : ∀ P : DerivedCategory (scalarReductionSource.{u, u} l E T),
    IsDerivedCompleteUnrestricted.{u, u} l E T P ↔
      IsIso (completedAdicIntrinsicUnit T d 1
        (fun _ ↦ Padic.coefficientExtensionUniformizer l E) (C.derived.functor.obj P))

/-- Open coefficient restriction, fixed on finite constant sections and all limit projections.
The extension is the exact adjoint to actual restriction from the recorded open model.
Source: Stacks Tags 03DI and 09BP; Step 8
(blueprint: lem-sf-open-quotient-koszul-completeness). -/
structure OpenDvrOpenModel {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] where
  /-- The finite constant comparison on the open site. -/
  finite : ∀ n : ℕ,
    (SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op ⋙
        (integralCoefficientCommRingSheaf.{u, u} l E X n).obj ≅
      (integralCoefficientCommRingSheaf.{u, u} l E U n).obj
  /-- The finite restriction comparison is identity on constants. -/
  finite_constants : ∀ (n : ℕ) (V : U.ProEtᵒᵖ)
      (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))),
    (finite n).hom.app V
        ((adicLisseConstantUnit X _).app
          ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj V) a) =
      (adicLisseConstantUnit U _).app V a
  /-- Completed restriction is induced by the finite quotient comparisons. -/
  ring : SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) ≅
    completedIntegralCommRingSheafUnrestricted.{u, u} l E U
  ring_projection : ∀ n : ℕ,
    Functor.whiskerLeft
        (SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n).hom ≫
          (finite n).hom =
      ring.hom.hom ≫ (completedIntegralCommRingProjectionUnrestricted.{u, u} l E U n).hom
  /-- The scalar equivalence is actual restriction along the canonical ring comparison. -/
  modules : scalarReductionSource.{u, u} l E U ≌
    AlgebraicGeometry.Scheme.ProjectionRestriction.Mod
      (SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))
  modules_functor : modules.functor = SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ring.hom)
  [additive : modules.functor.Additive]
  [inverse_additive : modules.inverse.Additive]
  /-- The actual exact extension, with its restriction adjunction and section normalization. -/
  extension : SheafOfModules.OpenTensorNormalization.OpenExtension .ordinary j
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)

attribute [instance] OpenDvrOpenModel.additive OpenDvrOpenModel.inverse_additive

/-- Localized extension by zero after the canonical completed coefficient restriction.
Source: Stacks Tags 03DI and 09BP
(blueprint: lem-sf-open-quotient-koszul-completeness). -/
abbrev OpenDvrOpenModel.jShriek {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (O : OpenDvrOpenModel l E j) :
    DerivedCategory (scalarReductionSource.{u, u} l E U) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E X) :=
  O.modules.mapDerivedCategory.functor ⋙
    O.extension.ordinary.mapDerivedCategory

/-- Use the already normalized reduction/limit calculus, retaining its actual unit.
Source: Stacks Tags 07A6 and 0941
(blueprint: lem-sf-open-quotient-koszul-completeness). -/
abbrev openDvrSystem (T : Scheme.{u}) : CoefficientDerivedSystemCalculus.{u, u} l E T :=
  (coefficientDerivedSystemEvaluationCalculus.{u, u} l E T).choose

end WeilConjectures
