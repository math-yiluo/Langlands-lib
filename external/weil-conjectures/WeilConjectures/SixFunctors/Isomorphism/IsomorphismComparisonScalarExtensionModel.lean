/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
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
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization

/-!
# Coefficient compatibility: the ordinary and derived scalar models

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50--51
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
The ordinary tensor is expressed in its exact finite-free model. Its completion
comparison is identified with the specified universal derived-tensor comparison.
Split from `WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension`
for compile time.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem tensorModel_hom_ext (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) (f g : A ⟶ B)
    (h : ∀ (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U),
      f.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      g.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)))) : f = g := by
  subst A
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x => exact h U a x
  | add z z' hz hz' => simp only [map_add, hz, hz']

private theorem tensorModel_transport (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ ψ : R ⟶ S)
    (hφ : φ = ψ)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hB : B = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom ((hA.trans (congrArg
      (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans hB.symm)).val.app U
      ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      (eqToHom hB.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} ψ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(ψ.hom.app U).hom] x)) := by
  subst ψ
  subst A
  subst B
  rfl

private theorem tensorModel_natural (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ ψ : R ⟶ S)
    (hφ : φ = ψ)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (f : M ⟶ N)
    (A B C D : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hB : B = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N)
    (hC : C = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (hD : D = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ N)
    (a : A ⟶ B) (b : C ⟶ D)
    (ha : a = eqToHom hA ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom hB.symm)
    (hb : b = eqToHom hC ≫ SheafOfModules.changeOfRingsHom ψ M f ≫ eqToHom hD.symm) :
    a ≫ eqToHom ((hB.trans (congrArg
      (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N) hφ)).trans hD.symm) =
    eqToHom ((hA.trans (congrArg
      (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans hC.symm) ≫ b := by
  subst ψ
  subst A
  subst B
  subst C
  subst D
  simpa using ha.trans hb.symm

private theorem tensorModel_iso (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ ψ : R ⟶ S)
    (hφ : φ = ψ)
    (F G : (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ⥤ (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)))
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hG : ∀ M, G.obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hF N).symm)
    (hmG : ∀ {M N} (f : M ⟶ N), G.map f = eqToHom (hG M) ≫
      SheafOfModules.changeOfRingsHom ψ M f ≫ eqToHom (hG N).symm) :
    ∃! e : F ≅ G, ∀ (M : (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) (U : W.ProEtᵒᵖ)
      (a : S.obj.obj U) (x : M.val.obj U),
      (e.hom.app M).val.app U ((eqToHom (hF M).symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      (eqToHom (hG M).symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf ψ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(ψ.hom.app U).hom] x)) := by
  let hobj (M) := ((hF M).trans (congrArg
    (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans (hG M).symm
  let e : F ≅ G := NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) (by
    intro M N f
    exact tensorModel_natural W φ ψ hφ M N f _ _ _ _ (hF M) (hF N) (hG M) (hG N)
      _ _ (hmF f) (hmG f))
  have he (M) (U) (a) (x) := tensorModel_transport W φ ψ hφ M _ _ (hF M) (hG M) U a x
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply tensorModel_hom_ext W φ M _ _ (hF M)
  intro U a x
  exact (he' M U a x).trans (he M U a x).symm

/-- The two ordinary tensor models have the same pure tensors, with their canonical
coefficient actions. Source: the quotient-cone calculation at Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: the two coefficient maps agree after every quotient projection, so are equal.
The sheafified balanced tensor constructions therefore have identical generators
and relations. Send each displayed generator to the other displayed generator.
This gives inverse natural maps, uniquely determined by local tensor generation. -/
theorem isomorphismScalarSheafModel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! e : integralOrdinaryScalar l E L ι W ≅ completedOrdinaryScalarExtension l E L ι W,
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (integralOrdinaryTensorSection l E L ι W M U a x) =
          completedScalarTensorSection l E L ι W M U a x := by
  have hφ : integralCompletedScalarMap l E L ι W = completedCoefficientMap l E L ι W := by
    apply (completedCoefficientMap_existsUnique l E L ι W).unique
    · exact (integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec
    · exact (completedCoefficientMap_existsUnique l E L ι W).exists.choose_spec
  exact tensorModel_iso W (integralCompletedScalarMap l E L ι W)
    (completedCoefficientMap l E L ι W) hφ (integralOrdinaryScalar l E L ι W)
    (completedOrdinaryScalarExtension l E L ι W)
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose)
    ((completedScalarChangeData l E L ι W).choose_spec.choose)
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose)
    ((completedScalarChangeData l E L ι W).choose_spec.choose_spec.choose)

/-- The actual identity on pure tensors between the two recorded ordinary models.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarSheafModel (W : AlgebraicGeometry.Scheme.{u}) :=
  (isomorphismScalarSheafModel_existsUnique l E L ι W).exists.choose

section DerivedComparison

attribute [local irreducible] integralScalarReductionWitness integralScalarReduction
  integralScalarTensorSection

private theorem scalarChainModel (W : AlgebraicGeometry.Scheme.{u}) :
    NatTrans.mapHomologicalComplex (isomorphismScalarSheafModel l E L ι W).hom
        (ComplexShape.up ℤ) ≫ completedScalarChainComparison l E L ι W =
      integralScalarCompletionChain l E L ι W := by
  apply (integralScalarCompletionChain_existsUnique l E L ι W).unique
  · constructor
    · intro P i n U a x
      dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f,
        NatTrans.mapHomologicalComplex_app_f]
      simp only [Category.assoc, SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply]
      change (((completedScalarChainComparison l E L ι W).app P).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι W P)).f i ≫
        (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op n)) n).f i
        ).val.app U
          (((isomorphismScalarSheafModel l E L ι W).hom.app (P.X i)).val.app U
            (integralOrdinaryTensorSection l E L ι W (P.X i) U a x)) = _
      exact (congrArg (fun z ↦
        (((completedScalarChainComparison l E L ι W).app P).f i ≫
          (CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι W P)).f i ≫
          (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op n)) n).f i
          ).val.app U z)
        ((isomorphismScalarSheafModel_existsUnique l E L ι W).exists.choose_spec
          (P.X i) U a x)).trans
        ((completedScalarChainComparison_existsUnique l E L ι W).exists.choose_spec.1
          P i n U a x)
    · intro P i j hij
      dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f]
      have hj : j = i - 1 := by omega
      subst j
      change ((NatTrans.mapHomologicalComplex
        (isomorphismScalarSheafModel l E L ι W).hom (.up ℤ)).app P).f i ≫
          (((completedScalarChainComparison l E L ι W).app P).f i ≫
            (CochainComplex.mappingCocone.snd
              (completedScalarRoosEndomorphism l E L ι W P)).v i (i - 1) (by omega)) = 0
      have h := (completedScalarChainComparison_existsUnique l E L ι W).exists.choose_spec.2 P i
      change ((completedScalarChainComparison l E L ι W).app P).f i ≫ _ = 0 at h
      rw [h]
      simp
  · exact (integralScalarCompletionChain_existsUnique l E L ι W).exists.choose_spec

attribute [local irreducible] completedScalarChangeData

private theorem exactDerivedModel
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (es : F ≅ G) (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃! e : F.mapDerivedCategory ≅ LF,
      ∀ P : CochainComplex C ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient _ _).obj P) =
        F.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex es (.up ℤ)).hom.app P) := by
  let V := HomotopyCategory.quasiIso C (.up ℤ)
  let : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactorsh.hom V :=
    Functor.isLeftDerivedFunctor_of_inverts V _ G.mapDerivedCategoryFactorsh
  let j : G.mapDerivedCategory ≅ LF :=
    Functor.leftDerivedUnique _ _ G.mapDerivedCategoryFactorsh.hom ε V
  let e := Functor.mapDerivedCategoryNatIso es ≪≫ j
  have he (P : CochainComplex C ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient _ _).obj P) =
        F.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex es (.up ℤ)).hom.app P) := by
    have hj := Functor.leftDerivedNatTrans_app G.mapDerivedCategory LF
      G.mapDerivedCategoryFactorsh.hom ε V (𝟙 _) ((HomotopyCategory.quotient _ _).obj P)
    change j.hom.app _ ≫ ε.app _ = _ at hj
    dsimp only [e, Iso.trans_hom, NatTrans.comp_app]
    rw [Category.assoc]
    erw [hj]
    have hg : G.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ _).obj P) =
        G.mapDerivedCategoryFactors.hom.app P := by
      rw [Functor.mapDerivedCategoryFactorsh_hom_app]
      change G.mapDerivedCategory.map (𝟙 _) ≫
        G.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
      erw [CategoryTheory.Functor.map_id, Category.id_comp,
        CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
    rw [hg]
    simp only [NatTrans.id_app, Category.comp_id]
    exact Functor.mapDerivedCategoryNatIso_fac es P
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply LF.leftDerived_ext ε V
  apply NatTrans.ext
  funext P
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  exact (he' P).trans (he P).symm

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

attribute [-instance] SheafOfModules.instPreadditive in
/-- Identify the exact finite-free tensor model with the universal derived tensor
model, retaining its counit and the SPECIFIED completion comparison χ.
Source: the quotient-cone calculation accompanying Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: both completed coefficient maps have the same finite residue projections,
so they coincide. Their ordinary functors are canonically identified on sheafified
pure tensors. Finite freeness makes ordinary extension exact on every complex.
The universal left-derived counit therefore identifies its localization with
completedDerivedScalarExtension on every complex. The displayed normalization
uniquely determines that natural isomorphism by localization. On a good resolution,
both completion maps have the same quotient augmentation and zero shifted-product
coordinate. Their normalized descent proves the second equation. -/
theorem isomorphismScalarModel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! e : integralOrdinaryDerivedScalar l E L ι W ≅
        completedDerivedScalarExtension l E L ι W,
      (∀ P : CochainComplex (integralTowerModules l E W) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι W P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (isomorphismScalarSheafModel l E L ι W)
                (ComplexShape.up ℤ)).hom.app P)) ∧
      e.hom ≫ completedScalarComparison l E L ι W = scalarCompletion l E L ι W := by
    let F := integralOrdinaryScalar l E L ι W
    let G := completedOrdinaryScalarExtension l E L ι W
    let es : F ≅ G := isomorphismScalarSheafModel l E L ι W
    let LF := completedDerivedScalarExtension l E L ι W
    let ε : DerivedCategory.Qh ⋙ LF ⟶
        G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
      (completedScalarChangeData l E L ι W).choose_spec.choose_spec.choose_spec.choose_spec.2.2
        |>.choose_spec.choose
    let : PreservesFiniteLimits G := preservesFiniteLimits_of_natIso es
    let : PreservesFiniteColimits G := preservesFiniteColimits_of_natIso es
    let V := HomotopyCategory.quasiIso (integralTowerModules l E W) (.up ℤ)
    let : LF.IsLeftDerivedFunctor ε V :=
      (completedScalarChangeData l E L ι W).choose_spec.choose_spec.choose_spec.choose_spec.2.2
        |>.choose_spec.choose_spec.1
    obtain ⟨e, he0, heuniq⟩ := exactDerivedModel F G es LF ε
    have hε (P : CochainComplex (integralTowerModules l E W) ℤ) :
        completedScalarCounit l E L ι W P = ε.app
          ((HomotopyCategory.quotient (integralTowerModules l E W) (.up ℤ)).obj P) := by
      rfl
    have he (P : CochainComplex (integralTowerModules l E W) ℤ) :
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι W P =
          F.mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (isomorphismScalarSheafModel l E L ι W) (.up ℤ)).hom.app P) := by
      rw [hε]
      exact he0 P
    have hc : e.inv ≫ scalarCompletion l E L ι W =
        completedScalarComparison l E L ι W := by
      apply (completedScalarComparison_existsUnique l E L ι W).unique
      · intro P
        dsimp only [NatTrans.comp_app]
        rw [Category.assoc]
        erw [(scalarCompletion_existsUnique l E L ι W).exists.choose_spec.1 P]
        rw [← scalarChainModel l E L ι W]
        dsimp only [NatTrans.comp_app]
        erw [CategoryTheory.Functor.map_comp]
        apply (cancel_epi (e.hom.app (DerivedCategory.Q.obj P.obj))).mp
        simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
        erw [he P.obj]
        rfl
      · exact (completedScalarComparison_existsUnique l E L ι W).exists.choose_spec
    have hec : e.hom ≫ completedScalarComparison l E L ι W =
        scalarCompletion l E L ι W := by
      rw [← hc]
      simp
    refine ⟨e, ⟨he, hec⟩, ?_⟩
    intro e' he'
    apply heuniq e'
    intro P
    rw [← hε P]
    exact he'.1 P

end DerivedComparison

end WeilConjectures
