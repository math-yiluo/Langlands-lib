/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-! # Vanishing reduction and multiplication by ℓ

Source: Bhatt--Scholze, Section 6.5, the two-term resolution of the residue ring.
(blueprint: lem-weil-pbc-integral-reduction-scalar)
-/

@[expose] public section

universe u v w

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private theorem reductionScalar_aux
    {C : Type w} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
    [Abelian.HasFunctorialFlatResolution C]
    (n : ℕ) (R S : C) [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (q : R ⟶ S) [IsMonHom q]
    (p : Mod.regular R ⟶ (Mod.comap q).obj (Mod.regular S))
    (w : (n • 𝟙 (Mod.regular R)) ≫ p = 0)
    (hS : (ShortComplex.mk (n • 𝟙 (Mod.regular R)) p w).ShortExact)
    (K : DerivedCategory (Mod C R))
    (hK : IsZero ((Mod.extendScalars q).leftDerivedFunctor.obj K)) :
    IsIso (n • 𝟙 K) := by
  have (Z : Mod C R) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj Z) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Z)
      (NatIso.ofComponents (fun Y ↦ β_ Z Y) (by intros; simp [curriedTensor]))
  have : HasColimitsOfShape ℤ (Mod C R) :=
    inferInstance
  have : HasExactColimitsOfShape ℤ (Mod C R) :=
    inferInstance
  have (Z : Mod C R) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj Z) := inferInstance
  have : Abelian.HasFunctorialFlatResolution
      (Mod C R) := inferInstance
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso K
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P).1 hP
  let ext := Mod.extendScalars q
  let ε := ext.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)
  have : IsIso ε := ext.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP'
  have hLP : IsZero (ext.leftDerivedFunctor.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) :=
    hK.of_iso (ext.leftDerivedFunctor.mapIso e)
  have hEP : IsZero (DerivedCategory.Q.obj
      ((ext.mapHomologicalComplex (.up ℤ)).obj P)) := by
    exact (hLP.of_iso (asIso ε).symm).of_iso
      ((DerivedCategory.quotientCompQhIso _).symm.app _)
  have hE := (DerivedCategory.isZero_Q_obj_iff _).1 hEP
  have hforget := hE.map (Mod.forget S)
  have hten : (((tensorLeft ((Mod.comap q).obj (Mod.regular S))).mapHomologicalComplex
      (.up ℤ)).obj P).Acyclic := by
    intro n
    apply (ShortComplex.exact_map_iff_of_faithful _ (Mod.forget R)).1
    have h := hforget.of_iso
      ((NatIso.mapHomologicalComplex (Mod.extendForgetTensorIso q) (.up ℤ)).app P)
    exact h n
  have hright : (((tensorRight ((Mod.comap q).obj (Mod.regular S))).mapHomologicalComplex
      (.up ℤ)).obj P).Acyclic :=
    hten.of_iso ((NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight ((Mod.comap q).obj (Mod.regular S)))
        (.up ℤ)).app P)
  have hQr := (DerivedCategory.isZero_Q_obj_iff _).2 hright
  have hDtensor := hQr.of_iso
    (DerivedCategory.QObjTensorSingleFunctorObjIso P hP' ((Mod.comap q).obj (Mod.regular S)))
  have hQtensor := hDtensor.of_iso (whiskerLeftIso (DerivedCategory.Q.obj P)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
      ((Mod.comap q).obj (Mod.regular S))).symm)
  have wz : ((n : ℤ) • 𝟙 (Mod.regular R)) ≫ p = 0 := by simpa using w
  have hSz : (ShortComplex.mk ((n : ℤ) • 𝟙 (Mod.regular R)) p wz).ShortExact := by
    simpa using hS
  let : MonoidalLinear ℤ (Mod C R) :=
    { whiskerLeft_smul := by intro Z Y W r f; exact (tensorLeft Z).map_zsmul
      smul_whiskerRight := by intro r Y W f Z; exact (tensorRight Z).map_zsmul }
  have hcone := hQtensor.of_iso (DerivedCategory.reductionIso wz hSz P).symm
  have hiso : IsIso (DerivedCategory.Q.map ((n : ℤ) • 𝟙 P)) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (DerivedCategory.mappingCone_triangle_distinguished ((n : ℤ) • 𝟙 P))).mp hcone
  have hnp : IsIso (n • 𝟙 (DerivedCategory.Q.obj P)) := by
    simp only [natCast_zsmul] at hiso
    simpa using hiso
  let eP : DerivedCategory.Q.obj P ≅ K :=
    (DerivedCategory.quotientCompQhIso _).symm.app P ≪≫ e
  have h : n • 𝟙 K = eP.inv ≫ (n • 𝟙 (DerivedCategory.Q.obj P)) ≫ eP.hom := by
    simp
  rw [h]
  infer_instance

/-- If the derived reduction of any integral complex vanishes, multiplication by ℓ is
invertible on it. No constructibility or boundedness is needed.
Source: Bhatt--Scholze, Section 6.5, two-term residue resolution.
(blueprint: lem-weil-pbc-integral-reduction-scalar)

Proof: pull the proved short exact coefficient sequence to X. Its two free terms
resolve the residue module. After tensoring with a K-flat representative of K this
identifies restriction of its derived reduction with the cone of multiplication by ℓ.
Restriction of scalars preserves zero objects. Thus this cone is zero, and the
associated distinguished triangle shows that multiplication by ℓ is invertible.
This applies to unbounded complexes and includes the zero complex and empty X. -/
theorem integralReduction_isIso_nsmul_of_isZero (X : Scheme.{u})
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)))
    (hK : IsZero ((integralReduction ℓ E X).obj K)) : IsIso (ℓ • 𝟙 K) := by
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteColimits pointUpperStar.{u} := by
    have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance
  let F := upperStarFromPoint X
  have : PreservesFiniteLimits F := by dsimp [F, upperStarFromPoint]; infer_instance
  have : PreservesFiniteColimits F := by dsimp [F, upperStarFromPoint]; infer_instance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj (integralResidue ℓ E)) X
  let q := coefficientMap (integralReductionMap ℓ E) X
  let p : Mod.regular R ⟶ (Mod.comap q).obj (Mod.regular S) :=
    Mod.homMk q (by
      change μ[R] ≫ q = R ◁ q ≫ (q ▷ S) ≫ μ[S]
      rw [IsMonHom.mul_hom, tensorHom_def']
      exact Category.assoc _ _ _)
  have w : (ℓ • 𝟙 (Mod.regular R)) ≫ p = 0 := by
    apply (Mod.forget R).map_injective
    change (ℓ • 𝟙 R) ≫ q = 0
    have h := congrArg F.map (integralReduction_comp_zero ℓ E)
    change F.map ((ℓ • 𝟙 (integralCoeff ℓ E)) ≫ integralReductionMap ℓ E) = F.map 0 at h
    rw [F.map_comp, F.map_nsmul, F.map_id, F.map_zero] at h
    exact h
  have hS : (ShortComplex.mk (ℓ • 𝟙 (Mod.regular R)) p w).ShortExact := by
    apply ShortExact.reflects_shortExact_of_faithful (Mod.forget R)
    have h := (integralReductionSequence_shortExact ℓ E).map_of_exact F
    change (ShortComplex.mk (ℓ • 𝟙 (F.obj (integralCoeff ℓ E)))
      (F.map (integralReductionMap ℓ E)) _).ShortExact
    simpa [integralReductionSequence, ShortComplex.map] using h
  exact reductionScalar_aux ℓ R S q p w hS K hK

end AlgebraicGeometry.ProEtale.CondensedRing
