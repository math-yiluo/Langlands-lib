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
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Reduction preserves triangulated properties after restriction

Source: Bhatt--Scholze, Lemma 6.5.9(3), the two-term free resolution of O_E/ℓ.
(blueprint: lem-weil-pbc-integral-reduction-triangulated-property)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralReductionTriangulatedProperty
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private theorem reduction_mem_aux
    {C : Type*} [Category.{u + 1} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    (n : ℕ) (R S : C) [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (q : R ⟶ S) [IsMonHom q]
    (p : Mod.regular R ⟶ (Mod.comap q).obj (Mod.regular S))
    (w : (n • 𝟙 (Mod.regular R)) ≫ p = 0)
    (hS : (ShortComplex.mk (n • 𝟙 (Mod.regular R)) p w).ShortExact)
    (P : ObjectProperty (DerivedCategory (Mod C R)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (K : DerivedCategory (Mod C R)) (hK : P K)
    (ε : DerivedCategory.Qh ⋙ ((Mod.extendScalars q).leftDerivedFunctor ⋙
          (Mod.comap q).mapDerivedCategory) ⟶
      (tensorLeft ((Mod.comap q).obj (Mod.regular S))).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hε : Functor.IsLeftDerivedFunctor
      ((Mod.extendScalars q).leftDerivedFunctor ⋙ (Mod.comap q).mapDerivedCategory)
      ε (HomotopyCategory.quasiIso (Mod C R) (.up ℤ))) :
    P ((Mod.comap q).mapDerivedCategory.obj ((Mod.extendScalars q).leftDerivedFunctor.obj K)) := by
  have (Z : Mod C R) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj Z) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Z)
      (NatIso.ofComponents (fun Y ↦ β_ Z Y) (by intros; simp [curriedTensor]))
  have : HasColimitsOfShape ℤ (Mod C R) := inferInstance
  have : HasExactColimitsOfShape ℤ (Mod C R) := inferInstance
  have (Z : Mod C R) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj Z) := inferInstance
  have : Abelian.HasFunctorialFlatResolution (Mod C R) := inferInstance
  let B := (Mod.comap q).obj (Mod.regular S)
  have : (tensorLeft B).PreservesKFlatQuasiIso := by
    refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
    intro L hL hLa
    exact (CochainComplex.acyclic_tensorRight_of_kFlat L hL hLa B).of_iso
      ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight B) _).app L).symm
  have wz : ((n : ℤ) • 𝟙 (Mod.regular R)) ≫ p = 0 := by simpa using w
  have hSz : (ShortComplex.mk ((n : ℤ) • 𝟙 (Mod.regular R)) p wz).ShortExact := by
    simpa using hS
  let : MonoidalLinear ℤ (Mod C R) :=
    { whiskerLeft_smul := by intro Z Y W r f; exact (tensorLeft Z).map_zsmul
      smul_whiskerRight := by intro r Y W f Z; exact (tensorRight Z).map_zsmul }
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  have hL' := (HomotopyCategory.kFlat_quotient_obj_iff L).1 hL
  have : IsIso (ε.app ((HomotopyCategory.quotient _ _).obj L)) :=
    ((tensorLeft B).isLeftDerivedFunctor_iff_isIso_app_of_kFlat ε).1 hε L hL'
  let eL : DerivedCategory.Q.obj L ≅ K :=
    (DerivedCategory.quotientCompQhIso _).symm.app L ≪≫ e
  let eRed :
      (Mod.comap q).mapDerivedCategory.obj ((Mod.extendScalars q).leftDerivedFunctor.obj K) ≅
        DerivedCategory.Q.obj (((tensorLeft B).mapHomologicalComplex (.up ℤ)).obj L) :=
    (Mod.comap q).mapDerivedCategory.mapIso
        ((Mod.extendScalars q).leftDerivedFunctor.mapIso e.symm) ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ _).obj L)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  let eSym := DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight B) _).app L)
  let eTensor := (DerivedCategory.QObjTensorSingleFunctorObjIso L hL' B).symm ≪≫
    whiskerLeftIso (DerivedCategory.Q.obj L)
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app B)
  let eCone := eRed ≪≫ eSym ≪≫ eTensor ≪≫ DerivedCategory.reductionIso wz hSz L
  apply P.prop_of_iso eCone.symm
  exact P.ext_of_isTriangulatedClosed₃ _
    (DerivedCategory.mappingCone_triangle_distinguished ((n : ℤ) • 𝟙 L))
    (P.prop_of_iso eL.symm hK) (P.prop_of_iso eL.symm hK)

/-- Any triangulated property of an integral complex also holds for its derived reduction
regarded as an integral complex by restriction of scalars.

Source: Bhatt--Scholze, Lemma 6.5.9(3), using the two-term free coefficient resolution.
(blueprint: lem-weil-pbc-integral-reduction-triangulated-property)

Proof. Pull the short exact integral coefficient sequence to X; exact monoidal inverse
image identifies it with the short exact sequence from multiplication by ℓ on the regular
integral module to the restricted residue regular module. Choose a K-flat representative
P of K. The assumed derived tensor counit is invertible on P, by the K-flat criterion.
Tensor symmetry and the comparison between derived tensor and termwise tensor on P
identify restricted reduction with P tensored with the residue module in degree zero.
The two-term coefficient resolution identifies this with the cone of multiplication by
ℓ on P. The mapping cone triangle is distinguished. Its first two objects are isomorphic
to K, so triangulated closure and isomorphism invariance give the assertion. This works
for unbounded K, for the zero complex, and on the empty scheme. -/
theorem integralReduction_restricted_mem
    (X : Scheme.{u})
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)))) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))) (hK : P K)
    (ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E X ⋙
          (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory) ⟶
        Functor.mapHomotopyCategory
          (tensorLeft ((Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).obj
            (Mod.regular (condensedRingObj
              (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X)))) (.up ℤ) ⋙
          DerivedCategory.Qh)
    (hε : Functor.IsLeftDerivedFunctor
        (integralReduction ℓ E X ⋙
          (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory)
        ε (HomotopyCategory.quasiIso
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (integralCoeff ℓ E) X)) (.up ℤ))) :
    P ((Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory.obj
      ((integralReduction ℓ E X).obj K)) := by
  let F := upperStarFromPoint X
  have : F.IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : PreservesFiniteLimits F := by
    dsimp [F, upperStarFromPoint, pointUpperStar]
    infer_instance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj (integralResidue ℓ E)) X
  let q := coefficientMap (integralReductionMap ℓ E) X
  let B := (Mod.comap q).obj (Mod.regular S)
  let p : Mod.regular R ⟶ B := Mod.homMk q (by
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
  exact reduction_mem_aux ℓ R S q p w hS P K hK ε hε

end AlgebraicGeometry.ProEtale.CondensedRing
