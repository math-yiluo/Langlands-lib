/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
import all WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralReductionUnderlyingDirectImage
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportSheaves
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Finite quotient supported classical window

Source: Stacks Project, etale-cohomology.tex, Tag 0A45; proetale.tex, Tags 09B1
and 09AA; blueprint `lem-sfb-finite-quotient-supported-classical-window`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.DerivedNakayama
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private noncomputable instance abSheafNatColimits (X : Scheme.{u}) :
    HasColimitsOfShape ℕ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall.{u + 2, u, u, u + 1} _ _
  exact Sheaf.instHasColimitsOfShape

private theorem ab_classical_iso {X : Scheme.{u}}
    {M N : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (e : M ≅ N)
    (hM : IsClassicalAbelian M) : IsClassicalAbelian N :=
  (ProEtale.isClassical_iso_iff
    ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).mapIso e)).mp hM

private theorem ab_classical_image (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsClassicalAbelian ((comparisonUpperStar Ab.{u + 1} X).obj M) := by
  apply (classical_iff_counit X _).mpr
  infer_instance

private theorem ab_classical_image_derived (X : Scheme.{u})
    (M : DerivedCategory (Sheaf X.smallEtaleTopology Ab.{u + 1})) (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((comparisonUpperStar Ab.{u + 1} X).mapDerivedCategory.obj M)) := by
  exact ab_classical_iso
    (((comparisonUpperStar Ab.{u + 1} X).mapDerivedCategoryHomologyFunctorIso q).app M)
    (ab_classical_image X _)

private theorem ab_classical_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (hM : IsClassicalAbelian M) :
    IsClassicalAbelian ((ProEtale.upperStar Ab.{u + 1} f).obj M) := by
  have := (classical_iff_counit Y M).mp hM
  let e := asIso ((comparisonAdjunction Ab.{u + 1} Y).counit.app M)
  apply ab_classical_iso
    ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).symm.app _ ≪≫
      (ProEtale.upperStar Ab.{u + 1} f).mapIso e)
  exact ab_classical_image X _

private theorem ab_comparison_derived_unit (X : Scheme.{u}) :
    IsIso (comparisonAdjunction Ab.{u + 1} X).derivedPlus.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic
    (comparisonAdjunction Ab.{u + 1} X)
    (fun _ _ ↦ inferInstance)
    (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective Ab.{u + 1} X I) K

private theorem ab_classical_counit (X : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K.obj)) :
    IsIso ((comparisonAdjunction Ab.{u + 1} X).derivedPlus.counit.app K) := by
  have := ab_comparison_derived_unit X
  let L := comparisonUpperStar Ab.{u + 1} X
  let adj := (comparisonAdjunction Ab.{u + 1} X).derivedPlus
  let G := (comparisonLowerStar Ab.{u + 1} X).rightDerivedFunctorPlus
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  have ff := adj.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hsingle (Y : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (hY : L.essImage Y) :
      IsIso (adj.counit.app ((DerivedCategory.Plus.singleFunctor _ 0).obj Y)) := by
    obtain ⟨Z, ⟨e⟩⟩ := hY
    let e' := (L.mapDerivedCategoryPlusSingleFunctor 0).app Z ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e
    exact adj.isIso_counit_app_of_iso e'.symm
  apply DerivedCategory.Plus.isIso_app_of_bounded adj.counit L.essImage hsingle K a b
  intro q
  let Y := (DerivedCategory.Plus.homologyFunctor _ q).obj K
  have hY : IsClassicalAbelian Y := hK q
  have := (classical_iff_counit X Y).mp hY
  exact ⟨_, ⟨asIso ((comparisonAdjunction Ab.{u + 1} X).counit.app Y)⟩⟩

private theorem ab_classical_direct_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (a b : ℤ) (hbound : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hK : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K))
    (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((ProEtale.lowerStar Ab.{u + 1} f).rightDerivedFunctor.obj K)) := by
  have hge : K.IsGE a := (DerivedCategory.isGE_iff K a).mpr
    (fun q hq ↦ hbound q (Or.inl hq))
  have hle : K.IsLE b := (DerivedCategory.isLE_iff K b).mpr
    (fun q hq ↦ hbound q (Or.inr hq))
  let Kp : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    ⟨K, a, hge⟩
  have : Kp.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Kp a).mp hge
  have : Kp.IsLE b := (DerivedCategory.Plus.isLE_ι_obj_iff Kp b).mp hle
  have := ab_classical_counit X Kp a b hK
  let e := asIso ((comparisonAdjunction Ab.{u + 1} X).derivedPlus.counit.app Kp)
  let M := (comparisonLowerStar Ab.{u + 1} X).rightDerivedFunctorPlus.obj Kp
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f Ab.{u + 1})) := by
    have := isIso_lowerStarComparisonUpperStarBaseChange f Ab.{u + 1}
    exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange f Ab.{u + 1}))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective
        Ab.{u + 1} f I)
  let c := asIso (Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange f Ab.{u + 1}))
  let d := c.app M ≪≫ (ProEtale.lowerStar Ab.{u + 1} f).rightDerivedFunctorPlus.mapIso e
  let Z := (Etale.lowerStar Ab.{u + 1} f).rightDerivedFunctorPlus.obj M
  let d' := ((comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategoryPlusCompatibility.app Z) ≪≫
    DerivedCategory.Plus.ι.mapIso d ≪≫
    (ProEtale.lowerStar Ab.{u + 1} f).rightDerivedFunctorPlusCompatibility.app Kp
  apply ab_classical_iso ((DerivedCategory.homologyFunctor _ q).mapIso d')
  exact ab_classical_image_derived Y Z.obj q

private theorem ab_classical_triangle (X : Scheme.{u})
    (T : Pretriangulated.Triangle
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})))
    (hT : T ∈ Pretriangulated.distinguishedTriangles) (a b c d : ℤ)
    (h₂ : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj T.obj₂))
    (h₃ : ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj T.obj₃))
    (hc₂ : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj T.obj₂))
    (hc₃ : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj T.obj₃))
    (q : ℤ) : IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj T.obj₁) := by
  have := ab_comparison_derived_unit X
  let L := comparisonUpperStar Ab.{u + 1} X
  let adj := (comparisonAdjunction Ab.{u + 1} X).derivedPlus
  let ff := adj.fullyFaithfulLOfIsIsoUnit
  have : L.mapDerivedCategoryPlus.Full := ff.full
  let F := L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι
  have hmem (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
      (a b : ℤ) (hb : ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
      (hK : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K)) :
      F.essImage K := by
    have hge : K.IsGE a := (DerivedCategory.isGE_iff K a).mpr
      (fun q hq ↦ hb q (Or.inl hq))
    have hle : K.IsLE b := (DerivedCategory.isLE_iff K b).mpr
      (fun q hq ↦ hb q (Or.inr hq))
    let Kp : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
      ⟨K, a, hge⟩
    have : Kp.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Kp a).mp hge
    have : Kp.IsLE b := (DerivedCategory.Plus.isLE_ι_obj_iff Kp b).mp hle
    have := ab_classical_counit X Kp a b hK
    exact ⟨_, ⟨DerivedCategory.Plus.ι.mapIso (asIso (adj.counit.app Kp))⟩⟩
  obtain ⟨M, ⟨e⟩⟩ := F.essImage.ext_of_isTriangulatedClosed₁ T hT
    (hmem _ a b h₂ hc₂) (hmem _ c d h₃ hc₃)
  apply ab_classical_iso ((DerivedCategory.homologyFunctor _ q).mapIso e)
  exact ab_classical_image_derived X M.obj q

private theorem module_classical_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : pulledBackModuleObjects Λ Y) (hM : IsClassicalAbelian M.X) :
    IsClassicalAbelian ((upperStar Λ f).obj M).X := by
  apply ab_classical_iso ((profinitePointModuleForgetPullbackIso Λ f).app M).symm
  exact ab_classical_pullback f M.X hM

private theorem module_classical_derived_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (pulledBackModuleObjects Λ Y))
    (hK : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X)
    (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((upperStar Λ f).mapDerivedCategory.obj K)).X := by
  apply ab_classical_iso ((Mod.forget (condensedRingObj Λ X)).mapIso
    (((upperStar Λ f).mapDerivedCategoryHomologyFunctorIso q).app K))
  exact module_classical_pullback Λ f _ (hK q)

private theorem module_classical_reflect_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : pulledBackModuleObjects Λ Z)
    (hM : IsClassicalAbelian ((lowerStar Λ i).obj M).X) : IsClassicalAbelian M.X := by
  have := moduleCounitOfAbelian Λ i
    (ProEtale.abelian_closed_support_counit_and_unit i j hij).1
  apply ab_classical_iso ((Mod.forget (condensedRingObj Λ Z)).mapIso
    (asIso ((upperStarLowerStarAdjunction Λ i).counit.app M)))
  exact module_classical_pullback Λ i _ hM

private theorem quotient_annihilator
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    (l ^ n : Padic.coefficientExtensionRing l E n) = 0 := by
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hval : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    have hext := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
    change spectralNorm (Padic l) E (l : E) < 1
    simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := l))
  have hl : (l : O) ∈ Ideal.span ({π} : Set O) := by
    rw [hgen]
    exact (h.2.1 (l : O)).mpr hval
  have hp : (l : O) ^ n ∈ Padic.coefficientExtensionIdeal l E n :=
    Ideal.pow_mem_pow hl n
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  simpa only [map_pow, map_natCast] using hz

private theorem functor_annihilator
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (M : A) (r : ℕ) (h : r • 𝟙 M = 0) :
    r • 𝟙 (F.obj M) = 0 := by
  calc
    r • 𝟙 (F.obj M) = r • F.map (𝟙 M) :=
      congrArg (fun f ↦ r • f) (F.map_id M).symm
    _ = F.map (r • 𝟙 M) := F.map_nsmul.symm
    _ = F.map 0 := congrArg F.map h
    _ = 0 := F.map_zero M M

private theorem ell_torsion_of_annihilated
    {A : Type*} [Category* A] [Abelian A] [HasColimitsOfShape ℕ A]
    (l : ℕ) (hl : l.Prime) (M : A) (e : ℕ) (he : (l ^ e) • 𝟙 M = 0) :
    IsEllPowerTorsion l hl M := by
  have hi : 𝟙 M ≫ ((l ^ e) • 𝟙 M) = 0 := by simpa using he
  let D := ellPowerKernelFunctor l (F := M)
  let a := ellPowerKernelColimitMap l (F := M)
  let b : M ⟶ colimit D :=
    kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e
  have hba : b ≫ a = 𝟙 M := by
    dsimp [b, a, ellPowerKernelColimitMap]
    rw [Category.assoc, colimit.ι_desc]
    exact kernel.lift_ι _ _ _
  have hab : a ≫ b = 𝟙 (colimit D) := by
    apply colimit.hom_ext
    intro r
    let t := e + r
    have her : e ≤ t := Nat.le_add_right e r
    have hrt : r ≤ t := Nat.le_add_left r e
    have hmap : kernel.ι ((l ^ r) • 𝟙 M) ≫
        kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ D.map (homOfLE her) =
        D.map (homOfLE hrt) := by
      apply (cancel_mono (kernel.ι ((l ^ t) • 𝟙 M))).mp
      simp only [D, ellPowerKernelFunctor, ellPowerKernelMap, Category.assoc,
        kernel.lift_ι, Category.comp_id]
    calc
      colimit.ι D r ≫ a ≫ b =
          kernel.ι ((l ^ r) • 𝟙 M) ≫
            kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e := by
        dsimp [a, b, ellPowerKernelColimitMap]
        rw [← Category.assoc, colimit.ι_desc]
        rfl
      _ = kernel.ι ((l ^ r) • 𝟙 M) ≫
            kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫
              D.map (homOfLE her) ≫ colimit.ι D t := by rw [colimit.w]
      _ = D.map (homOfLE hrt) ≫ colimit.ι D t := by
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ colimit.ι D t) hmap
      _ = colimit.ι D r ≫ 𝟙 _ := by rw [colimit.w, Category.comp_id]
  exact ⟨⟨b, hab, hba⟩⟩

private theorem window_module_annihilator
    {A : Type*} [Category* A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] {R : A} [MonObj R] (r : ℕ)
    (h : r • 𝟙 R = 0) (M : Mod A R) : r • 𝟙 M = 0 := by
  have hη : r • η[R] = 0 := by
    simpa only [Preadditive.comp_nsmul, Category.comp_id, comp_zero] using
      congrArg (fun f ↦ η[R] ≫ f) h
  apply Mod.hom_ext
  change r • 𝟙 M.X = 0
  calc
    r • 𝟙 M.X = (λ_ M.X).inv ≫ (r • η[R]) ▷ M.X ≫ Mod.act M.X := by
      simp only [MonoidalCategory.nsmul_whiskerRight, Preadditive.comp_nsmul,
        Preadditive.nsmul_comp, Mod.one_act, Iso.inv_hom_id]
    _ = 0 := by rw [hη]; simp

private theorem window_quotient_annihilator
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ)
    (C : DerivedCategory (supportModules (quotientRing l E n) X)) :
    (l ^ n) • 𝟙 C = 0 := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hpoint : (l ^ n) • 𝟙 (quotientRing l E n) = 0 := by
    apply Sheaf.hom_ext
    ext S f
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    change (l ^ n) • f.down s = 0
    rw [nsmul_eq_mul, Nat.cast_pow, quotient_annihilator l E n, zero_mul]
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hring : (l ^ n) • 𝟙 (condensedRingObj (quotientRing l E n) X) = 0 := by
    exact functor_annihilator (upperStarFromPoint X) _ _ hpoint
  let K := DerivedCategory.Q.objPreimage C
  let e : DerivedCategory.Q.obj K ≅ C := DerivedCategory.Q.objObjPreimageIso C
  have hK : (l ^ n) • 𝟙 K = 0 := by
    apply HomologicalComplex.hom_ext
    intro q
    rw [HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f,
      HomologicalComplex.zero_f]
    exact window_module_annihilator _ hring (K.X q)
  have hQ := functor_annihilator DerivedCategory.Q K (l ^ n) hK
  have he := congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) hQ
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
    Category.id_comp, Iso.inv_hom_id, comp_zero, zero_comp] using he

private theorem window_support_triangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    ∃ adj : lowerStar Λ i ⊣ closedSupport Λ i j,
      letI := closedSupport_lowerStarExact Λ i j (by rw [hij, compl_compl])
      ∃ δ : (upperStar Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
        ((closedSupport Λ i j).rightDerivedFunctor ⋙
          (lowerStar Λ i).mapDerivedCategory) ⋙
            shiftFunctor (DerivedCategory (supportModules Λ X)) (1 : ℤ),
        ∀ K, Pretriangulated.Triangle.mk
          (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K)
          ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app K)
          (δ.app K) ∈ Pretriangulated.distinguishedTriangles := by
  have hji : Set.range i.base = (Set.range j.base)ᶜ := by rw [hij, compl_compl]
  let := closedSupport_lowerStarExact Λ i j hji
  refine ⟨closedSupportAdjunction Λ i j hji, ?_⟩
  exact transportAdjunctionTriangle
    (closedSupportAdjunction Λ i j hji).mapDerivedCategoryRightDerivedAdjunction
    (closedSupportDerivedAdjunction Λ i j hji)
    (upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction
    (closedSupportOpenDerivedAdjunction Λ j) (closedSupport_triangle Λ i j hji)

private theorem window_heart_bound
    (l : ℕ) [Fact l.Prime] {V X : Scheme.{u}} (j : V ⟶ X)
    [QuasiCompact j] [QuasiSeparated j] (c : ℕ)
    (hc : relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j ≤ (c : WithTop ℕ))
    (M : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (hM : IsClassicalAbelian M ∧ IsEllPowerTorsion l (Fact.out : l.Prime) M)
    (q : ℤ) (hq : q < 0 ∨ (c : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((ProEtale.lowerStar Ab.{u + 1} j).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  rcases hq with hq | hq
  · have := (ProEtale.lowerStar Ab.{u + 1} j).isGE_rightDerivedFunctor_obj_singleFunctor M
    exact DerivedCategory.isZero_of_isGE _ 0 q hq
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    by_contra hn
    have hle : (r : WithTop ℕ) ≤
        relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j :=
      le_sSup ⟨r, rfl, M, hM.1, hM.2, hn⟩
    have hle := hle.trans hc
    have hrc : r ≤ c := WithTop.coe_le_coe.mp hle
    exact (not_le_of_gt hq) (Int.ofNat_le.mpr hrc)

private theorem window_image_bound
    (l : ℕ) [Fact l.Prime] {V X : Scheme.{u}} (j : V ⟶ X)
    [QuasiCompact j] [QuasiSeparated j] (c : ℕ)
    (hc : relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j ≤ (c : WithTop ℕ))
    (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}))
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K) ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, q < a ∨ b + (c : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((ProEtale.lowerStar Ab.{u + 1} j).rightDerivedFunctor.obj K)) := by
  let T := (ProEtale.lowerStar Ab.{u + 1} j).rightDerivedFunctor
  let P : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1} → Prop := fun M ↦
    ∀ q : ℤ, q < 0 ∨ (c : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (T.obj ((DerivedCategory.singleFunctor _ 0).obj M)))
  have h := DerivedCategory.bounded_heart_amplitude _ _ T P
    (fun M N e h q hq ↦ (h q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        (T.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e))).symm)
    (fun q _ ↦ (DerivedCategory.homologyFunctor _ q).map_isZero
      (T.map_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero (isZero_zero _))))
    0 c (by omega) (fun _ h ↦ h) a b hab K hK
    (fun q ↦ window_heart_bound l j c hc _ (hclass q))
  simpa using h

private theorem window_support_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S Z V : Scheme.{u}} (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (c : ℕ)
    (hc : relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j ≤ (c : WithTop ℕ))
    (a b : ℤ) (hab : a ≤ b)
    (B : integralDerived l E X)
    (hB : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj B))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
        ((Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
          (AdicCompletion.ring l E V)).mapDerivedCategory.obj
          ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B))) ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
            (AdicCompletion.ring l E V)).mapDerivedCategory.obj
            ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B)))) :
    ∀ q : ℤ, q < a ∨ b + (c : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((upperStar (integralCoefficientRing l E) v).mapDerivedCategory.obj
          ((closedSupport
          (integralCoefficientRing l E) i j).rightDerivedFunctor.obj B))) := by
  let Λ := integralCoefficientRing l E
  let J := (upperStar Λ j).mapDerivedCategory.obj B
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (AdicCompletion.ring l E V)
  let W := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.ring l E X)
  have hJ (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (U.mapDerivedCategory.obj J)) :=
    U.isZero_homologyFunctor_mapDerivedCategory_obj
      ((upperStar Λ j).isZero_homologyFunctor_mapDerivedCategory_obj (hB q hq))
  have hL := window_image_bound l j c hc a b hab _ hJ hclass
  have hLi (q : ℤ) (hq : q < a ∨ b + (c : ℤ) < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar Λ j).rightDerivedFunctor.obj J)) := by
    apply W.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    exact (hL q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((integralForgetDirectImageIso l E j).app J))
  obtain ⟨adj, htri⟩ := window_support_triangle Λ i j hij
  let : PreservesFiniteColimits (lowerStar Λ i) := by
    have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
      adj.leftAdjoint_preservesColimits
    infer_instance
  obtain ⟨δ, hδ⟩ := htri
  have hcounit := moduleCounitOfAbelian Λ i
    (ProEtale.abelian_closed_support_counit_and_unit i j hij).1
  have ff := (upperStarLowerStarAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.faithful
  intro q hq
  apply (upperStar Λ v).isZero_homologyFunctor_mapDerivedCategory_obj
  apply (lowerStar Λ i).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  have h₁ := hLi (q - 1) (by rcases hq with hq | hq <;> omega)
  have h₃ := hB q (by rcases hq with hq | hq <;> omega)
  exact (DerivedCategory.HomologySequence.exact₁ _ (hδ B) (q - 1) q (by omega)).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

private theorem window_support_classical
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S Z V : Scheme.{u}} (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (c : ℕ)
    (hc : relativeCohomologicalDimension.{u} l (Fact.out : l.Prime) j ≤ (c : WithTop ℕ))
    (a b : ℤ) (hab : a ≤ b)
    (B : integralDerived l E X)
    (hB : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj B))
    (hBc : ∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj B).X)
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
        ((Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
          (AdicCompletion.ring l E V)).mapDerivedCategory.obj
          ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B))) ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
            (AdicCompletion.ring l E V)).mapDerivedCategory.obj
            ((upperStar (integralCoefficientRing l E) j).mapDerivedCategory.obj B))))
    (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      ((upperStar (integralCoefficientRing l E) v).mapDerivedCategory.obj
        ((closedSupport
          (integralCoefficientRing l E) i j).rightDerivedFunctor.obj B))).X := by
  let Λ := integralCoefficientRing l E
  let J := (upperStar Λ j).mapDerivedCategory.obj B
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (AdicCompletion.ring l E V)
  let W := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.ring l E X)
  have hJ (r : ℤ) (hr : r < a ∨ b < r) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (U.mapDerivedCategory.obj J)) :=
    U.isZero_homologyFunctor_mapDerivedCategory_obj
      ((upperStar Λ j).isZero_homologyFunctor_mapDerivedCategory_obj (hB r hr))
  have hL := window_image_bound l j c hc a b hab _ hJ hclass
  let L := (lowerStar Λ j).rightDerivedFunctor.obj J
  let e := (integralForgetDirectImageIso l E j).app J
  have hLb (r : ℤ) (hr : r < a ∨ b + (c : ℤ) < r) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (W.mapDerivedCategory.obj L)) :=
    (hL r hr).of_iso ((DerivedCategory.homologyFunctor _ r).mapIso e)
  have hLc (r : ℤ) : IsClassicalAbelian
      ((DerivedCategory.homologyFunctor _ r).obj (W.mapDerivedCategory.obj L)) :=
    ab_classical_iso ((DerivedCategory.homologyFunctor _ r).mapIso e.symm)
      (ab_classical_direct_image j _ a b hJ (fun r ↦ (hclass r).1) r)
  obtain ⟨adj, htri⟩ := window_support_triangle Λ i j hij
  let : PreservesFiniteColimits (lowerStar Λ i) := by
    have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
      adj.leftAdjoint_preservesColimits
    infer_instance
  obtain ⟨δ, hδ⟩ := htri
  let A := (closedSupport Λ i j).rightDerivedFunctor.obj B
  let T := W.mapDerivedCategory.mapTriangle.obj
    (Pretriangulated.Triangle.mk
      (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app B)
      ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app B)
      (δ.app B))
  have hT := W.mapDerivedCategory.map_distinguished _ (hδ B)
  have hAc (r : ℤ) : IsClassicalAbelian
      ((DerivedCategory.homologyFunctor _ r).obj
        (W.mapDerivedCategory.obj ((lowerStar Λ i).mapDerivedCategory.obj A))) :=
    ab_classical_triangle X T hT a b a (b + c)
      (fun r hr ↦ W.isZero_homologyFunctor_mapDerivedCategory_obj (hB r hr)) hLb
      (fun r ↦ ab_classical_iso ((W.mapDerivedCategoryHomologyFunctorIso r).app B)
        (hBc r)) hLc r
  apply module_classical_derived_pullback Λ v A
  intro r
  apply module_classical_reflect_closed Λ i j hij
  apply ab_classical_iso
    (W.mapIso (((lowerStar Λ i).mapDerivedCategoryHomologyFunctorIso r).app A) ≪≫
      (W.mapDerivedCategoryHomologyFunctorIso r).app
        ((lowerStar Λ i).mapDerivedCategory.obj A)).symm
  exact hAc r

/-- A bounded classical finite quotient complex has a bounded closed-support window.

Source: Stacks Project, etale-cohomology.tex, Tag 0A45; proetale.tex, Tags 09B1
and 09AA; blueprint `lem-sfb-finite-quotient-supported-classical-window`.

The ring objects `Λ_T = p_T^* Λ` carry the canonical transported multiplication
`Functor.monObjObj` of the scoped `CategoryTheory.Obj` instance, as in the closed-support
dependency module.

Proof (the route of the Lean proof; it refines blueprint steps 1--8):
1. Restrict `C` along `A_X → B_X` to the integral complex `K`; restriction is exact with
   identical underlying abelian sheaves, so `K` has cohomology in `[a,b]`, classical.
   `ℓ ∈ (π)` in the DVR `A`, so `ℓ ^ n = 0` in `B`; it kills the continuous coefficient
   ring pointwise, hence `B_X`, hence (unit-action identity) every `B_X`-module, termwise
   every complex, and so `ℓ ^ n • 𝟙 C = 0` and `ℓ ^ n • 𝟙 K = 0`.
2. `J = j_A^* K` has cohomology in `[a,b]`; its underlying cohomology is classical (the
   comparison inverse-image square) and killed by `ℓ ^ n`, hence `ℓ`-power torsion (the
   `ℓ`-power kernel colimit is split by the stage-`n` inclusion).
3. On a classical `ℓ`-power torsion heart object, `Rj_{*,Ab}` has range `[0,c]`: the lower
   bound is the right-derived lower t-bound, the upper one the defining supremum
   `cd_ℓ(j) ≤ c`.  Bounded-heart amplitude puts `Rj_{*,Ab}` of the underlying complex of `J`
   in `[a,b+c]`.
4. The integral forget/direct-image comparison (forgetting `A`-structure commutes with
   `Rj_*`) and faithful exact forgetting give `L = Rj_{*,A} J` in `[a,b+c]`; its underlying
   cohomology is classical by bounded étale descent along the comparison counit and the qcqs
   direct-image comparison.
5. The canonical support triangle `i_* RΓ_Z K → K → Rj_*j^*K`, transported to the published
   `upperStar` presentation by uniqueness of adjoints, and the long exact sequence
   `H^{q-1}(L) → H^q(i_* RΓ_Z K) → H^q(K)` put `RΓ_Z K` in `[a,b+c+1]` (`i_*` exact, faithful).
6. The two outer terms of the forgotten triangle are bounded and classical, so they and their
   arrow descend along the fully faithful bounded-below étale comparison and the fibre is
   classical; the invertible closed counit reflects this from `i_*` to `Z`.  Derived support,
   cohomology and forgetting are additive, so they keep `ℓ ^ n • 𝟙 = 0`: every cohomology
   sheaf is `ℓ`-power torsion, equivalently locally `ℓ`-power torsion.
No constructibility or finite Tor-amplitude is used.
(blueprint: lem-sfb-finite-quotient-supported-classical-window). -/
theorem finite_quotient_supported_classical_window
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [IsNoetherian X]
    [∀ x : X, Invertible (l : X.residueField x)]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b : ℤ) (hab : a ≤ b) (c : ℕ)
    (hcd : (relativeCohomologicalDimension l (Fact.out : l.Prime) j : WithTop ℕ) ≤ c)
    (C : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (quotientRing l E n) X)))
    (hCbound : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C))
    (hCclass : ∀ q : ℤ,
      IsClassicalAbelian
        (((DerivedCategory.homologyFunctor _ q).obj C).X)) :
    (∀ q : ℤ, q < a ∨ b + c + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (((closedSupport (integerRing l E) i j).rightDerivedFunctor).obj
          (((Mod.comap
            ((upperStarFromPoint X).mapMon.map
              (Mon.ofHom (reductionRing l E n))).hom).mapDerivedCategory).obj C)))) ∧
    (∀ q : ℤ,
      IsClassicalAbelian
          (((DerivedCategory.homologyFunctor _ q).obj
            (((closedSupport (integerRing l E) i j).rightDerivedFunctor).obj
              (((Mod.comap
                ((upperStarFromPoint X).mapMon.map
                  (Mon.ofHom (reductionRing l E n))).hom).mapDerivedCategory).obj C))).X) ∧
        IsEllPowerTorsionLocal l (Fact.out : l.Prime)
          (((DerivedCategory.homologyFunctor _ q).obj
            (((closedSupport (integerRing l E) i j).rightDerivedFunctor).obj
              (((Mod.comap
                ((upperStarFromPoint X).mapMon.map
                  (Mon.ofHom (reductionRing l E n))).hom).mapDerivedCategory).obj C))).X)) := by
  have _ := hn
  let R := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStarFromPoint X).mapMon.map (Mon.ofHom (reductionRing l E n))).hom
  let K := R.mapDerivedCategory.obj C
  have hK (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) :=
    R.isZero_homologyFunctor_mapDerivedCategory_obj (hCbound q hq)
  have hKclass (q : ℤ) :
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X := by
    apply ab_classical_iso
      ((Mod.forget (condensedRingObj (integerRing l E) X)).mapIso
        ((R.mapDerivedCategoryHomologyFunctorIso q).app C))
    exact hCclass q
  have hkill : (l ^ n) • 𝟙 K = 0 :=
    functor_annihilator R.mapDerivedCategory C _
      (window_quotient_annihilator l E X n C)
  let Λ := integerRing l E
  let W := Mod.forget (D := Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
    (condensedRingObj Λ U)
  let J := (upperStar Λ j).mapDerivedCategory.obj K
  let := abSheafNatColimits U
  have hJ (q : ℤ) :
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
        (W.mapDerivedCategory.obj J)) ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj (W.mapDerivedCategory.obj J)) := by
    constructor
    · exact ab_classical_iso ((W.mapDerivedCategoryHomologyFunctorIso q).app J)
        (module_classical_derived_pullback Λ j K hKclass q)
    · apply ell_torsion_of_annihilated l (Fact.out : l.Prime) _ n
      exact functor_annihilator (DerivedCategory.homologyFunctor _ q) _ _
        (functor_annihilator W.mapDerivedCategory _ _
          (functor_annihilator (upperStar Λ j).mapDerivedCategory _ _ hkill))
  have hji : Set.range j = (Set.range i)ᶜ := by rw [hij, compl_compl]
  let F := (closedSupport Λ i j).rightDerivedFunctor.obj K
  let I := (upperStar Λ (𝟙 Z)).mapDerivedCategory
  let e : I.obj F ≅ F :=
    ((Functor.mapDerivedCategoryNatIso (upperStarId Λ Z)) ≪≫
      Functor.mapDerivedCategoryIdIso _).app F
  have hb := window_support_bound l E (𝟙 Z) i j hji c hcd a b hab K hK hJ
  have hc := window_support_classical l E (𝟙 Z) i j hji c hcd a b hab K hK hKclass hJ
  refine ⟨fun q hq ↦ (hb q hq).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso e.symm), fun q ↦ ⟨?_, ?_⟩⟩
  · exact ab_classical_iso
      ((Mod.forget (condensedRingObj Λ Z)).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso e)) (hc q)
  · let := abSheafNatColimits Z
    apply (isEllPowerTorsion_iff_local l (Fact.out : l.Prime) _).mp
    apply ell_torsion_of_annihilated l (Fact.out : l.Prime) _ n
    exact functor_annihilator (Mod.forget (condensedRingObj Λ Z)) _ _
      (functor_annihilator (DerivedCategory.homologyFunctor _ q) _ _
        (functor_annihilator (closedSupport Λ i j).rightDerivedFunctor _ _ hkill))

end AlgebraicGeometry.ProEtale.CondensedRing
