/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PointDerivedHom.PointDerivedHomModels
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Exact extension and normalized sections for integral point coefficients

Source: main-20261015 blueprint, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence; point comparison,
third paragraph (blueprint: lem-pod-integral-point-coefficient-adjunction).

The coefficient and site universes are independent. All sheaves, scalar maps,
local tensor generators and adjunction formulas reuse PointDerivedHomModels.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.PointDerivedHom
open scoped ChangeOfRings TensorProduct

namespace WeilConjectures.IntegralPointCoefficientAdjunction

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing valuation ring, lifted only into the containing coefficient universe.
Source: blueprint point coefficients
(blueprint: lem-pod-integral-point-coefficient-adjunction). -/
abbrev R := coefficientRing.{t, u} l E 1 true

/-- The existing completed integral coefficient sheaf on the unchanged small site.
Source: blueprint point coefficients
(blueprint: lem-pod-integral-point-coefficient-adjunction). -/
abbrev B := coefficientSheaf.{t, u} k l E 1 true

/-- The limit lift of the actual constant residue maps, with commutativity retained.
Source: blueprint point coefficients
(blueprint: lem-pod-integral-point-coefficient-adjunction). -/
abbrev alpha := coefficientMap.{t, u} k l E 1 true

private theorem finite_transition (n : ℕ)
    (U : (Spec (.of k)).ProEtᵒᵖ)
    (a : ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 2))) :
    (integralCoefficientSheafTransition l E (Spec (.of k)) n).hom.app U
        (scalar.{t, u} k (coefficientSheaf.{t, u} k l E (n + 2) false)
          (coefficientMap.{t, u} k l E (n + 2) false) U a) =
      scalar.{t, u} k (coefficientSheaf.{t, u} k l E (n + 1) false)
        (coefficientMap.{t, u} k l E (n + 1) false) U
          (ULift.up (Padic.coefficientExtensionTransition l E (n + 1) a.down)) := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  let f : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift
  exact (congrArg (fun h ↦ (h.app U).hom a)
    (toSheafify_naturality J ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).map f))).symm

private def continuousRingPresheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj V := CommRingCat.of C(V.unop.left, A)
  map h := CommRingCat.ofHom
    (ContinuousMap.compRightAlgHom A A h.unop.left.base.hom).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def constantToContinuous (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ continuousRingPresheaf X A where
  app V := CommRingCat.ofHom (ContinuousMap.C : A →+* C(V.unop.left, A))
  naturality _ _ h := by ext; rfl

private theorem continuousRingPresheaf_isSheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousRingPresheaf X A) := by
  let : HasLimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    CommRingCat.hasLimitsOfSize.{t + 1, max u (t + 1), t}
  let : PreservesLimitsOfSize.{t, t + 1} (forget CommRingCat.{max u (t + 1)}) :=
    CommRingCat.forget_preservesLimitsOfSize.{t + 1, max u (t + 1), t}
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (continuousRingPresheaf X A) (forget CommRingCat.{max u (t + 1)})]
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.ProEt.topology X) Scheme.proetaleTopology (continuousMapPresheaf A)
    ((isSheaf_fpqcTopology_continuousMapPresheaf A).of_le
      Scheme.proetaleTopology_le_fpqcTopology)

private theorem constantToContinuous_locallyInjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  equalizerSieve_mem {V} a b h := by
    classical
    by_cases he : IsEmpty V.unop.left
    · let _ := he
      exact (Scheme.ProEt.topology X).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology V.unop)
    · obtain ⟨x⟩ := not_isEmpty_iff.mp he
      have hab : a = b := congrArg (fun f : C(V.unop.left, A) ↦ f x) h
      subst b
      simp

private theorem constantToContinuous_locallySurjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  imageSieve_mem {V} f := by
    classical
    change C(V.left, A) at f
    let U (x : V.left) : V.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete {f x}).preimage f.continuous⟩
    let W (x : V.left) : X.ProEt := Scheme.ProEt.mk ((U x).ι ≫ V.hom)
    let i (x : V.left) : W x ⟶ V :=
      MorphismProperty.Over.homMk (U x).ι rfl
    have hm : Presieve.ofArrows W i ∈ Scheme.ProEt.precoverage X V := by
      change (Presieve.ofArrows W i).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage V.left
      rw [Presieve.map_ofArrows]
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro x
        exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
      · intro x
        change IsOpenImmersion (U x).ι
        infer_instance
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hm)
    rw [Sieve.generate_le_iff]
    rintro Y g ⟨x⟩
    refine ⟨f x, ?_⟩
    apply ContinuousMap.ext
    intro y
    exact y.property.symm

namespace Ordinary

attribute [local instance 3000] abSheafify abLocallyBijective

variable (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)

private def constantPresheafHomEquiv
    (M : ModuleCat.{max u (t + 1)} R)
    (Q : PresheafOfModules.{max u (t + 1)}
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj (RingCat.of R))) :
    ((constantPresheaf.{t, u} k R).obj M ⟶ Q) ≃
      (M ⟶ Q.obj (op (finalObject k))) where
  toFun f := f.app (op (finalObject k))
  invFun f :=
    { app := fun U ↦ ModuleCat.ofHom
        ((Q.map (toFinal k U.unop).op).hom.comp f.hom)
      naturality := by
        intro U V i
        ext x
        change Q.map (toFinal k V.unop).op (f.hom x) =
          Q.map i (Q.map (toFinal k U.unop).op (f.hom x))
        rw [← Q.map_comp_apply]
        have h : (toFinal k V.unop).op = (toFinal k U.unop).op ≫ i := by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact (MorphismProperty.Over.w i.unop).symm
        rw [h] }
  left_inv f := by
    ext U x
    exact (PresheafOfModules.naturality_apply f (toFinal k U.unop).op x).symm
  right_inv f := by
    ext x
    change Q.map (toFinal k (finalObject k)).op (f.hom x) = f.hom x
    have h : toFinal k (finalObject k) = 𝟙 _ := by
      apply MorphismProperty.Over.Hom.ext
      rfl
    rw [h, op_id, Q.map_id]
    rfl

private def constantHomEquiv
    (M : ModuleCat.{max u (t + 1)} R)
    (F : Modules.{t, u} k (constantRing.{t, u} k R)) :
    ((constantModules.{t, u} k R).obj M ⟶ F) ≃
      (M ⟶ (sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).obj F) :=
  (PresheafOfModules.sheafificationHomEquiv.{max u (t + 1), t, max u (t + 1), t + 1}
    (constantUnit.{t, u} k R)).trans
    (constantPresheafHomEquiv.{t, u} k M
      ((PresheafOfModules.restrictScalars (constantUnit.{t, u} k R)).obj F.val))

private theorem constantHomEquiv_naturality_left
    {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N)
    (F : Modules.{t, u} k (constantRing.{t, u} k R))
    (g : (constantModules.{t, u} k R).obj N ⟶ F) :
    constantHomEquiv.{t, u} k M F ((constantModules.{t, u} k R).map f ≫ g) =
      f ≫ constantHomEquiv.{t, u} k N F g := by
  change constantPresheafHomEquiv.{t, u} k _ _
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R)).homEquiv _ _
        ((PresheafOfModules.sheafification.{max u (t + 1), t, max u (t + 1), t + 1}
            (constantUnit.{t, u} k R)).map
          ((constantPresheaf.{t, u} k R).map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  rfl

private theorem constantHomEquiv_naturality_right
    (M : ModuleCat.{max u (t + 1)} R)
    {F G : Modules.{t, u} k (constantRing.{t, u} k R)}
    (f : (constantModules.{t, u} k R).obj M ⟶ F) (g : F ⟶ G) :
    constantHomEquiv.{t, u} k M G (f ≫ g) =
      constantHomEquiv.{t, u} k M F f ≫
        (sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).map g := by
  change constantPresheafHomEquiv.{t, u} k _ _
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R)).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private def constantAdjunction :
    constantModules.{t, u} k R ⊣
      sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantHomEquiv.{t, u} k
      homEquiv_naturality_left_symm := by
        intro M N F f g
        apply (constantHomEquiv.{t, u} k M F).injective
        rw [Equiv.apply_symm_apply, constantHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g ↦ constantHomEquiv_naturality_right k _ f g }

open SheafOfModules.CoefficientOrdinaryProof

private def extensionFunctor : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B :=
  constantModules.{t, u} k R ⋙ tensorFunctor.{max u (t + 1), t + 1, t} α

private def extensionSectionsIso :
    restriction.{max u (t + 1), t + 1, t} α ⋙ sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _) ≅
      sections.{t, u} k B α :=
  NatIso.ofComponents (fun F ↦
    (show ((restriction.{max u (t + 1), t + 1, t} α ⋙
      sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).obj F) ≃ₗ[R]
      (sections.{t, u} k B α).obj F from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toModuleIso) (by intros; rfl)

private def extensionAdjunction : extensionFunctor.{t, u} k B α ⊣ sections.{t, u} k B α :=
  ((constantAdjunction.{t, u} k).comp (tensorAdjunction.{max u (t + 1), t + 1, t} α)).ofNatIsoRight
    (extensionSectionsIso.{t, u} k B α)

private theorem constant_exact :
    PreservesFiniteLimits (constantModules.{t, u} k R) ∧
      PreservesFiniteColimits (constantModules.{t, u} k R) := by
  let P := constantPresheaf.{t, u} k R
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits P (PresheafOfModules.sheafification
    (constantUnit.{t, u} k R)),
    comp_preservesFiniteColimits P (PresheafOfModules.sheafification
      (constantUnit.{t, u} k R))⟩

private theorem extension_exact
    (hf : SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      ((SheafOfModules.restrictScalars.{max u (t + 1)}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat RingCat)).map α)).obj
            (SheafOfModules.unit (ring.{t, u} k B)))) :
    PreservesFiniteLimits (extensionFunctor.{t, u} k B α) ∧
      PreservesFiniteColimits (extensionFunctor.{t, u} k B α) := by
  let C := constantRing.{t, u} k R
  let N := (restriction.{max u (t + 1), t + 1, t} α).obj
    (SheafOfModules.unit (ring.{t, u} k B))
  let := SheafOfModules.isMonoidal_W_independentCoefficients C
  let := SheafOfModules.monoidalCategory C
  let := SheafOfModules.symmetricCategory C
  have hN := SheafOfModules.flat_to_cat C N hf
  have : PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorLeft N) := hN.1.1
  obtain ⟨e, he⟩ := SheafOfModules.exists_changeOfRings_tensor_comparison_independent α
  let iso : tensorFunctor.{max u (t + 1), t + 1, t} α ⋙
      SheafOfModules.toSheaf (ring.{t, u} k B) ≅
    CategoryTheory.MonoidalCategory.tensorLeft N ⋙
      SheafOfModules.toSheaf (ring.{t, u} k C) :=
    NatIso.ofComponents e (fun f ↦ he f)
  have : PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorLeft N ⋙
      SheafOfModules.toSheaf (ring.{t, u} k C)) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (tensorFunctor.{max u (t + 1), t + 1, t} α ⋙
      SheafOfModules.toSheaf (ring.{t, u} k B)) :=
    preservesFiniteLimits_of_natIso iso.symm
  have : PreservesFiniteLimits (tensorFunctor.{max u (t + 1), t + 1, t} α) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf _)
  have : PreservesFiniteLimits (constantModules.{t, u} k R) := (constant_exact k).1
  let : (extensionFunctor.{t, u} k B α).IsLeftAdjoint :=
    (extensionAdjunction.{t, u} k B α).isLeftAdjoint
  have : PreservesFiniteColimits (extensionFunctor.{t, u} k B α) :=
    inferInstance
  exact ⟨comp_preservesFiniteLimits _ _, inferInstance⟩

end Ordinary

end WeilConjectures.IntegralPointCoefficientAdjunction
