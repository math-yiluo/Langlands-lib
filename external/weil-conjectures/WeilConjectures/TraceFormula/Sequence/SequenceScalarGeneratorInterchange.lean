/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import Mathlib.Algebra.Homology.HomologicalComplex
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
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Ordinary scalar and geometric interchange on strict quotient systems

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D (ordinary composition);
sites-modules.tex, tensor/restriction adjunction, Tags 03D7 and 03EK;
the agent-formulated whole-sequence calculation extracted from mixed coherence
(blueprint: lem-trf-sequence-scalar-generator-interchange).

The six routes below are composites of the recorded ordinary comparisons.
Functor associators only make the parenthesization explicit. No derived scalar
functor, K-flat hypothesis, realization or flatness of quotient maps is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] integralComparisonSequenceScalarModel
  CategoryTheory.Functor.leftAdjoint

attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local irreducible] HasDerivedCategory.standard

private theorem scalar_transpose_apply
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat} (φ : R ⟶ S)
    {F : SheafOfModules R ⥤ SheafOfModules S}
    (adj : F ⊣ SheafOfModules.restrictScalars φ)
    (σ : ∀ (N : SheafOfModules R) (U : Cᵒᵖ), N.val.obj U → (F.obj N).val.obj U)
    (hσ : ∀ N U x, (adj.unit.app N).val.app U x = σ N U x)
    (N : SheafOfModules R) (T : SheafOfModules S) (a : F.obj N ⟶ T)
    (U : Cᵒᵖ) (x : N.val.obj U) :
    (adj.homEquiv N T a).val.app U x = a.val.app U (σ N U x) := by
  rw [Adjunction.homEquiv_unit]
  change a.val.app U ((adj.unit.app N).val.app U x) = _
  rw [hσ]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem scalarAdjunction (X : Scheme.{t}) :
    ∃ adj : (integralComparisonSequenceScalarModel l E L ι X).E ⊣
      SheafOfModules.restrictScalars ((sheafCompose
        (coefficientSequenceTopology (ProEt.topology X)) (forget₂ CommRingCat RingCat)).map
          (integralComparisonSequenceScalarMap l E L ι X)),
      ∀ (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ)
        (x : N.val.obj U), (adj.unit.app N).val.app U x =
          integralComparisonSequenceTensorSection l E L ι X N U 1 x := by
  obtain ⟨_, _, ho⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralComparisonSequenceScalarMap l E L ι X)
  let D := integralComparisonSequenceScalarModel l E L ι X
  obtain ⟨a, ha⟩ := ho D.E D.obj_eq D.map_eq
  refine ⟨a, ?_⟩
  intro N U x
  have hu := ha N (D.E.obj N) (eqToHom (D.obj_eq N).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at hu
  exact hu

private theorem tensor_map_unit (X : Scheme.{t})
    {N N' : coefficientSequenceModules l E X} (a : N ⟶ N')
    (U : (ℕ × X.ProEt)ᵒᵖ) (x : N.val.obj U) :
    ((integralComparisonSequenceScalarModel l E L ι X).E.map a).val.app U
      (integralComparisonSequenceTensorSection l E L ι X N U 1 x) =
    integralComparisonSequenceTensorSection l E L ι X N' U 1 (a.val.app U x) := by
  obtain ⟨adj, hu⟩ := scalarAdjunction l E L ι X
  have h := congrArg (fun q ↦ q.val.app U x) (adj.unit.naturality a)
  change (adj.unit.app N').val.app U (a.val.app U x) =
    ((integralComparisonSequenceScalarModel l E L ι X).E.map a).val.app U
      ((adj.unit.app N).val.app U x) at h
  rw [hu, hu] at h
  exact h.symm

private theorem tensor_restrict_unit (X : Scheme.{t})
    (N : coefficientSequenceModules l E X) (n : ℕ) {U V : X.ProEt}
    (a : U ⟶ V) (x : N.val.obj (op (n, V))) :
    ((integralComparisonSequenceScalarModel l E L ι X).E.obj N).val.map
      (Prod.mkHom (𝟙 n) a).op
      (integralComparisonSequenceTensorSection l E L ι X N (op (n, V)) 1 x) =
    integralComparisonSequenceTensorSection l E L ι X N (op (n, U)) 1
      (N.val.map (Prod.mkHom (𝟙 n) a).op x) := by
  obtain ⟨adj, hu⟩ := scalarAdjunction l E L ι X
  have h := PresheafOfModules.naturality_apply (adj.unit.app N).val
    (Prod.mkHom (𝟙 n) a).op x
  change (adj.unit.app N).val.app (op (n, U))
      (N.val.map (Prod.mkHom (𝟙 n) a).op x) =
    ((integralComparisonSequenceScalarModel l E L ι X).E.obj N).val.map
      (Prod.mkHom (𝟙 n) a).op ((adj.unit.app N).val.app (op (n, V)) x) at h
  rw [hu, hu] at h
  exact h.symm

private theorem generator_natural {X Y : Scheme.{t}} (f : X ⟶ Y)
    {N N' : coefficientSequenceModules l E Y} (a : N ⟶ N')
    (n : ℕ) (U : Y.ProEt) (x : N.val.obj (op (n, U))) :
    ((integralComparisonSequencePullback l E f).map a).val.app
      (op (n, (proEtaleBaseChange f).obj U))
      (integralComparisonSequenceGenerator l E f N n U x) =
    integralComparisonSequenceGenerator l E f N' n U (a.val.app (op (n, U)) x) := by
  have h := congrArg (fun q ↦ q.val.app (op (n, U)) x)
    ((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E f)).unit.naturality a)
  exact h.symm

private theorem pullback_transpose_apply {X Y : Scheme.{t}} (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y) (T : coefficientSequenceModules l E X)
    (a : (integralComparisonSequencePullback l E f).obj N ⟶ T)
    (n : ℕ) (U : Y.ProEt) (x : N.val.obj (op (n, U))) :
    (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).homEquiv
      N T a).val.app (op (n, U))) x =
    a.val.app (op (n, (proEtaleBaseChange f).obj U))
      (integralComparisonSequenceGenerator l E f N n U x) := by
  rfl

private theorem composition_generator {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) (N : coefficientSequenceModules l E V)
    (n : ℕ) (U : V.ProEt) (x : N.val.obj (op (n, U))) :
    ((integralComparisonSequenceComposition l E h k).hom.app N).val.app
      (op (n, (proEtaleBaseChange (h ≫ k)).obj U))
      (integralComparisonSequenceGenerator l E (h ≫ k) N n U x) =
    ((integralComparisonSequencePullback l E k ⋙
      integralComparisonSequencePullback l E h).obj N).val.map
        (Prod.mkHom (𝟙 n) ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op
      (integralComparisonSequenceGenerator l E h
        ((integralComparisonSequencePullback l E k).obj N) n
        ((proEtaleBaseChange k).obj U)
        (integralComparisonSequenceGenerator l E k N n U x)) := by
  obtain ⟨d, hd, hv⟩ :=
    (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose_spec
  let adj := (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)).comp
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h))
  let adj' := Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E (h ≫ k))
  have hc : conjugateEquiv adj adj'
      (integralComparisonSequenceComposition l E h k).hom = d.hom :=
    congrArg Iso.hom hd
  have hu := unit_conjugateEquiv adj adj'
    (integralComparisonSequenceComposition l E h k).hom N
  rw [hc] at hu
  have hs := congrArg (fun q ↦ q.val.app (op (n, U)) x) hu
  dsimp only [Adjunction.comp_unit_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hs
  erw [hv] at hs
  exact hs.symm

private theorem tensor_smul (X : Scheme.{t}) (N : coefficientSequenceModules l E X)
    (U : (ℕ × X.ProEt)ᵒᵖ) (c : (coefficientSequenceCommRingSheaf l L X).obj.obj U)
    (x : N.val.obj U) :
    integralComparisonSequenceTensorSection l E L ι X N U c x =
      c • integralComparisonSequenceTensorSection l E L ι X N U 1 x := by
  let D := integralComparisonSequenceScalarModel l E L ι X
  let φ := integralComparisonSequenceScalarMap l E L ι X
  let η := (PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (J := coefficientSequenceTopology (ProEt.topology X))
    (𝟙 ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
      (forget₂ CommRingCat RingCat)).obj (coefficientSequenceCommRingSheaf l L X)).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ N)
  change (eqToHom (D.obj_eq N).symm).val.app U
      (η.app U (c ⊗ₜ[_, (φ.hom.app U).hom] x)) =
    c • (eqToHom (D.obj_eq N).symm).val.app U
      (η.app U ((1 : (coefficientSequenceCommRingSheaf l L X).obj.obj U)
        ⊗ₜ[_, (φ.hom.app U).hom] x))
  rw [← ((eqToHom (D.obj_eq N).symm).val.app U).hom.map_smul]
  rw [← (η.app U).hom.map_smul]
  congr 2
  change (c ⊗ₜ[_, (φ.hom.app U).hom] x) = ((c * 1) ⊗ₜ[_, (φ.hom.app U).hom] x)
  rw [mul_one]

private theorem tensor_map (X : Scheme.{t})
    {N N' : coefficientSequenceModules l E X} (a : N ⟶ N')
    (U : (ℕ × X.ProEt)ᵒᵖ) (c : (coefficientSequenceCommRingSheaf l L X).obj.obj U)
    (x : N.val.obj U) :
    ((integralComparisonSequenceScalarModel l E L ι X).E.map a).val.app U
      (integralComparisonSequenceTensorSection l E L ι X N U c x) =
    integralComparisonSequenceTensorSection l E L ι X N' U c (a.val.app U x) := by
  calc
    _ = c • ((integralComparisonSequenceScalarModel l E L ι X).E.map a).val.app U
        (integralComparisonSequenceTensorSection l E L ι X N U 1 x) := by
      rw [tensor_smul l E L ι X N U c x]
      exact (((integralComparisonSequenceScalarModel l E L ι X).E.map a).val.app U).hom.map_smul
        c _
    _ = c • integralComparisonSequenceTensorSection l E L ι X N' U 1
        (a.val.app U x) := congrArg (fun y ↦ c • y) (tensor_map_unit l E L ι X a U x)
    _ = _ := (tensor_smul l E L ι X N' U c (a.val.app U x)).symm

private theorem generator_smul {X Y : Scheme.{t}} (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf l E Y).obj.obj (op (n, U)))
    (x : N.val.obj (op (n, U))) :
    integralComparisonSequenceGenerator l E f N n U (b • x) =
      integralComparisonSequenceRingComponent l E f (op (n, U)) b •
        (show ((integralComparisonSequencePullback l E f).obj N).val.obj
          (op (n, (proEtaleBaseChange f).obj U)) from
            integralComparisonSequenceGenerator l E f N n U x) := by
  exact (((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f)).unit.app N).val.app (op (n, U))).hom.map_smul
      b x

private theorem scalar_pullback_tensor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf l L Y).obj.obj (op (n, U)))
    (x : N.val.obj (op (n, U))) :
    ((integralComparisonSequenceScalarPullback l E L ι f).hom.app N).val.app
      (op (n, (proEtaleBaseChange f).obj U))
      (integralComparisonSequenceTensorSection l E L ι X
        ((integralComparisonSequencePullback l E f).obj N)
        (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceRingComponent l L f (op (n, U)) b)
        (integralComparisonSequenceGenerator l E f N n U x)) =
    integralComparisonSequenceGenerator l L f
      ((integralComparisonSequenceScalarModel l E L ι Y).E.obj N) n U
      (integralComparisonSequenceTensorSection l E L ι Y N (op (n, U)) b x) := by
  have h := (integralComparisonSequenceScalarPullback_existsUnique l E L ι f).exists.choose_spec
    N n U x
  rw [tensor_smul l E L ι X _ _ _ _]
  erw [(((integralComparisonSequenceScalarPullback l E L ι f).hom.app N).val.app
    (op (n, (proEtaleBaseChange f).obj U))).hom.map_smul, h]
  rw [tensor_smul l E L ι Y N (op (n, U)) b x]
  exact (generator_smul l L f _ n U b
    (integralComparisonSequenceTensorSection l E L ι Y N (op (n, U)) 1 x)).symm

/-- The route through the geometric compositor over E and then both scalar squares.
Source: Stacks 0D6D, tensor/restriction adjunction, 03D7 and 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange). -/
def sequenceScalarGeometricLeft {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V) :=
  Functor.whiskerRight
      (integralComparisonSequenceComposition l E h k).hom
      (integralComparisonSequenceScalarModel l E L ι Z).E ≫
    (Functor.associator (integralComparisonSequencePullback l E k)
      (integralComparisonSequencePullback l E h)
      (integralComparisonSequenceScalarModel l E L ι Z).E).hom ≫
    Functor.whiskerLeft (integralComparisonSequencePullback l E k)
      (integralComparisonSequenceScalarPullback l E L ι h).hom ≫
    (Functor.associator (integralComparisonSequencePullback l E k)
      (integralComparisonSequenceScalarModel l E L ι W).E
      (integralComparisonSequencePullback l L h)).inv ≫
    Functor.whiskerRight
      (integralComparisonSequenceScalarPullback l E L ι k).hom
      (integralComparisonSequencePullback l L h) ≫
    (Functor.associator (integralComparisonSequenceScalarModel l E L ι V).E
      (integralComparisonSequencePullback l L k)
      (integralComparisonSequencePullback l L h)).hom

/-- The route through the composite scalar square and the geometric compositor over L.
Source: Stacks 0D6D, tensor/restriction adjunction, 03D7 and 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange). -/
def sequenceScalarGeometricRight {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V) :=
  (integralComparisonSequenceScalarPullback l E L ι (h ≫ k)).hom ≫
    Functor.whiskerLeft (integralComparisonSequenceScalarModel l E L ι V).E
      (integralComparisonSequenceComposition l L h k).hom

/-- The identity-coefficient square followed by multiplication at the source.
Source: Stacks 0D6D, tensor/restriction adjunction, 03D7 and 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange). -/
def sequenceScalarUnitLeft {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (integralComparisonSequenceScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom ≫
    Functor.whiskerRight
      (integralComparisonSequenceScalarUnit l E Y).hom (integralComparisonSequencePullback l E f) ≫
    (Functor.leftUnitor (integralComparisonSequencePullback l E f)).hom

/-- Multiplication at the target after ordinary geometric inverse image.
Source: Stacks 0D6D, tensor/restriction adjunction, 03D7 and 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange). -/
def sequenceScalarUnitRight {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  Functor.whiskerLeft (integralComparisonSequencePullback l E f)
      (integralComparisonSequenceScalarUnit l E X).hom ≫
    (Functor.rightUnitor (integralComparisonSequencePullback l E f)).hom

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

/-- The two scalar squares followed by multiplication of the coefficient factors.
Source: Stacks 0D6D, tensor/restriction adjunction, 03D7 and 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange). -/
def sequenceScalarTowerLeft {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (Functor.associator (integralComparisonSequencePullback l E f)
      (integralComparisonSequenceScalarModel l E L ι X).E
      (integralComparisonSequenceScalarModel l L M j X).E).inv ≫
    Functor.whiskerRight
      (integralComparisonSequenceScalarPullback l E L ι f).hom
      (integralComparisonSequenceScalarModel l L M j X).E ≫
    (Functor.associator (integralComparisonSequenceScalarModel l E L ι Y).E
      (integralComparisonSequencePullback l L f)
      (integralComparisonSequenceScalarModel l L M j X).E).hom ≫
    Functor.whiskerLeft (integralComparisonSequenceScalarModel l E L ι Y).E
      (integralComparisonSequenceScalarPullback l L M j f).hom ≫
    (Functor.associator (integralComparisonSequenceScalarModel l E L ι Y).E
      (integralComparisonSequenceScalarModel l L M j Y).E
      (integralComparisonSequencePullback l M f)).inv ≫
    Functor.whiskerRight
      (integralComparisonSequenceScalarComposition l E L ι M j Y).hom
      (integralComparisonSequencePullback l M f)

/-- Multiplication of coefficient factors followed by the composite scalar square.
Source: Stacks 0D6D, tensor/restriction adjunction, 03D7 and 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange). -/
def sequenceScalarTowerRight {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  Functor.whiskerLeft (integralComparisonSequencePullback l E f)
      (integralComparisonSequenceScalarComposition l E L ι M j X).hom ≫
    (integralComparisonSequenceScalarPullback l E M (j.comp ι) f).hom

/-- Equality is determined on local iterated-unit tensor generators by adjunction.
Source: Stacks tensor/restriction adjunction, 03D7, 03EK and 0DV0
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: transpose first along tensor/restriction, then along inverse image/direct
image. The displayed values are exactly the section values of the transposes.
They agree at every sequence-site object and section, hence the transposes and
therefore the original maps agree. This uses sheafification uniqueness rather
than a claim that all sections are globally pure tensors. -/
theorem sequenceScalarPullback_hom_ext
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ x : Y, IsUnit (l : Y.presheaf.stalk x))
    (N : coefficientSequenceModules l E Y) (T : coefficientSequenceModules l L X)
    (a b : (integralComparisonSequenceScalarModel l E L ι X).E.obj
      ((integralComparisonSequencePullback l E f).obj N) ⟶ T)
    (hab : ∀ (n : ℕ) (U : Y.ProEt) (x : N.val.obj (op (n, U))),
      a.val.app (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l E L ι X
          ((integralComparisonSequencePullback l E f).obj N)
          (op (n, (proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceGenerator l E f N n U x)) =
      b.val.app (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l E L ι X
          ((integralComparisonSequencePullback l E f).obj N)
          (op (n, (proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceGenerator l E f N n U x))) : a = b := by
  obtain ⟨adj, hu⟩ := scalarAdjunction l E L ι X
  apply (adj.homEquiv _ T).injective
  apply ((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f)).homEquiv N _).injective
  ext A x
  rcases A with ⟨⟨n, U⟩⟩
  rw [pullback_transpose_apply, pullback_transpose_apply]
  simp only [scalar_transpose_apply _ adj
    (fun P A x ↦ integralComparisonSequenceTensorSection l E L ι X P A 1 x) hu]
  exact hab n U x

/-- The twice-iterated adjunction also determines maps on unit tensor generators.
Source: Stacks tensor/restriction adjunction, 03D7, 03EK and 0DV0
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: transpose successively through the outer tensor adjunction, the inner
tensor adjunction, and the inverse-image adjunction. The displayed composites
are exactly the values of the transposes on every local section of N. Sectionwise
equality gives equality of the transposes and injectivity of the three adjunction
bijections gives equality of the original maps. Sheafification uniqueness removes
any need to write arbitrary sheaf sections as global pure tensors. -/
theorem sequenceScalarTowerPullback_hom_ext
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ x : Y, IsUnit (l : Y.presheaf.stalk x))
    (N : coefficientSequenceModules l E Y) (T : coefficientSequenceModules l M X)
    (a b : (integralComparisonSequenceScalarModel l L M j X).E.obj
      ((integralComparisonSequenceScalarModel l E L ι X).E.obj
        ((integralComparisonSequencePullback l E f).obj N)) ⟶ T)
    (hab : ∀ (n : ℕ) (U : Y.ProEt) (x : N.val.obj (op (n, U))),
      a.val.app (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l L M j X
          ((integralComparisonSequenceScalarModel l E L ι X).E.obj
            ((integralComparisonSequencePullback l E f).obj N))
          (op (n, (proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceTensorSection l E L ι X
            ((integralComparisonSequencePullback l E f).obj N)
            (op (n, (proEtaleBaseChange f).obj U)) 1
            (integralComparisonSequenceGenerator l E f N n U x))) =
      b.val.app (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l L M j X
          ((integralComparisonSequenceScalarModel l E L ι X).E.obj
            ((integralComparisonSequencePullback l E f).obj N))
          (op (n, (proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceTensorSection l E L ι X
            ((integralComparisonSequencePullback l E f).obj N)
            (op (n, (proEtaleBaseChange f).obj U)) 1
            (integralComparisonSequenceGenerator l E f N n U x)))) : a = b := by
  obtain ⟨adj, hu⟩ := scalarAdjunction l E L ι X
  obtain ⟨adj', hu'⟩ := scalarAdjunction l L M j X
  apply (adj'.homEquiv _ T).injective
  apply (adj.homEquiv _ _).injective
  apply ((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f)).homEquiv N _).injective
  ext A x
  rcases A with ⟨⟨n, U⟩⟩
  rw [pullback_transpose_apply, pullback_transpose_apply]
  simp only [scalar_transpose_apply _ adj
    (fun P A x ↦ integralComparisonSequenceTensorSection l E L ι X P A 1 x) hu]
  simp only [scalar_transpose_apply _ adj'
    (fun P A x ↦ integralComparisonSequenceTensorSection l L M j X P A 1 x) hu']
  exact hab n U x

/-- The common scalar-unit route sends 1 tensor gamma_f(x) to gamma_f(x).
Source: Stacks tensor/restriction adjunction, 03D7, 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: the scalar square sends the input to gamma_f(1 tensor x).
Naturality of gamma_f with the multiplication unitor gives gamma_f(x).
The other route multiplies the scalar 1 directly; ordinary unit interchange
identifies the routes on the whole system. -/
theorem sequenceScalarUnit_generator
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ x : Y, IsUnit (l : Y.presheaf.stalk x))
    (N : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
    (x : N.val.obj (op (n, U))) :
    ((sequenceScalarUnitLeft l E f).app N).val.app
      (op (n, (proEtaleBaseChange f).obj U))
      (integralComparisonSequenceTensorSection l E E (AlgHom.id ℚ_[l] E) X
        ((integralComparisonSequencePullback l E f).obj N)
        (op (n, (proEtaleBaseChange f).obj U)) 1
        (integralComparisonSequenceGenerator l E f N n U x)) =
      integralComparisonSequenceGenerator l E f N n U x := by
  have hs := (integralComparisonSequenceScalarPullback_existsUnique
    l E E (AlgHom.id ℚ_[l] E) f).exists.choose_spec N n U x
  change ((integralComparisonSequencePullback l E f).map
      ((integralComparisonSequenceScalarUnit l E Y).hom.app N)).val.app
        (op (n, (proEtaleBaseChange f).obj U))
      (((integralComparisonSequenceScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom.app
        N).val.app (op (n, (proEtaleBaseChange f).obj U)) _) = _
  erw [hs]
  have hn := generator_natural l E f
    ((integralComparisonSequenceScalarUnit l E Y).hom.app N) n U
    (integralComparisonSequenceTensorSection l E E (AlgHom.id ℚ_[l] E)
      Y N (op (n, U)) 1 x)
  have hu := (integralComparisonSequenceScalarUnit_existsUnique l E Y).exists.choose_spec
    N (op (n, U)) 1 x
  erw [hu, one_smul] at hn
  exact hn

/-- The common geometric route has the specified iterated-unit tensor value.
The restriction along fibre-product pasting makes the two test objects explicit.
Source: Stacks 0D6D, 03D7, 03EK; mixed calculation on adjunction-unit generators
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: apply the unit equation for the prescribed compositor mate, then the
scalar/pullback generator equation twice and naturality of gamma_h. Both routes
give gamma_h(gamma_k(1 tensor x)), restricted along the canonical pasting map.
This proves the value on every source section, not only global sections. -/
theorem sequenceScalarGeometric_generator
    {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (_hV : ∀ x : V, IsUnit (l : V.presheaf.stalk x))
    (_hW : ∀ x : W, IsUnit (l : W.presheaf.stalk x))
    (_hZ : ∀ x : Z, IsUnit (l : Z.presheaf.stalk x))
    (N : coefficientSequenceModules l E V) (n : ℕ) (U : V.ProEt)
    (x : N.val.obj (op (n, U))) :
    ((sequenceScalarGeometricLeft l E L ι h k).app N).val.app
      (op (n, (proEtaleBaseChange (h ≫ k)).obj U))
      (integralComparisonSequenceTensorSection l E L ι Z
        ((integralComparisonSequencePullback l E (h ≫ k)).obj N)
        (op (n, (proEtaleBaseChange (h ≫ k)).obj U)) 1
        (integralComparisonSequenceGenerator l E (h ≫ k) N n U x)) =
    ((integralComparisonSequencePullback l L k ⋙
      integralComparisonSequencePullback l L h).obj
        ((integralComparisonSequenceScalarModel l E L ι V).E.obj N)).val.map
          (CategoryTheory.Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op
      (integralComparisonSequenceGenerator l L h
        ((integralComparisonSequencePullback l L k).obj
          ((integralComparisonSequenceScalarModel l E L ι V).E.obj N)) n
        ((proEtaleBaseChange k).obj U)
        (integralComparisonSequenceGenerator l L k
          ((integralComparisonSequenceScalarModel l E L ι V).E.obj N) n U
          (integralComparisonSequenceTensorSection l E L ι V N (op (n, U)) 1 x))) := by
  have hh := (integralComparisonSequenceScalarPullback_existsUnique l E L ι h).exists.choose_spec
    ((integralComparisonSequencePullback l E k).obj N) n ((proEtaleBaseChange k).obj U)
    (integralComparisonSequenceGenerator l E k N n U x)
  have hk := (integralComparisonSequenceScalarPullback_existsUnique l E L ι k).exists.choose_spec
    N n U x
  let A := op (n, (proEtaleBaseChange (h ≫ k)).obj U)
  change ((integralComparisonSequencePullback l L h).map
      ((integralComparisonSequenceScalarPullback l E L ι k).hom.app N)).val.app A
    (((integralComparisonSequenceScalarPullback l E L ι h).hom.app
      ((integralComparisonSequencePullback l E k).obj N)).val.app A
        (((integralComparisonSequenceScalarModel l E L ι Z).E.map
          ((integralComparisonSequenceComposition l E h k).hom.app N)).val.app A _)) = _
  have hc := composition_generator l E h k N n U x
  have ht := tensor_restrict_unit l E L ι Z
    ((integralComparisonSequencePullback l E k ⋙
      integralComparisonSequencePullback l E h).obj N) n
    ((MorphismProperty.Over.pullbackComp h k).hom.app U)
    (integralComparisonSequenceGenerator l E h
      ((integralComparisonSequencePullback l E k).obj N) n
      ((proEtaleBaseChange k).obj U)
      (integralComparisonSequenceGenerator l E k N n U x))
  erw [tensor_map_unit l E L ι Z
    ((integralComparisonSequenceComposition l E h k).hom.app N) A
    (integralComparisonSequenceGenerator l E (h ≫ k) N n U x)]
  erw [hc, ← ht]
  erw [PresheafOfModules.naturality_apply
    ((integralComparisonSequenceScalarPullback l E L ι h).hom.app
      ((integralComparisonSequencePullback l E k).obj N)).val
    (Prod.mkHom (𝟙 n) ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op]
  erw [hh]
  erw [PresheafOfModules.naturality_apply
    ((integralComparisonSequencePullback l L h).map
      ((integralComparisonSequenceScalarPullback l E L ι k).hom.app N)).val
    (Prod.mkHom (𝟙 n) ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op]
  erw [generator_natural l L h
    ((integralComparisonSequenceScalarPullback l E L ι k).hom.app N)]
  erw [hk]
  rfl

/-- The common tower route has value gamma_f(c*j(b) tensor x), with source-local
coefficients transported by the recorded constant-coefficient maps.
Source: Stacks tensor/restriction adjunction, 03D7, 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: the two scalar squares give c tensor gamma_f(b tensor x), then
gamma_f(c tensor (b tensor x)). Naturality with the recorded scalar associator
multiplies the coefficients to c*j(b). The other route multiplies them first.
The adjunction argument proves equality for arbitrary target-local sections;
this explicit value only uses b,c on the source test object. All restriction
maps preserve products and intertwine j, including non-flat quotient maps. -/
theorem sequenceScalarTower_generator
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ x : Y, IsUnit (l : Y.presheaf.stalk x))
    (N : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf l L Y).obj.obj (op (n, U)))
    (c : (coefficientSequenceCommRingSheaf l M Y).obj.obj (op (n, U)))
    (x : N.val.obj (op (n, U))) :
    ((sequenceScalarTowerLeft l E L ι M j f).app N).val.app
      (op (n, (proEtaleBaseChange f).obj U))
      (integralComparisonSequenceTensorSection l L M j X
        ((integralComparisonSequenceScalarModel l E L ι X).E.obj
          ((integralComparisonSequencePullback l E f).obj N))
        (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceRingComponent l M f (op (n, U)) c)
        (integralComparisonSequenceTensorSection l E L ι X
          ((integralComparisonSequencePullback l E f).obj N)
          (op (n, (proEtaleBaseChange f).obj U))
          (integralComparisonSequenceRingComponent l L f (op (n, U)) b)
          (integralComparisonSequenceGenerator l E f N n U x))) =
    integralComparisonSequenceGenerator l M f
      ((integralComparisonSequenceScalarModel l E M (j.comp ι) Y).E.obj N) n U
      (integralComparisonSequenceTensorSection l E M (j.comp ι) Y N (op (n, U))
        (c * (integralComparisonSequenceScalarMap l L M j Y).hom.app (op (n, U)) b) x) := by
  let A := op (n, (proEtaleBaseChange f).obj U)
  change ((integralComparisonSequencePullback l M f).map
      ((integralComparisonSequenceScalarComposition l E L ι M j Y).hom.app N)).val.app A
    (((integralComparisonSequenceScalarPullback l L M j f).hom.app
      ((integralComparisonSequenceScalarModel l E L ι Y).E.obj N)).val.app A
        (((integralComparisonSequenceScalarModel l L M j X).E.map
          ((integralComparisonSequenceScalarPullback l E L ι f).hom.app N)).val.app A _)) = _
  erw [tensor_map l L M j X
    ((integralComparisonSequenceScalarPullback l E L ι f).hom.app N) A
    (integralComparisonSequenceRingComponent l M f (op (n, U)) c)
    (integralComparisonSequenceTensorSection l E L ι X
      ((integralComparisonSequencePullback l E f).obj N) A
      (integralComparisonSequenceRingComponent l L f (op (n, U)) b)
      (integralComparisonSequenceGenerator l E f N n U x))]
  erw [scalar_pullback_tensor l E L ι f N n U b x]
  erw [scalar_pullback_tensor l L M j f
    ((integralComparisonSequenceScalarModel l E L ι Y).E.obj N) n U c
    (integralComparisonSequenceTensorSection l E L ι Y N (op (n, U)) b x)]
  erw [generator_natural l M f
    ((integralComparisonSequenceScalarComposition l E L ι M j Y).hom.app N) n U]
  have ha := (integralComparisonSequenceScalarComposition_existsUnique
    l E L ι M j Y).exists.choose_spec N (op (n, U)) c b x
  erw [ha]

/-- Geometric composition and scalar change commute on the whole sequence site.
Source: Stacks 0D6D, 03D7, 03EK; ordinary mixed tensor calculation
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: transpose twice, using tensor/restriction and inverse-image adjunctions
and their composite. Equality is tested on every local section x through
1 tensor gamma_kh(x). The unit equation for the prescribed pasting mate sends
gamma_kh(x) to gamma_h(gamma_k(x)). Both routes therefore give
gamma_h(gamma_k(1 tensor x)). This is an equality of whole-system maps:
vertical restrictions preserve units and tensors, while horizontal restrictions
are the actual semilinear quotient maps and preserve 1. Sheafification uniqueness
extends the equality from tensors; arbitrary sheaf sections need not be pure.
Naturality in N gives the displayed equality of natural transformations. -/
theorem sequenceScalarGeometric_interchange
    {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (_hV : ∀ x : V, IsUnit (l : V.presheaf.stalk x))
    (_hW : ∀ x : W, IsUnit (l : W.presheaf.stalk x))
    (_hZ : ∀ x : Z, IsUnit (l : Z.presheaf.stalk x)) :
    sequenceScalarGeometricLeft l E L ι h k = sequenceScalarGeometricRight l E L ι h k := by
  apply NatTrans.ext
  funext N
  apply sequenceScalarPullback_hom_ext l E L ι (h ≫ k) _hZ _hV
  intro n U x
  refine (sequenceScalarGeometric_generator l E L ι h k _hV _hW _hZ N n U x).trans ?_
  have hs := (integralComparisonSequenceScalarPullback_existsUnique
    l E L ι (h ≫ k)).exists.choose_spec N n U x
  dsimp only [sequenceScalarGeometricRight, NatTrans.comp_app, Functor.whiskerLeft_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [hs, composition_generator l L h k]

/-- The scalar unit commutes with ordinary inverse image of whole quotient systems.
Source: Stacks tensor/restriction adjunction, 03D7, 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: transpose through both adjunctions. On 1 tensor gamma_f(x) the scalar
square gives gamma_f(1 tensor x), and naturality of gamma_f with multiplication
gives gamma_f(x). Multiplication at X gives the same section. The transposes
agree on all source-local sections, hence the maps agree. Quotient maps and
vertical restrictions preserve 1 and multiplication, so this is a whole-system
identity, without flatness or cancellation of coefficients. -/
theorem sequenceScalarUnit_interchange
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ x : Y, IsUnit (l : Y.presheaf.stalk x)) :
    sequenceScalarUnitLeft l E f = sequenceScalarUnitRight l E f := by
  apply NatTrans.ext
  funext N
  apply sequenceScalarPullback_hom_ext l E E (AlgHom.id ℚ_[l] E) f _hX _hY
  intro n U x
  refine (sequenceScalarUnit_generator l E f _hX _hY N n U x).trans ?_
  change integralComparisonSequenceGenerator l E f N n U x =
    ((integralComparisonSequenceScalarUnit l E X).hom.app _).val.app _ _
  have hu := (integralComparisonSequenceScalarUnit_existsUnique l E X).exists.choose_spec
    ((integralComparisonSequencePullback l E f).obj N)
    (op (n, (proEtaleBaseChange f).obj U)) 1
    (integralComparisonSequenceGenerator l E f N n U x)
  exact (hu.trans (one_smul _ _)).symm

/-- The scalar tower associator commutes with ordinary inverse image.
Source: Stacks tensor/restriction adjunction, 03D7, 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: the twice-composed adjunction tests on 1 tensor (1 tensor gamma_f(x)).
The left route gives successively 1 tensor gamma_f(1 tensor x),
gamma_f(1 tensor (1 tensor x)), and gamma_f(1 tensor x); the right gives the
same. For source-local coefficient sections b,c, linearity and the recorded
associator give gamma_f(c*j(b) tensor x) on c tensor (b tensor gamma_f(x)).
Horizontal quotients are ring maps and commute with j, so q(c*j(b)) =
q(c)*j(q(b)); vertical restrictions satisfy the same formula. Adjunction and
sheafification uniqueness prove equality on entire systems, without any
assumption that target-local coefficients come from the source or are flat. -/
theorem sequenceScalarTower_interchange
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ x : Y, IsUnit (l : Y.presheaf.stalk x)) :
    sequenceScalarTowerLeft l E L ι M j f = sequenceScalarTowerRight l E L ι M j f := by
  apply NatTrans.ext
  funext N
  apply sequenceScalarTowerPullback_hom_ext l E L ι M j f _hX _hY
  intro n U x
  have hl := sequenceScalarTower_generator l E L ι M j f _hX _hY N n U 1 1 x
  simp only [map_one, mul_one] at hl
  refine hl.trans ?_
  change _ = ((integralComparisonSequenceScalarPullback l E M (j.comp ι) f).hom.app
    N).val.app _
      (((integralComparisonSequenceScalarComposition l E L ι M j X).hom.app _).val.app _ _)
  have ha := (integralComparisonSequenceScalarComposition_existsUnique
    l E L ι M j X).exists.choose_spec
      ((integralComparisonSequencePullback l E f).obj N)
      (op (n, (proEtaleBaseChange f).obj U)) 1 1
      (integralComparisonSequenceGenerator l E f N n U x)
  simp only [map_one, mul_one] at ha
  erw [ha]
  exact ((integralComparisonSequenceScalarPullback_existsUnique
    l E M (j.comp ι) f).exists.choose_spec N n U x).symm

/-- The geometric interchange is equality of cochain maps of arbitrary unbounded complexes.
Source: Stacks 010V and the ordinary whole-system calculation, 0D6D, 03D7, 03EK
(blueprint: lem-trf-sequence-scalar-generator-interchange).
Proof: use the ordinary geometric interchange in every degree. Both ordinary
functors are additive, hence preserve zero morphisms, so their degreewise images
are complexes. Naturality with the differential is the cochain-map condition.
Degreewise equality gives equality of cochain maps. Every component is still a
map of sequence-site sheaves, retaining all vertical and horizontal restrictions.
No totalization, sum, resolution or localization is taken, hence no boundedness
or quotient-flatness assumption is needed. -/
theorem sequenceScalarGeometric_interchange_cochain
    {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (_hV : ∀ x : V, IsUnit (l : V.presheaf.stalk x))
    (_hW : ∀ x : W, IsUnit (l : W.presheaf.stalk x))
    (_hZ : ∀ x : Z, IsUnit (l : Z.presheaf.stalk x))
    (P : CochainComplex (coefficientSequenceModules l E V) ℤ) :
    (NatTrans.mapHomologicalComplex
      (sequenceScalarGeometricLeft l E L ι h k) (.up ℤ)).app P =
    (NatTrans.mapHomologicalComplex
      (sequenceScalarGeometricRight l E L ι h k) (.up ℤ)).app P := by
  rw [sequenceScalarGeometric_interchange l E L ι h k _hV _hW _hZ]

end WeilConjectures
