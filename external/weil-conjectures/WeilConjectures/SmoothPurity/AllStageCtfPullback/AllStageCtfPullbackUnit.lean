/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ConstantGeometricStalkUnit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible

/-! # Pullback of finite-Tor complexes and the actual coefficient units

Source: main-20261015, sec-six-functors-basics/sk-def-purity-conv,
lemma-section-normal-bundle--1, the expression Ls* Rg! Lambda_B and its Picard assertion;
Bhatt--Scholze, Lemma 6.5.9(5); Stacks Tag 099N(5).
(blueprint: lem-pur-all-stage-ctf-pullback-unit).

Positive exponent j is indexed by n with j = n+1. The integral unit uses the regular
completed coefficient sheaf, its strict quotient tower and zero shifted Roos coordinate.
The two field units are the images of this very arrow in the recorded categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.AllStageCtfPullback

/-- The coefficient prime is invertible in residue fields of the fixed base schemes.
This transports the recorded local-ring witness along the actual residue morphism.
Source: purity conventions, ell distinct from p
(blueprint: lem-pur-all-stage-ctf-pullback-unit). -/
@[instance_reducible] def residueInvertible (P : PurityFiniteSetting.{u}) (W : Scheme.{u})
    [W.Over (Spec (.of P.field.k))] (w : W) :
    Invertible (P.coefficients.l : W.residueField w) :=
  IsUnit.invertible (by
    simpa only [map_natCast] using
      (P.coefficientPrime_isUnit_stalk W (W ↘ Spec (.of P.field.k)) w).map (W.residue w).hom)

/-- The rational unit is exactly the localization of the existing completed integral unit.
The source comparison is the prescribed unchanged-object equation for rational pullback.
Source: blueprint field-stage clause; Stacks 099N(5)
(blueprint: lem-pur-all-stage-ctf-pullback-unit). -/
def rationalUnit (P : PurityFiniteSetting.{u}) (E : Type u) [Field E]
    [Algebra (Padic P.coefficients.l) E] [FiniteDimensional (Padic P.coefficients.l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))] :
    (@rationalDerivedPullback.{u} P.coefficients.l inferInstance E inferInstance
      inferInstance inferInstance X Y f
      (fun x ↦ residueInvertible P X x) (fun y ↦ residueInvertible P Y y)).obj
        (constantWeilRationalObject P.coefficients.l E P.field P.coefficients.different Y) ≅
      constantWeilRationalObject P.coefficients.l E P.field P.coefficients.different X :=
  letI := fun x ↦ residueInvertible P X x
  letI := fun y ↦ residueInvertible P Y y
  eqToIso ((rationalDerivedPullback_existsUnique P.coefficients.l E f).exists.choose_spec.2.1
    (constantWeilRationalObject P.coefficients.l E P.field P.coefficients.different Y)) ≪≫
    (sfRationalConstructibleLocalization P.coefficients.l E X).mapIso
      (ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit P.coefficients.l E f))

/-- At every finite field stage, the algebraically closed unit comparison is the
inclusion of the rationalized completed unit. Both units are literal recorded pairs.
The unchanged-stage comparison is the defining object equation of common-stage pullback.
Source: blueprint common-stage paragraph; Stacks 099N(5)
(blueprint: lem-pur-all-stage-ctf-pullback-unit). -/
def commonUnit (P : PurityFiniteSetting.{u})
    (L : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))] :
    (@commonStageDerivedPullback.{u, u} P.coefficients.l inferInstance P.coefficients.Qbar
      inferInstance inferInstance inferInstance X Y f
      (fun x ↦ residueInvertible P X x) (fun y ↦ residueInvertible P Y y)).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := Y) L).obj
          (constantWeilRationalObject P.coefficients.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u}
              P.coefficients.l P.coefficients.Qbar L) P.field P.coefficients.different Y)) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := X) L).obj
          (constantWeilRationalObject P.coefficients.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u}
              P.coefficients.l P.coefficients.Qbar L) P.field P.coefficients.different X) :=
  letI := fun x ↦ residueInvertible P X x
  letI := fun y ↦ residueInvertible P Y y
  eqToIso ((commonStageDerivedPullback_existsUnique
    P.coefficients.l P.coefficients.Qbar f).exists.choose_spec.1 _) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := X) L).mapIso
        (rationalUnit P (AlgebraicallyClosedCoefficients.Coefficient.{u}
          P.coefficients.l P.coefficients.Qbar L) f)

private theorem torAmplitude_of_iso (W : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory W A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude W A K a b) :
    HasProEtaleTorAmplitude W A L a b := by
  refine ⟨h.1, ?_⟩
  rintro C P ⟨eC⟩ f hf hP M i hi
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem goodRepresentative (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (K : DerivedCategory (integralTowerModules l E W)) :
    ∃ R : (integralOperationsGoodComplex l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj R.obj ≅ K) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
  have := Localization.essSurj (DerivedCategory.Q (C := integralTowerModules l E W))
    (HomologicalComplex.quasiIso _ (.up ℤ))
  let L := (DerivedCategory.Q (C := integralTowerModules l E W)).objPreimage K
  let e := (DerivedCategory.Q (C := integralTowerModules l E W)).objObjPreimageIso K
  obtain ⟨R, f, hR, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) L
  let : QuasiIso f := hf
  let : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (integralTowerModules l E W) f).2 hf
  have hsite (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (R.X i) := by
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (R.X i)).symm (hflat i)
  exact ⟨⟨R, hR, hsite⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫ e⟩⟩

/-- Pullback preserves the fixed finite Tor interval, the uniform integral Tor interval,
on the actual completed coefficients. The rational and common-stage functors have
exactly the full constructible categories as their domains and codomains; their units
are rationalUnit and commonUnit above, obtained from the reexported
ConstantGeometricStalkUnit.integralUnit by localization and the same-stage inclusion.
The exact finite unit is ConstantGeometricStalkUnit.finiteUnit.

Source: main-20261015, lemma-section-normal-bundle--1; Bhatt--Scholze, 6.5.9(5), Stacks 099N(5)
(blueprint: lem-pur-all-stage-ctf-pullback-unit).
Proof:
1. Apply proposition-six-operations-dctf--1 at every positive finite exponent. Its hypotheses
are finite type and separatedness of f, and finite type of X and Y over k. Transport
from its tensor-pullback coordinates by the canonical unit-preserving comparison to
finiteDerivedPullback. The unchanged interval witnesses the finite-Tor restriction.
2. IntegralOperations_preserve_constructible gives completeness, bounded constructibility
and invertibility of the actual Roos-projection reduction comparison on every good
representative. Identifying its finite term with finite inverse image of the reduction
of K gives the displayed derived isomorphism. Apply step 1 at every n using the SAME
supplied endpoints a,b. This is exactly finiteTorConstructibleIntegral on X.
3. Finite constant-ring pullback identifies the regular unit by its adjoint ring map;
exactness gives ConstantGeometricStalkUnit.finiteUnit in the derived category. The quotient
maps preserve constant sections, so these unit identifications commute with transitions.
4. The regular completed sheaf is flat and K-flat, and its finite reductions are the
regular finite sheaves. Its actual augmentation is a quasi-isomorphism by rank-one
completeness. The reexported ConstantGeometricStalkUnit.integralChainUnit lemmas fix the strict cone
comparison and integralUnit. The coefficient-objects constructibility theorem puts these objects
in the full constructible categories. None is the discrete integral constant sheaf.
5. Rational pullback acts on integral representatives and tensors morphisms with scalars;
raw localization of the existing integralUnit is rationalUnit. Common-stage pullback uses the same
operation over one finite field and the specified scalar comparisons; its commonUnit is
its image under that stage inclusion. The scalar-extension comparisons are natural,
identity- and tower-compatible, so these maps are independent of the chosen field stage.
6. At the field stages finiteTorFieldCoefficientCategory is the full constructible
category by definition. Empty schemes, identity maps, the zero complex and exponent
one satisfy the same constructions with their unique maps; no extra hypothesis occurs. -/
theorem preserves_ctf_and_unit (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left] :
    (∀ (n : ℕ)
      (K : proEtaleDerivedCategory Y.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))),
      intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y.left K →
      ∀ a b : ℤ,
        HasProEtaleTorAmplitude Y.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) K a b →
        intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n)) X.left
            ((finiteDerivedPullback P.coefficients.l P.extension n f.left).obj K) ∧
          HasProEtaleTorAmplitude X.left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((finiteDerivedPullback P.coefficients.l P.extension n f.left).obj K) a b) ∧
    (∀ (n : ℕ)
      (K : proEtaleDerivedCategory Y.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))),
      finiteTorConstructible P.coefficients.l P.extension (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y.left K →
        finiteTorConstructible P.coefficients.l P.extension (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) X.left
          ((finiteDerivedPullback P.coefficients.l P.extension n f.left).obj K)) ∧
    (∀ (K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension Y.left)),
      sfIntegralConstructible P.coefficients.l P.extension Y.left K →
      ∀ a b : ℤ,
        (∀ n : ℕ, HasProEtaleTorAmplitude Y.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension Y.left n).obj K)
          a b) →
        sfIntegralConstructible P.coefficients.l P.extension X.left
          ((integralDerivedPullback P.coefficients.l P.extension f.left).obj K) ∧
        (∀ n : ℕ,
          HasProEtaleTorAmplitude X.left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
              ((integralDerivedPullback P.coefficients.l P.extension f.left).obj K)) a b ∧
          Nonempty (((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
              ((integralDerivedPullback P.coefficients.l P.extension f.left).obj K)) ≅
              (finiteDerivedPullback P.coefficients.l P.extension n f.left).obj
                ((scalarReductionDerivedExtension P.coefficients.l P.extension Y.left n).obj K))) ∧
        (∀ (R : (integralOperationsGoodComplex
          P.coefficients.l P.extension Y.left).FullSubcategory)
          (e : DerivedCategory.Q.obj R.obj ≅ K) (n : ℕ),
          IsIso (integralPullbackFiniteComparison P.coefficients.l P.extension f.left K R e n))) ∧
    (∀ K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension Y.left),
      finiteTorConstructibleIntegral P.coefficients.l P.extension Y.left K →
        finiteTorConstructibleIntegral P.coefficients.l P.extension X.left
          ((integralDerivedPullback P.coefficients.l P.extension f.left).obj K)) := by
  classical
  let := fun x : X.left ↦ residueInvertible P X.left x
  let := fun y : Y.left ↦ residueInvertible P Y.left y
  have hfinite (n : ℕ)
      (K : proEtaleDerivedCategory Y.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)))
      (hK : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_pos n) Y.left K) (a b : ℤ)
      (hTor : HasProEtaleTorAmplitude Y.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) K a b) :
      intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
          (Nat.succ_pos n) X.left
          ((finiteDerivedPullback P.coefficients.l P.extension n f.left).obj K) ∧
        HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((finiteDerivedPullback P.coefficients.l P.extension n f.left).obj K) a b := by
    let A := Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing _ _ _ (Nat.succ_pos n)
    obtain ⟨hc, ht⟩ := sf_pullback_torAmplitude P.field P.coefficients.l
      P.coefficients.different P.extension (n + 1) (Nat.succ_pos n) X Y f K hK a b hTor
    let e := (openSquareDerivedPullbackModel A f.left).app K
    let C := intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_pos n) X.left
    have : C.IsClosedUnderIsomorphisms :=
      (proEtale_bounded_constructible_isTriangulated X.left A).1
    exact ⟨C.prop_of_iso e hc, torAmplitude_of_iso X.left A e a b ht⟩
  have hintegral :
    (∀ (K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension Y.left)),
      sfIntegralConstructible P.coefficients.l P.extension Y.left K →
      ∀ a b : ℤ,
        (∀ n : ℕ, HasProEtaleTorAmplitude Y.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension Y.left n).obj K)
          a b) →
        sfIntegralConstructible P.coefficients.l P.extension X.left
          ((integralDerivedPullback P.coefficients.l P.extension f.left).obj K) ∧
        (∀ n : ℕ,
          HasProEtaleTorAmplitude X.left
            (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
            ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
              ((integralDerivedPullback P.coefficients.l P.extension f.left).obj K)) a b ∧
          Nonempty (((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
              ((integralDerivedPullback P.coefficients.l P.extension f.left).obj K)) ≅
              (finiteDerivedPullback P.coefficients.l P.extension n f.left).obj
                ((scalarReductionDerivedExtension P.coefficients.l P.extension Y.left n).obj K))) ∧
        (∀ (R : (integralOperationsGoodComplex
          P.coefficients.l P.extension Y.left).FullSubcategory)
          (e : DerivedCategory.Q.obj R.obj ≅ K) (n : ℕ),
          IsIso (integralPullbackFiniteComparison
            P.coefficients.l P.extension f.left K R e n))) := by
    intro K hK a b ht
    obtain ⟨hc, hi⟩ :=
      (integralOperations_preserve_constructible P.coefficients.l P.extension f.left).1 K hK
    refine And.intro hc (And.intro ?_ hi)
    intro n
    obtain ⟨R, ⟨eR⟩⟩ := goodRepresentative P.coefficients.l P.extension Y.left K
    let A := Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing _ _ _ (Nat.succ_pos n)
    let := hi R eR n
    let e := asIso (integralPullbackFiniteComparison
        P.coefficients.l P.extension f.left K R eR n) ≪≫
      DerivedCategory.Q.mapIso
        ((NatIso.mapHomologicalComplex
          (integralFinitePullbackModel P.coefficients.l P.extension f.left n)
          (.up ℤ)).app
            ((unrestrictedIntegralFiniteComplex P.coefficients.l P.extension Y.left n).obj
            R.obj)) ≪≫
      ((proEtaleConstantRingPullback A f.left).mapDerivedCategoryFactors.app
        ((unrestrictedIntegralFiniteComplex P.coefficients.l P.extension Y.left n).obj
          R.obj)).symm ≪≫
      (proEtaleConstantRingDerivedPullback A f.left).mapIso
        ((coefficientFiniteReductionModel P.coefficients.l P.extension Y.left
          R.obj R.property.1 n).symm ≪≫
          (scalarReductionDerivedExtension P.coefficients.l P.extension Y.left n).mapIso eR) ≪≫
      (openSquareDerivedPullbackModel A f.left).app _
    obtain ⟨c, d, _, hred⟩ := hK.2
    have hb := (hfinite n _ (hred n).1 a b (ht n)).2
    exact ⟨torAmplitude_of_iso X.left A e.symm a b hb, ⟨e⟩⟩
  refine ⟨hfinite, ?_, hintegral, ?_⟩
  · rintro n K ⟨hc, a, b, ht⟩
    obtain ⟨hc', ht'⟩ := hfinite n K hc a b ht
    exact ⟨hc', a, b, ht'⟩
  · rintro K ⟨hc, a, b, hab, ht⟩
    obtain ⟨hc', hred, _⟩ := hintegral K hc a b ht
    exact ⟨hc', a, b, hab, fun n ↦ (hred n).1⟩

end WeilConjectures.AllStageCtfPullback
