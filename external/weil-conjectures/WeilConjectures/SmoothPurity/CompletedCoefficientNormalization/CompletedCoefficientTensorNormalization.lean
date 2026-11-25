/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientComparison

/-! # Normalized tensor presentation of completed coefficient rings

Source: main-20261015, smooth-purity, Cartesian coefficients and twists,
integral twist paragraph; Stacks 03EK and 03EL
(blueprint: lem-pur-completed-coefficient-tensor-normalization).

The pushout in commutative ring sheaves is the sheafified balanced ring tensor.
Its two inclusions express a pure tensor as the product of their images.
All maps in the conclusion are fixed by quotient projections or by these inclusions.
Site and coefficient universes are independent; level n always means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientNormalization

/-- The existing ring-sheaf category, retaining commutativity for its pushouts.
Source: Stacks 03EK (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev Rings (T : Scheme.{t}) := Sheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}

/-- A ring homomorphism transported through the common coefficient lift.
Source: Stacks 0H7J (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def liftHom {A : Type u} {B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{t + 1} A →+* ULift.{t + 1} B :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

/-- Constant integral scalars for the base field, with their discrete meaning.
Source: Stacks 0H7J (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev discrete (l : ℕ) [Fact l.Prime] (T : Scheme.{t}) : Rings.{t, u} T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{max u (t + 1)} (PadicInt l)))

/-- The actual constant finite base quotient, starting at exponent one.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev baseLevel (l : ℕ) (T : Scheme.{t}) (n : ℕ) : Rings.{t, u} T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{max u (t + 1)} (ZMod (l ^ (n + 1)))))

/-- Reduction in the base quotient tower, followed by constant sheafification.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def baseTransition (l : ℕ) (T : Scheme.{t}) (n : ℕ) :
    baseLevel.{t, u} l T (n + 1) ⟶ baseLevel.{t, u} l T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom)))

/-- The base inverse sequence, using the existing sequence construction.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def baseTower (l : ℕ) (T : Scheme.{t}) : ℕᵒᵖ ⥤ Rings.{t, u} T :=
  Functor.ofOpSequence (baseTransition l T)

/-- A_T is the existing categorical inverse limit, not the discrete constant ring.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev baseCompletion (l : ℕ) (T : Scheme.{t}) : Rings.{t, u} T :=
  limit (baseTower l T)

/-- The base projections are the coordinate maps of that limit.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev baseProjection (l : ℕ) (T : Scheme.{t}) (n : ℕ) :=
  limit.π (baseTower.{t, u} l T) (op n)

/-- Constant sheafification of the actual l-adic residue homomorphism.
Source: PadicInt.toZModPow (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def baseResidue (l : ℕ) [Fact l.Prime] (T : Scheme.{t}) (n : ℕ) :
    discrete.{t, u} l T ⟶ baseLevel l T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (p := l) (n + 1)).comp ULift.ringEquiv.toRingHom)))

/-- The existing pointwise Kan extension, using colimits only in the actual
site indexing sizes. This is a size specialization of Mathlib's construction.
Source: Stacks 00VC (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev kan {T' T : Scheme.{t}} (h : T' ⟶ T)
    (P : T.ProEtᵒᵖ ⥤ CommRingCat.{max u (t + 1)}) :
    (proEtaleBaseChange h).op.HasLeftKanExtension P :=
  letI : HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  letI : (proEtaleBaseChange h).op.HasPointwiseLeftKanExtension P :=
    fun _ ↦ HasColimitsOfShape.has_colimit _
  Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (proEtaleBaseChange h).op P)

/-- The same left-Kan-extension/sheafification inverse image as the recorded
pro-etale inverse image, at the common coefficient universe.
Source: Stacks 00VC, 00YV (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev inverse {T' T : Scheme.{t}} (h : T' ⟶ T) : Rings.{t, u} T ⥤ Rings.{t, u} T' :=
  letI := kan.{t, u} h
  Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange h)
    CommRingCat.{max u (t + 1)} (ProEt.topology T) (ProEt.topology T')

/-- The constant comparison is the adjoint of the map preserving constant sections.
It uses exactly the construction of proEtaleConstantInverseImageMap, at general size.
Source: Stacks 0H7J (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def delta {T' T : Scheme.{t}} (h : T' ⟶ T) (C : CommRingCat.{max u (t + 1)}) :
    (inverse.{t, u} h).obj ((constantSheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}).obj C) ⟶
      (constantSheaf (ProEt.topology T') CommRingCat.{max u (t + 1)}).obj C :=
  letI : HasColimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t + 1, t + 1, u, u} _
  letI := kan.{t, u} h
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (proEtaleBaseChange h)
    CommRingCat.{max u (t + 1)} (ProEt.topology T) (ProEt.topology T')).homEquiv _ _).symm
      (((sheafificationAdjunction (ProEt.topology T) CommRingCat.{max u (t + 1)}).homEquiv _ _).symm
        (Functor.whiskerLeft (proEtaleBaseChange h).op
          (toSheafify (ProEt.topology T') ((Functor.const T'.ProEtᵒᵖ).obj C))))

variable (l : ℕ) [Fact l.Prime]

/-- Epsilon is specified by every residue, hence uniquely by the limit property.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure BaseData where
  epsilon : ∀ T : Scheme.{t}, discrete.{t, u} l T ⟶ baseCompletion l T
  residue : ∀ (T : Scheme.{t}) (n : ℕ),
    epsilon T ≫ baseProjection l T n = baseResidue l T n

variable (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]

/-- The existing discrete coefficient sheaf, with commutativity retained.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev integralDiscrete (T : Scheme.{t}) : Rings.{t, u} T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l H)))

/-- Constant sheafification of the actual integral residue, retaining commutativity.
This is integralConstantQuotientOfUniverses before forgetting commutativity.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def integralResidue (T : Scheme.{t}) (n : ℕ) :
    integralDiscrete l H T ⟶ integralCoefficientCommRingSheaf l H T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l H (n + 1))).comp
        ULift.ringEquiv.toRingHom)))

/-- The constant scalar inclusion attached to a specified integral restriction.
The accompanying theorem fixes that restriction by the inclusion into H.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def scalar (f : PadicInt l →+* Padic.coefficientExtensionIntegers l H) (T : Scheme.{t}) :
    discrete.{t, u} l T ⟶ integralDiscrete l H T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)))

/-- The ring-sheaf tensor: the pushout of the two specified scalar maps.
CommRingCat pushouts are balanced ring tensors, and sheaf colimits are their
sheafifications; its pure tensors are products of the images of the two inclusions.
Source: Stacks 03EK (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev tensor (d : BaseData.{t, u} l)
    (f : PadicInt l →+* Padic.coefficientExtensionIntegers l H) (T : Scheme.{t}) :=
  pushout (d.epsilon T) (scalar l H f T)

/-- The constant map from an admissible base quotient to an integral quotient.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def residueFromBase (T : Scheme.{t}) (n k : ℕ)
    (j : ZMod (l ^ (k + 1)) →+* Padic.coefficientExtensionRing l H (n + 1)) :
    baseLevel.{t, u} l T k ⟶ integralCoefficientCommRingSheaf l H T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (j.comp ULift.ringEquiv.toRingHom)))

/-- The coefficient tensor presentation with its full quotient normalization.
The formula quantifies over every admissible k, so also asserts independence of k.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure Presentation (d : BaseData.{t, u} l) where
  integers : PadicInt l →+* Padic.coefficientExtensionIntegers l H
  integers_spec : ∀ a : PadicInt l, (integers a : H) = algebraMap (Padic l) H (a : Padic l)
  beta : ∀ T : Scheme.{t}, tensor l H d integers T ≅
    completedIntegralCommRingSheafUnrestricted l H T
  projection : ∀ (T : Scheme.{t}) (n k : ℕ),
    Ideal.span ({(l : Padic.coefficientExtensionIntegers l H) ^ (k + 1)} :
      Set (Padic.coefficientExtensionIntegers l H)) ≤
        Padic.coefficientExtensionIdeal l H (n + 1) →
    ∃ j : ZMod (l ^ (k + 1)) →+* Padic.coefficientExtensionRing l H (n + 1),
      (∀ a : PadicInt l, j (PadicInt.toZModPow (k + 1) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l H (n + 1)) (integers a)) ∧
      ∀ (U : T.ProEtᵒᵖ) (x : (baseCompletion.{t, u} l T).obj.obj U)
        (b : (integralDiscrete l H T).obj.obj U),
        (((beta T).hom ≫ completedIntegralCommRingProjectionUnrestricted l H T n).hom.app U)
          ((pushout.inl (d.epsilon T) (scalar l H integers T)).hom.app U x *
            (pushout.inr (d.epsilon T) (scalar l H integers T)).hom.app U b) =
          ((residueFromBase l H T n k j).hom.app U
            ((baseProjection l T k).hom.app U x)) * (integralResidue l H T n).hom.app U b

/-- Base inverse image, specified by all finite projections and the epsilon square.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure BasePullback (d : BaseData.{t, u} l) {T' T : Scheme.{t}} (h : T' ⟶ T) where
  alpha : (inverse.{t, u} h).obj (baseCompletion.{t, u} l T) ⟶ baseCompletion l T'
  projection : ∀ n : ℕ,
    alpha ≫ baseProjection l T' n = (inverse.{t, u} h).map (baseProjection l T n) ≫
      delta.{t, u} h (CommRingCat.of (ULift.{max u (t + 1)} (ZMod (l ^ (n + 1)))))
  epsilon_square : (inverse.{t, u} h).map (d.epsilon T) ≫ alpha =
    delta.{t, u} h (CommRingCat.of (ULift.{max u (t + 1)} (PadicInt l))) ≫ d.epsilon T'
  constant_iso : ∀ C : CommRingCat.{max u (t + 1)}, IsIso (delta.{t, u} h C)

/-- The actual tensor of the two inverse-image rings over the inverse-image base.
Source: Stacks 03EL (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
abbrev pulledTensor (d : BaseData.{t, u} l) (p : Presentation l H d)
    {T' T : Scheme.{t}} (h : T' ⟶ T) :=
  pushout ((inverse.{t, u} h).map (d.epsilon T))
    ((inverse.{t, u} h).map (scalar l H p.integers T))

/-- The inverse-image tensor comparison and all scalar structures, normalized on
both tensor inclusions. Multiplicativity then gives its pure-tensor normalization.
Source: Stacks 03EL and the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure Pullback (d : BaseData.{t, u} l) (p : Presentation l H d)
    {T' T : Scheme.{t}} (h : T' ⟶ T) (a : BasePullback l d h) where
  alpha : (inverse.{t, u} h).obj (completedIntegralCommRingSheafUnrestricted l H T) ⟶
    completedIntegralCommRingSheafUnrestricted l H T'
  projection : ∀ n : ℕ,
    alpha ≫ completedIntegralCommRingProjectionUnrestricted l H T' n =
      (inverse.{t, u} h).map (completedIntegralCommRingProjectionUnrestricted l H T n) ≫
        delta.{t, u} h (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l H (n + 1))))
  scalar_square : (inverse.{t, u} h).map (scalar l H p.integers T) ≫
      delta.{t, u} h (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l H))) =
    delta.{t, u} h (CommRingCat.of (ULift.{max u (t + 1)} (PadicInt l))) ≫
      scalar l H p.integers T'
  sigma : (inverse.{t, u} h).obj (tensor l H d p.integers T) ≅ pulledTensor l H d p h
  sigma_left : (inverse.{t, u} h).map (pushout.inl (d.epsilon T) (scalar l H p.integers T)) ≫
    sigma.hom = pushout.inl _ _
  sigma_right : (inverse.{t, u} h).map (pushout.inr (d.epsilon T) (scalar l H p.integers T)) ≫
    sigma.hom = pushout.inr _ _
  change : pulledTensor l H d p h ⟶ tensor l H d p.integers T'
  change_left : pushout.inl _ _ ≫ change = a.alpha ≫
    pushout.inl (d.epsilon T') (scalar l H p.integers T')
  change_right : pushout.inr _ _ ≫ change =
    delta.{t, u} h
              (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l H))) ≫
      pushout.inr (d.epsilon T') (scalar l H p.integers T')
  beta_square : (inverse.{t, u} h).map (p.beta T).hom ≫ alpha =
    sigma.hom ≫ change ≫ (p.beta T').hom

variable (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]

/-- The discrete coefficient inclusion is constant sheafification of its restriction.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def constantInclusion (f : Padic.coefficientExtensionIntegers l H →+*
    Padic.coefficientExtensionIntegers l F) (T : Scheme.{t}) :
    integralDiscrete l H T ⟶ integralDiscrete l F T :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom (liftHom f))

/-- Every admissible ramified quotient map is the quotient of the actual inclusion.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
def quotientInclusion (f : Padic.coefficientExtensionIntegers l H →+*
    Padic.coefficientExtensionIntegers l F) (T : Scheme.{t}) (k n : ℕ)
    (hk : Padic.coefficientExtensionIdeal l H (k + 1) ≤
      (Padic.coefficientExtensionIdeal l F (n + 1)).comap f) :
    integralCoefficientCommRingSheaf l H T k ⟶ integralCoefficientCommRingSheaf l F T n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
    (liftHom (Ideal.quotientMap (Padic.coefficientExtensionIdeal l F (n + 1)) f hk)))

/-- The coefficient-field compatibility, including the full ramified projection
formula defining i_EF and the two factor equations defining 1 tensor q_EF.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
structure Extension (iota : H →ₐ[Padic l] F) (d : BaseData.{t, u} l)
    (p : Presentation l H d) (q : Presentation l F d) where
  integers : Padic.coefficientExtensionIntegers l H →+* Padic.coefficientExtensionIntegers l F
  integers_spec : ∀ x, (integers x : F) = iota (x : H)
  admissible : ∀ n : ℕ, ∃ k : ℕ, Padic.coefficientExtensionIdeal l H (k + 1) ≤
    (Padic.coefficientExtensionIdeal l F (n + 1)).comap integers
  inclusion : ∀ T : Scheme.{t}, completedIntegralCommRingSheafUnrestricted l H T ⟶
    completedIntegralCommRingSheafUnrestricted l F T
  projection : ∀ (T : Scheme.{t}) (n k : ℕ)
    (hk : Padic.coefficientExtensionIdeal l H (k + 1) ≤
      (Padic.coefficientExtensionIdeal l F (n + 1)).comap integers),
    inclusion T ≫ completedIntegralCommRingProjectionUnrestricted l F T n =
      completedIntegralCommRingProjectionUnrestricted l H T k ≫
        quotientInclusion l H F integers T k n hk
  tensorMap : ∀ T : Scheme.{t}, tensor l H d p.integers T ⟶ tensor l F d q.integers T
  tensor_left : ∀ T : Scheme.{t},
    pushout.inl (d.epsilon T) (scalar l H p.integers T) ≫ tensorMap T =
      pushout.inl (d.epsilon T) (scalar l F q.integers T)
  tensor_right : ∀ T : Scheme.{t},
    pushout.inr (d.epsilon T) (scalar l H p.integers T) ≫ tensorMap T =
      constantInclusion l H F integers T ≫ pushout.inr (d.epsilon T) (scalar l F q.integers T)
  beta_square : ∀ T : Scheme.{t}, (p.beta T).hom ≫ inclusion T =
    tensorMap T ≫ (q.beta T).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The two canonical restrictions of the p-adic scalar inclusion coincide.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private theorem integer_scalar_square (iota : H →ₐ[Padic l] F)
    (d : BaseData.{t, u} l) (p : Presentation l H d) (q : Presentation l F d)
    (f : Padic.coefficientExtensionIntegers l H →+* Padic.coefficientExtensionIntegers l F)
    (hf : ∀ x, (f x : F) = iota (x : H)) :
    f.comp p.integers = q.integers := by
  ext z
  rw [RingHom.comp_apply, hf, p.integers_spec, q.integers_spec, iota.commutes]

/-- Projection of a presentation on its completed-base inclusion.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private theorem presentation_left (d : BaseData.{t, u} l) (p : Presentation l H d)
    (T : Scheme.{t}) (n k : ℕ)
    (hk : Ideal.span ({(l : Padic.coefficientExtensionIntegers l H) ^ (k + 1)} :
      Set (Padic.coefficientExtensionIntegers l H)) ≤
        Padic.coefficientExtensionIdeal l H (n + 1)) :
    ∃ j : ZMod (l ^ (k + 1)) →+* Padic.coefficientExtensionRing l H (n + 1),
      (∀ a : PadicInt l, j (PadicInt.toZModPow (k + 1) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l H (n + 1)) (p.integers a)) ∧
      pushout.inl (d.epsilon T) (scalar l H p.integers T) ≫ (p.beta T).hom ≫
          completedIntegralCommRingProjectionUnrestricted l H T n =
        baseProjection l T k ≫ residueFromBase l H T n k j := by
  obtain ⟨j, hj, hp⟩ := p.projection T n k hk
  refine ⟨j, hj, ?_⟩
  ext U x
  change (((p.beta T).hom ≫
    completedIntegralCommRingProjectionUnrestricted l H T n).hom.app U)
      ((pushout.inl (d.epsilon T) (scalar l H p.integers T)).hom.app U x) =
    (residueFromBase l H T n k j).hom.app U ((baseProjection l T k).hom.app U x)
  simpa only [map_one, mul_one] using hp U x 1

/-- Every level admits a base exponent, uniformly over the site.
Source: Stacks 03CO and the local-field DVR theorem
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private theorem base_admissible (n : ℕ) :
    Ideal.span ({(l : Padic.coefficientExtensionIntegers l H) ^ (n + 1)} :
      Set (Padic.coefficientExtensionIntegers l H)) ≤
        Padic.coefficientExtensionIdeal l H (n + 1) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l H).choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l H) ∈
      Padic.coefficientExtensionMaximalIdeal l H := by
    apply (h.2.1 _).2
    change spectralNorm ℚ_[l] H (l : H) < 1
    rw [← map_natCast (algebraMap ℚ_[l] H), spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l H} :
      Set (Padic.coefficientExtensionIntegers l H)) =
        Padic.coefficientExtensionMaximalIdeal l H :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change (l : Padic.coefficientExtensionIntegers l H) ^ (n + 1) ∈
    Ideal.span ({Padic.coefficientExtensionUniformizer l H} :
      Set (Padic.coefficientExtensionIntegers l H)) ^ (n + 1)
  rw [hgen]
  exact Ideal.pow_mem_pow hm (n + 1)

/-- Projection of a presentation on its discrete-integer inclusion.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private theorem presentation_right (d : BaseData.{t, u} l) (p : Presentation l H d)
    (T : Scheme.{t}) (n : ℕ) :
    pushout.inr (d.epsilon T) (scalar l H p.integers T) ≫ (p.beta T).hom ≫
        completedIntegralCommRingProjectionUnrestricted l H T n =
      integralResidue l H T n := by
  obtain ⟨j, _, hp⟩ := p.projection T n n (base_admissible l H n)
  ext U b
  change (((p.beta T).hom ≫
    completedIntegralCommRingProjectionUnrestricted l H T n).hom.app U)
      ((pushout.inr (d.epsilon T) (scalar l H p.integers T)).hom.app U b) = _
  simpa only [map_one, one_mul] using hp U 1 b

/-- The base data are the canonical residue-normalized completion map.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private def canonicalBase : BaseData.{t, u} l where
  epsilon T := purTwistZlCompletionMapOfUniverses.{t, u} T l
  residue T n := (purTwistZlCompletionMap_existsUniqueOfUniverses.{t, u} T l).exists.choose_spec n

private theorem baseResidue_epi (T : Scheme.{t}) (n : ℕ) :
    Epi (baseResidue.{t, u} l T n) := by
  let q : CommRingCat.of (ULift.{max u (t + 1)} (PadicInt l)) ⟶
      CommRingCat.of (ULift.{max u (t + 1)} (ZMod (l ^ (n + 1)))) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom))
  have : Epi q := ConcreteCategory.epi_of_surjective q (by
    intro x
    obtain ⟨z, hz⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)) x.down
    exact ⟨ULift.up z, congrArg ULift.up hz⟩)
  change Epi ((constantSheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}).map q)
  let := (constantSheafAdj (ProEt.topology T) CommRingCat.{max u (t + 1)}
    (MorphismProperty.Over.mkIdTerminal _ _)).isLeftAdjoint
  infer_instance

private theorem baseFiniteFactor_ext (T : Scheme.{t}) {B : Rings.{t, u} T} (k m : ℕ)
    (f : baseLevel.{t, u} l T k ⟶ B) (g : baseLevel.{t, u} l T m ⟶ B)
    (h : baseResidue l T k ≫ f = baseResidue l T m ≫ g) :
    baseProjection l T k ≫ f = baseProjection l T m ≫ g := by
  let t := max k m
  let p (i : ℕ) (hi : i ≤ t) := (baseTower.{t, u} l T).map (homOfLE hi).op
  have hp (i : ℕ) (hi : i ≤ t) :
      baseProjection l T t ≫ p i hi = baseProjection l T i :=
    limit.w (baseTower l T) (homOfLE hi).op
  have hr (i : ℕ) (hi : i ≤ t) :
      baseResidue l T t ≫ p i hi = baseResidue l T i := by
    rw [← (canonicalBase.{t, u} l).residue T t, Category.assoc, hp,
      (canonicalBase.{t, u} l).residue]
  have : Epi (baseResidue.{t, u} l T t) := baseResidue_epi l T t
  have he : p k (le_max_left k m) ≫ f = p m (le_max_right k m) ≫ g := by
    apply (cancel_epi (baseResidue l T t)).mp
    simpa only [← Category.assoc, hr] using h
  rw [← hp k (le_max_left k m), ← hp m (le_max_right k m),
    Category.assoc, Category.assoc, he]

/-- The normalized coefficient tensor presentation, using the existing proved
coefficient pushout comparison and quotient factorization for every admissible level.
Source: Stacks 03EK and the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private def canonicalPresentation : Presentation l H (canonicalBase.{t, u} l) := by
  let f := purTwistIntegersMap l H
  have hf := (purTwistIntegersMap_existsUnique l H).exists.choose_spec
  letI (T : Scheme.{t}) : IsIso (purTwistCoefficientComparison T l H) :=
    purTwistCoefficientComparison_isIso T l H
  refine ⟨f, hf, fun T ↦ asIso (purTwistCoefficientComparison T l H), ?_⟩
  intro T n k hk
  let g := (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l H (n + 1))).comp f
  have hker : RingHom.ker (PadicInt.toZModPow (k + 1)) ≤ RingHom.ker g := by
    rw [PadicInt.ker_toZModPow, Ideal.span_le, Set.singleton_subset_iff]
    change Ideal.Quotient.mk _ (f ((l : PadicInt l) ^ (k + 1))) = 0
    rw [map_pow, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact hk (Ideal.subset_span (Set.mem_singleton _))
  let j := (PadicInt.toZModPow (k + 1)).liftOfSurjective
    (ZMod.ringHom_surjective _) ⟨g, hker⟩
  have hj (z : PadicInt l) : j (PadicInt.toZModPow (k + 1) z) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l H (n + 1)) (f z) :=
    RingHom.liftOfSurjective_comp_apply _ _ _ z
  have hc : purTwistCompletedScalarMap T l H ≫
      completedIntegralCommRingProjectionUnrestricted l H T n =
        baseProjection l T k ≫ residueFromBase l H T n k j := by
    obtain ⟨m, q, hq, hp⟩ :=
      (purTwistCompletedScalarMap_existsUnique T l H).exists.choose_spec n
    erw [hp]
    apply baseFiniteFactor_ext l T m k
    dsimp [baseResidue, purTwistZlReductionOfUniverses, residueFromBase]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext z
    exact (hq z.down).trans (hj z.down).symm
  have hd := (purTwistIntegralCompletionMap_existsUnique T l H).exists.choose_spec n
  refine ⟨j, hj, ?_⟩
  intro U x b
  have hl := pushout.inl_desc (purTwistCompletedScalarMap T l H)
    (purTwistIntegralCompletionMap T l H) (purTwistCoefficientSquare T l H)
  have hr := pushout.inr_desc (purTwistCompletedScalarMap T l H)
    (purTwistIntegralCompletionMap T l H) (purTwistCoefficientSquare T l H)
  rw [map_mul]
  congr 1
  · exact ConcreteCategory.congr_hom (congrArg (fun v ↦ v.hom.app U)
      ((Category.assoc _ _ _).symm.trans ((congrArg
        (fun v ↦ v ≫ completedIntegralCommRingProjectionUnrestricted l H T n) hl).trans hc))) x
  · exact ConcreteCategory.congr_hom (congrArg (fun v ↦ v.hom.app U)
      ((Category.assoc _ _ _).symm.trans ((congrArg
        (fun v ↦ v ≫ completedIntegralCommRingProjectionUnrestricted l H T n) hr).trans hd))) b

/-- The field inclusion restricts to integer rings and takes each uniformizer
ideal power into the corresponding power in the upper field.
Source: Serre, Local Fields, II §2; Stacks 03CO
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private theorem integral_inclusion (iota : H →ₐ[Padic l] F) :
    ∃ f : Padic.coefficientExtensionIntegers l H →+* Padic.coefficientExtensionIntegers l F,
      (∀ x, (f x : F) = iota (x : H)) ∧
      ∀ n, Padic.coefficientExtensionIdeal l H (n + 1) ≤
        (Padic.coefficientExtensionIdeal l F (n + 1)).comap f := by
  let R := Padic.coefficientExtensionIntegers l H
  let S := Padic.coefficientExtensionIntegers l F
  have hR := (Padic.coefficientExtensionIntegers_dvr l H).choose_spec
  have hS := (Padic.coefficientExtensionIntegers_dvr l F).choose_spec
  have hn (x : H) : spectralNorm ℚ_[l] F (iota x) = spectralNorm ℚ_[l] H x := by
    unfold spectralNorm
    rw [minpoly.algHom_eq iota iota.injective]
  let f : R →+* S := (iota.toRingHom.comp R.subtype).codRestrict S (by
    intro x
    apply (hS.1 _).mpr
    change spectralNorm ℚ_[l] F (iota (x : H)) ≤ 1
    rw [hn]
    exact (hR.1 _).mp x.property)
  refine ⟨f, fun _ ↦ rfl, fun n ↦ ?_⟩
  have hgenR : Ideal.span ({Padic.coefficientExtensionUniformizer l H} : Set R) =
      Padic.coefficientExtensionMaximalIdeal l H :=
    hR.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenS : Ideal.span ({Padic.coefficientExtensionUniformizer l F} : Set S) =
      Padic.coefficientExtensionMaximalIdeal l F :=
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  apply Ideal.map_le_iff_le_comap.mp
  change Ideal.map f (Ideal.span {Padic.coefficientExtensionUniformizer l H} ^ (n + 1)) ≤ _
  rw [Ideal.map_pow]
  change Ideal.map f (Ideal.span {Padic.coefficientExtensionUniformizer l H}) ^ (n + 1) ≤
    Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ (n + 1)
  apply pow_le_pow_left'
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
  rw [hgenS]
  apply (hS.2.1 _).mpr
  change spectralNorm ℚ_[l] F (iota (Padic.coefficientExtensionUniformizer l H : H)) < 1
  rw [hn]
  apply (hR.2.1 _).mp
  change Padic.coefficientExtensionUniformizer l H ∈
    Padic.coefficientExtensionMaximalIdeal l H
  rw [← hgenR]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The tensor map of a coefficient inclusion, fixed on both factors.
Source: Stacks 03EK (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private def inclusionTensor (iota : H →ₐ[Padic l] F)
    (d : BaseData.{t, u} l) (p : Presentation l H d) (q : Presentation l F d)
    (f : Padic.coefficientExtensionIntegers l H →+* Padic.coefficientExtensionIntegers l F)
    (hf : ∀ x, (f x : F) = iota (x : H)) (T : Scheme.{t}) :
    tensor l H d p.integers T ⟶ tensor l F d q.integers T :=
  pushout.desc (pushout.inl (d.epsilon T) (scalar l F q.integers T))
    (constantInclusion l H F f T ≫ pushout.inr (d.epsilon T) (scalar l F q.integers T)) (by
      rw [pushout.condition, ← Category.assoc]
      congr 1
      dsimp [scalar, constantInclusion]
      rw [← Functor.map_comp]
      congr 1
      ext z
      exact congrArg Subtype.val (RingHom.congr_fun
        (integer_scalar_square l H F iota d p q f hf) z.down).symm)

/-- The completed coefficient inclusion is obtained from the tensor inclusion.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private def inclusion (iota : H →ₐ[Padic l] F)
    (d : BaseData.{t, u} l) (p : Presentation l H d) (q : Presentation l F d)
    (f : Padic.coefficientExtensionIntegers l H →+* Padic.coefficientExtensionIntegers l F)
    (hf : ∀ x, (f x : F) = iota (x : H)) (T : Scheme.{t}) :
    completedIntegralCommRingSheafUnrestricted l H T ⟶
      completedIntegralCommRingSheafUnrestricted l F T :=
  (p.beta T).inv ≫ inclusionTensor l H F iota d p q f hf T ≫ (q.beta T).hom

/-- Every quotient map is compatible with constant integral reduction.
Source: Stacks 03CO (blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private theorem residue_quotient
    (f : Padic.coefficientExtensionIntegers l H →+* Padic.coefficientExtensionIntegers l F)
    (T : Scheme.{t}) (k n : ℕ)
    (hk : Padic.coefficientExtensionIdeal l H (k + 1) ≤
      (Padic.coefficientExtensionIdeal l F (n + 1)).comap f) :
    integralResidue l H T k ≫ quotientInclusion l H F f T k n hk =
      constantInclusion l H F f T ≫ integralResidue l F T n := by
  dsimp [integralResidue, quotientInclusion, constantInclusion]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Every admissible ramified quotient computes the tensor-defined inclusion.
Source: the integral twist paragraph, comparison on pure tensors
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private theorem inclusion_projection (iota : H →ₐ[Padic l] F)
    (d : BaseData.{t, u} l) (p : Presentation l H d) (q : Presentation l F d)
    (f : Padic.coefficientExtensionIntegers l H →+* Padic.coefficientExtensionIntegers l F)
    (hf : ∀ x, (f x : F) = iota (x : H)) (T : Scheme.{t}) (n k : ℕ)
    (hk : Padic.coefficientExtensionIdeal l H (k + 1) ≤
      (Padic.coefficientExtensionIdeal l F (n + 1)).comap f) :
    inclusion l H F iota d p q f hf T ≫
        completedIntegralCommRingProjectionUnrestricted l F T n =
      completedIntegralCommRingProjectionUnrestricted l H T k ≫
        quotientInclusion l H F f T k n hk := by
  apply (cancel_epi (p.beta T).hom).mp
  simp only [inclusion, Category.assoc, Iso.hom_inv_id_assoc]
  apply pushout.hom_ext
  · let r := max k n
    have hH : Ideal.span ({(l : Padic.coefficientExtensionIntegers l H) ^ (r + 1)} :
        Set (Padic.coefficientExtensionIntegers l H)) ≤
          Padic.coefficientExtensionIdeal l H (k + 1) := by
      apply le_trans _ (base_admissible l H k)
      rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
      exact Ideal.pow_le_pow_right (Nat.add_le_add_right (le_max_left k n) 1)
    have hF : Ideal.span ({(l : Padic.coefficientExtensionIntegers l F) ^ (r + 1)} :
        Set (Padic.coefficientExtensionIntegers l F)) ≤
          Padic.coefficientExtensionIdeal l F (n + 1) := by
      apply le_trans _ (base_admissible l F n)
      rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
      exact Ideal.pow_le_pow_right (Nat.add_le_add_right (le_max_right k n) 1)
    obtain ⟨jH, hjH, hpH⟩ := presentation_left l H d p T k r hH
    obtain ⟨jF, hjF, hpF⟩ := presentation_left l F d q T n r hF
    simp only [inclusionTensor, pushout.inl_desc_assoc]
    rw [hpF]
    have hh := congrArg (fun v ↦ v ≫ quotientInclusion l H F f T k n hk) hpH
    simp only [Category.assoc] at hh
    rw [hh]
    congr 1
    dsimp [residueFromBase, quotientInclusion]
    rw [← Functor.map_comp]
    congr 1
    ext z
    change jF z.down = Ideal.quotientMap _ f hk (jH z.down)
    obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (r + 1)) z.down
    rw [← ha, hjF, hjH]
    change Ideal.Quotient.mk _ (q.integers a) = Ideal.Quotient.mk _ (f (p.integers a))
    apply congrArg (Ideal.Quotient.mk _)
    exact (RingHom.congr_fun (integer_scalar_square l H F iota d p q f hf) a).symm
  · simp only [inclusionTensor, pushout.inr_desc_assoc]
    rw [Category.assoc, presentation_right]
    have hh := congrArg (fun v ↦ v ≫ quotientInclusion l H F f T k n hk)
      (presentation_right l H d p T k)
    simp only [Category.assoc] at hh
    rw [hh, residue_quotient]

/-- Extension data are fixed by the tensor inclusions and every quotient projection.
Source: the integral twist paragraph
(blueprint: lem-pur-completed-coefficient-tensor-normalization). -/
private def extension (iota : H →ₐ[Padic l] F)
    (d : BaseData.{t, u} l) (p : Presentation l H d) (q : Presentation l F d) :
    Extension l H F iota d p q := by
  let h := integral_inclusion l H F iota
  let f := h.choose
  have hf := h.choose_spec.1
  have ha := h.choose_spec.2
  refine ⟨f, hf, fun n ↦ ⟨n, ha n⟩, inclusion l H F iota d p q f hf,
    inclusion_projection l H F iota d p q f hf,
    inclusionTensor l H F iota d p q f hf, ?_, ?_, ?_⟩
  · intro T
    exact pushout.inl_desc _ _ _
  · intro T
    exact pushout.inr_desc _ _ _
  · intro T
    simp only [inclusion, Iso.hom_inv_id_assoc]

end WeilConjectures.CompletedCoefficientNormalization
