/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicConstructibleRealization
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstruction
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.Compactification.RefinementCategory

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Data for ordinary locally finite adic compact support

Source: current blueprint, prose-10-20, common-field
comparisons; Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-locally-finite-adic-compact-support-data).

The auxiliary coefficient closure in the finite-stage construction is lifted only to
use its published interface. Every finite field below is a subfield of PadicAlgCl,
and the descended functor acts on the original, unlifted common-stage category.
The section presentation fixes the scalar comparison as a mate of actual operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]

/-- Native coefficient inverse images, fixed by precomposition of locally finite functions.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
class NativeRings where
  [commutative : ∀ T : Scheme.{u}, IsCommMonObj (abRing l T)]
  pull : ∀ {U V : Scheme.{u}} (g : U ⟶ V),
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (ringSheaf l V) ≅ ringSheaf l U
  pull_normalized : ∀ {U V : Scheme.{u}} (g : U ⟶ V) (W : V.ProEtᵒᵖ)
      (s : (ringSheaf l V).obj.obj W)
      (x : ((proEtaleBaseChange g).obj W.unop).left),
    (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      (pull g).hom).hom.app W s).down.1 x =
        s.down.1 ((pullback.fst W.unop.hom g).base x)

attribute [instance] NativeRings.commutative

/-- The existing ringed coefficient interface, specialized to the native ring sheaf.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
def nativeCoefficients [N : NativeRings.{u} l] : PurCompactSupport.Coefficients.{u} where
  ring := fun W ↦ ringSheaf l W
  pull := N.pull

/-- Canonical section transport of native operations. Direct image is identity on
underlying sections; pullback and open extension are its uniquely normalized mates.
Source: Stacks Tags 03D6, 03D7, 03DI and 0B65
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
class NativeGeometry extends NativeRings.{u} l where
  [additive : ∀ T : Scheme.{u}, (sections l T).Additive]
  [limits : ∀ T : Scheme.{u}, PreservesFiniteLimits (sections l T)]
  [colimits : ∀ T : Scheme.{u}, PreservesFiniteColimits (sections l T)]
  [equivalence : ∀ T : Scheme.{u}, (sections l T).IsEquivalence]
  lower : ∀ {U V : Scheme.{u}} (g : U ⟶ V),
    ProEtale.adicLowerStar l g ⋙ sections l V ≅ sections l U ⋙
      proEtaleRingModuleDirectImage g (ringSheaf l V) (ringSheaf l U) (pull g)
  lower_normalized : ∀ {U V : Scheme.{u}} (g : U ⟶ V)
      (M : ProEtale.AdicSheaf l U) (W : V.ProEtᵒᵖ)
      (m : ((sections l V).obj ((ProEtale.adicLowerStar l g).obj M)).val.obj W),
    HEq (((lower g).hom.app M).val.app W m) m
  upper : ∀ {U V : Scheme.{u}} (g : U ⟶ V),
    ProEtale.adicUpperStar l g ⋙ sections l U ≅ sections l V ⋙
      proEtaleRingModulePullback g (ringSheaf l V) (ringSheaf l U) (pull g)
  upper_normalized : ∀ {U V : Scheme.{u}} (g : U ⟶ V),
    (mateEquiv (ProEtale.adicUpperStarLowerStarAdjunction l g)
      (proEtaleRingModuleAdjunction g (ringSheaf l V) (ringSheaf l U) (pull g))
      (.mk _ _ _ _ (upper g).inv)) = (lower g).hom
  extension : ∀ {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j],
    ProEtale.adicOpenImmersionLowerShriek l j ⋙ sections l V ≅ sections l U ⋙
      PurCompactSupport.openExtension (nativeCoefficients l) j
  extension_normalized : ∀ {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j],
    (mateEquiv (ProEtale.adicOpenImmersionLowerShriekAdjunction l j)
      (PurCompactSupport.openAdjunction (nativeCoefficients l) j)
      (.mk _ _ _ _ (extension j).inv)) = (upper j).hom

attribute [instance] NativeGeometry.additive NativeGeometry.limits NativeGeometry.colimits
  NativeGeometry.equivalence

/-- Additivity in the existing section presentation.
Source: internal/section module equivalence
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
noncomputable instance nativeSections_additive [G : NativeGeometry.{u} l]
    (T : Scheme.{u}) : (sections l T).Additive := G.additive T

/-- Additivity of the existing ringed direct image in native coefficients.
Source: Stacks, Modules on Sites
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
noncomputable instance nativeDirect_additive [G : NativeGeometry.{u} l]
    {U V : Scheme.{u}} (g : U ⟶ V) :
    (proEtaleRingModuleDirectImage g (ringSheaf l V) (ringSheaf l U) (G.pull g)).Additive :=
  proEtaleRingModuleDirectImage_additive g (ringSheaf l V) (ringSheaf l U) (G.pull g)

/-- The actual native compact-support functor, with the specified compactification.
Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
abbrev actual {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (ProEtale.adicOpenImmersionLowerShriek l c.i).mapDerivedCategory ⋙
    (ProEtale.adicLowerStar l c.g).rightDerivedFunctor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The proper transport uses the actual K-injective resolution comparisons.
Source: Stacks Tags 09T5 and 08BJ
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
def properTransport [G : NativeGeometry.{u} l] {U V : Scheme.{u}} (g : U ⟶ V) :
    (ProEtale.adicLowerStar l g).rightDerivedFunctor ⋙ (sections l V).mapDerivedCategory ≅
      (sections l U).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage g (ringSheaf l V) (ringSheaf l U) (G.pull g) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (ProEtale.adicLowerStar l g) (sections l V)).symm ≪≫
    Functor.rightDerivedFunctorNatIso (G.lower g) ≪≫
    Functor.rightDerivedFunctorCompIso (sections l U)
      (proEtaleRingModuleDirectImage g (ringSheaf l V) (ringSheaf l U) (G.pull g)) ≪≫
    Functor.isoWhiskerRight (sections l U).rightDerivedFunctorIsoMapDerivedCategory
      (proEtaleRingModuleDirectImage g (ringSheaf l V)
        (ringSheaf l U) (G.pull g)).rightDerivedFunctor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical ordinary-derived internal/section compact-support comparison.
Source: Stacks Tags 09T5, 08BJ and 03DI
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
def operationTransport [G : NativeGeometry.{u} l]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    actual l c ⋙ (sections l Y).mapDerivedCategory ≅
      (sections l X).mapDerivedCategory ⋙ PurCompactSupport.image (nativeCoefficients l) c :=
  Functor.isoWhiskerLeft
      (ProEtale.adicOpenImmersionLowerShriek l c.i).mapDerivedCategory
      (properTransport l c.g) ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso (G.extension c.i))
      (proEtaleRingDerivedDirectImage c.g (ringSheaf l Y) (ringSheaf l c.Z) (G.pull c.g))

/-- The published construction accepts a closure in the scheme universe. This is
only the canonical size lift of the same algebraic closure.
Source: Mathlib IsAlgClosed.of_ringEquiv and AlgEquiv.isAlgebraic
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
instance liftedClosure : IsAlgClosure (Padic l) (ULift.{u} (PadicAlgCl l)) where
  isAlgClosed := ⟨fun p ↦ by
    have h := (IsAlgClosed.splits (p.map ULift.ringEquiv.toRingHom)).map
      (ULift.ringEquiv : ULift.{u} (PadicAlgCl l) ≃+* PadicAlgCl l).symm.toRingHom
    simpa only [Polynomial.map_map,
      RingEquiv.symm_toRingHom_comp_toRingHom, Polynomial.map_id] using h⟩
  isAlgebraic := Algebra.IsAlgebraic.of_injective
    (ULift.algEquiv (R := Padic l) (A := PadicAlgCl l)).toAlgHom ULift.down_injective

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

/-- The finite field attached to an unlifted common-stage index, in the published
finite-operation interface. Source: common finite-field convention
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
abbrev finiteField (E : Index l (PadicAlgCl l)) : FieldStage.{u} l where
  carrier := Coefficient.{u} l (PadicAlgCl l) E

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem in
/-- The stage morphism is fixed by the very same construction record as the parent
adjunction. Its beta is the published scalar q, including identity field extensions.
Source: blueprint common-field comparisons
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
structure StageAction where
  system : (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) Y)
  finite : ∀ E : Index l (PadicAlgCl l),
    HEq (system.Φ E) (P.ring.operation c (.rational (finiteField l E))).F
  scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    HEq (system.β h)
      ((P.fields.rationalComparison c (finiteField l E) (finiteField l L)
        (coefficientInclusion l (PadicAlgCl l) E L h)).q)

/-- Normalization by the recorded proper/open scalar mate, on integral representatives.
Source: Bhatt--Scholze, Remark 6.8.15, blueprint common-field comparison
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
def IntegralNormalization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (alpha : stage.system.functor ⋙ target.J ≅ source.J ⋙ actual l c) : Prop :=
  ∀ (E : Index l (PadicAlgCl l))
      (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    let rationalInput :=
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
    let input := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj rationalInput
    ∃ (A B : sfRationalConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y)
      (r : A ⟶ B),
      HEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app rationalInput) ∧
    ∃ (M₁ M₂ M₃ M₄ M₅ : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : (sections l Y).mapDerivedCategory.obj
        ((stage.system.functor ⋙ target.J).obj input) ⟶ M₁)
      (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃) (a₃ : M₃ ⟶ M₄) (a₄ : M₄ ⟶ M₅)
      (a₅ : M₅ ⟶ (sections l Y).mapDerivedCategory.obj
        ((source.J ⋙ actual l c).obj input)),
      HEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      HEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient.{u} l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient.{u} l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₃ ((PurCompactSupport.comparison (change E) c).app K.obj) ∧
      HEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₅ ((operationTransport l c).inv.app (source.J.obj input)) ∧
      (sections l Y).mapDerivedCategory.map (alpha.hom.app input) =
        a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The complete comparison. Integral finite-Tor representatives suffice: integral
residue Tor supplies every integral constructible object. The displayed equality fixes
alpha by the proper/open scalar mate on derived arrows; functoriality fixes fractions
and the StageAction fields fix transitions between coefficient fields.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-compact-support-realization). -/
structure CompactSupportComparison [G : NativeGeometry.{u} l] where
  source : Realization l X
  target : Realization l Y
  middle : Realization l c.Z
  stage : StageAction l D hl P c
  change : ∀ E : Index l (PadicAlgCl l),
    PurCompactSupport.Change (PurCompactSupport.completed l (Coefficient.{u} l
      (PadicAlgCl l) E)) (nativeCoefficients l)
  change_source : ∀ E : Index l (PadicAlgCl l),
    (change E).map X = (source.coefficient E).integralMap l X
  change_target : ∀ E : Index l (PadicAlgCl l),
    (change E).map Y = (target.coefficient E).integralMap l Y
  change_middle : ∀ E : Index l (PadicAlgCl l),
    (change E).map c.Z = (middle.coefficient E).integralMap l c.Z
  alpha : stage.system.functor ⋙ target.J ≅ source.J ⋙ actual l c
  integral : IntegralNormalization l D hl P c source target stage change alpha
  preserves : ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K →
    ProEtale.DerivedCategory.boundedAdicConstructible l Y ((actual l c).obj K)

end WeilConjectures.LocallyFiniteAdicCompactSupport
