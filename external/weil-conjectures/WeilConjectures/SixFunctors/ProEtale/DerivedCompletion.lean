/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealization
import WeilConjectures.Algebra.Homology.RoosCoordinatesQuasiIso
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
/-!
# Derived completion for pulled-back continuous integral coefficients

md` (blueprint: definition-derived-adic-completeness).

The coefficient objects are the continuous condensed rings of DerivedNakayama,
pulled back by the published strong monoidal inverse image from the point.
Positive level n is indexed by n-1. Completion uses the explicit augmented Roos
complex on a K-flat representative, with zero homotopy in its second coordinate.
Normalization uses extension of scalars over the successive finite coefficient rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The continuous integral coefficient ring pulled back from the point.
Source: blueprint, coefficient sheaves (blueprint: definition-derived-adic-completeness). -/
abbrev ring (X : Scheme.{u}) := condensedRingObj (DerivedNakayama.integerRing l E) X

/-- Internal modules over the completed continuous coefficient ring.
Source: blueprint, ambient category (blueprint: definition-derived-adic-completeness). -/
abbrev Modules (X : Scheme.{u}) := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (ring l E X)

/-- The continuous finite quotient ring at the positive level n+1.
Source: blueprint, finite coefficient sheaves (blueprint: definition-derived-adic-completeness). -/
abbrev finiteRing (X : Scheme.{u}) (n : ℕ) :=
  condensedRingObj (DerivedNakayama.quotientRing l E (n + 1)) X

/-- Commutativity of the continuous finite quotient ring, before pullback.
Source: blueprint, coefficient sheaves (blueprint: definition-derived-adic-completeness). -/
instance quotientRing_isCommMonObj (n : ℕ) :
    IsCommMonObj (DerivedNakayama.quotientRing l E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj _

-- Keep the continuous coefficient structures behind small named instance constants.
local instance ringMonoidalObject (X : Scheme.{u}) : MonObj (ring l E X) :=
  inferInstance
local instance ringCommutative (X : Scheme.{u}) : IsCommMonObj (ring l E X) :=
  inferInstance
local instance finiteRingMonoidalObject (X : Scheme.{u}) (n : ℕ) :
    MonObj (finiteRing l E X n) := inferInstance
local instance finiteRingCommutative (X : Scheme.{u}) (n : ℕ) :
    IsCommMonObj (finiteRing l E X n) := inferInstance
local instance modulesMonoidal (X : Scheme.{u}) : MonoidalCategory (Modules l E X) :=
  inferInstance
local instance modulesSymmetric (X : Scheme.{u}) : SymmetricCategory (Modules l E X) :=
  inferInstance
local instance modulesClosed (X : Scheme.{u}) : MonoidalClosed (Modules l E X) :=
  inferInstance
local instance modulesMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive (Modules l E X) := inferInstance
local instance finiteModulesDerived (X : Scheme.{u}) (n : ℕ) :
    HasDerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (finiteRing l E X n)) :=
  inferInstance
local instance modulesDerived (X : Scheme.{u}) : HasDerivedCategory (Modules l E X) :=
  inferInstance
local instance modulesProducts (X : Scheme.{u}) : HasCountableProducts (Modules l E X) :=
  inferInstance
local instance complexProducts (X : Scheme.{u}) :
    HasCountableProducts (CochainComplex (Modules l E X) ℤ) := inferInstance
local instance modulesNatProducts (X : Scheme.{u}) :
    HasLimitsOfShape (Discrete ℕ) (Modules l E X) := HasCountableProducts.out ℕ
local instance complexNatProducts (X : Scheme.{u}) :
    HasLimitsOfShape (Discrete ℕ) (CochainComplex (Modules l E X) ℤ) := inferInstance
local instance complexNatLimit (X : Scheme.{u})
    (F : Discrete ℕ ⥤ CochainComplex (Modules l E X) ℤ) : HasLimit F :=
  HasLimitsOfShape.has_limit F

/-- The actual quotient morphism pulled back from the point.
Source: blueprint, reduction cone (blueprint: definition-derived-adic-completeness). -/
abbrev quotient (X : Scheme.{u}) (n : ℕ) : ring l E X ⟶ finiteRing l E X n :=
  (upperStarFromPoint X).map (DerivedNakayama.reductionRing l E (n + 1))

/-- The quotient topology induced by the spectral topology on the finite extension.
Source: blueprint, continuous coefficient rings (blueprint:
definition-derived-adic-completeness). -/
abbrev finiteTopology (n : ℕ) : TopologicalSpace (Padic.coefficientExtensionRing l E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstance

/-- The quotient transition is continuous for the quotient topologies.
Source: blueprint, reduction identities (blueprint: definition-derived-adic-completeness).
Proof: the quotient map O_E to O_E/pi^(n+2) is a quotient map. Its composite
with the displayed factor is the continuous quotient map to O_E/pi^(n+1),
so the quotient universal property proves continuity. -/
theorem continuous_transition (n : ℕ) :
    @Continuous _ _ (finiteTopology l E (n + 2)) (finiteTopology l E (n + 1))
      (Padic.coefficientExtensionTransition l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact continuous_quot_lift _ continuous_quot_mk

/-- Continuous postcomposition with the specified quotient transition.
Source: blueprint, canonical transitions (blueprint: definition-derived-adic-completeness). -/
def transitionRingSheaf (n : ℕ) :
    DerivedNakayama.quotientRingSheaf l E (n + 2) ⟶
      DerivedNakayama.quotientRingSheaf l E (n + 1) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ⟨{
    app := fun _ ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((Padic.coefficientExtensionTransition l E (n + 1)).compLeftContinuous _
        (continuous_transition l E n)).comp ULift.ringEquiv.toRingHom))
    naturality := fun _ _ _ ↦ rfl }⟩

/-- The same quotient transition as a morphism of internal condensed rings.
Source: blueprint, canonical transitions (blueprint: definition-derived-adic-completeness). -/
abbrev transitionRing (n : ℕ) :
    DerivedNakayama.quotientRing l E (n + 2) ⟶
      DerivedNakayama.quotientRing l E (n + 1) :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (transitionRingSheaf l E n)

/-- The transition between the pulled-back finite ring objects.
Source: blueprint, canonical transitions (blueprint: definition-derived-adic-completeness). -/
abbrev transition (X : Scheme.{u}) (n : ℕ) : finiteRing l E X (n + 1) ⟶
    finiteRing l E X n := (upperStarFromPoint X).map (transitionRing l E n)

/-- The finite quotient transition is a morphism of the pulled-back ring objects.
Source: functoriality of monoid objects (blueprint: definition-derived-adic-completeness). -/
instance transition_isMonHom (X : Scheme.{u}) (n : ℕ) :
    IsMonHom (transition l E X n) := by
  exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _ (transitionRing l E n)

private theorem restricted_linear {C : Type*} [Category C] [MonoidalCategory C]
    {R S T : C} [MonObj S] [MonObj T] (q : R ⟶ S) (r : R ⟶ T)
    (f : S ⟶ T) [IsMonHom f] (h : q ≫ f = r) :
    (q ▷ S ≫ μ[S]) ≫ f = R ◁ f ≫ (r ▷ T ≫ μ[T]) := by
  simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_def']
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, h]

/-- Quotient and transition maps preserve the scalar action on the regular module.
Source: blueprint, construction of the reduction cone
(blueprint: definition-derived-adic-completeness).
Proof: a ring homomorphism sends ab to its image product. In the transition equation,
the composite O_E to the smaller quotient equals the direct quotient. Apply these
identities to continuous functions pointwise; naturality and inverse image preserve them. -/
theorem coefficient_linearity :
    (∀ n : ℕ, Mod.act (Mod.regular (DerivedNakayama.integerRing l E)).X ≫
        DerivedNakayama.reductionRing l E (n + 1) =
      DerivedNakayama.integerRing l E ◁ DerivedNakayama.reductionRing l E (n + 1) ≫
        Mod.act (DerivedNakayama.quotientModule l E (n + 1)).X) ∧
    (∀ n : ℕ, Mod.act (DerivedNakayama.quotientModule l E (n + 2)).X ≫
        transitionRing l E n =
      DerivedNakayama.integerRing l E ◁ transitionRing l E n ≫
        Mod.act (DerivedNakayama.quotientModule l E (n + 1)).X) := by
  constructor
  · intro n
    change μ[DerivedNakayama.integerRing l E] ≫
      DerivedNakayama.reductionRing l E (n + 1) =
      DerivedNakayama.integerRing l E ◁ DerivedNakayama.reductionRing l E (n + 1) ≫
        (DerivedNakayama.reductionRing l E (n + 1) ▷
          DerivedNakayama.quotientRing l E (n + 1) ≫ μ[_])
    simpa only [tensorHom_def', Category.assoc] using
      (IsMonHom.mul_hom (DerivedNakayama.reductionRing l E (n + 1)))
  · intro n
    exact restricted_linear (DerivedNakayama.reductionRing l E (n + 2))
      (DerivedNakayama.reductionRing l E (n + 1)) (transitionRing l E n) (by rfl)

/-- The actual unit quotient map as an integral-module morphism on the point.
Source: blueprint, unit of the reduction cone (blueprint: definition-derived-adic-completeness). -/
def quotientUnit (n : ℕ) : Mod.regular (DerivedNakayama.integerRing l E) ⟶
    DerivedNakayama.quotientModule l E (n + 1) :=
  Mod.homMk (DerivedNakayama.reductionRing l E (n + 1))
    ((coefficient_linearity l E).1 n)

/-- The actual transition as an integral-module morphism on the point.
Source: blueprint, canonical transitions (blueprint: definition-derived-adic-completeness). -/
def quotientStep (n : ℕ) : DerivedNakayama.quotientModule l E (n + 2) ⟶
    DerivedNakayama.quotientModule l E (n + 1) :=
  Mod.homMk (transitionRing l E n) ((coefficient_linearity l E).2 n)

/-- The pulled-back finite coefficient module with its integral scalar action.
Source: blueprint, finite coefficient sheaves (blueprint: definition-derived-adic-completeness). -/
abbrev finiteModule (X : Scheme.{u}) (n : ℕ) : Modules l E X :=
  (DerivedNakayama.pullback l E X).obj (DerivedNakayama.quotientModule l E (n + 1))

/-- The coefficient quotient map from the monoidal unit, with the canonical action transport.
Source: blueprint, tensor units (blueprint: definition-derived-adic-completeness). -/
def finiteUnit (X : Scheme.{u}) (n : ℕ) : 𝟙_ (Modules l E X) ⟶ finiteModule l E X n :=
  (DerivedNakayama.regularPullbackIso l E X).inv ≫
    (DerivedNakayama.pullback l E X).map (quotientUnit l E n)

/-- Ordinary tensor reduction of a complex, used only on K-flat representatives.
Source: blueprint, K-flat construction of reductions
(blueprint: definition-derived-adic-completeness). -/
abbrev level (X : Scheme.{u}) (n : ℕ) :
    CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  (tensorRight (finiteModule l E X n)).mapHomologicalComplex (.up ℤ)

/-- The strict transition P tensor B_(n+2) to P tensor B_(n+1).
Source: blueprint, canonical transitions (blueprint: definition-derived-adic-completeness). -/
def levelStep (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (level l E X (n + 1)).obj P ⟶ (level l E X n).obj P :=
  (NatTrans.mapHomologicalComplex
    ((tensoringRight (Modules l E X)).map
      ((DerivedNakayama.pullback l E X).map (quotientStep l E n))) (.up ℤ)).app P

/-- The chain map p to p tensor 1 at each positive level.
Source: blueprint, canonical reduction cone (blueprint: definition-derived-adic-completeness). -/
def levelUnit (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    P ⟶ (level l E X n).obj P :=
  (NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso (Modules l E X)).inv ≫
      (tensoringRight (Modules l E X)).map (finiteUnit l E X n)) (.up ℤ)).app P

/-- The termwise product of the strict reduction tower of P.
Source: blueprint, Roos model (blueprint: definition-derived-adic-completeness). -/
abbrev product (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :=
  ∏ᶜ fun n : ℕ ↦ (level l E X n).obj P

/-- The specified 1 minus shift on the strict reduction product.
Source: Stacks 08TC, blueprint Roos model (blueprint: definition-derived-adic-completeness). -/
def oneSubShift (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    product l E X P ⟶ product l E X P :=
  towerTransitionEndomorphism (levelStep l E X P)

/-- The two coordinates (x,y) of the reduction Roos complex in degree i.
Source: blueprint, Roos model (blueprint: definition-derived-adic-completeness). -/
def roosX (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :=
  (product l E X P).X i ⊞ (product l E X P).X (i - 1)

/-- The differential (dx,(1-s)x-dy) of the reduction Roos complex.
Source: blueprint, Roos model (blueprint: definition-derived-adic-completeness). -/
def roosD (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :
    roosX l E X P i ⟶ roosX l E X P (i + 1) :=
  biprod.lift (biprod.fst ≫ (product l E X P).d i (i + 1))
    (biprod.fst ≫ (oneSubShift l E X P).f i ≫
      eqToHom (congrArg (product l E X P).X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ (product l E X P).d (i - 1) ((i + 1) - 1))

private def genericRoosX {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (i : ℤ) := V.X i ⊞ V.X (i - 1)

private def genericRoosD {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (i : ℤ) :
    genericRoosX V i ⟶ genericRoosX V (i + 1) :=
  biprod.lift (biprod.fst ≫ V.d i (i + 1))
    (biprod.fst ≫ t.f i ≫
      eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ V.d (i - 1) ((i + 1) - 1))

private theorem genericRoosD_sq {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (i : ℤ) :
    genericRoosD V t i ≫ genericRoosD V t (i + 1) = 0 := by
  dsimp only [genericRoosD, genericRoosX]
  apply biprod.hom_ext
  · simp
  · suffices biprod.fst ≫ V.d i (i + 1 + 1 - 1) ≫ t.f (i + 1 + 1 - 1) -
        biprod.fst ≫ eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) ≫
          V.d (i + 1 - 1) (i + 1 + 1 - 1) ≫ t.f (i + 1 + 1 - 1) = 0 by
      simpa using this
    have hd := V.eqToHom_comp_d
      (i := i) (i' := i + 1 - 1) (j := i + 1 + 1 - 1)
      (by change i + 1 = i + 1 + 1 - 1; omega)
      (by change i + 1 - 1 + 1 = i + 1 + 1 - 1; omega)
    rw [reassoc_of% hd, sub_self]

private def genericRoos {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) : CochainComplex C ℤ :=
  CochainComplex.of (genericRoosX V) (genericRoosD V t) (genericRoosD_sq V t)

/-- The specified Roos differential squares to zero.
Source: blueprint, Roos construction (blueprint: definition-derived-adic-completeness).
Proof: the first coordinate is d squared. In the second coordinate the two mixed
terms cancel because 1-s is a chain map; the remaining d squared term is zero. -/
theorem roosD_sq (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :
    roosD l E X P i ≫ roosD l E X P (i + 1) = 0 := by
  exact genericRoosD_sq (product l E X P) (oneSubShift l E X P) i

/-- The explicit homotopy inverse limit of the strict derived reductions of a K-flat P.
Source: Stacks 08TC, blueprint Roos model (blueprint: definition-derived-adic-completeness). -/
def roos (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    CochainComplex (Modules l E X) ℤ :=
  CochainComplex.of (roosX l E X P) (roosD l E X P) (roosD_sq l E X P)

/-- The product of the specified tensor-unit maps.
Source: blueprint, strict reduction augmentation (blueprint:
definition-derived-adic-completeness). -/
def unitProduct (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    P ⟶ product l E X P := Pi.lift (levelUnit l E X P)

private theorem quotientUnit_step (n : ℕ) :
    quotientUnit l E (n + 1) ≫ quotientStep l E n = quotientUnit l E n := by
  apply Mod.hom_ext
  rfl

private theorem finiteUnit_step (X : Scheme.{u}) (n : ℕ) :
    finiteUnit l E X (n + 1) ≫
      (DerivedNakayama.pullback l E X).map (quotientStep l E n) = finiteUnit l E X n := by
  dsimp only [finiteUnit]
  rw [Category.assoc, ← Functor.map_comp, quotientUnit_step]

private theorem levelUnit_step (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ)
    (n : ℕ) : levelUnit l E X P (n + 1) ≫ levelStep l E X P n = levelUnit l E X P n := by
  apply HomologicalComplex.hom_ext
  intro i
  change ((ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X (n + 1)) ≫
    P.X i ◁ (DerivedNakayama.pullback l E X).map (quotientStep l E n) =
    (ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X n
  rw [Category.assoc, ← whiskerLeft_comp, finiteUnit_step]

private theorem unitProduct_oneSubShift (X : Scheme.{u})
    (P : CochainComplex (Modules l E X) ℤ) :
    unitProduct l E X P ≫ oneSubShift l E X P = 0 := by
  apply Pi.hom_ext
  intro n
  simp [oneSubShift, towerTransitionEndomorphism, towerProductShift, unitProduct,
    levelUnit_step]

/-- The map with coordinates (unit,0) is a chain map.
Source: blueprint, canonical reduction comparison (blueprint: definition-derived-adic-completeness).
Proof: the tensor units commute with d. Quotient transitions preserve 1 and commute
with the quotient maps, so (1-s) unit = 0. These are exactly the two chain-map equations. -/
theorem augmentation_comm (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ)
    (i : ℤ) :
    biprod.lift ((unitProduct l E X P).f i) 0 ≫ (roos l E X P).d i (i + 1) =
      P.d i (i + 1) ≫ biprod.lift ((unitProduct l E X P).f (i + 1)) 0 := by
  have hz (j : ℤ) : (unitProduct l E X P).f j ≫ (oneSubShift l E X P).f j = 0 :=
    congrArg (fun f ↦ f.f j) (unitProduct_oneSubShift l E X P)
  simp only [roos, CochainComplex.of_d]
  dsimp only [roosD, roosX]
  apply biprod.hom_ext
  · simp
  · simpa using hz (i + 1 - 1)

/-- The canonical completion comparison, with the specified zero shifted-product component.
Source: blueprint, canonical reduction comparison (blueprint:
definition-derived-adic-completeness). -/
def augmentation (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    P ⟶ roos l E X P :=
  CochainComplex.ofHom (fun i ↦ biprod.lift ((unitProduct l E X P).f i) 0)
    (augmentation_comm l E X P)

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts
  AdicCompletion.modulesNatProducts AdicCompletion.complexNatProducts
  AdicCompletion.complexNatLimit

/-- Derived completeness in the unbounded internal-module category of the continuous
pulled-back integral coefficients. A K-flat representative computes the derived reductions;
the specified augmentation, with zero nullhomotopy, must be invertible after localization.
Source: blueprint definition and its Roos construction
(blueprint: definition-derived-adic-completeness). -/
def IsDerivedComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X)) : Prop :=
  ∃ P : CochainComplex (AdicCompletion.Modules l E X) ℤ,
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
        IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint
attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed
  modulesMonoidalPreadditive finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts
  complexNatLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The quotient maps factor through each consecutive quotient, as ring-object morphisms.
Source: blueprint, canonical coefficient tower (blueprint: definition-derived-adic-completeness).
Proof: quotient factor after quotient is the smaller quotient homomorphism.
This identity holds pointwise on continuous functions, and inverse image preserves composition. -/
theorem quotient_transition (n : ℕ) :
    quotient l E X (n + 1) ≫ transition l E X n = quotient l E X n := by
  rw [← Functor.map_comp]
  congr 1

/-- The derived category over the positive finite coefficient level n+1.
Source: blueprint, normalized complexes (blueprint: definition-derived-adic-completeness). -/
abbrev FiniteDerived (n : ℕ) := DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (finiteRing l E X n))

/-- Canonical derived extension from the integral coefficients to positive level n+1.
Source: blueprint, K_n (blueprint: definition-derived-adic-completeness). -/
abbrev derivedReduction (n : ℕ) : DerivedCategory (Modules l E X) ⥤ FiniteDerived l E X n :=
  (Mod.extendScalars (quotient l E X n)).leftDerivedFunctor

/-- Exact derived restriction from level n+1 back to the integral ring.
Source: blueprint, reduction tower (blueprint: definition-derived-adic-completeness). -/
abbrev restrict (n : ℕ) : FiniteDerived l E X n ⥤ DerivedCategory (Modules l E X) :=
  (Mod.comap (quotient l E X n)).mapDerivedCategory

/-- Consecutive derived base change over B_(n+2), rather than over the integral ring.
Source: blueprint, reduction identities (blueprint: definition-derived-adic-completeness). -/
abbrev finiteExtend (n : ℕ) : FiniteDerived l E X (n + 1) ⥤ FiniteDerived l E X n :=
  (Mod.extendScalars (transition l E X n)).leftDerivedFunctor

/-- Exact restriction along B_(n+2) to B_(n+1).
Source: blueprint, normalization (blueprint: definition-derived-adic-completeness). -/
abbrev finiteRestrict (n : ℕ) : FiniteDerived l E X n ⥤ FiniteDerived l E X (n + 1) :=
  (Mod.comap (transition l E X n)).mapDerivedCategory

/-- Canonical composition of exact restriction, including the quotient-factor identity.
Source: blueprint, coherent reductions (blueprint: definition-derived-adic-completeness). -/
def restrictComp (n : ℕ) :
    finiteRestrict l E X n ⋙ restrict l E X (n + 1) ≅ restrict l E X n :=
  Functor.mapDerivedCategoryCompIso
    (Mod.comap (transition l E X n)) (Mod.comap (quotient l E X (n + 1))) ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (quotient l E X (n + 1)) (transition l E X n)).symm ≪≫
        Mod.comapCongr (quotient_transition l E X n))

/-- Composition of left adjoints when the composite right adjoint has been identified.
Source: uniqueness of left adjoints (blueprint: definition-derived-adic-completeness). -/
def adjunctionAssociation
    {C D A : Type*} [Category C] [Category D] [Category A]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ A} {I : A ⥤ D}
    {L : C ⥤ A} {R : A ⥤ C}
    (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ R) (e : I ⋙ G ≅ R) : F ⋙ H ≅ L :=
  ((a.comp b).ofNatIsoRight e).leftAdjointUniq c

/-- The derived reduction identity determined by the canonical adjunction units and counits.
This is the canonical association (P tensor B_(n+2)) tensor B_(n+1) = P tensor B_(n+1).
Source: blueprint, normalization (blueprint: definition-derived-adic-completeness). -/
def reductionComp (n : ℕ) :
    derivedReduction l E X (n + 1) ⋙ finiteExtend l E X n ≅ derivedReduction l E X n :=
  let a : derivedReduction l E X (n + 1) ⊣ restrict l E X (n + 1) :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1))
  let b : finiteExtend l E X n ⊣ finiteRestrict l E X n :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n)
  let c : derivedReduction l E X n ⊣ restrict l E X n :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)
  adjunctionAssociation a b c (restrictComp l E X n)

/-- Transition between the derived reductions, given by the consecutive unit and association.
Source: blueprint, canonical transition maps (blueprint: definition-derived-adic-completeness). -/
def derivedStep (K : DerivedCategory (Modules l E X)) (n : ℕ) :
    (derivedReduction l E X (n + 1)).obj K ⟶
      (finiteRestrict l E X n).obj ((derivedReduction l E X n).obj K) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n)).unit.app
      ((derivedReduction l E X (n + 1)).obj K) ≫
    (finiteRestrict l E X n).map ((reductionComp l E X n).hom.app K)

/-- The canonical comparison on any specified K-flat representative of K.
Source: blueprint, canonical completion map (blueprint: definition-derived-adic-completeness). -/
def completionMap (K : DerivedCategory (Modules l E X))
    (P : CochainComplex (Modules l E X) ℤ) (e : DerivedCategory.Q.obj P ≅ K) :
    K ⟶ DerivedCategory.Q.obj (roos l E X P) :=
  e.inv ≫ DerivedCategory.Q.map (augmentation l E X P)

private def finiteModuleIso (X : Scheme.{u}) (n : ℕ) :
    finiteModule l E X n ≅ (Mod.comap (quotient l E X n)).obj
      (Mod.regular (finiteRing l E X n)) :=
  (Functor.mapModComapIso (upperStarFromPoint X)
    (DerivedNakayama.reductionRing l E (n + 1))).app
      (Mod.regular (DerivedNakayama.quotientRing l E (n + 1)))

private theorem genericCocone_d_snd {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (q : ℤ) :
    (CochainComplex.mappingCocone t).d q (q + 1) ≫
        (CochainComplex.mappingCocone.snd t).v
          (q + 1) q (by omega) =
      -((CochainComplex.mappingCocone.snd t).v
          q (q - 1) (by omega) ≫ V.d (q - 1) q) -
        (CochainComplex.mappingCocone.fst t).f q ≫
          t.f q := by
  have h := CochainComplex.mappingCone.d_snd_v t
    (q + -1) q (by omega)
  simp only [CochainComplex.mappingCocone.snd, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cocycle.leftShift_coe, HomologicalComplex.neg_f_apply,
    CochainComplex.HomComplex.Cocycle.homOf]
  rw [CochainComplex.HomComplex.Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ q (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ (q + -1) (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v (n := 1) _ _ _ _ _ _ _ (q + -1) (by omega)]
  dsimp only [CochainComplex.mappingCocone]
  simp only [show (-1 * -1 + -1 * (-1 - 1) / 2 : ℤ) = 2 by rfl,
    show (-1 * 0 + -1 * (-1 - 1) / 2 : ℤ) = 1 by rfl,
    show Int.negOnePow 2 = 1 by rfl, Int.negOnePow_one, Units.neg_smul,
    one_smul, neg_neg, CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg,
    CochainComplex.shiftFunctorObjXIso, Preadditive.neg_comp, Category.assoc,
    HomologicalComplex.d_comp_XIsoOfEq_hom_assoc]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  rw [← V.XIsoOfEq_hom_comp_d (by omega : q - 1 = q + -1) q]
  simp only [← Category.assoc, CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom]
  rw [h]
  erw [Category.id_comp, Category.id_comp]
  simp only [neg_add_rev]
  abel

private def genericCoconeCoordinateIso {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (i : ℤ) :
    (CochainComplex.mappingCocone t).X i ≅ (genericRoos V t).X i where
  hom := biprod.lift ((CochainComplex.mappingCocone.fst t).f i)
    (-(CochainComplex.mappingCocone.snd t).v i (i - 1) (by omega))
  inv := biprod.desc ((CochainComplex.mappingCocone.inl t).v i i
    (add_zero i))
    (-(CochainComplex.mappingCocone.inr t).1.v
      (i - 1) i (by omega))
  hom_inv_id := by
    simpa [biprod.lift_desc] using
      CochainComplex.mappingCocone.id_X t i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

private def genericCoconeIso {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) :
    CochainComplex.mappingCocone t ≅ genericRoos V t :=
  HomologicalComplex.Hom.isoOfComponents (genericCoconeCoordinateIso V t) (by
    intro q r h
    obtain rfl : q + 1 = r := h
    apply biprod.hom_ext
    · simp only [genericCoconeCoordinateIso, genericRoos, CochainComplex.of_d, genericRoosD,
        Category.assoc, biprod.lift_fst_assoc, biprod.lift_fst]
      exact (CochainComplex.mappingCocone.fst t).comm q (q + 1)
    · simp only [genericCoconeCoordinateIso, genericRoos, CochainComplex.of_d, genericRoosD,
        Category.assoc, Preadditive.comp_sub, biprod.lift_fst_assoc,
        biprod.lift_snd_assoc, biprod.lift_snd]
      have hq : q + 1 - 1 = q := by omega
      apply (cancel_mono (eqToHom (congrArg V.X hq))).mp
      simp only [Preadditive.sub_comp, Category.assoc, Preadditive.neg_comp,
        Preadditive.comp_neg, eqToHom_trans]
      rw [show V.d (q - 1) (q + 1 - 1) ≫
          eqToHom (congrArg V.X hq) =
          V.d (q - 1) q by
        exact V.d_comp_XIsoOfEq_hom hq (q - 1)]
      rw [show (CochainComplex.mappingCocone.snd t).v
          (q + 1) (q + 1 - 1) (by omega) ≫
          eqToHom (congrArg V.X hq) =
          (CochainComplex.mappingCocone.snd t).v
            (q + 1) q (by omega) by
        exact CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom _ _ _ _ _ hq]
      simp only [eqToHom_refl, Category.comp_id]
      rw [genericCocone_d_snd]
      simp [neg_sub, sub_neg_eq_add])

private theorem modules_countableAB4Star : CountableAB4Star (Modules l E X) :=
  .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)

private def productMap {P P' : CochainComplex (Modules l E X) ℤ} (a : P ⟶ P') :
    product l E X P ⟶ product l E X P' :=
  Limits.Pi.map (fun n ↦ (level l E X n).map a)

private theorem productMap_oneSubShift {P P' : CochainComplex (Modules l E X) ℤ}
    (a : P ⟶ P') :
    productMap l E X a ≫ oneSubShift l E X P' =
      oneSubShift l E X P ≫ productMap l E X a := by
  apply Pi.hom_ext
  intro n
  have ht := (NatTrans.mapHomologicalComplex
    ((tensoringRight (Modules l E X)).map
      ((DerivedNakayama.pullback l E X).map (quotientStep l E n))) (.up ℤ)).naturality a
  change (level l E X (n + 1)).map a ≫ levelStep l E X P' n =
    levelStep l E X P n ≫ (level l E X n).map a at ht
  simp [productMap, oneSubShift, towerTransitionEndomorphism, towerProductShift,
    Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp, ht]

private theorem genericRoosMap_comm
    {A : Type v} [Category.{w} A] [Abelian A]
    {V V' : CochainComplex A ℤ} (t : V ⟶ V) (t' : V' ⟶ V')
    (a : V ⟶ V') (h : a ≫ t' = t ≫ a) (i : ℤ) :
    biprod.map (a.f i) (a.f (i - 1)) ≫ genericRoosD V' t' i =
      genericRoosD V t i ≫ biprod.map (a.f (i + 1)) (a.f ((i + 1) - 1)) := by
  have hs (j : ℤ) := congrArg (fun f ↦ HomologicalComplex.Hom.f f j) h
  dsimp only [HomologicalComplex.comp_f] at hs
  apply biprod.hom_ext
  · simp +instances [genericRoosD, genericRoosX, Category.assoc]
  · simp +instances only [genericRoosX, genericRoosD, add_sub_cancel_right,
      eqToHom_naturality, Category.assoc, biprod.lift_snd, Preadditive.comp_sub,
      biprod.map_fst_assoc, eqToHom_naturality_assoc, biprod.map_snd_assoc,
      HomologicalComplex.Hom.comm, biprod.map_snd, biprod.lift_snd_assoc,
      Preadditive.sub_comp, sub_left_inj]
    rw [hs (i + 1 - 1)]

private theorem roosMap_comm {P P' : CochainComplex (Modules l E X) ℤ}
    (a : P ⟶ P') (i : ℤ) :
    biprod.map ((productMap l E X a).f i) ((productMap l E X a).f (i - 1)) ≫
        (roos l E X P').d i (i + 1) =
      (roos l E X P).d i (i + 1) ≫
        biprod.map ((productMap l E X a).f (i + 1))
          ((productMap l E X a).f ((i + 1) - 1)) := by
  simpa only [roos, CochainComplex.of_d, roosD, genericRoosD, genericRoosX, roosX]
    using genericRoosMap_comm (oneSubShift l E X P) (oneSubShift l E X P')
    (productMap l E X a) (productMap_oneSubShift l E X a) i

private def roosMap {P P' : CochainComplex (Modules l E X) ℤ} (a : P ⟶ P') :
    roos l E X P ⟶ roos l E X P' :=
  CochainComplex.ofHom
    (fun i ↦ biprod.map ((productMap l E X a).f i) ((productMap l E X a).f (i - 1)))
    (roosMap_comm l E X a)

private theorem augmentation_naturality {P P' : CochainComplex (Modules l E X) ℤ}
    (a : P ⟶ P') :
    augmentation l E X P ≫ roosMap l E X a = a ≫ augmentation l E X P' := by
  ext i : 1
  change biprod.lift ((unitProduct l E X P).f i) 0 ≫
    biprod.map ((productMap l E X a).f i) ((productMap l E X a).f (i - 1)) =
      a.f i ≫ biprod.lift ((unitProduct l E X P').f i) 0
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    have h : unitProduct l E X P ≫ productMap l E X a = a ≫ unitProduct l E X P' := by
      apply Pi.hom_ext
      intro n
      simp only [unitProduct, productMap, Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc,
        Pi.lift_comp_π]
      exact ((NatTrans.mapHomologicalComplex
        ((rightUnitorNatIso (Modules l E X)).inv ≫
          (tensoringRight (Modules l E X)).map (finiteUnit l E X n)) (.up ℤ)).naturality a).symm
    exact congrArg (fun f ↦ f.f i) h
  · simp

private theorem roosMap_quasiIso
    {P P' : CochainComplex (Modules l E X) ℤ}
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P')
    (a : P ⟶ P') [QuasiIso a] : QuasiIso (roosMap l E X a) := by
  let := modules_countableAB4Star l E X
  have hlevel (n : ℕ) : QuasiIso ((level l E X n).map a) := by
    let F := tensorRight (finiteModule l E X n)
    let : F.PreservesKFlatQuasiIso :=
      Functor.PreservesKFlatQuasiIso.mk' F
        (fun K hK hKa ↦ CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa _)
    exact F.quasiIso_mapHomologicalComplex_map_of_kFlat hP hP' a
  let f := Discrete.natTrans
    (F := Discrete.functor (fun n : ℕ ↦ (level l E X n).obj P))
    (G := Discrete.functor (fun n : ℕ ↦ (level l E X n).obj P'))
    (fun n ↦ (level l E X n.as).map a)
  have (n : Discrete ℕ) : QuasiIso (f.app n) := hlevel n.as
  have hp : QuasiIso (productMap l E X a) := HomologicalComplex.quasiIso_limMap f
  exact CochainComplex.quasiIso_of_roos_coordinates
    (product l E X P) (product l E X P') (roos l E X P) (roos l E X P')
    (oneSubShift l E X P) (oneSubShift l E X P')
    (fun _ ↦ Iso.refl _) (fun _ ↦ Iso.refl _)
    (by intro i; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      roos, CochainComplex.of_d, roosD])
    (by intro i; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      roos, CochainComplex.of_d, roosD])
    (productMap l E X a) (roosMap l E X a) (by intro i; rfl) hp

private theorem generic_augmentation_isIso_iff
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    (good : CochainComplex A ℤ → Prop)
    (hres : ∀ Z : CochainComplex A ℤ,
      ∃ (W : CochainComplex A ℤ) (q : W ⟶ Z), QuasiIso q ∧ good W)
    (T : CochainComplex A ℤ → CochainComplex A ℤ)
    (eta : ∀ P, P ⟶ T P)
    (mapT : ∀ {P P' : CochainComplex A ℤ}, (P ⟶ P') → (T P ⟶ T P'))
    (hnat : ∀ {P P' : CochainComplex A ℤ} (a : P ⟶ P'),
      eta P ≫ mapT a = a ≫ eta P')
    (hmap : ∀ {P P' : CochainComplex A ℤ}, good P → good P' →
      ∀ (a : P ⟶ P') [QuasiIso a], QuasiIso (mapT a))
    (P P' : CochainComplex A ℤ) (hP : good P) (hP' : good P')
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    IsIso (DerivedCategory.Q.map (eta P)) ↔ IsIso (DerivedCategory.Q.map (eta P')) := by
  classical
  obtain ⟨Z, t, ht, f, he⟩ := DerivedCategory.right_fac e.hom
  let := ht
  have ht' : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).1 ht
  have hf : IsIso (DerivedCategory.Q.map f) := by
    have hh : DerivedCategory.Q.map f = DerivedCategory.Q.map t ≫ e.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [hh]
    infer_instance
  have hf' : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).1 hf
  obtain ⟨W, q, hq, hW⟩ := hres Z
  let := ht'
  let := hf'
  let := hq
  let u := q ≫ t
  let b := q ≫ f
  have : QuasiIso u := inferInstance
  have : QuasiIso b := inferInstance
  have := hmap hW hP u
  have := hmap hW hP' b
  have step (A : CochainComplex (A) ℤ)
      (c : W ⟶ A) [QuasiIso c] [QuasiIso (mapT c)] :
      IsIso (DerivedCategory.Q.map (eta W)) ↔
        IsIso (DerivedCategory.Q.map (eta A)) := by
    have hn := congrArg DerivedCategory.Q.map (hnat c)
    simp only [Functor.map_comp] at hn
    constructor
    · intro h
      let := h
      have : IsIso (DerivedCategory.Q.map c ≫
          DerivedCategory.Q.map (eta A)) := by rw [← hn]; infer_instance
      exact IsIso.of_isIso_comp_left (DerivedCategory.Q.map c) _
    · intro h
      let := h
      have : IsIso (DerivedCategory.Q.map (eta W) ≫
          DerivedCategory.Q.map (mapT c)) := by rw [hn]; infer_instance
      exact IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map (mapT c))
  exact (step P u).symm.trans (step P' b)

private theorem augmentation_isIso_iff
    (P P' : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P')
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    IsIso (DerivedCategory.Q.map (augmentation l E X P)) ↔
      IsIso (DerivedCategory.Q.map (augmentation l E X P'))  := by
  exact generic_augmentation_isIso_iff
    ((HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat)
    (fun Z ↦ by
      obtain ⟨W, q, hq, _, hW⟩ := CochainComplex.exists_quasiIso_flat_kFlat Z
      exact ⟨W, q, hq, hW⟩)
    (roos l E X) (augmentation l E X) (roosMap l E X)
    (augmentation_naturality l E X) (roosMap_quasiIso l E X) P P' hP hP' e

/-- Completeness can be checked on any K-flat representative, retaining the actual
augmentation rather than merely an isomorphism between the two objects.
Source: blueprint, representative independence (blueprint: definition-derived-adic-completeness).
Proof: refine a derived isomorphism to a common roof and replace its vertex by a
native K-flat resolution. Tensoring a quasi-isomorphism between K-flat complexes
with any coefficient object preserves quasi-isomorphisms: its mapping cone is
K-flat and acyclic, so tensoring that cone remains acyclic. Pro-etale repleteness
makes countable products exact in internal modules. Products of these tensor
maps and the generic Roos coordinate comparison therefore give quasi-isomorphisms
of Roos complexes. Their two-coordinate maps commute with the specified (unit,0)
augmentations. Cancel the two invertible legs after localization. Finally cancel
the representative isomorphism e in the definition of completionMap. -/
theorem isDerivedComplete_iff (K : DerivedCategory (Modules l E X))
    (P : CochainComplex (Modules l E X) ℤ)
    (_hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ K) :
    IsDerivedComplete l E X K ↔ IsIso (completionMap l E X K P e) := by
  constructor
  · rintro ⟨P', hP', ⟨e'⟩, hη⟩
    have := (augmentation_isIso_iff l E X P' P hP' _hP (e' ≪≫ e.symm)).mp hη
    unfold completionMap
    infer_instance
  · intro h
    change IsIso (e.inv ≫ DerivedCategory.Q.map (augmentation l E X P)) at h
    let := h
    have : IsIso (DerivedCategory.Q.map (augmentation l E X P)) :=
      IsIso.of_isIso_comp_left e.inv _
    exact ⟨P, _hP, ⟨e⟩, inferInstance⟩

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint
attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed
  modulesMonoidalPreadditive finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts
  complexNatLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The derived reduction at level n+1, regarded as an integral-coefficient complex.
Source: blueprint, inverse system (blueprint: definition-derived-adic-completeness). -/
abbrev integralLevel (K : DerivedCategory (Modules l E X)) (n : ℕ) :=
  (restrict l E X n).obj ((derivedReduction l E X n).obj K)

/-- The canonical transition after exact restriction to the common integral category.
Source: blueprint, compatible reduction tower (blueprint: definition-derived-adic-completeness). -/
def integralStep (K : DerivedCategory (Modules l E X)) (n : ℕ) :
    integralLevel l E X K (n + 1) ⟶ integralLevel l E X K n :=
  (restrict l E X (n + 1)).map (derivedStep l E X K n) ≫
    (restrictComp l E X n).hom.app ((derivedReduction l E X n).obj K)

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale.AdicCompletion

section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts
  AdicCompletion.modulesNatProducts AdicCompletion.complexNatProducts
  AdicCompletion.complexNatLimit
attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed
  modulesMonoidalPreadditive finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts
  complexNatLimit


private theorem genericCoconeIso_inv_fst_f
    {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (i : ℤ) :
    (genericCoconeIso V t).inv.f i ≫ (CochainComplex.mappingCocone.fst t).f i =
      (biprod.fst : (genericRoos V t).X i ⟶ V.X i) := by
  change (genericCoconeCoordinateIso V t i).inv ≫
    (CochainComplex.mappingCocone.fst t).f i = _
  apply (cancel_epi (genericCoconeCoordinateIso V t i).hom).mp
  rw [Iso.hom_inv_id_assoc]
  simp only [genericCoconeCoordinateIso, biprod.lift_fst]

private theorem strictScalarRealization
    (K : DerivedCategory (Modules l E X)) (P : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (eP : DerivedCategory.Q.obj P ≅ K) :
    ∃ e : ∀ n, DerivedCategory.Q.obj ((level l E X n).obj P) ≅ integralLevel l E X K n,
      (∀ n, DerivedCategory.Q.map (levelStep l E X P n) ≫ (e n).hom =
        (e (n + 1)).hom ≫ integralStep l E X K n) ∧
      (∀ n, DerivedCategory.Q.map (levelUnit l E X P n) ≫ (e n).hom =
        eP.hom ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app K)
    := by
  exact Mod.KFlatScalarTower.realization
    (ring l E X) (finiteRing l E X) (quotient l E X) (transition l E X)
    (quotient_transition l E X) (finiteModule l E X) (finiteUnit l E X)
    (fun n ↦ (DerivedNakayama.pullback l E X).map (quotientStep l E n))
    (finiteModuleIso l E X)
    (by
      intro n
      change (𝟙 _ ≫ (upperStarFromPoint X).map
        (DerivedNakayama.reductionRing l E (n + 1))) ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id])
    (by
      intro n
      change (upperStarFromPoint X).map (transitionRing l E n) ≫ 𝟙 _ =
        𝟙 _ ≫ (upperStarFromPoint X).map (transitionRing l E n)
      simp only [Category.id_comp, Category.comp_id]) K P hP eP

private theorem composed_unit_compatible
    {C D A : Type*} [Category C] [Category D] [Category A]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ A} {I : A ⥤ D}
    {L : C ⥤ A} {R : A ⥤ C}
    (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ R) (e : I ⋙ G ≅ R) (K : C) :
    let t := ((a.comp b).ofNatIsoRight e).leftAdjointUniq c
    a.unit.app K ≫ (G.map (b.unit.app (F.obj K) ≫ I.map (t.hom.app K)) ≫
      e.hom.app (L.obj K)) = c.unit.app K := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app ((a.comp b).ofNatIsoRight e) c K
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app, Category.assoc, Functor.whiskerLeft_app] at h
  rw [← e.hom.naturality ((((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app K)] at h
  simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using h

/-- The coherent tensor-unit maps to the derived reductions.
Source: blueprint, reduction cone (blueprint: definition-derived-adic-completeness).
Proof: reductionComp is formed by left-adjoint uniqueness, which identifies the
composite unit with the direct unit. Composing this identity with restrictComp
is exactly the displayed compatibility of the positive consecutive units. -/
theorem reductionUnit_compatible (K : DerivedCategory (Modules l E X)) (n : ℕ) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1))).unit.app K ≫
        integralStep l E X K n =
      (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app K := by
  exact composed_unit_compatible
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1)))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n))
    (restrictComp l E X n) K

private theorem generic_roosLimit
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    [HasCountableProducts A] [CountableAB4Star A]
    (V : ℕ → CochainComplex A ℤ) (t : ∀ n, V (n + 1) ⟶ V n)
    (P : CochainComplex A ℤ) (K : DerivedCategory A)
    (e : DerivedCategory.Q.obj P ≅ K)
    (D : ℕ → DerivedCategory A) (d : ∀ n, D (n + 1) ⟶ D n) [HasProduct D]
    (c : ∀ n, P ⟶ V n) (uD : ∀ n, K ⟶ D n)
    (aug : P ⟶ genericRoos (∏ᶜ V) (towerTransitionEndomorphism t))
    (haug : aug ≫ (genericCoconeIso (∏ᶜ V) (towerTransitionEndomorphism t)).inv ≫
      CochainComplex.mappingCocone.fst (towerTransitionEndomorphism t) = Pi.lift c)
    (eL : ∀ n, DerivedCategory.Q.obj (V n) ≅ D n)
    (hstep : ∀ n, DerivedCategory.Q.map (t n) ≫ (eL n).hom = (eL (n + 1)).hom ≫ d n)
    (hunit : ∀ n, DerivedCategory.Q.map (c n) ≫ (eL n).hom = e.hom ≫ uD n) :
    ∃ (p : DerivedCategory.Q.obj
        (genericRoos (∏ᶜ V) (towerTransitionEndomorphism t)) ⟶ ∏ᶜ D)
      (δ : ∏ᶜ D ⟶ (DerivedCategory.Q.obj
        (genericRoos (∏ᶜ V) (towerTransitionEndomorphism t)))⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle d _ p δ ∧
        (e.inv ≫ DerivedCategory.Q.map aug) ≫ p = Pi.lift uD := by
  classical
  let Q := DerivedCategory.Q (C := A)
  have hp := (derivedCategory_termwiseProduct_isLimit A ℕ V).some
  let hfan := (Fan.isLimitMapConeEquiv Q V (limit.cone (Discrete.functor V))) hp
  let cone : Fan D := Fan.mk (Q.obj (∏ᶜ V))
    (fun n ↦ Q.map (Pi.π V n) ≫ (eL n).hom)
  let en : Discrete.functor (fun n ↦ Q.obj (V n)) ≅ Discrete.functor D :=
    Discrete.natIso (fun n ↦ eL n.as)
  let hc : IsLimit cone := (IsLimit.postcomposeHomEquiv en _).symm hfan
  let ep : Q.obj (∏ᶜ V) ≅ ∏ᶜ D :=
    hc.conePointUniqueUpToIso (productIsProduct D)
  have he (n : ℕ) : ep.hom ≫ Pi.π D n = Q.map (Pi.π V n) ≫ (eL n).hom :=
    hc.conePointUniqueUpToIso_hom_comp (productIsProduct D) ⟨n⟩
  have hs : Q.map (towerTransitionEndomorphism t) ≫ ep.hom =
      ep.hom ≫ towerTransitionEndomorphism d := by
    apply Pi.hom_ext
    intro n
    have hπ := (towerTransitionEndomorphism_eq_iff
      t (towerTransitionEndomorphism t)).mp rfl n
    have hdπ := (towerTransitionEndomorphism_eq_iff
      d (towerTransitionEndomorphism d)).mp rfl n
    simp only [Category.assoc, hdπ, Preadditive.comp_sub, he]
    rw [← Q.map_comp_assoc, hπ]
    simp only [Functor.map_sub, Functor.map_comp, Preadditive.sub_comp]
    simp only [← Category.assoc, he]
    dsimp only [Q]
    simp only [Category.assoc, hstep]
  let ec := Q.mapIso (genericCoconeIso (∏ᶜ V) (towerTransitionEndomorphism t))
  let T := Q.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle (towerTransitionEndomorphism t))
  let p : Q.obj (genericRoos (∏ᶜ V) (towerTransitionEndomorphism t)) ⟶ ∏ᶜ D :=
    ec.inv ≫ T.mor₁ ≫ ep.hom
  let δ : ∏ᶜ D ⟶ (Q.obj (genericRoos (∏ᶜ V) (towerTransitionEndomorphism t)))⟦(1 : ℤ)⟧ :=
    ep.inv ≫ T.mor₃ ≫ ec.hom⟦(1 : ℤ)⟧'
  refine ⟨p, δ, ?_, ?_⟩
  · have hT : T ∈ distTriang (DerivedCategory A) :=
      DerivedCategory.mappingCocone_triangle_distinguished _
    exact (Pretriangulated.distinguished_iff_of_iso
      (Pretriangulated.Triangle.isoMk T
        (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism d) δ)
        ec ep ep (by simp [p]) hs (by simp [δ]))).mp hT
  · apply Pi.hom_ext
    intro n
    simp only [p, Category.assoc, he, ec, Functor.mapIso_inv]
    change e.inv ≫ Q.map aug ≫
      Q.map (genericCoconeIso (∏ᶜ V) (towerTransitionEndomorphism t)).inv ≫
      Q.map (CochainComplex.mappingCocone.fst (towerTransitionEndomorphism t)) ≫
      Q.map (Pi.π V n) ≫ (eL n).hom = _
    rw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc aug, haug,
      ← Q.map_comp_assoc]
    simp only [Pi.lift_comp_π]
    rw [hunit, Iso.inv_hom_id_assoc]

/-- The specified augmented Roos model is the derived inverse limit of the canonical
reductions; its evaluations compose with the explicit completionMap to the tensor units.
The extra product instance is the usual categorical choice of product, not a hypothesis
on K, and no choice of a triangulated lift is used to define the comparison.
Source: blueprint, Roos interpretation, Stacks 08TC
(blueprint: definition-derived-adic-completeness).
Proof: on a K-flat P, ordinary tensor with B_n computes relative derived extension.
The scalar-extension counit gives the level identifications, compatibly with quotient
transitions and tensor units. Exact countable products of module sheaves identify the
product of the localized levels with the localized termwise product. The signed
interchange of the two coordinates identifies roos with Cone(1-s)[-1]. Its cone triangle
gives the asserted distinguished triangle. Its first arrow is the first-coordinate
projection, whose composite with (unit,0) is the product of the canonical units.
The coordinate formula makes the first projection of the augmentation the product
of the specified tensor units, so this identifies the actual augmented limit map. -/
theorem roos_isDerivedLimit (K : DerivedCategory (Modules l E X))
    (P : CochainComplex (Modules l E X) ℤ)
    (_hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ K)
    [HasProduct (integralLevel l E X K)] :
    ∃ (p : DerivedCategory.Q.obj (roos l E X P) ⟶ ∏ᶜ (integralLevel l E X K))
      (δ : ∏ᶜ (integralLevel l E X K) ⟶
        (DerivedCategory.Q.obj (roos l E X P))⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle (integralStep l E X K) _ p δ ∧
        completionMap l E X K P e ≫ p = Pi.lift (f := integralLevel l E X K)
          (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
            (quotient l E X n)).unit.app K) := by
  obtain ⟨eL, hstep, hunit⟩ := strictScalarRealization l E X K P _hP e
  let := modules_countableAB4Star l E X
  exact generic_roosLimit (fun n ↦ (level l E X n).obj P) (levelStep l E X P)
    P K e (integralLevel l E X K) (integralStep l E X K) (levelUnit l E X P)
    (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app K)
    (augmentation l E X P)
    (by
      have hh : augmentation l E X P ≫
          (genericCoconeIso (product l E X P) (oneSubShift l E X P)).inv ≫
          CochainComplex.mappingCocone.fst (oneSubShift l E X P) =
          unitProduct l E X P := by
        apply HomologicalComplex.hom_ext
        intro i
        change biprod.lift ((unitProduct l E X P).f i) 0 ≫
          ((genericCoconeIso (product l E X P) (oneSubShift l E X P)).inv.f i ≫
            (CochainComplex.mappingCocone.fst (oneSubShift l E X P)).f i) = _
        rw [genericCoconeIso_inv_fst_f, biprod.lift_fst]
      exact hh)
    eL hstep hunit

end

end AlgebraicGeometry.ProEtale.AdicCompletion
