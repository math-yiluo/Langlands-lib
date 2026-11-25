/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction

/-! # Coordinates for the finite tensor representative square

Source: Stacks 07A4 and 00YV.
(blueprint: def-pur-finite-pullback-tensor-representative-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.FinitePullbackTensorRep
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing abelian instance in the finite coefficient presentation.
Source: Stacks 04JC (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
local instance modules_abelian (W : Scheme.{u}) (n : ℕ) :
    Abelian (normalizedDVRModules l E W n) :=
  SheafOfModules.instAbelian (integralCoefficientSheaf l E W n)

/-- The existing standard derived category in the fixed universe.
Source: Stacks 04JC (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
local instance modules_derived (W : Scheme.{u}) (n : ℕ) :
    HasDerivedCategory.{u + 2} (normalizedDVRModules l E W n) :=
  HasDerivedCategory.standard _

attribute [local implicit_reducible] modules_abelian modules_derived

/-- The standard derived quotient at the fixed finite module category and universe.
Source: Stacks 05RU (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
abbrev quotient (W : Scheme.{u}) (n : ℕ) :
    CochainComplex (normalizedDVRModules l E W n) ℤ ⥤
      proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1)) :=
  DerivedCategory.Q

/-- The ordinary, identified-coefficient module pullback used in the construction.
Source: Stacks 03EL (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
abbrev ordinary {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
  proEtaleRingModulePullback f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)

/-- Additivity of the existing ordinary pullback.
Source: Stacks 04JC (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
local instance ordinary_additive {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (ordinary l E f n).Additive :=
  proEtaleRingModulePullback_additive f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)

/-- Left exactness of the existing ordinary pullback.
Source: Stacks 04JC (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
local instance ordinary_limits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Limits.PreservesFiniteLimits (ordinary l E f n) :=
  proEtaleRingModulePullback_preservesFiniteLimits f
    (integralCoefficientCommRingSheaf l E Y n) (integralCoefficientCommRingSheaf l E X n)
    (pullbackTensorCoefficientIso l E f n)

/-- Right exactness of the existing ordinary pullback.
Source: Stacks 04JC (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
local instance ordinary_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Limits.PreservesFiniteColimits (ordinary l E f n) :=
  proEtaleRingModulePullback_preservesFiniteColimits f
    (integralCoefficientCommRingSheaf l E Y n) (integralCoefficientCommRingSheaf l E X n)
    (pullbackTensorCoefficientIso l E f n)

/-- The same pullback on complexes.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def pull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤
      CochainComplex (normalizedDVRModules l E X n) ℤ :=
  (ordinary l E f n).mapHomologicalComplex (.up ℤ)

/-- The uncurried total-tensor functor, including its simultaneous map on both inputs.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
def totalTensor (W : Scheme.{u}) (n : ℕ) :
    CochainComplex (normalizedDVRModules l E W n) ℤ ×
      CochainComplex (normalizedDVRModules l E W n) ℤ ⥤
        CochainComplex (normalizedDVRModules l E W n) ℤ :=
  Functor.uncurry.obj ((proEtaleOrdinaryTensor W
    (integralCoefficientCommRingSheaf l E W n)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))

/-- The object of that same signed direct-sum total tensor functor.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
abbrev tensor (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E W n) ℤ) :=
  (totalTensor l E W n).obj (P, Q)

/-- The fixed tensor-model representative comparison followed by its recorded identification.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def representative (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) P)
    (hQ : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) Q) :
    (quotient l E W n).obj (tensor l E W n P Q) ≅
      (finiteIntrinsicDerivedTensor l E W n).obj
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  (pullbackTensorFiniteModel l E W n).representative.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≪≫
    (pullbackTensorFiniteModelIso l E W n).app
      ((quotient l E W n).obj P, (quotient l E W n).obj Q)

/-- The published ordinary derived pullback, with its original instance choices.
Source: Stacks 0735 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
abbrev derived {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  proEtaleRingDerivedPullback f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)

/-- The published computation isomorphism for the ordinary derived pullback.
Source: Stacks 0735 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
abbrev ordinaryFactors {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  proEtaleRingDerivedPullbackFactors f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)

/-- The derived realization with the module categories and exactness instances fixed.
Source: Stacks 00YV (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
def realization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    derived l E f n ≅ finiteDerivedPullback l E n f :=
  @Functor.mapDerivedCategoryNatIso
    (normalizedDVRModules l E Y n) (normalizedDVRModules l E X n) _ _
    (SheafOfModules.instAbelian (integralCoefficientSheaf l E Y n))
    (SheafOfModules.instAbelian (integralCoefficientSheaf l E X n)) _ _
    (ordinary l E f n) (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (ordinary_additive l E f n)
    (sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f)
    (ordinary_limits l E f n) (ordinary_colimits l E f n)
    (sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f)
    (sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f)
    (pullbackTensorFiniteRealization l E f n)

/-- Exact pullback computed in the ordinary model, using the prescribed realization.
Source: Stacks 00YV (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def factors {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    DerivedCategory.Q ⋙ finiteDerivedPullback l E n f ≅
      pull l E f n ⋙ DerivedCategory.Q := by
  unfold pull
  exact isoWhiskerLeft DerivedCategory.Q
      (realization l E f n).symm ≪≫
    (ordinaryFactors l E f n)

/-- The forward total-tensor comparison in the ordinary presentation.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    (pull l E f n).obj (tensor l E Y n P Q) ⟶
      tensor l E X n ((pull l E f n).obj P) ((pull l E f n).obj Q) := by
  unfold pull
  exact (proEtaleTensorPullbackTotalIso f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n) P Q).inv

/-- The ordinary compositor induced by the fixed, unit-normalized realizations.
Source: Stacks 00YV (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
def moduleComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ) :
    ordinary l E (h ≫ f) n ≅ ordinary l E f n ⋙ ordinary l E h n :=
  pullbackTensorFiniteRealization l E (h ≫ f) n ≪≫
    sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) h f ≪≫
    isoWhiskerRight (pullbackTensorFiniteRealization l E f n).symm
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) h) ≪≫
    isoWhiskerLeft (ordinary l E f n) (pullbackTensorFiniteRealization l E h n).symm

/-- Its degreewise action on complexes.
Source: Stacks 00YV (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def complexComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ) :
    pull l E (h ≫ f) n ≅ pull l E f n ⋙ pull l E h n :=
  by
    unfold pull
    exact (mapHomologicalComplexCompIso (moduleComp l E f h n).symm (.up ℤ)).symm

end WeilConjectures.FinitePullbackTensorRep
