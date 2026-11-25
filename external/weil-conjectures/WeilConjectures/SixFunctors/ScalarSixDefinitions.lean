/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Coefficient change, inverse image and locally closed extension

(1)--(3);
Stacks Project, Tags 0G7E, 0D6D, 09AA, 09BM, 09BN and 09AH.
(blueprint: proposition-six-operations-change-coefficients).

The witnesses below include equations, not just existence of unrelated isomorphisms.
Pullback is exact, so its unbounded derived functor is written as its termwise
localization. Scalar extension is the ordinary, uncompleted total left derived functor.
The locally closed functors are the published factorization-independent extensions,
transported through the fixed internal/sectionwise module equivalence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option linter.unusedVariables false
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Bundled parameters for commutative condensed coefficients.
Source: blueprint coefficient change (blueprint: proposition-six-operations-change-coefficients). -/
abbrev ScalarSixRing := CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

/-- Expose the left functor already specified by an adjunction. This avoids rebuilding
its K-flat tensor instances when specializing the published scalar adjunction.
Source: blueprint coefficient change (blueprint: proposition-six-operations-change-coefficients). -/
abbrev scalarSixAdjunctionLeft {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}
    (_adj : F ⊣ G) : C ⥤ D := F

/-- Additivity of the unchanged forward module equivalence.
Source: internal module operations transport
(auxiliary; not a blueprint node). -/
instance scalarSixEquivalenceAdditive (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    (ModuleRingedComparison.equivalence Λ.X X).functor.Additive :=
  ((InternalModuleOperations.internal_module_operations_transport Λ.X).1 X).1

/-- Additivity of the unchanged inverse module equivalence.
Source: internal module operations transport
(auxiliary; not a blueprint node). -/
instance scalarSixEquivalenceInverseAdditive (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    (ModuleRingedComparison.equivalence Λ.X X).inverse.Additive :=
  ((InternalModuleOperations.internal_module_operations_transport Λ.X).1 X).2.1

/-- Ordinary unbounded derived scalar extension, using the published coefficient map
and the left functor of its derived adjunction (definitionally L(Ext)).
Source: blueprint clause (1) (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixChange {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ'.X X) :=
  scalarSixAdjunctionLeft (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))

/-- Exact inverse image applied termwise. This is canonically the total derived pullback.
Source: blueprint clause (1) (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixPull (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  D((f)^*⟦Λ.X⟧)

/-- The canonical non-flat pullback comparison, the scalar-adjunction mate of the
identity-on-underlying-sheaves restriction comparison `derivedComapUpperStarIso`.
Source: blueprint proof (1), steps 1--2 (blueprint:
proposition-six-operations-change-coefficients). -/
def scalarSixPullHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f ⋙ scalarSixChange a X ⟶
      scalarSixChange a Y ⋙ scalarSixPull Λ' f :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)

/-- The ordinary, exact inverse-image compositor, localized termwise.
Source: blueprint clause (1) (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixPullComp (Λ : ScalarSixRing.{u}) {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ W) :
    scalarSixPull Λ (f ≫ g) ≅ scalarSixPull Λ g ⋙ scalarSixPull Λ f :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Λ.X f g) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The tensor associator, fixed as the conjugate of transitivity of exact restriction.
On K-flat representatives its formula is c tensor (b tensor m) to cb tensor m.
Source: blueprint proof (3), step 7 (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixTower {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    scalarSixChange a X ⋙ scalarSixChange b X ≅ scalarSixChange (a ≫ b) X :=
  (conjugateIsoEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X))
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X)))).symm
    (Functor.mapDerivedCategoryNatIso
        (Mod.comapCongr (coefficientMap_comp (Λ := Λ.X) (Λ' := Λ'.X) (Λ'' := Λ''.X)
          a.hom.hom b.hom.hom X)) ≪≫
      Functor.mapDerivedCategoryNatIso (Mod.comapComp _ _ ) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)

/-- The fixed section-ring model of a condensed coefficient object.
Source: blueprint proof step 1 (blueprint: proposition-six-operations-change-coefficients). -/
abbrev scalarSixSectionRing (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :=
  ModuleRingedComparison.ring Λ.X X

/-- The fixed exact equivalence on unbounded derived module categories, forward direction.
Source: blueprint proof step 1 (blueprint: proposition-six-operations-change-coefficients). -/
abbrev scalarSixForward (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) :=
  (ModuleRingedComparison.equivalence Λ.X X).functor.mapDerivedCategory

/-- The inverse of the same equivalence, applied termwise.
Source: blueprint proof step 1 (blueprint: proposition-six-operations-change-coefficients). -/
abbrev scalarSixBackward (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) :=
  (ModuleRingedComparison.equivalence Λ.X X).inverse.mapDerivedCategory

/-- Noetherian coefficient object for a finite-type scheme over a field. The two
Noetherian proofs follow from finite type and quasi-compactness, with no added hypotheses.
Source: blueprint proof (2), step 3 (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixCoefficients (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    LocallyClosedCoefficients.{u} where
  scheme := X.left
  locallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
  compact := QuasiCompact.compactSpace_of_compactSpace X.hom
  ring := scalarSixSectionRing Λ X.left

/-- Canonical coefficient identifications in the two module presentations. The adjunct
normalization fixes every section, hence determines the ring isomorphism uniquely.
Source: blueprint proof steps 1 and 3 (blueprint:
proposition-six-operations-change-coefficients). -/
structure ScalarSixGeometry where
  coefficient : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (scalarSixSectionRing Λ Y) ≅ scalarSixSectionRing Λ X
  coefficientNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (scalarSixSectionRing Λ Y).obj.obj V),
    ((proEtaleRingDirectImageMap f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (coefficient Λ f)).hom.app V).hom r =
      ((condensedPushforwardHom Λ.X f).hom.app V).hom r

  push : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    lowerStar Λ.X f ⋙ (ModuleRingedComparison.equivalence Λ.X Y).functor ≅
      (ModuleRingedComparison.equivalence Λ.X X).functor ⋙
        proEtaleRingModuleDirectImage f (scalarSixSectionRing Λ Y)
          (scalarSixSectionRing Λ X) (coefficient Λ f)
  pushNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleRingedComparison.internalModules Λ.X X) (V : Y.ProEtᵒᵖ)
    (m : ((lowerStar Λ.X f).obj M).X.obj.obj V),
    ((push Λ f).hom.app M).val.app V m = m
  pull : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    upperStar Λ.X f ⋙ (ModuleRingedComparison.equivalence Λ.X X).functor ≅
      (ModuleRingedComparison.equivalence Λ.X Y).functor ⋙
        proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
          (scalarSixSectionRing Λ X) (coefficient Λ f)
  pullNormalization : ∀ (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (upperStarLowerStarAdjunction Λ.X f)
      (proEtaleRingModuleAdjunction f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (coefficient Λ f))
      (.mk _ _ _ _ (pull Λ f).inv)) = (push Λ f).hom

/-- The locally closed coefficient arrow with its canonically normalized coefficient map.
Source: blueprint clause (2) (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixImmersion (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    LocallyClosedCoefficientImmersion (scalarSixCoefficients Λ S) (scalarSixCoefficients Λ X)
    where
  hom := f.left
  immersion := inferInstance
  coefficient := G.coefficient Λ f.left

/-- Expose immersion stability in the over-category at its actual underlying map.
Source: blueprint clause (2) (blueprint: proposition-six-operations-change-coefficients). -/
instance scalarSixOverCompImmersion {k : Type u} [Field k]
    {T S X : Over (Spec (.of k))} (g : T ⟶ S) (f : S ⟶ X)
    [IsImmersion g.left] [IsImmersion f.left] : IsImmersion (g ≫ f).left :=
  inferInstanceAs (IsImmersion (g.left ≫ f.left))

/-- Expose the published extension's additive structure without unfolding the arrow.
Source: blueprint clause (2) (blueprint: proposition-six-operations-change-coefficients). -/
instance scalarSixExtensionAdditive (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    (E.extension a).Additive := E.additive a

/-- Expose the published extension's exactness, finite-limit half.
Source: blueprint clause (2) (blueprint: proposition-six-operations-change-coefficients). -/
instance scalarSixExtensionFiniteLimits (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    PreservesFiniteLimits (E.extension a) := E.finiteLimits a

/-- Expose the published extension's exactness, finite-colimit half.
Source: blueprint clause (2) (blueprint: proposition-six-operations-change-coefficients). -/
instance scalarSixExtensionFiniteColimits (E : LocallyClosedExtensionData.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    PreservesFiniteColimits (E.extension a) := E.finiteColimits a

/-- The actual extension by zero on internal-module derived categories, transported
from the published exact locally closed extension. No choice of a new extension functor.
Source: blueprint clause (2) (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixExtension (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (Λ : ScalarSixRing.{u}) {k : Type u} [Field k] {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left) :=
  scalarSixForward Λ S.left ⋙ E.derived (scalarSixImmersion G Λ f) ⋙
    scalarSixBackward Λ X.left

/-- The fixed equivalence on the two ordinary unbounded derived categories.
Source: blueprint proof step 1 (blueprint: proposition-six-operations-change-coefficients). -/
abbrev scalarSixEquivalence (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ≌
      DerivedCategory (proEtaleRingModules X (scalarSixSectionRing Λ X)) :=
  (ModuleRingedComparison.equivalence Λ.X X).mapDerivedCategory

/-- The localized, adjunction-normalized inverse-image square.
Source: blueprint proof steps 1--2 (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixPullSection (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f ⋙ scalarSixForward Λ X ≅ scalarSixForward Λ Y ⋙
      (proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ f)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (G.pull Λ f) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Clause (1), with its canonical normalization, and the inverse-image square of (3).
All coefficient maps are allowed, including non-flat maps.
Source: blueprint clauses (1), (3) (blueprint: proposition-six-operations-change-coefficients). -/
structure ScalarSixPullbackData where
  theta : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    scalarSixPull Λ f ⋙ scalarSixChange a X ≅ scalarSixChange a Y ⋙ scalarSixPull Λ' f
  thetaNormalization : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y), (theta a f).hom = scalarSixPullHom a f
  composition : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)),
    (theta a (f ≫ g)).hom.app K ≫
        (scalarSixPullComp Λ' f g).hom.app ((scalarSixChange a W).obj K) =
      (scalarSixChange a X).map ((scalarSixPullComp Λ f g).hom.app K) ≫
        (theta a f).hom.app ((scalarSixPull Λ g).obj K) ≫
          (scalarSixPull Λ' f).map ((theta a g).hom.app K)
  tower : ∀ {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
    (scalarSixTower a b X).hom.app ((scalarSixPull Λ f).obj K) ≫
        (theta (a ≫ b) f).hom.app K =
      (scalarSixChange b X).map ((theta a f).hom.app K) ≫
        (theta b f).hom.app ((scalarSixChange a Y).obj K) ≫
          (scalarSixPull Λ'' f).map ((scalarSixTower a b Y).hom.app K)

/-- Cancel the fixed presentation equivalence in an open extension comparison.
Source: functorial transport (auxiliary; not a blueprint node). -/
def scalarSixTransportOpen
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (e' : B ≌ D) (J : A ⥤ B) (F : C ⥤ D)
    (d : J ⋙ e'.functor ≅ e.functor ⋙ F) :
    e.functor ⋙ F ⋙ e'.inverse ≅ J :=
  Functor.isoWhiskerRight d.symm e'.inverse ≪≫
    Functor.isoWhiskerLeft J e'.unitIso.symm ≪≫ Functor.rightUnitor _

/-- Transport an extension's restriction through the fixed equivalences.
Source: functorial transport (auxiliary; not a blueprint node). -/
def scalarSixTransportRestriction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (e' : B ≌ D) (F : C ⥤ D) (R : B ⥤ A) (Q : D ⥤ C)
    (d : R ⋙ e.functor ≅ e'.functor ⋙ Q) (rho : F ⋙ Q ≅ 𝟭 C) :
    (e.functor ⋙ F ⋙ e'.inverse) ⋙ R ≅ 𝟭 A :=
  (Functor.rightUnitor ((e.functor ⋙ F ⋙ e'.inverse) ⋙ R)).symm ≪≫
    Functor.isoWhiskerLeft ((e.functor ⋙ F ⋙ e'.inverse) ⋙ R) e.unitIso ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (e.functor ⋙ F ⋙ e'.inverse) d ≪≫
        Functor.isoWhiskerLeft (e.functor ⋙ F)
          (Functor.isoWhiskerRight e'.counitIso Q) ≪≫
        Functor.isoWhiskerLeft e.functor rho ≪≫ Functor.rightUnitor _)
      e.inverse ≪≫ e.unitIso.symm

/-- Transport a compositor and cancel the middle presentation equivalence.
Source: functorial transport (auxiliary; not a blueprint node). -/
def scalarSixTransportComposition
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    (eA : A ≌ A') (eB : B ≌ B') (eC : C ≌ C')
    (F : B' ⥤ C') (G : A' ⥤ B') (H : A' ⥤ C') (gamma : G ⋙ F ≅ H) :
    (eA.functor ⋙ G ⋙ eB.inverse) ⋙ (eB.functor ⋙ F ⋙ eC.inverse) ≅
      eA.functor ⋙ H ⋙ eC.inverse :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (eA.functor ⋙ G)
      (Functor.isoWhiskerRight eB.counitIso F)) eC.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft eA.functor gamma) eC.inverse

section Standing

variable {k : Type u} [Field k]

/-- The ordinary open comparison and its adjunction-mate normalization. These are
witnesses in the assertion, not an assumed replacement extension functor.
Source: blueprint proof step 4 (blueprint: proposition-six-operations-change-coefficients). -/
structure ScalarSixOpenComparison (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] where
  comparison : ∀ (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left],
    openImmersionLowerShriek Λ.X j.left ⋙
        (ModuleRingedComparison.equivalence Λ.X X.left).functor ≅
      (ModuleRingedComparison.equivalence Λ.X S.left).functor ⋙
        E.extension (scalarSixImmersion G Λ j)
  normalization : ∀ (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left],
    (mateEquiv (openImmersionLowerShriekUpperStarAdjunction Λ.X j.left)
      (E.openAdjunction (scalarSixImmersion G Λ j)
        (inferInstanceAs (IsOpenImmersion j.left)))
      (.mk _ _ _ _ (comparison Λ j).inv)) = (G.pull Λ j.left).hom

variable (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
  (G : ScalarSixGeometry.{u})

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport of the normalized open comparison, using only localization and the
fixed equivalence unit. Source: blueprint proof step 4
(blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixOpenIso (O : ScalarSixOpenComparison E G k) (Λ : ScalarSixRing.{u})
    {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left] :
    scalarSixExtension E G Λ j ≅ D(openImmersionLowerShriek Λ.X j.left) :=
  letI := E.additive (scalarSixImmersion G Λ j)
  letI := E.finiteLimits (scalarSixImmersion G Λ j)
  letI := E.finiteColimits (scalarSixImmersion G Λ j)
  let d : D(openImmersionLowerShriek Λ.X j.left) ⋙ scalarSixForward Λ X.left ≅
      scalarSixForward Λ S.left ⋙ E.derived (scalarSixImmersion G Λ j) :=
    Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ.X j.left)
      (ModuleRingedComparison.equivalence Λ.X X.left).functor ≪≫
        Functor.mapDerivedCategoryNatIso (O.comparison Λ j) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (ModuleRingedComparison.equivalence Λ.X S.left).functor
            (E.extension (scalarSixImmersion G Λ j))).symm
  scalarSixTransportOpen (scalarSixEquivalence Λ S.left) (scalarSixEquivalence Λ X.left)
    D(openImmersionLowerShriek Λ.X j.left) (E.derived (scalarSixImmersion G Λ j)) d

/-- Restriction of the actual extension, transported from the published derived
restriction and the normalized inverse-image square.
Source: blueprint proof step 6 (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixRestriction (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    scalarSixExtension E G Λ f ⋙ scalarSixPull Λ f.left ≅ 𝟭 _ :=
  scalarSixTransportRestriction
    (scalarSixEquivalence Λ S.left) (scalarSixEquivalence Λ X.left)
    (E.derived (scalarSixImmersion G Λ f)) (scalarSixPull Λ f.left)
    (scalarSixImmersion G Λ f).pull.mapDerivedCategory (scalarSixPullSection G Λ f.left)
    (D.restriction (scalarSixImmersion G Λ f))

/-- The extension compositor is the published gamma, with the middle equivalence
cancelled. The equality argument identifies exactly the canonical coefficient arrows.
Source: blueprint proof step 6 (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixExtensionComp (Λ : ScalarSixRing.{u}) {T S X : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
    (h : scalarSixImmersion G Λ (g ≫ f) =
      (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g)) :
    scalarSixExtension E G Λ g ⋙ scalarSixExtension E G Λ f ≅
      scalarSixExtension E G Λ (g ≫ f) :=
  scalarSixTransportComposition
    (scalarSixEquivalence Λ T.left) (scalarSixEquivalence Λ S.left)
    (scalarSixEquivalence Λ X.left)
    (E.derived (scalarSixImmersion G Λ f)) (E.derived (scalarSixImmersion G Λ g))
    (E.derived (scalarSixImmersion G Λ (g ≫ f)))
    (D.gamma (scalarSixImmersion G Λ f) (scalarSixImmersion G Λ g) ≪≫
      eqToIso (congrArg E.derived h.symm))

/-- Exact closed direct image, applied termwise and transported through the fixed
module equivalence. Exactness comes from the published closed comparison, rather than
from a new assumption on the coefficient ring.
Source: blueprint proof step 5 (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixClosedPush (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left] :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left) :=
  letI := E.additive (scalarSixImmersion G Λ i)
  letI := E.finiteLimits (scalarSixImmersion G Λ i)
  letI := E.finiteColimits (scalarSixImmersion G Λ i)
  let e := E.closedComparison (scalarSixImmersion G Λ i)
    (inferInstanceAs (IsClosedImmersion i.left))
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  scalarSixForward Λ S.left ⋙ (scalarSixImmersion G Λ i).push.mapDerivedCategory ⋙
    scalarSixBackward Λ X.left

/-- The closed specialization is the localization of the actual closed direct-image
comparison supplied by the coherence node.
Source: blueprint clause (2) (blueprint: proposition-six-operations-change-coefficients). -/
def scalarSixClosedIso (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left] :
    scalarSixExtension E G Λ i ≅ scalarSixClosedPush E G Λ i :=
  letI := E.additive (scalarSixImmersion G Λ i)
  letI := E.finiteLimits (scalarSixImmersion G Λ i)
  letI := E.finiteColimits (scalarSixImmersion G Λ i)
  let e := E.closedComparison (scalarSixImmersion G Λ i)
    (inferInstanceAs (IsClosedImmersion i.left))
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft (scalarSixForward Λ S.left)
    (Functor.mapDerivedCategoryNatIso
      (E.closedComparison (scalarSixImmersion G Λ i)
        (inferInstanceAs (IsClosedImmersion i.left))))) (scalarSixBackward Λ X.left)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The published open scalar comparison at the fixed scalar-change functors.
This is exactly the existing comparison, with its functor types checked once.
Source: blueprint open comparison
(auxiliary; not a blueprint node). -/
def scalarSixOpenScalarIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S X : Scheme.{u}} (j : S ⟶ X) [IsOpenImmersion j] :
    D(openImmersionLowerShriek Λ.X j) ⋙ scalarSixChange a X ≅
      scalarSixChange a S ⋙ D(openImmersionLowerShriek Λ'.X j) :=
  derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] scalarSixExtension scalarSixChange scalarSixPull
  scalarSixRestriction scalarSixExtensionComp scalarSixOpenIso scalarSixClosedIso
  scalarSixClosedPush scalarSixTower

/-- The type of single-arrow immersion comparisons, without an existence assertion.
Source: blueprint clause (2) (auxiliary; not a blueprint node). -/
abbrev ScalarSixImmersionComparisons (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) [IsImmersion f.left],
      scalarSixExtension E G Λ f ⋙ scalarSixChange a X.left ≅
        scalarSixChange a S.left ⋙ scalarSixExtension E G Λ' f

/-- The type of geometric coefficient-composition identities.
Source: blueprint clause (2) (auxiliary; not a blueprint node). -/
abbrev ScalarSixImmersionIdentifiers (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] :=
  ∀ (Λ : ScalarSixRing.{u}) {T S X : Over (Spec (.of k))}
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left],
      scalarSixImmersion G Λ (g ≫ f) =
        (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g)

/-- An unchanged comparison equation, named to keep structure projections compact.
Source: blueprint clauses (2)--(3)
(auxiliary; not a blueprint node). -/
def ScalarSixImmersionNormalization (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k)
    (beta : ScalarSixImmersionComparisons E G k) : Prop :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) [IsImmersion f.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
      (scalarSixPull Λ' f.left).map ((beta a f).hom.app M) ≫
          (scalarSixRestriction E D G Λ' f).hom.app ((scalarSixChange a S.left).obj M) =
        (C.theta a f.left).inv.app ((scalarSixExtension E G Λ f).obj M) ≫
          (scalarSixChange a S.left).map ((scalarSixRestriction E D G Λ f).hom.app M)

/-- An unchanged comparison equation, named to keep structure projections compact.
Source: blueprint clauses (2)--(3)
(auxiliary; not a blueprint node). -/
def ScalarSixImmersionComposition (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k)
    (beta : ScalarSixImmersionComparisons E G k)
    (compositionIdentifier : ScalarSixImmersionIdentifiers G k) : Prop :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {T S X : Over (Spec (.of k))}
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X T.left)),
      (scalarSixChange a X.left).map
          ((scalarSixExtensionComp E D G Λ (k := k) (T := T) (S := S) (X := X) f g
            (compositionIdentifier Λ (T := T) (S := S) (X := X) f g)).hom.app M) ≫
          (beta a (g ≫ f)).hom.app M =
        (beta a f).hom.app ((scalarSixExtension E G Λ g).obj M) ≫
          (scalarSixExtension E G Λ' f).map ((beta a g).hom.app M) ≫
            (scalarSixExtensionComp E D G Λ' (k := k) (T := T) (S := S) (X := X) f g
              (compositionIdentifier Λ' (T := T) (S := S) (X := X) f g)).hom.app
              ((scalarSixChange a T.left).obj M)

/-- An unchanged comparison equation, named to keep structure projections compact.
Source: blueprint clauses (2)--(3)
(auxiliary; not a blueprint node). -/
def ScalarSixImmersionOpenValue (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k)
    (beta : ScalarSixImmersionComparisons E G k) : Prop :=
  ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (j : S ⟶ X) [IsOpenImmersion j.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
      (scalarSixChange a X.left).map ((scalarSixOpenIso E G O Λ j).hom.app M) ≫
          (scalarSixOpenScalarIso a j.left).hom.app M =
        (beta a j).hom.app M ≫
          (scalarSixOpenIso E G O Λ' j).hom.app ((scalarSixChange a S.left).obj M)

attribute [local irreducible] ScalarSixImmersionNormalization
  ScalarSixImmersionComposition ScalarSixImmersionOpenValue

/-- An unchanged extension-comparison clause with its witnesses kept explicit.
Source: blueprint clauses (2)--(3)
(auxiliary; not a blueprint node). -/
def ScalarSixImmersionTower (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (k : Type u) [Field k] (beta : ScalarSixImmersionComparisons E G k) : Prop :=
  ∀ {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) [IsImmersion f.left]
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)),
      (scalarSixTower a b X.left).hom.app ((scalarSixExtension E G Λ f).obj M) ≫
          (beta (a ≫ b) f).hom.app M =
        (scalarSixChange b X.left).map ((beta a f).hom.app M) ≫
          (beta b f).hom.app ((scalarSixChange a S.left).obj M) ≫
            (scalarSixExtension E G Λ'' f).map ((scalarSixTower a b S.left).hom.app M)

attribute [local irreducible] ScalarSixImmersionTower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end Standing

end AlgebraicGeometry.ProEtale.CondensedRing
