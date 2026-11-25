/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteScalarPullOrdinary
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Section normalization of scalar restriction and direct image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem whisker_equality_sections
    {C D B : Type*} [Category C] [Category D] [Category B]
    {J : GrothendieckTopology B} {R : Sheaf J RingCat.{u + 1}}
    {F G : C ⥤ D} (h : F = G) (H : D ⥤ SheafOfModules.{u + 1} R)
    {T : C ⥤ SheafOfModules.{u + 1} R} (e : G ⋙ H ≅ T)
    (he : ∀ (N : C) (V : Bᵒᵖ) (x : ((G ⋙ H).obj N).val.obj V),
      HEq (((e.hom.app N).val.app V) x) x)
    (N : C) (V : Bᵒᵖ) (x : ((F ⋙ H).obj N).val.obj V) :
    HEq ((((Functor.isoWhiskerRight (eqToIso h) H ≪≫ e).hom.app N).val.app V) x) x := by
  subst G
  change HEq (((H.map (𝟙 _) ≫ e.hom.app N).val.app V) x) x
  rw [H.map_id, Category.id_comp]
  exact he N V x

/-- The finite scalar/direct-image comparison is identity on underlying sections.
Source: Stacks Tag 0D6E
(blueprint: lem-sf-finite-scalar-restriction-direct-sections).
Proof: the ringed restriction/direct-image factor is identity on sections by its
normalization. The finite direct-image equality contributes only an equality
transport, which is heterogeneously identity by equality induction. -/
theorem finiteScalarRestrictionDirect_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : normalizedDVRModules l E X n) (V : Y.ProEt)
    (x : N.val.obj (op ((proEtaleBaseChange f).obj V))) :
    HEq (((finiteScalarRestrictionDirect l E f n).hom.app N).val.app (op V) x) x := by
  unfold finiteScalarRestrictionDirect
  have hd := (proEtaleRingRestrictionDirectImage_existsUnique f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map Y)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map X)
      ((PurCompactSupport.completed l E).pull f)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull f)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).square f)).choose_spec.1
  refine whisker_equality_sections
    (PurCompactSupport.finiteDirectImage_eq l E n f).symm
    (pbcRestrict
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map Y))
    (proEtaleRingRestrictionDirectImage f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map Y)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).map X)
      ((PurCompactSupport.completed l E).pull f)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull f)
      ((PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)).square f)) ?_ N (op V) x
  intro N W x
  exact heq_of_eq (hd N W x)

end WeilConjectures.IntegralSystemRealization
