/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationLift
import Mathlib.RingTheory.Localization.Module

/-! # Linear normalized descent through Verdier rationalization

The construction applies to any triangulated linear functor whose scalar action
extends to the localized coefficient ring. It requires no equivalence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w w' v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.NormalizedScalar

variable {R : Type w} [CommRing R] (M : Submonoid R)
  (A : Type w') [CommRing A] [Algebra R A] [IsLocalization M A]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear A D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The existing Verdier lift is linear over the localized coefficient ring.
Source: localization of modules, applied to each Hom group.
(blueprint: lem-weil-pbc-normalized-scalar-localization).

Proof: the lift preserves scalar endomorphisms for elements of R by the standard
formula on QX. Hence it is R-linear. Its Hom maps extend uniquely to A-linear
maps because both Hom groups are A-modules. The quotient's A-action restricts
to its R-action by the defining scalar normalization. -/
theorem lift_linear (H : C ⥤ D) [H.CommShift ℤ] [H.IsTriangulated]
    (hH : ∀ (r : R) (X : C), H.map (r • 𝟙 X) = algebraMap R A r • 𝟙 (H.obj X)) :
    (CategoryTheory.Rationalization.lift M A H hH).Linear A := by
  let : Linear R D :=
    { homModule := fun X Y ↦ Module.compHom (X ⟶ Y) (algebraMap R A)
      smul_comp := fun X Y Z r f g ↦ Linear.smul_comp X Y Z (algebraMap R A r) f g
      comp_smul := fun X Y Z f r g ↦ Linear.comp_smul X Y Z f (algebraMap R A r) g }
  have (X Y : D) : IsScalarTower R A (X ⟶ Y) :=
    ⟨by
      intro r a f
      change (r • a) • f = (algebraMap R A r) • (a • f)
      rw [Algebra.smul_def, mul_smul]⟩
  let J := CategoryTheory.Rationalization.lift M A H hH
  have : J.Linear R := (CategoryTheory.Functor.linear_iff R J).2 fun X r ↦ by
    rw [CategoryTheory.Rationalization.lift_map_smul_id]
    exact algebraMap_smul A r (𝟙 (J.obj X))
  have (X Y : CategoryTheory.Rationalization M C) : IsScalarTower R A (X ⟶ Y) := by
    constructor
    intro r a f
    rw [Algebra.smul_def, mul_smul,
      CategoryTheory.Rationalization.algebraMap_smul]
  exact ⟨fun {X Y} f a ↦
    ((J.mapLinearMap R).extendScalarsOfIsLocalization M A).map_smul a f⟩

/-- An additive linear triangulated forward lift with a shift-compatible comparison
and its scalar naturality equation.
Source: Verdier localization and scalar localization of Hom modules.
(blueprint: lem-weil-pbc-normalized-scalar-localization). -/
def ForwardFunctorData (H : C ⥤ D) [H.CommShift ℤ] : Prop :=
  ∃ (J : CategoryTheory.Rationalization M C ⥤ D) (_ : J.Additive)
    (_ : J.Linear A) (_ : J.CommShift ℤ)
    (e : CategoryTheory.Rationalization.Q M C ⋙ J ≅ H),
    NatTrans.CommShift e.hom ℤ ∧ J.IsTriangulated ∧
    ∀ (X Y : C) (f : X ⟶ Y) (a : A),
      J.map (a • (CategoryTheory.Rationalization.Q M C).map f) ≫ e.hom.app Y =
        e.hom.app X ≫ (a • H.map f)

/-- A normalized forward functor through the ordinary Verdier rationalization.
Source: Verdier localization and scalar localization of Hom modules.
(blueprint: lem-weil-pbc-normalized-scalar-localization).

Proof: use the existing triangulated Verdier lift, not an inverse of an asserted
realization equivalence. Its standard comparison commutes with every integer
shift. The previous lemma supplies A-linearity. Naturality of that same comparison,
multiplied by any a in A, gives the fraction equation, including a=1 and a=0. -/
theorem forward_exists (H : C ⥤ D) [H.CommShift ℤ] [H.IsTriangulated]
    (hH : ∀ (r : R) (X : C), H.map (r • 𝟙 X) = algebraMap R A r • 𝟙 (H.obj X)) :
    ∃ (J : CategoryTheory.Rationalization M C ⥤ D) (_ : J.Additive)
      (_ : J.Linear A) (_ : J.CommShift ℤ)
      (e : CategoryTheory.Rationalization.Q M C ⋙ J ≅ H),
      NatTrans.CommShift e.hom ℤ ∧ J.IsTriangulated ∧
      ∀ (X Y : C) (f : X ⟶ Y) (a : A),
        J.map (a • (CategoryTheory.Rationalization.Q M C).map f) ≫ e.hom.app Y =
          e.hom.app X ≫ (a • H.map f) := by
  let J := CategoryTheory.Rationalization.lift M A H hH
  have : J.Linear A := lift_linear M A H hH
  refine ⟨J, inferInstance, inferInstance, inferInstance,
    CategoryTheory.Rationalization.liftFac M A H hH, inferInstance, inferInstance, ?_⟩
  intro X Y f a
  rw [J.map_smul]
  simpa only [CategoryTheory.Functor.comp_map, Linear.smul_comp, Linear.comp_smul] using
    congrArg (fun g ↦ a • g)
      ((CategoryTheory.Rationalization.liftFac M A H hH).hom.naturality f)

end WeilConjectures.NormalizedScalar
