/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-! # Data for the normalized finite Tate-power presentation

The existing finite-power data of the smooth-dualizing construction, extracted
without changing any declaration's name, signature or body.
Source: the ordered tensor-power construction in the smooth-dualizing corollary
(blueprint: def-sf-etale-power-presentation-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures
namespace AdicSmoothDualizing
open AlgebraicGeometry.Scheme
attribute [local irreducible] finiteEtaleTateTensorFamily

/-- Reassociation of the nonnegative etale Tate powers, with the unit at degree zero.
Source: corollary proof and the detailed coefficient-twist conventions
(blueprint: corollary-dualizing-complex-smooth-scheme--1). -/
abbrev etalePowerProduct (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates d ⊗
      finiteEtaleTateLine T P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates

/-- The underlying sheaf tensor unitor, before endpoint presentation transport.
Source: corollary, zero-power tensor normalization
(blueprint: corollary-dualizing-complex-smooth-scheme--1). -/
def etalePowerUnitor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  λ_ (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates)

/-- The zero power-step has the specified tensor-unitor data.
Source: corollary, coefficient unit at power zero
(blueprint: corollary-dualizing-complex-smooth-scheme--1).
Proof: the zero finite Tate power and the tensor unit are the same constant regular
module sheaf, obtained by sheafifying that constant presheaf. Thus the unitor has
exactly these endpoints. Heterogeneous equality fixes its data uniquely. -/
theorem existsUnique_etalePowerZero (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ∃! e : etalePowerProduct P T 0 ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates 1,
      HEq e (etalePowerUnitor P T) := by
  refine ⟨etalePowerUnitor P T, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- A subsequent sheaf tensor power is literally the preceding power tensor the line.
Source: corollary, positive tensor powers
(blueprint: corollary-dualizing-complex-smooth-scheme--1).
Proof: this is the successor clause of finiteEtaleTateTwist, with the same sheaf
monoidal structure. Its comparison is identity, so the prescribed data is unique. -/
theorem existsUnique_etalePowerPositive (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (d : ℕ) :
    ∃! e : etalePowerProduct P T (d + 1) ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates (d + 2),
      HEq e (Iso.refl (etalePowerProduct P T (d + 1))) := by
  refine ⟨Iso.refl _, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The power-step comparison is exactly the tensor unitor at zero and identity
thereafter. Its specified data is preserved by the endpoint transports.
Source: corollary proof, positive tensor powers
(blueprint: corollary-dualizing-complex-smooth-scheme--1). -/
def etalePowerStep (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (d : ℕ) → etalePowerProduct P T d ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates (d + 1)
  | 0 => (existsUnique_etalePowerZero P T).exists.choose
  | d + 1 => (existsUnique_etalePowerPositive P T d).exists.choose

/-- Every nonnegative finite Tate power is flat, including the coefficient unit.
Source: corollary proof and finite Tate descent
(blueprint: corollary-dualizing-complex-smooth-scheme--1).
Proof: the normalized root line is locally free of rank one because ell is invertible.
Its positive tensor powers remain locally free of rank one; power zero is the unit.
Tensoring with a locally free rank-one sheaf is locally the identity and hence exact. -/
theorem etalePowerFlat (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (d : ℕ) :
    ObjectProperty.flat (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates d) := by
  let e := finiteEtaleTateTensorFamily T P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) P.Coefficient
    P.diagonalExponent_annihilates hT
  have h := (e.tensorInverse (d : ℤ)).flat
  dsimp only [e] at h
  rw [finiteEtaleTateTensorFamily_obj] at h
  exact h

/-- The finite Tate sheaf placed in degree zero.
Source: the corollary's finite coefficient model
(blueprint: corollary-dualizing-complex-smooth-scheme--1). -/
abbrev etaleSingle (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates d)

/-- The existing ordered derived tensor, with its site and coefficients explicit.
Source: the corollary's ordered tensor convention
(blueprint: corollary-dualizing-complex-smooth-scheme--1). -/
abbrev etaleTensor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T

/-- The comparison family is fixed by the actual tensor map, shift comparison,
flat single-complex comparison, and sheaf-power step. HEq only transports their
endpoint presentations; it fixes the data of every factor.
Source: the corollary's normalized finite powers
(blueprint: corollary-dualizing-complex-smooth-scheme--1).
Proof: at zero use the zero-shift unitor. At the successor tensor the preceding
comparison with the shifted root line. Move the two shifts outside tensor using
derivedTensorShiftIso, use singleFunctorObjTensorIso for the flat Tate power,
then etalePowerStep and PurityFiniteSetting.frameDegreeNext. These maps have the displayed
endpoints by unfolding the definitions. Induction constructs the family. HEq fixes each factor
uniquely; induction therefore also proves uniqueness of the whole family. -/
structure EtalePowerPresentation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) where
  comparison : (d : ℕ) → P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧
  normalized :
    letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    HEq (comparison 0) (((shiftFunctorZero _ ℤ).app (P.diagonalTwistEtale T 0)).symm) ∧
      ∀ d : ℕ,
        ∃ (e₁ : P.diagonalTwistEtale T (d + 1) ≅
              ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧))
          (e₂ : ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧) ≅
              (((etaleTensor P T).obj (etaleSingle P T d)).obj
                (etaleSingle P T 1))⟦2 * (d : ℤ) + 2⟧)
          (e₃ : ((etaleTensor P T).obj (etaleSingle P T d)).obj (etaleSingle P T 1) ≅
              (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d))
          (e₄ : (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d) ≅
              etaleSingle P T (d + 1)),
          HEq e₁ ((Etale.derivedTensorRight (ModuleCat.{u + 1} P.Coefficient) T
            ((etaleSingle P T 1)⟦(2 : ℤ)⟧)).mapIso (comparison d)) ∧
          HEq e₂ (Etale.derivedTensorShiftIso (ModuleCat.{u + 1} P.Coefficient) (X := T)
            (etaleSingle P T d) (etaleSingle P T 1) (2 * (d : ℤ)) 2) ∧
          HEq e₃ (Etale.singleFunctorObjTensorIso
            (A := ModuleCat.{u + 1} P.Coefficient) (X := T)
            (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates d)
            (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates) (etalePowerFlat P T hT d)) ∧
          HEq e₄ ((DerivedCategory.singleFunctor _ 0).mapIso (etalePowerStep P T d)) ∧
          comparison (d + 1) = e₁ ≪≫ e₂ ≪≫
            (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso (e₃ ≪≫ e₄) ≪≫
            eqToIso (congrArg (fun j : ℤ ↦ (etaleSingle P T (d + 1))⟦j⟧)
              (PurityFiniteSetting.frameDegreeNext d))

/-- One normalized successor comparison, using the four prescribed factors and the degree equality.
Source: ordered finite Tate powers (blueprint: def-sf-etale-power-presentation-data). -/
def etalePowerPresentationNext (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (d : ℕ)
    (e : P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧) :
    P.diagonalTwistEtale T (d + 1) ≅ (etaleSingle P T (d + 1))⟦2 * ((d + 1 : ℕ) : ℤ)⟧ :=
  ((Etale.derivedTensorRight (ModuleCat.{u + 1} P.Coefficient) T
    ((etaleSingle P T 1)⟦(2 : ℤ)⟧)).mapIso e) ≪≫
  Etale.derivedTensorShiftIso (ModuleCat.{u + 1} P.Coefficient) (X := T)
    (etaleSingle P T d) (etaleSingle P T 1) (2 * (d : ℤ)) 2 ≪≫
  (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso
    (Etale.singleFunctorObjTensorIso
      (A := ModuleCat.{u + 1} P.Coefficient) (X := T)
      (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates d)
      (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates) (etalePowerFlat P T hT d) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (etalePowerStep P T d)) ≪≫
  eqToIso (congrArg (fun j : ℤ ↦ (etaleSingle P T (d + 1))⟦j⟧)
    (PurityFiniteSetting.frameDegreeNext d))

end AdicSmoothDualizing
end WeilConjectures
