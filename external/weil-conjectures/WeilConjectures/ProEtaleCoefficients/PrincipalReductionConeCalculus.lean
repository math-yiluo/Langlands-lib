/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.ProEtaleCoefficients.PrincipalConeTensorNormalization
import WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Strict principal reduction and its compatible cone comparisons

Source: blueprint main-20261015, chap-The-pro-etale-site,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md`,
Cones paragraph; Stacks Tag 014E, definition-cone
(blueprint: lem-pe-principal-reduction-cone-calculus).

Positive level n+1 is indexed by n : ℕ, as in AdicCompletion. Cone coordinates
are ordered target, shifted source. The comparison is one natural family,
including its quotient transitions and its specified reduction coaugmentations.
-/

@[expose] public noncomputable section
set_option linter.privateModule false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u vC uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace PrincipalConeShift
open CochainComplex
universe vS aS bS
variable {A : Type u} [Category.{vS} A] [Preadditive A] [HasBinaryBiproducts A]
variable {C : Type aS} [Category.{bS} C]
variable [HasShift C ℤ] {F G : C ⥤ CochainComplex A ℤ}
  [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
end PrincipalConeShift

section StrictCones

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

section DoubleCones

open CochainComplex CochainComplex.HomComplex Preadditive

private abbrev diagonal {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :=
  mappingCone.map f f s t h.symm

end DoubleCones

private abbrev chainAction (μ : 𝟭 C ⟶ 𝟭 C) :
    𝟭 (CochainComplex C ℤ) ⟶ 𝟭 (CochainComplex C ℤ) :=
  μ.mapHomologicalComplex (.up ℤ)

private local instance chainAction_commShift (μ : 𝟭 C ⟶ 𝟭 C) :
    NatTrans.CommShift (chainAction μ) ℤ where
  shift_comm n := by
    ext M i
    simp [chainAction, CochainComplex.shiftFunctor_map_f']

end StrictCones

namespace PrincipalReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

open AlgebraicGeometry.ProEtale.AdicCompletion

private abbrev action (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ 𝟭 _ :=
  chainAction (DerivedNakayama.scalarOnModules l E X d)

attribute [local irreducible] DerivedNakayama.scalarOnModules DerivedNakayama.uniformizerEnd

end PrincipalReduction
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.PrincipalReduction

open AlgebraicGeometry.ProEtale.AdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

end AlgebraicGeometry.ProEtale.PrincipalReduction
