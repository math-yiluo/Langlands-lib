/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarUnitUnique
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists

/-! # Generic normalized scalar comparison

Source: Stacks 03D7, 03EK and 06YY.
(blueprint: lem-sf-fixed-scalar-unit-unique).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe sa sb sw
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SequenceScalarConstruction
variable {C : Type sa} [Category.{sb} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{sw} RingCat.{sw})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sw}] [HasSheafify J AddCommGrpCat.{sw}]
  [EssentiallySmall.{sw} C]

/-- Normalized scalar comparison for fixed cochain models.
Source: Stacks 03D7, 03EK and 06YY
(blueprint: lem-sf-fixed-scalar-unit-unique).
Proof: construct the normalized scalar packages with exactly these cochain models.
Apply the package-level normalized comparison and its uniqueness. Transport its
conclusion along the recorded model equalities. This proves the statement before
specializing to concrete quotient rings, so no concrete coefficient sequence is unfolded. -/
theorem fixedScalarUnitUnique
    {R : Sheaf J CommRingCat.{sw}} {φ : R ⟶ R} (hφ : φ = 𝟙 R)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :
    ∃! a : D.E ≅ 𝟭 _, ∀ P U (s : R.obj.obj U) (x : P.val.obj U),
      (a.hom.app P).val.app U (SheafOfModules.systemModelTmul D P U s x) =
        s • x := by
  obtain ⟨A, hA⟩ := scalarPackageExists φ D
  have h := scalarUnitUnique hφ A
  rw [hA] at h
  exact h

end SequenceScalarConstruction
