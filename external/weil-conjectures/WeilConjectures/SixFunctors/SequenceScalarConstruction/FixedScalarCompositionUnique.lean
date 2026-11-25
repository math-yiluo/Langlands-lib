/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarCompositionUnique
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists

/-! # Generic normalized scalar comparison

Source: Stacks 03D7, 03EK and 06YY.
(blueprint: lem-sf-fixed-scalar-composition-unique).
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
(blueprint: lem-sf-fixed-scalar-composition-unique).
Proof: construct the normalized scalar packages with exactly these cochain models.
Apply the package-level normalized comparison and its uniqueness. Transport its
conclusion along the recorded model equalities. This proves the statement before
specializing to concrete quotient rings, so no concrete coefficient sequence is unfolded. -/
theorem fixedScalarCompositionUnique
    {R S T : Sheaf J CommRingCat.{sw}} {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ)
    (D1 : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (D2 : SheafOfModules.DerivedChangeOfRingsCochainModel ψ)
    (D3 : SheafOfModules.DerivedChangeOfRingsCochainModel γ) :
    ∃! a : D1.E ⋙ D2.E ≅ D3.E,
      ∀ P U (c : T.obj.obj U) (b : S.obj.obj U) (x : P.val.obj U),
        (a.hom.app P).val.app U
          (SheafOfModules.systemModelTmul D2 (D1.E.obj P) U c
            (SheafOfModules.systemModelTmul D1 P U b x)) =
          SheafOfModules.systemModelTmul D3 P U (c * (ψ.hom.app U) b) x := by
  obtain ⟨A, hA⟩ := scalarPackageExists φ D1
  obtain ⟨B, hB⟩ := scalarPackageExists ψ D2
  obtain ⟨D, hD⟩ := scalarPackageExists γ D3
  have h := scalarCompositionUnique hγ A B D
  rw [hA, hB, hD] at h
  exact h

end SequenceScalarConstruction
