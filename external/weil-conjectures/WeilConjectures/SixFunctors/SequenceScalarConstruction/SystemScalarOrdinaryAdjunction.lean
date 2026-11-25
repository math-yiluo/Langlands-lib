/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists

/-! # Generic normalized scalar comparison

Source: Stacks 03D7, 03EK and 06YY.
(blueprint: lem-sf-system-scalar-ordinary-adjunction).
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

/-- The actual ordinary scalar adjunction for a fixed cochain model, with its unit formula.
Source: Stacks 03D7, 03EK and 06YY
(blueprint: lem-sf-system-scalar-ordinary-adjunction).
Proof: construct the normalized scalar package with this fixed model. Transport
its ordinary adjunction through the model equality. Its normalized unit is one
tensor the section; unfold the generic tensor generator and simplify one_smul.
The argument is generic in the model so no concrete quotient system is unfolded. -/
theorem scalarOrdinaryAdjunction
    {R S : Sheaf J CommRingCat.{sw}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :
    ∃ adj : D.E ⊣ SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ),
      ∀ (N : SheafOfModules.{sw}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
        (x : N.val.obj U),
        (adj.unit.app N).val.app U x =
          (eqToHom (D.obj_eq N).symm).val.app U
            ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
              ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := by
  obtain ⟨A, hA⟩ := scalarPackageExists φ D
  rw [← hA]
  refine ⟨A.ordinaryAdj, ?_⟩
  intro N U x
  have h := A.unit_normalized N U x
  dsimp only [SheafOfModules.systemModelTmul] at h
  rw [one_smul] at h
  exact h

end SequenceScalarConstruction
