/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel

/-! # Generic normalized scalar comparison

Source: Stacks 03D7, 03EK and 06YY.
(blueprint: lem-sf-system-scalar-tensor-section).
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

/-- Generic scalar comparison extracted from IntegralComparisonSequenceSystems.
Source: Stacks 03D7, 03EK and 06YY
(blueprint: lem-sf-system-scalar-tensor-section).
Proof: Write the sheafification unit explicitly. Both the unit and the transport by the object
equality are linear. Move the scalar through these two linear maps; multiplication by scalar s
sends one tensor x to s tensor x in the balanced tensor product. -/
theorem modelTmul_eq
    {R S : Sheaf J CommRingCat.{sw}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (N : SheafOfModules.{sw} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (eqToHom (D.obj_eq N).symm).val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      SheafOfModules.systemModelTmul D N U s x := by
  let η := (PresheafOfModules.sheafificationAdjunction.{sw}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf φ N)
  change (eqToHom (D.obj_eq N).symm).val.app U
      (η.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • (eqToHom (D.obj_eq N).symm).val.app U
      (η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  rw [← ((eqToHom (D.obj_eq N).symm).val.app U).hom.map_smul]
  rw [← (η.app U).hom.map_smul]
  congr 2
  change (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
    ((s * 1) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  rw [mul_one]

end SequenceScalarConstruction
