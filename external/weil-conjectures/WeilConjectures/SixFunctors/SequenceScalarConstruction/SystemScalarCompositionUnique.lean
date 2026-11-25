/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators

/-! # Generic normalized scalar comparison

Source: Stacks 03D7, 03EK and 06YY.
(blueprint: lem-sf-system-scalar-composition-unique).
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
(blueprint: lem-sf-system-scalar-composition-unique).
Proof: Use the existing scalar composition isomorphism and its pure tensor equation for
existence. For uniqueness transpose under the second ordinary adjunction, then use local unit
tensor generators for the first model. Both transposes agree on these generators by the two
specified tensor formulas and the normalized unit equation. -/
theorem scalarCompositionUnique
    {R S T : Sheaf J CommRingCat.{sw}} {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ)
    (A : SheafOfModules.SystemScalarModel φ) (B : SheafOfModules.SystemScalarModel ψ)
    (D : SheafOfModules.SystemScalarModel γ) :
    ∃! a : A.model.E ⋙ B.model.E ≅ D.model.E,
      ∀ P U (c : T.obj.obj U) (b : S.obj.obj U) (x : P.val.obj U),
        (a.hom.app P).val.app U
          (SheafOfModules.systemModelTmul B.model (A.model.E.obj P) U c
            (SheafOfModules.systemModelTmul A.model P U b x)) =
          SheafOfModules.systemModelTmul D.model P U (c * (ψ.hom.app U) b) x := by
  let a := SheafOfModules.systemScalarModelComposition hγ A B D
  have ha := SheafOfModules.systemScalarModelComposition_tmul hγ A B D
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply (B.ordinaryAdj.homEquiv _ _).injective
  apply SheafOfModules.systemScalarModel_hom_ext A P _
  intro V y
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (b.hom.app P).val.app V
      ((B.ordinaryAdj.unit.app (A.model.E.obj P)).val.app V
        (SheafOfModules.systemModelTmul A.model P V 1 y)) =
    (a.hom.app P).val.app V
      ((B.ordinaryAdj.unit.app (A.model.E.obj P)).val.app V
        (SheafOfModules.systemModelTmul A.model P V 1 y))
  rw [B.unit_normalized]
  exact (hb P V 1 1 y).trans (ha P V 1 1 y).symm

end SequenceScalarConstruction
