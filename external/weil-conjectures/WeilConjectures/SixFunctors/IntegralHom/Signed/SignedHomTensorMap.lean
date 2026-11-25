/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorComponents
import WeilConjectures.SixFunctors.IntegralHom.HomComplexTensorPureEquivalence
import WeilConjectures.SixFunctors.IntegralHom.Tensor.TensorEvaluationInterchange

/-! # The signed Hom--tensor chain map

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 0A8X and 08J7.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option quotPrecheck false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

local notation "J" => AlgebraicGeometry.Scheme.ProEt.topology Y

attribute [local instance 2000] abSheafify abLocallyBijective

private theorem generator_transport
    (A B : CochainComplex (Modules.{t, u} Y R) ℤ) (p q n : ℤ) (h : p + q = n)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X p).val.obj U) (y : (B.X q).val.obj U) :
    (eqToHom (congrArg (fun k ↦ (((totalTensor.{t, u} Y R).obj A).obj B).X k) h)).val.app U
        (totalPair.{t, u} Y R A B p q U x y) =
      coefficientTensorGenerator.{u, t + 1, t} J R A B p q n h U x y := by
  subst n
  rfl

/-- The signed exchange exists for arbitrary, possibly unbounded, complexes.
Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 0A8X and 08J7
(blueprint: lem-sf-signed-hom-tensor-map).

Proof: transpose the composite which reassociates (Hom(P,I) tensor Q) tensor P,
interchanges Q and P using the Koszul braiding, reassociates back, and applies
evaluation tensor the identity of Q. All its factors are chain maps. On degrees
a,b,p the only interchange contributes (-1)^(bp); normalized evaluation sends
v tensor x to v(x). Thus the composite has the required local formula.
No boundedness, flatness or injectivity hypothesis occurs. -/
theorem signedHomTensor_exists (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ) :
    ∃ f : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q), IsSignedHomTensor Y R P I Q f := by
  let H := homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I
  obtain ⟨uncurry, huncurry⟩ := homComplexTensor_pure_equivalence Y R H P I
  let e := uncurry.symm (𝟙 H)
  obtain ⟨psi, hpsi⟩ := tensorEvaluation_interchange Y R H P I Q e
  let HQ := ((totalTensor.{t, u} Y R).obj H).obj Q
  let IQ := ((totalTensor.{t, u} Y R).obj I).obj Q
  obtain ⟨curry, hcurry⟩ := homComplexTensor_pure_equivalence Y R HQ P IQ
  refine ⟨curry psi, ?_⟩
  intro a b p U v z x
  change evaluate.{t, u} Y R P IQ (a + b) p U
    (((curry psi).f (a + b)).val.app U (totalPair.{t, u} Y R H Q a b U v z)) x = _
  have hstart := hcurry psi (a + b) p U (totalPair.{t, u} Y R H Q a b U v z) x
  have hcalc := hpsi a b p U v z x
  have he := huncurry e a p U v x
  have hid : uncurry e = 𝟙 H := uncurry.apply_symm_apply _
  rw [hid] at he
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app] at he
  have ht := generator_transport Y R I Q (p + a) b (p + (a + b))
    (add_assoc p a b) U (evaluate.{t, u} Y R P I a p U v x) z
  exact hstart.trans (hcalc.trans
    ((congrArg (fun w ↦ (b * p).negOnePow •
      coefficientTensorGenerator.{u, t + 1, t} J R I Q (p + a) b (p + (a + b))
        (add_assoc p a b) U w z) he.symm).trans
      (congrArg (fun w ↦ (b * p).negOnePow • w) ht.symm)))

end WeilConjectures.IntegralHom
