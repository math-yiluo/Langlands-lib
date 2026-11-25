/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorCoordinateMap
public import WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomProjectionNaturality
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationExt
import all WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralTensorUnitSections

/-! # The signed Hom-tensor comparison at the coefficient unit -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
attribute [local instance 20000] abSheafify abLocallyBijective
attribute [local instance] countableColimits ordinaryTensorZero ordinaryTensorObjZero
attribute [local implicit_reducible] homComplex totalTensor coefficientTotalTensor
  evaluate projection coefficientUnit
attribute [local irreducible] homComplexFunctor

private theorem homObjMap_eval
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (M N N' : Modules.{t, u} Y R) (g : N ⟶ N')
    (U : Y.ProEtᵒᵖ) (φ : (SheafOfModules.homObj (R := R) M N).val.obj U)
    (x : M.val.obj U) :
    (((SheafOfModules.homObjMap (R := R) (𝟙 M) g).val.app U φ).app
      (op (Over.mk (𝟙 U.unop)))) x =
        g.val.app U ((φ.app (op (Over.mk (𝟙 U.unop)))) x) := by
  rfl

private theorem totalPair_eq_generator
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (A B : CochainComplex (Modules.{t, u} Y R) ℤ) (a b : ℤ)
    (U : Y.ProEtᵒᵖ) (x : (A.X a).val.obj U) (y : (B.X b).val.obj U) :
    totalPair Y R A B a b U x y = coefficientTensorGenerator.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R A B a b (a + b) rfl U x y := by
  rfl

private theorem generator_cast
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (A B : CochainComplex (Modules.{t, u} Y R) ℤ) (a b k k' : ℤ)
    (h : a + b = k) (e : k = k') (U : Y.ProEtᵒᵖ)
    (v : (A.X a).val.obj U) (z : (B.X b).val.obj U) :
    (eqToHom (congrArg (fun j ↦ (((totalTensor Y R).obj A).obj B).X j) e)).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} (AlgebraicGeometry.Scheme.ProEt.topology Y)
          R A B a b k h U v z) =
      (by
        exact coefficientTensorGenerator.{u, t + 1, t}
          (AlgebraicGeometry.Scheme.ProEt.topology Y) R A B a b k' (h.trans e) U v z) := by
  subst k'
  rfl

private theorem signed_formula_index
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (A I B : CochainComplex (Modules.{t, u} Y R) ℤ)
    (f : ((totalTensor Y R).obj (homComplex (R := R) A I)).obj B ⟶
      homComplex (R := R) A (((totalTensor Y R).obj I).obj B))
    (hf : IsSignedHomTensor Y R A I B f)
    (a b k : ℤ) (hk : a + b = k) (p : ℤ) (U : Y.ProEtᵒᵖ)
    (v : (homComplex (R := R) A I).X a |>.val.obj U)
    (z : (B.X b).val.obj U) (x : (A.X p).val.obj U) :
    evaluate Y R A (((totalTensor Y R).obj I).obj B) k p U
      ((f.f k).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} (AlgebraicGeometry.Scheme.ProEt.topology Y)
          R (homComplex (R := R) A I) B a b k hk U v z)) x =
      (by
        exact (b * p).negOnePow •
          coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R I B (p + a) b (p + k)
              ((add_assoc p a b).trans (congrArg (fun j ↦ p + j) hk)) U
                (evaluate Y R A I a p U v x) z) := by
  subst k
  have h := hf a b p U v z x
  rw [totalPair_eq_generator, totalPair_eq_generator] at h
  rw [generator_cast Y R I B (p + a) b (p + a + b) (p + (a + b)) rfl
    (add_assoc p a b) U (evaluate Y R A I a p U v x) z] at h
  exact h

private theorem evaluate_map
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (A I I' : CochainComplex (Modules.{t, u} Y R) ℤ) (g : I ⟶ I')
    (n p : ℤ) (U : Y.ProEtᵒᵖ)
    (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I).X n
      |>.val.obj U) (x : (A.X p).val.obj U) :
    evaluate Y R A I' n p U
        (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := R)).obj (op A)).map g |>.f n |>.val.app U <| v) x =
      (g.f (p + n)).val.app U (evaluate Y R A I n p U v x) := by
  have h := homProjection_map Y R A I I' g n p
  have hh := congrArg (fun k ↦ k.val.app U v) h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hh
  have hv := congrArg (fun k ↦ k.app (op (Over.mk (𝟙 U.unop))) x) hh
  dsimp only [evaluate]
  exact hv.trans (homObjMap_eval Y R (A.X p) (I.X (p + n)) (I'.X (p + n))
    (g.f (p + n)) U ((projection Y R A I n p).val.app U v) x)

private theorem signed_unit
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (A I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (f : ((totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I)).obj
          (coefficientUnit.{t, u} Y R) ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A
        (((totalTensor.{t, u} Y R).obj I).obj (coefficientUnit.{t, u} Y R)))
    (hf : IsSignedHomTensor Y R A I (coefficientUnit.{t, u} Y R) f) :
    f ≫ ((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := R)).obj (op A)).map (tensorUnitIso.{t, u} Y R I).hom =
      ((tensorUnitIso.{t, u} Y R (homComplex (R := R) A I))).hom := by
  let C := homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I
  let ui := tensorUnitIso.{t, u} Y R I
  let uc := tensorUnitIso.{t, u} Y R C
  apply (cancel_epi uc.inv).1
  rw [Iso.inv_hom_id]
  apply homComplex_evaluation_ext Y R A I C
  intro n p U v x
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change evaluate Y R A I n p U
    ((((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := R)).obj (op A)).map ui.hom).f n |>.val.app U <|
      (f.f n).val.app U ((uc.inv.f n).val.app U v)) x =
        evaluate Y R A I n p U v x
  have he := evaluate_map.{t, u} Y R A
    (((totalTensor.{t, u} Y R).obj I).obj (coefficientUnit.{t, u} Y R)) I
    ui.hom n p U ((f.f n).val.app U ((uc.inv.f n).val.app U v)) x
  refine he.trans ?_
  have h := signed_formula_index Y R A I (coefficientUnit Y R) f hf
    n 0 n (add_zero n) p U v
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat RingCat)).obj R))).inv.val.app U
      (1 : R.obj.obj U)) x
  have hs : evaluate Y R A (((totalTensor.{t, u} Y R).obj I).obj
      (coefficientUnit.{t, u} Y R)) n p U
        ((f.f n).val.app U ((uc.inv.f n).val.app U v)) x =
      (ui.inv.f (p + n)).val.app U (evaluate Y R A I n p U v x) := by
    rw [tensorUnitIso_inv_section, tensorUnitIso_inv_section]
    simpa only [zero_mul, Int.negOnePow_zero, one_smul] using h
  rw [hs]
  exact congrArg (fun k ↦ (k.f (p + n)).val.app U (evaluate Y R A I n p U v x))
    ui.inv_hom_id

/-- A signed Hom-tensor map at the coefficient unit is the map fixed by the unitors.

Source: the degree-zero coefficient unit in paragraph 1 of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks 0A8X
(blueprint: lem-sf-integral-signed-hom-tensor-unit).

Proof: cancel the inverse right unitor on the source and test equality on all
Hom product projections and identity-slice sections. Naturality of Hom projections
moves postcomposition with the target unitor through evaluation. The inverse
unitor section formula writes each input as v tensor 1. The signed formula has
coefficient degree zero, so its sign is one. Transport its total degree to n
explicitly; the resulting evaluation is exactly the inverse target unitor.
The target unitors cancel. No injectivity, flatness or boundedness is required. -/
theorem integral_signedHomTensor_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (A I : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) :
    let R := completedIntegralCommRingSheafUnrestricted l E Y
    let B := (CochainComplex.singleFunctor
      (PrincipalKoszulStrictReplacement.Modules l E Y) 0).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))
    ∀ (f : ((totalTensor Y R).obj (homComplex (R := R) A I)).obj B ⟶
        homComplex (R := R) A (((totalTensor Y R).obj I).obj B)),
      IsSignedHomTensor Y R A I B f →
        f ≫ ((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := R)).obj (op A)).map (PrincipalIntrinsicCompletion.tensorUnit l E Y I).hom =
            (PrincipalIntrinsicCompletion.tensorUnit l E Y (homComplex (R := R) A I)).hom := by
  dsimp only
  intro f hf
  have h := signed_unit Y (completedIntegralCommRingSheafUnrestricted l E Y) A I f hf
  unfold tensorUnitIso at h
  unfold PrincipalIntrinsicCompletion.tensorUnit
  exact h

end WeilConjectures.IntegralHom
