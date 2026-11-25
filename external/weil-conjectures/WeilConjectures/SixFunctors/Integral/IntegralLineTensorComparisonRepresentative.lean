/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonDefinitions
public import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
public import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorReductionTowerComparison

/-! Integral line tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
open IntegralOnSlice

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  HasDerivedCategory.standard reductionWitness

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

private theorem generator_smul (n : ℕ) (M : Mod l E X none) (V : X.ProEtᵒᵖ)
    (a : (finite l E X none n).obj.obj V) (x : M.val.obj V) :
    generator l E X none n M V a x = a • generator l E X none n M V 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
      (topology X none) (finite l E X none n)).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
          (projection l E X none n) M)
  let g := (eqToHom (reduction_obj l E X none n M).symm).val.app V
  change g (η.app V (a ⊗ₜ[(ring l E X none).obj.obj V,
      ((projection l E X none n).hom.app V).hom] x)) =
    a • g (η.app V ((1 : (finite l E X none n).obj.obj V) ⊗ₜ[
      (ring l E X none).obj.obj V, ((projection l E X none n).hom.app V).hom] x))
  rw [← g.hom.map_smul, ← (η.app V).hom.map_smul]
  congr 2
  symm
  exact (ModuleCat.ExtendScalars.smul_tmul
    (f := ((projection l E X none n).hom.app V).hom) a 1 x).trans (by rw [mul_one])

private theorem tensorGenerator_smul
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R)) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
    (a : R.obj.obj V) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    coefficientTensorGenerator.{r, c, v} J R P Q p q k h V (a • x) y =
      a • coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y := by
  delta coefficientTotalTensor coefficientTensorGenerator
  simp only [← TensorProduct.smul_tmul', map_smul]

-- Retain the named witnesses in the original public signature.
set_option linter.unusedVariables false in
/-- A line has a K-flat single complex, its tensor with a good complex is good,
and scalar extension commutes with that total tensor with the specified generators.
Source: Stacks 06YQ, 06YY and 07A4
(blueprint: lem-sf-integral-line-tensor-comparison-representative).

Proof: a rank-one trivialization makes tensor by T the identity on module sheaves.
Exactness is local, so T is flat. Its degree-zero single complex is bounded above
with flat terms, hence K-flat. Tensor of two K-flat complexes is K-flat by the
associativity isomorphism and the acyclic-tensor criterion. Each term of the total
complex is a direct sum of tensors of flat modules and is therefore flat. This
proves that the tensor with P belongs to Good. At each quotient, extend scalars on
the direct-sum total tensor. On the summand in bidegree (p,q), the balanced map is
 a tensor (x tensor y) ↦ (a tensor x) tensor (1 tensor y).
Its inverse sends (a tensor x) tensor (b tensor y) to ab tensor (x tensor y).
The balancing relations make both maps well defined and inverse; sheafification
and the coproduct universal property extend them to all sections and all summands.
The maps commute with the two differential components because scalar extension
is additive, and both total differentials have the same sign (-1)^p in the second
component. They therefore give the asserted chain isomorphism β. Its formula on
sheafified pure tensors is precisely the displayed equation. The argument includes
n = 0, whose quotient is the positive first power, and arbitrary unbounded P. -/
theorem integralLineTensorComparison_representative
    (T : Mod l E X none) [T.IsFiniteLocallyFreeOfRank 1]
    (P : (Good l E X none).FullSubcategory) :
      ∃ (hT : CochainComplex.IsKFlatIndependentCoefficients
          (J := topology X none) (R := ring l E X none)
          ((integralLineSingle l E X).obj T))
        (hS : Good l E X none (integralLineComplex l E X P.obj T)),
        ∀ n : ℕ, ∃ β :
            (integralLineFiniteComplex l E X n).obj (integralLineComplex l E X P.obj T) ≅
              integralLineFiniteTensor l E X P.obj T n,
          (∀ (p q k : ℤ) (hpq : p + q = k) (V : X.ProEtᵒᵖ)
              (a : (finite l E X none n).obj.obj V)
              (x : (P.obj.X p).val.obj V)
              (y : (((integralLineSingle l E X).obj T).X q).val.obj V),
            (β.hom.f k).val.app V
                (generator l E X none n ((integralLineComplex l E X P.obj T).X k) V a
                  (coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                    (ring l E X none) P.obj ((integralLineSingle l E X).obj T)
                    p q k hpq V x y)) =
              coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                (finite l E X none n) ((integralLineFiniteComplex l E X n).obj P.obj)
                ((integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))
                p q k hpq V (generator l E X none n (P.obj.X p) V a x)
                (generator l E X none n (((integralLineSingle l E X).obj T).X q) V 1 y)) := by
  classical
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : HasDerivedCategory
      (SheafOfModules.LineUnbounded.Modules.{t, u} X (ring l E X none)) :=
    HasDerivedCategory.standard _
  let R := ring l E X none
  let Rm := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
    (forget₂ CommRingCat RingCat)).obj R
  have hcover : ∀ U : X.ProEt, ∃ s : Sieve U,
      s ∈ AlgebraicGeometry.Scheme.ProEt.topology X U ∧
      ∀ (V : X.ProEt) (f : V ⟶ U), s f →
        Nonempty (T.over V ≅ SheafOfModules.unit (Rm.over V)) := by
    obtain ⟨I, V, hV, h⟩ :=
      (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
        (M := T) (r := 1)).mp inferInstance
    intro U
    refine ⟨Sieve.ofObjects V U, hV U, ?_⟩
    rintro Z f ⟨i, ⟨g⟩⟩
    let e : T.over (V i) ≅ SheafOfModules.unit (Rm.over (V i)) :=
      (h i).some ≪≫ SheafOfModules.freeUniqueIso (ULift (Fin 1))
    exact ⟨((SheafOfModules.overFunctorMap Rm g).app T).symm ≪≫
      (SheafOfModules.overMap Rm g).mapIso e ≪≫
        SheafOfModules.overMapUnitIso (R := Rm) g⟩
  obtain ⟨_, _, _, _, _, _, _, hflat, _⟩ :=
    SheafOfModules.LineEvaluation.evaluation_inverse_pair R T hcover
  obtain ⟨hT, hTf, _⟩ :=
    SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization R T hflat
  have htotal := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (ring l E X none) P.obj ((integralLineSingle l E X).obj T)
    P.property.1 hT P.property.2 hTf
  refine ⟨hT, ⟨htotal.1, htotal.2.1⟩, ?_⟩
  intro n
  obtain ⟨κ, hκ⟩ := scalarTensorTotal.{t + 1, t, u}
    (projection l E X none n) (reduction l E X none n)
    (reduction_obj l E X none n) (unrestrictedReduction_map l E X n)
  refine ⟨κ.app (P.obj, (integralLineSingle l E X).obj T), ?_⟩
  intro p q k hpq V a x y
  subst k
  have hh := hκ P.obj ((integralLineSingle l E X).obj T) p q (p + q) rfl V x y
  change ((κ.hom.app (P.obj, (integralLineSingle l E X).obj T)).f (p + q)).val.app V
      (generator l E X none n _ V 1
        (coefficientTensorGenerator.{u, t + 1, t} (topology X none)
          (ring l E X none) P.obj ((integralLineSingle l E X).obj T)
          p q (p + q) rfl V x y)) =
    coefficientTensorGenerator.{u, t + 1, t} (topology X none) (finite l E X none n)
      ((integralLineFiniteComplex l E X n).obj P.obj)
      ((integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))
      p q (p + q) rfl V (generator l E X none n (P.obj.X p) V 1 x)
      (generator l E X none n (((integralLineSingle l E X).obj T).X q) V 1 y) at hh
  rw [generator_smul, map_smul]
  trans a • coefficientTensorGenerator.{u, t + 1, t} (topology X none)
    (finite l E X none n) ((integralLineFiniteComplex l E X n).obj P.obj)
    ((integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))
    p q (p + q) rfl V (generator l E X none n (P.obj.X p) V 1 x)
    (generator l E X none n (((integralLineSingle l E X).obj T).X q) V 1 y)
  · exact congrArg (fun z ↦ a • z) hh
  rw [generator_smul l E X n (P.obj.X p) V a x]
  exact (tensorGenerator_smul.{t + 1, t, u} (topology X none)
    (finite l E X none n) _ _ p q (p + q) rfl V a _ _).symm

end WeilConjectures
