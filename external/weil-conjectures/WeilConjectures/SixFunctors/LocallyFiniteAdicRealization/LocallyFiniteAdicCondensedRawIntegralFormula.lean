/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedStageData
public import WeilConjectures.SixFunctors.AdicFiniteRealization.LocallyFiniteAdicFiniteCondensedRealization

/-! # The integral formula of the raw finite realization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-finite-condensed-raw-integral-formula)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
universe u a b v v' v'' w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

variable [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
private theorem postcompHEq
    {C : Type a} {A B : Type b} {D : Type w}
    [Category.{v} C] [ca : Category.{v'} A] [cb : Category.{v'} B] [Category.{v''} D]
    (hAB : A = B) (hcat : HEq ca cb)
    (Q : C ⥤ A) (P : C ⥤ B) (hQP : HEq Q P)
    (F : A ⥤ D) (G : B ⥤ D) (hFG : HEq F G) : Q ⋙ F = P ⋙ G := by
  subst B
  cases eq_of_heq hcat
  cases eq_of_heq hQP
  cases eq_of_heq hFG
  rfl

private theorem rawCategoryHEq
    (l : ℕ) [Fact l.Prime] {A B : Type u}
    [fa : Field A] [fb : Field B]
    [aa : Algebra ℚ_[l] A] [ab : Algebra ℚ_[l] B]
    [na : FiniteDimensional ℚ_[l] A] [nb : FiniteDimensional ℚ_[l] B]
    (T : Scheme.{u}) (h : A = B) (hf : HEq fa fb) (ha : HEq aa ab) :
    HEq (inferInstance : Category (sfRationalConstructibleCategory l A T))
      (inferInstance : Category (sfRationalConstructibleCategory l B T)) := by
  cases h
  cases hf
  cases ha
  rfl

private theorem integralRestriction
    (A : FiniteCondensedData l X) (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (pbcFiniteField.{u} l (PadicAlgCl l) E) X ⋙
      (A.stage E).rational.functor =
    (A.stage E).integral.functor ⋙ pbcStageLocalization l (PadicAlgCl l) X E := by
  refine CategoryTheory.Functor.hext (F := _) (G := _)
    (fun K ↦ (A.stage E).objects _) (fun K L f ↦ ?_)
  have ht := (A.stage E).tensors K L 1 f
  simp only [map_one, fdRawTensor] at ht
  dsimp only [Functor.comp_map, sfRationalConstructibleLocalization, pbcStageLocalization,
    ScalarLocalization.localization]
  exact ht

/-- The raw finite comparison restricts to the specified integral identity.
Source: the raw identity pins and pure-tensor formula, BS 6.8.14(2).
(blueprint: lem-sf-finite-condensed-raw-integral-formula). -/
theorem finiteRawIntegralFormula (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        finiteFunctor l X A.toCore E =
      (A.stage E).integral.functor ⋙ pbcStageLocalization l (PadicAlgCl l) X E ⋙
        (A.realization E).J := by
  have hf := A.raw.finite_functor
  unfold FdCompletionFiniteFunctor at hf
  have hc : HEq (GeneralAlgebraicallyClosedCoefficients.stageCategory l (PadicAlgCl l) X E)
      (inferInstance : Category
        (sfRationalConstructibleCategory l (pbcFiniteField.{u} l (PadicAlgCl l) E) X)) := by
    exact rawCategoryHEq l X (by rfl) (by unfold pbcFiniteFieldField; rfl)
      (by unfold pbcFiniteFieldAlgebra; rfl)
  have hQ : HEq
      (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
      (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l (PadicAlgCl l) E) X) := by
    rfl
  have h := postcompHEq (by rfl) hc
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l (PadicAlgCl l) E) X)
    hQ (A.raw.family.Φ E) (A.stage E).rational.functor (hf E)
  change (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
    A.raw.family.Φ E) ⋙ (A.realization E).J = _
  refine (congrArg (fun F ↦ F ⋙ (A.realization E).J) h).trans ?_
  exact congrArg (fun F ↦ F ⋙ (A.realization E).J) (integralRestriction l X A E)

end WeilConjectures.LocallyFiniteAdicRealization
