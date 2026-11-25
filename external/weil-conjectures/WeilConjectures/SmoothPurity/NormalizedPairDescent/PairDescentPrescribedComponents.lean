/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent

/-! # Specified components of the normalized coefficient-pair functor

Source: the existing pairDescent_with_components proof in DerivedPullbackTensorHom.
(blueprint: lem-weil-pair-descent-prescribed-components).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory

namespace WeilConjectures.NormalizedPairDescent
variable {I : Type*} [Preorder I] [IsDirectedOrder I]
  {C : I → Type*} [∀ i, Category* (C i)]
  {D : I → Type*} [∀ i, Category* (D i)]
  (S : StageSystem C) (T : StageSystem D) (φ : ∀ i, C i ⥤ D i)

/-- The literal output pair of the stagewise functors.
Source: coefficient-pair descent.
(blueprint: lem-weil-pair-descent-prescribed-components). -/
abbrev object (P : S.PairCategory) : T.PairCategory :=
  ⟨P.stage, (φ P.stage).obj P.obj⟩

/-- Coherent coefficient-pair descent with the prescribed comparison components.
Source: the existing pairDescent_with_components proof in DerivedPullbackTensorHom.
(blueprint: lem-weil-pair-descent-prescribed-components).
Proof: apply coefficient-pair descent. The output pair is definitionally the stagewise
output. For each pair of represented objects, substitute the given hom and inverse
component equalities into the generic representative formula. Conversely, substitute
these equalities backwards to recover the generic prescription and its uniqueness. -/
theorem existsUnique
    (b : ∀ {i j} (h : i ≤ j), φ i ⋙ T.T h ≅ S.T h ⋙ φ j)
    (hcoh : StageSystem.pairFunctorCoherent S T φ b)
    (c : ∀ (P : S.PairCategory) (M : I) (h : P.stage ≤ M),
      (object S T φ P).toStage h ≅ (φ M).obj (P.toStage h))
    (hc : ∀ (P : S.PairCategory) (M : I) (h : P.stage ≤ M),
      HEq ((b h).hom.app P.obj) (c P M h).hom ∧
        HEq ((b h).inv.app P.obj) (c P M h).inv) :
    ∃! F : S.PairCategory ⥤ T.PairCategory,
      (∀ P, F.obj P = object S T φ P) ∧
      (∀ (P Q : S.PairCategory) (M : I) (hP : P.stage ≤ M) (hQ : Q.stage ≤ M)
        (a : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (StageSystem.PairCategory.mkHom M hP hQ a))
          (StageSystem.PairCategory.mkHom
            (X := object S T φ P) (Y := object S T φ Q)
            M hP hQ ((c P M hP).hom ≫ (φ M).map a ≫ (c Q M hQ).inv))) := by
  have H := StageSystem.coefficientPairFunctor_exists S T φ b hcoh
  apply (existsUnique_congr (fun F ↦ ?_)).mp H
  constructor
  · rintro ⟨ho, hm⟩
    refine ⟨fun P ↦ ?_, fun P Q M hP hQ a ↦ ?_⟩
    · exact (ho P).trans (StageSystem.coefficientPairFunctorObject_eq S T φ P)
    · cases P with
      | mk i P =>
        cases Q with
        | mk j Q =>
          have hp := eq_of_heq (hc ⟨i, P⟩ M hP).1
          have hq := eq_of_heq (hc ⟨j, Q⟩ M hQ).2
          simpa only [hp, hq, StageSystem.coefficientPairFunctorObject,
            object] using hm M hP hQ a
  · rintro ⟨ho, hm⟩
    refine ⟨fun P ↦ ?_, fun {P Q} M hP hQ a ↦ ?_⟩
    · exact (ho P).trans (StageSystem.coefficientPairFunctorObject_eq S T φ P).symm
    · cases P with
      | mk i P =>
        cases Q with
        | mk j Q =>
          have hp := eq_of_heq (hc ⟨i, P⟩ M hP).1
          have hq := eq_of_heq (hc ⟨j, Q⟩ M hQ).2
          simpa only [hp, hq, StageSystem.coefficientPairFunctorObject,
            object] using hm ⟨i, P⟩ ⟨j, Q⟩ M hP hQ a

end WeilConjectures.NormalizedPairDescent
