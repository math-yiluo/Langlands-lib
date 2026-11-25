/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfAlgebraicallyClosedCoefficients.SfAlgebraicallyClosedCoefficients

import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import Mathlib.CategoryTheory.Whiskering

/-! # Normalized scalar stages for algebraically closed coefficients

The scalar-stage part of the intrinsic common-stage construction is isolated here
so that normalization and pair-category constructions compile independently.
Source: the scalar-stage steps of blueprint order 1462
(blueprint: lem-general-algebraically-closed-coefficient-stages).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures
namespace GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] ScalarLocalization.category

attribute [local irreducible] sfRationalConstructibleLocalization
  sfRationalTriangulationDatum sfRationalScalarExtension
  sfRationalScalarComp sfRationalScalarUnit sfIntegralScalarComp sfIntegralScalarUnit
  sfIntegralOrdinaryComparison

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

private theorem unique_heq {α : Sort*} (a : α) : ∃! x : α, HEq x a :=
  ⟨a, HEq.rfl, fun _ h ↦ eq_of_heq h⟩

private theorem stage_spec_existsUnique
    {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
    (T : ∀ {i j : I}, i ≤ j → C i ⥤ C j)
    (a : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), T h ⋙ T h' ≅ T (h.trans h'))
    (c : ∀ {i j k m : I} (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ m) (X : C i),
      (T h'').map ((a h h').hom.app X) ≫ (a (h.trans h') h'').hom.app X =
        (a h' h'').hom.app ((T h).obj X) ≫ (a h (h'.trans h'')).hom.app X) :
    ∃! R : StageSystem C,
      (∀ (i j : I) (h : i ≤ j), R.T h = T h) ∧
      (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), HEq (R.assoc h h') (a h h')) := by
  let S : StageSystem C := ⟨T, a, c⟩
  refine ⟨S, ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩, ?_⟩
  rintro ⟨T', a', c'⟩ ⟨hT, ha⟩
  have ht : @T' = @T := by funext i j h; exact hT i j h
  cases ht
  have he : @a' = @a := by funext i j k h h'; exact eq_of_heq (ha i j k h h')
  cases he
  rfl

private theorem commShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

private theorem unique_transport
    {α β : Sort u} (e : α = β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ a b, HEq a b → (P a ↔ Q b)) (hQ : ∃! b, Q b) : ∃! a, P a := by
  subst β
  have hpq : P = Q := funext (fun a ↦ propext (h a a HEq.rfl))
  simpa only [hpq] using hQ
private theorem equality_commShift_component
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F G : C ⥤ D) (h : F = G) (c : F.CommShift ℤ) (d : G.CommShift ℤ)
    (hc : HEq c d) (n : ℤ) (X : C) :
    HEq ((Functor.commShiftIso F (self := c) n).hom.app X)
      ((Functor.commShiftIso G (self := d) n).hom.app X) := by
  subst G
  cases eq_of_heq hc
  rfl

private theorem equality_mapped_commShift_component
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ]
    (F G : C ⥤ D) (h : F = G) (c : F.CommShift ℤ) (d : G.CommShift ℤ)
    (hc : HEq c d) (Q : D ⥤ E) (n : ℤ) (X : C) :
    HEq (Q.map ((Functor.commShiftIso F (self := c) n).hom.app X))
      (Q.map ((Functor.commShiftIso G (self := d) n).hom.app X)) := by
  subst G
  cases eq_of_heq hc
  rfl

private theorem exact_cast
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) (e : F = G) (c : G.CommShift ℤ)
    (hc : @Functor.IsTriangulated _ _ _ _ _ _ G c _ _ _ _ _ _ _ _) :
    @Functor.IsTriangulated _ _ _ _ _ _ F
      (cast (congrArg (fun H : C ⥤ D ↦ H.CommShift ℤ) e.symm) c)
      _ _ _ _ _ _ _ _ := by
  subst G
  exact hc

private theorem exact_heq
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) (e : F = G) (cF : F.CommShift ℤ) (c : G.CommShift ℤ)
    (hs : HEq cF c)
    (hc : @Functor.IsTriangulated _ _ _ _ _ _ G c _ _ _ _ _ _ _ _) :
    @Functor.IsTriangulated _ _ _ _ _ _ F
      cF
      _ _ _ _ _ _ _ _ := by
  subst G
  cases eq_of_heq hs
  exact hc

private theorem normalized_shift_existsUnique
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (I : D ⥤ E) [I.Full] [I.Faithful] [I.CommShift ℤ]
    (H : C ⥤ E) [H.CommShift ℤ] (e : F ⋙ I ≅ H) :
    ∃! c : F.CommShift ℤ, ∀ n X,
      HEq (I.map ((Functor.commShiftIso F (self := c) n).hom.app X) ≫
        (I.commShiftIso n).hom.app (F.obj X))
        (e.hom.app ((shiftFunctor C n).obj X) ≫ (H.commShiftIso n).hom.app X ≫
          (shiftFunctor E n).map (e.inv.app X)) := by
  let c : F.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  have hc (n : ℤ) (X : C) :
      HEq (I.map ((Functor.commShiftIso F (self := c) n).hom.app X) ≫
        (I.commShiftIso n).hom.app (F.obj X))
        (e.hom.app ((shiftFunctor C n).obj X) ≫ (H.commShiftIso n).hom.app X ≫
          (shiftFunctor E n).map (e.inv.app X)) := by
    change HEq (I.map ((Functor.CommShift.OfComp.iso e n).hom.app X) ≫
      (I.commShiftIso n).hom.app (F.obj X)) _
    simp [Category.assoc]
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply commShift_ext
  intro n
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app (F.obj X))).mp
  exact eq_of_heq ((hc' n X).trans (hc n X).symm)

-- Match the transported field and module structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The specified raw rational stage, using its equivalent small coefficient model.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable def Stage (E : Index l Ω) :=
  sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage l Ω Y E) :=
  inferInstanceAs (Category (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance stagePreadditive (E : Index l Ω) :
    Preadditive (Stage l Ω Y E) :=
  inferInstanceAs (Preadditive
    (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance stageZero (E : Index l Ω) :
    HasZeroObject (Stage l Ω Y E) :=
  sfRationalConstructibleZero l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance stageShift (E : Index l Ω) :
    HasShift (Stage l Ω Y E) ℤ :=
  sfRationalConstructibleShift l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance stageShiftAdditive (E : Index l Ω) (n : ℤ) :
    (shiftFunctor (Stage l Ω Y E) n).Additive :=
  sfRationalConstructibleShiftAdditive l (Coefficient.{u} l Ω E) Y n

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance stagePretriangulated (E : Index l Ω) :
    Pretriangulated (Stage l Ω Y E) :=
  sfRationalConstructiblePretriangulated l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance stageTriangulated (E : Index l Ω) :
    IsTriangulated (Stage l Ω Y E) :=
  sfRationalConstructibleTriangulated l (Coefficient.{u} l Ω E) Y

/-- The characteristic parameter affects only preservation proofs, not scalar extension.
This identifies the datum-free transition with every allowed specialization before
forming the common-stage system, without choosing a finite-field datum.
Source: blueprint order 1821, scalar-transition clause
(blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: unfold sfConstructibleIntegralScalarExtension. For either parameter its object
is the same ambient completed extension with a proof of the same intrinsic predicate.
Proof irrelevance identifies these subtype objects; the full-subcategory morphism maps
are the same ambient maps. Functor extensionality gives the first equality. Substitute
that equality in sfRationalScalarExtension_existsUnique: the two specifications have
the same object formula and the same image of every pure tensor. Uniqueness gives the
second equality. The argument includes identity coefficient maps and zero objects and
uses no geometric hypothesis on Y. -/
theorem scalarExtension_parameter_independent
    (l : ℕ) [Fact l.Prime] (p q : ℕ) (hp : l ≠ p) (hq : l ≠ q)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u}) :
    sfConstructibleIntegralScalarExtension p l hp E L ι Y =
        sfConstructibleIntegralScalarExtension q l hq E L ι Y ∧
      sfRationalScalarExtension l E Y p hp L ι =
        sfRationalScalarExtension l E Y q hq L ι := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      unfold sfRationalScalarExtension
      exact ⟨rfl, rfl⟩

/-- The actual completed rational scalar transition, with both coefficient identifications.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable def transition (E L : Index l Ω) (h : E ≤ L) :
    Stage l Ω Y E ⥤ Stage l Ω Y L :=
  sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The datum-free restricted completed integral tensor transition.
Only its preservation proof uses the zero instance of the redundant parameter.
Source: blueprint order 1821 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable abbrev integralTransition (E L : Index l Ω) (h : E ≤ L) :=
  sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- The integral transition inherits the ordinary tensor shift through its canonical
quotient-completion comparison, not through an arbitrary exact-functor witness.
Source: blueprint order 1462, exact transition clause
(blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: conjugate the ordinary derived tensor shift by sfIntegralOrdinaryComparison.
The full intrinsic subcategory inherits the ambient shift. The inclusion's shift
comparisons identify its shifted objects with ambient shifts on both sides. Full
faithfulness lifts each component and its inverse. Naturality, the zero equation and
the addition equation follow from the ordinary ones by cancellation of the comparisons.
The formula fixes all components,
so extensionality of natural isomorphisms and proof irrelevance prove uniqueness. -/
theorem integralScalarCommShift_existsUnique
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u}) :
    ∃! c : (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).CommShift ℤ,
      (fun [commInst : (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).CommShift ℤ] ↦
        ∀ (n : ℤ) (K : sfIntegralConstructibleCategory l E Y),
          HEq
            ((((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).commShiftIso n).hom.app K).hom ≫
              ((sfIntegralConstructible l L Y).ι.commShiftIso n).hom.app
                ((sfConstructibleIntegralScalarExtension 0 l
                  (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K))
            ((sfIntegralOrdinaryComparison l E L ι Y).inv.app
                ((shiftFunctor (sfIntegralConstructibleCategory l E Y) n).obj K) ≫
              (Functor.commShiftIso
                ((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y)
                n).hom.app K ≫
              (shiftFunctor (DerivedCategory (scalarReductionSource.{u, u} l L Y)) n).map
                ((sfIntegralOrdinaryComparison l E L ι Y).hom.app K)))
        (commInst := c) := by
  exact normalized_shift_existsUnique
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y)
    (sfIntegralConstructible l L Y).ι
    ((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y)
    (sfIntegralOrdinaryComparison l E L ι Y).symm

/-- The fixed ordinary-to-completed normalization of the integral transition shift.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance integralTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (integralTransition l Ω Y E L h).CommShift ℤ :=
  (integralScalarCommShift_existsUnique l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).exists.choose

private noncomputable def auxiliaryFiniteDatum (p : ℕ) (hp : p.Prime) :
    FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

section
attribute [local semireducible] ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition
variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

set_option linter.unusedSectionVars false in
/-- The proof parameter in preservation cannot change the tensor functor.
Source: blueprint order 1821, scalar transitions
(blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: the integral restrictions have the same ambient object and arrow maps;
only their membership proofs differ, hence they agree by proof irrelevance.
The two rational functors therefore satisfy the identical exists-unique tensor
specification of sfRationalScalarExtension_existsUnique. Its uniqueness identifies
these functors on objects and all pure tensors, hence on every morphism. -/
theorem specialization_transition (E L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : E ≤ L) :
    transition l Ω Y E L h = SfAlgebraicallyClosedCoefficients.transition D l hl Ω Y E L h := by
  unfold transition SfAlgebraicallyClosedCoefficients.transition
  exact (scalarExtension_parameter_independent l 0 D.p
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y).2

include D hl in
private theorem normalized_transitionShift_existsUnique
    (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) :
    ∃! c : (transition l Ω Y E L h).CommShift ℤ,
      (fun [_commInst : (transition l Ω Y E L h).CommShift ℤ] ↦
        ∀ K : Stage l Ω Y E,
          HEq (((transition l Ω Y E L h).commShiftIso (1 : ℤ)).hom.app K)
            ((sfRationalConstructibleLocalization l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y).map
              (((integralTransition l Ω Y E L h).commShiftIso (1 : ℤ)).hom.app K.obj)))
        (_commInst := c) := by
  have hi : HEq (integralTransitionCommShift l Ω Y E L h)
      (SfAlgebraicallyClosedCoefficients.integralTransitionCommShift D l hl Ω Y E L h) := by
    apply heq_of_eq
    apply (integralScalarCommShift_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y).unique
    · exact (integralScalarCommShift_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y).exists.choose_spec
    · exact (SfAlgebraicallyClosedCoefficients.integralTransitionCommShift_existsUnique
        D l hl Ω Y E L h).exists.choose_spec
  have hF := specialization_transition D l hl Ω Y E L h
  have hInt := (scalarExtension_parameter_independent l 0 D.p
    (Fact.out : l.Prime).ne_zero hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y).1
  apply unique_transport
    (congrArg (fun F : Stage l Ω Y E ⥤ Stage l Ω Y L ↦ F.CommShift ℤ) hF) _ _ ?_
    (SfAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique D l hl Ω Y E L h)
  intro c d hcd
  have hleft (K : Stage l Ω Y E) := equality_commShift_component _ _ hF c d hcd 1 K
  have hright (K : Stage l Ω Y E) := equality_mapped_commShift_component _ _ hInt
    (integralTransitionCommShift l Ω Y E L h)
    (SfAlgebraicallyClosedCoefficients.integralTransitionCommShift D l hl Ω Y E L h)
    hi (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) 1 K.obj
  constructor
  · intro hc K
    exact (hleft K).symm.trans ((hc K).trans (hright K))
  · intro hd K
    exact (hleft K).trans ((hd K).trans (hright K).symm)

end

set_option linter.unusedVariables false in
/-- The rational transition shift is uniquely fixed by localizing the normalized integral
shift. Source: blueprint order 1462, exact transition clause
(blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: choose a prime p strictly greater than l and use the concrete datum with base
field ZMod p. The integral transition and its normalized shift agree with the p=0
versions by parameter independence and integral normalization uniqueness. Equality
transport therefore identifies the two rational normalization predicates at shift one.
Transport the existing finite-field exists-unique theorem along that equality of
functors and predicates. This proves existence and uniqueness of the full coherent
integer-shift datum, with precisely the required integral-image normalization. -/
theorem transitionCommShift_existsUnique (E L : Index l Ω) (h : E ≤ L) :
    ∃! c : (transition l Ω Y E L h).CommShift ℤ,
      (fun [commInst : (transition l Ω Y E L h).CommShift ℤ] ↦
        ∀ K : Stage l Ω Y E,
          HEq (((transition l Ω Y E L h).commShiftIso (1 : ℤ)).hom.app K)
            ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
              (((integralTransition l Ω Y E L h).commShiftIso (1 : ℤ)).hom.app K.obj)))
        (commInst := c) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let D := auxiliaryFiniteDatum p hp
  have hlp : l ≠ D.p := by
    change l ≠ p
    omega
  exact normalized_transitionShift_existsUnique D l hlp Ω Y E L h

/-- The canonical, integral-image-normalized shift comparison of the rational transition.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance transitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (transition l Ω Y E L h).CommShift ℤ :=
  (transitionCommShift_existsUnique l Ω Y E L h).exists.choose

section
attribute [local semireducible] ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition
variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The normalized scalar shift comparisons agree under specialization.
Source: blueprint order 1821, exact transitions
(blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: the integral comparison is fixed by the same ordinary tensor shift and
quotient-completion normalization on every object, independently of the proof
parameter. Uniqueness identifies the two integral CommShift structures. The
rational shift comparison is uniquely their localized image at one, with its
coherent integer iterates, so its uniqueness gives the displayed identification. -/
theorem specialization_transitionShift
    (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) :
    HEq (transitionCommShift l Ω Y E L h)
      (SfAlgebraicallyClosedCoefficients.transitionCommShift D l hl Ω Y E L h) := by
  have hi : HEq (integralTransitionCommShift l Ω Y E L h)
      (SfAlgebraicallyClosedCoefficients.integralTransitionCommShift D l hl Ω Y E L h) := by
    apply heq_of_eq
    apply (integralScalarCommShift_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y).unique
    · exact (integralScalarCommShift_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y).exists.choose_spec
    · exact (SfAlgebraicallyClosedCoefficients.integralTransitionCommShift_existsUnique
        D l hl Ω Y E L h).exists.choose_spec
  have hF := specialization_transition D l hl Ω Y E L h
  let c : (transition l Ω Y E L h).CommShift ℤ :=
    cast (congrArg (fun F : Stage l Ω Y E ⥤ Stage l Ω Y L ↦ F.CommShift ℤ) hF.symm)
      (SfAlgebraicallyClosedCoefficients.transitionCommShift D l hl Ω Y E L h)
  have hc : HEq c
      (SfAlgebraicallyClosedCoefficients.transitionCommShift D l hl Ω Y E L h) :=
    cast_heq _ _
  apply HEq.trans (b := c) ?_ hc
  apply heq_of_eq
  apply (transitionCommShift_existsUnique l Ω Y E L h).unique
  · exact (transitionCommShift_existsUnique l Ω Y E L h).exists.choose_spec
  · intro K
    apply (equality_commShift_component _ _ hF c
      (SfAlgebraicallyClosedCoefficients.transitionCommShift D l hl Ω Y E L h) hc 1 K).trans
    have ho := (SfAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
      D l hl Ω Y E L h).exists.choose_spec K
    have hInt := (scalarExtension_parameter_independent l 0 D.p
      (Fact.out : l.Prime).ne_zero hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y).1
    exact ho.trans (equality_mapped_commShift_component _ _ hInt
      (integralTransitionCommShift l Ω Y E L h)
      (SfAlgebraicallyClosedCoefficients.integralTransitionCommShift D l hl Ω Y E L h)
      hi (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) 1 K.obj).symm

end

section
attribute [local semireducible] ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition

/-- Exactness for the normalized shift comparison on the recorded intrinsic rational stages.
Source: blueprint order 1462, exact transition clause
(blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: choose a prime p greater than l and the concrete finite-field datum with
base ZMod p. Parameter independence identifies the rational scalar functors, and
specialization_transitionShift identifies their specified CommShift structures.
Transport the finite-field transitionExact theorem along both equalities. Its
triangulated-functor assertion is therefore for the prescribed normalized shift. -/
@[instance]
theorem transitionExact (E L : Index l Ω) (h : E ≤ L) :
    (transition l Ω Y E L h).IsTriangulated := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let D := auxiliaryFiniteDatum p hp
  have hlp : l ≠ D.p := by
    change l ≠ p
    omega
  exact exact_heq (transition l Ω Y E L h)
    (SfAlgebraicallyClosedCoefficients.transition D l hlp Ω Y E L h)
    (specialization_transition D l hlp Ω Y E L h)
    (transitionCommShift l Ω Y E L h)
    (SfAlgebraicallyClosedCoefficients.transitionCommShift D l hlp Ω Y E L h)
    (specialization_transitionShift D l hlp Ω Y E L h)
    (SfAlgebraicallyClosedCoefficients.transitionExact D l hlp Ω Y E L h)

end

set_option linter.unusedSectionVars false in

/-- Additivity of the published intrinsic rational scalar-extension functor.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: the transition is the published sfRationalScalarExtension. Its named
additivity instance gives precisely the two equations for the recorded stage Hom groups. -/
@[instance]
theorem transitionAdditive (E L : Index l Ω) (h : E ≤ L) :
    (transition l Ω Y E L h).Additive := by
  exact sfRationalScalarExtension_additive l (Coefficient.{u} l Ω E) Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h)

/-- Balanced tensor composition followed by the specified coefficient-map equality.
This helper keeps the ordinary field structures explicit during size transport.
Source: blueprint order 1821 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable def scalarAssociator
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (ι : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : E →ₐ[Padic l] M)
    (h : j.comp ι = k) (Y : AlgebraicGeometry.Scheme.{u}) :
    sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        sfRationalScalarExtension l L Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j ≅
      sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M k :=
  sfRationalScalarComp l E L ι Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j ≪≫
    eqToIso (congrArg
      (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M) h)

attribute [local irreducible] scalarAssociator

/-- The scalar associator is fixed by the published balanced-tensor comparison.
Source: blueprint order 1462, canonical composition clause
(blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: use sfRationalScalarComp, followed by equality transport along the actual
coefficient-inclusion composition law, exactly scalarAssociator. The stage
structures are the published rational structures, so this has the asserted endpoints.
HEq specifies the entire natural isomorphism and hence proves uniqueness. -/
theorem associator_existsUnique (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    ∃! a : transition l Ω Y E L h ⋙ transition l Ω Y L M k ≅
        transition l Ω Y E M (h.trans k),
      HEq a (scalarAssociator l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
        (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
        ((coefficientInclusion_laws l Ω).2 E L M h k) Y) := by
  unfold transition
  exact unique_heq (scalarAssociator l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
    (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
    ((coefficientInclusion_laws l Ω).2 E L M h k) Y)

/-- The canonical scalar associator, with its tensor-generator normalization.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable def associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition l Ω Y E L h ⋙ transition l Ω Y L M k ≅
      transition l Ω Y E M (h.trans k) :=
  (associator_existsUnique l Ω Y E L M h k).exists.choose

attribute [local irreducible] associator

/-- The normalized scalar unit, transported through the coefficient identifications.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable def unitor (E : Index l Ω) : transition l Ω Y E E le_rfl ≅
    𝟭 (Stage l Ω Y E) :=
  eqToIso (congrArg (sfRationalScalarExtension l
    (Coefficient.{u} l Ω E) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E))
    ((coefficientInclusion_laws l Ω).1 E)) ≪≫
    sfRationalScalarUnit l (Coefficient.{u} l Ω E) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))

private theorem scalarAssociator_pentagon
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (Y : AlgebraicGeometry.Scheme.{u})
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : M →ₐ[Padic l] N)
    (ij : E →ₐ[Padic l] M) (jk : L →ₐ[Padic l] N) (ijk : E →ₐ[Padic l] N)
    (hij : j.comp i = ij) (hjk : k.comp j = jk)
    (hijk : k.comp ij = ijk) (hijk' : jk.comp i = ijk)
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l M Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) N k).map
        ((scalarAssociator l E L M i j ij hij Y).hom.app K) ≫
        (scalarAssociator l E M N ij k ijk hijk Y).hom.app K =
      (scalarAssociator l L M N j k jk hjk Y).hom.app
          ((sfRationalScalarExtension l E Y 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i).obj K) ≫
        (scalarAssociator l E L N i jk ijk hijk' Y).hom.app K := by
  subst ij
  subst jk
  subst ijk
  have hcast : (eqToIso (congrArg
      (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) N)
      hijk')).hom.app K = 𝟙 _ := by
    rfl
  unfold scalarAssociator
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [hcast]
  simp only [eqToIso.hom, eqToHom_refl, NatTrans.id_app,
    Category.comp_id]
  have hp := (sfRationalScalar_coherence l E L i Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).2.2 N k K
  erw [Category.comp_id]
  exact hp

private theorem scalarAssociator_pentagon_nat
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (Y : AlgebraicGeometry.Scheme.{u})
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : M →ₐ[Padic l] N)
    (ij : E →ₐ[Padic l] M) (jk : L →ₐ[Padic l] N) (ijk : E →ₐ[Padic l] N)
    (hij : j.comp i = ij) (hjk : k.comp j = jk)
    (hijk : k.comp ij = ijk) (hijk' : jk.comp i = ijk)
    :
    Functor.whiskerRight (scalarAssociator l E L M i j ij hij Y).hom
        (sfRationalScalarExtension l M Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) N k) ≫
        (scalarAssociator l E M N ij k ijk hijk Y).hom =
      (Functor.associator
        (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i)
        (sfRationalScalarExtension l L Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j)
        (sfRationalScalarExtension l M Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) N k)).hom ≫
      Functor.whiskerLeft
        (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i)
        (scalarAssociator l L M N j k jk hjk Y).hom ≫
      (scalarAssociator l E L N i jk ijk hijk' Y).hom := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
    scalarAssociator_pentagon l E L M N Y i j k ij jk ijk hij hjk hijk hijk' K

private noncomputable def normalizedAssociator
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition l Ω Y E L h ⋙ transition l Ω Y L M k ≅
      transition l Ω Y E M (h.trans k) := by
  delta transition
  exact scalarAssociator l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
    (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
    ((coefficientInclusion_laws l Ω).2 E L M h k) Y

attribute [local irreducible] normalizedAssociator

private theorem associator_formula (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    associator l Ω Y E L M h k = normalizedAssociator l Ω Y E L M h k := by
  unfold associator normalizedAssociator
  exact eq_of_heq ((associator_existsUnique l Ω Y E L M h k).exists.choose_spec)

private theorem normalized_pentagon
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) :
    Functor.whiskerRight (normalizedAssociator l Ω Y E L M h k).hom (transition l Ω Y M N m) ≫
        (normalizedAssociator l Ω Y E M N (h.trans k) m).hom =
      (Functor.associator (transition l Ω Y E L h) (transition l Ω Y L M k)
        (transition l Ω Y M N m)).hom ≫
      Functor.whiskerLeft (transition l Ω Y E L h) (normalizedAssociator l Ω Y L M N k m).hom ≫
        (normalizedAssociator l Ω Y E L N h (k.trans m)).hom := by
  delta normalizedAssociator transition
  exact scalarAssociator_pentagon_nat l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (Coefficient.{u} l Ω M) (Coefficient.{u} l Ω N) Y
    (coefficientInclusion l Ω E L h) (coefficientInclusion l Ω L M k)
    (coefficientInclusion l Ω M N m) (coefficientInclusion l Ω E M (h.trans k))
    (coefficientInclusion l Ω L N (k.trans m))
    (coefficientInclusion l Ω E N ((h.trans k).trans m))
    ((coefficientInclusion_laws l Ω).2 E L M h k)
    ((coefficientInclusion_laws l Ω).2 L M N k m)
    ((coefficientInclusion_laws l Ω).2 E M N (h.trans k) m)
    ((coefficientInclusion_laws l Ω).2 E L N h (k.trans m))

attribute [local irreducible] transition

-- Compare whole natural transformations before taking components. This keeps the
-- proof-irrelevant inclusion witnesses out of large functor-object conversions.
private theorem associator_pentagon
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) :
    Functor.whiskerRight (associator l Ω Y E L M h k).hom (transition l Ω Y M N m) ≫
        (associator l Ω Y E M N (h.trans k) m).hom =
      (Functor.associator (transition l Ω Y E L h) (transition l Ω Y L M k)
        (transition l Ω Y M N m)).hom ≫
      Functor.whiskerLeft (transition l Ω Y E L h) (associator l Ω Y L M N k m).hom ≫
        (associator l Ω Y E L N h (k.trans m)).hom := by
  rw [associator_formula l Ω Y E L M h k,
    associator_formula l Ω Y E M N (h.trans k) m,
    associator_formula l Ω Y L M N k m,
    associator_formula l Ω Y E L N h (k.trans m)]
  exact normalized_pentagon l Ω Y E L M N h k m

/-- The normalized tensor associators satisfy the stage-system cocycle.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: equality induction on the composite algebra maps reduces the normalized
scalar pentagon to sfRationalScalar_coherence. The coefficient inclusions compose
by coefficientInclusion_laws. Their chosen associators equal the normalized tensor
comparisons by associator_existsUnique. Apply the natural-transformation pentagon
at K, including repeated fields and identity inclusions. -/
theorem associator_cocycle
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω Y M N m).map
        ((GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k).hom.app K) ≫
        (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E M N (h.trans k) m).hom.app K =
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y L M N k m).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h).obj K) ≫
        (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L N h (k.trans m)).hom.app K :=
            by
  have hc := NatTrans.congr_app (associator_pentagon l Ω Y E L M N h k m) K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using hc

/-- The tensor transitions and associators uniquely determine the stage system.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: take T to be transition and assoc to be associator; associator_cocycle is
precisely the required coherence equation. Conversely the displayed equalities fix
all data fields of StageSystem; the remaining cocycle proof is proof irrelevant. -/
theorem stageSystem_existsUnique
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    :
    ∃! S : StageSystem (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y),
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L), S.T h =
          GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h) ∧
      (∀ (E L M : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (k : L ≤ M),
        HEq (S.assoc h k) (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k)) := by
  exact stage_spec_existsUnique (fun {E L} h ↦ transition l Ω Y E L h)
    (fun {E L M} h k ↦ associator l Ω Y E L M h k)
    (fun h k m K ↦ associator_cocycle l Ω Y _ _ _ _ h k m K)

/-- The stage system with exactly the specified tensor functors and associators.
The uniqueness specification fixes every data field, retaining a small opaque interface
for later elaboration of dependent representative types.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable abbrev stageSystem : StageSystem (Stage l Ω Y) :=
  (stageSystem_existsUnique l Ω Y).exists.choose

/-- The existing tensor functor as a transition of the uniquely fixed stage system.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable abbrev stageTransition (E L : Index l Ω) (h : E ≤ L) :=
  (stageSystem l Ω Y).T h

/-- The specified shift comparison transported by equality of the transition functors.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages). -/
noncomputable instance stageTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition l Ω Y E L h).CommShift ℤ :=
  cast (congrArg (fun F : Stage l Ω Y E ⥤ Stage l Ω Y L ↦ F.CommShift ℤ)
    ((stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E L h).symm)
    (transitionCommShift l Ω Y E L h)

attribute [local irreducible] stageCategory

/-- Exactness of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: stageSystem_existsUnique identifies this functor and its shift comparison
with the specified tensor extension. Apply transitionExact. -/
@[instance]
theorem stageTransition_exact
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h).IsTriangulated := by
  exact exact_cast _ _
    ((stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E L h)
    (transitionCommShift l Ω Y E L h) (transitionExact l Ω Y E L h)

/-- Additivity of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: lem-general-algebraically-closed-coefficient-stages).
Proof: equality of functors with transition reduces the claim to transitionAdditive. -/
@[instance]
theorem stageTransition_additive
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h).Additive := by
  unfold stageTransition
  rw [(stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E L h]
  exact transitionAdditive l Ω Y E L h

end GeneralAlgebraicallyClosedCoefficients
end WeilConjectures
