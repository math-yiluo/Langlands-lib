/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import Mathlib.CategoryTheory.Sites.Limits

/-! # The completed coefficient structural map

Source: Stacks Tags 0D6E and 0A07: constant coefficients and direct image of limits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward

private instance coefficientSheafify (W : Scheme.{t}) :
    HasSheafify (ProEt.topology W) CommRingCat.{max u (t + 1)} :=
  integralCoefficientRingSheafify.{t, u} W

variable {X Y : Scheme.{t}} (f : X ⟶ Y)

private def commConstantPush (B : CommRingCat.{max u (t + 1)}) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj B ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj B) :=
  ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj B) _).symm
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)))

private theorem commConstantPush_naturality
    {B C : CommRingCat.{max u (t + 1)}} (h : B ⟶ C) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map h ≫
        commConstantPush.{t, u} f C =
      commConstantPush.{t, u} f B ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map h) := by
  apply (Adjunction.homEquiv_naturality_right_square_iff
    (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)})
    ((Functor.const Y.ProEtᵒᵖ).map h) _ _ _).mpr
  apply NatTrans.ext
  funext U
  exact congrArg (fun k ↦ k.app ((proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map h))

private theorem constantPush_naturality
    {B C : CommRingCat.{max u (t + 1)}} (h : B ⟶ C) :
    (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map h) ≫
        constantPush.{t, u} f C =
      constantPush.{t, u} f B ≫ (ringPush.{t, u} f).map
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map h)) := by
  have hh := congrArg ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map)
    (commConstantPush_naturality.{t, u} f h)
  ext U x
  exact congrArg (fun z ↦ z.hom.app U x) hh

private instance ringPush_limits : PreservesLimitsOfShape ℕᵒᵖ (ringPush.{t, u} f) := by
  let V := sheafToPresheaf (ProEt.topology Y) RingCat.{max u (t + 1)}
  have : PreservesLimitsOfShape ℕᵒᵖ (ringPush.{t, u} f ⋙ V) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology X) RingCat.{max u (t + 1)} ⋙
        (Functor.whiskeringLeft Y.ProEtᵒᵖ X.ProEtᵒᵖ RingCat.{max u (t + 1)}).obj
          (proEtaleBaseChange f).op))
  exact preservesLimitsOfShape_of_reflects_of_preserves (ringPush.{t, u} f) V

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finiteStructure_transition (n : ℕ) :
    finiteStructure l E f (n + 1) ≫
        (ringPush.{t, u} f).map (integralCoefficientSheafTransition l E X n) =
      integralCoefficientSheafTransition l E Y n ≫ finiteStructure l E f n := by
  let h : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  exact (constantPush_naturality.{t, u} f h).symm

private theorem structure_constant
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n) :
    integralConstantToCompletionOfUniverses l E Y ≫ c =
      constantStructure l E f ≫
        (ringPush.{t, u} f).map (integralConstantToCompletionOfUniverses l E X) := by
  let G := ringPush.{t, u} f
  apply (isLimitOfPreserves G (limit.isLimit
    (integralCoefficientSheafSystem l E X))).hom_ext
  intro n
  change (integralConstantToCompletionOfUniverses l E Y ≫ c) ≫
      G.map (projection l E X n.unop) =
    (constantStructure l E f ≫ G.map (integralConstantToCompletionOfUniverses l E X)) ≫
      G.map (projection l E X n.unop)
  rw [Category.assoc, hc, ← Category.assoc]
  rw [Category.assoc (constantStructure l E f), ← G.map_comp]
  have hq (W : Scheme.{t}) : integralConstantToCompletionOfUniverses l E W ≫
      projection l E W n.unop = integralConstantQuotientOfUniverses l E W n.unop :=
    limit.lift_π _ _
  rw [hq Y, hq X]
  let h : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n.unop + 1))) :=
    CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  exact constantPush_naturality.{t, u} f h

/-- The completed structural map is uniquely fixed by the finite constant-section maps.

Source: Stacks sites-cohomology.tex Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-structure-map).
Proof: first transpose naturality of the sheafification unit through the constant-sheaf
adjunction. Forgetting commutativity gives naturality of the specified constant-section
maps. Apply this to the actual quotient transition homomorphisms. The limit projections
on Y followed by these finite maps are therefore a cone over the direct image of the
finite tower on X. Ring-sheaf direct image preserves limits: after the conservative
sheaf-to-presheaf functor it is precomposition, which preserves limits pointwise.
The universal lift of this cone gives c and its finite projection equations. Two such
maps agree after every projection of the preserved limit, so are equal. For the constant
integral square, test the two composites at each finite projection. The constant-to-limit
map is the lift of its actual quotient cone; naturality for that quotient map identifies
the resulting composites. Thus the uniquely constructed map also makes this square
commute. This argument
uses all positive exponents and the actual quotient transitions. On empty sites the
same limit universal property applies; it also covers identity scheme maps. -/
theorem completedStructure_existsUnique :
    ∃! c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X),
      (∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
        projection l E Y n ≫ finiteStructure l E f n) ∧
      integralConstantToCompletionOfUniverses l E Y ≫ c =
        constantStructure l E f ≫
          (ringPush.{t, u} f).map (integralConstantToCompletionOfUniverses l E X) := by
  let G := ringPush.{t, u} f
  let D := integralCoefficientSheafSystem l E X
  let γ (n : ℕ) := projection l E Y n ≫ finiteStructure l E f n
  let T : Cone (D ⋙ G) :=
    { pt := R l E Y
      π := NatTrans.ofOpSequence γ (by
        intro n
        simp only [Functor.const_obj_map, D, Functor.comp_map,
          integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
        symm
        change γ (n + 1) ≫ G.map (integralCoefficientSheafTransition l E X n) = γ n
        dsimp only [γ]
        rw [Category.assoc, finiteStructure_transition]
        rw [← Category.assoc]
        congr 1
        simpa only [projection, integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          limit.w (integralCoefficientSheafSystem l E Y) (homOfLE n.le_succ).op) }
  let h := isLimitOfPreserves G (limit.isLimit D)
  refine ⟨h.lift T, ⟨?_, ?_⟩, ?_⟩
  · intro n
    exact h.fac T (op n)
  · exact structure_constant (l := l) (E := E) (f := f) (h.lift T)
      (fun n ↦ h.fac T (op n))
  · intro c hc
    apply h.hom_ext
    intro n
    exact (hc.1 n.unop).trans (h.fac T n).symm

end WeilConjectures.CompletedCoefficientPushforward
