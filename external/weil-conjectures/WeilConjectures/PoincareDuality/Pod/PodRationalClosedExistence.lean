/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import all WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations

/-! # Existence of the rational normalized partial closed datum

Source: Stacks Project, Tag 08J9; the rational localization step in the
blueprint `lem-pod-derived-automorphism-hom-evaluation`.
(blueprint: lem-pod-rational-closed-existence)

The integral transpose is linear by parameter naturality and tensor bilinearity.
Base change gives the localized transpose and its inverse; tensor-product
induction proves parameter naturality for all localized morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard

section Localization
variable {R : Type*} [CommRing R] {A : Type*} [Category* A]
  [Preadditive A] [Linear R A]

private def extendHomEquiv (p : R)
    (M N X Y : ScalarLocalization R A p) (M₀ N₀ X₀ Y₀ : A)
    (hM : M = ⟨M₀⟩) (hN : N = ⟨N₀⟩) (hX : X = ⟨X₀⟩) (hY : Y = ⟨Y₀⟩)
    (e : (M₀ ⟶ N₀) ≃ₗ[R] (X₀ ⟶ Y₀)) : (M ⟶ N) ≃ₗ[Localization.Away p] (X ⟶ Y) := by
  cases hM
  cases hN
  cases hX
  cases hY
  exact e.baseChange R (Localization.Away p)

private theorem extendHomEquiv_apply (p : R)
    (M N X Y : ScalarLocalization R A p) (M₀ N₀ X₀ Y₀ : A)
    (hM : M = ⟨M₀⟩) (hN : N = ⟨N₀⟩) (hX : X = ⟨X₀⟩) (hY : Y = ⟨Y₀⟩)
    (e : (M₀ ⟶ N₀) ≃ₗ[R] (X₀ ⟶ Y₀))
    (a : Localization.Away p) (f : M₀ ⟶ N₀) (q : M ⟶ N)
    (hq : HEq q (a ⊗ₜ[R] f)) :
    HEq (extendHomEquiv p M N X Y M₀ N₀ X₀ Y₀ hM hN hX hY e q)
      (a ⊗ₜ[R] e f) := by
  cases hM
  cases hN
  cases hX
  cases hY
  cases hq
  rfl

private theorem extendHomEquiv_symm_apply (p : R)
    (M N X Y : ScalarLocalization R A p) (M₀ N₀ X₀ Y₀ : A)
    (hM : M = ⟨M₀⟩) (hN : N = ⟨N₀⟩) (hX : X = ⟨X₀⟩) (hY : Y = ⟨Y₀⟩)
    (e : (M₀ ⟶ N₀) ≃ₗ[R] (X₀ ⟶ Y₀))
    (a : Localization.Away p) (f : X₀ ⟶ Y₀) (q : X ⟶ Y)
    (hq : HEq q (a ⊗ₜ[R] f)) :
    HEq ((extendHomEquiv p M N X Y M₀ N₀ X₀ Y₀ hM hN hX hY e).symm q)
      (a ⊗ₜ[R] e.symm f) := by
  cases hM
  cases hN
  cases hX
  cases hY
  cases hq
  rfl

private theorem localizedHom_induction (p : R)
    (M N : ScalarLocalization R A p) (M₀ N₀ : A)
    (hM : M = ⟨M₀⟩) (hN : N = ⟨N₀⟩)
    (Q : (M ⟶ N) → Prop) (q : M ⟶ N)
    (hz : Q 0)
    (ht : ∀ (a : Localization.Away p) (f : M₀ ⟶ N₀) (q : M ⟶ N),
      HEq q (a ⊗ₜ[R] f) → Q q)
    (ha : ∀ q q', Q q → Q q' → Q (q + q')) : Q q := by
  cases hM
  cases hN
  induction q using TensorProduct.inductionOn with
  | tmul a f => exact ht a f _ HEq.rfl
  | add q q' hq hq' => exact ha q q' hq hq'

private theorem localizedTranspose_naturality (p : R) (T : A × A ⥤ A)
    (F : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (ho : ∀ MN, F.obj MN = ⟨T.obj (MN.1.obj, MN.2.obj)⟩)
    (hm : ∀ L L' M M', ∃ b : (L ⟶ L') →ₗ[Localization.Away p]
        (M ⟶ M') →ₗ[Localization.Away p] (F.obj (L, M) ⟶ F.obj (L', M')),
      (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧
      ∀ (f : L.obj ⟶ L'.obj) (g : M.obj ⟶ M'.obj) (a b' : Localization.Away p),
        HEq (b (a ⊗ₜ[R] f) (b' ⊗ₜ[R] g))
          ((a * b') ⊗ₜ[R] T.map (Prod.mkHom f g)))
    (M N H : ScalarLocalization R A p) (H₀ : A) (hH : H = ⟨H₀⟩)
    (e₀ : ∀ L : A, (T.obj (L, M.obj) ⟶ N.obj) ≃ₗ[R] (L ⟶ H₀))
    (hn : ∀ (L L' : A) (f : L' ⟶ L) (h : T.obj (L, M.obj) ⟶ N.obj),
      e₀ L' (T.map (Prod.mkHom f (𝟙 _)) ≫ h) = f ≫ e₀ L h)
    (e : ∀ L, (F.obj (L, M) ⟶ N) ≃ₗ[Localization.Away p] (L ⟶ H))
    (he : ∀ L (a : Localization.Away p) (f : T.obj (L.obj, M.obj) ⟶ N.obj)
      (q : F.obj (L, M) ⟶ N), HEq q (a ⊗ₜ[R] f) → HEq (e L q) (a ⊗ₜ[R] e₀ L.obj f))
    (L L' : ScalarLocalization R A p) (f : L' ⟶ L) (h : F.obj (L, M) ⟶ N) :
    e L' (F.map (Prod.mkHom f (𝟙 _)) ≫ h) = f ≫ e L h := by
  obtain ⟨b, hb, hbp⟩ := hm L' L M M
  rw [hb]
  have pure (a : Localization.Away p) (f : L'.obj ⟶ L.obj)
      (c : Localization.Away p) (h₀ : T.obj (L.obj, M.obj) ⟶ N.obj)
      (q : F.obj (L, M) ⟶ N) (hq : HEq q (c ⊗ₜ[R] h₀)) :
      e L' (b (a ⊗ₜ[R] f) (𝟙 _) ≫ q) = (a ⊗ₜ[R] f) ≫ e L q := by
    have ht := hbp f (𝟙 M.obj) a 1
    have hc := heq_comp (ho (L', M)) (ho (L, M)) rfl ht hq
    have hl := he L' (c * (a * 1)) (T.map (Prod.mkHom f (𝟙 _)) ≫ h₀)
      (b (a ⊗ₜ[R] f) (𝟙 _) ≫ q)
      (hc.trans (heq_of_eq (ScalarLocalization.composition_tmul R A p _ _ _ _ _ _ _)))
    have hr := heq_comp rfl rfl hH (HEq.rfl : HEq (a ⊗ₜ[R] f) (a ⊗ₜ[R] f)) (he L c h₀ q hq)
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change (c * (a * 1)) ⊗ₜ[R] e₀ L'.obj (T.map (Prod.mkHom f (𝟙 _)) ≫ h₀) =
      ScalarLocalization.composition R A p _ _ _ (c ⊗ₜ[R] e₀ L.obj h₀) (a ⊗ₜ[R] f)
    rw [ScalarLocalization.composition_tmul, mul_one, hn]
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    apply localizedHom_induction p (F.obj (L, M)) N (T.obj (L.obj, M.obj)) N.obj
      (ho (L, M)) rfl _ h
    · simp only [comp_zero, map_zero]
    · exact fun c h₀ q hq ↦ pure a f c h₀ q hq
    · intro q q' hq hq'
      simp only [Preadditive.comp_add, map_add, hq, hq']
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, Preadditive.add_comp, hf, hf']
    exact (Preadditive.add_comp (C := ScalarLocalization R A p) _ _ _
      f f' (e L h)).symm

end Localization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The scalar-localized integral transpose admits a rational partial closed
structure with the prescribed pure-tensor normalization. This is the existence
part of `podRationalClosed_existsUnique`.
Source: Stacks Project, Tag 08J9; the assigned localization normalization in
`lem-pod-derived-automorphism-hom-evaluation` (agent refinement of coefficient transport).
Proof: apply integral parameter naturality to a scalar multiple of the identity.
Integral tensor bilinearity identifies the resulting equation with linearity
of transposition. Tensor this linear equivalence and its inverse with the
localization ring. Transport the endpoints through the recorded tensor and Hom
object equalities. On pure tensors, the naturality equation is the integral
equation multiplied by the two scalars, using the prescribed bilinear tensor
and composition formulas. Tensor-product induction extends it to arbitrary
localized arrows. The inverse equivalence has exactly the displayed pure-tensor
normalization by the base-change formula.
(blueprint: lem-pod-rational-closed-existence). -/
theorem podRationalClosed_exists :
    ∃ S : PodPartialClosed (rationalDerivedTensor l E W)
        (constructibleRationalHomPairs l E W) (rationalDerivedInternalHom l E W),
      ∀ (L : sfRationalConstructibleCategory l E W)
        (P : (constructibleRationalHomPairs l E W).FullSubcategory)
        (f : L.obj ⟶ (constructibleIntegralHom l E W).obj
          (integralPairOfRationalHomPair l E W P))
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        (q : L ⟶ (rationalDerivedInternalHom l E W).obj P),
        HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) →
        HEq ((S.transpose L P).symm q)
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            ((podIntegralClosed l E W).transpose L.obj
              (integralPairOfRationalHomPair l E W P)).symm f) := by
  obtain ⟨β, hβ⟩ := constructibleIntegralTensor_bilinear l E W
  let TI := constructibleIntegralTensor l E W
  let SI := podIntegralClosed l E W
  let I := integralPairOfRationalHomPair l E W
  let T := rationalDerivedTensor l E W
  let H := rationalDerivedInternalHom l E W
  have hT := (rationalDerivedTensor_existsUnique l E W).exists.choose_spec
  have hH := (rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec
  let ei (L : sfIntegralConstructibleCategory l E W)
      (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
      (TI.obj (L, P.obj.1.unop) ⟶ P.obj.2) ≃ₗ[Padic.coefficientExtensionIntegers l E]
        (L ⟶ (constructibleIntegralHom l E W).obj P) := {
    SI.transpose L P with
    map_smul' := by
      intro r f
      have ht : TI.map (Prod.mkHom (r • 𝟙 L) (𝟙 P.obj.1.unop)) = r • 𝟙 _ := by
        rw [← hβ, map_smul, LinearMap.smul_apply, hβ]
        change r • TI.map (𝟙 (L, P.obj.1.unop)) = _
        rw [TI.map_id]
      have hn := SI.parameter_naturality L L P (r • 𝟙 L) f
      rw [ht, Linear.smul_comp, Category.id_comp, Linear.smul_comp,
        Category.id_comp] at hn
      exact hn }
  let e (L : sfRationalConstructibleCategory l E W)
      (P : (constructibleRationalHomPairs l E W).FullSubcategory) :=
    extendHomEquiv (Padic.coefficientExtensionUniformizer l E)
      (T.obj (L, P.obj.1.unop)) P.obj.2 L (H.obj P)
      (TI.obj (L.obj, P.obj.1.unop.obj)) P.obj.2.obj L.obj
      ((constructibleIntegralHom l E W).obj (I P))
      (hT.1 _) rfl rfl (hH.1 P) (ei L.obj (I P))
  have he (L : sfRationalConstructibleCategory l E W)
      (P : (constructibleRationalHomPairs l E W).FullSubcategory)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (f : TI.obj (L.obj, P.obj.1.unop.obj) ⟶ P.obj.2.obj)
      (q : T.obj (L, P.obj.1.unop) ⟶ P.obj.2)
      (hq : HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)) :
      HEq (e L P q) (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] ei L.obj (I P) f) :=
    extendHomEquiv_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _ a f q hq
  refine ⟨{ transpose := fun L P ↦ (e L P).toAddEquiv
            parameter_naturality := ?_ }, ?_⟩
  · intro L L' P f h
    exact localizedTranspose_naturality _ TI T hT.1 hT.2
      P.obj.1.unop P.obj.2 (H.obj P) ((constructibleIntegralHom l E W).obj (I P))
      (hH.1 P) (fun L ↦ ei L (I P))
      (fun L L' f h ↦ SI.parameter_naturality L L' (I P) f h)
      (fun L ↦ e L P) (fun L a f q hq ↦ he L P a f q hq) L L' f h
  · intro L P f a q hq
    exact extendHomEquiv_symm_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _ a f q hq

end WeilConjectures
