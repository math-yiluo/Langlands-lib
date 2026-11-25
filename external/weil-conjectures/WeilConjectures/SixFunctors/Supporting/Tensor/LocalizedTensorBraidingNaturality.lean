/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso

/-! # Naturality of the localized tensor braiding

Source: Stacks 06YS and 0941; derived pullback tensor isomorphism, step 11
(blueprint: lem-coef-localized-tensor-braiding-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

private theorem localizedBraiding_natural
    {R : Type*} [CommRing R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    (p : R) (T : A × A ⥤ A) (bi : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (hn : ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (bi M' N').hom =
        (bi M N).hom ≫ T.map (Prod.mkHom g f))
    (F : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (br : ∀ M N, F.obj (M, N) ≅ F.obj (N, M))
    (ho : ∀ MN, F.obj MN = ⟨T.obj (MN.1.obj, MN.2.obj)⟩)
    (hm : ∀ M M' N N', ∃ b : (M ⟶ M') →ₗ[Localization.Away p]
        (N ⟶ N') →ₗ[Localization.Away p] (F.obj (M, N) ⟶ F.obj (M', N')),
      (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (a b' : Localization.Away p),
        HEq (b (a ⊗ₜ[R] f) (b' ⊗ₜ[R] g))
          ((a * b') ⊗ₜ[R] T.map (Prod.mkHom f g)))
    (hb : ∀ M N, HEq (br M N).hom
      ((ScalarLocalization.localization R A p).map (bi M.obj N.obj).hom)) :
    ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
      F.map (Prod.mkHom f g) ≫ (br M' N').hom =
        (br M N).hom ≫ F.map (Prod.mkHom g f) := by
  intro M M' N N' f g
  obtain ⟨b, he, hp⟩ := hm M M' N N'
  obtain ⟨b', he', hp'⟩ := hm N N' M M'
  rw [he, he']
  have ht (a : Localization.Away p) (f : M.obj ⟶ M'.obj)
      (c : Localization.Away p) (g : N.obj ⟶ N'.obj) :
      b (a ⊗ₜ[R] f) (c ⊗ₜ[R] g) ≫ (br M' N').hom =
        (br M N).hom ≫ b' (c ⊗ₜ[R] g) (a ⊗ₜ[R] f) := by
    have hl := heq_comp (ho (M, N)) (ho (M', N')) (ho (N', M'))
      (hp f g a c) (hb M' N')
    have hr := heq_comp (ho (M, N)) (ho (N, M)) (ho (N', M'))
      (hb M N) (hp' g f c a)
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ScalarLocalization.composition R A p _ _ _
        (1 ⊗ₜ[R] (bi M'.obj N'.obj).hom)
        ((a * c) ⊗ₜ[R] T.map (Prod.mkHom f g)) =
      ScalarLocalization.composition R A p _ _ _
        ((c * a) ⊗ₜ[R] T.map (Prod.mkHom g f))
        (1 ⊗ₜ[R] (bi M.obj N.obj).hom)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      one_mul, mul_one, mul_comm c a, hn]
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | tmul c g => exact ht a f c g
    | add g g' hg hg' =>
      simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
        Preadditive.comp_add, hg, hg']
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
      Preadditive.comp_add, hf, hf']

/-- The normalized rational Koszul symmetry is natural for all rational arrows.
Source: Stacks 06YS and 0941; derived-pullback-tensor-iso, proof step 11.
Proof: the completed integral braiding is obtained from the natural system
braiding by the normalized reduction/tensor comparison and derived limit.
The coherent reduction counit equation and uniqueness identify this natural
map with pullbackTensorIntegralBraiding. Thus it is natural integrally.
The rational braiding is its localization, by its defining normalization.
For pure-tensor arrows a tensor f and b tensor g, rational tensor bilinearity
and localized composition make both sides a*b times integral naturality.
Tensor-product induction in both arrows proves the equality for arbitrary
sums. The object equalities in rationalDerivedTensor_existsUnique identify
all endpoints; transporting along them preserves the equality. Coefficients
have degree zero, so this preserves the specified Koszul sign.
(blueprint: lem-coef-localized-tensor-braiding-naturality). -/
theorem localizedTensorBraiding_naturality
    (hn : ∀ M M' N N' : sfIntegralConstructibleCategory l E W,
      ∀ (f : M ⟶ M') (g : N ⟶ N'),
      (constructibleIntegralTensor l E W).map (Prod.mkHom f g) ≫
          (pullbackTensorIntegralBraiding l E W M' N').hom =
        (pullbackTensorIntegralBraiding l E W M N).hom ≫
          (constructibleIntegralTensor l E W).map (Prod.mkHom g f))
    (M M' N N' : sfRationalConstructibleCategory l E W) (f : M ⟶ M') (g : N ⟶ N') :
    (rationalDerivedTensor l E W).map (Prod.mkHom f g) ≫
        (pullbackTensorRationalBraiding l E W M' N').hom =
      (pullbackTensorRationalBraiding l E W M N).hom ≫
        (rationalDerivedTensor l E W).map (Prod.mkHom g f) := by
  exact localizedBraiding_natural
    (R := Padic.coefficientExtensionIntegers l E)
    (A := sfIntegralConstructibleCategory l E W) _ (constructibleIntegralTensor l E W)
    (pullbackTensorIntegralBraiding l E W) hn (rationalDerivedTensor l E W)
    (pullbackTensorRationalBraiding l E W)
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2
    (fun M N ↦ (pullbackTensorRationalBraiding_existsUnique l E W M N).exists.choose_spec)
    M M' N N' f g

end WeilConjectures
