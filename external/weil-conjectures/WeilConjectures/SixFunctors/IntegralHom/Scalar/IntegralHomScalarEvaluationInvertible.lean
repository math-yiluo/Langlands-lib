/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.CategoryTheory.Monoidal.Closed.DualizableCoefficientHomAction
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionDualizableCoefficient
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionTensorAssociativity

/-! # Invertibility of the scalar transpose of reduced evaluation

Source: the finite-free argument and extension-restriction adjunction of
`lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] HasDerivedCategory.standard RingedDerivedNative.monoidal

-- Independent coefficient universes require extra elaboration of localization instances.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The completed-ring transpose of scalar-reduced evaluation is invertible.
This is a scalar assertion with no chosen representatives and no signed chain map.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2;
Stacks Tags 07A4, 07A6, 08J7 and 08J9.
(blueprint: lem-sf-integral-hom-scalar-evaluation-invertible).

Proof: the two-term resolution of the restricted quotient unit has dualizable
terms, so its localization is dualizable. The coefficient-resolution comparison
identifies restricted reduction B=UF with tensor by this coefficient; evaluating
at the unit shows B(unit) is dualizable. The normalized tensor mate p is an
invertible associative tensor strength. Its value at (X,unit), followed by the
right unitor, identifies B with tensor by B(unit), compatibly with p. For a left
dual D of B(unit), conjugate the associator between the two composites of the
coefficient-duality and tensor-Hom adjunctions. The resulting right-adjoint
isomorphism is exactly the evaluation transpose. Transport the tensor-Hom
adjunction along the constructed native tensor comparison and cancel its inverse
maps in the counit. Finally scalar-adjunction naturality combines p with B of
evaluation and gives the displayed map. The middle scalar counit is precisely
that in the definition of p. No perfection of K or L is used. The zero quotient
and empty site satisfy the same argument. -/
theorem scalar_reduced_evaluation_transpose_isIso
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let U := scalarReductionDerivedRestriction l E Y n
    let F := integralDerivedReduction l E Y D hl n
    let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
    let H := (hom.{t, u} Y R).obj (op K, L)
    let X := U.obj (F.obj H)
    IsIso ((a.adjunction K).homEquiv X (U.obj (F.obj L))
      (adj.homEquiv (a.tensor.obj (K, X)) (F.obj L)
        (m.mu.hom.app (K, X) ≫
          m.target.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj H))) ≫
          m.mu.inv.app (K, H) ≫ F.map ((a.adjunction K).counit.app L)))) := by
  classical
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let R := completedIntegralCommRingSheaf l E Y D hl
  let : MonoidalCategory (completedIntegralDerivedCategory l E Y D hl) :=
    by with_unfolding_all exact
      RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J R
  let : SymmetricCategory (completedIntegralDerivedCategory l E Y D hl) :=
    by with_unfolding_all exact
      RingedDerivedNative.symmetric.{t + 1, t, u, max u (t + 1) + 1} J R
  let B : completedIntegralDerivedCategory l E Y D hl ⥤
      completedIntegralDerivedCategory l E Y D hl :=
    integralDerivedReduction l E Y D hl n ⋙ scalarReductionDerivedRestriction l E Y n
  let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
  let H : completedIntegralDerivedCategory l E Y D hl ⥤
      completedIntegralDerivedCategory l E Y D hl :=
    (Functor.curry.obj (hom.{t, u} Y R)).obj (op K)
  let e : a.tensor ≅ tensor (completedIntegralDerivedCategory l E Y D hl) := by
    with_unfolding_all exact tensorPresentationNativeIso Y R a
  have ha := reductionTensorStrength_associativity l E Y D hl a n m
  let p := nativeScalarTensorStrength
        (C := completedIntegralDerivedCategory l E Y D hl) a.tensor m.target.tensor adj m.mu e
  have hn (X X' V V' : completedIntegralDerivedCategory l E Y D hl)
      (f : X ⟶ X') (g : V ⟶ V') :
      (f ⊗ₘ B.map g) ≫ p.app (X', V') = p.app (X, V) ≫ B.map (f ⊗ₘ g) :=
    p.naturality (Prod.mkHom f g)
  have hi (X V : completedIntegralDerivedCategory l E Y D hl) :
      IsIso (p.app (X, V)) := by
    have := reductionTensorStrength_isIso l E Y D hl a n m X V
    dsimp only [p, nativeScalarTensorStrength, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  let : ∀ X V, IsIso (p.app (X, V)) := hi
  have hc := integralReduction_dualizable_coefficient l E Y D hl n
  dsimp only at hc
  rcases hc with ⟨N, hN, ⟨r⟩⟩
  have hunit : IsDualizable (B.obj (𝟙_ (completedIntegralDerivedCategory l E Y D hl))) :=
    IsDualizable.of_iso ((r.app (𝟙_ _)) ≪≫ λ_ N).symm hN
  let := hunit.some
  let D' := (B.obj (𝟙_ (completedIntegralDerivedCategory l E Y D hl)))ᘁ
  let : ExactPairing D' (B.obj (𝟙_ _)) :=
    BraidedCategory.exactPairing_swap _ _
  let eK : (Functor.curry.obj a.tensor).obj K ≅
      tensorLeft (C := completedIntegralDerivedCategory l E Y D hl) K :=
    NatIso.ofComponents (fun V ↦ e.app (K, V)) (by
      intro V V' f
      change a.tensor.map (Prod.mkHom (𝟙 K) f) ≫ e.hom.app (K, V') =
        e.hom.app (K, V) ≫ K ◁ f
      simpa only [tensor_map, id_tensorHom] using
        e.hom.naturality (Prod.mkHom (𝟙 K) f))
  let ad := (a.adjunction K).ofNatIsoLeft eK
  have h : IsIso (ad.homEquiv (B.obj (H.obj L)) (B.obj L)
      (p.app (K, H.obj L) ≫ B.map (ad.counit.app L))) :=
    MonoidalClosed.isIso_transpose_of_strength B (fun X V ↦ p.app (X, V)) hn ha K ad L D'
  have he : ad.homEquiv (B.obj (H.obj L)) (B.obj L)
      (p.app (K, H.obj L) ≫ B.map (ad.counit.app L)) =
      (a.adjunction K).homEquiv (B.obj (H.obj L)) (B.obj L)
        ((scalarTensorStrength a.tensor m.target.tensor adj m.mu).app (K, H.obj L) ≫
          B.map ((a.adjunction K).counit.app L)) := by
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
    congr 1
    change e.hom.app (K, B.obj (H.obj L)) ≫
        (e.inv.app (K, B.obj (H.obj L)) ≫
          (scalarTensorStrength a.tensor m.target.tensor adj m.mu).app (K, H.obj L) ≫
            B.map (e.hom.app (K, H.obj L))) ≫
          B.map (e.inv.app (K, H.obj L) ≫ (a.adjunction K).counit.app L) = _
    rw [Category.assoc, Iso.hom_inv_id_app_assoc, B.map_comp]
    simp only [Category.assoc]
    rw [← B.map_comp_assoc, Iso.hom_inv_id_app, B.map_id, Category.id_comp]
  rw [he, scalarTensorStrength_app] at h
  change IsIso ((a.adjunction K).homEquiv (B.obj (H.obj L)) (B.obj L)
    (adj.homEquiv _ _ _ ≫ (scalarReductionDerivedRestriction l E Y n).map
      ((integralDerivedReduction l E Y D hl n).map ((a.adjunction K).counit.app L)))) at h
  rw [← adj.homEquiv_naturality_right] at h
  simpa only [B, H, adj, Functor.comp_obj, Functor.curry_obj_obj_obj,
    integralDerivedReduction, Category.assoc] using h

end WeilConjectures.IntegralHom
