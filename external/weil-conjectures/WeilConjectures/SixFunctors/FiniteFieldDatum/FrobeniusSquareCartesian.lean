/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The Cartesian Frobenius square

Source: Deligne, Weil II, (1.1.10)(i), (1.1.11), pp. 151--152, and (1.1.14), p. 153;
Weil conjectures blueprint, `def:weil-direct-image-object`, Cartesian Frobenius square
(blueprint: lem-weil-frobenius-square-cartesian).

The scalar extensions and their morphism use the chosen categorical pullback. The two
horizontal maps use the dependency's unrestricted `galoisMap`, since the models need
not be of finite type. `IsPullback` asserts precisely that the canonical comparison
`(g_X, f)` into the chosen pullback is invertible, including its projection equations.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- Geometric Frobenius commutes with scalar extension of a morphism, and its square
is Cartesian, with the displayed inverse coefficient actions. The last two clauses
identify the scalar extension of the base with `Spec k` by its second projection and
state the Cartesian structure square over `Spec k`.

Source: Deligne, Weil II, (1.1.10)(i), (1.1.11), pp. 151--152, and (1.1.14), p. 153;
blueprint `def:weil-direct-image-object`
(blueprint: lem-weil-frobenius-square-cartesian).

Proof:
1. The geometric field Frobenius and its inverse fix the base field. Contravariant
   functoriality of `Spec` gives inverse endomorphisms of `Spec k` over `Spec k₀`.
2. For each model, the induced fibre-product maps fix the first projection and act
   by these two `Spec` maps on the second. The fibre-product universal property
   identifies both composites with the identity, giving the stated inverses.
3. The scalar extension of `f₀` commutes with these maps: both composites have first
   projection `f₀` after the first projection and second projection `Spec γ` after
   the second. Uniqueness gives the displayed commutativity equation.
4. In `P = X ×_{f,Y,g_Y} Y`, let `r : P ⟶ X` be the first projection. The inverse
   of the comparison `(g_X, f)` is `r ≫ g_X⁻¹`. Commutativity, the inverse identities,
   and pullback uniqueness show that the two composites are identities.
5. For the identity structure morphism of `Spec k₀`, the second projection of its
   scalar extension is an isomorphism with inverse `(Spec ι, id)`. The projection
   identities identify the coefficient action with `Spec γ`. The same calculation
   in step 4 gives the structure square of any model over `Spec k`.
The dependencies used are `def-weil-finite-field-fiber`, `prose-10-19`,
`def-weil-affine-spectrum`, `def-pc-fibre-product` and `def-weil-scheme-over-base`. -/
theorem frobenius_square_cartesian (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))) (f₀ : X₀ ⟶ Y₀) :
    D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _) ≫
      D.galoisMap X₀.hom ((@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _).symm) = 𝟙 _ ∧
    D.galoisMap X₀.hom ((@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _).symm) ≫
      D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _) = 𝟙 _ ∧
    D.galoisMap Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _) ≫
      D.galoisMap Y₀.hom ((@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _).symm) = 𝟙 _ ∧
    D.galoisMap Y₀.hom ((@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _).symm) ≫
      D.galoisMap Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _) = 𝟙 _ ∧
    D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _) ≫
      ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left =
      ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left ≫
        D.galoisMap Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _) ∧
    IsPullback
      (D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _))
      ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
      ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
      (D.galoisMap Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _)) ∧
    IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of D.k₀)))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
    IsPullback
      (D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _))
      (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      (Spec.map (CommRingCat.ofHom
      (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _).toRingHom)) := by
  let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let f := ((Over.pullback b).map f₀).left
  have hX := D.galoisMap_inverse X₀.hom σ
  have hY := D.galoisMap_inverse Y₀.hom σ
  have hcomm : D.galoisMap X₀.hom σ ≫ f = f ≫ D.galoisMap Y₀.hom σ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, f, Over.pullback_map_left, pullback.lift_fst]
      rw [← Category.assoc, (D.galoisMap_projections X₀.hom σ).1,
        (D.galoisMap_projections Y₀.hom σ).1]
      simp only [b, pullback.lift_fst]
    · simp only [Category.assoc, f, Over.pullback_map_left, pullback.lift_snd]
      rw [(D.galoisMap_projections X₀.hom σ).2,
        (D.galoisMap_projections Y₀.hom σ).2]
      simp [b]
  let eX : _ ≅ _ := ⟨D.galoisMap X₀.hom σ, D.galoisMap X₀.hom σ.symm, hX.1, hX.2⟩
  let eY : _ ≅ _ := ⟨D.galoisMap Y₀.hom σ, D.galoisMap Y₀.hom σ.symm, hY.1, hY.2⟩
  have : IsIso (D.galoisMap X₀.hom σ) := eX.isIso_hom
  have : IsIso (D.galoisMap Y₀.hom σ) := eY.isIso_hom
  refine ⟨hX.1, hX.2, hY.1, hY.2, hcomm, IsPullback.of_horiz_isIso ⟨hcomm⟩,
    inferInstance, ?_⟩
  change IsPullback (baseChangeMap X₀.hom _) _ _ _
  exact isPullback_baseChangeMap X₀.hom _

end WeilConjectures.FiniteFieldDatum
