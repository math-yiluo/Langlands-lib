/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Comparing derived pullbacks along a factorization through a trivial pullback

Let `Φ, γ, F : X ⟶ X` be endomorphisms of a scheme with `F ≫ γ = Φ`, and suppose that the derived
pullback along `F` is identified with the derived pullback along the identity,
`ε : LF^* ≅ L(𝟙 X)^*`. Then the derived pullbacks along `Φ` and `γ` are identified:
```
          ≅                           ε                          ≅
  LΦ^* ──────▶ Lγ^* ⋙ LF^* ──────────────▶ Lγ^* ⋙ L(𝟙 X)^* ──────▶ Lγ^*
```
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfFactor`). This is how the scheme Frobenius
`Φ` and the geometric Galois Frobenius `γ` of a geometric fibre are compared, `F` being the
absolute Frobenius, which acts as the identity on the étale topos.

The identification is compatible with pullback along a morphism `f : X ⟶ Y` intertwining the
three endomorphisms of `X` with three endomorphisms of `Y`, as soon as the identifications `ε`
of `X` and of `Y` are
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_leftDerivedUpperStarIsoOfFactor`).
This is pure coherence of the composition isomorphisms of derived pullbacks: their
associativity (`AlgebraicGeometry.Etale.leftDerivedUpperStarComp_assoc'_app`) and unit laws
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp_id_left_hom_app`,
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp_id_right_hom_app`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

section Factor

variable {X : Scheme.{u}} {Φ γ F : X ⟶ X} (hF : F ≫ γ = Φ)
  (ε : L((F)^*[A]) ≅ L((𝟙 X)^*[A]))

/-- The identification `LΦ^* ≅ Lγ^*` of the derived pullbacks along endomorphisms `Φ = F ≫ γ`,
given an identification `ε : LF^* ≅ L(𝟙 X)^*`: the composite
`LΦ^* ≅ Lγ^* ⋙ LF^* ≅ Lγ^* ⋙ L(𝟙 X)^* ≅ Lγ^*`. -/
noncomputable def leftDerivedUpperStarIsoOfFactor : L((Φ)^*[A]) ≅ L((γ)^*[A]) :=
  leftDerivedUpperStarComp A F γ Φ hF.symm ≪≫ Functor.isoWhiskerLeft L((γ)^*[A]) ε ≪≫
    (leftDerivedUpperStarComp A (𝟙 X) γ γ (Category.id_comp γ).symm).symm

lemma leftDerivedUpperStarIsoOfFactor_hom_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarIsoOfFactor A hF ε).hom.app K =
      (leftDerivedUpperStarComp A F γ Φ hF.symm).hom.app K ≫
        ε.hom.app (L((γ)^*[A]).obj K) ≫
          (leftDerivedUpperStarComp A (𝟙 X) γ γ (Category.id_comp γ).symm).inv.app K :=
  rfl

end Factor

section Compatibility

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {ΦX γX FX : X ⟶ X} (hX : FX ≫ γX = ΦX) (εX : L((FX)^*[A]) ≅ L((𝟙 X)^*[A]))
  {ΦY γY FY : Y ⟶ Y} (hY : FY ≫ γY = ΦY) (εY : L((FY)^*[A]) ≅ L((𝟙 Y)^*[A]))
  (hΦ : ΦX ≫ f = f ≫ ΦY) (hγ : γX ≫ f = f ≫ γY) (hFf : FX ≫ f = f ≫ FY)

/-- **Compatibility of `leftDerivedUpperStarIsoOfFactor` with pullback.** Let `f : X ⟶ Y`
intertwine endomorphisms `ΦX = FX ≫ γX` of `X` with endomorphisms `ΦY = FY ≫ γY` of `Y`, and
suppose that the identifications `εX : LFX^* ≅ L(𝟙 X)^*` and `εY : LFY^* ≅ L(𝟙 Y)^*` are
compatible with `f`: the two identifications `L(FX ≫ f)^* ≅ Lf^*`,
```
L(FX ≫ f)^* ≅ LFY^* ⋙ Lf^* ≅ L(𝟙 Y)^* ⋙ Lf^* ≅ Lf^*   (through `εY`),
L(FX ≫ f)^* ≅ Lf^* ⋙ LFX^* ≅ Lf^* ⋙ L(𝟙 X)^* ≅ Lf^*   (through `εX`),
```
agree. Then the square
```
Lf^* LΦY^* K ──Lf^* κY──▶ Lf^* LγY^* K
     │ ≅                       │ ≅
     ▼                         ▼
LΦX^* Lf^* K ────κX─────▶ LγX^* Lf^* K
```
commutes, `κ` being `AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfFactor` and the vertical
arrows the identifications of the derived pullbacks along `ΦX ≫ f = f ≫ ΦY` and
`γX ≫ f = f ≫ γY`. -/
lemma leftDerivedUpperStar_map_leftDerivedUpperStarIsoOfFactor
    (hε : ∀ M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A),
      (leftDerivedUpperStarComp A f FY (FX ≫ f) hFf).hom.app M ≫
          L((f)^*[A]).map (εY.hom.app M) ≫
            (leftDerivedUpperStarComp A f (𝟙 Y) f (Category.comp_id f).symm).inv.app M =
        (leftDerivedUpperStarComp A FX f (FX ≫ f) rfl).hom.app M ≫
          εX.hom.app (L((f)^*[A]).obj M) ≫
            (leftDerivedUpperStarComp A (𝟙 X) f f (Category.id_comp f).symm).inv.app M)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((f)^*[A]).map ((leftDerivedUpperStarIsoOfFactor A hY εY).hom.app K) ≫
        (leftDerivedUpperStarComp A f γY (γX ≫ f) hγ).inv.app K ≫
          (leftDerivedUpperStarComp A γX f (γX ≫ f) rfl).hom.app K =
      (leftDerivedUpperStarComp A f ΦY (ΦX ≫ f) hΦ).inv.app K ≫
        (leftDerivedUpperStarComp A ΦX f (ΦX ≫ f) rfl).hom.app K ≫
          (leftDerivedUpperStarIsoOfFactor A hX εX).hom.app (L((f)^*[A]).obj K) := by
  have hP : ΦX ≫ f = (FX ≫ f) ≫ γY := by rw [← hX, Category.assoc, Category.assoc, hγ]
  set N := L((γY)^*[A]).obj K
  set θ := (leftDerivedUpperStarComp A f γY (γX ≫ f) hγ).inv.app K ≫
    (leftDerivedUpperStarComp A γX f (γX ≫ f) rfl).hom.app K with hθ
  -- associativity for `f, FY, γY`, for `FX, f, γY` and for `FX, γX, f`
  have a₁ := leftDerivedUpperStarComp_assoc'_app A f FY γY (FX ≫ f) ΦY (ΦX ≫ f) hFf hY.symm hP K
  have a₂ := leftDerivedUpperStarComp_assoc'_app A FX f γY (FX ≫ f) (γX ≫ f) (ΦX ≫ f) rfl hγ
    hP K
  have a₃ := leftDerivedUpperStarComp_assoc'_app A FX γX f ΦX (γX ≫ f) (ΦX ≫ f) hX.symm rfl rfl
    K
  -- the compatibility of the `ε`s at `N = LγY^* K`
  have b : (leftDerivedUpperStarComp A f FY (FX ≫ f) hFf).hom.app N ≫
      L((f)^*[A]).map (εY.hom.app N) =
      (leftDerivedUpperStarComp A FX f (FX ≫ f) rfl).hom.app N ≫
        εX.hom.app (L((f)^*[A]).obj N) ≫
          (leftDerivedUpperStarComp A (𝟙 X) f f (Category.id_comp f).symm).inv.app N ≫
            (leftDerivedUpperStarComp A f (𝟙 Y) f (Category.comp_id f).symm).hom.app N := by
    rw [← cancel_mono
      ((leftDerivedUpperStarComp A f (𝟙 Y) f (Category.comp_id f).symm).inv.app N)]
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using hε N
  -- the unit laws
  have u₂ := leftDerivedUpperStarComp_id_right_hom_app A f N
  have hi : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W)
      (M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)),
      (leftDerivedUpperStarComp A (𝟙 Z) g g (Category.id_comp g).symm).inv.app M =
        (leftDerivedUpperStarId A Z).hom.app (L((g)^*[A]).obj M) := fun g M ↦ by
    rw [← cancel_epi ((leftDerivedUpperStarComp A (𝟙 _) g g (Category.id_comp g).symm).hom.app M),
      Iso.hom_inv_id_app, leftDerivedUpperStarComp_id_left_hom_app]
  -- coherence on the right of `εX`
  have c₂ : (leftDerivedUpperStarComp A (𝟙 X) f f (Category.id_comp f).symm).inv.app N ≫
      (leftDerivedUpperStarComp A f (𝟙 Y) f (Category.comp_id f).symm).hom.app N ≫
        L((f)^*[A]).map
          ((leftDerivedUpperStarComp A (𝟙 Y) γY γY (Category.id_comp γY).symm).inv.app K) ≫ θ =
      L((𝟙 X)^*[A]).map θ ≫
        (leftDerivedUpperStarComp A (𝟙 X) γX γX (Category.id_comp γX).symm).inv.app
          (L((f)^*[A]).obj K) := by
    rw [hi f N, hi γY K, hi γX, reassoc_of% u₂]
    exact ((leftDerivedUpperStarId A X).hom.naturality θ).symm
  -- coherence on the left of `εX`
  have c₁ : (leftDerivedUpperStarComp A (FX ≫ f) γY (ΦX ≫ f) hP).hom.app K ≫
      (leftDerivedUpperStarComp A FX f (FX ≫ f) rfl).hom.app N ≫ L((FX)^*[A]).map θ =
      (leftDerivedUpperStarComp A ΦX f (ΦX ≫ f) rfl).hom.app K ≫
        (leftDerivedUpperStarComp A FX γX ΦX hX.symm).hom.app (L((f)^*[A]).obj K) := by
    rw [← reassoc_of% a₂, hθ, Functor.map_comp, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, a₃]
  rw [← cancel_epi ((leftDerivedUpperStarComp A f ΦY (ΦX ≫ f) hΦ).hom.app K),
    Iso.hom_inv_id_app_assoc]
  simp only [leftDerivedUpperStarIsoOfFactor_hom_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% a₁, reassoc_of% b, c₂, ← εX.hom.naturality_assoc, reassoc_of% c₁]
  rfl

end Compatibility

end Etale

end AlgebraicGeometry
