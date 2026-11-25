/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DoubleDual
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The double-dual morphism under a proper push-forward

This file proves blueprint `lemma-internal-adjunction-two-exchange-formulas--4`. For a proper
`f : X ⟶ Y`, the morphism `Rf_* δ_K` is identified with `δ_{Rf_* K}`; in particular one is an
isomorphism if and only if the other is.

## Main statements

- `CategoryTheory.Adjunction.isIso_dualComparison_of_isIso_projection`: let `F ⊣ G` with `F`
  oplax monoidal and compatible with the braidings, and let `G ⊣ Q'`. If the projection maps
  `G N ⊗ T ⟶ G (N ⊗ F T)` are isomorphisms, the dual comparison
  `G [M, Q' W'] ⟶ [G M, G Q' W'] ⟶ [G M, W']` is an isomorphism. This holds by Yoneda: under
  the adjunctions it is precomposition with the projection map.
- `CategoryTheory.Adjunction.isIso_map_toIhomIhom_iff_of_isIso_projection`,
  `CategoryTheory.Adjunction.nonempty_arrowIso_map_toIhomIhom_of_isIso_projection`: hence
  `G δ_M ≅ δ_{G M}` as arrows (`CategoryTheory.MonoidalClosed.mapToIhomIhomArrowIso`).
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff`,
  `AlgebraicGeometry.Etale.nonempty_arrowIso_rightDerivedLowerStar_map_verdierDualDoubleDual`
  (`lemma-internal-adjunction-two-exchange-formulas--4`, general coefficients): for proper `f`,
  given the braided axiom for `Lf^*`, the projection formula for `Rf_*` and `Rf^! ω_Y ≅ ω_X`,
  `Rf_* δ_K ≅ δ_{Rf_* K}`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff_of_finite`:
  the case of a finite coefficient ring, where the projection formula and `Rf^! ω_Y ≅ ω_X` are
  known.

## Implementation notes

The comparison used is the canonical one, `Rf_* RHom(K, ω_X) ⟶ RHom(Rf_* K, Rf_* ω_X) ⟶
RHom(Rf_* K, ω_Y)`. It is built from the lax monoidal structure of `Rf_*` as the right adjoint
of `Lf^*` (`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`) and the counit of
`Rf_* ≅ Rf_! ⊣ Rf^!`. The repository's Verdier exchange `derivedHomRightDerivedLowerShriekIso`
is not used, so no self-duality of that isomorphism is needed. `Rf_*` is lax braided as soon
as `Lf^*` is (`CategoryTheory.Adjunction.rightAdjointLaxBraidedOfδ`). The braided axiom for
`Lf^*` is the hypothesis `hbr`, proved as `AlgebraicGeometry.Etale.leftDerivedUpperStarBraided`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
  Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.OplaxMonoidal]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4` (auxiliary): the right adjoint of
an oplax monoidal functor compatible with the braidings is lax braided, for the lax monoidal
structure `CategoryTheory.Adjunction.rightAdjointLaxMonoidal`. -/
@[instance_reducible]
def rightAdjointLaxBraidedOfδ
    (h : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) :
    G.LaxBraided :=
  letI := adj.rightAdjointLaxMonoidal
  { braided X Y := by
      rw [rightAdjointLaxMonoidal_μ, rightAdjointLaxMonoidal_μ,
        ← homEquiv_naturality_right, ← homEquiv_naturality_left]
      congr 1
      rw [Category.assoc, BraidedCategory.braiding_naturality, reassoc_of% (h _ _)] }

variable [MonoidalClosed C] [MonoidalClosed D]

omit [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D] in
/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4` (auxiliary): the projection map
`G M ⊗ T ⟶ G (M ⊗ F T)` built from the lax monoidal structure of the right adjoint `G` is the
transpose of `δ ≫ ε ▷ F T`, the form of `CategoryTheory.Adjunction.rightAdjointProjectionMap`. -/
lemma whiskerLeft_unit_comp_rightAdjointLaxMonoidal_μ (M : D) (T : C) :
    letI := adj.rightAdjointLaxMonoidal
    G.obj M ◁ adj.unit.app T ≫ μ G M (F.obj T) =
      adj.homEquiv _ _ (δ F (G.obj M) T ≫ adj.counit.app M ▷ F.obj T) := by
  let := adj.rightAdjointLaxMonoidal
  rw [rightAdjointLaxMonoidal_μ, homEquiv_unit, homEquiv_unit]
  erw [adj.unit.naturality_assoc (G.obj M ◁ adj.unit.app T)]
  rw [Functor.comp_map, ← G.map_comp]
  congr 2
  dsimp
  rw [← δ_natural_right_assoc]
  congr 1
  rw [tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc,
    Adjunction.left_triangle_components, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4`: let `F ⊣ G` with `F` oplax
monoidal and compatible with the braidings, let `G ⊣ Q'` and `e : W ≅ Q' W'`. If the projection maps
`G M ⊗ T ⟶ G (M ⊗ F T)` are isomorphisms, the dual comparison
`G [M, W] ⟶ [G M, G W] ⟶ [G M, W']` (through `G e` and the counit of `G ⊣ Q'`) is an isomorphism.
Under the adjunctions `F ⊣ G`, `M ⊗ - ⊣ [M, -]` and `G ⊣ Q'`, composing with it is precomposition
with the projection map. -/
theorem isIso_dualComparison_of_isIso_projection
    (h : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    {Q' : C ⥤ D} (q : G ⊣ Q') {W : D} {W' : C} (e : W ≅ Q'.obj W') (M : D)
    (hπ : ∀ T : C, IsIso (adj.homEquiv _ _ (δ F (G.obj M) T ≫ adj.counit.app M ▷ F.obj T))) :
    letI := adj.rightAdjointLaxBraidedOfδ h
    IsIso (dualComparison G (G.map e.hom ≫ q.counit.app W') M) := by
  let := adj.rightAdjointLaxBraidedOfδ h
  apply isIso_of_yoneda_map_bijective
  intro T
  let π := G.obj M ◁ adj.unit.app T ≫ μ G M (F.obj T)
  have : IsIso π := by
    have := whiskerLeft_unit_comp_rightAdjointLaxMonoidal_μ adj M T
    dsimp only [π]
    rw [this]
    exact hπ T
  let E : (T ⟶ G.obj ((ihom M).obj W)) ≃ (T ⟶ (ihom (G.obj M)).obj W') :=
    (adj.homEquiv _ _).symm.trans <| ((ihom.adjunction M).homEquiv _ _).symm.trans <|
      ((Iso.refl _).homCongr e).trans <| (q.homEquiv _ _).symm.trans <|
        ((asIso π).homCongr (Iso.refl _)).symm.trans ((ihom.adjunction (G.obj M)).homEquiv _ _)
  have hfun : (fun (x : T ⟶ G.obj ((ihom M).obj W)) ↦
      x ≫ dualComparison G (G.map e.hom ≫ q.counit.app W') M) = ⇑E := by
    funext φ
    apply uncurry_injective
    simp only [E, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      Iso.homCongr_symm]
    rw [uncurry_natural_left, dualComparison, uncurry_natural_right, uncurry_eq,
      Category.assoc, ihomComparison_ev_assoc]
    simp only [Adjunction.homEquiv_counit]
    erw [uncurry_curry]
    erw [Iso.homCongr_apply]
    simp only [Iso.symm_inv, asIso_hom, Iso.symm_hom, Iso.refl_inv, Category.comp_id,
      Functor.map_comp, Category.assoc, π]
    have hφ : adj.unit.app T ≫ G.map (F.map φ ≫ adj.counit.app _) = φ := by
      simpa only [homEquiv_unit, homEquiv_counit] using (adj.homEquiv _ _).apply_symm_apply φ
    have hμ := μ_natural_right G M (F.map φ ≫ adj.counit.app ((ihom M).obj W))
    simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc] at hμ
    erw [← reassoc_of% hμ]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      Category.assoc, ← Functor.map_comp, hφ]
    rfl
  rw [hfun]
  exact E.bijective

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4` (formal core): under the
hypotheses of `CategoryTheory.Adjunction.isIso_dualComparison_of_isIso_projection`, `G δ_M` is an
isomorphism if and only if `δ_{G M}` (relative to `W'`) is. -/
theorem isIso_map_toIhomIhom_iff_of_isIso_projection
    (h : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    {Q' : C ⥤ D} (q : G ⊣ Q') {W : D} {W' : C} (e : W ≅ Q'.obj W') (M : D)
    (hπ : ∀ (N : D) (T : C),
      IsIso (adj.homEquiv _ _ (δ F (G.obj N) T ≫ adj.counit.app N ▷ F.obj T))) :
    IsIso (G.map (toIhomIhom W M)) ↔ IsIso (toIhomIhom W' (G.obj M)) := by
  let := adj.rightAdjointLaxBraidedOfδ h
  have := isIso_dualComparison_of_isIso_projection adj h q e M (hπ M)
  have := isIso_dualComparison_of_isIso_projection adj h q e ((ihom M).obj W)
    (hπ ((ihom M).obj W))
  exact isIso_map_toIhomIhom_iff G (G.map e.hom ≫ q.counit.app W') M

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4` (formal core): under the
hypotheses of `CategoryTheory.Adjunction.isIso_dualComparison_of_isIso_projection`, `G δ_M` and
`δ_{G M}` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_toIhomIhom_of_isIso_projection
    (h : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    {Q' : C ⥤ D} (q : G ⊣ Q') {W : D} {W' : C} (e : W ≅ Q'.obj W') (M : D)
    (hπ : ∀ (N : D) (T : C),
      IsIso (adj.homEquiv _ _ (δ F (G.obj N) T ≫ adj.counit.app N ▷ F.obj T))) :
    Nonempty (Arrow.mk (G.map (toIhomIhom W M)) ≅ Arrow.mk (toIhomIhom W' (G.obj M))) := by
  let := adj.rightAdjointLaxBraidedOfδ h
  have := isIso_dualComparison_of_isIso_projection adj h q e M (hπ M)
  have := isIso_dualComparison_of_isIso_projection adj h q e ((ihom M).obj W)
    (hπ ((ihom M).obj W))
  exact ⟨mapToIhomIhomArrowIso G (G.map e.hom ≫ q.counit.app W') M⟩

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Proper

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y S : Scheme.{u}} (aX : X ⟶ S) (aY : Y ⟶ S) [HasCompactification aX]
  [HasCompactification aY]
  (f : X ⟶ Y) [IsProper f] [HasCompactification f]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4`: for a proper `f : X ⟶ Y`,
`Rf_* δ_K` is an isomorphism if and only if `δ_{Rf_* K}` is. The hypotheses are the braided axiom
for `Lf^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarBraided`), the projection formula for
`Rf_*`, and `Rf^! ω_Y ≅ ω_X`. -/
theorem isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff
    (hbr : LeftDerivedUpperStarBraided (ModuleCat.{u + 1} Λ) f)
    [IsIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f)]
    (γ : (R(f)^![Λ]).obj (dualizingComplex Λ aY) ≅ dualizingComplex Λ aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((R((f)_*[ModuleCat.{u + 1} Λ])).map ((verdierDualDoubleDual Λ aX).app K)) ↔
      IsIso ((verdierDualDoubleDual Λ aY).app ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) := by
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) f
  let p := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  have h : ∀ M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (L((f)^*[ModuleCat.{u + 1} Λ])).map (β_ M N).hom ≫ δ (L((f)^*[ModuleCat.{u + 1} Λ])) N M =
        δ (L((f)^*[ModuleCat.{u + 1} Λ])) M N ≫ (β_ ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj N)).hom := by
    intro M N
    rw [← cancel_epi (μ (L((f)^*[ModuleCat.{u + 1} Λ])) M N), reassoc_of% (hbr M N),
        Functor.Monoidal.μ_δ,
      Functor.Monoidal.μ_δ_assoc, Category.comp_id]
  let q := (rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f)
  have hπ : ∀ (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (T : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      IsIso (p.homEquiv _ _ (δ (L((f)^*[ModuleCat.{u + 1} Λ])) ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          N) T ≫
        p.counit.app N ▷ (L((f)^*[ModuleCat.{u + 1} Λ])).obj T)) := fun N T ↦
    inferInstanceAs (IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app N).app
        T))
  rw [verdierDualDoubleDual_app, verdierDualDoubleDual_app]
  exact p.isIso_map_toIhomIhom_iff_of_isIso_projection h q γ.symm K hπ

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4`: for a proper `f : X ⟶ Y`, under
the hypotheses of
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff`,
`Rf_* δ_K` and `δ_{Rf_* K}` are isomorphic arrows, through the canonical comparison
`Rf_* 𝔻_X ⟶ 𝔻_Y Rf_*`. -/
theorem nonempty_arrowIso_rightDerivedLowerStar_map_verdierDualDoubleDual
    (hbr : LeftDerivedUpperStarBraided (ModuleCat.{u + 1} Λ) f)
    [IsIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f)]
    (γ : (R(f)^![Λ]).obj (dualizingComplex Λ aY) ≅ dualizingComplex Λ aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (Arrow.mk ((R((f)_*[ModuleCat.{u + 1} Λ])).map ((verdierDualDoubleDual Λ aX).app K)) ≅
      Arrow.mk ((verdierDualDoubleDual Λ aY).app ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K))) := by
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) f
  let p := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  have h : ∀ M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (L((f)^*[ModuleCat.{u + 1} Λ])).map (β_ M N).hom ≫ δ (L((f)^*[ModuleCat.{u + 1} Λ])) N M =
        δ (L((f)^*[ModuleCat.{u + 1} Λ])) M N ≫ (β_ ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj N)).hom := by
    intro M N
    rw [← cancel_epi (μ (L((f)^*[ModuleCat.{u + 1} Λ])) M N), reassoc_of% (hbr M N),
        Functor.Monoidal.μ_δ,
      Functor.Monoidal.μ_δ_assoc, Category.comp_id]
  let q := (rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f)
  have hπ : ∀ (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (T : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      IsIso (p.homEquiv _ _ (δ (L((f)^*[ModuleCat.{u + 1} Λ])) ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          N) T ≫
        p.counit.app N ▷ (L((f)^*[ModuleCat.{u + 1} Λ])).obj T)) := fun N T ↦
    inferInstanceAs (IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app N).app
        T))
  rw [verdierDualDoubleDual_app, verdierDualDoubleDual_app]
  exact p.nonempty_arrowIso_map_toIhomIhom_of_isIso_projection h q γ.symm K hπ

end Proper

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} (aY : Y ⟶ S)
  (f : X ⟶ Y) [IsProper f] [HasCompactification f] [HasCompactification aY]
  [HasCompactification (f ≫ aY)]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4`: for a proper `f : X ⟶ Y` and a
finite ring `Λ`, given the braided axiom for `Lf^*`, `Rf_* δ_K` is an isomorphism if and only if
`δ_{Rf_* K}` is. In particular, if `δ_{Rf_* K}` is an isomorphism then so is `Rf_* δ_K`. -/
theorem isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff_of_finite
    (hbr : LeftDerivedUpperStarBraided (ModuleCat.{u + 1} Λ) f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((R((f)_*[ModuleCat.{u + 1} Λ])).map
        ((verdierDualDoubleDual _ (f ≫ aY)).app K)) ↔
      IsIso ((verdierDualDoubleDual _ aY).app ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) :=
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ f
  isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff _ (f ≫ aY) aY f hbr
    (nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ f aY).some K

end Finite

end Etale

end AlgebraicGeometry
