/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!

# Exchanges of nearby cycles and the projection formula, abstractly

Blueprint `lemma-compatibilities-base-change-maps` (1) states that the compact-support exchange
`ν_f : Rf_{s!} S_V ⟶ S_W Rf_{η!}` is compatible with the projection formula. For a compactified
morphism `f = p ∘ h`, `ν_f` is built from the adjoint `ν_h` of the inverse pullback exchange of the
open immersion `h` and the inverse of the proper exchange `χ_p`. This file proves the two
building blocks, for abstract adjunctions with monoidal left (respectively right) adjoints and lax
monoidal nearby cycles, from the monoidality of the pullback exchange `α`:

* `CategoryTheory.μ_comp_map_projectionMap_comp_app`: for an adjunction `L ⊣ R`
  (`p^* ⊣ Rp_*`), a mate `χ : S_W R ⟶ R' S_V` of a monoidal `α` is compatible with the
  projection maps `N ⊗ R X ⟶ R (L N ⊗ X)` (`CategoryTheory.projectionMap`);
* `CategoryTheory.map_comp_comp_map_leftProjectionMap`: for an adjunction `P ⊣ Lp`
  (`h_! ⊣ h^*`), the adjoint `ν : S_V P' ⟶ P S_W` of the inverse of a monoidal `α` is compatible
  with the projection maps `P (Lp N ⊗ X) ⟶ N ⊗ P X` (`CategoryTheory.leftProjectionMap`).

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory

variable {W V W' V' : Type*} [Category W] [Category V] [Category W'] [Category V']
  [MonoidalCategory W] [MonoidalCategory V] [MonoidalCategory W'] [MonoidalCategory V']
  {SW : W ⥤ W'} {SV : V ⥤ V'} [SW.LaxMonoidal] [SV.LaxMonoidal]
  {L : W ⥤ V} {R : V ⥤ W} {L' : W' ⥤ V'} {R' : V' ⥤ W'} [L.Monoidal] [L'.Monoidal]

/-- The projection morphism `N ⊗ R X ⟶ R (L N ⊗ X)` of an adjunction `L ⊣ R` with `L` monoidal:
the adjoint of `L(N ⊗ R X) ≅ L N ⊗ L R X ⟶ L N ⊗ X`. -/
noncomputable def projectionMap (adj : L ⊣ R) (N : W) (X : V) : N ⊗ R.obj X ⟶ R.obj (L.obj N ⊗ X) :=
  adj.homEquiv _ _ (Functor.OplaxMonoidal.δ L N (R.obj X) ≫ L.obj N ◁ adj.counit.app X)

/-- **The mate of a monoidal exchange is compatible with the projection formula** (the proper case
of blueprint `lemma-compatibilities-base-change-maps` (1)). -/
theorem μ_comp_map_projectionMap_comp_app (adj : L ⊣ R) (adj' : L' ⊣ R')
    (α : SW ⋙ L' ⟶ L ⋙ SV)
    (hα : ∀ N M : W, L'.map (μ SW N M) ≫ α.app (N ⊗ M) =
      Functor.OplaxMonoidal.δ L' (SW.obj N) (SW.obj M) ≫ (α.app N ⊗ₘ α.app M) ≫
        μ SV (L.obj N) (L.obj M) ≫ SV.map (μ L N M))
    (χ : R ⋙ SW ⟶ SV ⋙ R')
    (hm : ∀ Y : V, L'.map (χ.app Y) ≫ adj'.counit.app (SV.obj Y) =
      α.app (R.obj Y) ≫ SV.map (adj.counit.app Y))
    (N : W) (X : V) :
    μ SW N (R.obj X) ≫ SW.map (projectionMap adj N X) ≫ χ.app (L.obj N ⊗ X) =
      SW.obj N ◁ χ.app X ≫ projectionMap adj' (SW.obj N) (SV.obj X) ≫
        R'.map (α.app N ▷ SV.obj X ≫ μ SV (L.obj N) X) := by
  have hπ (N : W) (X : V) : L.map (projectionMap adj N X) ≫ adj.counit.app (L.obj N ⊗ X) =
      Functor.OplaxMonoidal.δ L N (R.obj X) ≫ L.obj N ◁ adj.counit.app X := by
    simp [projectionMap, Adjunction.homEquiv_unit]
  have hπ' (N : W') (X : V') : L'.map (projectionMap adj' N X) ≫ adj'.counit.app (L'.obj N ⊗ X) =
      Functor.OplaxMonoidal.δ L' N (R'.obj X) ≫ L'.obj N ◁ adj'.counit.app X := by
    simp [projectionMap, Adjunction.homEquiv_unit]
  have hn : L'.map (SW.map (projectionMap adj N X)) ≫ α.app (R.obj (L.obj N ⊗ X)) =
      α.app (N ⊗ R.obj X) ≫ SV.map (L.map (projectionMap adj N X)) := α.naturality _
  have hc : L'.map (R'.map (α.app N ▷ SV.obj X ≫ μ SV (L.obj N) X)) ≫
      adj'.counit.app (SV.obj (L.obj N ⊗ X)) = adj'.counit.app _ ≫
        (α.app N ▷ SV.obj X ≫ μ SV (L.obj N) X) := adj'.counit.naturality _
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hm, reassoc_of% hn, ← SV.map_comp, hπ, reassoc_of% (hα N (R.obj X)), ← SV.map_comp,
    Functor.Monoidal.μ_δ_assoc, ← μ_natural_right]
  simp only [Adjunction.counit_naturality, Adjunction.counit_naturality_assoc]
  rw [reassoc_of% (hπ' (SW.obj N) (SV.obj X))]
  erw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hm]
  congr 1
  simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  rfl


end CategoryTheory

namespace CategoryTheory

variable {W V W' V' : Type*} [Category W] [Category V] [Category W'] [Category V']
  [MonoidalCategory W] [MonoidalCategory V] [MonoidalCategory W'] [MonoidalCategory V']
  {SW : W ⥤ W'} {SV : V ⥤ V'} [SW.LaxMonoidal] [SV.LaxMonoidal]
  {P : V ⥤ W} {Lp : W ⥤ V} {P' : V' ⥤ W'} {Lp' : W' ⥤ V'} [Lp.Monoidal] [Lp'.Monoidal]

/-- The projection morphism `P(Lp N ⊗ X) ⟶ N ⊗ P X` of an adjunction `P ⊣ Lp` with `Lp`
monoidal: the adjoint of `Lp N ⊗ X ⟶ Lp N ⊗ Lp P X ≅ Lp (N ⊗ P X)`. -/
noncomputable def leftProjectionMap (adj : P ⊣ Lp) (N : W) (X : V) :
    P.obj (Lp.obj N ⊗ X) ⟶ N ⊗ P.obj X :=
  (adj.homEquiv _ _).symm (Lp.obj N ◁ adj.unit.app X ≫ μ Lp N (P.obj X))

/-- **The adjoint of an inverse pullback exchange is compatible with the projection formula** (the
open case of blueprint `lemma-compatibilities-base-change-maps` (1)): for `ν : S_V ⋙ P' ⟶ P ⋙ S_W`
adjoint to `α⁻¹` along `P ⊣ Lp`, `P' ⊣ Lp'`, with `α` monoidal. -/
theorem map_comp_comp_map_leftProjectionMap (adj : P ⊣ Lp) (adj' : P' ⊣ Lp')
    (α : SW ⋙ Lp' ≅ Lp ⋙ SV)
    (hα : ∀ N M : W, Lp'.map (μ SW N M) ≫ α.hom.app (N ⊗ M) =
      Functor.OplaxMonoidal.δ Lp' (SW.obj N) (SW.obj M) ≫ (α.hom.app N ⊗ₘ α.hom.app M) ≫
        μ SV (Lp.obj N) (Lp.obj M) ≫ SV.map (μ Lp N M))
    (ν : SV ⋙ P' ⟶ P ⋙ SW)
    (hν : ∀ X : V, SV.map (adj.unit.app X) ≫ α.inv.app (P.obj X) =
      adj'.unit.app (SV.obj X) ≫ Lp'.map (ν.app X))
    (N : W) (X : V) :
    P'.map (α.hom.app N ▷ SV.obj X ≫ μ SV (Lp.obj N) X) ≫ ν.app (Lp.obj N ⊗ X) ≫
        SW.map (leftProjectionMap adj N X) =
      leftProjectionMap adj' (SW.obj N) (SV.obj X) ≫ SW.obj N ◁ ν.app X ≫
        μ SW N (P.obj X) := by
  have hπ (N : W) (X : V) : adj.unit.app _ ≫ Lp.map (leftProjectionMap adj N X) =
      Lp.obj N ◁ adj.unit.app X ≫ μ Lp N (P.obj X) := by
    simp [leftProjectionMap, Adjunction.homEquiv_counit]
  have hπ' (N : W') (X : V') : adj'.unit.app _ ≫ Lp'.map (leftProjectionMap adj' N X) =
      Lp'.obj N ◁ adj'.unit.app X ≫ μ Lp' N (P'.obj X) := by
    simp [leftProjectionMap, Adjunction.homEquiv_counit]
  have hi : (Lp ⋙ SV).map (leftProjectionMap adj N X) ≫ α.inv.app (N ⊗ P.obj X) =
      α.inv.app (P.obj (Lp.obj N ⊗ X)) ≫ (SW ⋙ Lp').map (leftProjectionMap adj N X) :=
    α.inv.naturality _
  have key : μ SV (Lp.obj N) (Lp.obj (P.obj X)) ≫ SV.map (μ Lp N (P.obj X)) ≫
      α.inv.app (N ⊗ P.obj X) = (α.inv.app N ⊗ₘ α.inv.app (P.obj X)) ≫
        μ Lp' (SW.obj N) (SW.obj (P.obj X)) ≫ Lp'.map (μ SW N (P.obj X)) := by
    rw [← cancel_mono (α.hom.app (N ⊗ P.obj X))]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
    rw [hα, Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom_assoc]
    simp
  apply (adj'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [adj'.unit_naturality_assoc, adj'.unit_naturality_assoc, ← reassoc_of% (hν (Lp.obj N ⊗ X))]
  erw [← hi]
  rw [Functor.comp_map]
  rw [← SV.map_comp_assoc, hπ, SV.map_comp_assoc, ← μ_natural_right_assoc]
  erw [key]
  erw [reassoc_of% (hπ' (SW.obj N) (SV.obj X))]
  rw [← μ_natural_right_assoc]
  have hpre : α.hom.app N ▷ SV.obj X ≫ SV.obj (Lp.obj N) ◁ SV.map (adj.unit.app X) ≫
      (α.inv.app N ⊗ₘ α.inv.app (P.obj X)) =
      Lp'.obj (SW.obj N) ◁ adj'.unit.app (SV.obj X) ≫ Lp'.obj (SW.obj N) ◁ Lp'.map (ν.app X) := by
    rw [tensorHom_def]
    erw [whisker_exchange_assoc]
    rw [← comp_whiskerRight_assoc, Iso.hom_inv_id_app, id_whiskerRight, Category.id_comp,
      ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
    erw [hν]
    rfl
  rw [reassoc_of% hpre]
  rfl

end CategoryTheory
