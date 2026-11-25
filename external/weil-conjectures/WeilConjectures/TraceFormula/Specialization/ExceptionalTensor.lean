/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!

# The exceptional exchange and the projection formula, abstractly

Let `f : V ⟶ W`, with `Rf_! ⊣ Rf^!` on both fibres, nearby cycles `S_V`, `S_W` (lax monoidal),
the pullback exchange `α_f : f_s^* S_W ⟶ S_V f^*`, the compact-support exchange
`ν_f : Rf_{s!} S_V ⟶ S_W Rf_!` and its mate, the exceptional exchange
`β_f : S_V Rf^! ⟶ Rf_s^! S_W`. Write `π : Rf_!(f^* N ⊗ X) ≅ N ⊗ Rf_! X` for the projection
formula and `t_f : f^* N ⊗ Rf^! M ⟶ Rf^!(N ⊗ M)` for its mate with the exceptional counit.

Blueprint `lemma-compatibilities-base-change-maps` (2) is the identity

`β_f S_V(t_f) μ_V(α_f ⊗ 1) = f_s^! μ_W t_{f_s}(1 ⊗ β_f)`

of maps `f_s^* S_W N ⊗ S_V f^! M ⟶ f_s^! S_W(N ⊗ M)`. It follows from (1), the compatibility of
`ν_f` with the projection formula, by passing to adjoints
(`CategoryTheory.whiskerRight_comp_μ_comp_map_comp_mateEquiv_app`).

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory

variable {V V' W W' : Type*} [Category V] [Category V'] [Category W] [Category W']
  [MonoidalCategory V] [MonoidalCategory V'] [MonoidalCategory W] [MonoidalCategory W']
  {SV : V ⥤ V'} {SW : W ⥤ W'} [SV.LaxMonoidal] [SW.LaxMonoidal]
  {F : V ⥤ W} {G : W ⥤ V} {F' : V' ⥤ W'} {G' : W' ⥤ V'} {Lp : W ⥤ V} {Lp' : W' ⥤ V'}

/-- **The exceptional exchange and the projection formula** (blueprint
`lemma-compatibilities-base-change-maps`, (1) ⇒ (2)): let `β` be the mate of `ν` for the adjunctions
`F ⊣ G` and `F' ⊣ G'`, `t` and `t'` the maps adjoint to `π ≫ (1 ◁ ε)` for projection-formula
maps `π`, `π'`, natural in the second variable along `β`. If `ν` is compatible with the projection
formula (`h₁`), then
`(α ▷ 1) ≫ μ_V ≫ S_V(t) ≫ β = (1 ◁ β) ≫ t' ≫ G'(μ_W)`. -/
theorem whiskerRight_comp_μ_comp_map_comp_mateEquiv_app (a : F ⊣ G) (a' : F' ⊣ G')
    (α : SW ⋙ Lp' ⟶ Lp ⋙ SV) (ν : SV ⋙ F' ⟶ F ⋙ SW) (N M : W)
    (π : F.obj (Lp.obj N ⊗ G.obj M) ⟶ N ⊗ F.obj (G.obj M))
    (π₁ : F'.obj (Lp'.obj (SW.obj N) ⊗ SV.obj (G.obj M)) ⟶
      SW.obj N ⊗ F'.obj (SV.obj (G.obj M)))
    (π₂ : F'.obj (Lp'.obj (SW.obj N) ⊗ G'.obj (SW.obj M)) ⟶
      SW.obj N ⊗ F'.obj (G'.obj (SW.obj M)))
    (hπ : F'.map (Lp'.obj (SW.obj N) ◁ (mateEquiv a a' ν).app M) ≫ π₂ =
      π₁ ≫ SW.obj N ◁ F'.map ((mateEquiv a a' ν).app M))
    (t : Lp.obj N ⊗ G.obj M ⟶ G.obj (N ⊗ M))
    (ht : F.map t ≫ a.counit.app (N ⊗ M) = π ≫ N ◁ a.counit.app M)
    (t' : Lp'.obj (SW.obj N) ⊗ G'.obj (SW.obj M) ⟶ G'.obj (SW.obj N ⊗ SW.obj M))
    (ht' : F'.map t' ≫ a'.counit.app _ = π₂ ≫ SW.obj N ◁ a'.counit.app (SW.obj M))
    (h₁ : F'.map (α.app N ▷ SV.obj (G.obj M) ≫ μ SV (Lp.obj N) (G.obj M)) ≫
        ν.app (Lp.obj N ⊗ G.obj M) ≫ SW.map π =
      π₁ ≫ SW.obj N ◁ ν.app (G.obj M) ≫ μ SW N (F.obj (G.obj M))) :
    α.app N ▷ SV.obj (G.obj M) ≫ μ SV (Lp.obj N) (G.obj M) ≫ SV.map t ≫
        (mateEquiv a a' ν).app (N ⊗ M) =
      Lp'.obj (SW.obj N) ◁ (mateEquiv a a' ν).app M ≫ t' ≫ G'.map (μ SW N M) := by
  have hm := mateEquiv_counit a a' ν (N ⊗ M)
  have hm' := mateEquiv_counit a a' ν M
  have hn : F'.map (SV.map t) ≫ ν.app (G.obj (N ⊗ M)) =
      ν.app (Lp.obj N ⊗ G.obj M) ≫ SW.map (F.map t) := ν.naturality t
  have hc : F'.map (G'.map (μ SW N M)) ≫ a'.counit.app (SW.obj (N ⊗ M)) =
      a'.counit.app (SW.obj N ⊗ SW.obj M) ≫ μ SW N M := a'.counit.naturality (μ SW N M)
  simp only [Functor.comp_obj] at hm hm'
  apply (a'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hm, reassoc_of% hn, ← SW.map_comp, ht, hc, reassoc_of% ht', reassoc_of% hπ,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hm', SW.map_comp, ← Category.assoc,
    ← Category.assoc, ← Category.assoc, ← Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h₁]
  simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]
  have hμ := μ_natural_right SW N (a.counit.app M)
  simp only [Functor.id_obj] at hμ
  rw [hμ]
  rfl

end CategoryTheory
