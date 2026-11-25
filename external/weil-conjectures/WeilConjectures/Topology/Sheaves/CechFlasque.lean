/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Topology.Sheaves.CechCriterion

/-!
# Flasque sheaves are Čech-acyclic

The Čech complex of a flasque abelian sheaf on any family of open subsets is exact in positive
degrees (`TopCat.Sheaf.exactAt_cechComplex_of_isFlasque`).

Embed the flasque sheaf `F` into an injective sheaf `I`, with cokernel `Q`. Since `F` is
flasque, `I(V) → Q(V)` is surjective for every open `V`, and `Q` is again flasque. So the Čech
complexes of `F`, `I` and `Q` form a short exact sequence of complexes, and the Čech complex
of `I` is exact in positive degrees. In degree `1` a cocycle of `F` is the coboundary of a
`0`-cochain of `I` whose image in `Q` glues to a section of `Q`; lifting this section to `I`
corrects the `0`-cochain. In degree `q + 2` the image in `Q` of the `(q + 1)`-cochain of `I` is
a cocycle, hence a coboundary by induction, since `Q` is flasque.
-/

@[expose] public section

universe u v

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

open Presheaf

variable {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X)

/-- **Flasque sheaves are Čech-acyclic.** The Čech complex of a flasque abelian sheaf on any
family `U` of open subsets is exact in every positive degree. -/
theorem exactAt_cechComplex_of_isFlasque (q : ℕ) :
    ∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      [Presheaf.IsFlasque F.obj], ((cechComplex U).obj F.obj).ExactAt (q + 1) := by
  induction q with
  | zero =>
    intro F _
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have : Presheaf.IsFlasque S.X₁.obj := ‹_›
    have hsurj (V : Opens X) : Function.Surjective (S.g.hom.app (op V)) :=
      (AddCommGrpCat.epi_iff_surjective _).1 (IsFlasque.epi_of_shortExact hS)
    rw [exactAt_cechComplex_iff']
    intro c hc
    obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff' U _ 0).1
      (exactAt_cechComplex_of_injective U S.X₂ 0) (((cechComplex U).map S.f.hom).f 1 c)
      ((cechComplex_map_f_d_apply U S.f.hom _ c).symm.trans (by rw [hc, map_zero]))
    -- the image of `b` in `Q` is a `0`-cocycle, so it glues to a section `σ` of `Q`
    have hgb : ((cechComplex U).obj S.X₃.obj).d 0 1
        (((cechComplex U).map S.g.hom).f 0 b) = 0 := by
      rw [← cechComplex_map_f_d_apply, hb, cechComplex_map_f_map_f_eq_zero U _ _ app_g_app_f]
    obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing S.X₃
      (fun z : Fin 1 → ι ↦ ⨅ l, U (z l)) _ (map_inf_eq_of_cechComplex_d_zero U _ _ hgb)
    -- lift `σ` to a section `τ` of `I`, and correct `b` by the restrictions of `τ`
    obtain ⟨τ, rfl⟩ := hsurj _ σ
    let b' : ((cechComplex U).obj S.X₂.obj).X 0 := fun z ↦
      S.X₂.obj.map (homOfLE (le_iSup (fun z : Fin 1 → ι ↦ ⨅ l, U (z l)) z)).op τ
    have hb' : ((cechComplex U).obj S.X₂.obj).d 0 1 b' = 0 :=
      cechComplex_d_zero_restrict U _ τ _
    obtain ⟨a, ha⟩ := exists_cechComplex_map_f_eq U S.f.hom S.g.hom (exists_app_f_eq hS) 0
      (b - b') (by
        funext z
        rw [map_sub, cechComplex_sub_apply, cechComplex_map_f_apply', cechComplex_map_f_apply',
          cechComplex_zero_apply]
        dsimp only [b']
        rw [NatTrans.naturality_apply]
        exact sub_eq_zero.2 (hσ z).symm)
    refine ⟨a, cechComplex_map_f_injective U _ (injective_app_f hS) _ ?_⟩
    rw [cechComplex_map_f_d_apply, ha, map_sub, hb, hb', sub_zero]
  | succ q ih =>
    intro F _
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have : Presheaf.IsFlasque S.X₁.obj := ‹_›
    have : Presheaf.IsFlasque S.X₂.obj := isFlasque_of_injective
    have : Presheaf.IsFlasque S.X₃.obj := IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    have hsurj (V : Opens X) : Function.Surjective (S.g.hom.app (op V)) :=
      (AddCommGrpCat.epi_iff_surjective _).1 (IsFlasque.epi_of_shortExact hS)
    rw [exactAt_cechComplex_iff']
    intro c hc
    obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff' U _ (q + 1)).1
      (exactAt_cechComplex_of_injective U S.X₂ (q + 1)) (((cechComplex U).map S.f.hom).f _ c)
      ((cechComplex_map_f_d_apply U S.f.hom _ c).symm.trans (by rw [hc, map_zero]))
    -- the image of `b` in `Q` is a cocycle, hence a coboundary since `Q` is flasque
    obtain ⟨e, he⟩ := (exactAt_cechComplex_iff' U _ q).1 (ih S.X₃)
      (((cechComplex U).map S.g.hom).f _ b) (by
        rw [← cechComplex_map_f_d_apply, hb, cechComplex_map_f_map_f_eq_zero U _ _ app_g_app_f])
    obtain ⟨e', he'⟩ : ∃ e' : ((cechComplex U).obj S.X₂.obj).X q,
        ((cechComplex U).map S.g.hom).f q e' = e := by
      choose e' he' using fun y ↦ hsurj _ (e y)
      exact ⟨e', funext fun y ↦ (cechComplex_map_f_apply U S.g.hom _ e' y).trans (he' y)⟩
    obtain ⟨a, ha⟩ := exists_cechComplex_map_f_eq U S.f.hom S.g.hom (exists_app_f_eq hS) _
      (b - ((cechComplex U).obj S.X₂.obj).d q (q + 1) e') (by
        rw [map_sub, cechComplex_map_f_d_apply, he', he, sub_self])
    refine ⟨a, cechComplex_map_f_injective U _ (injective_app_f hS) _ ?_⟩
    rw [cechComplex_map_f_d_apply, ha, map_sub, cechComplex_d_d_apply, sub_zero, hb]

end TopCat.Sheaf
