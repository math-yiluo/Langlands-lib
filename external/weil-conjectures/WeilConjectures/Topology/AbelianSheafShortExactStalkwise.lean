/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Abelian

/-!
# Short exactness of abelian sheaves is detected on stalks

Source: literature/stacks-project/modules.tex, Modules, Lemma 01AG (lemma-abelian),
specialized to the constant sheaf of integers; Sheaves, Section 007S
(section-exactness-points) (blueprint: lem-sc-abelian-sheaf-short-exact-stalkwise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace TopCat

/--
Source: literature/stacks-project/modules.tex, Modules, Lemma 01AG (lemma-abelian),
specialized to the constant sheaf of integers; Sheaves, Section 007S
(section-exactness-points).

For a short complex of abelian sheaves, short exactness is equivalent to short
exactness of its stalk complex at every point. The forward implication maps the
short exact complex along each stalk functor. Conversely, exactness in the
middle
is detected by `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`, while the
monomorphism and epimorphism conditions are detected by the stalk criteria;
these three conditions are recombined using the definition of `ShortExact`.
(blueprint: lem-sc-abelian-sheaf-short-exact-stalkwise)
-/
theorem shortExact_iff_stalkFunctor_map_shortExact
    {X : TopCat.{u}}
    (S : ShortComplex (Sheaf AddCommGrpCat X)) :
    S.ShortExact ↔
      ∀ (x : X), (S.map (Sheaf.forget AddCommGrpCat X ⋙ Presheaf.stalkFunctor (X := X)
        AddCommGrpCat x)).ShortExact := by
  constructor
  · intro h x
    exact h.map_of_exact (Sheaf.forget AddCommGrpCat X ⋙
      Presheaf.stalkFunctor (X := X) AddCommGrpCat x)
  · intro h
    refine ShortComplex.ShortExact.mk'
      ((Sheaf.exact_iff_stalkFunctor_map_exact S).mpr (fun x ↦ (h x).exact)) ?_ ?_
    · open ZeroObject in
      -- Detect the endpoint condition as exactness of a complex with a zero map.
      let T : ShortComplex (Sheaf AddCommGrpCat X) :=
        ShortComplex.mk (0 : 0 ⟶ S.X₁) S.f zero_comp
      apply (T.exact_iff_mono rfl).mp
      apply (Sheaf.exact_iff_stalkFunctor_map_exact T).mpr
      intro x
      apply ((T.map (Sheaf.forget AddCommGrpCat X ⋙
        Presheaf.stalkFunctor (X := X) AddCommGrpCat x)).exact_iff_mono (by simp [T])).mpr
      exact (h x).mono_f
    · open ZeroObject in
      -- Detect the endpoint condition as exactness of a complex with a zero map.
      let T : ShortComplex (Sheaf AddCommGrpCat X) :=
        ShortComplex.mk S.g (0 : S.X₃ ⟶ 0) comp_zero
      apply (T.exact_iff_epi rfl).mp
      apply (Sheaf.exact_iff_stalkFunctor_map_exact T).mpr
      intro x
      apply ((T.map (Sheaf.forget AddCommGrpCat X ⋙
        Presheaf.stalkFunctor (X := X) AddCommGrpCat x)).exact_iff_epi (by simp [T])).mpr
      exact (h x).epi_g

end TopCat
