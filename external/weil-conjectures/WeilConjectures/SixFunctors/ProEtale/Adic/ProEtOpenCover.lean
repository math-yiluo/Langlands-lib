/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Open covers are pro-étale coverings on the small pro-étale site

For an object `U` of the small pro-étale site `X_proét` and an open subscheme `W` of `U`, the
composite `W ⟶ U ⟶ X` is weakly étale, so `W` is again an object of `X_proét`
(`AlgebraicGeometry.Scheme.ProEt.ofOpens`). A family of open subschemes covering `U` generates a
covering sieve of `X_proét` (`AlgebraicGeometry.Scheme.ProEt.generate_ofArrows_mem_topology`):
open covers are étale, hence pro-étale, coverings.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} (U : X.ProEt)

/-- An open subscheme `W` of an object `U` of `X_proét`, as an object of `X_proét`. -/
noncomputable def ofOpens (W : U.left.Opens) : X.ProEt :=
  MorphismProperty.Over.mk ⊤ (W.ι ≫ U.hom) inferInstance

/-- The inclusion of an open subscheme `W` of `U`, as a morphism of `X_proét`. -/
noncomputable def ofOpensι (W : U.left.Opens) : ofOpens U W ⟶ U :=
  MorphismProperty.Over.homMk W.ι rfl trivial

/-- **Open covers are coverings of `X_proét`**: a family of open subschemes `Wᵢ` covering an
object `U` of `X_proét` generates a covering sieve. -/
lemma generate_ofArrows_mem_topology {ι : Type*} (W : ι → U.left.Opens)
    (hW : ∀ x, ∃ i, x ∈ W i) :
    Sieve.generate (Presieve.ofArrows (fun i ↦ ofOpens U (W i)) fun i ↦ ofOpensι U (W i)) ∈
      topology X U := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  refine etalePrecoverage_le_proetalePrecoverage _ ?_
  refine (ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨i, hi⟩ := hW x
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩
  · exact (inferInstance : Etale (W i).ι)

end AlgebraicGeometry.Scheme.ProEt
