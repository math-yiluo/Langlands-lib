/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite

/-!
# Global sections on the spectrum of an algebraically closed field are exact

Let `K` be an algebraically closed field. An epimorphism of pro-étale sheaves on `Spec K` is
surjective on global sections (`AlgebraicGeometry.ProEtale.surjective_app_of_epi_of_iso`, which
works for any concrete coefficient category), so the global sections functor on `ℓ`-adic
pro-étale sheaves preserves epimorphisms.

## Main results

- `AlgebraicGeometry.ProEtale.preservesEpimorphisms_Γ_of_isAlgClosed`: the global sections
  functor on `ℓ`-adic pro-étale sheaves on `Spec K` preserves epimorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K]

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The global sections functor on `ℓ`-adic pro-étale sheaves on the spectrum of an
algebraically closed field preserves epimorphisms. -/
instance preservesEpimorphisms_Γ_of_isAlgClosed :
    (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).PreservesEpimorphisms
    where
  preserves {F G} φ _ := by
    let e := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology (Spec (.of K)))
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId (Spec (.of K)))
    have h : (Sheaf.Γ _ _).map φ =
        e.hom.app F ≫ ((sheafSections _ _).obj _).map φ ≫ e.inv.app G := by
      rw [← reassoc_of% (e.hom.naturality φ)]
      simp
    have : Epi (((sheafSections (Scheme.ProEt.topology (Spec (.of K)))
        (WeilCoefficients.{u} l)).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).map φ) :=
      (ModuleCat.epi_iff_surjective _).2 (surjective_app_of_epi_of_iso (Iso.refl _) φ)
    rw [h]
    infer_instance

end ProEtale

end AlgebraicGeometry
