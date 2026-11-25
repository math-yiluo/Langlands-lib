/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Sectionwise cokernels of abelian sheaves

A cokernel cofork `P' ──f──▶ P ──π──▶ Q` of sheaves of abelian groups which is sectionwise
right exact (`π` surjective on sections, with kernel the image of `f`) is a cokernel in sheaves
(`CategoryTheory.Sheaf.isColimitCokernelCoforkOfSurjective`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A cokernel cofork `P' ──f──▶ P ──π──▶ Q` of sheaves of abelian groups is a colimit if it is
sectionwise right exact: on each object, `π` is surjective with kernel the image of `f`. The
factorisation of a morphism `k : P ⟶ Z` killing `f` is defined sectionwise, by the universal
property of the cokernel of abelian groups. -/
noncomputable def isColimitCokernelCoforkOfSurjective {P' P Q : Sheaf J AddCommGrpCat.{w}}
    (f : P' ⟶ P) (π : P ⟶ Q) (w : f ≫ π = 0)
    (hπ : ∀ U : Cᵒᵖ, Function.Surjective (π.hom.app U))
    (hex : ∀ (U : Cᵒᵖ) (x : P.obj.obj U), π.hom.app U x = 0 → ∃ y, f.hom.app U y = x) :
    IsColimit (CokernelCofork.ofπ π w) := by
  have wU (U : Cᵒᵖ) : f.hom.app U ≫ π.hom.app U = 0 := by
    simpa using congrArg (fun φ ↦ φ.hom.app U) w
  have epiU (U : Cᵒᵖ) : Epi (π.hom.app U) := (AddCommGrpCat.epi_iff_surjective _).2 (hπ U)
  let hU (U : Cᵒᵖ) : IsColimit (CokernelCofork.ofπ (π.hom.app U) (wU U)) :=
    ShortComplex.Exact.gIsCokernel (S := ShortComplex.mk _ _ (wU U))
      ((ShortComplex.ab_exact_iff _).2 (hex U))
  have : Epi π := by
    have : Epi π.hom := NatTrans.epi_of_epi_app _
    exact (sheafToPresheaf J _).epi_of_epi_map this
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {Z} k hk ↦ ?_
  have hkU (U : Cᵒᵖ) : f.hom.app U ≫ k.hom.app U = 0 := by
    simpa using congrArg (fun φ ↦ φ.hom.app U) hk
  let l (U : Cᵒᵖ) := CokernelCofork.IsColimit.desc' (hU U) (k.hom.app U) (hkU U)
  have hl (U : Cᵒᵖ) : π.hom.app U ≫ (l U).1 = k.hom.app U := (l U).2
  refine ⟨ObjectProperty.homMk
    { app U := (l U).1
      naturality U V g := by
        rw [← cancel_epi (π.hom.app U), ← Category.assoc, ← NatTrans.naturality,
          Category.assoc, hl, ← Category.assoc, hl, NatTrans.naturality] }, ?_⟩
  exact ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ hl U))

end CategoryTheory.Sheaf
