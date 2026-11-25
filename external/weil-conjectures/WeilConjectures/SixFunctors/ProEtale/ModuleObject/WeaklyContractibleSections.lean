/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# Sections of module objects over weakly contractible objects

Let `X` be a scheme and `U` a weakly contractible object of `X_proét`. Taking sections over `U`
is an exact functor on abelian pro-étale sheaves and on module objects over `Λ_X`
(`ProEtale.CondensedRing.preservesHomology_sectionsFunctor`): it is left exact since limits of
sheaves are computed on sections, and it preserves epimorphisms since an epimorphism of sheaves is
locally surjective, hence surjective on sections over `U`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- An epimorphism of abelian pro-étale sheaves is surjective on sections over a weakly
contractible object. -/
lemma surjective_app_of_isWeaklyContractible_ab {T : Scheme.{u}} {W : T.ProEt}
    (hW : (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W)
    {F G : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op W)) :=
  hW ((sheafCompose _ (forget _)).map φ)
    ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1
      ((Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 inferInstance))

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  {X : Scheme.{u}}

/-- The sections over `U : X_proét` of module objects over `Λ_X`. -/
noncomputable abbrev sectionsFunctor (U : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤ Ab.{u + 1} :=
  Mod.forget _ ⋙ sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op U)

/-- Taking sections over a weakly contractible object is an exact functor on module objects
over `Λ_X`. -/
lemma preservesHomology_sectionsFunctor {U : X.ProEt}
    (hU : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} U) :
    (sectionsFunctor Λ U).PreservesHomology := by
  have : (sectionsFunctor Λ U).PreservesEpimorphisms := ⟨fun {M N} φ _ ↦ by
    have : Epi φ.hom := (Mod.forget _).map_epi φ
    exact (AddCommGrpCat.epi_iff_surjective _).2
      (surjective_app_of_isWeaklyContractible_ab hU φ.hom)⟩
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

end CondensedRing

end AlgebraicGeometry.ProEtale
