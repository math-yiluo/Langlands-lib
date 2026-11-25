/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# The pushforward of module objects along a finite morphism is exact

Let `f : X ⟶ Y` be a finite morphism of finite presentation. The pushforward `f_*` of pro-étale
sheaves of abelian groups preserves epimorphisms
(`AlgebraicGeometry.ProEtale.epi_lowerStar_map_of_isFinite_ab`), as for sheaves of modules
(`AlgebraicGeometry.ProEtale.epi_lowerStar_map_of_isFinite`): an epimorphism is surjective on
sections over weakly contractible objects, and the base change along `f` of the spectrum of a
w-contractible ring is weakly contractible. Hence `f_*` is exact, and so is the pushforward
`(f)_*⟦Λ⟧ = mapMod(f_*) ⋙ Res` of module objects over a condensed ring `Λ`
(`AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}}

/-- The pushforward along a finite morphism of finite presentation preserves epimorphisms of
pro-étale sheaves of abelian groups: an epimorphism is surjective on sections over weakly
contractible objects, and the base change of the spectrum of a w-contractible ring along `f` is
weakly contractible (`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_pullback_of_isFinite`).
-/
lemma epi_lowerStar_map_of_isFinite_ab (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    {G H : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (φ : G ⟶ H) [Epi φ] :
    Epi ((f)_*[Ab.{u + 1}].map φ) := by
  have hφ : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 ‹_›
  have hsurj (W : X.ProEt) (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
      Function.Surjective (φ.hom.app (op W)) :=
    hW ((sheafCompose _ (forget Ab.{u + 1})).map φ)
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 hφ)
  rw [← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun {V} s ↦ ?_⟩
  obtain ⟨ι, W, g, hW, hcov⟩ := Scheme.ProEt.exists_isWContractibleRing_cover V
  refine (Scheme.ProEt.topology Y).superset_covering ?_ hcov
  rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
  obtain ⟨R, _, ⟨e⟩⟩ := hW i
  refine (Presheaf.imageSieve _ s).downward_closed ?_ a
  exact hsurj _ (Scheme.ProEt.isWeaklyContractible_pullback_of_isFinite f e) _

/-- **Finite pushforward is exact** on pro-étale sheaves of abelian groups: for a finite
morphism `f` of finite presentation, `f_*` is left exact as a right adjoint and preserves
epimorphisms by `AlgebraicGeometry.ProEtale.epi_lowerStar_map_of_isFinite_ab`. -/
theorem preservesFiniteColimits_lowerStar_of_isFinite_ab (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] :
    PreservesFiniteColimits ((f)_*[Ab.{u + 1}]) := by
  have : ((f)_*[Ab.{u + 1}]).PreservesEpimorphisms :=
    ⟨fun φ _ ↦ epi_lowerStar_map_of_isFinite_ab f φ⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels ((f)_*[Ab.{u + 1}])
  exact Functor.preservesFiniteColimits_of_preservesHomology _

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-- **The pushforward of module objects along a finite morphism is exact**: the pushforward
`(f)_*⟦Λ⟧ = mapMod(f_*) ⋙ Res` of module objects over `Λ` along a finite morphism of finite
presentation preserves finite colimits, since `f_*` does
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isFinite_ab`). -/
theorem preservesFiniteColimits_lowerStar_of_isFinite [IsCommMonObj Λ] (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] :
    PreservesFiniteColimits (f)_*⟦Λ⟧ := by
  have := preservesFiniteColimits_lowerStar_of_isFinite_ab f
  unfold lowerStar
  infer_instance

end CondensedRing

end AlgebraicGeometry.ProEtale
