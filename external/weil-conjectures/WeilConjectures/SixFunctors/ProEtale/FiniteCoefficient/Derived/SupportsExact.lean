/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.SupportedSectionsFlasque
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# The exact sequence of supported sections for injective pro-étale sheaves

Let `j : U ⟶ X` be an open immersion. For an injective pro-étale sheaf `I` on `X` the
restriction `I ⟶ j_* j^* I` (the unit of `j^* ⊣ j_*`) is a split epimorphism, so injective
sheaves are flasque for the pair. Consequently, for a complex `I` of injective pro-étale sheaves,

`0 ⟶ 𝒢_Z I ⟶ I ⟶ j_* j^* I ⟶ 0`

is a short exact sequence of complexes, `𝒢_Z I = ker (I ⟶ j_* j^* I)` being the complex of
sections supported on the closed complement `Z` (`s_* s^! I` for a closed immersion
`s : Z ⟶ X` with quasi-compact open complement `j`,
`AlgebraicGeometry.ProEtale.closedUpperShriekCompLowerStarIso`). This is the pro-étale form of
blueprint `lemma-local-cohomology-right-adjoint--2`; the étale form is
`AlgebraicGeometry.Etale.shortExact_supportsShortComplex`.

The argument is the one on the étale site: the counit `j_! j^* F ⟶ F` at `F = j_* j^* I` is a
monomorphism, being the comparison `j_! ⟶ j_*` up to an isomorphism
(`AlgebraicGeometry.ProEtale.mono_openImmersionLowerShriekToLowerStar_app`), so by injectivity
the transpose of the counit of `j^* ⊣ j_*` extends along it to a section of the unit.

## Main statements

- `AlgebraicGeometry.ProEtale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`
- `AlgebraicGeometry.ProEtale.isFlasqueFor_of_injective`
- `AlgebraicGeometry.ProEtale.shortExact_supportsShortComplex`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The counit `j_! j^* (j_* G) ⟶ j_* G` of `j_! ⊣ j^*` at a pushforward is a monomorphism: up to
the identification of `j^*` with the restriction, it is the comparison `j_! G ⟶ j_* G`
precomposed with an isomorphism. -/
instance mono_openImmersionLowerShriekUpperStarAdjunction_counit_app_lowerStar
    (G : Sheaf (ProEt.topology U) A) :
    Mono ((openImmersionLowerShriekUpperStarAdjunction A j).counit.app ((j)_*[A].obj G)) := by
  rw [← Adjunction.rightAdjointUniq_hom_app_counit (openImmersionLowerShriekUpperStarAdjunction A j)
    (openImmersionLowerShriekAdjunction A j)]
  have h := openImmersionLowerShriekToLowerStar_app A j G
  have : Mono ((openImmersionLowerShriekAdjunction A j).counit.app ((j)_*[A].obj G)) := by
    have : Mono ((j)_!open[A].map
        ((inv (openImmersionRestrictionLowerStarAdjunction A j).counit).app G) ≫
          (openImmersionLowerShriekAdjunction A j).counit.app ((j)_*[A].obj G)) := by
      rw [← h]
      infer_instance
    rw [← IsIso.inv_hom_id_assoc ((j)_!open[A].map
      ((inv (openImmersionRestrictionLowerStarAdjunction A j).counit).app G))
      ((openImmersionLowerShriekAdjunction A j).counit.app ((j)_*[A].obj G))]
    infer_instance
  infer_instance

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The exact sequence of supported sections
for injective objects (pro-étale form)

For an injective pro-étale sheaf `I` on `X` and an open immersion `j`, the restriction
`I ⟶ j_* j^* I` (the unit of `j^* ⊣ j_*`) is a split epimorphism. Put `F = j_* j^* I`. The counit
`j_! j^* F ⟶ F` is a monomorphism, so by injectivity of `I` the map `j_! j^* F ⟶ I` adjoint to
the counit `j^* j_* j^* I ⟶ j^* I` extends to `σ : F ⟶ I`; `σ` is a section of the unit, as
both `σ ≫ η_I` and `𝟙_F` are adjoint to the counit. -/
theorem isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective
    (I : Sheaf (ProEt.topology X) A) [Injective I] :
    IsSplitEpi ((upperStarLowerStarAdjunction A j).unit.app I) := by
  let adj := upperStarLowerStarAdjunction A j
  let adj' := openImmersionLowerShriekUpperStarAdjunction A j
  let F := (j)_*[A].obj ((j)^*[A].obj I)
  let φ : (j)_!open[A].obj ((j)^*[A].obj F) ⟶ I := (adj'.homEquiv _ _).symm (adj.counit.app _)
  let σ : F ⟶ I := Injective.factorThru φ (adj'.counit.app F)
  have hσ : adj'.counit.app F ≫ σ = φ := Injective.comp_factorThru _ _
  refine ⟨⟨σ, ?_⟩⟩
  apply (adj.homEquiv _ _).symm.injective
  have h₁ : (j)^*[A].map σ = adj.counit.app ((j)^*[A].obj I) := by
    have := congrArg (adj'.homEquiv _ _) hσ
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp, ← assoc,
      adj'.right_triangle_components, id_comp] at this
    exact this
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, assoc, h₁]
  erw [adj.left_triangle_components]
  simp

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The exact sequence of supported sections
for injective objects (pro-étale form)

Injective pro-étale sheaves are flasque for the pair (`AlgebraicGeometry.ProEtale.IsFlasqueFor`).
-/
lemma isFlasqueFor_of_injective (I : Sheaf (ProEt.topology X) A) [Injective I] :
    IsFlasqueFor A j I := by
  have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective A j I
  unfold IsFlasqueFor
  infer_instance

/-- The restriction `I ⟶ j_* j^* I` of a complex of pro-étale sheaves to the open part,
degreewise the unit of `j^* ⊣ j_*`. -/
@[simps]
noncomputable def supportsUnit (I : CochainComplex (Sheaf (ProEt.topology X) A) ℤ) :
    I ⟶ (((j)^*[A] ⋙ (j)_*[A]).mapHomologicalComplex _).obj I where
  f n := (upperStarLowerStarAdjunction A j).unit.app (I.X n)
  comm' n m _ := ((upperStarLowerStarAdjunction A j).unit.naturality (I.d n m)).symm

/-- The short complex `𝒢_Z I ⟶ I ⟶ j_* j^* I` of a complex `I` of pro-étale sheaves, the first
term being the kernel of the restriction to the open part, the complex of supported sections. -/
@[simps]
noncomputable def supportsShortComplex (I : CochainComplex (Sheaf (ProEt.topology X) A) ℤ) :
    ShortComplex (CochainComplex (Sheaf (ProEt.topology X) A) ℤ) :=
  ShortComplex.mk (kernel.ι (supportsUnit A j I)) (supportsUnit A j I) (kernel.condition _)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The exact sequence of supported sections
for injective objects (pro-étale form)

For a complex `I` of injective pro-étale sheaves, `0 ⟶ 𝒢_Z I ⟶ I ⟶ j_* j^* I ⟶ 0` is a short
exact sequence of complexes. For a closed immersion `s : Z ⟶ X` with quasi-compact open
complement `j`, the first term is `s_* s^! I`
(`AlgebraicGeometry.ProEtale.closedUpperShriekCompLowerStarIso`). -/
theorem shortExact_supportsShortComplex (I : CochainComplex (Sheaf (ProEt.topology X) A) ℤ)
    [∀ n, Injective (I.X n)] :
    (supportsShortComplex A j I).ShortExact := by
  have : Epi (supportsUnit A j I) := by
    refine HomologicalComplex.epi_of_epi_f _ fun n ↦ ?_
    have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective A j (I.X n)
    rw [supportsUnit_f]
    infer_instance
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (by rw [supportsShortComplex_f]; infer_instance) this

end ProEtale

end AlgebraicGeometry
