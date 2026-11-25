/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

/-!
# Pullback of free étale sheaves of modules

For a morphism of schemes `h : Y ⟶ T` and an étale `T`-scheme `W`, the pullback `h^* Λ[W]` of
the free sheaf of `Λ`-modules `Λ[W] = j_{W!} Λ_W` is the free sheaf `Λ[W ×_T Y]`
(`AlgebraicGeometry.Etale.upperStarFreeSheafIso`). We show that this isomorphism is the unique
one which, on the generating sections, is given by the unit of the adjunction `h^* ⊣ h_*`
[Stacks 03S6].

## Main results

- `AlgebraicGeometry.Etale.existsUnique_upperStarFreeSheafIso`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {T Y : Scheme.{u}} (h : Y ⟶ T) (W : T.Etale)

/-- Precomposition with the inverse of `h^* Λ[W] ≅ Λ[W ×_T Y]` is the bijection
`AlgebraicGeometry.Etale.upperStarFreeSheafHomEquiv`. -/
lemma upperStarFreeSheafIso_inv_comp
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ T).obj W) ⟶ G) :
    (Etale.upperStarFreeSheafIso Λ h W).inv ≫ a =
      Etale.upperStarFreeSheafHomEquiv Λ h W G a := by
  rw [← Category.id_comp a, Etale.upperStarFreeSheafHomEquiv_comp, Category.id_comp]
  rfl

/-- **Inverse image of free étale sheaves of modules** [Stacks 03S6]: for `h : Y ⟶ T` and an
étale `T`-scheme `W`, with `W' = W ×_T Y`, there is a unique isomorphism
`θ : h^* Λ[W] ≅ Λ[W']` of sheaves of `Λ`-modules such that for every sheaf `H` on `T_ét` and
every section `s ∈ H(W)`, with `φ_s : Λ[W] ⟶ H` the morphism corresponding to `s`, the section
of `h^* H` over `W'` corresponding to `h^*(φ_s) ∘ θ⁻¹ : Λ[W'] ⟶ h^* H` is the
image `η_H(s)` of `s` under the unit `η : H ⟶ h_* h^* H`, a section of
`(h_* h^* H)(W) = (h^* H)(W')`. Here `Λ[W]` is the free sheaf `j_{W!} Λ_W`, the sheafification
of `V ↦ Λ^{(Hom_T(V, W))}`, and the correspondence `Hom(Λ[W], H) ≃ H(W)` is
`AlgebraicGeometry.Etale.freeSheafHomEquiv`.
(blueprint: `lem-weil-pbc-inverse-image-free-etale-module`) -/
theorem existsUnique_upperStarFreeSheafIso :
    ∃! θ : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ T).obj W) ≅
        (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W),
      ∀ (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (s : H.obj.obj (op W)),
        Etale.freeSheafHomEquiv Λ _ _
            (θ.inv ≫ (h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheafHomEquiv Λ W H).symm s)) =
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app H).hom.app (op W) s
    := by
  have hstd : ∀ (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (s : H.obj.obj (op W)),
      Etale.freeSheafHomEquiv Λ _ _ ((Etale.upperStarFreeSheafIso Λ h W).inv ≫
          (h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheafHomEquiv Λ W H).symm s)) =
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app H).hom.app (op W) s := by
    intro H s
    rw [upperStarFreeSheafIso_inv_comp]
    change Etale.freeSheafHomEquiv Λ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) _
      ((Etale.freeSheafHomEquiv Λ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) _).symm
      (Etale.freeSheafHomEquiv Λ W _ ((upperStarLowerStarAdjunction _ h).homEquiv _ _
        ((h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheafHomEquiv Λ W H).symm s))))) = _
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Adjunction.unit_naturality,
      Etale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
    rfl
  refine ⟨Etale.upperStarFreeSheafIso Λ h W, hstd, fun θ hθ ↦ ?_⟩
  have key (θ' : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ T).obj W) ≅
        (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W))
      (hθ' : ∀ (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (s : H.obj.obj (op W)),
        Etale.freeSheafHomEquiv Λ _ _
            (θ'.inv ≫
              (h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheafHomEquiv Λ W H).symm s)) =
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app H).hom.app (op W) s) :
      Etale.freeSheafHomEquiv Λ _ _ θ'.inv =
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app _).hom.app (op W)
          (Etale.freeSheafHomEquiv Λ W _ (𝟙 _)) := by
    have := hθ' _ (Etale.freeSheafHomEquiv Λ W _ (𝟙 _))
    rwa [Equiv.symm_apply_apply, CategoryTheory.Functor.map_id, Category.comp_id] at this
  exact Iso.ext ((Iso.inv_eq_inv _ _).1 ((Etale.freeSheafHomEquiv Λ _ _).injective
    ((key θ hθ).trans (key _ hstd).symm)))

end AlgebraicGeometry.Etale
