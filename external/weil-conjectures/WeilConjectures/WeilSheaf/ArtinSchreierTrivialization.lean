/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.WeilSheaf.ArtinSchreierInertia

/-!
# The trivialisation of the Artin–Schreier sheaf over the Artin–Schreier cover

Let `ℒ_ψ ⊆ ĀS_* ℚ̄_ℓ` be the `ψ`-isotypic component on the geometric affine line, the image of
the projector `e_ψ`. After pullback along the geometric Artin–Schreier map `ĀS`, the projector
becomes averaging followed by splitting
(`AlgebraicGeometry.affineLine.artinSchreierAverageModHom_splitModHom_of_restriction`), so the
uniqueness of epi-mono factorisations gives a trivialisation `ℚ̄_ℓ ≅ ĀS^* ℒ_ψ` whose composite with
`ĀS^* ℒ_ψ ⊆ ĀS^* ĀS_* ℚ̄_ℓ` is the splitting map. The deck transformations `σ̄_c` of `ĀS` act on
its section through `ψ(-c)` (`AlgebraicGeometry.affineLine.germ_artinSchreierSplitSection`).

## Main declarations

- `AlgebraicGeometry.affineLine.artinSchreierImage`: the underlying sheaf `ℒ_ψ` of the image.
- `AlgebraicGeometry.affineLine.artinSchreierCarrierIso`: it is the underlying sheaf of the image
  of `e_ψ` in Weil sheaves.
- `AlgebraicGeometry.affineLine.artinSchreierTrivialization`: `ℚ̄_ℓ ≅ ĀS^* ℒ_ψ`.
- `AlgebraicGeometry.affineLine.germ_artinSchreierTrivialization`: the deck transformation `σ̄_c`
  multiplies its section by `ψ(-c)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

local notation "Ā" => Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

variable (l) in
/-- The underlying morphism `ĀS_* ℚ̄_ℓ ⟶ ĀS_* ℚ̄_ℓ` of the projector `e_ψ`. -/
noncomputable abbrev affineLine.artinSchreierIdempotentHom (ψ : AddChar k₀ (PadicAlgCl l)) :
    (ĀS)_*ᵃ[l].obj (ProEtale.AdicSheaf.unit l Ā) ⟶ (ĀS)_*ᵃ[l].obj (ProEtale.AdicSheaf.unit l Ā) :=
  (ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).map
    (WeilSheaf.artinSchreierIdempotent ψ)

variable (l) in
/-- The `ψ`-isotypic component `ℒ_ψ ⊆ ĀS_* ℚ̄_ℓ` on the geometric affine line, the image of the
underlying morphism of the projector `e_ψ`. -/
noncomputable abbrev affineLine.artinSchreierImage (ψ : AddChar k₀ (PadicAlgCl l)) :
    ProEtale.AdicSheaf l Ā :=
  image (affineLine.artinSchreierIdempotentHom l ψ)

-- Instance search for the (co)kernels in the category of sheaves of modules is slow.
/-- The underlying sheaf of the image of the projector `e_ψ` in Weil sheaves is the image of the
underlying morphism. -/
noncomputable def affineLine.artinSchreierCarrierIso (ψ : AddChar k₀ (PadicAlgCl l)) :
    (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier ≅
      affineLine.artinSchreierImage l ψ := by
  let Φ := ObjectProperty.ι (WeilSheaf.objectProperty k₀ l (affineLine k₀)) ⋙
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))
  have := ObjectProperty.preservesKernels_ι _ (cokernel.π (WeilSheaf.artinSchreierIdempotent ψ))
  have := ObjectProperty.preservesCokernels_ι _ (WeilSheaf.artinSchreierIdempotent ψ)
  have : HasColimitsOfShape WalkingParallelPair (ProEtale.AdicSheaf l Ā) := inferInstance
  have : HasLimitsOfShape WalkingParallelPair (ProEtale.AdicSheaf l Ā) := inferInstance
  exact Φ.mapIso (Abelian.imageIsoImage _).symm ≪≫ Abelian.PreservesImage.iso Φ _ ≪≫
    Abelian.imageIsoImage _

/-- After pullback along `ĀS`, the projector `e_ψ` is averaging followed by splitting. -/
lemma affineLine.artinSchreierAverageModHom_comp_splitModHom (ψ : AddChar k₀ (PadicAlgCl l)) :
    affineLine.artinSchreierAverageModHom l ψ ≫ affineLine.artinSchreierSplitModHom l ψ =
      (ĀS)^*ᵃ[l].map (affineLine.artinSchreierIdempotentHom l ψ) :=
  affineLine.artinSchreierAverageModHom_splitModHom_of_restriction ψ _
    (affineLine.restriction_map_artinSchreierIdempotent ψ)

instance (ψ : AddChar k₀ (PadicAlgCl l)) :
    IsSplitEpi (affineLine.artinSchreierAverageModHom l ψ) :=
  ⟨⟨_, affineLine.artinSchreierSplitModHom_averageModHom ψ⟩⟩

instance (ψ : AddChar k₀ (PadicAlgCl l)) :
    IsSplitMono (affineLine.artinSchreierSplitModHom l ψ) :=
  ⟨⟨_, affineLine.artinSchreierSplitModHom_averageModHom ψ⟩⟩

variable (l) in
/-- **The trivialisation `ℚ̄_ℓ ≅ ĀS^* ℒ_ψ`**: both are the image of `ĀS^* e_ψ`, through the
factorisations `ĀS^* e_ψ = split ∘ average` and `ĀS^* e_ψ = ĀS^*(ℒ_ψ ⊆ ĀS_* ℚ̄_ℓ) ∘ ĀS^*(ĀS_* ℚ̄_ℓ ↠
ℒ_ψ)`. -/
noncomputable def affineLine.artinSchreierTrivialization (ψ : AddChar k₀ (PadicAlgCl l)) :
    ProEtale.AdicSheaf.unit l Ā ≅ (ĀS)^*ᵃ[l].obj (affineLine.artinSchreierImage l ψ) :=
  haveI := strongEpi_of_epi ((ĀS)^*ᵃ[l].map
    (factorThruImage (affineLine.artinSchreierIdempotentHom l ψ)))
  image.isoStrongEpiMono _ _ (affineLine.artinSchreierAverageModHom_comp_splitModHom ψ) ≪≫
    (image.isoStrongEpiMono ((ĀS)^*ᵃ[l].map
        (factorThruImage (affineLine.artinSchreierIdempotentHom l ψ)))
      ((ĀS)^*ᵃ[l].map (image.ι (affineLine.artinSchreierIdempotentHom l ψ)))
      (by rw [← Functor.map_comp, image.fac])).symm

/-- The trivialisation followed by `ĀS^* ℒ_ψ ⊆ ĀS^* ĀS_* ℚ̄_ℓ` is the splitting map. -/
@[reassoc]
lemma affineLine.artinSchreierTrivialization_hom_comp (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineLine.artinSchreierTrivialization l ψ).hom ≫
        (ĀS)^*ᵃ[l].map (image.ι (affineLine.artinSchreierIdempotentHom l ψ)) =
      affineLine.artinSchreierSplitModHom l ψ := by
  simp [affineLine.artinSchreierTrivialization]

/-- **The deck transformations act on the trivialisation through `ψ`.** The germ along the deck
transformation `σ̄_c` of `ĀS` multiplies the section of the trivialisation `ℚ̄_ℓ ≅ ĀS^* ℒ_ψ` by
`ψ(-c)`. -/
theorem affineLine.germ_artinSchreierTrivialization (ψ : AddChar k₀ (PadicAlgCl l)) (c : k₀) :
    (ProEtale.factorGerm (WeilCoefficients.{u} l)
        (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)
        (affineLine.artinSchreierImage l ψ).X).hom
        (ProEtale.globalSectionOfModHom (affineLine.artinSchreierTrivialization l ψ).hom) =
      ULift.up (ψ (-c)) •
        ProEtale.globalSectionOfModHom (affineLine.artinSchreierTrivialization l ψ).hom := by
  have hsplit := affineLine.artinSchreierTrivialization_hom_comp (l := l) ψ
  set θ := affineLine.artinSchreierTrivialization l ψ
  set ι := image.ι (affineLine.artinSchreierIdempotentHom l ψ)
  -- `ĀS^*(ℒ_ψ ⊆ ĀS_* ℚ̄_ℓ)` has the retraction `average ≫ θ`
  have hret : (ĀS)^*ᵃ[l].map ι ≫ affineLine.artinSchreierAverageModHom l ψ ≫ θ.hom = 𝟙 _ := by
    rw [← cancel_epi θ.hom, reassoc_of% hsplit,
      reassoc_of% (affineLine.artinSchreierSplitModHom_averageModHom (l := l) ψ), Category.comp_id]
  have hinj : Function.Injective
      ((Sheaf.Γ (Scheme.ProEt.topology Ā) (WeilCoefficients.{u} l)).map
        ((ĀS)^*ᵃ[l].map ι).hom).hom := by
    refine Function.LeftInverse.injective (g := ((Sheaf.Γ _ _).map
      (affineLine.artinSchreierAverageModHom l ψ ≫ θ.hom).hom).hom) fun x ↦ ?_
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', hret, Mod.id_hom',
      CategoryTheory.Functor.map_id]
    rfl
  have hθs : ((Sheaf.Γ (Scheme.ProEt.topology Ā) (WeilCoefficients.{u} l)).map
      ((ĀS)^*ᵃ[l].map ι).hom).hom (ProEtale.globalSectionOfModHom θ.hom) =
      affineLine.artinSchreierSplitSection l ψ := by
    rw [affineLine.artinSchreierSplitSection, ← hsplit, ProEtale.globalSectionOfModHom_eq,
      ProEtale.globalSectionOfModHom_eq, Mod.comp_hom', Functor.map_comp,
      ConcreteCategory.comp_apply]
  apply hinj
  rw [map_smul, hθs, ← affineLine.germ_artinSchreierSplitSection, ← hθs]
  exact (congrArg (fun φ ↦ φ.hom (ProEtale.globalSectionOfModHom θ.hom))
    (ProEtale.factorGerm_naturality (WeilCoefficients.{u} l)
      (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c) ι.hom)).symm

end AlgebraicGeometry
