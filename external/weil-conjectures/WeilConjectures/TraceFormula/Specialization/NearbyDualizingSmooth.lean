/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Smooth
public import WeilConjectures.TraceFormula.Specialization.KernelPullbackDeformation
public import WeilConjectures.TraceFormula.Specialization.NearbyCyclesBraided
public import WeilConjectures.TraceFormula.Specialization.NearbyCyclesTateTwist
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseProper
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothUnit

/-!

# The dualizing map of a smooth proper trait model over a generic base

Let `N` be a trait model of an `F`-scheme `X₁` over the generic base `(F, X₁)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`) whose structure morphism `q : 𝒳 ⟶ S` is proper
and smooth of pure relative dimension `d`, with `X₁` proper and smooth of pure relative
dimension `d` over `F`, and whose geometric generic fibre is all of `X₁ ×_F Spec Ω`. This file
proves that the dualizing map `θ_N : Ψ_N ω_{X₁} ⟶ ω_{X'}` of a family of dualizing maps over
generic bases (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`) is an isomorphism
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_of_smooth`; blueprint
`prose-E-15`, smooth case).

* **Global sections**
  (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_lowerStar_map_θ_of_smooth`):
  `Ra'_*(θ_N)` is invertible. Global sections of the duality map at the unit are invertible
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_lowerStar_nearbyDualityMap_of_isProper`),
  and the duality map at the unit is `θ_N` up to the unit `ε_Ψ = σ_N : ℚ̄_ℓ ⟶ Ψ_N ℚ̄_ℓ` of the lax
  monoidal structure of nearby cycles
  (`CategoryTheory.Verdier.isIso_map_of_isIso_map_nearbyDualityMap_unit`), invertible for smooth
  `q` (`NearbyCyclesModel.IsTraitModelOver.isIso_boundedConstructibleUnit_of_smooth`).
* **An abstract isomorphism**
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.nearbyCyclesDualizingComplexIsoOfSmooth`):
  `Ψ_N ω_{X₁} ≅ ω_{X'}`, the composite
  ```
  Ψ_N ω_{X₁} ≅ Ψ_N ℚ̄_ℓ(d)[2d] ≅ Ψ_N(ℚ̄_ℓ ⊗ ℚ̄_ℓ(d)[2d]) ≅ Ψ_N ℚ̄_ℓ ⊗ ℚ̄_ℓ(d)[2d]
    ≅ ℚ̄_ℓ ⊗ ℚ̄_ℓ(d)[2d] ≅ ℚ̄_ℓ(d)[2d] ≅ ω_{X'}
  ```
  of smooth purity on both fibres (`ProEtale.CondensedRing.isIso_smoothPurityMap`, an input of
  the smooth purity section), the commutation of nearby cycles with Tate twists
  (`NearbyCyclesModel.nearbyCyclesTateTwistIso`, with the pullbacks of the Tate twists
  `ProEtale.upperStarTateTwistDerivedIso`) and the invertible specialization
  unit.
* **Invertibility**: the endomorphism `ψ⁻¹ ∘ θ_N` of `ω_{X'}` is invertible on global sections,
  hence invertible (`ProEtale.CondensedRing.isIso_of_isIso_lowerStar_map_dualizingComplex`).

The isomorphism `θ_N` is not identified with the composite above: this would need the
compatibility of the purity isomorphisms with base change and of the trace with specialization,
which are not available (see `WeilConjectures.SmoothPurity.Defs`). What is proved is that the two
differ by an automorphism of `ω_{X'}`
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.exists_θ_eq_of_smooth`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {F : Type u} [Field F] {k' : Type u} [Field k']
  [IsSepClosed k'] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
  [IsSeparated X₁.hom] {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom]
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The unit `ε_Ψ` of the lax monoidal structure of nearby cycles of a smooth trait model over a
generic base is invertible: it is the specialization unit
(`NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal_ε`). -/
lemma IsTraitModelOfGenericBase.isIso_laxMonoidal_ε_of_smooth
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [Smooth q] :
    IsIso (@Functor.LaxMonoidal.ε _ _ _ _ _ _
      (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)))
      (boundedConstructibleNearbyCyclesLaxMonoidal _)) := by
  rw [boundedConstructibleNearbyCyclesLaxMonoidal_ε]
  exact h.isTraitModelOver.isIso_boundedConstructibleUnit_of_smooth _

omit [IsSepClosed k'] [Fact (ringChar F).Prime] [Fact (ringChar k').Prime]
  [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X'.hom] in
/-- The schemes of a trait model over a generic base are quasi-compact and quasi-separated, so
that the pullbacks along `ε`, `j` and `i` commute with sequential limits. -/
lemma IsTraitModelOfGenericBase.compactSpace_quasiSeparatedSpace
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    (CompactSpace X₁.left ∧ QuasiSeparatedSpace X₁.left) ∧
      (CompactSpace M.total ∧ QuasiSeparatedSpace M.total) ∧
      (CompactSpace M.generic ∧ QuasiSeparatedSpace M.generic) ∧
      (CompactSpace X'.left ∧ QuasiSeparatedSpace X'.left) := by
  have := h.isTraitModelOver.quasiCompact
  have := h.isTraitModelOver.isSeparated
  have : QuasiCompact g :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.isTraitModelOver.isPullback_j ‹_›
  have : QuasiSeparated g :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) h.isTraitModelOver.isPullback_j
      inferInstance
  exact ⟨⟨QuasiCompact.compactSpace_of_compactSpace X₁.hom,
      quasiSeparatedSpace_of_quasiSeparated X₁.hom⟩,
    ⟨QuasiCompact.compactSpace_of_compactSpace q, quasiSeparatedSpace_of_quasiSeparated q⟩,
    ⟨QuasiCompact.compactSpace_of_compactSpace g, quasiSeparatedSpace_of_quasiSeparated g⟩,
    ⟨QuasiCompact.compactSpace_of_compactSpace X'.hom,
      quasiSeparatedSpace_of_quasiSeparated X'.hom⟩⟩

/-- **Nearby cycles of the Tate twist of a smooth trait model over a generic base**:
`Ψ_N(ℚ̄_ℓ,X₁(d)[n]) ≅ ℚ̄_ℓ,X'(d)[n]`, the composite of
`Ψ_N(ℚ̄_ℓ ⊗ ℚ̄_ℓ(d)[n]) ≅ Ψ_N ℚ̄_ℓ ⊗ ℚ̄_ℓ(d)[n]` (`NearbyCyclesModel.nearbyCyclesTateTwistIso`,
with the pullbacks of the Tate twists `ProEtale.upperStarTateTwistDerivedIso`)
and of the inverse of the invertible specialization unit `σ_N : ℚ̄_ℓ ⟶ Ψ_N ℚ̄_ℓ`. -/
noncomputable def IsTraitModelOfGenericBase.nearbyCyclesTateTwistIsoOfSmooth
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [Smooth q] (d n : ℤ) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj
        (boundedConstructibleTateTwist ℓ X₁ d n) ≅ boundedConstructibleTateTwist ℓ X' d n :=
  have hc := h.compactSpace_quasiSeparatedSpace
  have := hc.1.1
  have := hc.1.2
  have := hc.2.1.1
  have := hc.2.1.2
  have := hc.2.2.1.1
  have := hc.2.2.1.2
  have := hc.2.2.2.1
  have := hc.2.2.2.2
  have : NeZero (ℓ : F) := neZero_natCast_of_ringChar_ne ℓ
  have : NeZero (ℓ : k') := neZero_natCast_of_ringChar_ne ℓ
  have := h.isTraitModelOver.isIso_boundedConstructibleUnit_of_smooth
    (h.preservesBoundedConstructible (ℓ := ℓ))
  (boundedConstructibleNearbyCycles _).mapIso (λ_ _).symm ≪≫
    nearbyCyclesTateTwistIso (h.preservesBoundedConstructible (ℓ := ℓ))
      (isDualizable_tateTwistDerived_of_trait ℓ q d)
      (ProEtale.upperStarTateTwistDerivedIso ℓ M.ε X₁.hom d)
      (ProEtale.upperStarTateTwistDerivedIso ℓ M.j
        (q ≫ traitToBase k' k') d)
      (ProEtale.upperStarTateTwistDerivedIso ℓ M.i
        (q ≫ traitToBase k' k') d) n (𝟙_ _) ≪≫
    whiskerRightIso (asIso (boundedConstructibleUnit ℓ
      (h.preservesBoundedConstructible (ℓ := ℓ)))).symm _ ≪≫ λ_ _

/-- **The nearby cycles of the dualizing complex of a smooth trait model over a generic base**:
for `X₁` smooth of pure relative dimension `d` over `F`, `X'` smooth of pure relative dimension
`d` over `k'` and `q` smooth, `Ψ_N ω_{X₁} ≅ ω_{X'}`, through smooth purity
`ω ≅ ℚ̄_ℓ(d)[2d]` on both fibres (`ProEtale.CondensedRing.smoothPurityMap`) and
`Ψ_N(ℚ̄_ℓ(d)[2d]) ≅ ℚ̄_ℓ(d)[2d]`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.nearbyCyclesTateTwistIsoOfSmooth`). -/
noncomputable def IsTraitModelOfGenericBase.nearbyCyclesDualizingComplexIsoOfSmooth
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [Smooth q] (d : ℕ)
    [SmoothOfRelativeDimension d (CondensedRing.toPoint X₁).left]
    [SmoothOfRelativeDimension d (CondensedRing.toPoint X').left] :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj
        (dualizingComplex ℓ X₁) ≅ dualizingComplex ℓ X' :=
  (boundedConstructibleNearbyCycles _).mapIso
      (asIso (smoothPurityMap ℓ (CondensedRing.toPoint X₁) d)).symm ≪≫
    h.nearbyCyclesTateTwistIsoOfSmooth ℓ d (2 * d) ≪≫
    asIso (smoothPurityMap ℓ (CondensedRing.toPoint X') d)

omit [IsSepClosed k'] [Fact (ringChar F).Prime] [Fact (ringChar k').Prime]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The special fibre of a trait model whose structure morphism is smooth of pure relative
dimension `d` is smooth of pure relative dimension `d` over `k'`. -/
lemma IsTraitModelOfGenericBase.smoothOfRelativeDimension_toPoint_special
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) (d : ℕ) [SmoothOfRelativeDimension d q] :
    SmoothOfRelativeDimension d (CondensedRing.toPoint X').left := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange d
  rw [toPoint_left]
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
    h.isTraitModelOver.isPullback_i ‹_›

namespace NearbyDualizingDataOfGenericBase

variable {ℓ} (D : NearbyDualizingDataOfGenericBase k' ℓ)

/-- **Global sections of the dualizing map of a smooth proper model**: for a trait model `N`
over a generic base with `q` smooth and proper, `X₁` and `X'` proper and full geometric generic
fibre, `Ra'_*(θ_N)` is invertible: global sections of the duality map at the unit are invertible
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_lowerStar_nearbyDualityMap_of_isProper`), and
the unit `ε_Ψ` of nearby cycles is invertible
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_laxMonoidal_ε_of_smooth`), so
`CategoryTheory.Verdier.isIso_map_of_isIso_map_nearbyDualityMap_unit` applies. -/
theorem isIso_lowerStar_map_θ_of_smooth (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint X').left]
    [IsProper q] [Smooth q] (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    IsIso ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map (D.θ h)) := by
  let := boundedConstructibleNearbyCyclesLaxMonoidal (h.preservesBoundedConstructible (ℓ := ℓ))
  have := h.isIso_laxMonoidal_ε_of_smooth ℓ
  have hμ : (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))) A B) =
      boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ)) := by
    funext A B
    exact boundedConstructibleNearbyCycles_μ _ A B
  have h₁ := h.isIso_lowerStar_nearbyDualityMap_of_isProper ℓ D hgen (𝟙_ _)
  rw [← hμ] at h₁
  exact Verdier.isIso_map_of_isIso_map_nearbyDualityMap_unit _ _ _ h₁

/-- **The dualizing map of a smooth proper model is an isomorphism**, given some isomorphism
`ψ : Ψ_N ω_{X₁} ≅ ω_{X'}`: the endomorphism `ψ⁻¹ ∘ θ_N` of `ω_{X'}` is invertible on global
sections (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_lowerStar_map_θ_of_smooth`),
hence invertible (`ProEtale.CondensedRing.isIso_of_isIso_lowerStar_map_dualizingComplex`). -/
theorem isIso_θ_of_iso (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint X').left]
    [IsProper q] [Smooth q] (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (ψ : (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj
        (dualizingComplex ℓ X₁) ≅ dualizingComplex ℓ X') :
    IsIso (D.θ h) := by
  have := D.isIso_lowerStar_map_θ_of_smooth h hgen
  have : IsIso ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map
      (ψ.inv ≫ D.θ h)) := by
    rw [Functor.map_comp]
    infer_instance
  have := isIso_of_isIso_lowerStar_map_dualizingComplex ℓ X' (ψ.inv ≫ D.θ h)
  exact IsIso.of_isIso_comp_left ψ.inv _

/-- **The dualizing map of a smooth proper model is an isomorphism** (blueprint
`prose-E-15`, smooth case): for a trait model `N` over a generic base whose
structure morphism `q` is proper and smooth of pure relative dimension `d`, with `X₁` proper and
smooth of pure relative dimension `d` over `F` and full geometric generic fibre, the dualizing
map `θ_N : Ψ_N ω_{X₁} ⟶ ω_{X'}` is an isomorphism. -/
theorem isIso_θ_of_smooth (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint X').left]
    [IsProper q] (d : ℕ) [SmoothOfRelativeDimension d q]
    [SmoothOfRelativeDimension d (CondensedRing.toPoint X₁).left]
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    IsIso (D.θ h) := by
  have : Smooth q := SmoothOfRelativeDimension.smooth d q
  have := h.smoothOfRelativeDimension_toPoint_special d
  exact D.isIso_θ_of_iso h hgen (h.nearbyCyclesDualizingComplexIsoOfSmooth ℓ d)

/-- **The dualizing map of a smooth proper model, through smooth purity**: under the hypotheses
of `NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_of_smooth`, `θ_N` is the
isomorphism `Ψ_N ω_{X₁} ≅ ω_{X'}` of smooth purity on both fibres and of the invertible
specialization unit
(`NearbyCyclesModel.IsTraitModelOfGenericBase.nearbyCyclesDualizingComplexIsoOfSmooth`) followed
by an automorphism of `ω_{X'}`. -/
theorem exists_θ_eq_of_smooth (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint X').left]
    [IsProper q] (d : ℕ) [SmoothOfRelativeDimension d q]
    [SmoothOfRelativeDimension d (CondensedRing.toPoint X₁).left]
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    have : Smooth q := SmoothOfRelativeDimension.smooth d q
    have := h.smoothOfRelativeDimension_toPoint_special d
    ∃ u : dualizingComplex ℓ X' ≅ dualizingComplex ℓ X',
      D.θ h = (h.nearbyCyclesDualizingComplexIsoOfSmooth ℓ d).hom ≫ u.hom := by
  intro _ _
  have := D.isIso_θ_of_smooth h d hgen
  exact ⟨(h.nearbyCyclesDualizingComplexIsoOfSmooth ℓ d).symm ≪≫ asIso (D.θ h), by simp⟩

end NearbyDualizingDataOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
