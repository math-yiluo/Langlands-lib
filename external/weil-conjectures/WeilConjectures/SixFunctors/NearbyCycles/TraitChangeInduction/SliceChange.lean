/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Defs
public import WeilConjectures.TraceFormula.Specialization.SliceTraitMap

/-!

# The change of trait between the slices of a model and of its base change

Let `ι : R₁ ⟶ R₂` be a change of trait, `H : S₂(x) ⟶ S₁(x)` a morphism of slice traits over it
(`AlgebraicGeometry.SliceTrait.Hom`), `φ : M ⟶ N` a morphism of models over `Spec ι`, and
`cN : 𝒳_N ⟶ 𝔸¹_{S₁}`, `cM : 𝒳_M ⟶ 𝔸¹_{S₂}` compatible coordinates. The slices
`N' = 𝒳_N ×_{𝔸¹_{S₁}} S₁(x)` and `M' = 𝒳_M ×_{𝔸¹_{S₂}} S₂(x)`
(`NearbyCyclesModel.sliceTraitModel`) are related by a morphism of models
`NearbyCyclesModel.sliceTraitChangeHom : M' ⟶ N'` over `Spec ψ : S₂(x) ⟶ S₁(x)`; if the square of
total spaces of `φ` is cartesian over `Spec ι`, so is that of `sliceTraitChangeHom` over `Spec ψ`
(`NearbyCyclesModel.isPullback_sliceTraitChangeHom_total`). This is the change of trait to which
the induction hypothesis of Deligne's proof of SGA 4½, [Th. finitude], Prop. 3.7, applies
(`NearbyCyclesModel.isIso_pullbackExchange_sliceTraitChangeHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section Hom

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] {c : Ω₁ →+* Ω₂}
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁}
  {b₂ : R₂ →+* κ₂} {D₁ : SliceTrait a₁ b₁} {D₂ : SliceTrait a₂ b₂} (H : SliceTrait.Hom ι c D₁ D₂)
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)))
  (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)))
  (hcM : cM ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom ι)) = φ.total ≫ cN)

/-- The map of total spaces `𝒳_M ×_{𝔸¹_{S₂}} S₂(x) ⟶ 𝒳_N ×_{𝔸¹_{S₁}} S₁(x)` of the slices. -/
noncomputable def sliceTraitChangeTotal : sliceTraitTotal D₂ M cM ⟶ sliceTraitTotal D₁ N cN :=
  pullback.map _ _ _ _ φ.total (Spec.map (CommRingCat.ofHom H.ψ)) (affineLineMap ι) hcM
    H.spec_ψ.symm

@[reassoc (attr := simp)]
lemma sliceTraitChangeTotal_fst :
    sliceTraitChangeTotal H φ cN cM hcM ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.total :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sliceTraitChangeTotal_snd :
    sliceTraitChangeTotal H φ cN cM hcM ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom H.ψ) :=
  pullback.lift_snd _ _ _

/-- The map of geometric generic fibres of the slices, over `Spec Ω'₂ ⟶ Spec Ω'₁`. -/
noncomputable def sliceTraitChangeGeneric :
    (sliceTraitModel D₂ M cM).generic ⟶ (sliceTraitModel D₁ N cN).generic :=
  pullback.map _ _ _ _ (sliceTraitChangeTotal H φ cN cM hcM)
    (Spec.map (CommRingCat.ofHom H.ΩMap)) (Spec.map (CommRingCat.ofHom H.ψ))
    (sliceTraitChangeTotal_snd H φ cN cM hcM).symm (by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        H.ΩMap_comp_a])

/-- The map of special fibres of the slices, over `Spec κ'₂ ⟶ Spec κ'₁`. -/
noncomputable def sliceTraitChangeSpecial :
    pullback (sliceTraitStructure D₂ M cM) (Spec.map (CommRingCat.ofHom D₂.b)) ⟶
      pullback (sliceTraitStructure D₁ N cN) (Spec.map (CommRingCat.ofHom D₁.b)) :=
  pullback.map _ _ _ _ (sliceTraitChangeTotal H φ cN cM hcM)
    (Spec.map (CommRingCat.ofHom H.κMap)) (Spec.map (CommRingCat.ofHom H.ψ))
    (sliceTraitChangeTotal_snd H φ cN cM hcM).symm (by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        H.b_comp_ψ])

/-- **The change of trait between the slices** `M' ⟶ N'`, over the map of total spaces of the
slices and the map of their special fibres. -/
@[simps]
noncomputable def sliceTraitChangeHom :
    (sliceTraitModel D₂ M cM).Hom (sliceTraitModel D₁ N cN) (sliceTraitChangeTotal H φ cN cM hcM)
      (sliceTraitChangeSpecial H φ cN cM hcM) where
  total := sliceTraitChangeTotal H φ cN cM hcM
  generic := sliceTraitChangeGeneric H φ cN cM hcM
  comm_j := by simp [sliceTraitChangeGeneric]
  comm_i := by simp [sliceTraitChangeSpecial]
  comm_ε := by simp [sliceTraitChangeGeneric]

/-- The map of geometric generic fibres of the slices lies over `Spec Ω'₂ ⟶ Spec Ω'₁`. -/
@[reassoc]
lemma sliceTraitChangeGeneric_snd :
    sliceTraitChangeGeneric H φ cN cM hcM ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom H.ΩMap) :=
  pullback.lift_snd _ _ _

/-- The map of special fibres of the slices lies over `Spec κ'₂ ⟶ Spec κ'₁`. -/
@[reassoc]
lemma sliceTraitChangeSpecial_snd :
    sliceTraitChangeSpecial H φ cN cM hcM ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom H.κMap) :=
  pullback.lift_snd _ _ _

variable {φ cN cM} in
/-- **The square of total spaces of the change of trait of the slices is cartesian** if that of
`φ` is: `𝒳_M ×_{𝔸¹_{S₂}} S₂(x) = 𝒳_N ×_{𝔸¹_{S₁}} S₂(x) = (𝒳_N ×_{𝔸¹_{S₁}} S₁(x)) ×_{S₁(x)} S₂(x)`.
-/
theorem isPullback_sliceTraitChangeHom_total {q₁ : N.total ⟶ Spec (.of R₁)}
    {q₂ : M.total ⟶ Spec (.of R₂)} (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) = q₁)
    (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂) :
    IsPullback (sliceTraitChangeTotal H φ cN cM hcM) (pullback.snd cM D₂.toAffineLine)
      (pullback.snd cN D₁.toAffineLine) (Spec.map (CommRingCat.ofHom H.ψ)) := by
  -- `𝒳_M = 𝒳_N ×_{𝔸¹_{S₁}} 𝔸¹_{S₂}`
  have hA := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom ι))
  have hMN : IsPullback φ.total cM cN (affineLineMap ι) := by
    refine IsPullback.of_bot ?_ hcM.symm hA
    rw [hcM', hcN]
    exact hφ
  -- `𝒳_M ×_{𝔸¹_{S₂}} S₂(x) = 𝒳_N ×_{𝔸¹_{S₁}} S₂(x)`
  have h₁ := (IsPullback.of_hasPullback cM D₂.toAffineLine).paste_horiz hMN
  have h₂ := (IsPullback.of_hasPullback cN D₁.toAffineLine)
  refine IsPullback.of_right ?_ (sliceTraitChangeTotal_snd H φ cN cM hcM) h₂
  rw [sliceTraitChangeTotal_fst, H.spec_ψ]
  exact h₁

/-- A slice trait over an unramified change of trait is unramified over the slice trait of the
base: the uniformizer of `R₁` is one of `S₁(x)` and of `S₂(x)`. -/
lemma _root_.AlgebraicGeometry.SliceTrait.Hom.maximalIdeal_eq_map
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι) :
    maximalIdeal D₂.R = (maximalIdeal D₁.R).map H.ψ := by
  rw [D₂.maximalIdeal_eq, hun, Ideal.map_map, ← H.ψ_comp_φ, ← Ideal.map_map,
    ← D₁.maximalIdeal_eq]

/-- A prime dividing the naturals vanishing in the residue field of `R₁` divides those vanishing in
the residue field of a slice trait over `R₁`. -/
lemma _root_.AlgebraicGeometry.SliceTrait.dvd_of_natCast_eq_zero (D : SliceTrait a₁ b₁)
    {p : ℕ} (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n) (n : ℕ)
    (hn : (n : ResidueField D.R) = 0) : p ∣ n := by
  refine hp n ((ResidueField.map D.φ).injective ?_)
  rw [map_natCast, map_zero, hn]

end Hom

section Induction

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁]
  [Field Ω₂] {c : Ω₁ →+* Ω₂} {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁]
  [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}

/-- **The induction hypothesis on the slices** (SGA 4½, [Th. finitude], proof of 3.7). If the
invariance of nearby cycles under change of trait holds in chart dimension `m`, it applies to the
change of trait `M' ⟶ N'` between the slices over slice traits `S₁(x)`, `S₂(x)` related by a
morphism of slice traits `H` inducing an isomorphism of closed points (for instance the strict
localizations of `𝔸¹_{S₁}` and `𝔸¹_{S₂}` at the generic points of their special fibres), provided
the slice `𝒳_N ×_{𝔸¹_{S₁}} S₁(x)` locally embeds into `𝔸ᵐ_{S₁(x)}`. -/
theorem isIso_pullbackExchange_sliceTraitChangeHom {m : ℕ} (ih : TraitChangeInvariance.{u} T m)
    {D₁ : SliceTrait a₁ b₁} {D₂ : SliceTrait a₂ b₂} (H : SliceTrait.Hom ι c D₁ D₂)
    [IsIso (Spec.map (CommRingCat.ofHom H.κMap))]
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T))
    {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f') {q₁ : N.total ⟶ Spec (.of R₁)}
    {q₂ : M.total ⟶ Spec (.of R₂)} (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)))
    (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) = q₁)
    [LocallyOfFiniteType cN] [QuasiCompact cN] [IsSeparated cN]
    (hm : (pullback.snd cN D₁.toAffineLine).LocallyEmbedsInAffineSpace m)
    (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)))
    (hcM : cM ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom ι)) = φ.total ≫ cN)
    (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (sliceTraitModel D₁ N cN).generic)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
        (sliceTraitModel D₁ N cN).generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T))
      (sliceTraitModel D₁ N cN).generic
      ((finiteCoefficientDerivedEquivalence _ T).functor.obj K)) :
    IsIso (((sliceTraitChangeHom H φ cN cM hcM).toGeneric.pullbackExchange
      (Profinite.continuousMapRingObj T)).app K) := by
  have he : Spec.map (CommRingCat.ofHom (D₂.b.comp H.ψ)) =
      Spec.map (CommRingCat.ofHom H.κMap) ≫ Spec.map (CommRingCat.ofHom D₁.b) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, H.b_comp_ψ]
  have hNi : IsPullback (sliceTraitModel D₁ N cN).i
      (pullback.snd _ _ ≫ inv (Spec.map (CommRingCat.ofHom H.κMap)))
      (sliceTraitStructure D₁ N cN) (Spec.map (CommRingCat.ofHom (D₂.b.comp H.ψ))) := by
    rw [he]
    exact IsPullback.of_iso (isPullback_sliceTraitModel_i D₁ N cN) (Iso.refl _) (Iso.refl _)
      (asIso (Spec.map (CommRingCat.ofHom H.κMap))).symm (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp)
  have hs : sliceTraitChangeSpecial H φ cN cM hcM ≫ pullback.snd _ _ ≫
      inv (Spec.map (CommRingCat.ofHom H.κMap)) = pullback.snd _ _ := by
    rw [sliceTraitChangeSpecial_snd_assoc, IsIso.hom_inv_id, Category.comp_id]
  exact ih.isIso H.ψ H.injective_ψ (H.maximalIdeal_eq_map hun) p (D₁.dvd_of_natCast_eq_zero hp)
    hpT D₁.a D₂.a H.ΩMap D₁.injective_a D₂.injective_a D₁.isAlgebraic_a D₂.isAlgebraic_a
    H.ΩMap_comp_a D₂.b D₂.ker_b (sliceTraitChangeHom H φ cN cM hcM)
    (sliceTraitStructure D₁ N cN) inferInstance inferInstance inferInstance hm (pullback.snd _ _)
    (isPullback_sliceTraitModel_j D₁ N cN) _ hNi (sliceTraitStructure D₂ M cM)
    (pullback.snd _ _) (isPullback_sliceTraitModel_j D₂ M cM) (pullback.snd _ _)
    (isPullback_sliceTraitModel_i D₂ M cM)
    (isPullback_sliceTraitChangeHom_total H hcM hφ hcN hcM')
    (sliceTraitChangeGeneric_snd H φ cN cM hcM)
    hs K hK

end Induction

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
