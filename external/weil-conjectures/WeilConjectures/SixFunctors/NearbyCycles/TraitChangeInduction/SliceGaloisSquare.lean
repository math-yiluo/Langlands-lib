/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGalois
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelWeaklyEtale

/-!

# The change of trait on the generic slice from the change of the Galois-layer models

In the situation of `WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGalois`,
the model `N₁` (`NearbyCyclesModel.sliceTraitGaloisModel`) maps to `N` by the nilpotent
thickening `r₂` followed by the weakly étale cartesian part of the slice
(`NearbyCyclesModel.sliceTraitGaloisModelHom`), with invertible pullback exchange
(`NearbyCyclesModel.isIso_pullbackExchange_sliceTraitGaloisModelHom`). The square
```
N₂ ──τ──→ N₁
 │ψ_M      │ψ_N
 M ──φ──→  N
```
then shows that the pullback of the exchange of `φ` to the special fibre of the slice of `M` is
invertible as soon as the exchange of `τ` is
(`NearbyCyclesModel.isIso_map_pullbackExchange_of_sliceTraitGaloisChangeHom`): this is the step
of Deligne's proof of SGA 4½, [Th. finitude], 3.7, which identifies the change of trait on the
generic slice with the change of trait on the invariant summands.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme SliceTrait

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ

section General

variable {R₁ R Ω₁ Ω : Type u} [CommRing R₁] [CommRing R] [Algebra R₁ R] [Field Ω₁]
  [Algebra R₁ Ω₁] [Field Ω] [Algebra R Ω] [Algebra Ω₁ Ω] [Algebra R₁ Ω]
  [IsScalarTower R₁ R Ω] [IsScalarTower R₁ Ω₁ Ω]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (q : M.total ⟶ Spec (.of R)) (q₁ : N.total ⟶ Spec (.of R₁)) (g₁ : N.generic ⟶ Spec (.of Ω₁))
  (hN : N.j ≫ q₁ = g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
  (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R)))

/-- The pullback exchange of `N₂ ⟶ φ.cartesianModel ⟶ N` is invertible if `φ.total` is weakly
étale and `Spec(Ω₁ ⊗_{R₁} R)` is a single point: the first map is the identity of total spaces
and the universal homeomorphism `r₂` on generic fibres, the second is weakly étale base change. -/
theorem Hom.isIso_pullbackExchange_traitChangeModelHom_comp_fromCartesian
    [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] R))] [WeaklyEtale φ.total]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsIso ((((φ.traitChangeModelHom Ω q q₁ g₁ hN hq).comp φ.fromCartesian).pullbackExchange
      Λ).app C) := by
  have := φ.isIso_pullbackExchange_fromCartesian_of_weaklyEtale Λ
  exact Hom.isIso_pullbackExchange_app_comp Λ _ _ C inferInstance
    (Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq Λ φ.cartesianModel
      (φ.traitChangeThickening Ω q q₁ g₁ hN hq) (φ.traitChangeModel Ω q q₁ g₁ hN hq) rfl
      (φ.traitChangeModelHom Ω q q₁ g₁ hN hq) HEq.rfl HEq.rfl _)

/-- `NearbyCyclesModel.Hom.isIso_pullbackExchange_traitChangeModelHom_comp_fromCartesian` for a
model `P` and a morphism `ψ` equal to `N₂` and `N₂ ⟶ φ.cartesianModel ⟶ N` (to state it in
abbreviated forms without comparing large pullback exchanges). -/
theorem Hom.isIso_pullbackExchange_traitChangeModelHom_comp_fromCartesian_of_eq
    [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] R))] [WeaklyEtale φ.total]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (P : NearbyCyclesModel Y X') (hP : P = φ.traitChangeModel Ω q q₁ g₁ hN hq)
    (ψ : P.Hom N (𝟙 Y ≫ 𝟙 Y) (𝟙 X' ≫ f'))
    (hψ : HEq ψ ((φ.traitChangeModelHom Ω q q₁ g₁ hN hq).comp φ.fromCartesian))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsIso ((ψ.pullbackExchange Λ).app C) := by
  subst hP
  obtain rfl := eq_of_heq hψ
  exact φ.isIso_pullbackExchange_traitChangeModelHom_comp_fromCartesian q q₁ g₁ hN hq Λ C

end General

section Single

variable {R : Type u} [CommRing R] [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)
  {Y Y' : Scheme.{u}} (N : NearbyCyclesModel Y Y')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R))) {q : N.total ⟶ Spec (.of R)}
  (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R) = q)
  {g : N.generic ⟶ Spec (.of Ω)}
  (hNj : IsPullback N.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
  {p : Y' ⟶ Spec (.of κ)} (hNi : IsPullback N.i p q (Spec.map (CommRingCat.ofHom b)))

/-- The morphism of models `ψ : N₁ ⟶ N`: the nilpotent thickening `r₂` of generic fibres followed
by the weakly étale cartesian part of the slice. -/
noncomputable abbrev sliceTraitGaloisModelHom :
    (sliceTraitGaloisModel D N cN hcN hNj hNi).Hom N.toGeneric (𝟙 _ ≫ 𝟙 _)
      (𝟙 _ ≫ sliceTraitSpecial D N cN hcN hNi) :=
  ((sliceTraitGenericHom D N cN hcN hNj hNi).traitChangeModelHom D.Ω (sliceTraitStructure D N cN)
    q g hNj.w (sliceTrait_fst_comp D N cN hcN)).comp
    (sliceTraitGenericHom D N cN hcN hNj hNi).fromCartesian

/-- The pullback exchange of `ψ : N₁ ⟶ N` is invertible: the nilpotent thickening is a universal
homeomorphism, and the cartesian part is weakly étale base change. -/
theorem isIso_pullbackExchange_sliceTraitGaloisModelHom
    [Subsingleton (PrimeSpectrum (Ω ⊗[R] D.R))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic))) :
    IsIso (((sliceTraitGaloisModelHom D N cN hcN hNj hNi).pullbackExchange Λ).app C) := by
  have : WeaklyEtale (sliceTraitGenericHom D N cN hcN hNj hNi).total :=
    inferInstanceAs (WeaklyEtale (pullback.fst cN D.toAffineLine))
  exact Hom.isIso_pullbackExchange_traitChangeModelHom_comp_fromCartesian_of_eq (Ω := D.Ω)
    (sliceTraitGenericHom D N cN hcN hNj hNi) (sliceTraitStructure D N cN) q g hNj.w
    (sliceTrait_fst_comp D N cN hcN) Λ (sliceTraitGaloisModel D N cN hcN hNj hNi) rfl
    (sliceTraitGaloisModelHom D N cN hcN hNj hNi) HEq.rfl C

end Single

section Pair

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra R₁ Ω₁] [Algebra R₂ Ω₂]
  {c : Ω₁ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {D₁ : SliceTrait (algebraMap R₁ Ω₁) b₁} {D₂ : SliceTrait (algebraMap R₂ Ω₂) b₂}
  (H : SliceTrait.Hom ι c D₁ D₂) (hc : c.comp (algebraMap R₁ Ω₁) = (algebraMap R₂ Ω₂).comp ι)
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁))) {q₁ : N.total ⟶ Spec (.of R₁)}
  (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) = q₁)
  {g₁ : N.generic ⟶ Spec (.of Ω₁)}
  (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
  {p₁ : Y' ⟶ Spec (.of κ₁)} (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
  (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂))) {q₂ : M.total ⟶ Spec (.of R₂)}
  (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
  {g₂ : M.generic ⟶ Spec (.of Ω₂)}
  (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom (algebraMap R₂ Ω₂))))
  {p₂ : X' ⟶ Spec (.of κ₂)} (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
  (hcM : cM ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom ι)) = φ.total ≫ cN)
  (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))

/-- The change of trait of the slices commutes with the special fibres of the slices, if the
map of closed points `κ₁ ⟶ κ₂` of the base traits is compatible with that of the slice traits. -/
lemma sliceTraitChangeSpecial_comp_sliceTraitSpecial (κ₁₂ : κ₁ →+* κ₂)
    (hp : f' ≫ p₁ = p₂ ≫ Spec.map (CommRingCat.ofHom κ₁₂))
    (hκ : H.κMap.comp D₁.κS = D₂.κS.comp κ₁₂) :
    sliceTraitChangeSpecial H φ cN cM hcM ≫ sliceTraitSpecial D₁ N cN hcN hNi =
      sliceTraitSpecial D₂ M cM hcM' hMi ≫ f' := by
  apply hNi.hom_ext
  · simp only [Category.assoc, sliceTraitSpecial, IsPullback.lift_fst, φ.comm_i,
      IsPullback.lift_fst_assoc]
    simp [sliceTraitChangeSpecial]
  · simp only [Category.assoc, sliceTraitSpecial, IsPullback.lift_snd, hp,
      IsPullback.lift_snd_assoc]
    rw [sliceTraitChangeSpecial_snd_assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ]

include hgen in
/-- **The change of trait on the slice from the change of the Galois-layer models** (SGA 4½,
[Th. finitude], proof of 3.7): by the square `ψ_N ∘ τ = φ ∘ ψ_M` of morphisms of models, whose
vertical sides have invertible pullback exchanges, the pullback of the exchange of `φ` at `C`
to the special fibre of the slice of `M` is invertible once the exchange of `τ` is. -/
theorem isIso_map_pullbackExchange_of_sliceTraitGaloisChangeHom
    [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] D₁.R))] [Subsingleton (PrimeSpectrum (Ω₂ ⊗[R₂] D₂.R))]
    (κ₁₂ : κ₁ →+* κ₂) (hp : f' ≫ p₁ = p₂ ≫ Spec.map (CommRingCat.ofHom κ₁₂))
    (hκ : H.κMap.comp D₁.κS = D₂.κS.comp κ₁₂)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic)))
    (hτ : IsIso (((sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM
      hgen).pullbackExchange Λ).app (L((𝟙 N.generic ≫ 𝟙 N.generic)^*⟦Λ⟧).obj C))) :
    IsIso (L((𝟙 _ ≫ sliceTraitSpecial D₂ M cM hcM' hMi)^*⟦Λ⟧).map
      ((φ.toGeneric.pullbackExchange Λ).app C)) := by
  have h₁ := isIso_pullbackExchange_sliceTraitGaloisModelHom D₁ N cN hcN hNj hNi Λ C
  have h₂ := isIso_pullbackExchange_sliceTraitGaloisModelHom D₂ M cM hcM' hMj hMi Λ
    (L((φ.generic)^*⟦Λ⟧).obj C)
  have htot : (sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen).total ≫
      (sliceTraitGaloisModelHom D₁ N cN hcN hNj hNi).total =
      (sliceTraitGaloisModelHom D₂ M cM hcM' hMj hMi).total ≫ φ.toGeneric.total := by
    simp only [sliceTraitGaloisModelHom, Hom.comp_total, Hom.traitChangeModelHom_total,
      Hom.fromCartesian_total, sliceTraitGaloisChangeHom_total, Category.id_comp]
    exact sliceTraitChangeTotal_fst H φ cN cM hcM
  have hgen' : (sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen).generic ≫
      (sliceTraitGaloisModelHom D₁ N cN hcN hNj hNi).generic =
      (sliceTraitGaloisModelHom D₂ M cM hcM' hMj hMi).generic ≫ φ.toGeneric.generic := by
    simp only [sliceTraitGaloisModelHom, Hom.comp_generic, Hom.traitChangeModelHom_generic,
      Hom.fromCartesian_generic, sliceTraitGaloisChangeHom_generic, Category.assoc,
      Hom.traitChangeThickening, sliceTraitGaloisGenericMap_fst_assoc]
    exact pullback.fst _ _ ≫=
      sliceTraitCartesianGenericMap_fst H φ cN hcN hNj hNi cM hcM' hMj hMi hcM
  have hs : sliceTraitChangeSpecial H φ cN cM hcM ≫ (𝟙 _ ≫ sliceTraitSpecial D₁ N cN hcN hNi) =
      (𝟙 _ ≫ sliceTraitSpecial D₂ M cM hcM' hMi) ≫ f' := by
    rw [Category.id_comp, Category.id_comp,
      sliceTraitChangeSpecial_comp_sliceTraitSpecial H φ cN hcN hNi cM hcM' hMi hcM κ₁₂ hp hκ]
  with_reducible
    refine Hom.isIso_map_pullbackExchange_app_of_square_of_isIso Λ
      (sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen)
      (sliceTraitGaloisModelHom D₁ N cN hcN hNj hNi) (sliceTraitGaloisModelHom D₂ M cM hcM' hMj hMi)
      φ.toGeneric ?_ ?_ ?_ ?_ C ?_ ?_ ?_
  · with_reducible exact htot
  · with_reducible exact hgen'
  · simp
  · with_reducible exact hs
  · with_reducible exact h₁
  · with_reducible exact h₂
  · with_reducible exact hτ

end Pair

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
