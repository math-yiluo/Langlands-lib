/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisSquare
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMapInvariants

/-!

# The slice step of Deligne's induction over a morphism of slice traits

Let `H : S₂(x) ⟶ S₁(x)` be a morphism of slice traits over a change of trait `ι : R₁ ⟶ R₂`,
inducing an isomorphism of closed points, and `φ : M ⟶ N` a morphism of models over `Spec ι` with
compatible coordinates `cN`, `cM`. If Prop. 3.7 holds in chart dimension `m` and the slice of `N`
over `S₁(x)` locally embeds into `𝔸ᵐ`, then the pullback of the exchange of `φ.toGeneric` to the
special fibre of the slice of `M` is invertible at every complex bounded below of étale origin
(`NearbyCyclesModel.isIso_map_pullbackExchange_sliceTraitSpecial`), provided the composita
`Lᵢ = Ωᵢ(Sᵢ(x))` have Galois extensions `Lᵢ^sep / Lᵢ` of degrees invertible in the coefficients and
`L₁` is relatively separably closed in `L₂`.

This is the step (A) of SGA 4½, [Th. finitude], proof of 3.7: the four squares
```
M'  ──φ'──→  N'          N₂ ──τ──→ N₁
 │ρ_M         │ρ_N         │ψ_M      │ψ_N
N₂_{L₂^sep} ─τ'→ N₁_{L₁^sep}   M ──φ──→  N
```
reduce the change of trait on the slice to the change of trait `φ'` of the slices (the induction
hypothesis, `NearbyCyclesModel.isIso_pullbackExchange_sliceTraitChangeHom`), through the change of
Galois layers `τ'` (`NearbyCyclesModel.isIso_pullbackExchange_sliceTraitGaloisLayerMap`), the
invariants under the wild inertia groups
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic`)
and the
Galois-layer models (`NearbyCyclesModel.isIso_map_pullbackExchange_of_sliceTraitGaloisChangeHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme SliceTrait

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
  [IsStrictlyHenselianLocalRing R₂]
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

/-- Transport of the invertibility of a pullback exchange along equalities of models and of
morphisms of models (to pass between abbreviated and unfolded forms without comparing large
pullback exchanges). -/
theorem Hom.isIso_pullbackExchange_app_of_heq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Z Z' W W' : Scheme.{u}} {P P' : NearbyCyclesModel Z Z'} {Q Q' : NearbyCyclesModel W W'}
    {e : Z ⟶ W} {e' : Z' ⟶ W'} (hP : P = P') (hQ : Q = Q') (ψ : P.Hom Q e e')
    (ψ' : P'.Hom Q' e e') (h : HEq ψ ψ')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)))
    (hψ : IsIso ((ψ.pullbackExchange Λ).app C)) : IsIso ((ψ'.pullbackExchange Λ).app C) := by
  subst hP hQ
  obtain rfl := eq_of_heq h
  exact hψ

include hNj in
/-- The open immersion of generic fibres of the Galois-layer model `N₁` of a slice is affine: it is
the nilpotent thickening `r₂` followed by the base change of `𝒳_{N,η̄} ⟶ 𝒳_N`. -/
lemma isAffineHom_sliceTraitGaloisModel_j :
    IsAffineHom (sliceTraitGaloisModel D₁ N cN hcN hNj hNi).j := by
  have : IsAffineHom N.j := MorphismProperty.of_isPullback hNj.flip inferInstance
  have h₂ : IsAffineHom (sliceTraitGenericHom D₁ N cN hcN hNj hNi).cartesianModel.j :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have h₁ : IsAffineHom ((sliceTraitGenericHom D₁ N cN hcN hNj hNi).traitChangeThickening D₁.Ω
      (sliceTraitStructure D₁ N cN) q₁ g₁ hNj.w (sliceTrait_fst_comp D₁ N cN hcN)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact MorphismProperty.comp_mem _ _ _ h₁ h₂

include hc hcN hNj hNi hMj hcM hgen in
/-- **The slice step over a morphism of slice traits** (SGA 4½, [Th. finitude], proof of 3.7,
step (A)). Assume Prop. 3.7 in chart dimension `m`, and that the slice of `N` over `S₁(x)` locally
embeds into `𝔸ᵐ`. If `H` induces an isomorphism of closed points, the composita `Lᵢ` have Galois
extensions `Lᵢ^sep / Lᵢ` whose finite layers have degrees invertible in `T`, and `L₁` is relatively
separably closed in `L₂`, then the pullback of the exchange of `φ.toGeneric` to the special fibre of
the slice of `M` is invertible at every complex `K` bounded below of étale origin. -/
theorem isIso_map_pullbackExchange_sliceTraitSpecial {m : ℕ} (ih : TraitChangeInvariance.{u} T m)
    [IsIso (Spec.map (CommRingCat.ofHom H.κMap))]
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T))
    [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] D₁.R))] [Subsingleton (PrimeSpectrum (Ω₂ ⊗[R₂] D₂.R))]
    [IsGalois D₁.compositum D₁.compositumSep] [IsGalois D₂.compositum D₂.compositumSep]
    (hp₁ : ∀ L' : FiniteGaloisIntermediateField D₁.compositum D₁.compositumSep,
      IsUnit ((Module.finrank D₁.compositum L' : ℕ) : T))
    (hp₂ : ∀ L' : FiniteGaloisIntermediateField D₂.compositum D₂.compositumSep,
      IsUnit ((Module.finrank D₂.compositum L' : ℕ) : T))
    (hclosed : ∀ x : D₁.compositumSep,
      H.compositumSepMap x ∈ Set.range (algebraMap D₂.compositum D₂.compositumSep) →
        x ∈ Set.range (algebraMap D₁.compositum D₁.compositumSep))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    [LocallyOfFiniteType cN] [QuasiCompact cN] [IsSeparated cN]
    (hm : (pullback.snd cN D₁.toAffineLine).LocallyEmbedsInAffineSpace m)
    (κ₁₂ : κ₁ →+* κ₂) (hs : f' ≫ p₁ = p₂ ≫ Spec.map (CommRingCat.ofHom κ₁₂))
    (hκ : H.κMap.comp D₁.κS = D₂.κS.comp κ₁₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K)) :
    IsIso (L((𝟙 _ ≫ sliceTraitSpecial D₂ M cM hcM' hMi)^*⟦Profinite.continuousMapRingObj T⟧).map
      ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K)) := by
  have hK₀ := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T (𝟙 N.generic ≫ 𝟙 N.generic) hK
  have hIH := isIso_pullbackExchange_sliceTraitChangeHom T ih H hun p hp hpT φ hφ cN hcN hm cM hcM
    hcM' _ (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
      T (sliceTraitGeneric D₁ N cN hcN hNj)
      (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
        T (𝟙 N.generic) hK₀))
  have hB := isIso_pullbackExchange_sliceTraitGaloisLayerMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi
    hcM hgen _ _ hIH
  have hτ : IsIso (((sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM
      hgen).pullbackExchange (Profinite.continuousMapRingObj T)).app
        (L((𝟙 N.generic ≫ 𝟙 N.generic)^*⟦Profinite.continuousMapRingObj T⟧).obj K)) := by
    have := isAffineHom_sliceTraitGaloisModel_j (D₁ := D₁) cN hcN hNj hNi
    have := isAffineHom_sliceTraitGaloisModel_j (D₁ := D₂) cM hcM' hMj hMi
    have hC₁ := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
      T (sliceTraitGaloisModel D₁ N cN hcN hNj hNi).ε hK₀
    have hC₂ := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
      T (sliceTraitGaloisModel D₂ M cM hcM' hMj hMi).ε
      (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
        φ.generic hK₀)
    have hB' := Hom.isIso_pullbackExchange_app_of_heq _ (by rfl) (by rfl)
      (sliceTraitGaloisLayerMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen)
      (galoisLayerMap D₁.compositumSep D₂.compositumSep H.compositumSepMap
        H.compositumSepMap_comp_algebraMap
        (sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen)
        (sliceTraitGaloisChangeHom_generic_comp_residue H hc φ cN hcN hNj hNi cM hcM' hMj
          hMi hcM hgen)) HEq.rfl _ hB
    with_reducible
      have key := Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic
        (l := H.compositumMap) (ω := H.compositumSepMap) (hω := H.compositumSepMap_comp_algebraMap)
        T
        (sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen)
        (sliceTraitGaloisChangeHom_generic_comp_residue H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM
          hgen) hp₁ hp₂ hclosed
        (L((𝟙 N.generic ≫ 𝟙 N.generic)^*⟦Profinite.continuousMapRingObj T⟧).obj K)
        (by exact_mod_proofs hC₁) (by exact_mod_proofs hC₂) (hiso := by exact_mod_proofs hB')
    -- the abbreviated and unfolded forms of the models and the `MonObj` instances of the
    -- coefficients differ; `exact_mod_proofs` bridges the instance proofs
    exact_mod_proofs key
  -- the instances `MonObj` of the coefficients differ by deep instance proofs
  with_reducible
    have key := isIso_map_pullbackExchange_of_sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM
        hcM' hMj hMi hcM hgen κ₁₂ hs hκ (Profinite.continuousMapRingObj T) K
  have key' := key (by exact_mod_proofs hτ)
  exact_mod_proofs key'

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
