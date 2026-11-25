/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsTorsion
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelUnit
public import WeilConjectures.TraceFormula.Specialization.TraitTensorCompositum

/-!

# The change of geometric generic fibre over a change of trait, as a Galois layer

Let `φ : M ⟶ N` be a morphism of models, with `M` over `Spec R` and geometric generic point
`Spec Ω` (the square `M.generic ⟶ M.total ⟶ Spec R`, `M.generic ⟶ Spec Ω ⟶ Spec R` is cartesian)
and `N` over `Spec R₁` with geometric generic point `Spec Ω₁`, compatibly with a ring map
`R₁ ⟶ R` and an embedding `Ω₁ ⟶ Ω`. Put `T = Spec(Ω₁ ⊗_{R₁} R)`.

* The generic fibre of the cartesian model of `φ` is `M.total ×_{Spec R} T`
  (`NearbyCyclesModel.Hom.isPullback_cartesianModelTensor`), and the change of geometric generic
  fibre `g = φ.toCartesian.generic` is the base change of `ρ : Spec Ω ⟶ T`
  (`NearbyCyclesModel.Hom.isPullback_toCartesian_generic_cartesianModelTensor`).
* When `T` is a single point, the factorisation `Spec Ω ⟶ Spec L^sep ⟶ Spec L ⟶ T` of `ρ`
  (`AlgebraicGeometry.traitTensorSepPoint_comp_traitTensorCompositumGalois_comp`) gives
  `g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂` universal homeomorphisms and `q` the projection of the
  Galois layer of the model `N₂` with generic fibre `Z₂ = (M.total ×_{Spec R} T) ×_T Spec L`
  along `Z₂ ⟶ Spec L` and the Galois extension `L^sep / L`
  (`NearbyCyclesModel.Hom.traitChangeInsepMap_comp_traitChangeGaloisMap_comp`,
  `NearbyCyclesModel.Hom.traitChangeModel`).
* Consequently, with torsion coefficients `T₀` in which the degrees of the finite Galois
  subextensions of `L^sep / L` are invertible, the pullback exchange of `φ.toCartesian` is a split
  monomorphism at every complex of étale origin
  (`NearbyCyclesModel.Hom.isSplitMono_toCartesian_pullbackExchange_app_of_traitChange`).

This generalises `NearbyCyclesModel.affineSpaceSliceHom_toCart_generic_factor` (SGA 4½,
[Th. finitude], 3.4).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped TensorProduct CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

open Scheme

variable {R₁ R Ω₁ Ω : Type u} [CommRing R₁] [CommRing R] [Algebra R₁ R] [Field Ω₁]
  [Algebra R₁ Ω₁] [Field Ω] [Algebra R Ω] [Algebra Ω₁ Ω] [Algebra R₁ Ω]
  [IsScalarTower R₁ R Ω] [IsScalarTower R₁ Ω₁ Ω]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (q : M.total ⟶ Spec (.of R)) (g : M.generic ⟶ Spec (.of Ω))
  (q₁ : N.total ⟶ Spec (.of R₁)) (g₁ : N.generic ⟶ Spec (.of Ω₁))

/-- The morphism `c : 𝒳_{N,η̄} ×_{𝒳_N} 𝒳_M ⟶ T = Spec(Ω₁ ⊗_{R₁} R)` from the generic fibre of
the cartesian model of `φ`, induced by `𝒳_{N,η̄} ⟶ Spec Ω₁` and `𝒳_M ⟶ Spec R`. -/
noncomputable def cartesianModelTensor
    (hN : N.j ≫ q₁ = g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R))) :
    φ.cartesianModel.generic ⟶ Spec (traitTensor R₁ R Ω₁) :=
  (isPullback_traitTensor R₁ R Ω₁).lift (pullback.fst N.j φ.total ≫ g₁)
    (pullback.snd N.j φ.total ≫ q) (by
      rw [Category.assoc, ← hN, pullback.condition_assoc, hq, Category.assoc])

variable {φ q g q₁ g₁}

/-- `c` lies over `𝒳_{N,η̄} ⟶ Spec Ω₁`. -/
@[reassoc (attr := simp)]
lemma cartesianModelTensor_fst
    (hN : N.j ≫ q₁ = g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R))) :
    φ.cartesianModelTensor q q₁ g₁ hN hq ≫ traitTensorFst R₁ R Ω₁ =
      pullback.fst N.j φ.total ≫ g₁ :=
  IsPullback.lift_fst _ _ _ _

/-- `c` lies over `𝒳_M ⟶ Spec R`. -/
@[reassoc (attr := simp)]
lemma cartesianModelTensor_snd
    (hN : N.j ≫ q₁ = g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R))) :
    φ.cartesianModelTensor q q₁ g₁ hN hq ≫ traitTensorSnd R₁ R Ω₁ =
      pullback.snd N.j φ.total ≫ q :=
  IsPullback.lift_snd _ _ _ _

/-- **The generic fibre of the cartesian model over `T`**: the square
```
𝒳_{N,η̄} ×_{𝒳_N} 𝒳_M ──c──> Spec(Ω₁ ⊗_{R₁} R)
        │                         │
        ↓                         ↓
       𝒳_M ──────────q──────> Spec R
```
is cartesian, i.e. `φ.cartesianModel.generic ≅ 𝒳_M ×_{Spec R} T`. -/
theorem isPullback_cartesianModelTensor
    (hN : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R))) :
    IsPullback (φ.cartesianModelTensor q q₁ g₁ hN.w hq) φ.cartesianModel.j
      (traitTensorSnd R₁ R Ω₁) q := by
  have h := (IsPullback.of_hasPullback N.j φ.total).flip.paste_vert hN
  rw [hq] at h
  refine IsPullback.of_right (h₁₂ := traitTensorFst R₁ R Ω₁)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
    (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap R₁ R))) ?_
    (cartesianModelTensor_snd hN.w hq) (isPullback_traitTensor R₁ R Ω₁)
  rw [cartesianModelTensor_fst]
  exact h.flip

/-- The change of geometric generic fibre `g = φ.toCartesian.generic` and the morphism
`ρ : Spec Ω ⟶ T` commute with `c`. -/
@[reassoc]
lemma toCartesian_generic_cartesianModelTensor
    (hM : M.j ≫ q = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
    (hN : N.j ≫ q₁ = g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R)))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω))) :
    φ.toCartesian.generic ≫ φ.cartesianModelTensor q q₁ g₁ hN hq =
      g ≫ traitTensorPoint R₁ R Ω₁ Ω := by
  apply (isPullback_traitTensor R₁ R Ω₁).hom_ext
  · simp [hg]
  · simp [hM]

/-- **The change of geometric generic fibre is a base change of `ρ : Spec Ω ⟶ T`**: the square
```
𝒳_{M,η̄} ──g──> 𝒳_{N,η̄} ×_{𝒳_N} 𝒳_M
   │                     │ c
   ↓                     ↓
Spec Ω ─────ρ────> Spec(Ω₁ ⊗_{R₁} R)
```
is cartesian. -/
theorem isPullback_toCartesian_generic_cartesianModelTensor
    (hM : IsPullback M.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
    (hN : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R)))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω))) :
    IsPullback φ.toCartesian.generic g (φ.cartesianModelTensor q q₁ g₁ hN.w hq)
      (traitTensorPoint R₁ R Ω₁ Ω) := by
  refine IsPullback.of_right (h₁₂ := φ.cartesianModel.j) (v₁₃ := q)
    (h₂₂ := traitTensorSnd R₁ R Ω₁) ?_
    (toCartesian_generic_cartesianModelTensor hM.w hN.w hq hg)
    (isPullback_cartesianModelTensor hN hq).flip
  rw [traitTensorPoint_snd]
  simpa using hM

section Factor

variable (Ω φ q g q₁ g₁)
variable (hN : N.j ≫ q₁ = g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
  (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R)))

/-- The base `Z₂ = (𝒳_M ×_{Spec R} T) ×_T Spec L` of the Galois part of the change of geometric
generic fibre, `L = Ω₁(R)` the compositum. -/
noncomputable abbrev traitChangeGaloisBase : Scheme.{u} :=
  pullback (φ.cartesianModelTensor q q₁ g₁ hN hq) (traitTensorCompositumPoint R₁ R Ω₁ Ω)

/-- The nilpotent thickening `r₂ : Z₂ ⟶ φ.cartesianModel.generic`, base change of
`Spec L ⟶ T`. -/
noncomputable def traitChangeThickening :
    φ.traitChangeGaloisBase Ω q q₁ g₁ hN hq ⟶ φ.cartesianModel.generic :=
  pullback.fst _ _

/-- The projection `h₂ : Z₂ ⟶ Spec L`. -/
noncomputable def traitChangeResidue :
    φ.traitChangeGaloisBase Ω q q₁ g₁ hN hq ⟶
      Spec (.of (traitTensorCompositum R Ω₁ Ω)) :=
  pullback.snd _ _

/-- The Galois cover `Z₁ = Z₂ ×_{Spec L} Spec L^sep` of `Z₂`. -/
noncomputable abbrev traitChangeGaloisCover : Scheme.{u} :=
  pullback (φ.traitChangeResidue Ω q q₁ g₁ hN hq) (traitTensorCompositumGalois R Ω₁ Ω)

/-- The Galois part `q : Z₁ ⟶ Z₂`, base change of `Spec L^sep ⟶ Spec L`. -/
noncomputable def traitChangeGaloisMap :
    φ.traitChangeGaloisCover Ω q q₁ g₁ hN hq ⟶ φ.traitChangeGaloisBase Ω q q₁ g₁ hN hq :=
  pullback.fst _ _

/-- The purely inseparable part `r₁ : 𝒳_{M,η̄} ⟶ Z₁`, base change of `Spec Ω ⟶ Spec L^sep`. -/
noncomputable def traitChangeInsepMap
    (hM : M.j ≫ q = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω))) :
    M.generic ⟶ φ.traitChangeGaloisCover Ω q q₁ g₁ hN hq :=
  pullback.lift (pullback.lift φ.toCartesian.generic
    (g ≫ traitTensorSepPoint R Ω₁ Ω ≫ traitTensorCompositumGalois R Ω₁ Ω) (by
      rw [toCartesian_generic_cartesianModelTensor hM hN hq hg,
        ← traitTensorSepPoint_comp_traitTensorCompositumGalois_comp, Category.assoc,
        Category.assoc]))
    (g ≫ traitTensorSepPoint R Ω₁ Ω) (by
      rw [traitChangeResidue, pullback.lift_snd, Category.assoc])

variable {Ω φ q g q₁ g₁}

/-- **The factorisation of the change of geometric generic fibre**: `g = r₁ ≫ q ≫ r₂`. -/
@[reassoc]
theorem traitChangeInsepMap_comp_traitChangeGaloisMap_comp
    (hM : M.j ≫ q = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω))) :
    φ.traitChangeInsepMap Ω q g q₁ g₁ hN hq hM hg ≫ φ.traitChangeGaloisMap Ω q q₁ g₁ hN hq ≫
      φ.traitChangeThickening Ω q q₁ g₁ hN hq = φ.toCartesian.generic := by
  simp [traitChangeInsepMap, traitChangeGaloisMap, traitChangeThickening]

/-- The Galois part `q` is the base change of `Spec L^sep ⟶ Spec L` along `Z₂ ⟶ Spec L`. -/
theorem isPullback_traitChangeGaloisMap :
    IsPullback (φ.traitChangeGaloisMap Ω q q₁ g₁ hN hq) (pullback.snd _ _)
      (φ.traitChangeResidue Ω q q₁ g₁ hN hq) (traitTensorCompositumGalois R Ω₁ Ω) :=
  IsPullback.of_hasPullback _ _

/-- The thickening `r₂` is a universal homeomorphism when `T` is a single point. -/
instance [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] R))] :
    IsUniversalHomeomorphism (φ.traitChangeThickening Ω q q₁ g₁ hN hq) := by
  rw [traitChangeThickening]
  infer_instance

/-- The square exhibiting `r₁` as the base change of `Spec Ω ⟶ Spec L^sep`. -/
theorem isPullback_traitChangeInsepMap
    (hM : IsPullback M.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
    (hN : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω))) :
    IsPullback (φ.traitChangeInsepMap Ω q g q₁ g₁ hN.w hq hM.w hg) g (pullback.snd _ _)
      (traitTensorSepPoint R Ω₁ Ω) := by
  have t := (IsPullback.of_hasPullback (φ.traitChangeResidue Ω q q₁ g₁ hN.w hq)
    (traitTensorCompositumGalois R Ω₁ Ω)).paste_horiz
      (IsPullback.of_hasPullback (φ.cartesianModelTensor q q₁ g₁ hN.w hq)
        (traitTensorCompositumPoint R₁ R Ω₁ Ω))
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) t
  have h := isPullback_toCartesian_generic_cartesianModelTensor hM hN hq hg
  rw [← traitChangeInsepMap_comp_traitChangeGaloisMap_comp hN.w hq hM.w hg,
    ← traitTensorSepPoint_comp_traitTensorCompositumGalois_comp] at h
  simpa only [Category.assoc, traitChangeGaloisMap, traitChangeThickening] using h

/-- The purely inseparable part `r₁` is a universal homeomorphism. -/
theorem isUniversalHomeomorphism_traitChangeInsepMap [FaithfulSMul R Ω]
    [Algebra.IsAlgebraic R Ω]
    (hM : IsPullback M.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
    (hN : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω))) :
    IsUniversalHomeomorphism (φ.traitChangeInsepMap Ω q g q₁ g₁ hN.w hq hM.w hg) :=
  MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism)
    (isPullback_traitChangeInsepMap hq hM hN hg).flip inferInstance

variable (Ω φ q g q₁ g₁)

/-- The model `N₂` with the total space and special fibre of `M` and generic fibre
`Z₂ = (𝒳_M ×_{Spec R} T) ×_T Spec L`, mapped to `𝒳_M` and `Y` through the thickening
`r₂ : Z₂ ⟶ φ.cartesianModel.generic`. Its Galois layer along `Z₂ ⟶ Spec L` and `L^sep / L` has
generic fibre `Z₁` and projection the Galois part `q : Z₁ ⟶ Z₂`
(`NearbyCyclesModel.Hom.traitChangeModel_galoisLayerHom_generic`). -/
@[simps]
noncomputable def traitChangeModel : NearbyCyclesModel Y X' where
  total := M.total
  generic := φ.traitChangeGaloisBase Ω q q₁ g₁ hN hq
  j := φ.traitChangeThickening Ω q q₁ g₁ hN hq ≫ φ.cartesianModel.j
  i := M.i
  ε := φ.traitChangeThickening Ω q q₁ g₁ hN hq ≫ φ.cartesianModel.ε

/-- The projection of the Galois layer of `N₂` along `Z₂ ⟶ Spec L` and `L^sep / L` is the Galois
part `q` of the change of geometric generic fibre. -/
lemma traitChangeModel_galoisLayerHom_generic :
    ((φ.traitChangeModel Ω q q₁ g₁ hN hq).galoisLayerHom
      (φ.traitChangeResidue Ω q q₁ g₁ hN hq) (traitTensorCompositumSep R Ω₁ Ω)).generic =
      φ.traitChangeGaloisMap Ω q q₁ g₁ hN hq :=
  rfl

/-- The morphism of models `M ⟶ N₂^{L^sep}` to the Galois layer of `N₂`, over `f` and the
identity: the identity of total spaces and the purely inseparable part `r₁` on generic fibres. -/
@[simps]
noncomputable def toTraitChangeGaloisLayer
    (hM : M.j ≫ q = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω))) :
    M.Hom ((φ.traitChangeModel Ω q q₁ g₁ hN hq).galoisLayer
      (φ.traitChangeResidue Ω q q₁ g₁ hN hq) (traitTensorCompositumSep R Ω₁ Ω)) f (𝟙 X') where
  total := 𝟙 _
  generic := φ.traitChangeInsepMap Ω q g q₁ g₁ hN hq hM hg
  comm_j := by
    have h := congrArg (· ≫ φ.cartesianModel.j)
      (traitChangeInsepMap_comp_traitChangeGaloisMap_comp hN hq hM hg)
    simp only [Category.assoc] at h
    exact h.trans φ.toCartesian.comm_j
  comm_i := by simp [galoisLayer]
  comm_ε := by
    have h := congrArg (· ≫ φ.cartesianModel.ε)
      (traitChangeInsepMap_comp_traitChangeGaloisMap_comp hN hq hM hg)
    simp only [Category.assoc] at h
    exact h.trans φ.toCartesian.comm_ε

/-- The morphism of models `N₂ ⟶ φ.cartesianModel` over the identities: the identity of total
spaces and the thickening `r₂` on generic fibres. -/
@[simps]
noncomputable def traitChangeModelHom :
    (φ.traitChangeModel Ω q q₁ g₁ hN hq).Hom φ.cartesianModel (𝟙 Y) (𝟙 X') where
  total := 𝟙 _
  generic := φ.traitChangeThickening Ω q q₁ g₁ hN hq
  comm_j := by simp
  comm_i := by simp
  comm_ε := by simp

end Factor

/-- **The change of geometric generic fibre over a change of trait splits** (torsion
coefficients). Let `φ : M ⟶ N` be a morphism of models over the traits `Spec R ⟶ Spec R₁`, with
geometric generic points `Spec Ω ⟶ Spec Ω₁`, such that `Spec(Ω₁ ⊗_{R₁} R)` is a single point. Let
`T₀` be a finite discrete ring in which the degrees of the finite Galois subextensions of
`L^sep / L` are invertible (`L = Ω₁(R)`). Then for every complex `C` on `Y` which is bounded below
of étale origin, the pullback exchange of `φ.toCartesian` is a split monomorphism at `C`.

The change of geometric generic fibre factors as `g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂` universal
homeomorphisms and `q` the base change of `Spec L^sep ⟶ Spec L`, whose unit is split by the
`Gal(L^sep / L)`-invariant retraction (`ProEtale.exists_invariant_retraction_derivedUnit_galois`).
-/
theorem isSplitMono_toCartesian_pullbackExchange_app_of_traitChange [IsAlgClosed Ω]
    [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] R))]
    (hM : IsPullback M.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
    (hN : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R)))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω)))
    (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
    [Finite T₀]
    (hp : ∀ L' : FiniteGaloisIntermediateField (traitTensorCompositum R Ω₁ Ω)
      (traitTensorCompositumSep R Ω₁ Ω), IsUnit ((Module.finrank (traitTensorCompositum R Ω₁ Ω)
        L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Y)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) Y
      ((finiteCoefficientDerivedEquivalence Y T₀).functor.obj C)) :
    IsSplitMono ((φ.toCartesian.pullbackExchange (Profinite.continuousMapRingObj T₀)).app C) := by
  have := isUniversalHomeomorphism_traitChangeInsepMap hq hM hN hg
  obtain ⟨r, hr, -⟩ := ProEtale.exists_invariant_retraction_derivedUnit_galois
    (φ.traitChangeResidue Ω q q₁ g₁ hN.w hq) T₀ hp _
    (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀
      (φ.traitChangeThickening Ω q q₁ g₁ hN.w hq)
      (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀
        φ.cartesianModel.ε hC))
  -- the instantiated general statement differs from the goal by instance proofs inside the
  -- derived categories, whose comparison by the unifier times out
  exact_mod_proofs φ.isSplitMono_toCart_pullbackExchange_app_of_factor₃
    (Profinite.continuousMapRingObj T₀) C
    (φ.traitChangeInsepMap Ω q g q₁ g₁ hN.w hq hM.w hg) (φ.traitChangeGaloisMap Ω q q₁ g₁ hN.w hq)
    (φ.traitChangeThickening Ω q q₁ g₁ hN.w hq)
    (traitChangeInsepMap_comp_traitChangeGaloisMap_comp hN.w hq hM.w hg)
    (IsSplitMono.mk' ⟨r, hr⟩)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom
