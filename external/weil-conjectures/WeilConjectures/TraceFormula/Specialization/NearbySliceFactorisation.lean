/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.TraceFormula.Specialization.NearbyCartesianModel
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisCompositum

/-!

# The change of geometric generic fibre over a coordinate slice

Let `S = Spec A`, `A = k'⟦t⟧`, `B = K⟦t⟧`, `F = Frac A`, `F_K = Frac B`, `Ω = F^alg` and
`Ω_K = F_K^alg`. For the morphism of models `φ = hᵢ` over a coordinate generic slice
(`NearbyCyclesModel.affineSpaceSliceHom`) the change of geometric generic fibre is
```
g = φ.toCartesian.generic : 𝔸ⁿ_B ×_B Spec Ω_K ⟶ 𝔸ⁿ_B ×_S Spec Ω.
```
We identify it with a base change of a morphism of spectra of rings:

* `F_K` is the localization of `B` at the image of the nonzero elements of `A`
  (`AlgebraicGeometry.isLocalization_map_nonZeroDivisors_powerSeries`), so the square
  `Spec F_K ⟶ Spec F`, `Spec B ⟶ S` is cartesian and `T = Spec(Ω ⊗_F F_K)` is the fibre
  product `Spec B ×_S Spec Ω` (`AlgebraicGeometry.isPullback_traitGenericTensor`);
* the target of `g` is `𝔸ⁿ_B ×_B T`
  (`NearbyCyclesModel.isPullback_affineSpaceSliceHom_cartModel_generic`) and `g` is the base
  change of `ρ : Spec Ω_K ⟶ T`, the spectrum of the product map `Ω ⊗_F F_K ⟶ Ω_K`
  (`NearbyCyclesModel.isPullback_affineSpaceSliceHom_toCart_generic`).

The morphism `ρ` factors as `Spec Ω_K ⟶ Spec L^sep ⟶ Spec L ⟶ T`, with `L = F_K·Ω` the residue
field of the unique point of `T` (`AlgebraicGeometry.traitGenericSpecMap_factor`); the first and
last factors are universal homeomorphisms (`Ω_K / L^sep` is purely inseparable and
`Ω ⊗_F F_K ⟶ L` is surjective with nilpotent kernel), the middle one is the spectrum of the
Galois extension `L^sep / L`. Base changing along `𝔸ⁿ_B ×_B T ⟶ T` gives
`g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂` universal homeomorphisms and `q` a base change of
`Spec L^sep ⟶ Spec L` (`NearbyCyclesModel.affineSpaceSliceHom_toCart_generic_factor`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

section Ring

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- `F_K = Frac K⟦t⟧` is the localization of `K⟦t⟧` at the image of the nonzero elements of
`k'⟦t⟧`: every nonzero power series over `K` is a power of `t` times a unit. -/
theorem isLocalization_map_nonZeroDivisors_powerSeries :
    IsLocalization ((nonZeroDivisors (PowerSeries k')).map (PowerSeries.map (algebraMap k' K)))
      (FractionRing (PowerSeries K)) where
  map_units := by
    rintro ⟨_, y, hy, rfl⟩
    refine IsUnit.mk0 _ ?_
    rw [Ne, ← map_zero (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      (IsFractionRing.injective _ _).eq_iff, ← map_zero (PowerSeries.map (algebraMap k' K)),
      (PowerSeries.map_injective _ (algebraMap k' K).injective).eq_iff]
    exact nonZeroDivisors.ne_zero hy
  surj := by
    intro z
    obtain ⟨⟨b, b', hb'⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (PowerSeries K)) z
    obtain ⟨v, hv, hb⟩ := PowerSeries.exists_eq_X_pow_mul_isUnit (nonZeroDivisors.ne_zero hb')
    set m := b'.order.toNat
    refine ⟨⟨b * ↑hv.unit⁻¹, ⟨_, ⟨PowerSeries.X ^ m, ?_, rfl⟩⟩⟩, ?_⟩
    · exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
    · have h' : z * algebraMap _ (FractionRing (PowerSeries K)) (PowerSeries.X ^ m * v) =
          algebraMap _ _ b := by
        rw [← hb]
        exact h
      have hvu : algebraMap _ (FractionRing (PowerSeries K)) v *
          algebraMap _ _ (↑hv.unit⁻¹ : PowerSeries K) = 1 := by
        rw [← map_mul, IsUnit.mul_val_inv, map_one]
      change z * algebraMap _ _ (PowerSeries.map (algebraMap k' K) (PowerSeries.X ^ m)) =
        algebraMap _ _ (b * ↑hv.unit⁻¹)
      rw [map_pow, PowerSeries.map_X, map_mul, ← h', map_mul, mul_assoc, mul_assoc, hvu,
        mul_one]
  exists_of_eq := by
    intro x y h
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    exact IsFractionRing.injective _ _ h

/-- The square of rings `k'⟦t⟧ ⟶ K⟦t⟧ ⟶ F_K`, `k'⟦t⟧ ⟶ F ⟶ F_K` is a pushout:
`K⟦t⟧ ⊗_{k'⟦t⟧} F = F_K`. -/
theorem isPushout_traitLaurentFieldMap :
    IsPushout (CommRingCat.ofHom (PowerSeries.map (algebraMap k' K)))
      (CommRingCat.ofHom (algebraMap (PowerSeries k') (FractionRing (PowerSeries k'))))
      (CommRingCat.ofHom (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))
      (CommRingCat.ofHom (traitLaurentFieldMap k' K)) := by
  have := isLocalization_map_nonZeroDivisors_powerSeries k' K
  refine CommRingCat.isPushout_of_isLocalization _ _ ?_ (nonZeroDivisors (PowerSeries k'))
  ext a
  exact traitLaurentFieldMap_algebraMap k' K a

/-- The ring `Ω ⊗_F F_K`, with `F_K` an `F`-algebra through
`AlgebraicGeometry.traitLaurentFieldMap`. -/
noncomputable def traitGenericTensor : CommRingCat.{u} :=
  letI := (traitLaurentFieldMap k' K).toAlgebra
  .of (traitGenericField k' ⊗[FractionRing (PowerSeries k')] FractionRing (PowerSeries K))

/-- The map `Spec(Ω ⊗_F F_K) ⟶ Spec Ω` of the first factor. -/
noncomputable def traitGenericTensorFst :
    Spec (traitGenericTensor k' K) ⟶ Spec (.of (traitGenericField k')) :=
  letI := (traitLaurentFieldMap k' K).toAlgebra
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- The map `Spec(Ω ⊗_F F_K) ⟶ Spec F_K ⟶ Spec K⟦t⟧` of the second factor. -/
noncomputable def traitGenericTensorSnd : Spec (traitGenericTensor k' K) ⟶ trait K :=
  letI := (traitLaurentFieldMap k' K).toAlgebra
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom.comp
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))

/-- **`Spec(Ω ⊗_F F_K)` is the fibre product `Spec K⟦t⟧ ×_S Spec Ω`** of the trait map and the
geometric generic point of `S = Spec k'⟦t⟧`. -/
theorem isPullback_traitGenericTensor :
    IsPullback (traitGenericTensorFst k' K) (traitGenericTensorSnd k' K)
      (traitGenericPoint k') (traitMap k' K) := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  have h₁ := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (FractionRing (PowerSeries k')) (traitGenericField k')
      (FractionRing (PowerSeries K)))
  have h₂ := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_traitLaurentFieldMap k' K)).flip
  have e₁ : traitGenericTensorSnd k' K =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e₂ : traitGenericPoint k' =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing (PowerSeries k'))
        (traitGenericField k'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k')
          (FractionRing (PowerSeries k')))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rfl
  rw [e₁, e₂]
  exact h₁.paste_vert h₂

end Ring
section Factor

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

variable (k' K) in
/-- The morphism `ρ : Spec Ω_K ⟶ Spec(Ω ⊗_F F_K)` of the product map `Ω ⊗_F F_K ⟶ Ω_K`
(`AlgebraicGeometry.traitGenericTensorLift`). -/
noncomputable def traitGenericTensorPoint :
    Spec (.of (traitGenericField K)) ⟶ Spec (traitGenericTensor k' K) :=
  Spec.map (CommRingCat.ofHom (traitGenericTensorLift k' K))

/-- `ρ` lies over the map `Spec Ω_K ⟶ Spec Ω` of geometric generic points. -/
@[reassoc (attr := simp)]
lemma traitGenericTensorPoint_fst :
    traitGenericTensorPoint k' K ≫ traitGenericTensorFst k' K = traitGenericPointMap k' K := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  rw [traitGenericTensorPoint, traitGenericTensorFst, traitGenericPointMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext ω
  change traitGenericTensorLift k' K (ω ⊗ₜ 1) = _
  rw [traitGenericTensorLift_tmul, map_one, mul_one]

/-- `ρ` lies over the geometric generic point of `Spec K⟦t⟧`. -/
@[reassoc (attr := simp)]
lemma traitGenericTensorPoint_snd :
    traitGenericTensorPoint k' K ≫ traitGenericTensorSnd k' K = traitGenericPoint K := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  rw [traitGenericTensorPoint, traitGenericTensorSnd, traitGenericPoint, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext b
  change traitGenericTensorLift k' K (1 ⊗ₜ algebraMap _ _ b) = _
  rw [traitGenericTensorLift_tmul, map_one, one_mul, ← IsScalarTower.algebraMap_apply]

variable (k' K) in
/-- The surjection `Ω ⊗_F F_K ⟶ L = F_K·Ω` onto the compositum, the corestriction of the product
map. -/
noncomputable def traitGenericTensorToCompositum :
    traitGenericTensor k' K ⟶ .of (traitGenericCompositum k' K) :=
  CommRingCat.ofHom ((traitGenericTensorLift k' K).codRestrict (traitGenericCompositum k' K)
    fun x ↦ (range_traitGenericTensorLift k' K).le ⟨x, rfl⟩)

lemma surjective_traitGenericTensorToCompositum :
    Function.Surjective (traitGenericTensorToCompositum k' K) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := (range_traitGenericTensorLift k' K).ge hy
  exact ⟨x, Subtype.ext hx⟩

variable (k' K) in
/-- The separable closure `L^sep` of the compositum `L = F_K·Ω` in `Ω_K`. -/
noncomputable abbrev traitGenericCompositumSep : IntermediateField (traitGenericCompositum k' K)
    (traitGenericField K) :=
  separableClosure (traitGenericCompositum k' K) (traitGenericField K)

variable (k' K) in
/-- The universal homeomorphism `Spec Ω_K ⟶ Spec L^sep` (`Ω_K / L^sep` is purely inseparable). -/
noncomputable def traitGenericSepPoint :
    Spec (.of (traitGenericField K)) ⟶ Spec (.of (traitGenericCompositumSep k' K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

variable (k' K) in
/-- The pro-Galois morphism `Spec L^sep ⟶ Spec L`. -/
noncomputable def traitGenericCompositumGalois :
    Spec (.of (traitGenericCompositumSep k' K)) ⟶ Spec (.of (traitGenericCompositum k' K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

variable (k' K) in
/-- The closed immersion `Spec L ⟶ Spec(Ω ⊗_F F_K)` of the reduced point. -/
noncomputable def traitGenericCompositumPoint :
    Spec (.of (traitGenericCompositum k' K)) ⟶ Spec (traitGenericTensor k' K) :=
  Spec.map (traitGenericTensorToCompositum k' K)

/-- **The factorisation of `ρ`**: `Spec Ω_K ⟶ Spec L^sep ⟶ Spec L ⟶ Spec(Ω ⊗_F F_K)`. -/
@[reassoc]
theorem traitGenericSpecMap_factor :
    traitGenericSepPoint k' K ≫ traitGenericCompositumGalois k' K ≫
      traitGenericCompositumPoint k' K = traitGenericTensorPoint k' K := by
  rw [traitGenericSepPoint, traitGenericCompositumGalois, traitGenericCompositumPoint,
    traitGenericTensorPoint, ← Spec.map_comp, ← Spec.map_comp, traitGenericTensorToCompositum,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

instance : IsUniversalHomeomorphism (traitGenericSepPoint k' K) := by
  have := (traitGenericCompositum_tower (k' := k') (K := K)).2.2
  rw [traitGenericSepPoint]
  infer_instance

/-- `L^sep / L` is Galois. -/
instance : IsGalois (traitGenericCompositum k' K) (traitGenericCompositumSep k' K) :=
  (traitGenericCompositum_tower (k' := k') (K := K)).2.1

instance : IsClosedImmersion (traitGenericCompositumPoint k' K) :=
  IsClosedImmersion.spec_of_surjective _ surjective_traitGenericTensorToCompositum

/-- **`Spec L ⟶ Spec(Ω ⊗_F F_K)` is a universal homeomorphism**: a closed immersion onto the
one-point space `Spec(Ω ⊗_F F_K)`. -/
theorem isUniversalHomeomorphism_traitGenericCompositumPoint [IsSepClosed k'] [IsAlgClosed K]
    (htr : Algebra.trdeg k' K ≤ 1) :
    IsUniversalHomeomorphism (traitGenericCompositumPoint k' K) := by
  have : Subsingleton (Spec (traitGenericTensor k' K)) :=
    subsingleton_primeSpectrum_traitGenericField_tensorProduct (K := K) htr
  have : Surjective (traitGenericCompositumPoint k' K) :=
    ⟨fun x ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  infer_instance

end Factor

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] (n : ℕ) (i : Fin (n + 1))

/-- The geometric generic fibre of the cartesian model of the slice `hᵢ` is the fibre product
`𝔸ⁿ_B ×_S Spec Ω` of `𝔸ⁿ_B ⟶ Spec B ⟶ S` and the geometric generic point of `S`. -/
lemma isPullback_affineSpaceSliceHom_cartModel_generic_trait :
    IsPullback (pullback.fst (affineSpaceModel k' (n + 1)).geometric.j
        (affineSpaceSliceHom k' n i).total ≫
        pullback.snd (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k') (traitGenericPoint k'))
      (affineSpaceSliceHom k' n i).cartesianModel.j (traitGenericPoint k')
      (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k') ≫
        traitMap k' (traitSliceField k')) := by
  have h := (IsPullback.of_hasPullback (affineSpaceModel k' (n + 1)).geometric.j
    (affineSpaceSliceHom k' n i).total).paste_horiz
    (IsPullback.of_hasPullback (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')
      (traitGenericPoint k')).flip
  rw [← affineSpaceSlice_over n i (traitSliceCoord k')]
  exact h

variable (k') in
/-- The morphism `c : 𝔸ⁿ_B ×_S Spec Ω ⟶ T = Spec(Ω ⊗_F F_K)` from the geometric generic fibre
of the cartesian model of the slice (`B = K⟦t⟧`, `K = k'(x)^alg`), induced by the projections
to `Spec Ω` and to `𝔸ⁿ_B ⟶ Spec B`. -/
noncomputable def affineSpaceSliceCartTensor :
    (affineSpaceSliceHom k' n i).cartesianModel.generic ⟶
      Spec (traitGenericTensor k' (traitSliceField k')) :=
  (isPullback_traitGenericTensor k' (traitSliceField k')).lift
    (pullback.fst (affineSpaceModel k' (n + 1)).geometric.j
        (affineSpaceSliceHom k' n i).total ≫
        pullback.snd (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k') (traitGenericPoint k'))
    ((affineSpaceSliceHom k' n i).cartesianModel.j ≫
      𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k')) (by
    rw [Category.assoc]
    exact (isPullback_affineSpaceSliceHom_cartModel_generic_trait n i).w)

/-- **The generic fibre of the cartesian model of the slice over `T`**: the square
```
𝔸ⁿ_B ×_S Spec Ω ──c──> Spec(Ω ⊗_F F_K)
      │                      │
      ↓                      ↓
    𝔸ⁿ_B ───────────────> Spec B
```
is cartesian, i.e. `(affineSpaceSliceHom k' n i).cartesianModel.generic ≅ 𝔸ⁿ_B ×_B T`. -/
theorem isPullback_affineSpaceSliceHom_cartModel_generic :
    IsPullback (affineSpaceSliceCartTensor k' n i) (affineSpaceSliceHom k' n i).cartesianModel.j
      (traitGenericTensorSnd k' (traitSliceField k'))
      (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k')) := by
  refine IsPullback.of_right (h₁₂ := traitGenericTensorFst k' (traitSliceField k'))
    (v₁₃ := traitGenericPoint k') (h₂₂ := traitMap k' (traitSliceField k')) ?_
    (IsPullback.lift_snd _ _ _ _) (isPullback_traitGenericTensor k' (traitSliceField k'))
  rw [affineSpaceSliceCartTensor, IsPullback.lift_fst]
  exact isPullback_affineSpaceSliceHom_cartModel_generic_trait n i

/-- The change of geometric generic fibre `g` and the morphism `ρ : Spec Ω_K ⟶ T` commute with
`c`. -/
@[reassoc]
lemma affineSpaceSliceHom_toCart_generic_cartTensor :
    (affineSpaceSliceHom k' n i).toCartesian.generic ≫ affineSpaceSliceCartTensor k' n i =
      pullback.snd (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k')) (traitGenericPoint (traitSliceField k')) ≫
        traitGenericTensorPoint k' (traitSliceField k') := by
  apply (isPullback_traitGenericTensor k' (traitSliceField k')).hom_ext
  · simp [affineSpaceSliceCartTensor, affineSpaceSliceGeneric]
  · simp only [affineSpaceSliceCartTensor, Category.assoc, IsPullback.lift_snd,
      traitGenericTensorPoint_snd]
    simp

/-- **The change of geometric generic fibre over the slice is a base change of
`ρ : Spec Ω_K ⟶ Spec(Ω ⊗_F F_K)`**: the square
```
𝔸ⁿ_B ×_B Spec Ω_K ──g──> 𝔸ⁿ_B ×_S Spec Ω
        │                        │ c
        ↓                        ↓
     Spec Ω_K ──────ρ──────> Spec(Ω ⊗_F F_K)
```
is cartesian. -/
theorem isPullback_affineSpaceSliceHom_toCart_generic :
    IsPullback (affineSpaceSliceHom k' n i).toCartesian.generic
      (pullback.snd (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k')) (traitGenericPoint (traitSliceField k')))
      (affineSpaceSliceCartTensor k' n i) (traitGenericTensorPoint k' (traitSliceField k')) := by
  refine IsPullback.of_right (h₁₂ := (affineSpaceSliceHom k' n i).cartesianModel.j)
    (v₁₃ := 𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k'))
    (h₂₂ := traitGenericTensorSnd k' (traitSliceField k')) ?_
    (affineSpaceSliceHom_toCart_generic_cartTensor n i)
    (isPullback_affineSpaceSliceHom_cartModel_generic n i).flip
  rw [traitGenericTensorPoint_snd]
  simp only [Hom.toCartesian_generic, Hom.cartesianModel_j, pullback.lift_snd]
  exact IsPullback.of_hasPullback _ _

section Factor

variable (k') in
/-- The base `Z₂ = (𝔸ⁿ_B ×_S Spec Ω) ×_T Spec L` of the Galois part of the change of geometric
generic fibre over the slice, `L = F_K·Ω`. -/
noncomputable abbrev affineSpaceSliceGaloisBase : Scheme.{u} :=
  pullback (affineSpaceSliceCartTensor k' n i) (traitGenericCompositumPoint k' (traitSliceField k'))

variable (k') in
/-- The Galois cover `Z₁ = Z₂ ×_{Spec L} Spec L^sep` of `Z₂`. -/
noncomputable abbrev affineSpaceSliceGaloisCover : Scheme.{u} :=
  pullback (pullback.snd (affineSpaceSliceCartTensor k' n i)
    (traitGenericCompositumPoint k' (traitSliceField k')))
    (traitGenericCompositumGalois k' (traitSliceField k'))

variable (k') in
/-- The nilpotent thickening `r₂ : Z₂ ⟶ 𝔸ⁿ_B ×_S Spec Ω`, base change of `Spec L ⟶ T`. -/
noncomputable def affineSpaceSliceThickening :
    affineSpaceSliceGaloisBase k' n i ⟶ (affineSpaceSliceHom k' n i).cartesianModel.generic :=
  pullback.fst _ _

variable (k') in
/-- The Galois part `q : Z₁ ⟶ Z₂`, base change of `Spec L^sep ⟶ Spec L`. -/
noncomputable def affineSpaceSliceGaloisMap :
    affineSpaceSliceGaloisCover k' n i ⟶ affineSpaceSliceGaloisBase k' n i :=
  pullback.fst _ _

variable (k') in
/-- The purely inseparable part `r₁ : 𝔸ⁿ_B ×_B Spec Ω_K ⟶ Z₁`, base change of
`Spec Ω_K ⟶ Spec L^sep`. -/
noncomputable def affineSpaceSliceInsepMap :
    (affineSpaceModel (traitSliceField k') n).geometric.generic ⟶
      affineSpaceSliceGaloisCover k' n i :=
  pullback.lift (pullback.lift (affineSpaceSliceHom k' n i).toCartesian.generic
    (pullback.snd (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k')) (traitGenericPoint (traitSliceField k')) ≫
      traitGenericSepPoint k' (traitSliceField k') ≫
        traitGenericCompositumGalois k' (traitSliceField k')) (by
      rw [affineSpaceSliceHom_toCart_generic_cartTensor, ← traitGenericSpecMap_factor]
      simp only [Category.assoc]))
    (pullback.snd (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k')) (traitGenericPoint (traitSliceField k')) ≫
      traitGenericSepPoint k' (traitSliceField k')) (by
    rw [pullback.lift_snd, Category.assoc])

/-- **The factorisation of the change of geometric generic fibre over the slice**:
`g = r₁ ≫ q ≫ r₂`. -/
@[reassoc]
theorem affineSpaceSliceHom_toCart_generic_factor :
    affineSpaceSliceInsepMap k' n i ≫ affineSpaceSliceGaloisMap k' n i ≫
      affineSpaceSliceThickening k' n i = (affineSpaceSliceHom k' n i).toCartesian.generic := by
  simp [affineSpaceSliceInsepMap, affineSpaceSliceGaloisMap, affineSpaceSliceThickening]

/-- The Galois part `q` is the base change of `Spec L^sep ⟶ Spec L` along `Z₂ ⟶ Spec L`. -/
theorem isPullback_affineSpaceSliceGaloisMap :
    IsPullback (affineSpaceSliceGaloisMap k' n i) (pullback.snd _ _)
      (pullback.snd _ _) (traitGenericCompositumGalois k' (traitSliceField k')) :=
  IsPullback.of_hasPullback _ _

/-- The thickening `r₂` is a universal homeomorphism. -/
instance [IsSepClosed k'] : IsUniversalHomeomorphism (affineSpaceSliceThickening k' n i) := by
  have := isUniversalHomeomorphism_traitGenericCompositumPoint (trdeg_traitSliceField_le_one k')
  rw [affineSpaceSliceThickening]
  infer_instance

/-- The square exhibiting `r₁` as the base change of `Spec Ω_K ⟶ Spec L^sep`. -/
theorem isPullback_affineSpaceSliceInsepMap :
    IsPullback (affineSpaceSliceInsepMap k' n i)
      (pullback.snd (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k')) (traitGenericPoint (traitSliceField k')))
      (pullback.snd _ _) (traitGenericSepPoint k' (traitSliceField k')) := by
  have t := (IsPullback.of_hasPullback (pullback.snd (affineSpaceSliceCartTensor k' n i)
    (traitGenericCompositumPoint k' (traitSliceField k')))
    (traitGenericCompositumGalois k' (traitSliceField k'))).paste_horiz
      (IsPullback.of_hasPullback (affineSpaceSliceCartTensor k' n i)
        (traitGenericCompositumPoint k' (traitSliceField k')))
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) t
  have h := isPullback_affineSpaceSliceHom_toCart_generic (k' := k') n i
  rw [← affineSpaceSliceHom_toCart_generic_factor, ← traitGenericSpecMap_factor] at h
  simpa only [Category.assoc, affineSpaceSliceGaloisMap, affineSpaceSliceThickening] using h

/-- The purely inseparable part `r₁` is a universal homeomorphism. -/
instance : IsUniversalHomeomorphism (affineSpaceSliceInsepMap k' n i) :=
  MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism)
    (isPullback_affineSpaceSliceInsepMap n i).flip inferInstance

end Factor

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
