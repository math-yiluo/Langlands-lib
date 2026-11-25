/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGalois
public import WeilConjectures.TraceFormula.Specialization.TraitSliceTraitAlgebra

/-!

# Generic automorphisms as the Galois group of `L^sep / L`

Let `L = Ω(K⟦t⟧) ⊆ Ω_K` be the compositum of the image of `Ω = (Frac k'⟦t⟧)^alg` and of `K⟦t⟧`
(`AlgebraicGeometry.traitTensorCompositum`, for the algebra structures of
`AlgebraicGeometry.traitGenericFieldAlgebra`) and `L^sep` its separable closure in `Ω_K`. A
generic automorphism (`NearbyCyclesModel.GenericAut`) fixes `L`
(`NearbyCyclesModel.GenericAut.toRingAut_traitTensorCompositum`), hence restricts to an element of
`Gal(L^sep / L)`. This gives a group isomorphism
`NearbyCyclesModel.GenericAut.galoisEquiv : GenericAut k' K ≃* Gal(L^sep / L)`:

* it is injective since `Ω_K / L^sep` is purely inseparable;
* it is surjective since every automorphism of `L^sep / L` extends to the normal extension
  `Ω_K / L`, and an automorphism of `Ω_K` fixing `L` fixes `Frac K⟦t⟧` and the image of `Ω`.

-/

@[expose] public section

universe u

open CategoryTheory IntermediateField

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut

attribute [local instance] traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- The fixed points of a generic automorphism, as an intermediate field of `Ω_K / Ω`. -/
noncomputable def fixedIntermediateField (σ : GenericAut k' K) :
    IntermediateField (traitGenericField k') (traitGenericField K) :=
  (RingHom.eqLocusField (toRingAut σ).toRingHom (RingHom.id _)).toIntermediateField
    fun y ↦ toRingAut_traitGenericFieldMap σ y

/-- **A generic automorphism fixes the compositum `L = Ω(K⟦t⟧)`.** -/
lemma toRingAut_traitTensorCompositum (σ : GenericAut k' K) :
    ∀ y : traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K),
      toRingAut σ (y : traitGenericField K) = y := by
  have hle : traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K) ≤
      fixedIntermediateField σ := by
    refine adjoin_le_iff.2 ?_
    rintro _ ⟨a, rfl⟩
    exact toRingAut_algebraMap σ a
  exact fun y ↦ hle y.2

/-- A generic automorphism as an automorphism of `Ω_K` over the compositum `L = Ω(K⟦t⟧)`. -/
noncomputable def toCompositumAlgEquiv :
    GenericAut k' K →* (traitGenericField K ≃ₐ[traitTensorCompositum (PowerSeries K)
      (traitGenericField k') (traitGenericField K)] traitGenericField K) :=
  { toFun := fun σ ↦ AlgEquiv.ofRingEquiv (f := toRingAut σ) (toRingAut_traitTensorCompositum σ)
    map_one' := by
      ext
      simp
    map_mul' := fun σ τ ↦ by
      ext x
      exact RingEquiv.congr_fun (map_mul toRingAut σ τ) x }

@[simp]
lemma toCompositumAlgEquiv_apply (σ : GenericAut k' K) (x : traitGenericField K) :
    toCompositumAlgEquiv σ x = toRingAut σ x :=
  rfl

/-- The restriction of a generic automorphism to `L^sep`: a group homomorphism
`GenericAut k' K →* Gal(L^sep / L)`. -/
noncomputable def toGalois :
    GenericAut k' K →* (traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
      (traitGenericField K) ≃ₐ[traitTensorCompositum (PowerSeries K) (traitGenericField k')
        (traitGenericField K)] traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
          (traitGenericField K)) :=
  (AlgEquiv.restrictNormalHom _).comp toCompositumAlgEquiv

/-- The restriction of a generic automorphism to `L^sep` agrees with the generic automorphism. -/
lemma algebraMap_toGalois_apply (σ : GenericAut k' K) :
    ∀ y : traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K),
      ((toGalois σ y : traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
        (traitGenericField K)) : traitGenericField K) = toRingAut σ (y : traitGenericField K) := by
  intro y
  exact AlgEquiv.restrictNormal_commutes (toCompositumAlgEquiv σ) _ y

/-- The restriction to `L^sep` is injective: `Ω_K / L^sep` is purely inseparable. -/
lemma toGalois_injective :
    Function.Injective (toGalois (k' := k') (K := K)) := by
  set L := traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K)
  set Ls := traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K)
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine toRingAut_injective (RingEquiv.ext fun x ↦ ?_)
  rw [map_one, RingAut.one_apply]
  set q := ringExpChar (traitGenericField K)
  have : ExpChar Ls q := (algebraMap Ls (traitGenericField K)).expChar
    (algebraMap Ls (traitGenericField K)).injective q
  obtain ⟨n, s, hs⟩ := IsPurelyInseparable.pow_mem Ls q x
  apply iterateFrobenius_inj (traitGenericField K) q n
  have h := algebraMap_toGalois_apply σ s
  rw [hσ, AlgEquiv.one_apply] at h
  simp only [iterateFrobenius_def]
  rw [← map_pow, ← hs]
  exact h.symm

/-- `Ω_K` is an algebraic closure of the compositum `L`. -/
instance :
    IsAlgClosure (traitTensorCompositum (PowerSeries K) (traitGenericField k')
      (traitGenericField K)) (traitGenericField K) :=
  ⟨inferInstance, inferInstance⟩

/-- The restriction to `L^sep` is surjective: automorphisms of `L^sep / L` extend to `Ω_K`. -/
lemma toGalois_surjective :
    Function.Surjective (toGalois (k' := k') (K := K)) := by
  set L := traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K)
  intro τ
  have : Normal L (traitGenericField K) := IsAlgClosure.normal L (traitGenericField K)
  let e : traitGenericField K ≃ₐ[L] traitGenericField K := τ.liftNormal (traitGenericField K)
  have he (y : L) : e y = y := e.commutes y
  let e' : traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun a ↦
      he ⟨_, algebraMap_fractionRing_mem_traitTensorCompositum a⟩
  let σ := ofAlgEquiv e' fun y ↦ he ⟨_, IntermediateField.algebraMap_mem L y⟩
  have hσ (x : traitGenericField K) : toRingAut σ x = e x :=
    AlgEquiv.congr_fun (toAlgEquiv_ofAlgEquiv e' _) x
  refine ⟨σ, AlgEquiv.ext fun y ↦ Subtype.ext ?_⟩
  rw [algebraMap_toGalois_apply, hσ]
  exact AlgEquiv.liftNormal_commutes τ (traitGenericField K) y

/-- **The generic automorphisms are the Galois group of `L^sep / L`**: restriction to `L^sep` is a
group isomorphism `GenericAut k' K ≃* Gal(L^sep / L)`. -/
noncomputable def galoisEquiv :
    GenericAut k' K ≃* (traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
      (traitGenericField K) ≃ₐ[traitTensorCompositum (PowerSeries K) (traitGenericField k')
        (traitGenericField K)] traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
          (traitGenericField K)) :=
  MulEquiv.ofBijective toGalois ⟨toGalois_injective, toGalois_surjective⟩

@[simp]
lemma galoisEquiv_apply (σ : GenericAut k' K) :
    galoisEquiv σ = toGalois σ :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut
