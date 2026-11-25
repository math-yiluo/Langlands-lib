/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundTransport
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!
# Reduction of the uniform `Ext` bound to finite subextensions of `ℚ̄_ℓ`

An abstract finite extension `E` of `ℚ_ℓ` embeds into `ℚ̄_ℓ = PadicAlgCl ℓ`; its image is a
finite subextension `E' ⊆ ℚ̄_ℓ`, and the induced isomorphism `E ≃ E'` is a homeomorphism (a
linear isomorphism of finite-dimensional normed spaces over the complete field `ℚ_ℓ`). Hence the
coefficient rings `E̲_X` and `E̲'_X` are isomorphic ring objects, and the uniform `Ext` bound
`ProEtale.HasUniformConstructibleExtBound` transfers from `E'` to `E`
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_finiteIntermediateField`).

Similarly, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`, the rings of integers
`𝒪_E` and `𝒪_{E'}` of `E` and of its image `E'` are isomorphic topological rings, and the bound
transfers from `𝒪_{E'}` to `𝒪_E`
(`ProEtale.hasUniformConstructibleExtBound_padicIntegersRingObj_of_finiteIntermediateField`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace Profinite

variable {T T' : Type} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
  [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']

/-- A ring isomorphism `e : T ≃+* T'` which is a homeomorphism induces, by postcomposition, an
isomorphism of condensed rings `C(-, T) ≅ C(-, T')`. -/
noncomputable def continuousMapRingSheafIsoOfRingEquiv (e : T ≃+* T') (he : Continuous e)
    (he' : Continuous e.symm) :
    continuousMapRingSheaf.{u} T ≅ continuousMapRingSheaf T' where
  hom := continuousMapRingSheafMap e.toRingHom he
  inv := continuousMapRingSheafMap e.symm.toRingHom he'
  hom_inv_id := by
    ext S f
    refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext S f
    refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
    exact e.apply_symm_apply _

/-- A ring isomorphism `e : T ≃+* T'` which is a homeomorphism induces an isomorphism of ring
objects `C(-, T) ≅ C(-, T')` of condensed abelian groups. -/
noncomputable def continuousMapRingObjIsoOfRingEquiv (e : T ≃+* T') (he : Continuous e)
    (he' : Continuous e.symm) :
    continuousMapRingObj.{u} T ≅ continuousMapRingObj T' :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    (continuousMapRingSheafIsoOfRingEquiv e he he')

instance (e : T ≃+* T') (he : Continuous e) (he' : Continuous e.symm) :
    IsMonHom (continuousMapRingObjIsoOfRingEquiv.{u} e he he').hom :=
  inferInstanceAs (IsMonHom (continuousMapRingObjMap.{u} e.toRingHom he))

end Profinite

namespace AlgebraicGeometry.ProEtale

/-- The uniform `Ext` bound for the coefficient ring `T̲_X` only depends on the topological ring
`T` up to homeomorphic ring isomorphism. -/
lemma HasUniformConstructibleExtBound.of_continuousMapRingObj_ringEquiv {T T' : Type}
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
    (e : T ≃+* T') (he : Continuous e) (he' : Continuous e.symm) (X : Scheme.{u})
    (h : HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T') X)) :
    HasUniformConstructibleExtBound (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X) :=
  h.of_isIso
    ((upperStarFromPoint X).map (Profinite.continuousMapRingObjIsoOfRingEquiv e he he').hom)

/-! ### Abstract finite extensions `E` of `ℚ_ℓ` -/

section ContinuousMap

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- A (chosen) `ℚ_ℓ`-embedding of a finite extension `E` of `ℚ_ℓ` into `ℚ̄_ℓ`. -/
noncomputable def embeddingPadicAlgCl : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ :=
  IsAlgClosed.lift

/-- The image of a finite extension `E` of `ℚ_ℓ` under the embedding `embeddingPadicAlgCl`, a
finite subextension of `ℚ̄_ℓ`. -/
noncomputable def finiteIntermediateFieldOfEmbedding : PadicAlgCl.FiniteIntermediateField ℓ :=
  ⟨(embeddingPadicAlgCl ℓ E).fieldRange,
    (AlgEquiv.ofInjectiveField (embeddingPadicAlgCl ℓ E)).toLinearEquiv.finiteDimensional⟩

/-- The isomorphism of `E` with its image in `ℚ̄_ℓ`. -/
noncomputable def algEquivFiniteIntermediateFieldOfEmbedding :
    E ≃ₐ[ℚ_[ℓ]] (finiteIntermediateFieldOfEmbedding ℓ E).1 :=
  AlgEquiv.ofInjectiveField (embeddingPadicAlgCl ℓ E)

lemma continuous_algEquivFiniteIntermediateFieldOfEmbedding :
    Continuous (algEquivFiniteIntermediateFieldOfEmbedding ℓ E) :=
  continuous_induced_rng.2 (embeddingPadicAlgCl ℓ E).toLinearMap.continuous_of_finiteDimensional

lemma continuous_algEquivFiniteIntermediateFieldOfEmbedding_symm :
    Continuous (algEquivFiniteIntermediateFieldOfEmbedding ℓ E).symm :=
  (algEquivFiniteIntermediateFieldOfEmbedding ℓ E).symm.toLinearMap.continuous_of_finiteDimensional

/-- The uniform `Ext` bound for the coefficient ring `E̲_X` of an abstract finite extension `E` of
`ℚ_ℓ` follows from the one for the image `E'` of `E` in `ℚ̄_ℓ`. -/
theorem hasUniformConstructibleExtBound_continuousMapRingObj_of_finiteIntermediateField :
    ∃ E' : PadicAlgCl.FiniteIntermediateField ℓ, ∀ X : Scheme.{u},
      HasUniformConstructibleExtBound
          (condensedRingObj (Profinite.continuousMapRingObj.{u} E'.1) X) →
        HasUniformConstructibleExtBound
          (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X) :=
  ⟨finiteIntermediateFieldOfEmbedding ℓ E, fun X h ↦
    h.of_continuousMapRingObj_ringEquiv (algEquivFiniteIntermediateFieldOfEmbedding ℓ E).toRingEquiv
      (continuous_algEquivFiniteIntermediateFieldOfEmbedding ℓ E)
      (continuous_algEquivFiniteIntermediateFieldOfEmbedding_symm ℓ E) X⟩

end ContinuousMap

/-! ### Rings of integers of subfields of `ℚ̄_ℓ` -/

section Integers

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The image of a finite extension `E` of `ℚ_ℓ` embedded in `ℚ̄_ℓ`, a finite subextension of
`ℚ̄_ℓ`. -/
noncomputable def finiteIntermediateFieldOfAlgebra : FiniteIntermediateField ℓ :=
  ⟨(IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)).fieldRange,
    (AlgEquiv.ofInjectiveField
      (IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ))).toLinearEquiv.finiteDimensional⟩

/-- The isomorphism of a subfield `E` of `ℚ̄_ℓ` with its image. -/
noncomputable def algEquivFiniteIntermediateFieldOfAlgebra :
    E ≃ₐ[ℚ_[ℓ]] (finiteIntermediateFieldOfAlgebra ℓ E).1 :=
  AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ))

lemma algebraMap_algEquivFiniteIntermediateFieldOfAlgebra (x : E) :
    algebraMap (finiteIntermediateFieldOfAlgebra ℓ E).1 (PadicAlgCl ℓ)
        (algEquivFiniteIntermediateFieldOfAlgebra ℓ E x) =
      algebraMap E (PadicAlgCl ℓ) x :=
  rfl

/-- The isomorphism of the rings of integers `𝒪_E ≃ 𝒪_{E'}` of a subfield `E` of `ℚ̄_ℓ` and of
its image `E'`, the isomorphism `E ≃ E'` commuting with the embeddings into `ℚ̄_ℓ`. -/
noncomputable def integersRingEquivFiniteIntermediateFieldOfAlgebra :
    integers ℓ E ≃+* integers ℓ (finiteIntermediateFieldOfAlgebra ℓ E).1 where
  toFun x := ⟨algEquivFiniteIntermediateFieldOfAlgebra ℓ E x, by
    rw [mem_integers_iff, algebraMap_algEquivFiniteIntermediateFieldOfAlgebra]
    exact x.2⟩
  invFun y := ⟨(algEquivFiniteIntermediateFieldOfAlgebra ℓ E).symm y, by
    rw [mem_integers_iff, ← algebraMap_algEquivFiniteIntermediateFieldOfAlgebra,
      AlgEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext ((algEquivFiniteIntermediateFieldOfAlgebra ℓ E).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((algEquivFiniteIntermediateFieldOfAlgebra ℓ E).apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul (algEquivFiniteIntermediateFieldOfAlgebra ℓ E) x.1 y.1)
  map_add' x y := Subtype.ext (map_add (algEquivFiniteIntermediateFieldOfAlgebra ℓ E) x.1 y.1)

lemma continuous_integersRingEquivFiniteIntermediateFieldOfAlgebra :
    letI := normedFieldOfAlgebra ℓ E
    letI := normedFieldOfAlgebra ℓ (finiteIntermediateFieldOfAlgebra ℓ E).1
    Continuous (integersRingEquivFiniteIntermediateFieldOfAlgebra ℓ E) := by
  let := normedFieldOfAlgebra ℓ E
  let := normedFieldOfAlgebra ℓ (finiteIntermediateFieldOfAlgebra ℓ E).1
  exact continuous_induced_rng.2 (continuous_induced_rng.2
    ((continuous_algebraMap_padicAlgCl_of_algebra ℓ E).comp continuous_subtype_val))

lemma continuous_integersRingEquivFiniteIntermediateFieldOfAlgebra_symm :
    letI := normedFieldOfAlgebra ℓ E
    letI := normedFieldOfAlgebra ℓ (finiteIntermediateFieldOfAlgebra ℓ E).1
    Continuous (integersRingEquivFiniteIntermediateFieldOfAlgebra ℓ E).symm := by
  let := normedFieldOfAlgebra ℓ E
  let := normedFieldOfAlgebra ℓ (finiteIntermediateFieldOfAlgebra ℓ E).1
  refine continuous_induced_rng.2 (continuous_induced_rng.2 ?_)
  have h : Continuous fun y : integers ℓ (finiteIntermediateFieldOfAlgebra ℓ E).1 ↦
      algebraMap (finiteIntermediateFieldOfAlgebra ℓ E).1 (PadicAlgCl ℓ) y.1 :=
    (continuous_algebraMap_padicAlgCl_of_algebra ℓ _).comp continuous_subtype_val
  refine h.congr fun y ↦ ?_
  exact congrArg (algebraMap _ (PadicAlgCl ℓ))
    ((algEquivFiniteIntermediateFieldOfAlgebra ℓ E).apply_symm_apply y.1).symm

/-- The uniform `Ext` bound for the coefficient ring `𝒪̲_{E,X}` of a subfield `E` of `ℚ̄_ℓ`
follows from the one for its image `E'`, a finite subextension of `ℚ̄_ℓ`. -/
theorem hasUniformConstructibleExtBound_padicIntegersRingObj_of_finiteIntermediateField
    (X : Scheme.{u})
    (h : HasUniformConstructibleExtBound (condensedRingObj
      (Profinite.padicIntegersRingObj.{u} ℓ (finiteIntermediateFieldOfAlgebra ℓ E).1) X)) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) :=
  let := normedFieldOfAlgebra ℓ E
  let := normedFieldOfAlgebra ℓ (finiteIntermediateFieldOfAlgebra ℓ E).1
  h.of_continuousMapRingObj_ringEquiv (integersRingEquivFiniteIntermediateFieldOfAlgebra ℓ E)
    (continuous_integersRingEquivFiniteIntermediateFieldOfAlgebra ℓ E)
    (continuous_integersRingEquivFiniteIntermediateFieldOfAlgebra_symm ℓ E) X

end Integers

end AlgebraicGeometry.ProEtale
