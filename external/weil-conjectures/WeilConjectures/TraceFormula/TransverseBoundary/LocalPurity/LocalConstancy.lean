/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DivisorComplementDirectImage
public import WeilConjectures.TraceFormula.TransverseBoundary.LocalPurity.DirectImage
public import WeilConjectures.TraceFormula.TransverseBoundary.OneDivisor
public import WeilConjectures.TraceFormula.TransverseBoundary.OneDivisorDevissage

/-!
# Local constancy along the boundary divisor, constant coefficients `ℤ/ℓ`

Let `C` be a transverse corner over an algebraically closed field `k`
(`AlgebraicGeometry.Scheme.TransverseCorner`), `W = Z - X`, `j_W : Z - (X ∪ Y) ⟶ W` and
`Y - z ⟶ W` the punctured divisor. For a prime `ℓ` invertible in `k`, the restriction of
`R j_{W*} ℤ/ℓ` to `Y - z` has finite locally constant cohomology sheaves (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`, constant coefficients): near every point of
`Y - z`, purity for the regular divisor `Y` of the étale limit of smooth surfaces `Z`
(`Scheme.exists_hasDivisorComplementDirectImages_of_isEtaleLimitOfSmoothSurfaces`)
computes `R^q j_* ℤ/ℓ` as `ℤ/ℓ`, `i_* ℤ/ℓ` and `0`
(`AlgebraicGeometry.Etale.HasDivisorComplementDirectImages.hasFiniteLocallyConstantHomology`).

## Main statements

- `TransverseCorner.hasFiniteLocallyConstantHomology_puncturedYι_jW_constantZModModule`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

open AlgebraicGeometry.Etale

variable {k : Type u} [Field k] [IsAlgClosed k] (C : TransverseCorner k) {ℓ : ℕ} [Fact ℓ.Prime]

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`, constant coefficients `ℤ/ℓ`: the
restriction of `R j_{W*} ℤ/ℓ` to the punctured divisor `Y - z` has finite locally constant
cohomology sheaves. -/
theorem hasFiniteLocallyConstantHomology_puncturedYι_jW_constantZModModule
    (hℓ : (ℓ : k) ≠ 0) :
    HasFiniteLocallyConstantHomology C.puncturedY
      ((L((C.puncturedYι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
        ((R((C.jW)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
          ((DerivedCategory.singleFunctor _ 0).obj (constantZModModule C.V ℓ)))) := by
  intro n
  choose O hO hO' using fun d : C.puncturedY ↦
    exists_hasDivisorComplementDirectImages_of_isEtaleLimitOfSmoothSurfaces C.aZ
      C.isEtaleLimitOfSmoothSurfaces C.iY C.j C.range_j ℓ hℓ (C.iY (C.puncturedY.ι d)) ⟨_, rfl⟩
  let Q (d : C.puncturedY) : C.W.toScheme.Opens := C.W.ι ⁻¹ᵁ O d
  have hι (d : C.puncturedY) : C.W.ι (C.puncturedYι d) = C.iY (C.puncturedY.ι d) := by
    rw [← Scheme.Hom.comp_apply, puncturedYι_ι, Scheme.Hom.comp_apply]
  refine @IsFiniteLocallyConstantSheaf.of_openCover _ _ _ _ _ _ _ _ _ _
    (Scheme.openCoverOfIsOpenCover _ (fun d ↦ C.puncturedYι ⁻¹ᵁ Q d) (eq_top_iff.2 fun d _ ↦
      TopologicalSpace.Opens.mem_iSup.2 ⟨d, by simpa [Q, hι] using hO d⟩)) _ fun d ↦ ?_
  let E := (DerivedCategory.singleFunctor _ 0).obj (constantZModModule C.V ℓ)
  suffices h : HasFiniteLocallyConstantHomology (C.puncturedYι ⁻¹ᵁ Q d)
      ((L((C.puncturedYι ∣_ Q d)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
        ((R((C.jW ∣_ Q d)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
          ((L(((C.jW ⁻¹ᵁ Q d).ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj E))) by
    have := (h.of_iso (restrictOpensIso C.jW C.puncturedYι (Q d) E 0)) n
    exact IsFiniteLocallyConstantSheaf.of_iso (F := (DerivedCategory.homologyFunctor _ n).obj
      ((L(((C.puncturedYι ⁻¹ᵁ Q d).ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
        ((L((C.puncturedYι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
        ((R((C.jW)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj E))))
      ((leftDerivedUpperStarHomologyFunctorIso _ (C.puncturedYι ⁻¹ᵁ Q d).ι n).app _).symm
  -- the restriction of `ℤ/ℓ` to `V ∩ Q` is `ℤ/ℓ`
  let e : (DerivedCategory.singleFunctor _ 0).obj (constantZModModule (C.jW ⁻¹ᵁ Q d) ℓ) ≅
      (L(((C.jW ⁻¹ᵁ Q d).ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj E :=
    ((DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) _).app _)).symm ≪≫
      ((singleFunctorCompLeftDerivedUpperStarIso _ _).app _).symm
  refine HasFiniteLocallyConstantHomology.of_iso ?_
    ((R((C.jW ∣_ Q d)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)]) ⋙
      L((C.puncturedYι ∣_ Q d)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).mapIso e)
  -- purity on `Q`
  have hf : Set.range ((Q d).ι ≫ C.W.ι) ⊆ (O d : Set C.Z) := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  have hjQ : Set.range ((C.jW ∣_ Q d) ≫ (Q d).ι ≫ C.W.ι) =
      Set.range ((Q d).ι ≫ C.W.ι) ∩ Set.range C.j := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, jW_ι]
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨⟨C.jW v.1, v.2⟩, ?_⟩, ⟨C.i v.1, rfl⟩⟩
      rw [Scheme.Hom.comp_apply, ← jW_ι]
      rfl
    · rintro ⟨⟨q, rfl⟩, hz⟩
      have hzX : ((Q d).ι ≫ C.W.ι) q ∉ Set.range C.iX := ((Q d).ι q).2
      have hzY : ((Q d).ι ≫ C.W.ι) q ∉ Set.range C.iY := by
        rw [← Set.mem_compl_iff, ← C.range_j]
        exact hz
      have : ((Q d).ι ≫ C.W.ι) q ∈ Set.range (C.i ≫ C.j) := by
        rw [C.range_i_j]
        exact fun h ↦ h.elim hzX hzY
      obtain ⟨v, hv⟩ := this
      have hq : C.jW v = (Q d).ι q := C.W.ι.isOpenEmbedding.injective (by
        rw [← Scheme.Hom.comp_apply, jW_ι, hv, Scheme.Hom.comp_apply])
      refine ⟨⟨v, ?_⟩, ?_⟩
      · rw [Scheme.Hom.mem_preimage, hq]
        exact q.2
      · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact hv
  obtain ⟨D', i', _, hi', hdi⟩ := hO' d (Q d) ((Q d).ι ≫ C.W.ι) hf _ (C.jW ∣_ Q d) hjQ
  refine hdi.hasFiniteLocallyConstantHomology _ ?_
  rintro _ ⟨w, rfl⟩
  have hw : ((Q d).ι ≫ C.W.ι) ((C.puncturedYι ∣_ Q d) w) ∈ Set.range (i' ≫ (Q d).ι ≫ C.W.ι) := by
    rw [hi']
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, morphismRestrict_ι, Category.assoc,
      puncturedYι_ι]
    exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := hw
  exact ⟨x, ((Q d).ι ≫ C.W.ι).isOpenEmbedding.injective hx⟩

end AlgebraicGeometry.Scheme.TransverseCorner
