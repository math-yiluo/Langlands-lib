/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteTypePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve

/-!
# Constructibility of projective direct images

For a finite ring `Λ` killed by an integer invertible in a field `k`, this file proves that
every projective morphism `f` between schemes of finite type over `k` satisfies `𝒞(f)`: its
higher direct images preserve constructibility.

- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_projectiveLine`
  (`proposition-proper-direct-image-finite-coefficients`): the projective line `ℙ¹_S ⟶ S`, by
  resolving a constructible sheaf by finite pushforwards of constant sheaves and using the case of
  curves;
- `AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_projectiveLine`
  (`proposition-proper-direct-image-finite-coefficients`): from the projective line to all
  projective morphisms, through `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` (finite and surjective) and composition;
- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isClosedImmersion`
  (`proposition-proper-direct-image-finite-coefficients`).

A morphism `f : X ⟶ S` is projective (`def-pc-projective-morphism`) if it is the composite of a
closed immersion `X ⟶ ℙ(N; S)`, for a finite type `N` of homogeneous coordinates, with the
structure morphism; quasi-compactness is automatic here, `S` being Noetherian.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme ProjectiveSpace

/-- The projection `(ℙ¹_S)ⁿ ⟶ S` of the tower of projective lines is proper. -/
instance ProjectiveSpace.isProper_projectiveLinePowProj (n : ℕ) (S : Scheme.{u}) :
    IsProper (projectiveLinePowProj n S) := by
  induction n with
  | zero => exact inferInstanceAs (IsProper (𝟙 S))
  | succ n ih =>
    exact inferInstanceAs
      (IsProper ((ProjectiveLine (projectiveLinePow n S) ↘ _) ≫ projectiveLinePowProj n S))

/-- **Geometric fibres of a finite cover of the projective line.** For `h : Y ⟶ ℙ¹_S` finite and
a point `s : Spec Ω ⟶ S` with values in a field, the fibre `Y ×_S Spec Ω` of `h ≫ π` has
dimension at most one: it is finite over the fibre `ℙ¹_Ω` of `π : ℙ¹_S ⟶ S`. -/
lemma ProjectiveSpace.topologicalKrullDim_pullback_comp_projectiveLine_le_one
    {S Y : Scheme.{u}} (h : Y ⟶ ProjectiveLine S) [IsFinite h] (Ω : Type u) [Field Ω]
    (s : Spec (.of Ω) ⟶ S) :
    topologicalKrullDim (pullback (h ≫ ProjectiveLine S ↘ S) s : Scheme.{u}) ≤ 1 := by
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (pullbackRightPullbackFstIso (ProjectiveLine S ↘ S) s h).hom.homeomorph.isHomeomorph]
  refine (pullback.snd h (pullback.fst (ProjectiveLine S ↘ S) s)
    ).topologicalKrullDim_le_of_locallyQuasiFinite.trans ?_
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (isPullback_map (ULift.{u} (Fin 2)) s).isoPullback.hom.homeomorph.isHomeomorph]
  exact topologicalKrullDim_projectiveLine_le_one Ω

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-- The case of an affine base of `proposition-proper-direct-image-finite-coefficients`: every
constructible sheaf `Q` on `ℙ¹_S` embeds into a finite direct sum `G = ⨁ᵢ (hᵢ)_* Mᵢ` of direct
images of constant sheaves with finite values along finite morphisms `hᵢ : Yᵢ ⟶ ℙ¹_S`. Each `Yᵢ` is
projective over the affine scheme `S`, with geometric fibres of dimension at most one, so the
direct images `Rᵠ(hᵢ ≫ π)_* Mᵢ = Rᵠπ_*((hᵢ)_* Mᵢ)` are constructible by the case of curves
`proposition-proper-direct-image-finite-coefficients`; the resolution principle concludes. -/
theorem hasConstructibleDirectImages_projectiveLine_of_isAffine
    [HasInvertibleExponent Λ (Spec (.of k))] {S : Scheme.{u}} [IsAffine S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] :
    HasConstructibleDirectImages Λ (ProjectiveLine S ↘ S) := by
  have : HasInvertibleExponent Λ S := .of_hom aS
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S ≫ aS)
  have : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S ≫ aS)
  have : IsNoetherian (ProjectiveLine S) := {}
  refine hasConstructibleDirectImages_of_exists_mono _ fun Q hQ ↦ ?_
  obtain ⟨r, Y, h, _, M, _, φ, _⟩ :=
    exists_mono_biproduct_lowerStar_of_locallyOfFiniteType Λ (ProjectiveLine S ↘ S ≫ aS) Q
  have (i : Fin r) : IsConstructibleSheaf (((h i)_*[ModuleCat.{u + 1} Λ]).obj
      ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) := by
    have : Module.Finite Λ (M i) := .of_finite
    have := isFiniteLocallyConstantSheaf_constantSheaf (X := Y i) (M i)
    have : IsConstructibleSheaf
        ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i)) :=
      ⟨Stratification.trivial _, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 _) _⟩
    exact Scheme.IsConstructibleSheaf.lowerStar_of_isFinite (h i) _
  refine ⟨_, φ, inferInstance, IsConstructibleSheaf.biproduct _, ?_⟩
  refine constructibleHomology_rightDerivedLowerStar_biproduct _ _ fun i ↦ ?_
  refine (Etale.DerivedCategory.constructibleHomology _ S).prop_of_iso
    (rightDerivedLowerStarSingleLowerStarIso (h i) _ _).symm fun q ↦ ?_
  obtain ⟨m, _, j, _, hj⟩ := exists_isClosedImmersion_of_isFinite (ProjectiveLine S ↘ S) (𝟙 _)
    (Category.id_comp _) (h i)
  exact isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf Λ aS _ j hj
    (fun Ω _ _ s ↦ topologicalKrullDim_pullback_comp_projectiveLine_le_one (h i) Ω s) (M i) q

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Constructible coefficients on
the projective line.

Let `S` be of finite type over a field `k`, and let `Λ` be a finite ring killed by an integer
invertible in `k`. For every constructible sheaf `F` of `Λ`-modules on `ℙ¹_S`, every higher
direct image `Rᵠπ_* F` along `π : ℙ¹_S ⟶ S` is constructible. -/
theorem hasConstructibleDirectImages_projectiveLine [HasInvertibleExponent Λ (Spec (.of k))]
    {S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] :
    HasConstructibleDirectImages Λ (ProjectiveLine S ↘ S) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  refine HasConstructibleDirectImages.of_iSup_eq_top _ (fun U : S.affineOpens ↦ (U : S.Opens))
    (iSup_affineOpens_eq_top S) fun U ↦ ?_
  have : IsAffine U.1 := U.2
  have : QuasiCompact (U.1.ι ≫ aS) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 inferInstance
  have : IsLocallyNoetherian (ProjectiveLine U.1) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine U.1 ↘ U.1 ≫ U.1.ι ≫ aS)
  have : CompactSpace (ProjectiveLine U.1) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine U.1 ↘ U.1 ≫ U.1.ι ≫ aS)
  have : IsNoetherian (ProjectiveLine U.1) := {}
  -- `π ∣_ U` is `ℙ¹_U ⟶ U`, up to the isomorphism of the two pullbacks of `π` along `U ⟶ S`
  rw [← (isPullback_morphismRestrict (ProjectiveLine S ↘ S) U.1).flip.isoIsPullback_hom_snd _ _
    (isPullback_map (ULift.{u} (Fin 2)) U.1.ι)]
  exact HasConstructibleDirectImages.comp (fun F _ ↦
    (boundedConstructible_rightDerivedLowerStar_of_isFinite Λ _
      (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)).2)
    (hasConstructibleDirectImages_projectiveLine_of_isAffine (U.1.ι ≫ aS))

/-- **`𝒞` for finite morphisms.** A finite morphism `f : X ⟶ S` with Noetherian target
satisfies `𝒞(f)`: `f_*` is exact and preserves constructible sheaves. -/
theorem hasConstructibleDirectImages_of_isFinite {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsFinite f] : HasConstructibleDirectImages Λ f := fun F _ ↦
  (boundedConstructible_rightDerivedLowerStar_of_isFinite Λ f
    (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)).2

/-- **`𝒞` for the tower of projective lines.** If `𝒞(ℙ¹_T ⟶ T)` holds for every scheme `T` of
finite type over `k`, then `𝒞((ℙ¹_S)ⁿ ⟶ S)` holds for every `S` of finite type over `k`, the
projection being a composite of projective lines over successive bases of finite type. -/
theorem hasConstructibleDirectImages_projectiveLinePowProj
    (h : ∀ (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
      HasConstructibleDirectImages Λ (ProjectiveLine T ↘ T))
    {S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (n : ℕ) : HasConstructibleDirectImages Λ (projectiveLinePowProj n S) := by
  induction n with
  | zero =>
    have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
    have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
    have : IsNoetherian S := {}
    exact hasConstructibleDirectImages_of_isFinite (𝟙 S)
  | succ n ih => exact (h _ (projectiveLinePowProj n S ≫ aS)).comp ih

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Projective constructibility
from projective-line constructibility.

Suppose `𝒞(ℙ¹_T ⟶ T)` holds for every scheme `T` of finite type over `k`. Then `𝒞(f)` holds for
every projective morphism `f : X ⟶ S` with `S` of finite type over `k`: here `f` is the
composite of a closed immersion `e : X ⟶ ℙ(N; S)` with the structure morphism. -/
theorem HasConstructibleDirectImages.of_projectiveLine
    (h : ∀ (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
      HasConstructibleDirectImages Λ (ProjectiveLine T ↘ T))
    {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) (N : Type u) [Finite N] (e : X ⟶ ℙ(N; S)) [IsClosedImmersion e]
    (he : e ≫ ℙ(N; S) ↘ S = f) : HasConstructibleDirectImages Λ f := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsLocallyNoetherian ℙ(N; S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(N; S) ↘ S ≫ aS)
  have : CompactSpace ℙ(N; S) := QuasiCompact.compactSpace_of_compactSpace (ℙ(N; S) ↘ S ≫ aS)
  have : IsNoetherian ℙ(N; S) := {}
  -- `𝒞(ℙⁿ_S ⟶ S)`, through the finite surjective symmetric product `(ℙ¹_S)ᵏ ⟶ ℙⁿ_S`
  have hP : HasConstructibleDirectImages Λ (ℙ(N; S) ↘ S) := by
    cases isEmpty_or_nonempty N with
    | inl _ => exact hasConstructibleDirectImages_of_isFinite _
    | inr _ =>
      obtain ⟨k, σ, _, _, hσ⟩ := exists_isFinite_surjective_projectiveLinePow N S
      refine HasConstructibleDirectImages.of_comp_of_isFinite (ℙ(N; S) ↘ S ≫ aS) _ σ ?_
      rw [hσ]
      exact hasConstructibleDirectImages_projectiveLinePowProj h aS k
  subst he
  exact (hasConstructibleDirectImages_of_isFinite e).comp hP

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Projective direct-image
constructibility.

Let `Λ` be a finite ring killed by an integer invertible in the field `k`. Every projective
morphism `f : X ⟶ S` with `S` of finite type over `k` (so `f` is the composite of a closed
immersion `e : X ⟶ ℙ(N; S)` with the structure morphism) satisfies `𝒞(f)`. -/
theorem hasConstructibleDirectImages_of_isClosedImmersion
    [HasInvertibleExponent Λ (Spec (.of k))] {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) (N : Type u) [Finite N]
    (e : X ⟶ ℙ(N; S)) [IsClosedImmersion e] (he : e ≫ ℙ(N; S) ↘ S = f) :
    HasConstructibleDirectImages Λ f :=
  HasConstructibleDirectImages.of_projectiveLine
    (fun _ aT _ _ ↦ hasConstructibleDirectImages_projectiveLine aT) aS f N e he

end Etale

end AlgebraicGeometry
