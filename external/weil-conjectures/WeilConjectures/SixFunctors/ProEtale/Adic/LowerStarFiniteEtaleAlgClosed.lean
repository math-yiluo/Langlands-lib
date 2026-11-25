/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.PointCount
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleCounit
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarClopenSections

/-!
# Pushforward along a finite étale morphism to an algebraically closed point is exact

Let `K` be an algebraically closed field and `a : Y ⟶ Spec K` finite étale. Then `Y` is a finite
discrete space and every point `y` of `Y` is the image of a section `s_y` of `a`, since its
residue field is finite over `K`. These sections are open and closed immersions, as `a` is étale
and separated, with pairwise disjoint ranges `{y}` covering `Y`; hence `Y = ⊔_y Spec K` and the
pushforward `a_*` of `ℓ`-adic pro-étale sheaves is exact
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_sections`).

## Main results

- `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_id_of_isClosed`: a closed point of a scheme
  locally of finite type over an algebraically closed field `K` is the image of a section of the
  structure morphism.
- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isAlgClosed`: the
  pushforward along a finite étale `a : Y ⟶ Spec K` is exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A closed point `y` of a scheme locally of finite type over an algebraically closed field `K`
is the image of a section `s` of the structure morphism `a`: the residue field of `y` is finite
over `K`, hence admits a `K`-embedding into `K`. -/
theorem Scheme.Hom.exists_comp_eq_id_of_isClosed {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of K)) [LocallyOfFiniteType a] (y : Y)
    (hy : IsClosed {y}) :
    ∃ s : Spec (.of K) ⟶ Y, s ≫ a = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint K) = y := by
  let := (a.residueFieldAlgebraMap y).toAlgebra
  have := a.finite_residueField_of_isClosed y hy
  let φ : Y.residueField y →ₐ[K] K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Y.fromSpecResidueField y, ?_, ?_⟩
  · rw [Category.assoc, ← a.specMap_residueFieldAlgebraMap, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact φ.commutes x
  · rw [Scheme.Hom.comp_apply]
    exact Y.fromSpecResidueField_apply y _

/-- A section `s` of an étale morphism `a` is an open immersion: it is the graph of `s` over `a`
followed by the isomorphism `pullback (s ≫ a) a ≅ Y`. -/
lemma Scheme.Hom.isOpenImmersion_of_comp_eq_id {Y S : Scheme.{u}} (a : Y ⟶ S) [Etale a]
    (s : S ⟶ Y) (hs : s ≫ a = 𝟙 S) : IsOpenImmersion s := by
  have : IsIso (s ≫ a) := hs ▸ inferInstance
  have := isOpenImmersion_pullbackLift_of_etale a s
  rw [← pullback.lift_snd (f := s ≫ a) (g := a) (𝟙 S) s (by simp)]
  infer_instance

/-- A section `s` of a separated morphism `a` is a closed immersion: it is the graph of `s` over
`a` followed by the isomorphism `pullback (s ≫ a) a ≅ Y`. -/
lemma Scheme.Hom.isClosedImmersion_of_comp_eq_id {Y S : Scheme.{u}} (a : Y ⟶ S) [IsSeparated a]
    (s : S ⟶ Y) (hs : s ≫ a = 𝟙 S) : IsClosedImmersion s := by
  have : IsIso (s ≫ a) := hs ▸ inferInstance
  have := isClosedImmersion_pullbackLift_of_isSeparated a s
  rw [← pullback.lift_snd (f := s ≫ a) (g := a) (𝟙 S) s (by simp)]
  infer_instance

namespace ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- **Pushforward along a finite étale morphism to `Spec K`, `K` algebraically closed, is
exact.** The scheme `Y` is finite and discrete, and the sections of `a : Y ⟶ Spec K` through its
points form a clopen partition of `Y` into sections. -/
theorem preservesFiniteColimits_adicLowerStar_of_isAlgClosed {K : Type u} [Field K]
    [IsAlgClosed K] {Y : Scheme.{u}} (a : Y ⟶ Spec (.of K)) [IsFinite a] [Etale a] :
    PreservesFiniteColimits (a)_*ᵃ[l] := by
  have : IsLocallyArtinian Y := .of_locallyQuasiFinite a
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace a
  have : Finite Y := finite_of_compact_of_discrete
  choose s hs hy using fun y : Y ↦ a.exists_comp_eq_id_of_isClosed y (isClosed_discrete _)
  have hrange (y : Y) : Set.range (s y).base = {y} := by
    refine Set.ext fun z ↦ ⟨?_, ?_⟩
    · rintro ⟨p, rfl⟩
      rw [Subsingleton.elim p (IsLocalRing.closedPoint K), hy]
      rfl
    · rintro rfl
      exact ⟨_, hy z⟩
  have (y : Y) : IsOpenImmersion (s y) := a.isOpenImmersion_of_comp_eq_id (s y) (hs y)
  refine preservesFiniteColimits_adicLowerStar_of_sections a s l hs (fun y ↦ ?_) (fun y y' h ↦ ?_)
    (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, (hrange y).symm ▸ rfl⟩)
  · exact isClosed_discrete _
  · simp only [hrange]
    exact Set.disjoint_singleton.2 h

end ProEtale

end AlgebraicGeometry
