/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionProper

/-!
# Reduction modulo `ℓⁿ` commutes with `Rj_!` and `Rj^!` along open immersions

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). This file proves that an open immersion
`j : U ⟶ X` has a reduction comparison for `Rj_!` and `Rj^!`
(`ProEtale.CondensedRing.hasEtaleReductionLowerShriekIso_of_isOpenImmersion`), the open-immersion
case of blueprint `lemma-change-coefficients-exceptional-inverse-image`.

## Strategy

On both sides `Rj^!` is the pullback `j^*`: on bounded constructible `𝒪_E`-complexes, `Rj_!` is
the extension by zero `j_!` by independence of the compactification
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers`),
and `Rj^! ≅ j^*` is its conjugate; on the étale side this is
`Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`. As reduction commutes with pullback
(`ProEtale.CondensedRing.etaleReductionUpperStarIso`), we get an isomorphism
`δ : Rj^! ⋙ red_U ≅ red_X ⋙ Rj^!`
(`ProEtale.CondensedRing.etaleReductionUpperShriekIsoOfIsOpenImmersion`). Let
`θ : red_U ⋙ Rj_! ⟶ Rj_! ⋙ red_X` be the transpose of `δ` under `Rj_! ⊣ Rj^!`; its transpose
back is `δ`, an isomorphism, and it remains to see that `θ` is an isomorphism. This is checked
after restriction to `U` and to the closed complement `i : Z ⟶ X` of `j` (open–closed
conservativity on `X_ét`):

* after `j^*`, the map `θ_K` is identified, through the units of the two adjunctions
  `Rj_! ⊣ Rj^!` (invertible, `j_!` being fully faithful on both sides), with `δ_{Rj_! K}`;
* after `i^*`, source and target vanish: `i^* j_! = 0` on the étale side, and
  `i^* red_X ≅ red_Z i^*` with `i^* j_! = 0` on the condensed side.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-! ### `Rj_!` and `Rj^!` on bounded constructible `𝒪_E`-complexes -/

/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` of the derived pushforward on bounded constructible
`𝒪_E`-complexes: the conjugate of `boundedConstructibleUpperStarId` under the adjunctions
`L(𝟙 X)^* ⊣ R(𝟙 X)_*` and `𝟭 ⊣ 𝟭`. -/
noncomputable def boundedConstructibleLowerStarId_padicIntegers (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E (𝟙 X) ≅
      𝟭 (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :=
  conjugateIsoEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (𝟙 X)) Adjunction.id
    (boundedConstructibleUpperStarId (Profinite.padicIntegersRingObj ℓ E) ℓ X).symm

variable {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The lower shriek along an open immersion is the extension by zero, `Rj_! ≅ j_!`, on bounded
constructible `𝒪_E`-complexes: by independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers`), `Rj_!` is
`j_! ⋙ R(𝟙 X)_*` for the trivial compactification `U ⟶[j] X ⟶[𝟙] X`, and `R(𝟙 X)_* ≅ 𝟭`. -/
noncomputable def boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ j :=
  boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E
      (compactificationOverField j) (.ofIsOpenImmersion j.left) ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ j)
      (boundedConstructibleLowerStarId_padicIntegers ℓ E X) ≪≫
    Functor.rightUnitor _

/-- The exceptional inverse image along an open immersion is the pullback, `Rj^! ≅ j^*`, on
bounded constructible `𝒪_E`-complexes: the conjugate of
`boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers` under the adjunctions
`Rj_! ⊣ Rj^!` and `j_! ⊣ j^*`. -/
noncomputable def boundedConstructibleUpperShriekIsoUpperStar_padicIntegers :
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E j ≅
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ j :=
  conjugateIsoEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j).symm

/-! ### Reduction modulo `ℓⁿ` and `Rj^!` -/

/-- **Reduction modulo `ℓⁿ`, read on the étale site, commutes with `Rj^!` for an open immersion
`j`**: `Rj^! ⋙ red_U ≅ red_X ⋙ Rj^!`. Both exceptional inverse images are the pullback `j^*`
(`boundedConstructibleUpperShriekIsoUpperStar_padicIntegers` and
`Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`), and reduction commutes with pullback
(`etaleReductionUpperStarIso`). -/
noncomputable irreducible_def etaleReductionUpperShriekIsoOfIsOpenImmersion :
    have := HasCompactification.of_over j
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E j ⋙ etaleReduction ℓ E n U ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) j.left :=
  have := HasCompactification.of_over j
  Functor.isoWhiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E j) _ ≪≫
    etaleReductionUpperStarIso ℓ E n j ≪≫
    Functor.isoWhiskerLeft _
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ j.left ≪≫
        (Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion _ j.left).symm)

/-- Blueprint `lemma-change-coefficients-exceptional-inverse-image`, open-immersion case, for the
coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site. **Open immersions have a reduction
comparison for `Rj_!` and `Rj^!`**: there is an isomorphism `γ : Rj_! ⋙ red_X ≅ red_U ⋙ Rj_!` whose
transpose under `Rj_! ⊣ Rj^!` is an isomorphism.

The comparison `γ` is the inverse of the transpose `θ` of
`etaleReductionUpperShriekIsoOfIsOpenImmersion`, so that its own transpose is invertible by
construction; `θ` is invertible by open–closed conservativity on `X_ét`. After `j^*`, it is
identified with `δ_{Rj_! K}` through the units of the two adjunctions `Rj_! ⊣ Rj^!`, which are
invertible as `j_!` is fully faithful on both sides (`CategoryTheory.unit_mateEquiv`); after
`i^*`, for `i` the closed complement of `j`, both its source and target vanish. -/
theorem hasEtaleReductionLowerShriekIso_of_isOpenImmersion :
    HasEtaleReductionLowerShriekIso ℓ E n j := by
  have := HasCompactification.of_over j
  let A := ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)
  let adj₁ := PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j
  let adj₂ := Etale.rightDerivedUpperShriekAdjunction (integersModPowCoeff.{u} ℓ E n) j.left
  let δ := etaleReductionUpperShriekIsoOfIsOpenImmersion ℓ E n j
  obtain ⟨θ, hθ⟩ : ∃ θ, mateEquiv adj₁ adj₂ θ = δ.hom := ⟨_, Equiv.apply_symm_apply _ _⟩
  -- the units of `Rj_! ⊣ Rj^!` are invertible, `Rj_!` being fully faithful on both sides
  have : IsIso adj₁.unit := by
    have ff := (fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicIntegersRingObj ℓ E) ℓ j).ofIso
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j).symm
    have := ff.full
    have := ff.faithful
    infer_instance
  have : IsIso adj₂.unit := by
    have ff := (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction A
      j.left).fullyFaithfulLOfIsIsoUnit.ofIso
        (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left).symm
    have := ff.full
    have := ff.faithful
    infer_instance
  have (K : Dᵇc(U.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) : IsIso (θ.app K) := by
    let i := overClosedComplement j
    refine (Etale.jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar' A j.left i.left
      (range_overClosedComplement j)).isIso_of_pairFunctor _ ?_ ?_
    · rw [← NatIso.isIso_map_iff (Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion _ j.left)]
      have h := unit_mateEquiv adj₁ adj₂ θ K
      rw [hθ] at h
      dsimp only [Functor.id_obj] at h
      have hc : IsIso ((etaleReduction ℓ E n U).map (adj₁.unit.app K) ≫
          δ.hom.app ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j).obj K)) :=
        inferInstance
      rw [h] at hc
      exact IsIso.of_isIso_comp_left (adj₂.unit.app _) _
    · have hd : Disjoint (Set.range i.left.base) (Set.range j.left.base) :=
        (isCompl_range_overClosedComplement j).disjoint
      have h₁ : IsZero ((Etale.upperStar A i.left).mapDerivedCategory.obj
          ((Etale.rightDerivedLowerShriek A j.left).obj ((etaleReduction ℓ E n U).obj K))) :=
        (Etale.isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
          A j.left i.left hd _).of_iso ((Etale.upperStar A i.left).mapDerivedCategory.mapIso
            ((Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left).app _))
      have h₂ : IsZero ((Etale.upperStar A i.left).mapDerivedCategory.obj
          ((etaleReduction ℓ E n X).obj
            ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j).obj K))) := by
        have := Functor.preservesZeroMorphisms_of_iso
          (etaleReductionIsoDerivedEtaleReduction ℓ E n (overClosedComplementObj j)).symm
        refine (Functor.map_isZero (etaleReduction ℓ E n (overClosedComplementObj j))
          (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
            (Profinite.padicIntegersRingObj ℓ E) ℓ j i hd.symm K)).of_iso ?_
        exact ((Etale.leftDerivedUpperStarIsoMapDerivedCategory A i.left).app _).symm ≪≫
          ((etaleReductionUpperStarIso ℓ E n i).app _).symm ≪≫
          (etaleReduction ℓ E n _).mapIso ((boundedConstructibleUpperStar _ ℓ i).mapIso
            ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j).app
              K))
      exact ⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩
  have : IsIso θ := NatIso.isIso_of_isIso_app _
  refine ⟨(asIso θ).symm, ?_⟩
  rw [Iso.symm_inv, asIso_hom]
  exact hθ ▸ inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
