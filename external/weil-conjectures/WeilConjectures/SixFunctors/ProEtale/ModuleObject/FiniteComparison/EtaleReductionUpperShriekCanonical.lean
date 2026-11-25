/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekCanonical

/-!
# The canonical reduction comparisons for `Rf_!` and `Rf^!`

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). For every morphism `f : X ⟶ Y` of separated
`k`-schemes of finite type, this file constructs canonical isomorphisms (blueprint
`lemma-change-coefficients-exceptional-inverse-image`, for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`)

* `ProEtale.CondensedRing.etaleReductionLowerShriekIsoOfCompactification`:
  `Rf_! ⋙ red_Y ≅ red_X ⋙ Rf_!`, attached to a compactification `X ⟶[i] P ⟶[p] Y` of `f`;
* `ProEtale.CondensedRing.etaleReductionUpperShriekIso`: `Rf^! ⋙ red_X ≅ red_Y ⋙ Rf^!`, the
  transpose of the former for the chosen compactification `compactificationOverField f`,

without any choice of witnesses of existential statements: they are assembled from the canonical
comparisons along the open immersion `i` (the transpose of
`ProEtale.CondensedRing.etaleReductionUpperShriekIsoOfIsOpenImmersion`) and along the proper `p`
(`ProEtale.CondensedRing.etaleReductionLowerShriekIso`), through the composition isomorphisms
`R(i ≫ p)_! ≅ Ri_! ⋙ Rp_!` on both sides
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicIntegers` and
`Etale.rightDerivedLowerShriekCompIsoOfEq`).

## Main results

- `ProEtale.CondensedRing.etaleReductionLowerShriekIsoOfIsOpenImmersion`: the canonical
  comparison `Rj_! ⋙ red_X ≅ red_U ⋙ Rj_!` for an open immersion `j`, whose transpose is
  `etaleReductionUpperShriekIsoOfIsOpenImmersion`.
- `ProEtale.CondensedRing.etaleReductionLowerShriekIsoOfComp`: the stacked comparison for a
  composite, and `ProEtale.CondensedRing.isIso_mateEquiv_etaleReductionLowerShriekIsoOfComp`.
- `ProEtale.CondensedRing.etaleReductionUpperShriekIso`: reduction modulo `ℓⁿ` commutes with
  `Rf^!`, canonically.
- `ProEtale.CondensedRing.hasEtaleReductionLowerShriekIso_of_compactification`.
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

/-! ### Open immersions -/

section OpenImmersion

variable {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The canonical reduction square for `Rj_!` along an open immersion `j`:
`red_U ⋙ Rj_! ⟶ Rj_! ⋙ red_X`, the transpose under the adjunctions `Rj_! ⊣ Rj^!` of the
canonical isomorphism `etaleReductionUpperShriekIsoOfIsOpenImmersion`. -/
noncomputable def etaleReductionLowerShriekSquareOfIsOpenImmersion :
    have := HasCompactification.of_over j
    TwoSquare (etaleReduction ℓ E n U) (PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j)
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) j.left)
      (etaleReduction ℓ E n X) :=
  have := HasCompactification.of_over j
  (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
    (Etale.rightDerivedUpperShriekAdjunction _ j.left)).symm
    (etaleReductionUpperShriekIsoOfIsOpenImmersion ℓ E n j).hom

/-- The transpose of `etaleReductionLowerShriekSquareOfIsOpenImmersion` under the adjunctions
`Rj_! ⊣ Rj^!` is the canonical `etaleReductionUpperShriekIsoOfIsOpenImmersion`. -/
lemma mateEquiv_etaleReductionLowerShriekSquareOfIsOpenImmersion :
    have := HasCompactification.of_over j
    mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
      (Etale.rightDerivedUpperShriekAdjunction _ j.left)
      (etaleReductionLowerShriekSquareOfIsOpenImmersion ℓ E n j) =
        (etaleReductionUpperShriekIsoOfIsOpenImmersion ℓ E n j).hom :=
  Equiv.apply_symm_apply _ _

/-- The canonical reduction square for `Rj_!` along an open immersion is invertible. This is
checked after restriction to `U` and to the closed complement `i` of `j` (open–closed
conservativity on `X_ét`): after `j^*` it is identified, through the invertible units of the two
adjunctions `Rj_! ⊣ Rj^!`, with `etaleReductionUpperShriekIsoOfIsOpenImmersion`; after `i^*`,
its source and target vanish. -/
instance isIso_etaleReductionLowerShriekSquareOfIsOpenImmersion :
    IsIso (etaleReductionLowerShriekSquareOfIsOpenImmersion ℓ E n j) := by
  have := HasCompactification.of_over j
  let A := ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)
  let adj₁ := PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j
  let adj₂ := Etale.rightDerivedUpperShriekAdjunction (integersModPowCoeff.{u} ℓ E n) j.left
  let δ := etaleReductionUpperShriekIsoOfIsOpenImmersion ℓ E n j
  let θ := etaleReductionLowerShriekSquareOfIsOpenImmersion ℓ E n j
  have hθ : mateEquiv adj₁ adj₂ θ = δ.hom :=
    mateEquiv_etaleReductionLowerShriekSquareOfIsOpenImmersion ℓ E n j
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
  exact NatIso.isIso_of_isIso_app _

/-- Blueprint `lemma-change-coefficients-compact-support` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale
site, for an open immersion `j`. **The canonical isomorphism `Rj_! ⋙ red_X ≅ red_U ⋙ Rj_!`**:
the inverse of `etaleReductionLowerShriekSquareOfIsOpenImmersion`, the transpose of the canonical
`etaleReductionUpperShriekIsoOfIsOpenImmersion`. -/
noncomputable def etaleReductionLowerShriekIsoOfIsOpenImmersion :
    have := HasCompactification.of_over j
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j ⋙ etaleReduction ℓ E n X ≅
      etaleReduction ℓ E n U ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) j.left :=
  (asIso (etaleReductionLowerShriekSquareOfIsOpenImmersion ℓ E n j)).symm

/-- The transpose of `etaleReductionLowerShriekIsoOfIsOpenImmersion` under the adjunctions
`Rj_! ⊣ Rj^!` is the canonical isomorphism `etaleReductionUpperShriekIsoOfIsOpenImmersion`. -/
lemma mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion :
    have := HasCompactification.of_over j
    mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
      (Etale.rightDerivedUpperShriekAdjunction _ j.left)
      (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j).inv) =
        (etaleReductionUpperShriekIsoOfIsOpenImmersion ℓ E n j).hom :=
  mateEquiv_etaleReductionLowerShriekSquareOfIsOpenImmersion ℓ E n j

/-- The transpose of `etaleReductionLowerShriekIsoOfIsOpenImmersion` under `Rj_! ⊣ Rj^!` is an
isomorphism. -/
theorem isIso_mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion :
    have := HasCompactification.of_over j
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
      (Etale.rightDerivedUpperShriekAdjunction _ j.left)
      (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j).inv)) := by
  intro
  rw [mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion]
  infer_instance

end OpenImmersion

/-! ### Composition -/

section Comp

variable {X Y S : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
  {f : X ⟶ Y} {g : Y ⟶ S} {h : X ⟶ S}

/-- The composition isomorphism `Rh_! ≅ Rf_! ⋙ Rg_!` on bounded constructible `𝒪_E`-complexes for
`f ≫ g = h` (`boundedConstructibleLowerShriekComp_padicIntegers` transported along `f ≫ g = h`). -/
noncomputable def boundedConstructibleLowerShriekCompIsoOfEq_padicIntegers (w : f ≫ g = h) :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E h ≅
      PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g :=
  eqToIso (by rw [← w]) ≪≫ boundedConstructibleLowerShriekComp_padicIntegers ℓ E f g

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] in
/-- The underlying morphism of a morphism `h : X ⟶ S` of `k`-schemes is quasi-compact if `X` is
quasi-compact and `S` is separated over `k`. -/
lemma quasiCompact_left_of_over (h : X ⟶ S) : QuasiCompact h.left :=
  have : QuasiCompact (h.left ≫ S.hom) := by rw [Over.w h]; infer_instance
  QuasiCompact.of_comp h.left S.hom

variable [HasCompactification f.left] [HasCompactification g.left] [HasCompactification h.left]

/-- The stacked reduction square for a composite `f ≫ g = h`:
`red_X ⋙ Rh_! ⟶ Rh_! ⋙ red_S`, the vertical paste of the reduction squares `γ_f⁻¹` and `γ_g⁻¹`,
transported along the composition isomorphisms
`Rh_! ≅ Rf_! ⋙ Rg_!` (`boundedConstructibleLowerShriekCompIsoOfEq_padicIntegers` and
`Etale.rightDerivedLowerShriekCompIsoOfEq`). -/
noncomputable def etaleReductionLowerShriekSquareOfComp (w : f ≫ g = h)
    (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)
    (γg : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g ⋙ etaleReduction ℓ E n S ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          g.left) :
    TwoSquare (etaleReduction ℓ E n X) (PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E h)
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) h.left)
      (etaleReduction ℓ E n S) :=
  have := quasiCompact_left_of_over h
  (((TwoSquare.mk _ _ _ _ γf.inv).vComp (TwoSquare.mk _ _ _ _ γg.inv)).whiskerLeft
    (boundedConstructibleLowerShriekCompIsoOfEq_padicIntegers ℓ E w).inv).whiskerRight
    (Etale.rightDerivedLowerShriekCompIsoOfEq (integersModPowCoeff.{u} ℓ E n) f.left g.left h.left
      (by rw [← w]; rfl)).hom

instance isIso_etaleReductionLowerShriekSquareOfComp (w : f ≫ g = h)
    (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)
    (γg : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g ⋙ etaleReduction ℓ E n S ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          g.left) :
    IsIso (etaleReductionLowerShriekSquareOfComp ℓ E n w γf γg) := by
  have : IsIso (TwoSquare.mk _ _ _ _ γf.inv) := inferInstanceAs (IsIso γf.inv)
  have : IsIso (TwoSquare.mk _ _ _ _ γg.inv) := inferInstanceAs (IsIso γg.inv)
  have := quasiCompact_left_of_over h
  have := (TwoSquare.mk _ _ _ _ γf.inv).isIso_vComp (TwoSquare.mk _ _ _ _ γg.inv)
  have := ((TwoSquare.mk _ _ _ _ γf.inv).vComp (TwoSquare.mk _ _ _ _ γg.inv)).isIso_whiskerLeft
    (boundedConstructibleLowerShriekCompIsoOfEq_padicIntegers ℓ E w).inv
  exact (((TwoSquare.mk _ _ _ _ γf.inv).vComp (TwoSquare.mk _ _ _ _ γg.inv)).whiskerLeft
    (boundedConstructibleLowerShriekCompIsoOfEq_padicIntegers ℓ E w).inv).isIso_whiskerRight
    (Etale.rightDerivedLowerShriekCompIsoOfEq (integersModPowCoeff.{u} ℓ E n) f.left g.left h.left
      (by rw [← w]; rfl)).hom

/-- **The canonical reduction comparison for a composite**: for `f ≫ g = h` and comparisons
`γ_f : Rf_! ⋙ red_Y ≅ red_X ⋙ Rf_!` and `γ_g : Rg_! ⋙ red_S ≅ red_Y ⋙ Rg_!`, the comparison
`Rh_! ⋙ red_S ≅ red_X ⋙ Rh_!` inverse to the stacked square
`etaleReductionLowerShriekSquareOfComp`. -/
noncomputable def etaleReductionLowerShriekIsoOfComp (w : f ≫ g = h)
    (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)
    (γg : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g ⋙ etaleReduction ℓ E n S ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          g.left) :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E h ⋙ etaleReduction ℓ E n S ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) h.left :=
  (asIso (etaleReductionLowerShriekSquareOfComp ℓ E n w γf γg)).symm

/-- **Transposes of reduction comparisons compose**: if the transposes of `γ_f` and `γ_g` under
`Rf_! ⊣ Rf^!` and `Rg_! ⊣ Rg^!` are invertible, so is the transpose of
`etaleReductionLowerShriekIsoOfComp` under `Rh_! ⊣ Rh^!`
(`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`). -/
theorem isIso_mateEquiv_etaleReductionLowerShriekIsoOfComp (w : f ≫ g = h)
    (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)
    (γg : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g ⋙ etaleReduction ℓ E n S ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          g.left)
    (hf : IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γf.inv)))
    (hg : IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g)
      (Etale.rightDerivedUpperShriekAdjunction _ g.left) (TwoSquare.mk _ _ _ _ γg.inv))) :
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E h)
      (Etale.rightDerivedUpperShriekAdjunction _ h.left)
      (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIsoOfComp ℓ E n w γf γg).inv)) :=
  have := quasiCompact_left_of_over h
  isIso_mateEquiv_vComp_whiskerLeft_whiskerRight
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g)
    (Etale.rightDerivedUpperShriekAdjunction _ g.left)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E h)
    (Etale.rightDerivedUpperShriekAdjunction _ h.left)
    (boundedConstructibleLowerShriekCompIsoOfEq_padicIntegers ℓ E w)
    (Etale.rightDerivedLowerShriekCompIsoOfEq (integersModPowCoeff.{u} ℓ E n) f.left g.left h.left
      (by rw [← w]; rfl)) _ _

end Comp

/-! ### General morphisms -/

section General

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y}

/-- Blueprint `lemma-change-coefficients-compact-support` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale
site. **The canonical isomorphism `Rf_! ⋙ red_Y ≅ red_X ⋙ Rf_!` attached to a compactification
`X ⟶[i] P ⟶[p] Y` of `f`**: the composite (`etaleReductionLowerShriekIsoOfComp`) of the canonical
comparisons along the open immersion `i` (`etaleReductionLowerShriekIsoOfIsOpenImmersion`) and
along the proper `p` (`etaleReductionLowerShriekIso`). -/
noncomputable def etaleReductionLowerShriekIsoOfCompactification (c : Compactification f.left) :
    have := HasCompactification.of_over f
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left :=
  have := HasCompactification.of_over f
  have := HasCompactification.of_over c.overI
  have := HasCompactification.of_over c.overG
  etaleReductionLowerShriekIsoOfComp ℓ E n c.overI_overG
    (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n c.overI)
    (etaleReductionLowerShriekIso ℓ E n c.overG)

/-- The transpose of `etaleReductionLowerShriekIsoOfCompactification` under `Rf_! ⊣ Rf^!` is an
isomorphism: transposes compose (`isIso_mateEquiv_etaleReductionLowerShriekIsoOfComp`), and the
transposes along the open immersion and the proper morphism are invertible
(`isIso_mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion`,
`isIso_mateEquiv_etaleReductionLowerShriekIso`). -/
theorem isIso_mateEquiv_etaleReductionLowerShriekIsoOfCompactification
    (c : Compactification f.left) :
    have := HasCompactification.of_over f
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left)
      (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIsoOfCompactification ℓ E n c).inv)) :=
  have := HasCompactification.of_over f
  have := HasCompactification.of_over c.overI
  have := HasCompactification.of_over c.overG
  isIso_mateEquiv_etaleReductionLowerShriekIsoOfComp ℓ E n c.overI_overG _ _
    (isIso_mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n c.overI)
    (isIso_mateEquiv_etaleReductionLowerShriekIso ℓ E n c.overG)

/-- Every morphism of separated `k`-schemes of finite type has a reduction comparison for `Rf_!`
and `Rf^!`, witnessed by the canonical `etaleReductionLowerShriekIsoOfCompactification` of any
compactification of `f`. -/
theorem hasEtaleReductionLowerShriekIso_of_compactification (c : Compactification f.left) :
    HasEtaleReductionLowerShriekIso ℓ E n f :=
  ⟨_, isIso_mateEquiv_etaleReductionLowerShriekIsoOfCompactification ℓ E n c⟩

variable (f) in
/-- Blueprint `lemma-change-coefficients-exceptional-inverse-image` for the coefficient map
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site. **Reduction modulo `ℓⁿ` commutes with `Rf^!`,
canonically**: `Rf^! ⋙ red_X ≅ red_Y ⋙ Rf^!` for every morphism `f` of separated `k`-schemes of
finite type. It is the transpose under `Rf_! ⊣ Rf^!` of the canonical comparison
`etaleReductionLowerShriekIsoOfCompactification` for the chosen compactification
`compactificationOverField f`, invertible by
`isIso_mateEquiv_etaleReductionLowerShriekIsoOfCompactification`. -/
noncomputable def etaleReductionUpperShriekIso :
    have := HasCompactification.of_over f
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f ⋙ etaleReduction ℓ E n X ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) f.left :=
  have := HasCompactification.of_over f
  have := isIso_mateEquiv_etaleReductionLowerShriekIsoOfCompactification ℓ E n
    (compactificationOverField f)
  asIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (TwoSquare.mk _ _ _ _
      (etaleReductionLowerShriekIsoOfCompactification ℓ E n (compactificationOverField f)).inv))

variable (f) in
lemma etaleReductionUpperShriekIso_hom :
    have := HasCompactification.of_over f
    (etaleReductionUpperShriekIso ℓ E n f).hom =
      mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
        (Etale.rightDerivedUpperShriekAdjunction _ f.left)
        (TwoSquare.mk _ _ _ _
          (etaleReductionLowerShriekIsoOfCompactification ℓ E n
            (compactificationOverField f)).inv) :=
  rfl

end General

end AlgebraicGeometry.ProEtale.CondensedRing
