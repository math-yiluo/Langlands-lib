/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProduct
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekMate

/-!
# Reduction modulo `ℓⁿ`, `Rf_!` and `Rf^!`: stability under composition

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). Say that a morphism `f : Z ⟶ Y` *has a
reduction comparison* if there is an isomorphism `γ : Rf_! ⋙ red_Y ≅ red_Z ⋙ Rf_!` whose
transpose `Rf^! ⋙ red_Z ⟶ red_Y ⋙ Rf^!` under the adjunctions `Rf_! ⊣ Rf^!` is an isomorphism
(`ProEtale.CondensedRing.HasEtaleReductionLowerShriekIso`). Closed immersions have one
(`ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso_of_isClosedImmersion`).

This file shows that the property is stable under composition
(`ProEtale.CondensedRing.HasEtaleReductionLowerShriekIso.comp`): with the composition
isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on both sides, the stacked square of `γ_f` and `γ_g`
has invertible transpose (`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`).
This is the composition step of blueprint `lemma-change-coefficients-exceptional-inverse-image`
("compatibility with composition"), in the weak form of `exists_etaleReductionLowerShriekIso` (no
identification of `γ` with the canonical comparison). Every proper morphism is a closed immersion
followed by a projection `P ×_k Y ⟶ Y` (`exists_isClosedImmersion_comp_overProdSnd`).
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

/-- A morphism `f : Z ⟶ Y` *has a reduction comparison for `Rf_!` and `Rf^!`*: there is an
isomorphism `γ : Rf_! ⋙ red_Y ≅ red_Z ⋙ Rf_!` whose transpose under `Rf_! ⊣ Rf^!` is an
isomorphism. This is the conclusion of `exists_etaleReductionLowerShriekIso`. -/
def HasEtaleReductionLowerShriekIso {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : Z ⟶ Y) : Prop :=
  have := HasCompactification.of_over f
  ∃ γ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
      etaleReduction ℓ E n Y ≅
    etaleReduction ℓ E n Z ⋙
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left,
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γ.inv))

variable {X Y S : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- Closed immersions have a reduction comparison for `Rf_!` and `Rf^!`
(`exists_etaleReductionLowerShriekIso_of_isClosedImmersion`). -/
theorem hasEtaleReductionLowerShriekIso_of_isClosedImmersion (f : X ⟶ Y)
    [IsClosedImmersion f.left] : HasEtaleReductionLowerShriekIso ℓ E n f :=
  exists_etaleReductionLowerShriekIso_of_isClosedImmersion ℓ E n f

/-- **Reduction comparisons compose**: if `f` and `g` have a reduction comparison for the
lower and upper shrieks, so does `f ≫ g`. The comparison for `f ≫ g` is the stacked square of
those for `f` and `g`, transported along the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (`boundedConstructibleLowerShriekComp_padicIntegers` and
`Etale.nonempty_iso_rightDerivedLowerShriek_comp`); its transpose is invertible by
`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`. -/
theorem HasEtaleReductionLowerShriekIso.comp {f : X ⟶ Y} {g : Y ⟶ S}
    (hf : HasEtaleReductionLowerShriekIso ℓ E n f)
    (hg : HasEtaleReductionLowerShriekIso ℓ E n g) :
    HasEtaleReductionLowerShriekIso ℓ E n (f ≫ g) := by
  have := HasCompactification.of_over f
  have := HasCompactification.of_over g
  have := HasCompactification.of_over (f ≫ g)
  obtain ⟨γf, hγf⟩ := hf
  obtain ⟨γg, hγg⟩ := hg
  obtain ⟨e'⟩ := Etale.nonempty_iso_rightDerivedLowerShriek_comp
    (integersModPowCoeff.{u} ℓ E n) f.left g.left
  let sqf := TwoSquare.mk _ _ _ _ γf.inv
  let sqg := TwoSquare.mk _ _ _ _ γg.inv
  let c := boundedConstructibleLowerShriekComp_padicIntegers ℓ E f g
  let sq := ((sqf.vComp sqg).whiskerLeft c.inv).whiskerRight e'.hom
  have : IsIso sq := by
    have : IsIso sqf := inferInstanceAs (IsIso γf.inv)
    have : IsIso sqg := inferInstanceAs (IsIso γg.inv)
    have := sqf.isIso_vComp sqg
    have := (sqf.vComp sqg).isIso_whiskerLeft c.inv
    exact ((sqf.vComp sqg).whiskerLeft c.inv).isIso_whiskerRight e'.hom
  refine ⟨(asIso sq).symm, ?_⟩
  exact isIso_mateEquiv_vComp_whiskerLeft_whiskerRight
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g)
    (Etale.rightDerivedUpperShriekAdjunction _ g.left)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction _ (f ≫ g).left)
    (boundedConstructibleLowerShriekComp_padicIntegers ℓ E f g) e' _ _

/-! ### Factorization of proper morphisms -/

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
/-- **Graph factorization of a proper morphism**: a proper `f : X ⟶ Y` of separated `k`-schemes of
finite type is a closed immersion `X ⟶ P ×_k Y` followed by the second projection, for some
proper `k`-scheme `P`. Take a compactification `X ⟶[j] P ⟶ Spec k` of `X` (Nagata) and the
graph `(j, f)`: it is proper, its composite with the separated projection to `Y` being `f`, and
a monomorphism, its composite with the projection to `P` being the open immersion `j`. -/
theorem exists_isClosedImmersion_comp_overProdSnd (f : X ⟶ Y) [IsProper f.left] :
    ∃ (P : Over (Spec (.of k))) (_ : IsProper P.hom) (i : X ⟶ overProd P Y),
      IsClosedImmersion i.left ∧ i ≫ overProdSnd P Y = f := by
  let c := HasCompactification.compactification X.hom
  have := c.isProper
  have := c.isOpenImmersion
  have hc : c.i ≫ c.g = X.hom := c.comm.symm
  let i : X ⟶ overProd (Over.mk c.g) Y :=
    Over.homMk (pullback.lift c.i f.left (by simp [hc]))
      (by dsimp only [overProd, Over.mk_hom]; rw [pullback.lift_snd_assoc, Over.w])
  have hi₁ : i.left ≫ pullback.fst c.g Y.hom = c.i := by simp [i]
  have hi₂ : i.left ≫ pullback.snd c.g Y.hom = f.left := by simp [i]
  refine ⟨Over.mk c.g, c.isProper, i, ?_, ?_⟩
  · rw [IsClosedImmersion.iff_isProper_and_mono]
    have : IsProper (i.left ≫ pullback.snd c.g Y.hom) := by
      rw [hi₂]
      infer_instance
    refine ⟨IsProper.of_comp i.left (pullback.snd c.g Y.hom), ?_⟩
    have : Mono (i.left ≫ pullback.fst c.g Y.hom) := by
      rw [hi₁]
      infer_instance
    exact mono_of_mono _ (pullback.fst c.g Y.hom)
  · ext1
    simpa [overProdSnd] using hi₂

end AlgebraicGeometry.ProEtale.CondensedRing
