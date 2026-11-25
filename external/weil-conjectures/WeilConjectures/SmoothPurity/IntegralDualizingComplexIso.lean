/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.FiniteEndomorphisms
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftIsomorphisms
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionConservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriekCanonical
public import WeilConjectures.TateTwist.IntegralReduction

/-!
# The integral relative dualizing complex of a smooth morphism is a Tate twist

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`, and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ`. Then
`Rf^! 𝒪_{E,Y} ≅ 𝒪_{E,X}(d)[2d]` in `Dᵇc(X)⟦𝒪_E⟧`
(`ProEtale.CondensedRing.nonempty_iso_integralTateTwist_upperShriekUnit`).

The isomorphism is *not* constructed canonically: modulo `ℓⁿ` both sides are isomorphic by finite
smooth purity (`Etale.nonempty_iso_dualizingComplex_twistShift`), read through the canonical
reduction comparisons (`etaleReductionUpperShriekIso`, `etaleReductionIntegralTateTwistIso`) and
the fully faithful étale reading; there are finitely many morphisms between the reductions, so a
compatible family of isomorphisms exists by König's lemma and lifts
(`ProEtale.exists_forall_isIso_derivedReduction_map`); the lift is an isomorphism by derived
Nakayama (`isIso_of_isIso_etaleReduction_map`). It is used to prove that the relative dualizing
complex with `ℚ̄_ℓ`-coefficients is dualizable.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section Reading

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The étale reading commutes with the shifts. -/
noncomputable instance commShift_finiteEtaleReading : (finiteEtaleReading ℓ E n X).CommShift ℤ :=
  inferInstanceAs (((boundedConstructible _).ι ⋙
    (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
      (ν_*(X.left)[ModuleCat.{u + 1}
        (integersModPowCoeff.{u} ℓ E n)]).rightDerivedFunctor).CommShift ℤ)

variable {ℓ E n X}

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- Isomorphisms of étale readings, up to a shift, come from isomorphisms of bounded
constructible `𝒪_E ⧸ ℓⁿ`-complexes. -/
lemma nonempty_shift_iso_of_finiteEtaleReading
    {C C' : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧} (m : ℤ)
    (e : (shiftFunctor _ m).obj ((finiteEtaleReading ℓ E n X).obj C) ≅
      (finiteEtaleReading ℓ E n X).obj C') :
    Nonempty (C⟦m⟧ ≅ C') :=
  ⟨(finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E n X)).preimageIso
    (((finiteEtaleReading ℓ E n X).commShiftIso m).app C ≪≫ e)⟩

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- Morphisms between shifted bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes are finite as soon as
those between their étale readings are. -/
lemma finite_shift_hom_of_finiteEtaleReading
    {C C' : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧} (m : ℤ)
    (h : Finite ((shiftFunctor _ m).obj ((finiteEtaleReading ℓ E n X).obj C) ⟶
      (finiteEtaleReading ℓ E n X).obj C')) :
    Finite (C⟦m⟧ ⟶ C') :=
  @Finite.of_equiv _ _ h
    ((finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E n X)).homEquiv.trans
    ((((finiteEtaleReading ℓ E n X).commShiftIso m).app C).homCongr (Iso.refl _))).symm

end Reading

section Purity

variable {ℓ E} [NeZero (ℓ : k)] {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- Modulo `ℓⁿ`, read on the étale site, the shifted integral Tate twist and the integral relative
dualizing complex of `f` are isomorphic, by finite smooth purity. -/
lemma nonempty_shift_etaleReduction_integralTateTwist_iso_upperShriek :
    Nonempty ((shiftFunctor _ (2 * d : ℤ)).obj ((finiteEtaleReading ℓ E n X).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj
          (integralTateTwistBoundedConstructible ℓ E X.hom d))) ≅
      (finiteEtaleReading ℓ E n X).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj (𝟙_ _)))) := by
  have := HasCompactification.of_over f
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E n) X.left :=
    HasInvertibleExponent.of_hom X.hom
  obtain ⟨θ⟩ := Etale.nonempty_iso_dualizingComplex_twistShift (integersModPowCoeff.{u} ℓ E n)
    (d := d) f.left Y.hom
  exact ⟨(shiftFunctor _ (2 * d : ℤ)).mapIso
      (etaleReductionIntegralTateTwistIso ℓ E n X d ≪≫ (λ_ _).symm) ≪≫ θ.symm ≪≫
    ((etaleReductionUpperShriekIso ℓ E n f).app (𝟙_ _) ≪≫
      (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) f.left).mapIso
        (etaleReductionUnitIso ℓ E n Y)).symm⟩

/-- **The integral relative dualizing complex of a smooth morphism is a shifted Tate twist**:
`Rf^! 𝒪_{E,Y} ≅ 𝒪_{E,X}(d)[2d]` for `f` smooth of pure relative dimension `d` (the source is
noetherian, so it has finitely many connected components and the étale Tate twists `Λ_X(d)`,
`Λ = 𝒪_E ⧸ ℓⁿ`, have finitely many endomorphisms, `Etale.finite_endomorphisms_tateObject`). The
isomorphism is not canonical (König's lemma). -/
theorem nonempty_iso_integralTateTwist_upperShriekUnit :
    Nonempty ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E X.hom d) ≅
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj (𝟙_ _)) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have hfin (n : ℕ) : Finite (Etale.tateObject (integersModPowCoeff.{u} ℓ E (n + 1)) X.left d ⟶
      Etale.tateObject (integersModPowCoeff.{u} ℓ E (n + 1)) X.left d) := by
    have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E (n + 1)) X.left :=
      HasInvertibleExponent.of_hom X.hom
    exact Etale.finite_endomorphisms_tateObject _ _ d
  let T := integralTateTwistBoundedConstructible ℓ E X.hom d
  let W := (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj (𝟙_ _)
  let ι := (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).ι
  let red (n : ℕ) := boundedConstructibleIntegersModPowReduction X.left ℓ E n
  let ιn (n : ℕ) := (boundedConstructible
    (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X.left)).ι
  let Lred (n : ℕ) := (Mod.extendScalars (integersModPowReduction X.left ℓ E n)).leftDerivedFunctor
  -- the reductions of `T⟦2d⟧` and `W` in the ambient derived categories
  let A (n : ℕ) : (Lred n).obj ((shiftFunctor _ (2 * d : ℤ)).obj (ι.obj T)) ≅
      (ιn n).obj ((shiftFunctor _ (2 * d : ℤ)).obj ((red n).obj T)) :=
    ((Lred n).commShiftIso (2 * d : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 * d : ℤ)).mapIso
        ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app T).symm ≪≫
      (((ιn n).commShiftIso (2 * d : ℤ)).app _).symm
  let B (n : ℕ) : (Lred n).obj (ι.obj W) ≅ (ιn n).obj ((red n).obj W) :=
    ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app W).symm
  have hne (n : ℕ) : Nonempty ((Lred (n + 1)).obj ((shiftFunctor _ (2 * d : ℤ)).obj (ι.obj T)) ≅
      (Lred (n + 1)).obj (ι.obj W)) := by
    obtain ⟨e⟩ := nonempty_shift_etaleReduction_integralTateTwist_iso_upperShriek (ℓ := ℓ)
      (E := E) (n + 1) f d
    obtain ⟨e'⟩ := nonempty_shift_iso_of_finiteEtaleReading (2 * d : ℤ) e
    exact ⟨A (n + 1) ≪≫ (ιn (n + 1)).mapIso e' ≪≫ (B (n + 1)).symm⟩
  have hfin' (n : ℕ) : Finite ((Lred (n + 1)).obj ((shiftFunctor _ (2 * d : ℤ)).obj (ι.obj T)) ⟶
      (Lred (n + 1)).obj (ι.obj W)) := by
    obtain ⟨e⟩ := nonempty_shift_etaleReduction_integralTateTwist_iso_upperShriek (ℓ := ℓ)
      (E := E) (n + 1) f d
    have h₁ : Finite ((shiftFunctor _ (2 * d : ℤ)).obj ((finiteEtaleReading ℓ E (n + 1) X).obj
        ((red (n + 1)).obj T)) ⟶ (finiteEtaleReading ℓ E (n + 1) X).obj ((red (n + 1)).obj W)) :=
      let eT := (shiftFunctor _ (2 * d : ℤ)).mapIso
        (etaleReductionIntegralTateTwistIso ℓ E (n + 1) X d).symm
      @Finite.of_equiv _ _ (hfin n) ((Functor.FullyFaithful.ofFullyFaithful
          (shiftFunctor _ (2 * d : ℤ))).homEquiv.trans (eT.homCongr (eT ≪≫ e)))
    have h₂ := finite_shift_hom_of_finiteEtaleReading (2 * d : ℤ) h₁
    exact @Finite.of_equiv _ _ h₂ ((ObjectProperty.fullyFaithfulι _).homEquiv.trans
      ((A (n + 1)).homCongr (B (n + 1))).symm)
  obtain ⟨φ, hφ⟩ := ProEtale.exists_forall_isIso_derivedReduction_map
    (derivedCompleteIntegers_of_boundedConstructible W.property) hfin' hne
  let g : (shiftFunctor _ (2 * d : ℤ)).obj T ⟶ W :=
    (ObjectProperty.fullyFaithfulι _).preimage ((ι.commShiftIso (2 * d : ℤ)).hom.app T ≫ φ)
  have hg : IsIso ((Lred 1).map (ι.map g)) := by
    have hι : ι.map g = (ι.commShiftIso (2 * d : ℤ)).hom.app T ≫ φ :=
      (ObjectProperty.fullyFaithfulι _).map_preimage _
    have := hφ 0
    rw [hι, Functor.map_comp]
    infer_instance
  have hg' : IsIso ((red 1).map g) := by
    have := hg
    have h :=
      (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E 1).hom.naturality g
    have : IsIso ((ιn 1).map ((red 1).map g)) := by
      have : IsIso ((ιn 1).map ((red 1).map g) ≫
          (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E 1).hom.app W) := by
        have h' : (ιn 1).map ((red 1).map g) ≫
            (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E 1).hom.app W =
            (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E 1).hom.app _ ≫
              (Lred 1).map (ι.map g) := h
        rw [h']
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E 1).hom.app W)
    exact isIso_of_reflects_iso _ (ιn 1)
  have : IsIso g := isIso_of_isIso_etaleReduction_map ℓ E one_ne_zero g
    (inferInstanceAs (IsIso ((finiteEtaleReading ℓ E 1 X).map ((red 1).map g))))
  exact ⟨asIso g⟩

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing
