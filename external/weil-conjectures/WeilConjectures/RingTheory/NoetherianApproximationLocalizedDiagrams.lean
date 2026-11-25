/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import WeilConjectures.RingTheory.LocalizedApproximationCocones
import WeilConjectures.RingTheory.LocalizedApproximationTransitions
import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Defs

/-! # Localized diagrams of a supplied Noetherian approximation

Source: Stacks Project, Algebra, Tags 00RC, 00R1 and 00R6.
(blueprint: lem-weil-pbc-noetherian-approximation-localized-diagrams)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

-- Preserve the named nondependent forall binder in the existing signature.
set_option linter.unusedVariables false in
/-- Localization of a supplied Noetherian approximation produces the local diagrams used
in the stage-flatness criterion. No flatness of the limit is assumed, and no flat stage
is selected.

Source: Stacks Project, Algebra, Tag 00RC (`theorem-openness-flatness`), first
reduction paragraph, and Tag 00QX (`lemma-limit-module-essentially-finite-presentation`).
(blueprint: lem-weil-pbc-noetherian-approximation-localized-diagrams)

Proof:
1. Contract q to every top stage through the supplied cocone followed by ULift.down,
   and contract it further through the stage map to the base stage. Naturality and
   the commuting square show that every transition contracts the later prime to the
   earlier one. Take the prime localizations of these rings and the localizations of
   the stage modules. On fractions the transitions send x/s to f(x)/f(s); the
   contractions ensure that denominators remain invertible. Semilinearity makes these
   maps compatible with the localized scalar actions.
2. Apply filteredColimitLocalizationAtPrime to both ring diagrams, transporting the
   supplied colimits through the canonical lift equivalences. For modules lift a
   numerator and a denominator to a common stage. Equality of fractions is witnessed
   by a multiplier outside q; lift that multiplier, and use eventual equality in the
   original group colimit to descend its zero relation to a later stage. This proves
   that the localized module cocone is a colimit with limit M_q. Its scalar action is
   compatible on numerator/denominator representatives. The ring comparison induces
   the indicated map between the chosen categorical colimits.
3. The rings before localization are Noetherian by hypothesis. Localizations remain
   Noetherian, prime localizations are local, and the localized stage modules remain finite.
   All ring transition maps and the base-to-top maps are local, by the contraction identities.
4. Localize the supplied ring tensor isomorphism. First localize the two factors at
   the contracted primes, and then localize at the prime pulled back from the later
   top ring. The localization universal property gives the displayed pure-tensor
   formula and the IsLocalization witness. Tensor-localization compatibility applied
   to the supplied module tensor isomorphism gives the localized module base-change
   equivalence with its pure-tensor formula.
5. Identify the base colimit with R_p and the module colimit with M_q. Transport of
   the R-action along the induced map R → R_p gives the limit module linear
   equivalence in the statement. At each stage use the canonical map A_i → (A_i)_{p_i}
   and identify the module with (D_i)_{q_i} as an A_i-module. The localization universal
   property gives both IsLocalization witnesses. This construction does not use
   flatness, and neither asserts nor chooses a flat stage.
-/
theorem exists_localized_noetherian_approximation
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    let R' := ULift.{max u v w} R
    let S' := ULift.{max u v w} S
    let M' := ULift.{max u v w} M
    letI : Algebra R' S' := ULift.algebra' R S'
    ∀
    {Λ : Type (max u v w)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A B : Λ ⥤ CommRingCat.{max u v w}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R'))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S'))
      (D : Λ ⥤ AddCommGrpCat.{max u v w})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M'))
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hmodel :
      -- (1) the three colimits, compatible with `R' → S'` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R') π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S') κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M') ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R' S')) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) x) ∧
      -- (2) finiteness of the stages
      (∀ i, IsNoetherianRing (A.obj i)) ∧
      (∀ i, IsNoetherianRing (B.obj i)) ∧
      (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
      -- (3) transition base changes
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (η.app i).hom.toAlgebra
        letI := (A.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
          ∀ (x : B.obj i) (y : A.obj j),
            e (x ⊗ₜ[A.obj i] y) = (B.map (homOfLE h)).hom x * (η.app j).hom y) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (B.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
          ∀ (y : B.obj j) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x))
    (q : PrimeSpectrum S),
    ∃ (Aₗ Bₗ : Λ ⥤ CommRingCat.{max u v w})
      (Dₗ : Λ ⥤ AddCommGrpCat.{max u v w}),
    ∃ hcA : HasColimit Aₗ, letI := hcA
    ∃ hcB : HasColimit Bₗ, letI := hcB
    ∃ hcD : HasColimit Dₗ, letI := hcD
    ∃ hlocalA : ∀ i, IsLocalRing (Aₗ.obj i), letI := hlocalA
    ∃ hlocalB : ∀ i, IsLocalRing (Bₗ.obj i), letI := hlocalB
    ∃ hnoethA : ∀ i, IsNoetherianRing (Aₗ.obj i), letI := hnoethA
    ∃ hnoethB : ∀ i, IsNoetherianRing (Bₗ.obj i), letI := hnoethB
    ∃ hmodule : ∀ i, Module (Bₗ.obj i) (Dₗ.obj i), letI := hmodule
    ∃ hfinite : ∀ i, Module.Finite (Bₗ.obj i) (Dₗ.obj i), letI := hfinite
    ∃ hmoduleLimit : Module (colimit Bₗ : CommRingCat.{max u v w})
        (colimit Dₗ : AddCommGrpCat.{max u v w}), letI := hmoduleLimit
    ∃ (φ : ∀ i, Aₗ.obj i →+* Bₗ.obj i)
      (ψ : (colimit Aₗ : CommRingCat.{max u v w}) →+*
        (colimit Bₗ : CommRingCat.{max u v w})),
      (∀ i, IsLocalHom (φ i)) ∧
      (∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (Aₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (Bₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j),
        (Bₗ.map f).hom.comp (φ i) = (φ j).comp (Aₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j) (b : Bₗ.obj i) (x : Dₗ.obj i),
        (Dₗ.map f).hom (b • x) = (Bₗ.map f).hom b • (Dₗ.map f).hom x) ∧
      (∀ i, ψ.comp (colimit.ι Aₗ i).hom = (colimit.ι Bₗ i).hom.comp (φ i)) ∧
      (∀ (i : Λ) (b : Bₗ.obj i) (x : Dₗ.obj i),
        (colimit.ι Dₗ i).hom (b • x) =
          (colimit.ι Bₗ i).hom b • (colimit.ι Dₗ i).hom x) ∧
      (∀ (i j : Λ) (f : i ⟶ j),
        letI := (φ i).toAlgebra
        letI := (Aₗ.map f).hom.toAlgebra
        ∃ (t : Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j →+* Bₗ.obj j)
          (W : Submonoid (Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j)),
          (∀ (b : Bₗ.obj i) (a : Aₗ.obj j),
            t (b ⊗ₜ[Aₗ.obj i] a) = (Bₗ.map f).hom b * φ j a) ∧
          (letI := t.toAlgebra; IsLocalization W (Bₗ.obj j))) ∧
      (∀ (i j : Λ) (f : i ⟶ j),
        letI := (Bₗ.map f).hom.toAlgebra
        ∃ e : Bₗ.obj j ⊗[Bₗ.obj i] Dₗ.obj i ≃ₗ[Bₗ.obj j] Dₗ.obj j,
          ∀ (b : Bₗ.obj j) (x : Dₗ.obj i),
            e (b ⊗ₜ[Bₗ.obj i] x) = b • (Dₗ.map f).hom x) ∧
      (∃ ρ : R →+* (colimit Aₗ : CommRingCat.{max u v w}),
        letI := ρ.toAlgebra
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ψ
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ρ
        IsLocalization (q.asIdeal.comap (algebraMap R S)).primeCompl
          (colimit Aₗ : CommRingCat.{max u v w}) ∧
        Nonempty (LocalizedModule q.asIdeal.primeCompl M ≃ₗ[R]
          (colimit Dₗ : AddCommGrpCat.{max u v w}))) ∧
      (∀ i, ∃ ρ : A.obj i →+* Aₗ.obj i,
        letI := (φ i).toAlgebra
        letI := Module.compHom (Dₗ.obj i) (φ i)
        letI := ρ.toAlgebra
        letI := Module.compHom (Dₗ.obj i) ρ
        letI : Algebra (A.obj i) (B.obj i) := (η.app i).hom.toAlgebra
        letI : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
        letI : IsScalarTower (A.obj i) (B.obj i) (D.obj i) :=
          IsScalarTower.of_compHom _ _ _
        IsLocalization
          (q.asIdeal.comap ((ULift.ringEquiv.toRingHom.comp (κ.app i).hom).comp
            (η.app i).hom)).primeCompl (Aₗ.obj i) ∧
        Nonempty (LocalizedModule
          (q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)).primeCompl
          (D.obj i) ≃ₗ[A.obj i] Dₗ.obj i)) := by
  classical
  dsimp only
  intro Λ _ _ _ A B η π κ D ν _ hmodel q
  rcases hmodel with ⟨hcR, hcS, hcM, hcompat, hD, hν, hnoethA, hnoethB,
    hfiniteOriginal, htB, htD⟩
  obtain ⟨Aₗ, Bₗ, Dₗ, hcA, hcB, hcD, hlocalA, hlocalB, hmodule,
    hmoduleLimit, φ, ψ, hφ, hA, hB, hcomm,
    hscalar, hψ, hlimitScalar, hlimit, hstage,
    ρA, ρB, ζ, hρA, hρB, hη, hρAnat, hρBnat, hζ, hζscalar, hℓ⟩ :=
    exists_localized_approximation_cocones R S M A B η π κ D ν
      ⟨hcR, hcS, hcM, hcompat, hD, hν⟩ q
  let := hcA
  let := hcB
  let := hcD
  let := hlocalA
  let := hlocalB
  let := hmodule
  let := hmoduleLimit
  let qᵢ : ∀ i, Ideal (B.obj i) := fun i ↦
    q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)
  have hprime : ∀ i, (qᵢ i).IsPrime := fun i ↦ Ideal.IsPrime.comap _
  have hq (i j : Λ) (f : i ⟶ j) : Ideal.comap (B.map f).hom (qᵢ j) = qᵢ i := by
    dsimp only [qᵢ]
    rw [Ideal.comap_comap]
    congr 1
    rw [RingHom.comp_assoc]
    congr 1
    change (B.map f ≫ κ.app j).hom = (κ.app i).hom
    rw [κ.naturality]
    rfl
  have hρA' : ∀ i, letI := (ρA i).toAlgebra
      IsLocalization ((qᵢ i).comap (η.app i).hom).primeCompl (Aₗ.obj i) := by
    intro i
    simpa only [qᵢ, Ideal.comap_comap] using hρA i
  have hnoetherianA : ∀ i, IsNoetherianRing (Aₗ.obj i) := by
    intro i
    let := (ρA i).toAlgebra
    let := hρA' i
    exact IsLocalization.isNoetherianRing
      ((qᵢ i).comap (η.app i).hom).primeCompl (Aₗ.obj i) (hnoethA i)
  have hnoetherianB : ∀ i, IsNoetherianRing (Bₗ.obj i) := by
    intro i
    let := (ρB i).toAlgebra
    let := hρB i
    exact IsLocalization.isNoetherianRing (qᵢ i).primeCompl (Bₗ.obj i) (hnoethB i)
  have hfinite : ∀ i, Module.Finite (Bₗ.obj i) (Dₗ.obj i) := by
    intro i
    let := (ρB i).toAlgebra
    let := Module.compHom (Dₗ.obj i) (ρB i)
    have : IsScalarTower (B.obj i) (Bₗ.obj i) (Dₗ.obj i) :=
      IsScalarTower.of_compHom _ _ _
    let := hρB i
    obtain ⟨ℓ, _, hloc⟩ := hℓ i
    let := hloc
    let := hfiniteOriginal i
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B.obj i) (M := D.obj i)
    refine ⟨Submodule.fg_def.mpr ?_⟩
    exact ⟨ℓ '' (s : Set (D.obj i)), s.finite_toSet.image ℓ,
      span_eq_top_of_isLocalizedModule (Bₗ.obj i) (qᵢ i).primeCompl ℓ hs⟩
  let := hnoetherianA
  let := hnoetherianB
  let := hfinite
  obtain ⟨htransitionRing, htransitionModule⟩ :=
    localized_approximation_transition_base_change A B η D qᵢ hq Aₗ Bₗ Dₗ φ
      ρA ρB ζ hρA' hρB hη hρAnat hρBnat hζ hscalar hℓ htB htD
  exact ⟨Aₗ, Bₗ, Dₗ, hcA, hcB, hcD, hlocalA, hlocalB, hnoetherianA,
    hnoetherianB, hmodule, hfinite, hmoduleLimit, φ, ψ, hφ, hA, hB, hcomm,
    hscalar, hψ, hlimitScalar, htransitionRing, htransitionModule, hlimit, hstage⟩


end Algebra
