/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.SixFunctors.Sf.SfClopenLissePartition
import WeilConjectures.SixFunctors.Sf.SfClopenCoverGeometry
import WeilConjectures.SixFunctors.Sf.SfWeaklyContractibleProjective
import WeilConjectures.SixFunctors.Sf.SfClopenCoefficientComparison
import WeilConjectures.SixFunctors.Sf.SfClopenDerivedCompatibility

/-! # Simultaneous clopen lisse trivialization and complete restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem residue_ideal_maximal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  simpa only [Padic.coefficientExtensionIdeal, pow_one, hgen] using hm

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A common finite clopen partition trivializes finitely many finite lisse residue sheaves,
and ordinary restriction preserves their completed coefficient and derived quotient data.

Source: Stacks Project, proetale.tex, Tags 09C3 and 098F; sites-cohomology.tex, Tag 0946;
derived.tex, Tags 015F and 08TC (blueprint: lem-sf-clopen-lisse-complete-localization).

Proof: the coefficient DVR supplies the residue field. Form the common finite
clopen free partition by sf_clopen_lisse_partition. The cover-geometry theorem
passes terminal epimorphism-surjectivity to each component, in every coefficient
universe containing the site. Its module version gives exact evaluation and finite
free projectivity. Construct the normalized finite and completed coefficient datum
by sf_clopen_coefficient_comparison, and apply sf_clopen_derived_compatibility to
its clopen component. Assemble these conclusions with the free local models. -/
theorem sf_clopen_lisse_complete_localization
    (T : Scheme.{t}) (hT : IsAffine T)
    (hweak : ∀ (F G : Sheaf (Scheme.ProEt.topology T) (Type (max u (t + 1))))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 T)))))
    (J : Type v) [Finite J]
    (F : J → scalarReductionTarget l E T 0)
    (hF : ∀ j : J, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses T
      (Padic.coefficientExtensionRing l E 1)
      (fun N ↦ Module.Finite (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1)) N)
      (F j)) :
    ∃ (n : ℕ) (U : Fin n → T.Opens),
      (⨆ i, U i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      ∀ i : Fin n,
        IsClosed (U i : Set T) ∧ IsCompact (U i : Set T) ∧
        (∀ (A B : Sheaf (Scheme.ProEt.topology (U i).toScheme)
            (Type (max u (t + 1)))) (f : A ⟶ B), Epi f →
          Function.Surjective
            (f.hom.app (op (Scheme.ProEt.mk (𝟙 (U i).toScheme))))) ∧
        (∀ j : J, ∃ r : ℕ,
          Nonempty ((F j).over (Scheme.ProEt.mk (U i).ι) ≅
            proEtaleConstantModuleSheafOverOfUniverses T
              (Padic.coefficientExtensionRing l E 1) (Scheme.ProEt.mk (U i).ι)
              (ModuleCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1))
                (Fin r → ULift.{t + 1} (Padic.coefficientExtensionRing l E 1))))) ∧
        (∀ C : Sheaf (Scheme.ProEt.topology (U i).toScheme)
            CommRingCat.{max w (t + 1)},
          (SheafOfModules.evaluation.{max w (t + 1)}
            ((sheafCompose _ (forget₂ CommRingCat.{max w (t + 1)}
              RingCat.{max w (t + 1)})).obj C)
            (op (Scheme.ProEt.mk (𝟙 (U i).toScheme)))).PreservesHomology ∧
          ∀ r : ℕ, Projective (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{max w (t + 1)}
              RingCat.{max w (t + 1)})).obj C))) ∧
        ∃ d : SfClopenCoefficientRestriction l E T (U i),
          Nonempty (SfClopenCompleteRestriction d)  := by
  let := hT
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := residue_ideal_maximal l E
  let : Field (Padic.coefficientExtensionRing l E 1) :=
    Ideal.Quotient.field (Padic.coefficientExtensionIdeal l E 1)
  obtain ⟨n, U, hcover, hdisjoint, hlocal⟩ :=
    sf_clopen_lisse_partition T hweak (Padic.coefficientExtensionRing l E 1) J F hF
  refine ⟨n, U, hcover, hdisjoint, fun i ↦ ?_⟩
  obtain ⟨hc, hqc, hfree⟩ := hlocal i
  refine ⟨hc, hqc, (sf_clopen_cover_geometry T hweak).2 (U i) hc, hfree, ?_, ?_⟩
  · intro C
    exact sf_weakly_contractible_projective (U i).toScheme
      ((sf_clopen_cover_geometry T hweak).2 (U i) hc) C
  · obtain ⟨d⟩ := sf_clopen_coefficient_comparison l E T (U i)
    exact ⟨d, sf_clopen_derived_compatibility l E T (U i) hc d⟩

end WeilConjectures
