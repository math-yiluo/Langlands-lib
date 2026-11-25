/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteScalarCoherence
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteConstructibilityComparison
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicClosureScalarCoherence
import WeilConjectures.FourierTransform.FdIntegralIdentityRationalEquivalence
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleRationalHomComparison
import WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousFiltrationModels

/-! # Coherent finite adic realizations

Source: Bhatt--Scholze, Propositions 6.6.11 and 6.8.14(2); HRS Theorem 7.7.
(blueprint: lem-sf-adic-finite-realization-cocone).

The data declarations are reexported from
`AdicFiniteRealizationData`, allowing the proof steps to have independent modules.
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicFiniteRealization

private theorem realization_image (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
    (s : RationalModuleRealization l E T)
    (K : DerivedCategory (pbcModules T (rationalCoefficientSheaf l T E))) :
    finiteFreeTarget T (rationalCoefficientSheaf l T E) K ↔
      ∃ M, Nonempty (s.J.obj M ≅ K) := by
  have hf := ((constructibleRationalHomComparison l E T).2 s).2.1
  have hi := ((constructibleRationalHomComparison l E T).2 s).2.2
  let X : ContinuousRational.Base l :=
    { scheme := T, dimension := Fact.out, prime_unit := Fact.out }
  constructor
  · rintro ⟨⟨a, b, _, ha, hb⟩, hc⟩
    have := ha
    have := hb
    obtain ⟨_, M, _, ⟨e⟩, _⟩ := RationalConeModels.bounded_model l E T s hf hi
      (fun F hF ↦ ContinuousRational.rationalContinuousFiltrationModels l E X s F hF)
      K a b (fun r hr ↦ hr.elim
        (fun h ↦ DerivedCategory.isZero_of_isGE K a r h)
        (fun h ↦ DerivedCategory.isZero_of_isLE K b r h)) hc
    exact ⟨(pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj M, ⟨e⟩⟩
  · rintro ⟨⟨M⟩, ⟨e⟩⟩
    obtain ⟨⟨a, b, ha, hb⟩, hc⟩ := s.constructible M
    let q : (pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)).obj M.obj ≅ K :=
      (eqToIso (s.objects M)).symm ≪≫ e
    have := ha
    have := hb
    have hge := DerivedCategory.TStructure.t.isGE_of_iso q a
    have hle := DerivedCategory.TStructure.t.isLE_of_iso q b
    refine ⟨⟨min a b, b, min_le_right _ _, ?_, hle⟩, fun r ↦ ?_⟩
    · exact DerivedCategory.TStructure.t.isGE_of_ge K (min a b) a (min_le_left _ _)
    · obtain ⟨t, ht⟩ := hc r
      refine ⟨t, fun j ↦ ?_⟩
      have := ht j
      exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1}
        ((proEtaleModuleInverseImage (t.immersion j)
          (rationalCoefficientSheaf l T E)).mapIso
            ((DerivedCategory.homologyFunctor _ r).mapIso q))

private theorem core_exists (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))] : Nonempty (Core l T) := by
  classical
  let stage (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :=
    (fdIntegralIdentityRationalEquivalence D l hl (PadicAlgCl l) T E).choose
  obtain ⟨raw⟩ := fdCompletionInverseScalarCoherence D l hl (PadicAlgCl l) T stage
  let realization (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :=
    Classical.choice (rationalModuleRealizationFunctor l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T)
  refine ⟨⟨stage, raw, realization, ?_, ?_⟩⟩
  · intro E K L
    have hf := ((constructibleRationalHomComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T).2 (realization E)).2.1
    have hi := ((constructibleRationalHomComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T).2 (realization E)).2.2
    exact (Functor.FullyFaithful.ofFullyFaithful (realization E).J).map_bijective K L
  · intro E K
    exact realization_image l (pbcFiniteField.{u} l (PadicAlgCl l) E) T (realization E) K

end WeilConjectures.AdicFiniteRealization
