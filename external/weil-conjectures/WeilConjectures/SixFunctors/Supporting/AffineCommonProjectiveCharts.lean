/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import all WeilConjectures.SixFunctors.Constructible.ConstructibleFlatCohomologyTorBound
import all WeilConjectures.SixFunctors.Supporting.FieldTorAmplitude
import all WeilConjectures.AlgebraicGeometry.Finite.Field.FiniteFieldLisseInternalHom
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.Clopen.ClopenProjectiveChartCommonRefinement
import Mathlib.Data.Fintype.Order
import WeilConjectures.SixFunctors.Supporting.ResidueLisseProjectiveModels

/-!
# Common projective charts on an affine weakly contractible scheme

Source: Stacks Project, proetale.tex, Tag 09C3; Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8
(blueprint: lem-fix-affine-common-projective-charts).

All restrictions below are ordinary uncompleted derived ringed pullbacks. Coefficient
index zero is exponent one. Finite products of the unit module are finite direct sums.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
attribute [local irreducible] HasDerivedCategory.standard

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem residueFiniteTor (V : Scheme.{u})
    (K : proEtaleDerivedCategory V (Padic.coefficientExtensionRing l E 1))
    (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    HasFiniteProEtaleTorAmplitude V (Padic.coefficientExtensionRing l E 1) K := by
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := residueIdealMaximal l E
  let : Field (Padic.coefficientExtensionRing l E 1) :=
    Ideal.Quotient.field (Padic.coefficientExtensionIdeal l E 1)
  exact ⟨a, b, bounded_field_tor V _ K a b hab hbounded⟩

private theorem residueConstructible (V : Scheme.{u})
    (K : proEtaleDerivedCategory V (Padic.coefficientExtensionRing l E 1))
    (a b : ℤ) (_hab : a ≤ b)
    (hbounded : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hlocal : ∀ q : ℤ, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses V
      (Padic.coefficientExtensionRing l E 1)
      (fun L ↦ Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) L)
      ((DerivedCategory.homologyFunctor _ q).obj K)) :
    intrinsicFiniteTorsionConstructible l E 1 (by omega) V K := by
  classical
  have : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := residueIdealMaximal l E
  let : Field (Padic.coefficientExtensionRing l E 1) :=
    Ideal.Quotient.field (Padic.coefficientExtensionIdeal l E 1)
  refine ⟨(Set.finite_Icc a b).subset ?_, ?_⟩
  · intro q hq
    by_contra h
    exact hq (hbounded q (by simpa only [Set.mem_Icc, not_and_or, not_le] using h))
  · intro q
    apply (proEtaleModuleRestriction_constructible_iff V _ _).mpr
    refine ⟨Stratification.trivial V, fun i ↦ ?_⟩
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((ProEtale.upperStarId _ V).app _).symm (fixedFiniteModels V _ _ (hlocal q))

/-- Two ordinary restrictions with complete bounded finite lisse residue have
simultaneous bounded projective sheaf models on a finite clopen cover of an
already affine weakly contractible scheme.

Source: Stacks Project, Tag 09C3; Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8
(blueprint: lem-fix-affine-common-projective-charts).

Proof: the residue quotient is a field. The existing bounded-field Tor lemma
applies to the given residue cohomology bound and supplies a finite Tor bound
in the precise all-resolutions convention.
Finite local models give fixed finite locally constant sheaves and hence
intrinsic constructibility on the trivial stratification; the finite interval
bounds the support. Apply the residue-lisse projective-model theorem to each
ordinary restricted complex. The clopen common-refinement theorem intersects
the two resulting covers, preserves their bounded projective models, and
identifies the restrictions with the composite ordinary pullbacks. -/
theorem affine_common_projective_charts
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W V : Scheme.{u}) (f : V ⟶ W) [IsAffine V]
    (hweak : ∀ (F G : Sheaf (ProEt.topology V) (Type (u + 1)))
      (g : F ⟶ G), Epi g →
        Function.Surjective (g.hom.app (Opposite.op (ProEt.mk (𝟙 V)))))
    (M N : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (hresidue :
(∀ K : DerivedCategory (scalarReductionSource.{u, u} l E W),
          K = M ∨ K = N →
          IntegralOnSlice.IsComplete l E V none
            ((ordinaryIntegralDerivedPull l E f).obj K) ∧
          ∃ a b : ℤ, a ≤ b ∧
            (∀ q : ℤ, q < a ∨ b < q → IsZero
              ((DerivedCategory.homologyFunctor _ q).obj
                ((scalarReductionDerivedExtension l E V 0).obj
                  ((ordinaryIntegralDerivedPull l E f).obj K)))) ∧
            (∀ q : ℤ, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses V
              (Padic.coefficientExtensionRing l E 1)
              (fun L ↦ Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) L)
              ((DerivedCategory.homologyFunctor _ q).obj
                ((scalarReductionDerivedExtension l E V 0).obj
                  ((ordinaryIntegralDerivedPull l E f).obj K)))))) :
          ∃ (c : ℕ) (U : Fin c → V.Opens),
            (⨆ i, U i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
            (∀ i, CompactSpace (U i).toScheme) ∧
            (∀ i, QuasiSeparatedSpace (U i).toScheme) ∧
            ∀ (i : Fin c) (K : DerivedCategory (scalarReductionSource.{u, u} l E W)),
              K = M ∨ K = N →
              ∃ (P : CochainComplex (scalarReductionSource.{u, u} l E (U i).toScheme) ℤ)
                (a b : ℤ), a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
                (∀ q : ℤ, ∃ (r : ℕ)
                  (ι : P.X q ⟶ ∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
                    (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
                  (ρ : (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
                    (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
                    ⟶ P.X q), ι ≫ ρ = 𝟙 _) ∧
                Nonempty ((ordinaryIntegralDerivedPull l E
                  ((U i).ι ≫ f)).obj K ≅ DerivedCategory.Q.obj P) := by
  classical
  have hw : (ProEt.topology V).IsWeaklyContractible.{u + 1}
      (ProEt.mk (𝟙 V)) := by
    intro F G g hg
    have : Epi g := Sheaf.epi_of_isLocallySurjective g
    exact hweak F G g inferInstance
  apply clopen_projective_chart_common_refinement l E W V f M N
    (fun K hK ↦ (hresidue K hK).1)
  intro K hK
  obtain ⟨hc, a, b, hab, hb, hl⟩ := hresidue K hK
  have : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := residueIdealMaximal l E
  let : Field (Padic.coefficientExtensionRing l E 1) :=
    Ideal.Quotient.field (Padic.coefficientExtensionIdeal l E 1)
  exact residue_lisse_projective_models l E V inferInstance hw _ hc
    (residueConstructible l E V _ a b hab hb hl)
    (fun q ↦ (finiteLocal_iff V _ _).mp (fixedFiniteModels V _ _ (hl q)) |>.1)
    (residueFiniteTor l E V _ a b hab hb)

end WeilConjectures
