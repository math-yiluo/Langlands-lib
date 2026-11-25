/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.StratifiedLattice
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ContinuousLatticeIntersectionSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousFiniteEtaleTraceLattice

/-! Unordered stratified integral lattices
(blueprint: lem-sfb-topological-stratified-lattice-data). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Exact scalar extension identifies the trace image with the rational module.
This uses the existing counit and ordinary pushforward comparisons with the given
NormedField structure, avoiding any replacement of that structure.
Source: blueprint stratified-lattice proof, pushing down by the trace. -/
private theorem trace_image_adj_isIso
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {U : Scheme.{u}} (p : U ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P) [Epi τ] :
    let g := latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
      (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ
    IsIso (((Mod.extendRestrictAdjunction
      (coefficientMap (integralScalarMap l E) X)).homEquiv (image g) P).symm (image.ι g)) := by
  dsimp only
  let a := coefficientMap (integralScalarMap l E) X
  let F := Mod.extendScalars a
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) a
  let adj := Mod.extendRestrictAdjunction a
  let b := latticePushedEmbedding (integralScalarMap l E) X P p M e
  let g := b ≫ G.map τ
  have := integralScalarCounit_isIso l E X P
  have := integralScalarCounit_isIso l E X
    ((lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P))
  have := integralScalarUnderivedPushHom_isIso l E p M
  have := latticePushedEmbedding_map_isIso (integralScalarMap l E) X P p M e
  have hfac : F.map g ≫ adj.counit.app P = F.map b ≫ adj.counit.app _ ≫ τ := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun z ↦ F.map b ≫ z) (adj.counit.naturality τ)
  have : Epi (F.map g ≫ adj.counit.app P) := by
    rw [hfac]
    infer_instance
  have : Epi (F.map g) :=
    (epi_comp_iff_of_isIso (F.map g) (adj.counit.app P)).mp inferInstance
  have : Epi (F.map (factorThruImage g) ≫ F.map (image.ι g)) := by
    rw [← F.map_comp, image.fac]
    infer_instance
  have : Epi (F.map (image.ι g)) :=
    epi_of_epi (F.map (factorThruImage g)) (F.map (image.ι g))
  have : IsIso (F.map (image.ι g)) := isIso_of_mono_of_epi _
  change IsIso (F.map (image.ι g) ≫ adj.counit.app P)
  infer_instance


/-- A locally free rational module admits integral lattices on a finite locally closed
stratification. This is the lattice-atlas, finite-etale stratification, and trace step;
the ordered refinement is separate.

Proof. A Noetherian underlying space is compact and quasi-separated. Apply the
continuous etale-local lattice theorem to
obtain a qcqs etale surjection and an integral locally free model upstairs. The
coefficient-stratification argument restricts this model to the finite etale
strata of that cover. On each stratum apply the continuous finite-etale trace
theorem. Its locally free trace image embeds monomorphically into the rational
module, and exact rationalization makes the actual scalar-extension adjoint an
isomorphism. The generic coefficient-stratification argument packages these
embedded lattices over the finite locally closed partition.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph, p. 61; blueprint
`lem-sfb-topological-stratified-lattices`, steps 1--3.
(blueprint: lem-sfb-topological-stratified-lattice-data).
-/
theorem exists_topologicalStratifiedLatticeData
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
    (L : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Y))
    (hL : LocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) Y) L) :
    ∃ S : Y.FiniteLocallyClosedStratification,
      ∀ i : Fin S.n,
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain i)) Ab.{u + 1})
            (condensedRingObj (integralCoeff l E) (S.domain i)),
          LocallyFree (condensedRingObj (integralCoeff l E) (S.domain i)) M ∧
          ∃ ι : M ⟶ (Mod.comap
              (coefficientMap (integralScalarMap l E) (S.domain i))).obj
              ((upperStar (Profinite.continuousMapRingObj E)
                (S.immersion i)).obj L),
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
              (coefficientMap (integralScalarMap l E) (S.domain i))).homEquiv M
                ((upperStar (Profinite.continuousMapRingObj E)
                  (S.immersion i)).obj L)).symm ι) := by
  classical
  apply coefficient_stratified_lattice (integralCoeff l E)
    (Profinite.continuousMapRingObj E) (integralScalarMap l E) Y L hL
    (continuousLisse_etale_lattice l E Y L hL)
  intro Z V q _ _ _ P hP M hM he
  obtain ⟨e⟩ := he
  obtain ⟨τ, hτ, hI⟩ := continuousFiniteEtaleTrace_lattice l E Z P hP q M hM e
  let := hτ
  let g := latticePushedEmbedding (integralScalarMap l E) Z P q M e ≫
    (Mod.comap (coefficientMap (integralScalarMap l E) Z)).map τ
  exact ⟨image g, hI, image.ι g, inferInstance, trace_image_adj_isIso l E Z P q M e τ⟩

end AlgebraicGeometry.ProEtale.CondensedRing
