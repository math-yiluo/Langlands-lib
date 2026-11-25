/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRealizationFunctor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientExchangeFromComparisons

/-! # Realization of finite discrete coefficient sheaves and exchange steps

Source: Bhatt--Scholze, Proposition 5.3.2, Lemmas 5.4.1 and 5.4.3;
Stacks Project, Tag 09AK.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_finiteDiscreteCoefficientExchange
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

set_option linter.unusedVariables false in
/-- Finite discrete realization on constructible sheaves and on the three exchange steps.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemmas 5.4.1 and 5.4.3;
Stacks Project, Tag 09AK
(blueprint: lem-weil-pbc-finite-discrete-coefficient-realization).

Proof in words. Use the supplied monoidal constant-ring identification on every
scheme. Choose the canonical family induced from the point in the application.
Encode internal modules over the sheafified constant
ring as module-valued sheaves. Use a single sectionwise encoding on all schemes, so that
its comparison with the underlying abelian sheaf respects scalar actions and restriction.
These equivalences are additive and exact. Compose their inverses on derived categories
with the exact etale-to-pro-etale inverse image in the specified realization functor.
Its fullness, shift and triangulated structures are proved separately in the realization
API. Every constructible internal module becomes
an intrinsically constructible finite coefficient sheaf: transport its finite local
presentations on its finite stratification. A presentation map between finite free
constant-ring sheaves is a finite matrix of locally constant B-valued sections.
Refine its cover simultaneously for these finitely many entries, so the matrix is
constant. Its cokernel is then the constant sheaf of a finitely presented B-module,
which is finite because B is finite. Thus the original strata have locally constant
finite module sheaves as restrictions, including zero cokernels and empty strata.
Tag 09AK gives its etale sheaf origin, and
this gives the underived essential-image assertion here. Compatibility with single
complexes and bounded devissage are proved outside this statement.

For the step comparisons use functorial inverse-image comparison and the bounded below
qcqs direct-image comparison. All four morphisms of the square are finite type between
separated finite-type k-schemes, so the direct-image comparisons apply. These comparisons
are the mates of the same underived adjunction comparisons. The mate unit equation gives
the first commuting square below; coherent pullback composition and the commutativity of
sq give the second; the mate counit equation gives the third. The intermediate vertices
are exactly those in the specified unit--square--counit definitions. The factored
comparison record also carries the defining factorization equations for the two total
arrows; these are the internal definition and Etale.baseChange_app followed by map_comp.
Restrict along the
fully faithful bounded constructible inclusions using the displayed hypothesis hL.
The condition ell B = 0 ensures constructible pushforward in this finite-type setting.
No invertibility of exchange, properness, or Cartesian hypothesis is used. The construction
also applies to empty schemes and the zero ring. This statement requires only sheaf-level
origin, not derived origin for a bounded complex. -/
theorem finiteDiscreteExchange_coefficientRealization [DiscreteTopology B] [Finite B]
    (hB : (ℓ : B) = 0) (sq : CommSq g' f' f g)
    (eR : ∀ T : Scheme.{u},
      Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
          condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
    (heR : ∀ T : Scheme.{u}, IsMonHom (eR T).hom)
    (hEncoding : ∀ T : Scheme.{u},
      ∃ G : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (RingCat.of (ULift.{u + 1} B) : RingCat.{u + 1}))) ⥤
            Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B)),
        G.IsEquivalence ∧ Nonempty (G ⋙
          sheafCompose (Scheme.ProEt.topology T)
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ≅
          Mod.forget (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
              (RingCat.of (ULift.{u + 1} B) : RingCat.{u + 1}))))) :
    haveI : Fact (IsNilpotent (ℓ : B)) := ⟨⟨1, by rw [pow_one]; exact hB⟩⟩
    ∃ (E0 : FiniteDiscreteProEtaleSheaves B X ≌ FiniteDiscreteInternalModules B X)
      (E1 : FiniteDiscreteProEtaleSheaves B Y' ≌ FiniteDiscreteInternalModules B Y'),
      (∀ M : FiniteDiscreteInternalModules B X,
        ProEtale.IsConstructibleModuleObject
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) M →
        (ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} B)] ⋙ E0.functor).essImage M) ∧
      finiteDiscreteExchangeSteps B ℓ k sq
        (finiteDiscreteRealization B X E0) (finiteDiscreteRealization B Y' E1) := by
  have _ := heR
  have _ := hEncoding
  obtain ⟨e, he⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  let := he
  obtain ⟨G, hG, hforget⟩ := internalModuleAb_equivalence (ULift.{u + 1} B)
  let := hG
  let E := finiteDiscreteCoefficientEquivalence B e G hforget
  refine ⟨E X, E Y', ?_, ?_⟩
  · intro M hM
    obtain ⟨A, _, ⟨i⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj (ULift.{u + 1} B)
        (finiteDiscreteCoefficient_constructible B e G hforget X M hM)
    exact ⟨A, ⟨(E X).functor.mapIso i ≪≫ (E X).counitIso.app M⟩⟩
  · obtain ⟨P⟩ := finiteDiscreteCoefficient_derivedComparisonData B e G hforget
    exact coefficientComparisonData_exchangeSteps B ℓ k hB sq
      (fun T ↦ finiteDiscreteRealization B T (E T)) (P.toComparisonData B)

end AlgebraicGeometry.ProEtale.CondensedRing
