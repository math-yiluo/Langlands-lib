/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRealizationFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientExchange
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement

/-! # Realization of finite discrete coefficient sheaves and exchange steps

Source: Bhatt--Scholze, Proposition 5.3.2, Lemmas 5.4.1 and 5.4.3;
Stacks Project, Tag 09AK.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_finiteDiscreteExchangeRealization
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

/-- Deriving the coefficient equivalence realizes constructible single complexes
and the exchange steps.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemmas 5.4.1 and 5.4.3
(blueprint: lem-weil-pbc-finite-discrete-exchange-step-realization).

Proof. Identify the condensed coefficient ring by the finite clopen fibre cover.
Use the coefficient realization and apply its sheaf origin isomorphisms to single
complexes. The constructed realization is full by bounded below site comparison,
commutes with shifts, and is triangulated because both constituent functors are
exact. Its exchange-step comparisons are those of the coefficient realization. -/
theorem finiteDiscreteExchange_stepRealization [DiscreteTopology B] [Finite B]
    (hB : (ℓ : B) = 0) (sq : CommSq g' f' f g)
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
    ∃ F0 : FiniteDiscreteEtalePlus B X ⥤
        DerivedCategory (FiniteDiscreteInternalModules B X),
    ∃ cs : F0.CommShift ℤ,
      letI := cs
      F0.Full ∧ F0.IsTriangulated ∧
      (∀ M : FiniteDiscreteInternalModules B X,
        ProEtale.IsConstructibleModuleObject
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) M →
        F0.essImage ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
      ∃ F1 : FiniteDiscreteEtalePlus B Y' ⥤
          DerivedCategory (FiniteDiscreteInternalModules B Y'),
      finiteDiscreteExchangeSteps B ℓ k sq F0 F1 := by
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  obtain ⟨E0, E1, horigin, hsteps⟩ :=
    finiteDiscreteExchange_coefficientRealization B ℓ k hB sq
      (fun T ↦ finiteDiscreteSchemeRingIso B T eR)
      (fun T ↦ by let := heR; infer_instance) hEncoding
  refine ⟨finiteDiscreteRealization B X E0, inferInstance, ?_⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨?_, finiteDiscreteRealization B Y' E1, ?_⟩
  · intro M hM
    exact finiteDiscreteRealization_single B X E0 M (horigin M hM)
  · intro L hL
    exact hsteps L hL

end AlgebraicGeometry.ProEtale.CondensedRing
