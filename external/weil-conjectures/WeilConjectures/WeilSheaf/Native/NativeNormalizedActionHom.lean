/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeFrobeniusRingedModel.NativeActionSiteHomComparison
import all WeilConjectures.WeilSheaf.NativeFrobeniusRingedModel.NativeActionSiteHomComparison

/-! # The normalized forward action-site Hom comparison

This records the underlying map of the existing comparison, without choosing
new sites or equivalences. Source: native action-site Hom comparison step 2.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The action-site Hom comparison with its specified underlying ordinary map.
Source: the local Hom/evaluation paragraph of prose-10-20,
and the normalized component construction of native_action_site_hom_comparison.
(blueprint: lem-sf-native-normalized-action-hom).

Proof: use action_hom_component for each pair. Its underlying map is E(P.hom)
followed by A.hom. P.hom_naturality followed by A.hom_naturality proves
naturality; faithfulness of native forgetting lifts that equation. -/
theorem normalized_action_hom
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X)
    (P : TwistedActionRingedSite.Presentation A.J A.s A.R A.a) :
    letI := P.category
    ∃ h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := P.coefficient)) ⋙
        A.toWeil P ≅ ((A.toWeil P).op.prod (A.toWeil P)) ⋙
          Functor.uncurry.obj (ihomBifunctor k₀ l X),
      ∀ M N : TwistedActionRingedSite.Modules P.coefficient,
        (h.hom.app (op M, N)).hom.f = A.E.functor.map (P.hom M N).hom ≫
          (A.hom (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a).hom := by
  let _ := P.category
  refine ⟨NatIso.ofComponents
    (fun MN ↦ action_hom_component A P MN.1.unop MN.2) ?_, fun _ _ ↦ rfl⟩
  intro MN MN' fg
  apply Endofunctor.IsoAlgebra.hom_ext
  change A.E.functor.map
      (P.modules.functor.map (SheafOfModules.homObjMap (R := P.coefficient)
        fg.1.unop fg.2)).hom.f ≫
        (A.E.functor.map (P.hom MN'.1.unop MN'.2).hom ≫
          (A.hom (P.modules.functor.obj MN'.1.unop).obj.a
            (P.modules.functor.obj MN'.2).obj.a).hom) =
    (A.E.functor.map (P.hom MN.1.unop MN.2).hom ≫
        (A.hom (P.modules.functor.obj MN.1.unop).obj.a
          (P.modules.functor.obj MN.2).obj.a).hom) ≫
      (Mod.ihomMap (A.E.functor.map (P.modules.functor.map fg.1.unop).hom.f)).app _ ≫
        (ProEtale.AdicSheaf.ihom
          (A.E.functor.obj (P.modules.functor.obj MN'.1.unop).obj.a)).map
          (A.E.functor.map (P.modules.functor.map fg.2).hom.f)
  have hp := congrArg (fun f ↦ A.E.functor.map f ≫
      (A.hom (P.modules.functor.obj MN'.1.unop).obj.a
        (P.modules.functor.obj MN'.2).obj.a).hom)
    (P.hom_naturality fg.1.unop fg.2)
  have hh := congrArg (fun f ↦ A.E.functor.map (P.hom MN.1.unop MN.2).hom ≫ f)
    (A.hom_naturality (P.modules.functor.map fg.1.unop).hom.f
      (P.modules.functor.map fg.2).hom.f)
  simp only [Functor.map_comp, Category.assoc] at hp
  simp only [Category.assoc] at hh ⊢
  exact hp.trans hh

end AlgebraicGeometry.ProEtaleWeilSheaf
