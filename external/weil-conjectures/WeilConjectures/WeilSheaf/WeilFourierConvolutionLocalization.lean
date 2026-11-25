/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections

/-!
# Natural localization of functors with closed support

Source: convolution-kernel proof, Step 3, and the Weil open--closed adjunction.
(blueprint: lem-fd-weil-localization-functor)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

/-- A functor whose values restrict to zero on an open complement factors naturally through
the compact-support image of the closed immersion.
Source: convolution-kernel proof, Step 3.

Proof: whisker the closed adjunction unit by the functor. The open--closed localization
lemma makes every component invertible, so this is a natural isomorphism. The closed
immersion is proper, and its compact-support image is naturally its ordinary direct
image. This proves naturality as well as objectwise localization and works when either
the open or the closed part is empty.
(blueprint: lem-fd-weil-localization-functor) -/
theorem nonempty_iso_functor_closed_support
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X Z U : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [i.IsOver (Spec (CommRingCat.of k₀))] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hij : Set.range j = (Set.range i)ᶜ)
    {C : Type v} [Category.{w} C] (F : C ⥤ WeilComplex k₀ l X)
    (hF : ∀ P, IsZero ((upperStar j).obj (F.obj P))) :
    Nonempty (F ≅ F ⋙ upperStar i ⋙ derivedLowerShriek k₀ l i) := by
  obtain ⟨η, hη⟩ := exists_isIso_app_of_isZero_upperStar (k₀ := k₀) (l := l) i j hij
  have : ∀ P, IsIso ((Functor.whiskerLeft F η).app P) := fun P ↦ hη _ (hF P)
  have : IsIso (Functor.whiskerLeft F η) := NatIso.isIso_of_isIso_app _
  exact ⟨(Functor.rightUnitor F).symm ≪≫ asIso (Functor.whiskerLeft F η) ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft (upperStar i)
      (derivedLowerShriekIsoDerivedLowerStar (k₀ := k₀) (l := l) i).symm)⟩

end AlgebraicGeometry.WeilComplex
