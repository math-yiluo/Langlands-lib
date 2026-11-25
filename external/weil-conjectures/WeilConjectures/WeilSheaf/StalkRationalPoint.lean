/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.DirectImageRestriction

/-!
# Stalks on the point

At a geometric point `s : Spec k̄ ≅ X̄` which is an isomorphism, as on the point `Spec k₀`, the
stalk of a Weil sheaf is the space of global sections with its Frobenius
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_globalSections_stalkAt`): the restriction of
global sections to the stalk is bijective.
With `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_upperStar` this computes the stalk of a
Weil sheaf at a `k₀`-rational point as the global sections of its pullback to the point.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilCoefficients

variable {l : ℕ} [Fact l.Prime]

/-- The Frobenius module `(A, e)` of a finite-dimensional `ℚ̄_ℓ`-module `A` with an automorphism
`e`. -/
noncomputable def frobeniusModule (A : WeilCoefficients.{u} l)
    [FiniteDimensional (PadicAlgCl l) ((toModuleCat l).obj A)] (e : A ≅ A) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) where
  carrier := (toModuleCat l).obj A
  frobenius := linearEquivOfIso e

/-- An isomorphism `g : A ≅ B` intertwining automorphisms `e_A`, `e_B` is an isomorphism of the
Frobenius modules `(A, e_A) ≅ (B, e_B)`. -/
theorem nonempty_equiv_frobeniusModule {A B : WeilCoefficients.{u} l}
    [FiniteDimensional (PadicAlgCl l) ((toModuleCat l).obj A)]
    [FiniteDimensional (PadicAlgCl l) ((toModuleCat l).obj B)]
    (eA : A ≅ A) (eB : B ≅ B) (g : A ⟶ B) [IsIso g] (h : g ≫ eB.hom = eA.hom ≫ g) :
    Nonempty ((frobeniusModule A eA).Equiv (frobeniusModule B eB)) :=
  ⟨⟨linearEquivOfIso (asIso g), fun x ↦ by
    change ((toModuleCat l).map g).hom (((toModuleCat l).map eA.hom).hom x) =
      ((toModuleCat l).map eB.hom).hom (((toModuleCat l).map g).hom x)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, h]⟩⟩

end WeilCoefficients

namespace WeilSheaf

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The restriction `Γ(X̄, F) ⟶ F_s` of global sections to the stalk at a geometric point `s`
which is an isomorphism `Spec k̄ ≅ X̄` is bijective: the unit `F ⟶ s_* s^* F` is an isomorphism,
`s_*` being an equivalence. -/
instance isIso_globalSectionsToStalkObj {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l X)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [IsIso s] : IsIso (F.globalSectionsToStalkObj s) := by
  have : (s)_*[WeilCoefficients.{u} l].IsEquivalence :=
    (ProEtale.lowerStarEquivalence (WeilCoefficients.{u} l) (asIso s)).isEquivalence_functor
  have : IsIso ((ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) s).unit.app
      F.obj.carrier.X) :=
    (Adjunction.isIso_unit_app_iff_mem_essImage _).2 (Functor.EssSurj.mem_essImage _ _)
  unfold globalSectionsToStalkObj
  infer_instance

/-- **The stalk on the point is the space of global sections.** For a geometric point `s` of a
`k₀`-scheme which is an isomorphism `Spec k̄ ≅ X̄` (as for `X = Spec k₀`) and is fixed by the
Frobenius, the restriction of global sections to the stalk at `s` is an isomorphism of Frobenius
modules `Γ(X̄, F) ≅ F_s`. -/
theorem nonempty_equiv_globalSections_stalkAt {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [IsIso s] (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.hom =
      (specGeometricFrobenius k₀ ^ 1).asIso.hom ≫ s) :
    Nonempty (F.globalSections.Equiv (F.stalkAt s 1 hs)) :=
  have := F.finiteDimensional_globalSections
  have := F.finiteDimensional_stalkObj s
  WeilCoefficients.nonempty_equiv_frobeniusModule (A := (Sheaf.Γ _ _).obj F.obj.carrier.X)
    (B := F.stalkObj s) _ _ _ (globalSectionsToStalkObj_comp_stalkAt_iso F s hs)

end WeilSheaf

end AlgebraicGeometry
