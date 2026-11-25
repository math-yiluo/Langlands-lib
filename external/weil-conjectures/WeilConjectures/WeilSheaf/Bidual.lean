/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseBidual
public import WeilConjectures.WeilSheaf.Dual

/-!
# Biduality for lisse Weil sheaves

For a lisse Weil sheaf `P`, the biduality morphism `P ⟶ P^∨∨` of the underlying `ℓ`-adic
sheaves (`CategoryTheory.Mod.bidual`) is compatible with the Weil structures
(`AlgebraicGeometry.WeilSheaf.bidual_comm`): this follows from the compatibility of the
evaluations `P^∨ ⊗ P ⟶ ℚ̄_ℓ` and `P^∨∨ ⊗ P^∨ ⟶ ℚ̄_ℓ` with the Weil structures
(`AlgebraicGeometry.WeilSheaf.dual_evaluation_str`). It is an isomorphism, `P` being lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_bidual`), hence `P ≅ P^∨∨` as Weil sheaves
(`AlgebraicGeometry.WeilSheaf.nonempty_iso_dual_dual`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] Sheaf.symmetricCategory

/-- The biduality morphism `P ⟶ P^∨∨` of a lisse Weil sheaf is compatible with the Weil
structures. -/
theorem bidual_comm (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    (frobeniusPullback k₀ l X).map
        (Mod.bidual P.obj.carrier (adicConstant k₀ l X).obj.carrier) ≫
        ((P.dual hP).dual hP.dual).obj.str.hom =
      P.obj.str.hom ≫ Mod.bidual P.obj.carrier (adicConstant k₀ l X).obj.carrier := by
  let Fr := ProEtale.lowerStar (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
  let b := Mod.bidual P.obj.carrier (adicConstant k₀ l X).obj.carrier
  let sP := P.obj.str.hom.hom
  let sD := (P.dual hP).obj.str.hom.hom
  let sE := ((P.dual hP).dual hP.dual).obj.str.hom.hom
  let s₁ := (adicConstant k₀ l X).obj.str.hom.hom
  let evP := Mod.evaluation P.obj.carrier (adicConstant k₀ l X).obj.carrier
  let evD := Mod.evaluation (P.dual hP).obj.carrier (adicConstant k₀ l X).obj.carrier
  have hD : (sE ⊗ₘ sD) ≫ evD = μ Fr _ _ ≫ Fr.map evD ≫ s₁ :=
    dual_evaluation_str (P.dual hP) hP.dual
  have hP' : (sD ⊗ₘ sP) ≫ evP =
      μ Fr (P.dual hP).obj.carrier.X P.obj.carrier.X ≫ Fr.map evP ≫ s₁ :=
    dual_evaluation_str P hP
  have hb : b.hom ▷ (P.dual hP).obj.carrier.X ≫ evD =
      (β_ P.obj.carrier.X (P.dual hP).obj.carrier.X).hom ≫ evP :=
    Mod.uncurryHom_bidual _ _
  have : IsIso sD := inferInstanceAs (IsIso ((Mod.forget _).map (P.dual hP).obj.str.hom))
  have key : (Fr.map b.hom ≫ sE) ▷ (P.dual hP).obj.carrier.X ≫ evD =
      (sP ≫ b.hom) ▷ (P.dual hP).obj.carrier.X ≫ evD := by
    rw [← cancel_epi (Fr.obj P.obj.carrier.X ◁ sD), comp_whiskerRight, comp_whiskerRight,
      Category.assoc, Category.assoc, whisker_exchange_assoc, whisker_exchange_assoc,
      ← tensorHom_def_assoc, hD]
    refine (μ_natural_left_assoc Fr b.hom (P.dual hP).obj.carrier.X _).trans ?_
    rw [← Fr.map_comp_assoc, hb, Functor.map_comp_assoc, Functor.LaxBraided.braided_assoc, ← hP',
      ← tensorHom_def'_assoc, BraidedCategory.braiding_naturality_assoc]
    rfl
  exact Mod.uncurryHom_injective key

/-- **Biduality of a lisse sheaf** (blueprint: `proposition-six-operations-dctf--15`, "the canonical
map `P ⟶ P^∨∨` is an isomorphism"). -/
theorem nonempty_iso_dual_dual (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    Nonempty (P ≅ (P.dual hP).dual hP.dual) := by
  have : IsIso (Mod.bidual P.obj.carrier (adicConstant k₀ l X).obj.carrier) :=
    ProEtale.IsAdicLisseSheaf.isIso_bidual hP
  exact ⟨ObjectProperty.isoMk _ (IsoAlgebra.isoMk
    (asIso (Mod.bidual P.obj.carrier (adicConstant k₀ l X).obj.carrier)) (bidual_comm P hP))⟩

end AlgebraicGeometry.WeilSheaf
