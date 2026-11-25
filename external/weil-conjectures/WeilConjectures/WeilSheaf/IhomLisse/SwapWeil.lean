/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomSwap
public import WeilConjectures.WeilSheaf.IhomLisse.CompWeil

/-!
# Swapping iterated internal homs of pro-étale Weil sheaves

The swap `[a, [b, K]] ≅ [b, [a, K]]` (`CategoryTheory.Mod.ihomSwap`) is compatible with the Weil
structures (`AlgebraicGeometry.ProEtaleWeilSheaf.ihomSwap_comm`), which gives the natural
isomorphism `[a, [b, -]] ≅ [b, [a, -]]` of functors of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorCompIhomFunctorIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

attribute [local instance] Sheaf.symmetricCategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- **The swap `[a, [b, K]] ⟶ [b, [a, K]]` is compatible with the Weil structures.** -/
theorem ihomSwap_comm (a b K : ProEtaleWeilSheaf k₀ l X) :
    (WeilSheaf.frobeniusPullback k₀ l X).map (Mod.ihomSwap a.carrier b.carrier K.carrier) ≫
      (ihom k₀ l X b (ihom k₀ l X a K)).obj.str =
    (ihom k₀ l X a (ihom k₀ l X b K)).obj.str ≫ Mod.ihomSwap a.carrier b.carrier K.carrier := by
  rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom]
  exact Mod.map_ihomSwap_comp_of_eq
    (G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
      WeilCoefficients.{u} l])
    (ρ := adicConstantSheafToLowerStar l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)
    (c := fun M N ↦ frobeniusIhomComparison k₀ l X M N) uncurryHom_frobeniusIhomComparison
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) a.str b.str K.str
    _ (ihom_str_eq_trIso b K) _ (ihom_str_eq_trIso a K) _
    (ihom_str_eq_trIso a (ihom k₀ l X b K)) _ (ihom_str_eq_trIso b (ihom k₀ l X a K))

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- **Swapping iterated internal homs of pro-étale Weil sheaves**:
`[a, [b, -]] ≅ [b, [a, -]]`. -/
noncomputable def ihomFunctorCompIhomFunctorIso (a b : ProEtaleWeilSheaf k₀ l X) :
    ihomFunctor k₀ l X b ⋙ ihomFunctor k₀ l X a ≅ ihomFunctor k₀ l X a ⋙ ihomFunctor k₀ l X b :=
  NatIso.ofComponents
    (fun K ↦ IsoAlgebra.isoMk (Mod.ihomSwapIso a.carrier b.carrier K.carrier)
      (ihomSwap_comm a b K))
    fun f ↦ IsoAlgebra.hom_ext (Mod.ihomSwap_naturality _ _ f.hom.f)

end AlgebraicGeometry.ProEtaleWeilSheaf
