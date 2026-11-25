/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantFieldOfSmooth
public import WeilConjectures.WeilSheaf.ConstantFieldIrreducible

/-!
# Descent up to twist: reduction to geometrically connected schemes

Let `V₀` be a smooth irreducible affine scheme over a finite field `k₀`. It is smooth and
geometrically connected over its constant field `k'`
(`AlgebraicGeometry.exists_constantField_of_smooth`), and Weil sheaves on `V₀` relative to `k₀`
and to `k'` correspond, compatibly with irreducibility, pullbacks from `V₀` and constant twists
(`WeilConjectures.WeilSheaf.ConstantFieldIrreducible`). Hence the statement that irreducible
lisse Weil sheaves are constant twists of pulled-back lisse sheaves reduces to geometrically
connected schemes
(`WeilSheaf.IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback_of_constantField`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [Smooth (V ↘ Spec (CommRingCat.of k₀))] [IrreducibleSpace V] [IsAffine V]

/-- **Descent up to twist, reduction to the geometrically connected case**: if every
irreducible lisse Weil sheaf on `V`, regarded as a smooth geometrically connected scheme over a
finite field `k'`, is a constant twist of the pullback of a lisse sheaf on `V`, then so is every
irreducible lisse Weil sheaf on `V` relative to `k₀`. The field `k'` is the constant field of
`V`. -/
theorem IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback_of_constantField
    (hgc : ∀ (k' : Type u) [Field k'] [Finite k'] [Fact (ringChar k' ≠ l)]
      [V.Over (Spec (CommRingCat.of k'))] [IsSeparated (V ↘ Spec (CommRingCat.of k'))]
      [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k'))]
      [QuasiCompact (V ↘ Spec (CommRingCat.of k'))] [Smooth (V ↘ Spec (CommRingCat.of k'))]
      [GeometricallyConnected (V ↘ Spec (CommRingCat.of k'))] (G : WeilSheaf k' l V),
      G.IsIrreducibleLisse → ∃ (H : AdicSheaf l V) (hH : IsAdicLisseSheaf H)
        (b : (PadicAlgCl l)ˣ),
          Nonempty (G ≅ (geometricFiberPullback (k₀ := k') hH).constantTwist b))
    {G : WeilSheaf k₀ l V} (hG : G.IsIrreducibleLisse) :
    ∃ (H : AdicSheaf l V) (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ),
      Nonempty (G ≅ (geometricFiberPullback (k₀ := k₀) hH).constantTwist b) := by
  obtain ⟨k', _, _, _, c, hc, _, _⟩ :=
    exists_constantField_of_smooth (V ↘ Spec (CommRingCat.of k₀))
  let : V.Over (Spec (CommRingCat.of k')) := ⟨c⟩
  have : Fact (ringChar k' ≠ l) := ⟨by rw [← Algebra.ringChar_eq k₀ k']; exact Fact.out⟩
  have : Smooth (V ↘ Spec (CommRingCat.of k')) := inferInstanceAs (Smooth c)
  have : GeometricallyConnected (V ↘ Spec (CommRingCat.of k')) :=
    inferInstanceAs (GeometricallyConnected c)
  have : IsSeparated (V ↘ Spec (CommRingCat.of k')) := inferInstanceAs (IsSeparated c)
  have : QuasiCompact (V ↘ Spec (CommRingCat.of k')) := inferInstanceAs (QuasiCompact c)
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank k₀ k' = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm⟩
  obtain ⟨H, hH, b', ⟨e⟩⟩ := hgc k' _ (hG.constantFieldFunctor hc hm)
  obtain ⟨b, hb⟩ :=
    WeilSheaf.exists_iso_constantTwist_geometricFiberPullback_of_constantField hc hm hH b' e
  exact ⟨H, hH, b, hb⟩

end AlgebraicGeometry.WeilSheaf
