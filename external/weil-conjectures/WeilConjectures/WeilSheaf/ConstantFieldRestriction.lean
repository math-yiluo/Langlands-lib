/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
public import WeilConjectures.WeilSheaf.ConstantFieldComponent

/-!
# Restricting Weil sheaves to a component over a larger constant field

Let `k₀ ⊆ k'` be finite fields with `#k' = #k₀ ^ r` and `V` a `k'`-scheme, regarded also as a
`k₀`-scheme. The geometric fibre `V ×_{k₀} k̄` is the disjoint union of the `r` conjugates of the
component `θ : V ×_{k'} k̄' ⟶ V ×_{k₀} k̄`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberComponentMap`), and `θ` intertwines the geometric
Galois Frobenius over `k'` with the `r`-th power of that over `k₀`. Restricting along `θ` a Weil
sheaf `(K, φ)` relative to `k₀` and keeping the iterate `φ_r` of its Weil structure gives a Weil
sheaf relative to `k'`: `(K, φ) ↦ (θ^* K, θ^* φ_r)`
(`AlgebraicGeometry.ProEtaleWeilSheaf.componentRestriction`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

noncomputable section

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  {l : ℕ} [Fact l.Prime] {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  (r : ℕ) (hr : Nat.card k' = Nat.card k₀ ^ r)

/-- The component map `θ : V ×_{k'} k̄' ⟶ V ×_{k₀} k̄`. -/
abbrev componentMap : (V ↘ Spec (CommRingCat.of k')).geometricFiber ⟶
    (V ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  have : Algebra.IsAlgebraic k₀ k' := Algebra.IsAlgebraic.of_finite k₀ k'
  Scheme.Hom.geometricFiberComponentMap _ _ hc

include hr in
lemma geometricGaloisFrobenius_hom_comp_componentMap :
    (V ↘ Spec (CommRingCat.of k')).geometricGaloisFrobenius.asIso.hom ≫ componentMap hc =
      componentMap hc ≫ ((V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom :=
  have : Algebra.IsAlgebraic k₀ k' := Algebra.IsAlgebraic.of_finite k₀ k'
  Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberComponentMap _ _ hc r hr

/-- The commutation `θ^* ⋙ Fr'^* ≅ (Frʳ)^* ⋙ θ^*` of the pullback along the component map with
the Frobenius pullbacks (in the pushforward convention `Fr^* = (Fr⁻¹)_*` of the Weil sheaves). -/
def componentRestrictionCommIso :
    (componentMap hc)^*ᵃ[l] ⋙ WeilSheaf.frobeniusPullback k' l V ≅
      frobeniusPowPullback k₀ l V r ⋙ (componentMap hc)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l
      (V ↘ Spec (CommRingCat.of k')).geometricGaloisFrobenius.asIso).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫
    adicUpperStarCongr l (geometricGaloisFrobenius_hom_comp_componentMap hc r hr) ≪≫
    adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l
      ((V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso) _

/-- **Restriction to a component**: a pro-étale Weil sheaf `(K, φ)` on `V` relative to `k₀`
gives the pro-étale Weil sheaf `(θ^* K, θ^* φ_r)` on `V` relative to `k'`. -/
def componentRestriction : ProEtaleWeilSheaf k₀ l V ⥤ ProEtaleWeilSheaf k' l V :=
  powFunctor k₀ l V r ⋙ IsoAlgebra.mapOfNatIso (componentRestrictionCommIso hc r hr)

@[simp]
lemma componentRestriction_obj_carrier (K : ProEtaleWeilSheaf k₀ l V) :
    ((componentRestriction hc r hr).obj K).carrier = (componentMap hc)^*ᵃ[l].obj K.carrier :=
  rfl

end ProEtaleWeilSheaf

namespace WeilSheaf

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k' ≠ l)]
  {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))] [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  (r : ℕ) (hr : Nat.card k' = Nat.card k₀ ^ r)

/-- Restriction to a component, on Weil sheaves: the pullback of a constructible sheaf is
constructible. -/
def componentRestriction : WeilSheaf k₀ l V ⥤ WeilSheaf k' l V :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ ProEtaleWeilSheaf.componentRestriction hc r hr)
    fun G ↦ G.property.upperStar _

/-- Restriction to a component preserves lissity. -/
theorem IsLisse.componentRestriction {G : WeilSheaf k₀ l V} (hG : G.IsLisse) :
    ((componentRestriction hc r hr).obj G).IsLisse :=
  hG.upperStar _

end WeilSheaf

end AlgebraicGeometry
