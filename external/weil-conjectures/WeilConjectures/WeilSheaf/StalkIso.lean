/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFunctor

/-!
# Stalks of isomorphic Weil sheaves

An isomorphism of Weil sheaves induces isomorphisms of Frobenius modules between their geometric
stalks, and a zero Weil sheaf has zero stalks.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_of_iso` and
  `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_of_iso`: the isomorphism of stalks induced by an
  isomorphism of Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.subsingleton_stalk_of_isZero`: the stalks of a zero Weil sheaf
  vanish.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section StalkAt

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
    (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)

/-- The linear isomorphism between the stalks at `s` induced by an isomorphism of Weil
sheaves. -/
noncomputable def stalkAtLinearEquivOfIso {F G : WeilSheaf k₀ l X} (e : F ≅ G) :
    (F.stalkAt s m hs).carrier ≃ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier :=
  LinearEquiv.ofLinearMap (stalkAtMap s m hs e.hom) (stalkAtMap s m hs e.inv)
    (LinearMap.ext fun y ↦ (stalkAtMap_comp s m hs e.inv e.hom y).symm.trans
      ((congrArg (fun f ↦ stalkAtMap s m hs f y) e.inv_hom_id).trans (stalkAtMap_id s m hs G y)))
    (LinearMap.ext fun y ↦ (stalkAtMap_comp s m hs e.hom e.inv y).symm.trans
      ((congrArg (fun f ↦ stalkAtMap s m hs f y) e.hom_inv_id).trans (stalkAtMap_id s m hs F y)))

/-- The underlying linear map of `stalkAtLinearEquivOfIso` is the stalk map. -/
theorem stalkAtLinearEquivOfIso_toLinearMap {F G : WeilSheaf k₀ l X} (e : F ≅ G) :
    (stalkAtLinearEquivOfIso s m hs e).toLinearMap = stalkAtMap s m hs e.hom :=
  rfl

/-- An isomorphism of Weil sheaves induces an isomorphism of Frobenius modules between the
stalks at `s`. -/
theorem nonempty_equiv_stalkAt_of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G) :
    Nonempty ((F.stalkAt s m hs).Equiv (G.stalkAt s m hs)) :=
  ⟨FrobeniusModule.Equiv.ofComp (stalkAtLinearEquivOfIso s m hs e) (by
    rw [stalkAtLinearEquivOfIso_toLinearMap]
    exact LinearMap.ext fun x ↦ stalkAtMap_frobenius s m hs e.hom x)⟩

end StalkAt

/-- An isomorphism of Weil sheaves induces an isomorphism of Frobenius modules between the
stalks at a closed point. -/
theorem nonempty_equiv_stalk_of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G) (x : X.finitePoints) :
    Nonempty ((F.stalk x).Equiv (G.stalk x)) :=
  nonempty_equiv_stalkAt_of_iso _ _ _ e

/-- The stalks of a zero Weil sheaf are zero. -/
theorem subsingleton_stalk_of_isZero {F : WeilSheaf k₀ l X} (hF : IsZero F)
    (x : X.finitePoints) : Subsingleton (F.stalk x).carrier :=
  not_nontrivial_iff_subsingleton.1 fun h ↦
    (Set.eq_empty_iff_forall_notMem.1 (support_eq_empty_of_isZero hF)) x h

end AlgebraicGeometry.WeilSheaf
