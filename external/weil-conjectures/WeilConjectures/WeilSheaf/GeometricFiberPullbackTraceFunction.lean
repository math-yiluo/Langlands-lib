/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiberPullbackTrace

/-!
# The trace function of the Weil sheaf `p^* H`

For a lisse `ℓ`-adic sheaf `H` on `X₀`, the trace function of the Weil sheaf `p^* H` pulled back
from the model, at an `𝔽_{q^{n+1}}`-point with geometric point `x̄`, is the trace of the Galois
action of `σ^{n+1}` on `Γ(Spec k̄, x̄^* H)`
(`AlgebraicGeometry.WeilSheaf.traceFunction_geometricFiberPullback_eq_trace_galoisGlobalSections`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The underlying `ℓ`-adic sheaf of the Weil sheaf `p^* H` pulled back from the model is
`p^* H`. -/
noncomputable def geometricFiberPullbackObjCarrierIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    (geometricFiberPullback (k₀ := k₀) hH).obj.carrier ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H :=
  Iso.refl _

/-- The congruence isomorphisms of `ℓ`-adic pullbacks along two proofs of `g = g'` agree. The
proofs are compared as arguments of `adicUpperStarCongr`; the kernel compares them under
`NatTrans.app` only by unfolding everything. -/
lemma adicUpperStarCongr_hom_app_congr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (e e' : g = g')
    (M : AdicSheaf l Y) :
    (adicUpperStarCongr l e).hom.app M = (adicUpperStarCongr l e').hom.app M :=
  congrArg (fun i : (g)^*ᵃ[l] ≅ (g')^*ᵃ[l] => i.hom.app M) rfl

/-- The Weil structure of `p^* H` is the canonical one, `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`. -/
lemma geometricFiberPullback_str_hom_comp_carrierIso_hom {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.app
          (geometricFiberPullback (k₀ := k₀) hH).obj.carrier ≫
        (geometricFiberPullback (k₀ := k₀) hH).obj.str.hom ≫
          (geometricFiberPullbackObjCarrierIso hH).hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map
          (geometricFiberPullbackObjCarrierIso hH).hom ≫
        (adicUpperStarComp l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (CommRingCat.of k₀)))).hom.app H := by
  have hstr : (geometricFiberPullback (k₀ := k₀) hH).obj.str.hom =
      ((ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso k₀ l X).app H).hom := by
    rw [Endofunctor.IsoAlgebra.str_hom]
    rfl
  -- stated for a variable isomorphism `α`, so that the kernel does not unfold the concrete one
  have h {P Q : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (α : P ≅ Q) :
      α.hom.app (geometricFiberPullback (k₀ := k₀) hH).obj.carrier =
        α.hom.app (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H) := rfl
  rw [geometricFiberPullbackObjCarrierIso, Iso.refl_hom, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.id_comp, hstr, h]
  simp only [ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  -- the two sides differ in the proof of `Fr ≫ p = p`
  exact (Iso.hom_inv_id_app_assoc _ _ _).trans
    (congrArg (_ ≫ ·) (adicUpperStarCongr_hom_app_congr _ _ H))

/-- **The trace function of the Weil sheaf `p^* H` pulled back from the model**: at an
`𝔽_{q^{n+1}}`-point `y` with geometric point `x̄`, it is the trace of the Galois action of
`σ^{n+1}` on `Γ(Spec k̄, x̄^* H)`. -/
theorem traceFunction_geometricFiberPullback_eq_trace_galoisGlobalSections {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)))
    {x : Spec (.of (AlgebraicClosure k₀)) ⟶ X}
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.galoisExtension.liftAlgebraicClosure k₀ (n + 1)).toRingHom) ≫ y.1 = x)
    (h : ((geometricFrobeniusField k₀).pow (n + 1)).hom ≫ x = x) :
    (geometricFiberPullback (k₀ := k₀) hH).traceFunction (n + 1) y =
      LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map
        (galoisGlobalSections ((geometricFrobeniusField k₀).pow (n + 1)).hom x h H)).hom :=
  traceFunction_eq_trace_galoisGlobalSections_of_adicIso _ (geometricFiberPullbackObjCarrierIso hH)
    (geometricFiberPullback_str_hom_comp_carrierIso_hom hH) n y hx h

end AlgebraicGeometry.WeilSheaf
