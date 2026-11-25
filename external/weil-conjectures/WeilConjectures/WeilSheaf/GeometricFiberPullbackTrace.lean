/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GaloisGlobalSectionsTransport


/-!
# The trace function of a Weil sheaf pulled back from the model

Let `p : X̄ ⟶ X₀` be the projection of the geometric fibre and `H` an `ℓ`-adic sheaf on `X₀`. If
`F` is a Weil sheaf with an isomorphism `F ≅ p^* H` carrying its Weil structure to the canonical
one `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`, the trace function of `F` at an `𝔽_{qᵐ}`-point is the
trace of the Galois action of `σᵐ` on the global sections `Γ(Spec k̄, x̄^* H)` at the geometric
point `x̄` over the point
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_galoisGlobalSections_of_iso`); in
particular for `F = p^* H` itself
(`AlgebraicGeometry.WeilSheaf.traceFunction_geometricFiberPullback_eq_trace_galoisGlobalSections`,
in `WeilConjectures.WeilSheaf.GeometricFiberPullbackTraceFunction`).

The proof goes through the transports of global sections
(`AlgebraicGeometry.ProEtale.globalSectionsTransport`): the iterated Weil structures of `F` are
the canonical morphisms `(Frᵐ)^* p^* H ⟶ p^* H`
(`AlgebraicGeometry.WeilSheaf.frobeniusPowStr_comp_eq_of_iso`), and the transports along `p` of
the stalk of `H` at `x̄` intertwine the Galois action with the stalk Frobenius of `F`
(`AlgebraicGeometry.ProEtale.globalSectionsTransport_comm_of_upperStar`).
-/

@[expose] public section

universe u u'

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- **The iterated Weil structures of a sheaf pulled back from the model.** If an isomorphism
`e : F ≅ p^* H` of the underlying sheaves carries the Weil structure of `F` to the canonical
one `Fr^* p^* H ⟶ p^* H`, then it carries the iterated Weil structure `φ_m`, `m ≥ 1`, to the
canonical morphism `(Frᵐ)^* p^* H ⟶ p^* H`. -/
lemma frobeniusPowStr_comp_eq_of_iso (F : WeilSheaf k₀ l X) {H : AdicSheaf l X}
    (e : F.obj.carrier.X ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*[WeilCoefficients.{u} l].obj H.X)
    (hF : F.frobeniusStr ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[WeilCoefficients.{u}
        l].map e.hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H.X)
    (m : ℕ) (hm : 1 ≤ m) :
    F.frobeniusPowStr m ≫ e.hom =
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)^*[
        WeilCoefficients.{u} l].map
          e.hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ m) H.X := by
  induction m, hm using Nat.le_induction with
  | base =>
    have p := congrArg (fun e : Aut _ ↦ e.asIso.hom)
      (pow_one (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius)
    have n := (ProEtale.upperStarCongr (WeilCoefficients.{u} l) p).hom.naturality e.hom
    rw [frobeniusPowStr_one F p, Category.assoc, hF, ← reassoc_of% n,
      upperStarCongr_hom_app_comp_upperStarInvariantHom]
  | succ m hm ih =>
    have e' : (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.hom := by
      rw [pow_succ, Aut.mul_asIso, Iso.trans_hom]
    have n := (upperStarFactor (WeilCoefficients.{u} l) e').hom.naturality e.hom
    rw [Functor.comp_map] at n
    rw [← upperStarFactor_hom_app_comp_frobeniusPowStr_succ F m e', Category.assoc,
      Category.assoc, hF, ← Functor.map_comp_assoc, ih, Functor.map_comp_assoc,
      ← reassoc_of% n, upperStarFactor_hom_app_comp_upperStarInvariantHom]

/-- The compatibility of `e⁻¹ : p^* H ⟶ F` with the iterated Weil structure `φ_m` of `F` and the
identity structure `𝟙^* H ≅ H` of `H`, for `Frᵐ ≫ p = p ≫ 𝟙`. -/
lemma upperStarComp_hom_app_comp_map_inv_comp_frobeniusPowStr (F : WeilSheaf k₀ l X)
    {H : AdicSheaf l X}
    (e : F.obj.carrier.X ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*[WeilCoefficients.{u} l].obj H.X)
    (hF : F.frobeniusStr ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[WeilCoefficients.{u}
        l].map e.hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H.X)
    (m : ℕ) (hm : 1 ≤ m)
    (hc : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ 𝟙 X) :
    (ProEtale.upperStarComp (WeilCoefficients.{u} l)
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).hom.app H.X ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)^*[
        WeilCoefficients.{u} l].map
          e.inv ≫ F.frobeniusPowStr m =
      (ProEtale.upperStarCongr (WeilCoefficients.{u} l) hc).hom.app H.X ≫
        (ProEtale.upperStarComp (WeilCoefficients.{u} l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj (𝟙 X)).hom.app H.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*[WeilCoefficients.{u} l].map
          ((ProEtale.upperStarId (WeilCoefficients.{u} l) X).hom.app H.X) ≫ e.inv := by
  have k := frobeniusPowStr_comp_eq_of_iso F e hF m hm
  have k' : (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)^*[
      WeilCoefficients.{u} l].map e.inv ≫ F.frobeniusPowStr m =
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ m) H.X ≫
          e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, k, ← Functor.map_comp_assoc, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, e.inv_hom_id,
      Category.comp_id]
  rw [k', upperStarInvariantHom, Category.assoc, Iso.hom_inv_id_app_assoc,
    upperStarComp_id_right_hom_app_comp_map_upperStarId_hom_app_assoc,
    upperStarCongr_hom_app_trans_eq_assoc]

/-- **The trace function of a Weil sheaf pulled back from the model.** Let `e : F ≅ p^* H` be an
isomorphism of the underlying sheaves carrying the Weil structure of `F` to the canonical one
`Fr^* p^* H ⟶ p^* H`. At an `𝔽_{q^{n+1}}`-point `y` with geometric point `x̄`, the trace function
of `F` is the trace of the Galois action of `σ^{n+1}` on `Γ(Spec k̄, x̄^* H)`. -/
theorem traceFunction_eq_trace_galoisGlobalSections_of_iso (F : WeilSheaf k₀ l X)
    {H : AdicSheaf l X}
    (e : F.obj.carrier.X ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*[WeilCoefficients.{u} l].obj H.X)
    (hF : F.frobeniusStr ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[WeilCoefficients.{u}
        l].map e.hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H.X)
    (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)))
    {x : Spec (.of (AlgebraicClosure k₀)) ⟶ X}
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.galoisExtension.liftAlgebraicClosure k₀ (n + 1)).toRingHom) ≫ y.1 = x)
    (h : ((geometricFrobeniusField k₀).pow (n + 1)).hom ≫ x = x) :
    F.traceFunction (n + 1) y =
      LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map
        (galoisGlobalSections ((geometricFrobeniusField k₀).pow (n + 1)).hom x h H)).hom := by
  have : Finite (FiniteField.galoisExtension k₀ (n + 1)) := Module.finite_of_finite k₀
  have hs := Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) (n + 1) IsAlgClosed.lift y
  have hστ := specGeometricFrobenius_pow_hom_eq_geometricFrobeniusField_pow_hom k₀ (n + 1)
  have hx' := (Scheme.Hom.geometricFiberPoint_comp_geometricFiberProj _ IsAlgClosed.lift y.1
    y.2).trans hx
  subst hx'
  have hY := h.trans (Category.comp_id _).symm
  have hc : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (n + 1)).asIso.hom ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ 𝟙 X :=
    (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ (n + 1)).trans
      (Category.comp_id _).symm
  have comm := globalSectionsTransport_comm_of_upperStar (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (n + 1)).asIso.hom (𝟙 X) hc
    ((ProEtale.upperStarId (WeilCoefficients.{u} l) X).hom.app H.X) (F.frobeniusPowStr (n + 1))
    e.inv
    (upperStarComp_hom_app_comp_map_inv_comp_frobeniusPowStr F e hF (n + 1)
      (Nat.le_add_left 1 n) hc) (hστ ▸ hs.symm) hY
  have hiso : IsIso (globalSectionsTransport (WeilCoefficients.{u} l) (τ := (Iso.refl _).hom)
      (Category.id_comp ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint IsAlgClosed.lift
        y.1 y.2 ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)) e.inv) :=
    isIso_globalSectionsTransport _ (Iso.refl _) _ _
  rw [traceFunction, frobeniusEnd_stalkAt, globalSectionsTransport_congr_left _ _ hστ]
  refine Eq.trans (WeilCoefficients.trace_toModuleCat_map_eq_of_comp_eq
    (asIso (globalSectionsTransport (WeilCoefficients.{u} l) (τ := (Iso.refl _).hom)
      (Category.id_comp _) e.inv)) comm).symm ?_
  rw [globalSectionsTransport_upperStarId_hom_app _ hY h, galoisGlobalSections_eq]
  rfl

/-- The compatibility of an isomorphism `e : F ≅ p^* H` of `ℓ`-adic sheaves with the Weil
structures, read on the underlying sheaves. -/
lemma frobeniusStr_comp_forget_map_eq (F : WeilSheaf k₀ l X) {H : AdicSheaf l X}
    (e : F.obj.carrier ≅ ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H)
    (hF : (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.app F.obj.carrier ≫
          F.obj.str.hom ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map e.hom ≫
        (adicUpperStarComp l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (CommRingCat.of k₀)))).hom.app H) :
    F.frobeniusStr ≫ ((AdicSheaf.forget _).mapIso e).hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[
        WeilCoefficients.{u} l].map
          ((AdicSheaf.forget _).mapIso e).hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H.X := by
  have k := congrArg Mod.Hom.hom hF
  rw [Mod.comp_hom', Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom, Mod.comp_hom',
    Mod.comp_hom', adicUpperStar_map_hom, adicUpperStarComp_inv_app_hom,
    adicUpperStarCongr_hom_app_hom'] at k
  exact k

/-- `AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_galoisGlobalSections_of_iso` for an
isomorphism `e : F ≅ p^* H` of `ℓ`-adic sheaves compatible with the Weil structures. -/
theorem traceFunction_eq_trace_galoisGlobalSections_of_adicIso (F : WeilSheaf k₀ l X)
    {H : AdicSheaf l X}
    (e : F.obj.carrier ≅ ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H)
    (hF : (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.app F.obj.carrier ≫
          F.obj.str.hom ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map e.hom ≫
        (adicUpperStarComp l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (CommRingCat.of k₀)))).hom.app H)
    (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)))
    {x : Spec (.of (AlgebraicClosure k₀)) ⟶ X}
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.galoisExtension.liftAlgebraicClosure k₀ (n + 1)).toRingHom) ≫ y.1 = x)
    (h : ((geometricFrobeniusField k₀).pow (n + 1)).hom ≫ x = x) :
    F.traceFunction (n + 1) y =
      LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map
        (galoisGlobalSections ((geometricFrobeniusField k₀).pow (n + 1)).hom x h H)).hom :=
  traceFunction_eq_trace_galoisGlobalSections_of_iso F ((AdicSheaf.forget _).mapIso e)
    (frobeniusStr_comp_forget_map_eq F e hF) n y hx h

end AlgebraicGeometry.WeilSheaf
