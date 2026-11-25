/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.FiberMapPow
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# Stalks of the pullback of a Weil sheaf

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes with base change `φ̄ : X̄ ⟶ Ȳ`, and `F` a Weil
sheaf on `Y`. The stalk of `φ^* F` at a geometric point `t` of `X̄` is the stalk of `F` at
`t ≫ φ̄`, compatibly with the Frobenius relative to `𝔽_{qᵐ}`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_upperStar`). As a consequence pullback
preserves punctual purity (`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.upperStar`).
-/

@[expose] public section

universe u' u v

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Transports of global sections along a morphism `θ : j^* M ⟶ N` commute with transports along
structure maps `ψ_M : g_Y^* M ⟶ M` and `ψ_N : g_X^* N ⟶ N` compatible with `θ`, for
`g_X ≫ j = j ≫ g_Y`. -/
lemma globalSectionsTransport_comm_of_upperStar {X Y P : Scheme.{u}} (j : X ⟶ Y) (gX : X ⟶ X)
    (gY : Y ⟶ Y) (hc : gX ≫ j = j ≫ gY) {M : Sheaf (Scheme.ProEt.topology Y) A}
    {N : Sheaf (Scheme.ProEt.topology X) A} (ψM : (gY)^*[A].obj M ⟶ M)
    (ψN : (gX)^*[A].obj N ⟶ N) (θ : (j)^*[A].obj M ⟶ N)
    (hθ : (upperStarComp A gX j).hom.app M ≫ (gX)^*[A].map θ ≫ ψN =
      (upperStarCongr A hc).hom.app M ≫ (upperStarComp A j gY).hom.app M ≫ (j)^*[A].map ψM ≫ θ)
    {t t' : P ⟶ X} {τ : P ⟶ P} (hX : τ ≫ t = t' ≫ gX) (hY : τ ≫ (t ≫ j) = (t' ≫ j) ≫ gY) :
    globalSectionsTransport A hY ψM ≫
        globalSectionsTransport A (τ := (Iso.refl _).hom) (Category.id_comp (t' ≫ j)) θ =
      globalSectionsTransport A (τ := (Iso.refl _).hom) (Category.id_comp (t ≫ j)) θ ≫
        globalSectionsTransport A hX ψN := by
  have h₁ : ((Iso.refl _).hom ≫ τ) ≫ (t ≫ j) = t' ≫ (j ≫ gY) := by
    simp only [Iso.refl_hom, Category.id_comp, Category.assoc] at hY ⊢; exact hY
  have h₂ : (τ ≫ (Iso.refl _).hom) ≫ (t ≫ j) = t' ≫ (gX ≫ j) := by
    simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc, hX]
  rw [globalSectionsTransport_comp _ _ _ h₁, globalSectionsTransport_comp _ _ _ h₂,
    globalSectionsTransport_congr _ h₂ hc _
      ((upperStarComp A _ _).hom.app M ≫ (j)^*[A].map ψM ≫ θ) hθ,
    globalSectionsTransport_congr_left _ _
      (by simp : (τ ≫ (Iso.refl _).hom) = (Iso.refl _).hom ≫ τ)]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The image of a point with finite residue field has finite residue field. -/
theorem Hom.map_mem_finitePoints (g : X ⟶ Y) {x : X} (hx : x ∈ X.finitePoints) :
    g.base x ∈ Y.finitePoints :=
  have : Finite (X.residueField x) := hx
  Finite.of_injective _ (g.residueFieldMap x).hom.injective

/-- The degree of the image of a point with finite residue field divides the degree of the
point: the residue field of the image embeds into that of the point. -/
theorem Hom.degreeOver_dvd_degreeOver_comp (g : X ⟶ Y) (f : Y.Hom (Spec (.of k))) {x : X}
    (hx : x ∈ X.finitePoints) :
    f.degreeOver (g.base x) ∣ (g ≫ f).degreeOver x := by
  let := (f.residueFieldAlgebraMap (g.base x)).toAlgebra
  let := ((g ≫ f).residueFieldAlgebraMap x).toAlgebra
  let := (g.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k (Y.residueField (g.base x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change (g ≫ f).residueFieldAlgebraMap x c = _
      rw [residueFieldAlgebraMap_comp]
      rfl
  have : Finite (X.residueField x) := hx
  have : Module.Finite (Y.residueField (g.base x)) (X.residueField x) := Module.Finite.of_finite
  exact ⟨_, (Module.finrank_mul_finrank k (Y.residueField (g.base x)) (X.residueField x)).symm⟩

end AlgebraicGeometry.Scheme

namespace FrobeniusModule

variable {K : Type v} [Field K] [IsAlgClosed K]

/-- If the Frobenius of `N` has the characteristic polynomial of the `r`-th power of the
Frobenius of `M`, `r ≥ 1`, and `M` is pure of weight `w` relative to `q`, then `N` is pure of
weight `w` relative to `q ^ r`: every eigenvalue of `F_Mʳ` is the `r`-th power of an eigenvalue
of `F_M`. -/
theorem IsPureOfWeight.of_charpoly_eq_pow {ι : K →+* ℂ} {q : ℕ} {M N : FrobeniusModule.{u, v} K}
    {w : ℝ} (h : M.IsPureOfWeight ι q w) {r : ℕ} (hr : 0 < r)
    (hMN : N.frobeniusEnd.charpoly = (M.frobeniusEnd ^ r).charpoly) :
    N.IsPureOfWeight ι (q ^ r) w := by
  intro β hβ
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hMN,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_mem_spectrum,
    spectrum.map_pow_of_pos _ hr] at hβ
  obtain ⟨α, hα, rfl⟩ := hβ
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hα
  rw [map_pow, norm_pow, h α hα, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg q), ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

section Pullback

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y)

/-- The underlying sheaf of `φ^* F` is the pullback along `φ̄`. -/
lemma upperStar_obj_obj_carrier :
    ((upperStar φ).obj F).obj.carrier =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].obj
        F.obj.carrier :=
  rfl

/-- The Weil structure of `φ^* F` is transported from that of `F`. -/
lemma upperStar_obj_obj_str :
    ((upperStar φ).obj F).obj.str =
      (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
          (comp_over φ (Spec (CommRingCat.of k₀)))).app F.obj.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].mapIso
          F.obj.str :=
  Endofunctor.IsoAlgebra.mapOfNatIso_obj_str _ F.obj

private lemma frobeniusStr_upperStar_aux :
    ((upperStar φ).obj F).frobeniusStr =
      (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.app
          ((upperStar φ).obj F).obj.carrier.X ≫
      (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].obj
            F.obj.carrier).X ≫
      (ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))).inv.app
          F.obj.carrier.X ≫
        (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            F.obj.carrier.X ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[_].map
          F.frobeniusStr := by
  rw [frobeniusStr, upperStar_obj_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  change _ ≫ ((ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
    (comp_over φ (Spec (CommRingCat.of k₀)))).hom.app F.obj.carrier ≫ _).hom = _
  rw [Mod.comp_hom', ProEtale.adicUpperStar_map_hom,
    ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso_hom_app_hom]
  simp only [Category.assoc, frobeniusStr, Functor.map_comp]
  rfl

-- Stated for a variable isomorphism `α`: for `α = upperStarIsoLowerStarInv` the kernel times out
-- comparing the two objects, which agree only up to unfolding `upperStar`.
private lemma hom_inv_id_app_upperStar_assoc
    {P Q : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) ⥤
        Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)} (α : P ≅ Q) {Z} (h : P.obj
      ((Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].obj
        F.obj.carrier).X ⟶ Z) :
    α.hom.app ((upperStar φ).obj F).obj.carrier.X ≫
      α.inv.app ((Scheme.Hom.geometricFiberMap φ
        (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].obj F.obj.carrier).X ≫ h = h :=
  Iso.hom_inv_id_app_assoc α _ h

/-- The Weil structure of the pullback `φ^* F`, on the underlying sheaves: the pullback along `φ̄`
of the Weil structure of `F`, through `Fr_X^* φ̄^* ≅ (Fr_X ≫ φ̄)^* = (φ̄ ≫ Fr_Y)^* ≅ φ̄^* Fr_Y^*`.
-/
lemma frobeniusStr_upperStar :
    ((upperStar φ).obj F).frobeniusStr =
      (ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))).inv.app
          F.obj.carrier.X ≫
        (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            F.obj.carrier.X ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[_].map
          F.frobeniusStr :=
  (frobeniusStr_upperStar_aux φ F).trans (hom_inv_id_app_upperStar_assoc φ F _ _)


set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

section Comparison

variable {F}
variable (G : WeilSheaf k₀ l X) (θ : (φ̄)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X ⟶
  G.obj.carrier.X)

/-- The map `F_{t ≫ φ̄} ⟶ G_t` of stalks induced by `θ : φ̄^* F ⟶ G`: the transport along
`𝟙 ≫ (t ≫ φ̄) = t ≫ φ̄`. -/
noncomputable def stalkObjHomOfUpperStar
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    F.stalkObj (t ≫ φ̄) ⟶ G.stalkObj t :=
  ProEtale.globalSectionsTransport _ (τ := (Iso.refl _).hom) (Category.id_comp (t ≫ φ̄)) θ

instance isIso_stalkObjHomOfUpperStar [IsIso θ]
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    IsIso (stalkObjHomOfUpperStar φ G θ t) := by
  have e := ProEtale.globalSectionsTransport_eq_of_iso (WeilCoefficients.{u} l) (Iso.refl _)
    (Category.id_comp (t ≫ φ̄)) θ
  dsimp only [stalkObjHomOfUpperStar]
  erw [e]
  infer_instance

variable {φ G θ}

/-- The maps of stalks induced by a compatible `θ` intertwine the transports along the first
iterates of the Weil structures. -/
lemma globalSectionsTransport_frobeniusPowStr_one_comp_stalkObjHomOfUpperStar
    (hθ : (ProEtale.upperStarComp _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (φ̄)).hom.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map θ ≫
          G.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            F.obj.carrier.X ≫
        (φ̄)^*[_].map F.frobeniusStr ≫ θ)
    {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {τ : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    (hX : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.hom)
    (hY : τ ≫ (t ≫ φ̄) =
      (t' ≫ φ̄) ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.hom) :
    ProEtale.globalSectionsTransport _ hY (F.frobeniusPowStr 1) ≫
        stalkObjHomOfUpperStar φ G θ t' =
      stalkObjHomOfUpperStar φ G θ t ≫ ProEtale.globalSectionsTransport _ hX
        (G.frobeniusPowStr 1) := by
  have pX := congrArg (fun e ↦ e.asIso.hom)
    (pow_one (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius)
  have pY := congrArg (fun e ↦ e.asIso.hom)
    (pow_one (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius)
  rw [ProEtale.globalSectionsTransport_congr _ hX pX _ _ (G.frobeniusPowStr_one pX),
    ProEtale.globalSectionsTransport_congr _ hY pY _ _ (F.frobeniusPowStr_one pY),
    stalkObjHomOfUpperStar, stalkObjHomOfUpperStar]
  exact ProEtale.globalSectionsTransport_comm_of_upperStar _ (φ̄)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).symm F.frobeniusStr G.frobeniusStr θ hθ _ _

/-- The maps of stalks induced by a `θ : φ̄^* F ⟶ G` compatible with the Weil structures
intertwine the transports along the iterated Weil structures `φ_m`, `m ≥ 1`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp_stalkObjHomOfUpperStar
    (hθ : (ProEtale.upperStarComp _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (φ̄)).hom.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map θ ≫
          G.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            F.obj.carrier.X ≫
        (φ̄)^*[_].map F.frobeniusStr ≫ θ)
    (m : ℕ) (hm : 1 ≤ m)
    {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {τ : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    (hX : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (hY : τ ≫ (t ≫ φ̄) =
      (t' ≫ φ̄) ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom) :
    ProEtale.globalSectionsTransport _ hY (F.frobeniusPowStr m) ≫
        stalkObjHomOfUpperStar φ G θ t' =
      stalkObjHomOfUpperStar φ G θ t ≫ ProEtale.globalSectionsTransport _ hX
        (G.frobeniusPowStr m) := by
  induction m, hm using Nat.le_induction generalizing t t' τ with
  | base => exact globalSectionsTransport_frobeniusPowStr_one_comp_stalkObjHomOfUpperStar hθ hX hY
  | succ m hm ih =>
    have pc := Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow φ
      (comp_over φ (Spec (CommRingCat.of k₀)))
    set FX := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    set FY := (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    have e₁ := FX.pow_hom_comp_pow_hom m 1
    have haX : (Iso.refl _).hom ≫ t = (t ≫ (FX ^ m).asIso.inv) ≫ (FX ^ m).asIso.hom := by simp
    have hbX : τ ≫ (t ≫ (FX ^ m).asIso.inv) = t' ≫ (FX ^ 1).asIso.hom := by
      rw [← cancel_mono (FX ^ m).asIso.hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, hX, Category.assoc, e₁]
    have haY : (Iso.refl _).hom ≫ (t ≫ φ̄) =
        ((t ≫ (FX ^ m).asIso.inv) ≫ φ̄) ≫ (FY ^ m).asIso.hom := by
      rw [Category.assoc, pc]
      simp
    have hbY : τ ≫ ((t ≫ (FX ^ m).asIso.inv) ≫ φ̄) = (t' ≫ φ̄) ≫ (FY ^ 1).asIso.hom := by
      rw [Category.assoc t', pc, ← Category.assoc t', ← hbX]
      simp
    have hτ : τ ≫ (Iso.refl _).hom = τ := Category.comp_id τ
    rw [← F.globalSectionsTransport_frobeniusPowStr_comp m 1 le_rfl haY hbY hτ hY,
      ← G.globalSectionsTransport_frobeniusPowStr_comp m 1 le_rfl haX hbX hτ hX,
      Category.assoc, globalSectionsTransport_frobeniusPowStr_one_comp_stalkObjHomOfUpperStar hθ
        hbX hbY, ← Category.assoc, ih haX haY, Category.assoc]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private lemma linearEquivOfIso_toLinearMap' {M N : WeilCoefficients.{u} l} (e : M ≅ N) :
    (WeilCoefficients.linearEquivOfIso e).toLinearMap =
      ((WeilCoefficients.toModuleCat l).map e.hom).hom :=
  rfl

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private lemma toModuleCat_map_comp_hom' {M N P : WeilCoefficients.{u} l} (f : M ⟶ N)
    (g : N ⟶ P) :
    ((WeilCoefficients.toModuleCat l).map (f ≫ g)).hom =
      ((WeilCoefficients.toModuleCat l).map g).hom ∘ₗ
        ((WeilCoefficients.toModuleCat l).map f).hom := by
  rw [Functor.map_comp]
  rfl

/-- For `θ : φ̄^* F ≅ G` compatible with the Weil structures, the stalk of `F` at `t ≫ φ̄` and
the stalk of `G` at `t`, with their Frobenius relative to `𝔽_{qᵐ}`, are isomorphic. -/
lemma nonempty_equiv_stalkAt_of_upperStar [IsIso θ]
    (hθ : (ProEtale.upperStarComp _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (φ̄)).hom.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map θ ≫
          G.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            F.obj.carrier.X ≫
        (φ̄)^*[_].map F.frobeniusStr ≫ θ)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (m : ℕ)
    (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ t)
    (ht' : (t ≫ φ̄) ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ (t ≫ φ̄)) :
    Nonempty ((F.stalkAt (t ≫ φ̄) m ht').Equiv (G.stalkAt t m ht)) := by
  refine ⟨.ofComp (WeilCoefficients.linearEquivOfIso (asIso (stalkObjHomOfUpperStar φ G θ t)))
    ?_⟩
  rw [linearEquivOfIso_toLinearMap', asIso_hom]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [frobeniusEnd_stalkAt_zero, frobeniusEnd_stalkAt_zero]
    rfl
  · rw [frobeniusEnd_stalkAt, frobeniusEnd_stalkAt, ← toModuleCat_map_comp_hom',
      ← toModuleCat_map_comp_hom',
      globalSectionsTransport_frobeniusPowStr_comp_stalkObjHomOfUpperStar hθ m hm ht.symm
        ht'.symm]

end Comparison

section UpperStar


lemma upperStarComp_hom_app_comp_frobeniusStr_upperStar :
    @CategoryStruct.comp _ _ _
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].obj
        ((φ̄)^*[_].obj F.obj.carrier.X)) ((upperStar φ).obj F).obj.carrier.X
      ((ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
        (φ̄)).hom.app F.obj.carrier.X) ((upperStar φ).obj F).frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            F.obj.carrier.X ≫
        (φ̄)^*[_].map F.frobeniusStr :=
  (congrArg (_ ≫ ·) (frobeniusStr_upperStar φ F)).trans (Iso.hom_inv_id_app_assoc _ _ _)

-- Stated for a variable functor `P`: the two objects agree only up to unfolding `upperStar`.
private lemma map_id_comp_upperStar
    {P : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) ⥤
        Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)} {Z} (R : P.obj ((upperStar φ).obj F).obj.carrier.X ⟶ Z) :
    @CategoryStruct.comp _ _ (P.obj ((φ̄)^*[_].obj F.obj.carrier.X))
      (P.obj ((upperStar φ).obj F).obj.carrier.X) Z (P.map (𝟙 _)) R = R := by
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp R

private lemma comp_id_upperStar {W} (f : W ⟶ (φ̄)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X) :
    @Eq (W ⟶ ((upperStar φ).obj F).obj.carrier.X)
      (f ≫ (𝟙 _ : (φ̄)^*[_].obj F.obj.carrier.X ⟶ ((upperStar φ).obj F).obj.carrier.X)) f :=
  Category.comp_id f

/-- The identity `φ̄^* F ⟶ φ^* F` of the underlying sheaves is compatible with the Weil
structures. -/
lemma upperStar_frobeniusStr_compatible :
    (ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (φ̄)).hom.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
          (𝟙 _ : (φ̄)^*[_].obj F.obj.carrier.X ⟶ ((upperStar φ).obj F).obj.carrier.X) ≫
        ((upperStar φ).obj F).frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            F.obj.carrier.X ≫
        (φ̄)^*[_].map F.frobeniusStr ≫
          (𝟙 _ : (φ̄)^*[_].obj F.obj.carrier.X ⟶ ((upperStar φ).obj F).obj.carrier.X) :=
  ((congrArg (_ ≫ ·) (map_id_comp_upperStar φ F _)).trans
    (upperStarComp_hom_app_comp_frobeniusStr_upperStar φ F)).trans
    (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (comp_id_upperStar φ F _))).symm

end UpperStar

end Pullback

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- **Punctual purity on a closed fibre.** The pullback `φ^* F` of a sheaf punctually `ι`-pure of
weight `w` along a morphism `φ : X ⟶ Y` of `k₀`-schemes is punctually `ι`-pure of weight `w`:
at a closed point `z` of `X` over `x = φ z`, with `r = [κ(z) : κ(x)]`, the local Frobenius of
`φ^* F` at `z` has the characteristic polynomial of `Fₓʳ`, and `q_z = q_xʳ`.

The blueprint states this for the inclusion `X_y ⟶ X` of the fibre of a morphism `X ⟶ Y` over a
closed point `y`, with purity on `X_y` relative to `κ(y)`; since residue cardinalities do not
depend on the base field, purity relative to `κ(y)` and relative to `k₀` agree
(blueprint: `proposition-weights-under-usual-operations--7`). -/
theorem IsPunctuallyPureOfWeight.upperStar {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l Y}
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ((WeilSheaf.upperStar φ).obj F).IsPunctuallyPureOfWeight ι w := by
  intro z
  have hφ := comp_over φ (Spec (CommRingCat.of k₀))
  let x : Y.finitePoints := ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩
  have hdvd : (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
    have := Scheme.Hom.degreeOver_dvd_degreeOver_comp φ (Y ↘ Spec (CommRingCat.of k₀)) z.2
    rwa [hφ] at this
  have hz := Scheme.Hom.degreeOver_ne_zero (X ↘ Spec (CommRingCat.of k₀)) z.2
  have hx := Scheme.Hom.degreeOver_ne_zero (Y ↘ Spec (CommRingCat.of k₀)) x.2
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) z
  have ht' : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom =
      (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap φ hφ) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have : IsIso (𝟙 _ : (Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X ⟶ ((WeilSheaf.upperStar φ).obj F).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X)))
  obtain ⟨e₁⟩ := nonempty_equiv_stalkAt_of_upperStar (G := (WeilSheaf.upperStar φ).obj F) (θ := 𝟙 _)
    (upperStar_frobeniusStr_compatible (φ := φ) F) s _ ht ht'
  have hbase : (((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1 :=
    Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ x
  have hss' : (((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      ((s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hbase, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc]
    exact (congrArg φ.base
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ z)).symm
  have hc := F.charpoly_frobeniusEnd_stalkAt_of_dvd _ _ hss' (hbase ▸ x.2) hdvd
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ x) ht'
  have hr : 0 < (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
      (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hdvd) (Nat.pos_of_ne_zero hx)
  have key := (h x).of_charpoly_eq_pow hr (e₁.charpoly_frobeniusEnd.trans hc)
  have hq : (X ↘ Spec (CommRingCat.of k₀)).residueCard z.1 =
      (Y ↘ Spec (CommRingCat.of k₀)).residueCard x.1 ^
        ((X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
          (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) := by
    rw [Scheme.Hom.residueCard, Scheme.Hom.residueCard, ← pow_mul, Nat.mul_div_cancel' hdvd]
  rw [hq]
  exact key

end AlgebraicGeometry.WeilSheaf
