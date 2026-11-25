/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCover

/-!
# Transports along the Weil structure over arbitrary schemes

For a Weil sheaf `F` on `X₀`, a scheme `P` with a morphism `t : P ⟶ X̄` and a square
`τ ≫ t = t' ≫ Frᵐ`, the transport `Γ(P, t^* F) ⟶ Γ(P', t'^* F)` along the iterated Weil structure
`φ_m` (`AlgebraicGeometry.ProEtale.globalSectionsTransport`) generalises the Frobenius of the stalks
of `F` at geometric points, which is the case `P = P' = Spec k̄`
(`AlgebraicGeometry.WeilSheaf.stalkAt_frobenius_hom_eq_globalSectionsTransport`). This file
records, for arbitrary `P`:

* these transports commute with restrictions `Γ(P₁, t₁^* F) ⟶ Γ(P₂, t₂^* F)` along morphisms
  compatible with the squares (`AlgebraicGeometry.ProEtale.globalSectionsTransport_comp_resOver`);
* they compose (`AlgebraicGeometry.WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp'`);
* they are compatible with a morphism `θ : φ̄^* G ⟶ F` compatible with the Weil structures, for
  `φ : X₀ ⟶ Y₀` and a Weil sheaf `G` on `Y₀`
  (`AlgebraicGeometry.WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp_upperStar`).

They are used at the generic geometric point and at a strictly henselian neighbourhood of a
boundary point, for the Frobenius equivariance of blueprint `lemma-boundary-stalk--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Transports commute with restrictions.** For `ε : S₂ ⟶ S₁` over `Y` (`ε ≫ t₁ = t₂`) and
squares `τᵢ ≫ tᵢ = tᵢ ≫ g` with `τ₂ ≫ ε = ε ≫ τ₁`, the transport along the square at `S₁`
followed by the restriction along `ε` is the restriction followed by the transport at `S₂`. -/
lemma globalSectionsTransport_comp_resOver {Y S₁ S₂ : Scheme.{u}} {t₁ : S₁ ⟶ Y} {t₂ : S₂ ⟶ Y}
    {g : Y ⟶ Y} {τ₁ : S₁ ⟶ S₁} {τ₂ : S₂ ⟶ S₂} (h₁ : τ₁ ≫ t₁ = t₁ ≫ g) (h₂ : τ₂ ≫ t₂ = t₂ ≫ g)
    (ε : S₂ ⟶ S₁) (hε : ε ≫ t₁ = t₂) (hτ : τ₂ ≫ ε = ε ≫ τ₁)
    (P : Sheaf (Scheme.ProEt.topology Y) A) (ψ : (g)^*[A].obj P ⟶ P) :
    globalSectionsTransport A h₁ ψ ≫ (resOver A ε hε).app P =
      (resOver A ε hε).app P ≫ globalSectionsTransport A h₂ ψ := by
  have hψr : (upperStarComp A g (𝟙 Y)).hom.app P ≫ (g)^*[A].map ((upperStarId A Y).hom.app P) ≫
      ψ = (upperStarCongr A (Category.comp_id g)).hom.app P ≫ ψ := by
    rw [reassoc_of% upperStarComp_id_right_hom_app]
  have hψl : (upperStarComp A (𝟙 Y) g).hom.app P ≫ ((𝟙 Y))^*[A].map ψ ≫
      (upperStarId A Y).hom.app P = (upperStarCongr A (Category.id_comp g)).hom.app P ≫ ψ := by
    have n := (upperStarId A Y).hom.naturality ψ
    simp only [Functor.id_map] at n
    rw [n, reassoc_of% upperStarComp_id_left_hom_app]
  have hε' : ε ≫ t₁ = t₂ ≫ 𝟙 Y := hε.trans (Category.comp_id t₂).symm
  have k₁ : (ε ≫ τ₁) ≫ t₁ = t₂ ≫ g := by rw [Category.assoc, h₁, ← Category.assoc, hε]
  have k₂ : (τ₂ ≫ ε) ≫ t₁ = t₂ ≫ g := by rw [Category.assoc, hε, h₂]
  rw [resOver_app_eq_transport, globalSectionsTransport_comp_eq A h₁ hε' k₁ rfl
    (Category.id_comp g) _ _ ψ hψl, globalSectionsTransport_comp_eq A hε' h₂ k₂ rfl
    (Category.comp_id g) _ _ ψ hψr]
  exact globalSectionsTransport_congr_left A k₁ hτ.symm ψ

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` for `f = 𝟙`, followed by `f^* = (𝟙)^* ≅ 𝟭`,
is the identification `(f ≫ g)^* = g^*`. -/
lemma upperStarComp_hom_app_comp_upperStarCongr_id {Y Y' : Scheme.{u}} {f : Y' ⟶ Y'}
    (p : f = 𝟙 Y') (g : Y' ⟶ Y) (h : f ≫ g = g) (G : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarComp A f g).hom.app G ≫ (upperStarCongr A p).hom.app ((g)^*[A].obj G) ≫
        (upperStarId A Y').hom.app ((g)^*[A].obj G) =
      (upperStarCongr A h).hom.app G := by
  subst p
  simpa [upperStarCongr] using upperStarComp_id_left_hom_app A g G

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The transports along the iterated Weil structures compose, over arbitrary schemes, for
`b = 0`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp_zero (F : WeilSheaf k₀ l X)
    {P P' P'' : Scheme.{u}} {t : P ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t' : P' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t'' : P'' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {τ : P' ⟶ P} {τ' : P'' ⟶ P'} {τ'' : P'' ⟶ P} (a : ℕ)
    (ha : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom)
    (hb' : τ' ≫ t' = t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom)
    (hτ : τ' ≫ τ = τ'')
    (hab : τ'' ≫ t =
      t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (a + 0)).asIso.hom) :
    ProEtale.globalSectionsTransport _ ha (F.frobeniusPowStr a) ≫
        ProEtale.globalSectionsTransport _ hb' (F.frobeniusPowStr 0) =
      ProEtale.globalSectionsTransport _ hab (F.frobeniusPowStr (a + 0)) := by
  have p : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom = 𝟙 _ := by
    rw [pow_zero]
    rfl
  refine ProEtale.globalSectionsTransport_comp_eq _ ha hb' hab hτ
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a 0) _ _ _ ?_
  have n₁ := (ProEtale.upperStarCongr (WeilCoefficients.{u} l) p).hom.naturality
    (F.frobeniusPowStr a)
  have n₂ := (ProEtale.upperStarId (WeilCoefficients.{u} l) _).hom.naturality
    (F.frobeniusPowStr a)
  simp only [Functor.id_map] at n₂
  rw [F.frobeniusPowStr_zero p]
  rw [reassoc_of% n₁, n₂, reassoc_of% (ProEtale.upperStarComp_hom_app_comp_upperStarCongr_id p
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a 0)
    F.obj.carrier.X)]
  rfl

/-- The transports along the iterated Weil structures compose, over arbitrary schemes:
transporting along `φ_a` and then along `φ_b` is transporting along `φ_{a+b}`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp' (F : WeilSheaf k₀ l X) {P P' P'' : Scheme.{u}}
    {t : P ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t' : P' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t'' : P'' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {τ : P' ⟶ P} {τ' : P'' ⟶ P'} {τ'' : P'' ⟶ P} (a b : ℕ)
    (ha : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom)
    (hb' : τ' ≫ t' = t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).asIso.hom)
    (hτ : τ' ≫ τ = τ'')
    (hab : τ'' ≫ t =
      t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (a + b)).asIso.hom) :
    ProEtale.globalSectionsTransport _ ha (F.frobeniusPowStr a) ≫
        ProEtale.globalSectionsTransport _ hb' (F.frobeniusPowStr b) =
      ProEtale.globalSectionsTransport _ hab (F.frobeniusPowStr (a + b)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact F.globalSectionsTransport_frobeniusPowStr_comp_zero a ha hb' hτ hab
  have hg := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a b
  have h'' : (τ' ≫ τ) ≫ t = t'' ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).asIso.hom ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) := by
    rw [Category.assoc, ha, ← Category.assoc, hb', Category.assoc]
  have add := upperStarFactor_hom_app_comp_frobeniusPowStr_add F a b hb hg
  have hψ : (ProEtale.upperStarComp _ _ _).hom.app F.obj.carrier.X ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).asIso.hom)^*[_].map
        (F.frobeniusPowStr a) ≫ F.frobeniusPowStr b =
      (ProEtale.upperStarCongr _ hg).hom.app F.obj.carrier.X ≫ F.frobeniusPowStr (a + b) := by
    rw [← add]
    simp [ProEtale.upperStarFactor, ProEtale.upperStarCongr]
  rw [ProEtale.globalSectionsTransport_comp _ ha hb' h'',
    ProEtale.globalSectionsTransport_congr _ h'' hg _ _ hψ,
    ProEtale.globalSectionsTransport_congr_left _ _ hτ]

section UpperStar

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  {φ : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} {G : WeilSheaf k₀ l Y}
  {θ : (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[WeilCoefficients.{u} l].obj
    G.obj.carrier.X ⟶ F.obj.carrier.X}

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

/-- The transports along the first iterates of the Weil structures, over an arbitrary scheme `P`,
are intertwined by a morphism `θ : φ̄^* G ⟶ F` compatible with the Weil structures. -/
lemma globalSectionsTransport_frobeniusPowStr_one_comp_upperStar
    (hθ : (ProEtale.upperStarComp _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (φ̄)).hom.app G.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map θ ≫
          F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app G.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            G.obj.carrier.X ≫
        (φ̄)^*[_].map G.frobeniusStr ≫ θ)
    {P : Scheme.{u}} {t t' : P ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {τ : P ⟶ P}
    (hX : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.hom)
    (hY : τ ≫ (t ≫ φ̄) =
      (t' ≫ φ̄) ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.hom) :
    ProEtale.globalSectionsTransport _ hY (G.frobeniusPowStr 1) ≫
        ProEtale.globalSectionsTransport _ (τ := (Iso.refl _).hom) (Category.id_comp (t' ≫ φ̄)) θ =
      ProEtale.globalSectionsTransport _ (τ := (Iso.refl _).hom) (Category.id_comp (t ≫ φ̄)) θ ≫
        ProEtale.globalSectionsTransport _ hX (F.frobeniusPowStr 1) := by
  have pX := congrArg (fun e ↦ e.asIso.hom)
    (pow_one (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius)
  have pY := congrArg (fun e ↦ e.asIso.hom)
    (pow_one (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius)
  rw [ProEtale.globalSectionsTransport_congr _ hX pX _ _ (F.frobeniusPowStr_one pX),
    ProEtale.globalSectionsTransport_congr _ hY pY _ _ (G.frobeniusPowStr_one pY)]
  exact ProEtale.globalSectionsTransport_comm_of_upperStar _ (φ̄)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).symm G.frobeniusStr F.frobeniusStr θ hθ _ _

/-- **Transports along the Weil structures and pullbacks**, over an arbitrary scheme `P`: a
morphism `θ : φ̄^* G ⟶ F` compatible with the Weil structures intertwines the transports along
the iterated Weil structures `φ_m`, `m ≥ 1`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp_upperStar
    (hθ : (ProEtale.upperStarComp _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (φ̄)).hom.app G.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map θ ≫
          F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app G.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
            G.obj.carrier.X ≫
        (φ̄)^*[_].map G.frobeniusStr ≫ θ)
    (m : ℕ) (hm : 1 ≤ m) {P : Scheme.{u}}
    {t t' : P ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {τ : P ⟶ P}
    (hX : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (hY : τ ≫ (t ≫ φ̄) =
      (t' ≫ φ̄) ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom) :
    ProEtale.globalSectionsTransport _ hY (G.frobeniusPowStr m) ≫
        ProEtale.globalSectionsTransport _ (τ := (Iso.refl _).hom) (Category.id_comp (t' ≫ φ̄)) θ =
      ProEtale.globalSectionsTransport _ (τ := (Iso.refl _).hom) (Category.id_comp (t ≫ φ̄)) θ ≫
        ProEtale.globalSectionsTransport _ hX (F.frobeniusPowStr m) := by
  induction m, hm using Nat.le_induction generalizing t t' τ with
  | base => exact globalSectionsTransport_frobeniusPowStr_one_comp_upperStar hθ hX hY
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
    rw [← G.globalSectionsTransport_frobeniusPowStr_comp' m 1 haY hbY hτ hY,
      ← F.globalSectionsTransport_frobeniusPowStr_comp' m 1 haX hbX hτ hX,
      Category.assoc, globalSectionsTransport_frobeniusPowStr_one_comp_upperStar hθ
        hbX hbY, ← Category.assoc, ih haX haY, Category.assoc]

end UpperStar

end AlgebraicGeometry.WeilSheaf
