/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.SheafGluing
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence

/-!
# Descent of trivialisations along a pro-étale cover

Let `f : W ⟶ T` be a single-morphism pro-étale cover (weakly étale, surjective and
quasi-compact) and `M` an `ℓ`-adic sheaf on `T`. A trivialisation `ε : f^* M ≅ ℚ̄_ℓ,Wⁿ` whose
transition matrix on `W ×_T W` is the identity descends to a trivialisation `M ≅ ℚ̄_ℓ,Tⁿ`
(`AlgebraicGeometry.ProEtale.AdicSheaf.nonempty_iso_of_transitionMatrix_eq_one`).

The input is the sheaf property of `M` for the cover `f`, in the form of the descent of
morphisms `ℚ̄_ℓ ⟶ M` out of the unit, i.e. of global sections
(`AlgebraicGeometry.ProEtale.AdicSheaf.exists_upperStar_map_eq_of_cover`): the descended
morphisms `ℚ̄_ℓ,T ⟶ M` assemble to `ℚ̄_ℓ,Tⁿ ⟶ M`, whose pullback along `f` is `ε⁻¹`, hence is an
isomorphism, pullback along a cover being conservative.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {T W : Scheme.{u}}

/-- The isomorphisms `x^* ℚ̄_ℓ ≅ ℚ̄_ℓ` are compatible with the congruence isomorphisms. -/
lemma adicUpperStarCongr_hom_app_unit_comp {Q P : Scheme.{u}} {x y : Q ⟶ P} (p : x = y) :
    (adicUpperStarCongr l p).hom.app (unit l P) ≫ (adicUpperStarUnitIso l y).hom =
      (adicUpperStarUnitIso l x).hom := by
  subst p
  simp [adicUpperStarCongr]

/-- The inverse of a congruence isomorphism, on underlying sheaves. -/
lemma adicUpperStarCongr_inv_app_hom {Q P : Scheme.{u}} {x y : Q ⟶ P} (p : x = y)
    (M : AdicSheaf l P) :
    ((adicUpperStarCongr l p).inv.app M).hom =
      (upperStarCongr (WeilCoefficients.{u} l) p).inv.app M.X := by
  subst p
  rfl

/-- **Descent of morphisms out of the unit along a pro-étale cover.** Let `f : W ⟶ T` be weakly
étale, surjective and quasi-compact, and `M` an `ℓ`-adic sheaf on `T`. A morphism
`v : ℚ̄_ℓ,W ⟶ f^* M` whose pullbacks along any two `a b : W' ⟶ W` with `a ≫ f = b ≫ f` agree
(under `a^* f^* M ≅ (a ≫ f)^* M = (b ≫ f)^* M ≅ b^* f^* M`) is the pullback of a morphism
`ℚ̄_ℓ,T ⟶ M`. The morphism `f^* ℚ̄_ℓ,T ≅ ℚ̄_ℓ,W ⟶ f^* M` of underlying sheaves descends
(`AlgebraicGeometry.ProEtale.exists_hom_of_upperStar`), and the image of `1` under the descended
morphism is a global section of `M`, whose morphism out of `ℚ̄_ℓ,T`
(`AlgebraicGeometry.ProEtale.bijective_globalSectionOfModHom`) pulls back to `v`. -/
theorem exists_upperStar_map_eq_of_cover (f : W ⟶ T) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {M : AdicSheaf l T} (v : unit l W ⟶ (f)^*ᵃ[l].obj M)
    (hv : ∀ {W' : Scheme.{u}} (a b : W' ⟶ W) [WeaklyEtale a] [WeaklyEtale b]
      (hab : a ≫ f = b ≫ f),
      (adicUpperStarUnitIso l a).inv ≫ (a)^*ᵃ[l].map v ≫
          (adicUpperStarCompIso l hab).hom.app M =
        (adicUpperStarUnitIso l b).inv ≫ (b)^*ᵃ[l].map v) :
    ∃ w : unit l T ⟶ M, (adicUpperStarUnitIso l f).inv ≫ (f)^*ᵃ[l].map w = v := by
  -- the pullbacks of `ℚ̄_ℓ,T ≅ f^* ℚ̄_ℓ ⟶ f^* M` along `c` with `w = c ≫ f`
  have E₁ {W' : Scheme.{u}} (c : W' ⟶ W) (w : W' ⟶ T) (hc : w = c ≫ f) :
      (adicUpperStarCongr l hc).hom.app (unit l T) ≫ (adicUpperStarComp l c f).hom.app _ ≫
          (c)^*ᵃ[l].map ((adicUpperStarUnitIso l f).hom ≫ v) =
        (adicUpperStarUnitIso l w).hom ≫ (adicUpperStarUnitIso l c).inv ≫ (c)^*ᵃ[l].map v := by
    have h := adicUpperStarUnitIso_comp (l := l) c f
    rw [← cancel_mono (adicUpperStarUnitIso l c).inv, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at h
    rw [Functor.map_comp, reassoc_of% h, reassoc_of% adicUpperStarCongr_hom_app_unit_comp]
  have key {W' : Scheme.{u}} (a b : W' ⟶ W) (w : W' ⟶ T) (ha : w = a ≫ f) (hb : w = b ≫ f)
      [WeaklyEtale a] [WeaklyEtale b] :
      (adicUpperStarCongr l ha).hom.app (unit l T) ≫ (adicUpperStarComp l a f).hom.app _ ≫
          (a)^*ᵃ[l].map ((adicUpperStarUnitIso l f).hom ≫ v) ≫
            (adicUpperStarComp l a f).inv.app M ≫ (adicUpperStarCongr l ha).inv.app M =
        (adicUpperStarCongr l hb).hom.app (unit l T) ≫ (adicUpperStarComp l b f).hom.app _ ≫
          (b)^*ᵃ[l].map ((adicUpperStarUnitIso l f).hom ≫ v) ≫
            (adicUpperStarComp l b f).inv.app M ≫ (adicUpperStarCongr l hb).inv.app M := by
    have hab : a ≫ f = b ≫ f := ha.symm.trans hb
    have qa : a ≫ f = w := ha.symm
    have qb : b ≫ f = w := hb.symm
    have e := hv a b hab
    rw [adicUpperStarCompIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      NatTrans.comp_app] at e
    rw [reassoc_of% E₁ a w ha, reassoc_of% E₁ b w hb, ← reassoc_of% e, Iso.hom_inv_id_app_assoc,
      adicUpperStarCongr_inv_app ha qa, adicUpperStarCongr_inv_app hb qb,
      adicUpperStarCongr_hom_app_trans hab qb qa]
  obtain ⟨φ', hφ'⟩ := ProEtale.exists_hom_of_upperStar f inferInstance
    (adicConstantSheaf l T) M.X (upperStarAdicConstantSheafHom l f ≫ v.hom)
    (fun a b w ha hb _ _ _ ↦ by
      have h := congrArg (fun φ ↦ φ.hom) (key a b w ha hb)
      simp only [Mod.comp_hom', adicUpperStarComp_hom_app_hom, adicUpperStarComp_inv_app_hom,
        adicUpperStarCongr_hom_app_hom, adicUpperStarCongr_inv_app_hom,
        adicUpperStar_map_hom] at h
      simp only [ProEtale.upperStarComp', Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
        Category.assoc]
      exact h)
  -- the descended morphism, through the image of `1`
  obtain ⟨w, hw⟩ := (bijective_globalSectionOfModHom M).2
    (((Sheaf.Γ _ _).map φ').hom (oneGlobalSection (l := l) T))
  refine ⟨w, (bijective_globalSectionOfModHom _).1 ?_⟩
  rw [← globalSectionsToUpperStar_globalSectionOfModHom, hw, globalSectionOfModHom_eq]
  have n := congrArg (fun ψ ↦ ψ.hom (oneGlobalSection (l := l) T))
    ((globalSectionsToUpperStar (WeilCoefficients.{u} l) f).naturality φ')
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.comp_map] at n
  rw [n, hφ', Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  exact Γ_map_adicUpperStarUnitIso_globalSectionsToUpperStar_oneGlobalSection (l := l) f

/-- **Descent of trivialisations.** Let `f : W ⟶ T` be weakly étale, surjective and
quasi-compact, `M` an `ℓ`-adic sheaf on `T` and `ε : f^* M ≅ ℚ̄_ℓ,Wⁿ` a trivialisation whose
transition matrix on `W ×_T W` is the identity. Then `M ≅ ℚ̄_ℓ,Tⁿ`. -/
theorem nonempty_iso_of_transitionMatrix_eq_one (f : W ⟶ T) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {M : AdicSheaf l T} {n : ℕ}
    (ε : (f)^*ᵃ[l].obj M ≅ ⨁ fun _ : Fin n ↦ unit l W)
    (hε : transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition = 1) :
    Nonempty (M ≅ ⨁ fun _ : Fin n ↦ unit l T) := by
  have hι (g : W ⟶ T) (i : Fin n) :
      biproduct.ι (fun _ : Fin n ↦ unit l W) i ≫ (freeUpperStarIso l (Fin n) g).inv =
        (adicUpperStarUnitIso l g).inv ≫
          (g)^*ᵃ[l].map (biproduct.ι (fun _ : Fin n ↦ unit l T) i) := by
    simp [freeUpperStarIso]
  have hι' {P : Scheme.{u}} (g : P ⟶ W) (i : Fin n) :
      biproduct.ι (fun _ : Fin n ↦ unit l P) i ≫ (freeUpperStarIso l (Fin n) g).inv =
        (adicUpperStarUnitIso l g).inv ≫
          (g)^*ᵃ[l].map (biproduct.ι (fun _ : Fin n ↦ unit l W) i) := by
    simp [freeUpperStarIso]
  -- the transition isomorphisms are identities
  have htr {W' : Scheme.{u}} (a b : W' ⟶ W) [WeaklyEtale a] (hab : a ≫ f = b ≫ f) :
      transitionHom ε a b hab = 𝟙 _ := by
    let c : W' ⟶ pullback f f := pullback.lift a b hab
    have hc₁ : c ≫ pullback.fst f f = a := pullback.lift_fst _ _ _
    have hc₂ : c ≫ pullback.snd f f = b := pullback.lift_snd _ _ _
    have : WeaklyEtale (c ≫ pullback.fst f f) := by rw [hc₁]; infer_instance
    have : WeaklyEtale c := WeaklyEtale.of_comp _ (pullback.fst f f)
    have hab' : (c ≫ pullback.fst f f) ≫ f = (c ≫ pullback.snd f f) ≫ f := by rw [hc₁, hc₂, hab]
    apply unitMatrix_injective
    rw [← transitionMatrix, transitionMatrix_congr ε hc₁.symm hc₂.symm hab hab',
      transitionMatrix_comp ε c _ _ pullback.condition hab', hε,
      Matrix.map_one _ (map_zero _) (Subtype.ext (ContinuousMap.ext fun _ ↦ rfl)), unitMatrix_id]
  have htr' {W' : Scheme.{u}} (a b : W' ⟶ W) [WeaklyEtale a] (hab : a ≫ f = b ≫ f) :
      (trivPull f ε a).inv ≫ (adicUpperStarCongr l hab).hom.app M = (trivPull f ε b).inv := by
    have h := htr a b hab
    rw [← cancel_mono (trivPull f ε b).hom, Iso.inv_hom_id, Category.assoc]
    rw [transitionHom_eq] at h
    exact h
  -- the columns of `ε⁻¹` descend
  have hdesc (i : Fin n) : ∃ w : unit l T ⟶ M, (adicUpperStarUnitIso l f).inv ≫
      (f)^*ᵃ[l].map w = biproduct.ι (fun _ : Fin n ↦ unit l W) i ≫ ε.inv := by
    refine exists_upperStar_map_eq_of_cover f _ fun {W'} a b _ _ hab ↦ ?_
    have hp (p : W' ⟶ W) : biproduct.ι (fun _ : Fin n ↦ unit l W') i ≫
        (trivPull f ε p).inv = (adicUpperStarUnitIso l p).inv ≫
          (p)^*ᵃ[l].map (biproduct.ι (fun _ : Fin n ↦ unit l W) i ≫ ε.inv) ≫
            (adicUpperStarComp l p f).inv.app M := by
      rw [trivPull, Iso.trans_inv, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
        Functor.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% hι' p i]
    rw [adicUpperStarCompIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      NatTrans.comp_app]
    rw [← reassoc_of% hp a, reassoc_of% htr' a b hab, reassoc_of% hp b, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  choose w hw using hdesc
  let φ : (⨁ fun _ : Fin n ↦ unit l T) ⟶ M := biproduct.desc w
  have hφ : (freeUpperStarIso l (Fin n) f).inv ≫ (f)^*ᵃ[l].map φ = ε.inv := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [reassoc_of% hι f i, ← Functor.map_comp, biproduct.ι_desc, hw]
  have : IsIso ((f)^*ᵃ[l].map φ) := by
    rw [show (f)^*ᵃ[l].map φ = (freeUpperStarIso l (Fin n) f).hom ≫ ε.inv by
      rw [← hφ, Iso.hom_inv_id_assoc]]
    infer_instance
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ W) (fun _ ↦ f) ∈ Scheme.proetalePrecoverage T := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  have : IsIso φ := isIso_of_isIso_adicUpperStar l (fun _ : Unit ↦ f) hcov φ fun _ ↦ this
  exact ⟨(asIso φ).symm⟩

end AlgebraicGeometry.ProEtale.AdicSheaf
