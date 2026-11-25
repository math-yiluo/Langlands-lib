/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# Sections of lisse sheaves are detected by geometric points with varying fields

A variant of
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero`
in which the algebraically closed field of the geometric point may depend on the point of the
scheme: a morphism `ℚ̄_ℓ ⟶ H` into a lisse sheaf vanishes as soon as its global section vanishes
at a geometric point over every point. This applies to schemes which are not of finite type over
a field, such as weakly étale schemes over a curve, whose residue fields do not embed into a single
algebraically closed field of bounded size.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **A morphism `ℚ̄_ℓ ⟶ H` into a lisse sheaf with enough vanishing stalks vanishes**, the
geometric points being allowed to take values in different algebraically closed fields. The proof
is that of
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero`:
the rank of the column of locally finite functions representing `β` on a trivialising cover
descends to `Y`, is constant along specializations and vanishes at the images of the geometric
points. -/
theorem IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero' {Y : Scheme.{u}}
    {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) (β : AdicSheaf.unit l Y ⟶ H)
    (h : ∀ y : Y, ∃ (η : Y) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (s : Spec (.of K) ⟶ Y), η ⤳ y ∧ η ⤳ s.base (IsLocalRing.closedPoint K) ∧
      ((globalSectionsToUpperStar _ s).app H.X).hom (globalSectionOfModHom β) = 0) :
    β = 0 := by
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  let eU (i : ι) : (f i)^*ᵃ[l].obj (AdicSheaf.unit l Y) ≅
      ⨁ fun _ : Fin 1 ↦ AdicSheaf.unit l (V i) :=
    adicUpperStarUnitIso l (f i) ≪≫ unitFreeIso l (V i)
  let M (i : ι) := AdicSheaf.unitMatrix ((eU i).inv ≫ (f i)^*ᵃ[l].map β ≫ (e i).some.hom)
  let rk (i : ι) (v : V i) : ℕ := ((M i).map (PadicAlgCl.locallyFiniteFunctionsEval v)).rank
  have hfc (i i' : ι) (v : V i) (v' : V i') (hvv' : f i v = f i' v') : rk i v = rk i' v' :=
    AdicSheaf.rank_eq_of_apply_eq β (f i) (f i') (eU i) (e i).some (eU i') (e i').some v v' hvv'
  have hspec (i : ι) {v₀ v : V i} (hv : v₀ ⤳ v) : rk i v₀ = rk i v := by
    have : (M i).map (PadicAlgCl.locallyFiniteFunctionsEval v₀) =
        (M i).map (PadicAlgCl.locallyFiniteFunctionsEval v) := by
      ext a b
      exact (hv.map ((M i) a b).1.continuous).eq
    simp only [rk, this]
  have hsurj : ∀ y, ∃ i, y ∈ Set.range (f i) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hR)).1
  choose kk vv hvv using hsurj
  let Rk (y : Y) : ℕ := rk (kk y) (vv y)
  have hRk (i : ι) (v : V i) : Rk (f i v) = rk i v := hfc _ _ _ _ (hvv _)
  have hgen {η y : Y} (hηy : η ⤳ y) : Rk η = Rk y := by
    have hg : GeneralizingMap (f (kk y)) := Flat.generalizingMap _
    obtain ⟨v₀, hv₀, hfv₀⟩ := hg (show η ⤳ (f (kk y)) (vv y) by rw [hvv]; exact hηy)
    rw [← hfv₀, hRk]
    exact hspec _ hv₀
  have hstalk (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Y)
      (hs : ((globalSectionsToUpperStar _ s).app H.X).hom (globalSectionOfModHom β) = 0) :
      Rk (s.base (IsLocalRing.closedPoint K)) = 0 := by
    obtain ⟨i, v, hv⟩ : ∃ i v, f i v = s.base (IsLocalRing.closedPoint K) := ⟨_, _, hvv _⟩
    obtain ⟨t, ht⟩ := exists_comp_eq_of_weaklyEtale (f i) s ⟨v, hv⟩
    have hpt : f i (t.base (IsLocalRing.closedPoint K)) = s.base (IsLocalRing.closedPoint K) := by
      rw [← Scheme.Hom.comp_apply, ht]
    rw [← hpt, hRk]
    suffices hM : (M i).map (PadicAlgCl.locallyFiniteFunctionsEval
        (t.base (IsLocalRing.closedPoint K))) = 0 by
      simp only [rk, hM, Matrix.rank_zero]
    refine Matrix.ext fun a b ↦ ?_
    obtain rfl : b = 0 := Subsingleton.elim _ _
    let ψ : AdicSheaf.unit l (V i) ⟶ AdicSheaf.unit l (V i) :=
      (adicUpperStarUnitIso l (f i)).inv ≫ (f i)^*ᵃ[l].map β ≫ (e i).some.hom ≫
        biproduct.π (fun _ : Fin (n i) ↦ AdicSheaf.unit l (V i)) a
    have hMab : M i a 0 = AdicSheaf.unitEndFun ψ := by
      simp only [M, AdicSheaf.unitMatrix, eU, Iso.trans_inv, Category.assoc, ψ]
      rw [← Category.assoc (biproduct.ι _ 0), biproduct_ι_unitFreeIso_inv, Category.id_comp]
    -- the section `b = β(1)` and its restrictions
    set b := globalSectionOfModHom β
    rw [← ht] at hs
    have c1 := congrArg (fun φ ↦ φ.hom b) (globalSectionsToUpperStar_comp _ t (f i) H.X)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at c1
    rw [hs, map_zero] at c1
    have e2 := (globalSectionsToUpperStar_globalSectionOfModHom (f i) β).trans
      (globalSectionOfModHom_eq _)
    let φa := ((e i).some.hom ≫ biproduct.π (fun _ : Fin (n i) ↦ AdicSheaf.unit l (V i)) a).hom
    have e3 : ((Sheaf.Γ _ _).map φa).hom (((globalSectionsToUpperStar _ (f i)).app H.X).hom b) =
        adicConstantGlobalSection (AdicSheaf.unitEndFun ψ) := by
      refine (congrArg _ e2).trans ?_
      refine Eq.trans ?_ (Γ_map_hom_oneGlobalSection ψ)
      have := congrArg (fun φ ↦ φ.hom (oneGlobalSection (V i)))
        ((Sheaf.Γ (Scheme.ProEt.topology (V i)) (WeilCoefficients.{u} l)).map_comp
          ((adicUpperStarUnitIso l (f i)).inv ≫ (f i)^*ᵃ[l].map β).hom φa)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      exact this.symm
    have e4 : ((globalSectionsToUpperStar _ t).app (adicConstantSheaf l (V i))).hom
        (adicConstantGlobalSection (AdicSheaf.unitEndFun ψ)) = 0 := by
      have n := congrArg (fun φ ↦ φ.hom (((globalSectionsToUpperStar _ (f i)).app H.X).hom b))
        ((globalSectionsToUpperStar _ t).naturality φa)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.comp_map] at n
      exact (congrArg ((globalSectionsToUpperStar _ t).app (adicConstantSheaf l (V i))).hom
        e3).symm.trans (n.trans ((congrArg _ c1.symm).trans (map_zero _)))
    have e5 := globalSectionsToUpperStar_adicConstantGlobalSection (l := l) t
      (AdicSheaf.unitEndFun ψ)
    rw [e4, map_zero] at e5
    have e6 : PadicAlgCl.locallyFiniteFunctionsComp l t.base.hom (AdicSheaf.unitEndFun ψ) = 0 :=
      adicConstantGlobalSection_injective (e5.symm.trans (map_zero _).symm)
    have e7 := congrArg (fun c ↦ c.1 (IsLocalRing.closedPoint K)) e6
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [hMab]
    exact e7
  have hzero (i : ι) : (f i)^*ᵃ[l].map β = 0 := by
    have hM : M i = 0 := by
      refine Matrix.ext fun a b ↦ Subtype.ext (ContinuousMap.ext fun v ↦ ?_)
      have h0 : rk i v = 0 := by
        obtain ⟨η, K, _, _, s, hη, hηs, hs⟩ := h (f i v)
        rw [← hRk, ← hgen hη, hgen hηs]
        exact hstalk K s hs
      have : (M i).map (PadicAlgCl.locallyFiniteFunctionsEval v) = 0 := by
        have h0' : ((M i).map (PadicAlgCl.locallyFiniteFunctionsEval v)).rank = 0 := h0
        rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0'
        exact Matrix.toLin'.injective (by rw [map_zero]; exact h0')
      exact congrArg (fun N ↦ N a b) this
    have : (eU i).inv ≫ (f i)^*ᵃ[l].map β ≫ (e i).some.hom = 0 := by
      apply AdicSheaf.unitMatrix_injective
      change M i = _
      rw [hM]
      refine Matrix.ext fun a b ↦ ?_
      simp [AdicSheaf.unitMatrix, AdicSheaf.unitEndFun_zero]
    simpa using this
  exact eq_zero_of_adicUpperStar_map_eq_zero f hR β hzero


end AlgebraicGeometry.ProEtale
