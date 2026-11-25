/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# Sections of lisse `ℓ`-adic sheaves at geometric points

The restriction of a section of the constant `ℓ`-adic sheaf `ℚ̄_ℓ,V`, a locally finite
continuous function `c` on `V`, along an arbitrary morphism `g : W ⟶ V` is the function `c ∘ g`
(`AlgebraicGeometry.ProEtale.globalSectionsToUpperStar_adicConstantGlobalSection`): this is how
`g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W` was constructed.

For a lisse sheaf `H` on `Y`, a morphism `β : ℚ̄_ℓ ⟶ H`, the same as a global section of `H`,
becomes a column of locally finite functions on the members of a trivialising pro-étale cover.
Its rank at a point of a member descends to `Y`
(`AlgebraicGeometry.ProEtale.AdicSheaf.rank_eq_of_apply_eq`), and is constant along
specializations: continuous functions to the Hausdorff space `ℚ̄_ℓ` are constant along
specializations, and flat morphisms lift generizations. At the image of a geometric point
`s : Spec K ⟶ Y`, `K` algebraically closed, at which the section vanishes, the rank vanishes.
Hence a section of `H` vanishing at a geometric point over every irreducible component of a
Noetherian `Y` vanishes
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero`).

Similarly the rank of a trivialisation of `H` descends to `Y` and is constant along
specializations, so a nonzero lisse sheaf on a quasi-compact scheme has nonzero stalks at the
geometric points over some closed point
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_isClosed_nontrivial_globalSections_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {V W : Scheme.{u}}

/-- The global section of `ℚ̄_ℓ,V` given by a locally finite continuous function on `V`. -/
noncomputable def adicConstantGlobalSection (c : PadicAlgCl.locallyFiniteFunctions l V) :
    (Sheaf.Γ (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)).obj (adicConstantSheaf l V) :=
  ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)
    (Scheme.ProEt.isTerminalMkId V)).inv.app (adicConstantSheaf l V)).hom (ULift.up c)

/-- A section of `ℚ̄_ℓ,V` is determined by its function. -/
lemma adicConstantGlobalSection_injective :
    Function.Injective (adicConstantGlobalSection (l := l) (V := V)) := by
  intro c c' h
  have := congrArg ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)
    (Scheme.ProEt.isTerminalMkId V)).hom.app (adicConstantSheaf l V)).hom h
  simp only [adicConstantGlobalSection, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    Iso.inv_hom_id_app, ModuleCat.hom_id, LinearMap.id_apply] at this
  exact congrArg ULift.down this

/-- The unit section of `ℚ̄_ℓ,V` is the constant function `1`. -/
lemma oneGlobalSection_eq : oneGlobalSection (l := l) V = adicConstantGlobalSection 1 := by
  rw [oneGlobalSection, globalSectionOfHom_eq]
  congr 1
  rw [adicConstantSheaf_ε_comp_map_one']
  exact (adicConstantSheaf_one_app (X := V) (U := op (Scheme.ProEt.mk (𝟙 V))) 1).trans
    (by congr 1)

/-- **Restriction of functions.** The restriction along an arbitrary morphism `g : W ⟶ V` of the
section of `ℚ̄_ℓ,V` given by a function `c`, identified with a section of `ℚ̄_ℓ,W` through
`g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W`, is the function `c ∘ g`: the comparison `g^* ℚ̄_ℓ,V ⟶ ℚ̄_ℓ,W` is adjoint to
the precomposition `ℚ̄_ℓ,V ⟶ g_* ℚ̄_ℓ,W`. -/
lemma globalSectionsToUpperStar_adicConstantGlobalSection (g : W ⟶ V)
    (c : PadicAlgCl.locallyFiniteFunctions l V) :
    ((Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l g)).hom
        (((globalSectionsToUpperStar _ g).app (adicConstantSheaf l V)).hom
          (adicConstantGlobalSection c)) =
      adicConstantGlobalSection (PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom c) := by
  have h : (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit.app _ ≫
      (g)_*[_].map (upperStarAdicConstantSheafHom l g) = adicConstantSheafToLowerStar l g := by
    exact ((upperStarLowerStarAdjunction _ g).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have key : (globalSectionsToUpperStar _ g).app (adicConstantSheaf l V) ≫
      (Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l g) =
      (Sheaf.Γ _ _).map (adicConstantSheafToLowerStar l g) ≫
        (globalSectionsLowerStarIso _ g).hom.app (adicConstantSheaf l W) := by
    rw [globalSectionsToUpperStar_app, Category.assoc,
      ← (globalSectionsLowerStarIso _ g).hom.naturality, Functor.comp_map, ← Category.assoc,
      ← Functor.map_comp, h]
  have e := congrArg (fun φ ↦ φ.hom (adicConstantGlobalSection c)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  refine e.trans ?_
  rw [globalSectionsLowerStarIso_hom_app']
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  unfold adicConstantGlobalSection
  congr 1
  have n := congrArg (fun ψ ↦ ψ.hom (((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology V)
    (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId V)).inv.app (adicConstantSheaf l V)).hom
      (ULift.up c))) ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology V)
        (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId V)).hom.naturality
          (adicConstantSheafToLowerStar l g))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n
  refine (congrArg _ n).trans ?_
  have hi := congrArg (fun ψ ↦ ψ.hom (ULift.up c : (adicConstantSheaf l V).obj.obj
    (op (Scheme.ProEt.mk (𝟙 V))))) ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology V)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId V)).inv_hom_id_app
        (adicConstantSheaf l V))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at hi
  erw [hi]
  refine adicConstantSheaf_ext fun y ↦ ?_
  change c.1 (pullback.fst (𝟙 V) g ((overPullbackObjMkIdIso g).inv.left y)) = c.1 (g y)
  have h₁ : (overPullbackObjMkIdIso g).inv.left ≫ pullback.fst (𝟙 V) g = g := by
    have h₂ : (overPullbackObjMkIdIso g).inv.left ≫ pullback.snd (𝟙 V) g = 𝟙 W :=
      IsIso.inv_hom_id (pullback.snd (𝟙 V) g)
    rw [← Category.comp_id (pullback.fst (𝟙 V) g), pullback.condition, ← Category.assoc, h₂,
      ]
    exact Category.id_comp g
  exact congrArg (fun a : W ⟶ V ↦ c.1 (a.base y)) h₁

/-- The image of the unit section of `ℚ̄_ℓ,V` under an endomorphism `ψ` of the unit module is the
section given by the function of `ψ`. -/
lemma Γ_map_hom_oneGlobalSection (ψ : AdicSheaf.unit l V ⟶ AdicSheaf.unit l V) :
    ((Sheaf.Γ _ _).map ψ.hom).hom (oneGlobalSection V) =
      adicConstantGlobalSection (AdicSheaf.unitEndFun ψ) := by
  rw [oneGlobalSection_eq]
  have n := congrArg (fun φ ↦ φ.hom (ULift.up 1 : (adicConstantSheaf l V).obj.obj
    (op (Scheme.ProEt.mk (𝟙 V))))) ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology V)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId V)).inv.naturality ψ.hom)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n
  exact n.symm

/-- The restriction of the unit section of `ℚ̄_ℓ,V` along `g : W ⟶ V` is the unit section of
`ℚ̄_ℓ,W`. -/
lemma Γ_map_adicUpperStarUnitIso_globalSectionsToUpperStar_oneGlobalSection (g : W ⟶ V) :
    ((Sheaf.Γ _ _).map (adicUpperStarUnitIso l g).hom.hom).hom
        (((globalSectionsToUpperStar _ g).app (adicConstantSheaf l V)).hom (oneGlobalSection V)) =
      oneGlobalSection W := by
  rw [oneGlobalSection_eq, oneGlobalSection_eq]
  exact (globalSectionsToUpperStar_adicConstantGlobalSection g 1).trans (by congr 1)

/-- The restriction along `g : W ⟶ V` of the global section `β(1)` of a morphism
`β : ℚ̄_ℓ ⟶ M` of sheaves of modules is the global section of the pullback of `β`. -/
lemma globalSectionsToUpperStar_globalSectionOfModHom (g : W ⟶ V) {M : AdicSheaf l V}
    (β : AdicSheaf.unit l V ⟶ M) :
    ((globalSectionsToUpperStar _ g).app M.X).hom (globalSectionOfModHom β) =
      globalSectionOfModHom ((adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map β) := by
  have hhi : (adicUpperStarUnitIso l g).hom.hom ≫ (adicUpperStarUnitIso l g).inv.hom =
      𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id]; rfl
  have e1 : ((globalSectionsToUpperStar _ g).app (adicConstantSheaf l V)).hom
      (oneGlobalSection V) = ((Sheaf.Γ _ _).map (adicUpperStarUnitIso l g).inv.hom).hom
        (oneGlobalSection W) := by
    have h2 := congrArg ((Sheaf.Γ _ _).map (adicUpperStarUnitIso l g).inv.hom).hom
      (Γ_map_adicUpperStarUnitIso_globalSectionsToUpperStar_oneGlobalSection (l := l) g)
    have h3 := congrArg (fun φ ↦ φ.hom (((globalSectionsToUpperStar _ g).app
      (adicConstantSheaf l V)).hom (oneGlobalSection V)))
        (((Sheaf.Γ _ _).map_comp _ _).symm.trans
          ((congrArg (Sheaf.Γ _ _).map hhi).trans ((Sheaf.Γ _ _).map_id _)))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at h3
    exact h3.symm.trans h2
  have e2 : ((globalSectionsToUpperStar _ g).app M.X).hom (globalSectionOfModHom β) =
      ((Sheaf.Γ _ _).map ((adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map β).hom).hom
        (oneGlobalSection W) := by
    have n := congrArg (fun φ ↦ φ.hom (oneGlobalSection V))
      ((globalSectionsToUpperStar _ g).naturality β.hom)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.comp_map] at n
    refine (congrArg _ (globalSectionOfModHom_eq β)).trans (n.trans ?_)
    refine (congrArg _ e1).trans ?_
    have := congrArg (fun φ ↦ φ.hom (oneGlobalSection W))
      ((Sheaf.Γ (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)).map_comp
        (adicUpperStarUnitIso l g).inv.hom ((g)^*ᵃ[l].map β).hom)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this.symm
  exact e2.trans (globalSectionOfModHom_eq _).symm

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Restrictions along the members of a pro-étale cover are jointly faithful. -/
lemma eq_zero_of_adicUpperStar_map_eq_zero {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X) {M N : AdicSheaf l X}
    (φ : M ⟶ N) (h : ∀ i, (g i)^*ᵃ[l].map φ = 0) : φ = 0 := by
  have : IsIso (kernel.ι φ) := by
    refine isIso_of_isIso_adicUpperStar l g hg _ fun i ↦ ?_
    have e : (g i)^*ᵃ[l].map (kernel.ι φ) =
        (PreservesKernel.iso (g i)^*ᵃ[l] φ).hom ≫ kernel.ι ((g i)^*ᵃ[l].map φ) := by simp
    rw [e]
    have : IsIso (kernel.ι ((g i)^*ᵃ[l].map φ)) := kernel.ι_of_zero (h i)
    infer_instance
  rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]

variable (l) in
/-- The unit module as a free module of rank one. -/
noncomputable def unitFreeIso (W : Scheme.{u}) :
    AdicSheaf.unit l W ≅ ⨁ fun _ : Fin 1 ↦ AdicSheaf.unit l W :=
  (biproduct.isoProduct (fun _ : Fin 1 ↦ AdicSheaf.unit l W) ≪≫ productUniqueIso _).symm

lemma biproduct_ι_unitFreeIso_inv (W : Scheme.{u}) :
    biproduct.ι (fun _ : Fin 1 ↦ AdicSheaf.unit l W) 0 ≫ (unitFreeIso l W).inv = 𝟙 _ := by
  simp [unitFreeIso]


/-- The lift `t : Spec K ⟶ V` of a point `s : Spec K ⟶ Y` with values in an algebraically closed
field through a weakly étale `f : V ⟶ Y` whose image contains the image of `s`. -/
lemma exists_comp_eq_of_weaklyEtale {Y V : Scheme.{u}} (f : V ⟶ Y) [WeaklyEtale f]
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Y)
    (hs : s.base (IsLocalRing.closedPoint K) ∈ Set.range f.base) :
    ∃ t : Spec (.of K) ⟶ V, t ≫ f = s := by
  obtain ⟨v, hv⟩ := hs
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := s) v
    (IsLocalRing.closedPoint K) hv
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (pullback.snd f s) w
  exact ⟨σ ≫ pullback.fst f s, by rw [Category.assoc, pullback.condition, ← Category.assoc, hσ,
    Category.id_comp]⟩

/-- **A morphism `ℚ̄_ℓ ⟶ H` into a lisse sheaf with enough vanishing stalks vanishes.** Let
`β : ℚ̄_ℓ ⟶ H`, with global section `b = β(1)`. Suppose every point `y` of `Y` is related, in the
equivalence relation generated by specialization, to the image of a geometric point `s` at
which the stalk of `b` vanishes. Then `β = 0`. Trivialising `H` on a pro-étale cover, `β`
becomes a column of locally finite functions, whose rank at a point descends to `Y`
(`AlgebraicGeometry.ProEtale.AdicSheaf.rank_eq_of_apply_eq`). This rank is constant along
specializations, continuous functions to `ℚ̄_ℓ` being constant along specializations and flat
morphisms lifting generizations, and vanishes at the image of `s`
(`AlgebraicGeometry.ProEtale.globalSectionsToUpperStar_adicConstantGlobalSection`). -/
theorem IsAdicLisseSheaf.eq_zero_of_eqvGen_globalSectionsToUpperStar_eq_zero {Y : Scheme.{u}}
    {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) (β : AdicSheaf.unit l Y ⟶ H)
    (K : Type u) [Field K] [IsAlgClosed K]
    (h : ∀ y : Y, ∃ s : Spec (.of K) ⟶ Y,
      Relation.EqvGen (· ⤳ ·) y (s.base (IsLocalRing.closedPoint K)) ∧
      ((globalSectionsToUpperStar _ s).app H.X).hom (globalSectionOfModHom β) = 0) :
    β = 0 := by
  classical
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
  have hstalk (s : Spec (.of K) ⟶ Y)
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
        obtain ⟨s, hys, hs⟩ := h (f i v)
        have hgen' {y y' : Y} (hyy' : Relation.EqvGen (· ⤳ ·) y y') : Rk y = Rk y' := by
          induction hyy' with
          | rel _ _ h => exact hgen h
          | refl => rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
        rw [← hRk, hgen' hys]
        exact hstalk s hs
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

/-- **A morphism `ℚ̄_ℓ ⟶ H` into a lisse sheaf with enough vanishing stalks vanishes.** Let
`β : ℚ̄_ℓ ⟶ H`, with global section `b = β(1)`. Suppose every point `y` of `Y` is a
specialization of a point `η` which also specializes to the image of a geometric point `s` at
which the stalk of `b` vanishes. Then `β = 0`: a special case of
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_eqvGen_globalSectionsToUpperStar_eq_zero`.
-/
theorem IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero {Y : Scheme.{u}}
    {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) (β : AdicSheaf.unit l Y ⟶ H)
    (K : Type u) [Field K] [IsAlgClosed K]
    (h : ∀ y : Y, ∃ (η : Y) (s : Spec (.of K) ⟶ Y), η ⤳ y ∧
      η ⤳ s.base (IsLocalRing.closedPoint K) ∧
      ((globalSectionsToUpperStar _ s).app H.X).hom (globalSectionOfModHom β) = 0) :
    β = 0 := by
  refine hH.eq_zero_of_eqvGen_globalSectionsToUpperStar_eq_zero β K fun y ↦ ?_
  obtain ⟨η, s, hη, hηs, hs⟩ := h y
  exact ⟨s, (Relation.EqvGen.rel _ _ hη).symm.trans _ _ _ (.rel _ _ hηs), hs⟩

/-- **A section of a lisse sheaf on a connected noetherian scheme vanishing at one geometric
point vanishes.** The rank of the section is constant along specializations, hence locally
constant (`TopologicalSpace.NoetherianSpace.isLocallyConstant_of_specializes`), hence constant on
the connected space `Y`. -/
theorem IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero_of_preconnectedSpace
    {Y : Scheme.{u}} [NoetherianSpace Y] [PreconnectedSpace Y] {H : AdicSheaf l Y}
    (hH : IsAdicLisseSheaf H) (β : AdicSheaf.unit l Y ⟶ H) (K : Type u) [Field K]
    [IsAlgClosed K] (s : Spec (.of K) ⟶ Y)
    (hs : ((globalSectionsToUpperStar _ s).app H.X).hom (globalSectionOfModHom β) = 0) :
    β = 0 := by
  refine hH.eq_zero_of_eqvGen_globalSectionsToUpperStar_eq_zero β K fun y ↦ ⟨s, ?_, hs⟩
  let r : Setoid Y := Relation.EqvGen.setoid (· ⤳ ·)
  have hc : IsLocallyConstant (Quotient.mk r) :=
    NoetherianSpace.isLocallyConstant_of_specializes fun _ _ h ↦
      Quotient.sound (Relation.EqvGen.rel _ _ h)
  exact Quotient.exact (hc.apply_eq_of_preconnectedSpace _ _)


open ZeroObject in
variable (l) in
/-- On an empty scheme every `ℓ`-adic sheaf vanishes: the empty family covers it. -/
lemma isZero_adicSheaf_of_isEmpty {T : Scheme.{u}} [IsEmpty T] (M : AdicSheaf l T) : IsZero M := by
  have : IsIso (0 : M ⟶ 0) := isIso_of_isIso_adicUpperStar l
    (W := (Empty.elim : Empty → Scheme.{u})) (fun i ↦ i.elim) (by
      exact Scheme.zariskiPrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ isEmptyElim x, fun i ↦ i.elim⟩))
    _ (fun i ↦ i.elim)
  exact (isZero_zero _).of_iso (asIso (0 : M ⟶ 0))

/-- The global sections of `ℚ̄_ℓ` on a nonempty scheme are nonzero. -/
lemma nontrivial_globalSections_adicConstantSheaf (T : Scheme.{u}) [Nonempty T] :
    Nontrivial ((Sheaf.Γ (Scheme.ProEt.topology T) (WeilCoefficients.{u} l)).obj
      (adicConstantSheaf l T)) := by
  refine ⟨⟨adicConstantGlobalSection 1, 0, fun h ↦ ?_⟩⟩
  have h0 : adicConstantGlobalSection (l := l) (V := T) 0 = 0 := map_zero _
  have := adicConstantGlobalSection_injective (h.trans h0.symm)
  obtain ⟨x⟩ := ‹Nonempty T›
  have := congrArg (fun c ↦ c.1 x) this
  simp at this


open ZeroObject in
/-- **A nonzero lisse sheaf has nonzero stalks at a closed point.** Let `H` be a nonzero lisse
sheaf on a quasi-compact scheme `Y`. Then there is a closed point `y` of `Y` such that the stalk
`Γ(Spec K, s^* H)` is nonzero at every geometric point `s` over `y`. Indeed the rank of a
trivialisation of `H` descends to `Y`, is constant along specializations (flat morphisms lift
generizations) and is positive somewhere, `H` being nonzero; the closure of a point of positive
rank contains a closed point. -/
theorem IsAdicLisseSheaf.exists_isClosed_nontrivial_globalSections_upperStar {Y : Scheme.{u}}
    [CompactSpace Y] {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) (hH0 : ¬ IsZero H)
    (K : Type u) [Field K] [IsAlgClosed K] :
    ∃ y : Y, IsClosed {y} ∧ ∀ s : Spec (.of K) ⟶ Y,
      s.base (IsLocalRing.closedPoint K) = y →
        Nontrivial ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((s)^*[_].obj H.X)) := by
  classical
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  -- the rank of the trivialisations descends to `Y`
  have hn (i i' : ι) (v : V i) (v' : V i') (hvv' : f i v = f i' v') : n i = n i' := by
    have := AdicSheaf.rank_eq_of_apply_eq (𝟙 H) (f i) (f i') (e i).some (e i).some (e i').some
      (e i').some v v' hvv'
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id, AdicSheaf.unitMatrix_id, AdicSheaf.unitMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.rank_one, Matrix.rank_one, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  -- some member has a point and positive rank
  obtain ⟨i, v, hi⟩ : ∃ i, ∃ _ : V i, 0 < n i := by
    by_contra! hcon
    have hz (i : ι) : IsZero ((f i)^*ᵃ[l].obj H) := by
      by_cases hV : Nonempty (V i)
      · obtain ⟨v⟩ := hV
        have h0 : n i = 0 := Nat.le_zero.1 (hcon i v)
        refine IsZero.of_iso ?_ (e i).some
        rw [h0]
        exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
          fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩
      · have : IsEmpty (V i) := not_nonempty_iff.1 hV
        exact isZero_adicSheaf_of_isEmpty l _
    have : IsIso (0 : H ⟶ 0) := isIso_of_isIso_adicUpperStar l f hR _ fun i ↦ by
      have hz' : IsZero ((f i)^*ᵃ[l].obj 0) := Functor.map_isZero _ (isZero_zero _)
      rw [(hz i).eq_of_src ((f i)^*ᵃ[l].map 0) ((hz i).iso hz').hom]
      infer_instance
    exact hH0 ((isZero_zero _).of_iso (asIso (0 : H ⟶ 0)))
  -- a closed point in the closure of a point of positive rank
  obtain ⟨y, hy, hyc⟩ := isClosed_closure.exists_closed_singleton
    (S := closure {f i v}) ⟨_, subset_closure rfl⟩
  refine ⟨y, hyc, fun s hs ↦ ?_⟩
  have hsurj : ∀ y, ∃ j, y ∈ Set.range (f j) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hR)).1
  obtain ⟨j, w, hw⟩ := hsurj y
  have hg : GeneralizingMap (f j) := Flat.generalizingMap _
  obtain ⟨w₀, -, hw₀⟩ := hg (show f i v ⤳ f j w by rw [hw]; exact specializes_iff_mem_closure.2 hy)
  have hpos : 0 < n j := (hn j i w₀ v hw₀) ▸ hi
  obtain ⟨t, ht⟩ := exists_comp_eq_of_weaklyEtale (f j) s ⟨w, hw.trans hs.symm⟩
  let E : (s)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin (n j) ↦ AdicSheaf.unit l (Spec (.of K)) :=
    (adicUpperStarCongr l ht.symm).app H ≪≫ AdicSheaf.trivPull (f j) (e j).some t
  let a := biproduct.ι (fun _ : Fin (n j) ↦ AdicSheaf.unit l (Spec (.of K))) ⟨0, hpos⟩ ≫ E.inv
  let b := E.hom ≫ biproduct.π (fun _ : Fin (n j) ↦ AdicSheaf.unit l (Spec (.of K))) ⟨0, hpos⟩
  have hab : a.hom ≫ b.hom = 𝟙 _ := by
    rw [← Mod.comp_hom']
    simp [a, b]
  have : Nonempty (Spec (.of K)) := ⟨IsLocalRing.closedPoint K⟩
  have : Nontrivial ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      (AdicSheaf.unit l (Spec (.of K))).X) :=
    nontrivial_globalSections_adicConstantSheaf (l := l) (Spec (.of K))
  refine Function.Injective.nontrivial (f := ((Sheaf.Γ _ _).map a.hom).hom) fun x x' hxx' ↦ ?_
  have h₁ := congrArg ((Sheaf.Γ _ _).map b.hom).hom hxx'
  have h₂ (z) : ((Sheaf.Γ _ _).map b.hom).hom (((Sheaf.Γ _ _).map a.hom).hom z) = z := by
    have := congrArg (fun φ ↦ φ.hom z) (((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K)))
      (WeilCoefficients.{u} l)).map_comp a.hom b.hom).symm.trans
        ((congrArg (Sheaf.Γ _ _).map hab).trans ((Sheaf.Γ _ _).map_id _)))
    simpa using this
  rwa [h₂, h₂] at h₁

end AlgebraicGeometry.ProEtale
