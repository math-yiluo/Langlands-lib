/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom

/-!
# Morphisms of finite free `ℚ̄_ℓ,V`-modules as matrices of functions

An endomorphism `ψ` of the unit module `ℚ̄_ℓ,V` is multiplication by the locally finite continuous
function `AlgebraicGeometry.ProEtale.AdicSheaf.unitEndFun ψ` on `V`, the image of `1`
(`AlgebraicGeometry.ProEtale.adicConstantSheaf_app_eq_mul`); conversely every such function `a`
gives the endomorphism `AlgebraicGeometry.ProEtale.AdicSheaf.unitMul a`. Composition corresponds to
multiplication. Consequently a morphism `ℚ̄_ℓ,Vⁿ ⟶ ℚ̄_ℓ,Vᵐ` is the same as an `m × n` matrix of
functions (`AlgebraicGeometry.ProEtale.AdicSheaf.unitMatrix`,
`AlgebraicGeometry.ProEtale.AdicSheaf.ofUnitMatrix`), compatibly with composition.

For a weakly étale `g : W ⟶ V`, pulling back an endomorphism of `ℚ̄_ℓ,V` pulls back its function
along `g` (`AlgebraicGeometry.ProEtale.adicConstantSheafEndFun_adicUpperStar`): on sections the
comparison `g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W` is the identity (`AlgebraicGeometry.ProEtale.
upperStarIsoLocalizationRestriction_inv_app_comp_adicUpperStarUnitIso`).
-/

@[expose] public section

universe w

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T]

/-- Evaluation of locally finite functions at a point. -/
noncomputable def locallyFiniteFunctionsEval (t : T) :
    locallyFiniteFunctions l T →+* PadicAlgCl l where
  toFun f := f.1 t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma locallyFiniteFunctionsEval_apply (t : T) (f : locallyFiniteFunctions l T) :
    locallyFiniteFunctionsEval t f = f.1 t :=
  rfl

/-- A nowhere vanishing locally finite function is invertible. -/
lemma isUnit_of_forall_ne_zero (f : locallyFiniteFunctions l T) (hf : ∀ t, f.1 t ≠ 0) :
    IsUnit f := by
  have hc : Continuous fun t ↦ (f.1 t)⁻¹ := f.1.continuous.inv₀ hf
  let g : C(T, PadicAlgCl l) := ⟨fun t ↦ (f.1 t)⁻¹, hc⟩
  have hg : g ∈ locallyFiniteFunctions l T := by
    intro x
    obtain ⟨U, hU, hfU⟩ := f.2 x
    refine ⟨U, hU, ?_⟩
    obtain ⟨S, hS⟩ := Module.Finite.iff_fg.1 hfU
    let E := IntermediateField.adjoin ℚ_[l] (S : Set (PadicAlgCl l))
    have : FiniteDimensional ℚ_[l] E := IntermediateField.finiteDimensional_adjoin
      fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hfE : ∀ y ∈ U, f.1 y ∈ E := fun y hy ↦ by
      have : f.1 y ∈ Submodule.span ℚ_[l] (S : Set (PadicAlgCl l)) := by
        rw [hS]; exact Submodule.subset_span ⟨y, hy, rfl⟩
      exact (Submodule.span_le (p := Subalgebra.toSubmodule E.toSubalgebra)).2
        (fun z hz ↦ IntermediateField.subset_adjoin _ _ hz) this
    refine Submodule.finiteDimensional_of_le (S₂ := Subalgebra.toSubmodule E.toSubalgebra) ?_
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact E.inv_mem (hfE y hy)
  have h1 : f * ⟨g, hg⟩ = 1 := Subtype.ext (ContinuousMap.ext fun t ↦ mul_inv_cancel₀ (hf t))
  exact ⟨⟨f, ⟨g, hg⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

section ConstantRank

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The splitting `κ ≃ Fin r ⊕ (κ ∖ range ρ)` along an injection `ρ : Fin r → κ`. -/
noncomputable def sumComplEquiv {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} :=
  (Equiv.sumCompl (· ∈ Set.range ρ)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective ρ hρ).symm (Equiv.refl _))

omit [Fintype κ] in
@[simp]
lemma sumComplEquiv_symm_inl {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) (a : Fin r) :
    (sumComplEquiv ρ hρ).symm (Sum.inl a) = ρ a := by
  simp [sumComplEquiv]

/-- Pulled back along maps into a neighbourhood of a point, a matrix of locally finite functions
of constant rank `r` is equivalent to the matrix `[[1, 0], [0, 0]]` with an `r × r` identity
block. -/
lemma exists_isOpen_eq_mul (M : Matrix κ ι (locallyFiniteFunctions l T)) (r : ℕ)
    (hr : ∀ t, (M.map (locallyFiniteFunctionsEval t)).rank = r) (t₀ : T) :
    ∃ (U : Set T) (ρ : Fin r → κ) (γ : Fin r → ι) (hρ : Function.Injective ρ)
      (hγ : Function.Injective γ), IsOpen U ∧ t₀ ∈ U ∧
      ∀ {T' : Type w} [TopologicalSpace T'] (g : C(T', T)), Set.range g ⊆ U →
        ∃ (P : Matrix κ κ (locallyFiniteFunctions l T'))
        (Q : Matrix ι ι (locallyFiniteFunctions l T')), IsUnit P.det ∧ IsUnit Q.det ∧
        M.map (locallyFiniteFunctionsCompAlgHom l g) = P * ((Matrix.fromBlocks 1 0 0 0 :
          Matrix (Fin r ⊕ {i // i ∉ Set.range ρ}) (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
            (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q := by
  obtain ⟨ρ, γ, h⟩ := (M.le_rank_map_iff (locallyFiniteFunctionsEval t₀) r).1 (hr t₀).ge
  have hρ : Function.Injective ρ := fun a b hab ↦ by
    by_contra hne
    exact h (by rw [Matrix.det_zero_of_row_eq hne (by ext; simp [hab]), map_zero])
  have hγ : Function.Injective γ := fun a b hab ↦ by
    by_contra hne
    exact h (by rw [Matrix.det_zero_of_column_eq hne (by intro; simp [hab]), map_zero])
  let δ := (M.submatrix ρ γ).det
  refine ⟨{t | δ.1 t ≠ 0}, ρ, γ, hρ, hγ, isOpen_compl_singleton.preimage δ.1.continuous, h,
    fun {T'} _ g hg ↦ ?_⟩
  let M' := M.map (locallyFiniteFunctionsCompAlgHom l g)
  let N := M'.reindex (sumComplEquiv ρ hρ) (sumComplEquiv γ hγ)
  have hN : N = Matrix.fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks N).symm
  have hB : N.toBlocks₁₁ = (M.submatrix ρ γ).map (locallyFiniteFunctionsCompAlgHom l g) := by
    ext a b
    simp [N, M', Matrix.toBlocks₁₁]
  have hBu : IsUnit N.toBlocks₁₁.det := by
    rw [hB]
    erw [← RingHom.map_det (locallyFiniteFunctionsCompAlgHom l g).toRingHom]
    refine isUnit_of_forall_ne_zero _ fun t' ↦ ?_
    exact hg ⟨t', rfl⟩
  let := N.toBlocks₁₁.invertibleOfIsUnitDet hBu
  have hS := Matrix.schur_eq_zero_of_rank_le (fun t' : T' ↦ locallyFiniteFunctionsEval t')
    (fun x hx ↦ Subtype.ext (ContinuousMap.ext hx)) N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁
    N.toBlocks₂₂ (fun t' ↦ ?_)
  · rw [Matrix.invOf_eq_nonsing_inv] at hS
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := Matrix.exists_eq_mul_fromBlocks_one_zero _ _ _ _ hBu hS
    refine ⟨P.reindex (sumComplEquiv ρ hρ).symm (sumComplEquiv ρ hρ).symm,
      Q.reindex (sumComplEquiv γ hγ).symm (sumComplEquiv γ hγ).symm, by simpa using hP,
      by simpa using hQ, ?_⟩
    have hM' : M' = N.reindex (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm := by simp [N]
    change M' = _
    rw [hM', hN, hPQ]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  · rw [← hN]
    have : N.map (locallyFiniteFunctionsEval t') =
        (M.map (locallyFiniteFunctionsEval (g t'))).reindex (sumComplEquiv ρ hρ)
          (sumComplEquiv γ hγ) := by
      ext a b
      rfl
    rw [this, Matrix.rank_reindex, hr, Fintype.card_fin]

end ConstantRank

end PadicAlgCl

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal

universe u

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {V : Scheme.{u}}

/-- A `ℚ̄_ℓ,V`-linear endomorphism of `ℚ̄_ℓ,V` is multiplication by the image of `1`. -/
lemma adicConstantSheaf_app_eq_mul (f : adicConstantSheaf l V ⟶ adicConstantSheaf l V)
    (hf : (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ f =
      adicConstantSheaf l V ◁ f ≫ MonObj.mul) (U : V.ProEtᵒᵖ)
    (s : (adicConstantSheaf l V).obj.obj U) :
    f.hom.app U s = ULift.up (s.down * (f.hom.app U (ULift.up 1)).down) := by
  have h2 := congrArg (fun g ↦ μ (sheafToPresheaf _ _) (adicConstantSheaf l V)
    (adicConstantSheaf l V) ≫ (sheafToPresheaf _ _).map g) hf
  simp only [Functor.map_comp] at h2
  rw [← μ_natural_right_assoc, ← Category.assoc, adicConstantSheaf_μ_comp_map_mul'] at h2
  have h3 := congrArg (fun g ↦ g.app U (s ⊗ₜ (ULift.up 1 : (adicConstantSheaf l V).obj.obj U))) h2
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h3
  erw [adicConstantSheaf_mul_app_tmul, adicConstantSheaf_mul_app_tmul] at h3
  simp only [mul_one] at h3
  exact h3

/-- The terminal object `V ⟶ V` of the small pro-étale site of `V`. -/
noncomputable abbrev proEtTop (V : Scheme.{u}) : V.ProEt := Scheme.ProEt.mk (𝟙 V)

/-- The morphism from any object of the pro-étale site of `V` to `proEtTop V`. -/
noncomputable def toProEtTop (U : V.ProEt) : U ⟶ proEtTop V :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id _)

/-- The function on `V` corresponding to an endomorphism `f` of `ℚ̄_ℓ,V`: the image of `1`. -/
noncomputable def adicConstantSheafEndFun (f : adicConstantSheaf l V ⟶ adicConstantSheaf l V) :
    PadicAlgCl.locallyFiniteFunctions l V :=
  (f.hom.app (op (proEtTop V)) (ULift.up 1)).down

lemma adicConstantSheaf_app_one (f : adicConstantSheaf l V ⟶ adicConstantSheaf l V)
    (U : V.ProEt) :
    f.hom.app (op U) (ULift.up 1) = ULift.up (PadicAlgCl.locallyFiniteFunctionsComp l
      U.hom.base.hom (adicConstantSheafEndFun f)) := by
  have h := NatTrans.naturality_apply f.hom (toProEtTop U).op
    (ULift.up 1 : (adicConstantSheaf l V).obj.obj (op (proEtTop V)))
  have h1 : (adicConstantSheaf l V).obj.map (toProEtTop U).op
      (ULift.up 1 : (adicConstantSheaf l V).obj.obj (op (proEtTop V))) = ULift.up 1 := rfl
  rw [h1] at h
  rw [h]
  rfl

/-- `ℚ̄_ℓ,V`-linear endomorphisms of `ℚ̄_ℓ,V` are determined by their function. -/
lemma adicConstantSheaf_end_ext {f g : adicConstantSheaf l V ⟶ adicConstantSheaf l V}
    (hf : (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ f =
      adicConstantSheaf l V ◁ f ≫ MonObj.mul)
    (hg : (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ g =
      adicConstantSheaf l V ◁ g ≫ MonObj.mul)
    (h : adicConstantSheafEndFun f = adicConstantSheafEndFun g) : f = g := by
  apply Sheaf.hom_ext
  ext U s
  rw [adicConstantSheaf_app_eq_mul f hf, adicConstantSheaf_app_eq_mul g hg,
    adicConstantSheaf_app_one, adicConstantSheaf_app_one, h]

lemma adicConstantSheafEndFun_comp (f g : adicConstantSheaf l V ⟶ adicConstantSheaf l V)
    (hg : (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ g =
      adicConstantSheaf l V ◁ g ≫ MonObj.mul) :
    adicConstantSheafEndFun (f ≫ g) = adicConstantSheafEndFun f * adicConstantSheafEndFun g := by
  change ((g.hom.app _) (f.hom.app _ (ULift.up 1))).down = _
  rw [adicConstantSheaf_app_eq_mul g hg]
  rfl

/-- The product of a function `s` on `T` with the pullback of a function `a` on `V` along
`g : T ⟶ V`. -/
noncomputable def mulPullback {T : Scheme.{u}} (s : PadicAlgCl.locallyFiniteFunctions l T)
    (g : T ⟶ V) (a : PadicAlgCl.locallyFiniteFunctions l V) :
    PadicAlgCl.locallyFiniteFunctions l T :=
  s * PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom a

/-- Multiplication by a locally finite function `a` on `V`, an endomorphism of `ℚ̄_ℓ,V`. -/
noncomputable def adicConstantSheafMul (a : PadicAlgCl.locallyFiniteFunctions l V) :
    adicConstantSheaf l V ⟶ adicConstantSheaf l V :=
  ⟨{ app U := ModuleCat.ofHom
      { toFun s := ULift.up (mulPullback (T := U.unop.left) s.down U.unop.hom a)
        map_add' s t := by
          exact congrArg ULift.up (add_mul _ _ _)
        map_smul' r s := by
          exact congrArg ULift.up (smul_mul_assoc _ _ _) }
     naturality U U' g := by
       ext s
       refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
       change s.down.1 (g.unop.left x) * a.1 (U'.unop.hom x) =
         s.down.1 (g.unop.left x) * a.1 (U.unop.hom (g.unop.left x))
       congr 1
       exact congrArg a.1 (by rw [← MorphismProperty.Over.w g.unop]; rfl) }⟩

lemma adicConstantSheafMul_app (a : PadicAlgCl.locallyFiniteFunctions l V) (U : V.ProEtᵒᵖ)
    (s : (adicConstantSheaf l V).obj.obj U) :
    (adicConstantSheafMul a).hom.app U s =
      ULift.up (mulPullback (T := U.unop.left) s.down U.unop.hom a) :=
  rfl

lemma adicConstantSheafEndFun_mul (a : PadicAlgCl.locallyFiniteFunctions l V) :
    adicConstantSheafEndFun (adicConstantSheafMul a) = a := by
  change 1 * _ = a
  rw [one_mul]
  rfl

lemma adicConstantSheafMul_linear (a : PadicAlgCl.locallyFiniteFunctions l V) :
    (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ adicConstantSheafMul a =
      adicConstantSheaf l V ◁ adicConstantSheafMul a ≫ MonObj.mul := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← μ_natural_right_assoc, ← Category.assoc,
    adicConstantSheaf_μ_comp_map_mul']
  ext U : 2
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change ULift.up ((s.down * t.down) * _) = ULift.up (s.down * (t.down * _))
  rw [mul_assoc]

section Restriction

variable {W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)

lemma localizationRestriction_adicConstantSheaf :
    (localizationRestriction (WeilCoefficients.{u} l) g hg).obj (adicConstantSheaf l V) =
      adicConstantSheaf l W :=
  rfl

/-- For a weakly étale `g`, the comparison `g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W`, seen on the restriction, is the
identity. -/
lemma upperStarIsoLocalizationRestriction_inv_app_comp_adicUpperStarUnitIso :
    (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg).inv.app
        (adicConstantSheaf l V) ≫ (adicUpperStarUnitIso l g).hom.hom =
      eqToHom (localizationRestriction_adicConstantSheaf g hg) := by
  let adj1 := upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g
  let adj2 := localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) g hg
  have key (k : (localizationRestriction (WeilCoefficients.{u} l) g hg).obj
      (adicConstantSheaf l V) ⟶ adicConstantSheaf l W) :
      adj2.homEquiv _ _ k = adj1.homEquiv _ _
        ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg).hom.app _ ≫ k) := by
    rw [adj1.homEquiv_naturality_right, Adjunction.homEquiv_unit]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply (adj2.homEquiv _ _).injective
  erw [key, Iso.hom_inv_id_app_assoc]
  simp only [adicUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  ext U s
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  erw [localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  rfl

lemma adicUpperStarUnitIso_hom_hom_eq :
    (adicUpperStarUnitIso l g).hom.hom =
      (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg).hom.app
        (adicConstantSheaf l V) := by
  rw [← Iso.hom_inv_id_app_assoc (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
    g hg) (adicConstantSheaf l V) (adicUpperStarUnitIso l g).hom.hom,
    upperStarIsoLocalizationRestriction_inv_app_comp_adicUpperStarUnitIso, eqToHom_refl,
    Category.comp_id]

include hg in
/-- The function of the pullback of an endomorphism of `ℚ̄_ℓ,V` along a weakly étale `g` is the
pullback of its function. -/
lemma adicConstantSheafEndFun_adicUpperStar (ψ : AdicSheaf.unit l V ⟶ AdicSheaf.unit l V) :
    adicConstantSheafEndFun ((adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map ψ ≫
      (adicUpperStarUnitIso l g).hom).hom =
      PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom (adicConstantSheafEndFun ψ.hom) := by
  let e := upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg
  let f : adicConstantSheaf l V ⟶ adicConstantSheaf l V := ψ.hom
  have h1 : ((adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map ψ ≫
      (adicUpperStarUnitIso l g).hom).hom =
      (localizationRestriction (WeilCoefficients.{u} l) g hg).map f := by
    have h0 : (adicUpperStarUnitIso l g).hom.hom ≫ ((adicUpperStarUnitIso l g).inv ≫
        (g)^*ᵃ[l].map ψ ≫ (adicUpperStarUnitIso l g).hom).hom =
        ((g)^*ᵃ[l].map ψ).hom ≫ (adicUpperStarUnitIso l g).hom.hom :=
      congrArg (fun k ↦ k.hom) (Iso.hom_inv_id_assoc (adicUpperStarUnitIso l g)
        ((g)^*ᵃ[l].map ψ ≫ (adicUpperStarUnitIso l g).hom))
    rw [adicUpperStarUnitIso_hom_hom_eq g hg] at h0
    rw [← cancel_epi (e.hom.app (adicConstantSheaf l V))]
    refine h0.trans ?_
    exact e.hom.naturality f
  rw [h1]
  change ((f.hom.app _) (ULift.up 1)).down = _
  erw [adicConstantSheaf_app_one]
  rfl

end Restriction

namespace AdicSheaf

/-- The function on `V` of an endomorphism of the unit `ℚ̄_ℓ,V`-module. -/
noncomputable def unitEndFun (ψ : unit l V ⟶ unit l V) : PadicAlgCl.locallyFiniteFunctions l V :=
  adicConstantSheafEndFun ψ.hom

lemma unit_hom_linear (ψ : unit l V ⟶ unit l V) :
    (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ ψ.hom =
      adicConstantSheaf l V ◁ ψ.hom ≫ MonObj.mul :=
  IsModHom.smul_hom (A := adicConstantSheaf l V) (f := ψ.hom)

lemma unitEndFun_injective : Function.Injective (unitEndFun (l := l) (V := V)) :=
  fun ψ ψ' h ↦ Mod.hom_ext _ _ (adicConstantSheaf_end_ext (unit_hom_linear ψ)
    (unit_hom_linear ψ') h)

lemma unitEndFun_comp (ψ ψ' : unit l V ⟶ unit l V) :
    unitEndFun (ψ ≫ ψ') = unitEndFun ψ * unitEndFun ψ' :=
  adicConstantSheafEndFun_comp ψ.hom ψ'.hom (unit_hom_linear ψ')

lemma unitEndFun_id : unitEndFun (𝟙 (unit l V)) = 1 :=
  rfl

lemma unitEndFun_add (ψ ψ' : unit l V ⟶ unit l V) :
    unitEndFun (ψ + ψ') = unitEndFun ψ + unitEndFun ψ' :=
  rfl

lemma unitEndFun_zero : unitEndFun (0 : unit l V ⟶ unit l V) = 0 :=
  rfl

/-- Multiplication by a locally finite function, an endomorphism of the unit module. -/
noncomputable def unitMul (a : PadicAlgCl.locallyFiniteFunctions l V) : unit l V ⟶ unit l V :=
  Mod.homMk (adicConstantSheafMul a) (adicConstantSheafMul_linear a)

lemma unitEndFun_unitMul (a : PadicAlgCl.locallyFiniteFunctions l V) :
    unitEndFun (unitMul a) = a :=
  adicConstantSheafEndFun_mul a

end AdicSheaf

namespace AdicSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

/-- The matrix of functions of a morphism between finite free `ℚ̄_ℓ,V`-modules. -/
noncomputable def unitMatrix (ψ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V) :
    Matrix κ ι (PadicAlgCl.locallyFiniteFunctions l V) :=
  fun i j ↦ unitEndFun (biproduct.ι (fun _ : ι ↦ unit l V) j ≫ ψ ≫
    biproduct.π (fun _ : κ ↦ unit l V) i)

/-- `unitEndFun` as an additive map. -/
noncomputable def unitEndFunAddHom :
    (unit l V ⟶ unit l V) →+ PadicAlgCl.locallyFiniteFunctions l V where
  toFun := unitEndFun
  map_zero' := unitEndFun_zero
  map_add' := unitEndFun_add

lemma unitMatrix_comp (ψ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V)
    (ψ' : (⨁ fun _ : κ ↦ unit l V) ⟶ ⨁ fun _ : ν ↦ unit l V) :
    unitMatrix (ψ ≫ ψ') = unitMatrix ψ' * unitMatrix ψ := by
  refine Matrix.ext fun i j ↦ ?_
  have : biproduct.ι (fun _ : ι ↦ unit l V) j ≫ (ψ ≫ ψ') ≫ biproduct.π (fun _ : ν ↦ unit l V) i =
      ∑ k, (biproduct.ι (fun _ : ι ↦ unit l V) j ≫ ψ ≫ biproduct.π (fun _ : κ ↦ unit l V) k) ≫
        (biproduct.ι (fun _ : κ ↦ unit l V) k ≫ ψ' ≫ biproduct.π (fun _ : ν ↦ unit l V) i) := by
    simp only [Category.assoc, ← Preadditive.comp_sum]
    congr 2
    conv_lhs => rw [← Category.id_comp (ψ' ≫ _), ← biproduct.total, Preadditive.sum_comp]
    simp only [Category.assoc]
  rw [unitMatrix, this]
  change unitEndFunAddHom _ = _
  rw [map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  change unitEndFun _ = _
  rw [unitEndFun_comp, mul_comm]
  rfl

lemma unitMatrix_id [DecidableEq ι] :
    unitMatrix (𝟙 (⨁ fun _ : ι ↦ unit l V)) = 1 := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [unitMatrix, Matrix.one_apply, Category.id_comp]
  by_cases h : i = j
  · subst h
    rw [biproduct.ι_π_self, ite_eq_left rfl]
    rfl
  · rw [biproduct.ι_π_ne _ (Ne.symm h), ite_eq_right h]
    rfl

lemma unitMatrix_injective :
    Function.Injective (unitMatrix (l := l) (V := V) (ι := ι) (κ := κ)) := by
  intro ψ ψ' h
  refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun i ↦ ?_
  have := congrFun (congrFun h i) j
  simpa only [Category.assoc] using unitEndFun_injective this

/-- The morphism between finite free `ℚ̄_ℓ,V`-modules given by a matrix of functions. -/
noncomputable def ofUnitMatrix (N : Matrix κ ι (PadicAlgCl.locallyFiniteFunctions l V)) :
    (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V :=
  biproduct.matrix fun j i ↦ unitMul (l := l) (V := V) (N i j)

lemma unitMatrix_ofUnitMatrix (N : Matrix κ ι (PadicAlgCl.locallyFiniteFunctions l V)) :
    unitMatrix (ofUnitMatrix N) = N := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [unitMatrix, ofUnitMatrix, biproduct.matrix_π, biproduct.ι_desc]
  exact unitEndFun_unitMul _

end AdicSheaf

namespace AdicSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

lemma ofUnitMatrix_unitMatrix (ψ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V) :
    ofUnitMatrix (unitMatrix ψ) = ψ :=
  unitMatrix_injective (unitMatrix_ofUnitMatrix _)

lemma ofUnitMatrix_mul (N₁ : Matrix ν κ (PadicAlgCl.locallyFiniteFunctions l V))
    (N₂ : Matrix κ ι (PadicAlgCl.locallyFiniteFunctions l V)) :
    ofUnitMatrix (N₁ * N₂) = ofUnitMatrix N₂ ≫ ofUnitMatrix N₁ :=
  unitMatrix_injective (by rw [unitMatrix_comp, unitMatrix_ofUnitMatrix, unitMatrix_ofUnitMatrix,
    unitMatrix_ofUnitMatrix])

lemma ofUnitMatrix_one [DecidableEq ι] :
    ofUnitMatrix (1 : Matrix ι ι (PadicAlgCl.locallyFiniteFunctions l V)) = 𝟙 _ :=
  unitMatrix_injective (by rw [unitMatrix_ofUnitMatrix, unitMatrix_id])

lemma isIso_ofUnitMatrix [DecidableEq ι] (P : Matrix ι ι (PadicAlgCl.locallyFiniteFunctions l V))
    (hP : IsUnit P.det) : IsIso (ofUnitMatrix P) :=
  ⟨ofUnitMatrix P⁻¹, by rw [← ofUnitMatrix_mul, Matrix.nonsing_inv_mul _ hP, ofUnitMatrix_one],
    by rw [← ofUnitMatrix_mul, Matrix.mul_nonsing_inv _ hP, ofUnitMatrix_one]⟩

section Block

variable [DecidableEq ι] [DecidableEq κ] {r : ℕ} (ρ : Fin r → κ) (γ : Fin r → ι)
  (hρ : Function.Injective ρ) (hγ : Function.Injective γ)

/-- The morphism `ℚ̄_ℓ^ι ⟶ ℚ̄_ℓ^κ` projecting onto the coordinates in the range of `γ` and
including them as the coordinates in the range of `ρ`. -/
noncomputable def blockMap : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V :=
  biproduct.toSubtype _ (· ∈ Set.range γ) ≫
    (biproduct.whiskerEquiv ((Equiv.ofInjective γ hγ).symm.trans (Equiv.ofInjective ρ hρ))
      (fun _ ↦ Iso.refl (unit l V))).hom ≫ biproduct.fromSubtype _ (· ∈ Set.range ρ)

lemma unitMatrix_blockMap :
    unitMatrix (blockMap (l := l) (V := V) ρ γ hρ hγ) =
      (Matrix.fromBlocks 1 0 0 0 : Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
        (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex (PadicAlgCl.sumComplEquiv ρ hρ).symm
          (PadicAlgCl.sumComplEquiv γ hγ).symm := by
  refine Matrix.ext fun i j ↦ ?_
  obtain ⟨x, rfl⟩ := (PadicAlgCl.sumComplEquiv ρ hρ).symm.surjective i
  obtain ⟨y, rfl⟩ := (PadicAlgCl.sumComplEquiv γ hγ).symm.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rcases y with b | ⟨j, hj⟩
  · have h1 : biproduct.ι (fun _ : ι ↦ unit l V) ((PadicAlgCl.sumComplEquiv γ hγ).symm
        (Sum.inl b)) ≫ blockMap (l := l) (V := V) ρ γ hρ hγ =
        biproduct.ι (fun _ : κ ↦ unit l V) (ρ b) := by
      rw [PadicAlgCl.sumComplEquiv_symm_inl, blockMap,
        biproduct.ι_toSubtype_subtype_assoc (fun _ : ι ↦ unit l V) (· ∈ Set.range γ) ⟨γ b, b, rfl⟩]
      simp only [biproduct.whiskerEquiv_hom, Equiv.trans_apply, Iso.refl_inv,
        biproduct.ι_desc_assoc, Category.assoc, biproduct.ι_fromSubtype,
        Equiv.ofInjective_symm_apply, Equiv.ofInjective_apply]
      exact Category.id_comp _
    rw [unitMatrix, ← Category.assoc, h1]
    rcases x with a | ⟨i, hi⟩
    · rw [PadicAlgCl.sumComplEquiv_symm_inl]
      by_cases hab : b = a
      · subst hab
        rw [biproduct.ι_π_self]
        simp
        rfl
      · rw [biproduct.ι_π_ne _ (hρ.ne hab)]
        simp only [Matrix.fromBlocks_apply₁₁]
        rw [Matrix.one_apply_ne (Ne.symm hab)]
        rfl
    · have : (PadicAlgCl.sumComplEquiv ρ hρ).symm (Sum.inr ⟨i, hi⟩) = i := by
        simp [PadicAlgCl.sumComplEquiv]
      rw [this, biproduct.ι_π_ne _ (fun h ↦ hi ⟨b, h⟩)]
      rfl
  · have : (PadicAlgCl.sumComplEquiv γ hγ).symm (Sum.inr ⟨j, hj⟩) = j := by
      simp [PadicAlgCl.sumComplEquiv]
    rw [unitMatrix, this, blockMap]
    simp only [Category.assoc]
    erw [biproduct.ι_toSubtype_assoc, dite_eq_right hj]
    simp only [Limits.zero_comp]
    rcases x with a | ⟨i, hi⟩ <;> rfl

set_option linter.unusedFintypeInType false in
instance : Mono (biproduct.fromSubtype (fun _ : κ ↦ unit l V) (· ∈ Set.range ρ)) :=
  mono_of_mono_fac (biproduct.fromSubtype_toSubtype _ _)

set_option linter.unusedFintypeInType false in
instance : Epi (biproduct.toSubtype (fun _ : ι ↦ unit l V) (· ∈ Set.range γ)) :=
  epi_of_epi_fac (biproduct.fromSubtype_toSubtype _ _)

variable {ρ γ hρ hγ} in
lemma eq_blockMap_of_unitMatrix_eq
    (ψ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V)
    (P : Matrix κ κ (PadicAlgCl.locallyFiniteFunctions l V))
    (Q : Matrix ι ι (PadicAlgCl.locallyFiniteFunctions l V))
    (h : unitMatrix ψ = P * (Matrix.fromBlocks 1 0 0 0 : Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
        (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex (PadicAlgCl.sumComplEquiv ρ hρ).symm
          (PadicAlgCl.sumComplEquiv γ hγ).symm * Q) :
    ψ = ofUnitMatrix Q ≫ blockMap ρ γ hρ hγ ≫ ofUnitMatrix P := by
  rw [← ofUnitMatrix_unitMatrix ψ, h, ofUnitMatrix_mul, ofUnitMatrix_mul,
    ← unitMatrix_blockMap (l := l) (V := V) ρ γ hρ hγ, ofUnitMatrix_unitMatrix]

/-- The kernel of the block map is free on the coordinates outside the range of `γ`. -/
noncomputable def kernelBlockMapIso :
    kernel (blockMap (l := l) (V := V) ρ γ hρ hγ) ≅
      ⨁ Subtype.restrict (· ∈ Set.range γ)ᶜ (fun _ : ι ↦ unit l V) :=
  kernelCompMono _ _ ≪≫ kernelBiproductToSubtypeIso _ _

/-- The cokernel of the block map is free on the coordinates outside the range of `ρ`. -/
noncomputable def cokernelBlockMapIso :
    cokernel (blockMap (l := l) (V := V) ρ γ hρ hγ) ≅
      ⨁ Subtype.restrict (· ∈ Set.range ρ)ᶜ (fun _ : κ ↦ unit l V) :=
  (cokernelIsoOfEq (Category.assoc _ _ _).symm) ≪≫ cokernelEpiComp _ _ ≪≫
    cokernelBiproductFromSubtypeIso _ _

end Block

end AdicSheaf

namespace AdicSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ : Type} [Fintype ι] [Fintype κ] {W : Scheme.{u}}

variable (l ι) in
/-- The pullback of a finite free module is finite free. -/
noncomputable def freeUpperStarIso (g : W ⟶ V) :
    (g)^*ᵃ[l].obj (⨁ fun _ : ι ↦ unit l V) ≅ ⨁ fun _ : ι ↦ unit l W :=
  (g)^*ᵃ[l].mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ adicUpperStarUnitIso l g

lemma unitMatrix_adicUpperStar (g : W ⟶ V) [hg : WeaklyEtale g]
    (ψ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V) :
    unitMatrix ((freeUpperStarIso l ι g).inv ≫ (g)^*ᵃ[l].map ψ ≫ (freeUpperStarIso l κ g).hom) =
      (unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom) := by
  refine Matrix.ext fun i j ↦ ?_
  have h1 : biproduct.ι (fun _ : ι ↦ unit l W) j ≫ (freeUpperStarIso l ι g).inv =
      (adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map (biproduct.ι (fun _ : ι ↦ unit l V) j) := by
    simp [freeUpperStarIso]
  have h2 : (freeUpperStarIso l κ g).hom ≫ biproduct.π (fun _ : κ ↦ unit l W) i =
      (g)^*ᵃ[l].map (biproduct.π (fun _ : κ ↦ unit l V) i) ≫ (adicUpperStarUnitIso l g).hom := by
    simp [freeUpperStarIso]
  simp only [unitMatrix, Matrix.map_apply, Category.assoc, h2]
  rw [reassoc_of% h1]
  have := adicConstantSheafEndFun_adicUpperStar g hg
    (biproduct.ι (fun _ : ι ↦ unit l V) j ≫ ψ ≫ biproduct.π (fun _ : κ ↦ unit l V) i)
  simp only [Functor.map_comp, Category.assoc] at this
  exact this

end AdicSheaf

end AlgebraicGeometry.ProEtale
