/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# Morphisms of finite free `Λ_V`-modules as matrices of functions

This is the counterpart, for a coefficient field `Λ` with an ultrametric norm (the case of
interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

An endomorphism `ψ` of the unit module `Λ_V` is multiplication by the continuous
function `AlgebraicGeometry.ProEtale.FieldSheaf.unitEndFun ψ` on `V`, the image of `1`
(`AlgebraicGeometry.ProEtale.fieldConstantSheaf_app_eq_mul`); conversely every such function `a`
gives the endomorphism `AlgebraicGeometry.ProEtale.FieldSheaf.unitMul a`. Composition corresponds to
multiplication. Consequently a morphism `Λ_Vⁿ ⟶ Λ_Vᵐ` is the same as an `m × n` matrix of
functions (`AlgebraicGeometry.ProEtale.FieldSheaf.unitMatrix`,
`AlgebraicGeometry.ProEtale.FieldSheaf.ofUnitMatrix`), compatibly with composition.

For a weakly étale `g : W ⟶ V`, pulling back an endomorphism of `Λ_V` pulls back its function
along `g` (`AlgebraicGeometry.ProEtale.fieldConstantSheafEndFun_fieldUpperStar`): on sections the
comparison `g^* Λ_V ≅ Λ_W` is the identity (`AlgebraicGeometry.ProEtale.
upperStarIsoLocalizationRestriction_inv_app_comp_fieldUpperStarUnitIso`).
-/

@[expose] public section

universe w

open PadicAlgCl (sumComplEquiv sumComplEquiv_symm_inl)

namespace AlgebraicGeometry

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] {T : Type*} [TopologicalSpace T]

/-- Evaluation of continuous functions at a point. -/
noncomputable def fieldFunctionsEval (t : T) :
    fieldFunctions Λ T →+* Λ where
  toFun f := f.1 t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsUltrametricDist Λ] in
@[simp]
lemma fieldFunctionsEval_apply (t : T) (f : fieldFunctions Λ T) :
    fieldFunctionsEval t f = f.1 t :=
  rfl

omit [IsUltrametricDist Λ] in
/-- A nowhere vanishing continuous function is invertible. -/
lemma fieldFunctions_isUnit_of_forall_ne_zero (f : fieldFunctions Λ T) (hf : ∀ t, f.1 t ≠ 0) :
    IsUnit f := by
  have hc : Continuous fun t ↦ (f.1 t)⁻¹ := f.1.continuous.inv₀ hf
  let g : C(T, Λ) := ⟨fun t ↦ (f.1 t)⁻¹, hc⟩
  have hg : g ∈ fieldFunctions Λ T := Algebra.mem_top
  have h1 : f * ⟨g, hg⟩ = 1 := Subtype.ext (ContinuousMap.ext fun t ↦ mul_inv_cancel₀ (hf t))
  exact ⟨⟨f, ⟨g, hg⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

section ConstantRank



variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

omit [IsUltrametricDist Λ] in
/-- Pulled back along maps into a neighbourhood of a point, a matrix of continuous functions
of constant rank `r` is equivalent to the matrix `[[1, 0], [0, 0]]` with an `r × r` identity
block. -/
lemma exists_isOpen_eq_mul_field (M : Matrix κ ι (fieldFunctions Λ T)) (r : ℕ)
    (hr : ∀ t, (M.map (fieldFunctionsEval t)).rank = r) (t₀ : T) :
    ∃ (U : Set T) (ρ : Fin r → κ) (γ : Fin r → ι) (hρ : Function.Injective ρ)
      (hγ : Function.Injective γ), IsOpen U ∧ t₀ ∈ U ∧
      ∀ {T' : Type w} [TopologicalSpace T'] (g : C(T', T)), Set.range g ⊆ U →
        ∃ (P : Matrix κ κ (fieldFunctions Λ T'))
        (Q : Matrix ι ι (fieldFunctions Λ T')), IsUnit P.det ∧ IsUnit Q.det ∧
        M.map (fieldFunctionsCompAlgHom Λ g) = P * ((Matrix.fromBlocks 1 0 0 0 :
          Matrix (Fin r ⊕ {i // i ∉ Set.range ρ}) (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
            (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q := by
  obtain ⟨ρ, γ, h⟩ := (M.le_rank_map_iff (fieldFunctionsEval t₀) r).1 (hr t₀).ge
  have hρ : Function.Injective ρ := fun a b hab ↦ by
    by_contra hne
    exact h (by rw [Matrix.det_zero_of_row_eq hne (by ext; simp [hab]), map_zero])
  have hγ : Function.Injective γ := fun a b hab ↦ by
    by_contra hne
    exact h (by rw [Matrix.det_zero_of_column_eq hne (by intro; simp [hab]), map_zero])
  let δ := (M.submatrix ρ γ).det
  refine ⟨{t | δ.1 t ≠ 0}, ρ, γ, hρ, hγ, isOpen_compl_singleton.preimage δ.1.continuous, h,
    fun {T'} _ g hg ↦ ?_⟩
  let M' := M.map (fieldFunctionsCompAlgHom Λ g)
  let N := M'.reindex (sumComplEquiv ρ hρ) (sumComplEquiv γ hγ)
  have hN : N = Matrix.fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks N).symm
  have hB : N.toBlocks₁₁ = (M.submatrix ρ γ).map (fieldFunctionsCompAlgHom Λ g) := by
    ext a b
    simp [N, M', Matrix.toBlocks₁₁]
  have hBu : IsUnit N.toBlocks₁₁.det := by
    rw [hB]
    erw [← RingHom.map_det (fieldFunctionsCompAlgHom Λ g).toRingHom]
    refine fieldFunctions_isUnit_of_forall_ne_zero _ fun t' ↦ ?_
    exact hg ⟨t', rfl⟩
  let := N.toBlocks₁₁.invertibleOfIsUnitDet hBu
  have hS := Matrix.schur_eq_zero_of_rank_le (fun t' : T' ↦ fieldFunctionsEval t')
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
    have : N.map (fieldFunctionsEval t') =
        (M.map (fieldFunctionsEval (g t'))).reindex (sumComplEquiv ρ hρ)
          (sumComplEquiv γ hγ) := by
      ext a b
      rfl
    rw [this, Matrix.rank_reindex, hr, Fintype.card_fin]

end ConstantRank

end AlgebraicGeometry

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal

universe u

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] {V : Scheme.{u}}

omit [IsUltrametricDist Λ] in
/-- A `Λ_V`-linear endomorphism of `Λ_V` is multiplication by the image of `1`. -/
lemma fieldConstantSheaf_app_eq_mul (f : fieldConstantSheaf Λ V ⟶ fieldConstantSheaf Λ V)
    (hf : (MonObj.mul : fieldConstantSheaf Λ V ⊗ fieldConstantSheaf Λ V ⟶ _) ≫ f =
      fieldConstantSheaf Λ V ◁ f ≫ MonObj.mul) (U : V.ProEtᵒᵖ)
    (s : (fieldConstantSheaf Λ V).obj.obj U) :
    f.hom.app U s = ULift.up (s.down * (f.hom.app U (ULift.up 1)).down) := by
  have h2 := congrArg (fun g ↦ μ (sheafToPresheaf _ _) (fieldConstantSheaf Λ V)
    (fieldConstantSheaf Λ V) ≫ (sheafToPresheaf _ _).map g) hf
  simp only [Functor.map_comp] at h2
  rw [← μ_natural_right_assoc, ← Category.assoc, fieldConstantSheaf_μ_comp_map_mul'] at h2
  have h3 := congrArg (fun g ↦ g.app U (s ⊗ₜ (ULift.up 1 : (fieldConstantSheaf Λ V).obj.obj U))) h2
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h3
  erw [fieldConstantSheaf_mul_app_tmul, fieldConstantSheaf_mul_app_tmul] at h3
  simp only [mul_one] at h3
  exact h3

/-- The function on `V` corresponding to an endomorphism `f` of `Λ_V`: the image of `1`. -/
noncomputable def fieldConstantSheafEndFun (f : fieldConstantSheaf Λ V ⟶ fieldConstantSheaf Λ V) :
    fieldFunctions Λ V :=
  (f.hom.app (op (proEtTop V)) (ULift.up 1)).down

omit [IsUltrametricDist Λ] in
lemma fieldConstantSheaf_app_one (f : fieldConstantSheaf Λ V ⟶ fieldConstantSheaf Λ V)
    (U : V.ProEt) :
    f.hom.app (op U) (ULift.up 1) = ULift.up (fieldFunctionsComp Λ
      U.hom.base.hom (fieldConstantSheafEndFun f)) := by
  have h := NatTrans.naturality_apply f.hom (toProEtTop U).op
    (ULift.up 1 : (fieldConstantSheaf Λ V).obj.obj (op (proEtTop V)))
  have h1 : (fieldConstantSheaf Λ V).obj.map (toProEtTop U).op
      (ULift.up 1 : (fieldConstantSheaf Λ V).obj.obj (op (proEtTop V))) = ULift.up 1 := rfl
  rw [h1] at h
  rw [h]
  rfl

omit [IsUltrametricDist Λ] in
/-- `Λ_V`-linear endomorphisms of `Λ_V` are determined by their function. -/
lemma fieldConstantSheaf_end_ext {f g : fieldConstantSheaf Λ V ⟶ fieldConstantSheaf Λ V}
    (hf : (MonObj.mul : fieldConstantSheaf Λ V ⊗ fieldConstantSheaf Λ V ⟶ _) ≫ f =
      fieldConstantSheaf Λ V ◁ f ≫ MonObj.mul)
    (hg : (MonObj.mul : fieldConstantSheaf Λ V ⊗ fieldConstantSheaf Λ V ⟶ _) ≫ g =
      fieldConstantSheaf Λ V ◁ g ≫ MonObj.mul)
    (h : fieldConstantSheafEndFun f = fieldConstantSheafEndFun g) : f = g := by
  apply Sheaf.hom_ext
  ext U s
  rw [fieldConstantSheaf_app_eq_mul f hf, fieldConstantSheaf_app_eq_mul g hg,
    fieldConstantSheaf_app_one, fieldConstantSheaf_app_one, h]

omit [IsUltrametricDist Λ] in
lemma fieldConstantSheafEndFun_comp (f g : fieldConstantSheaf Λ V ⟶ fieldConstantSheaf Λ V)
    (hg : (MonObj.mul : fieldConstantSheaf Λ V ⊗ fieldConstantSheaf Λ V ⟶ _) ≫ g =
      fieldConstantSheaf Λ V ◁ g ≫ MonObj.mul) :
    fieldConstantSheafEndFun (f ≫ g) = fieldConstantSheafEndFun f * fieldConstantSheafEndFun g := by
  change ((g.hom.app _) (f.hom.app _ (ULift.up 1))).down = _
  rw [fieldConstantSheaf_app_eq_mul g hg]
  rfl

/-- The product of a function `s` on `T` with the pullback of a function `a` on `V` along
`g : T ⟶ V`. -/
noncomputable def fieldMulPullback {T : Scheme.{u}} (s : fieldFunctions Λ T)
    (g : T ⟶ V) (a : fieldFunctions Λ V) :
    fieldFunctions Λ T :=
  s * fieldFunctionsComp Λ g.base.hom a

/-- Multiplication by a continuous function `a` on `V`, an endomorphism of `Λ_V`. -/
noncomputable def fieldConstantSheafMul (a : fieldFunctions Λ V) :
    fieldConstantSheaf Λ V ⟶ fieldConstantSheaf Λ V :=
  ⟨{ app U := ModuleCat.ofHom
      { toFun s := ULift.up (fieldMulPullback (T := U.unop.left) s.down U.unop.hom a)
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

omit [IsUltrametricDist Λ] in
lemma fieldConstantSheafMul_app (a : fieldFunctions Λ V) (U : V.ProEtᵒᵖ)
    (s : (fieldConstantSheaf Λ V).obj.obj U) :
    (fieldConstantSheafMul a).hom.app U s =
      ULift.up (fieldMulPullback (T := U.unop.left) s.down U.unop.hom a) :=
  rfl

omit [IsUltrametricDist Λ] in
lemma fieldConstantSheafEndFun_mul (a : fieldFunctions Λ V) :
    fieldConstantSheafEndFun (fieldConstantSheafMul a) = a := by
  change 1 * _ = a
  rw [one_mul]
  rfl

omit [IsUltrametricDist Λ] in
lemma fieldConstantSheafMul_linear (a : fieldFunctions Λ V) :
    (MonObj.mul : fieldConstantSheaf Λ V ⊗ fieldConstantSheaf Λ V ⟶ _) ≫ fieldConstantSheafMul a =
      fieldConstantSheaf Λ V ◁ fieldConstantSheafMul a ≫ MonObj.mul := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← μ_natural_right_assoc, ← Category.assoc,
    fieldConstantSheaf_μ_comp_map_mul']
  ext U : 2
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change ULift.up ((s.down * t.down) * _) = ULift.up (s.down * (t.down * _))
  rw [mul_assoc]

section Restriction

variable {W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)

omit [IsUltrametricDist Λ] in
lemma localizationRestriction_fieldConstantSheaf :
    (localizationRestriction (FieldCoefficients.{u} Λ) g hg).obj (fieldConstantSheaf Λ V) =
      fieldConstantSheaf Λ W :=
  rfl

/-- For a weakly étale `g`, the comparison `g^* Λ_V ≅ Λ_W`, seen on the restriction, is the
identity. -/
lemma upperStarIsoLocalizationRestriction_inv_app_comp_fieldUpperStarUnitIso :
    (upperStarIsoLocalizationRestriction (FieldCoefficients.{u} Λ) g hg).inv.app
        (fieldConstantSheaf Λ V) ≫ (fieldUpperStarUnitIso Λ g).hom.hom =
      eqToHom (localizationRestriction_fieldConstantSheaf g hg) := by
  let adj1 := upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g
  let adj2 := localizationRestrictionLowerStarAdjunction (FieldCoefficients.{u} Λ) g hg
  have key (k : (localizationRestriction (FieldCoefficients.{u} Λ) g hg).obj
      (fieldConstantSheaf Λ V) ⟶ fieldConstantSheaf Λ W) :
      adj2.homEquiv _ _ k = adj1.homEquiv _ _
        ((upperStarIsoLocalizationRestriction (FieldCoefficients.{u} Λ) g hg).hom.app _ ≫ k) := by
    rw [adj1.homEquiv_naturality_right, Adjunction.homEquiv_unit]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply (adj2.homEquiv _ _).injective
  erw [key, Iso.hom_inv_id_app_assoc]
  simp only [fieldUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  ext U s
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  erw [localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  rfl

lemma fieldUpperStarUnitIso_hom_hom_eq :
    (fieldUpperStarUnitIso Λ g).hom.hom =
      (upperStarIsoLocalizationRestriction (FieldCoefficients.{u} Λ) g hg).hom.app
        (fieldConstantSheaf Λ V) := by
  rw [← Iso.hom_inv_id_app_assoc (upperStarIsoLocalizationRestriction (FieldCoefficients.{u} Λ)
    g hg) (fieldConstantSheaf Λ V) (fieldUpperStarUnitIso Λ g).hom.hom,
    upperStarIsoLocalizationRestriction_inv_app_comp_fieldUpperStarUnitIso, eqToHom_refl,
    Category.comp_id]

include hg in
/-- The function of the pullback of an endomorphism of `Λ_V` along a weakly étale `g` is the
pullback of its function. -/
lemma fieldConstantSheafEndFun_fieldUpperStar (ψ : FieldSheaf.unit Λ V ⟶ FieldSheaf.unit Λ V) :
    fieldConstantSheafEndFun ((fieldUpperStarUnitIso Λ g).inv ≫ (g)^*ᶠ[Λ].map ψ ≫
      (fieldUpperStarUnitIso Λ g).hom).hom =
      fieldFunctionsComp Λ g.base.hom (fieldConstantSheafEndFun ψ.hom) := by
  let e := upperStarIsoLocalizationRestriction (FieldCoefficients.{u} Λ) g hg
  let f : fieldConstantSheaf Λ V ⟶ fieldConstantSheaf Λ V := ψ.hom
  have h1 : ((fieldUpperStarUnitIso Λ g).inv ≫ (g)^*ᶠ[Λ].map ψ ≫
      (fieldUpperStarUnitIso Λ g).hom).hom =
      (localizationRestriction (FieldCoefficients.{u} Λ) g hg).map f := by
    have h0 : (fieldUpperStarUnitIso Λ g).hom.hom ≫ ((fieldUpperStarUnitIso Λ g).inv ≫
        (g)^*ᶠ[Λ].map ψ ≫ (fieldUpperStarUnitIso Λ g).hom).hom =
        ((g)^*ᶠ[Λ].map ψ).hom ≫ (fieldUpperStarUnitIso Λ g).hom.hom :=
      congrArg (fun k ↦ k.hom) (Iso.hom_inv_id_assoc (fieldUpperStarUnitIso Λ g)
        ((g)^*ᶠ[Λ].map ψ ≫ (fieldUpperStarUnitIso Λ g).hom))
    rw [fieldUpperStarUnitIso_hom_hom_eq g hg] at h0
    rw [← cancel_epi (e.hom.app (fieldConstantSheaf Λ V))]
    refine h0.trans ?_
    exact e.hom.naturality f
  rw [h1]
  change ((f.hom.app _) (ULift.up 1)).down = _
  erw [fieldConstantSheaf_app_one]
  rfl

end Restriction

namespace FieldSheaf

/-- The function on `V` of an endomorphism of the unit `Λ_V`-module. -/
noncomputable def unitEndFun (ψ : unit Λ V ⟶ unit Λ V) : fieldFunctions Λ V :=
  fieldConstantSheafEndFun ψ.hom

omit [IsUltrametricDist Λ] in
lemma unit_hom_linear (ψ : unit Λ V ⟶ unit Λ V) :
    (MonObj.mul : fieldConstantSheaf Λ V ⊗ fieldConstantSheaf Λ V ⟶ _) ≫ ψ.hom =
      fieldConstantSheaf Λ V ◁ ψ.hom ≫ MonObj.mul :=
  IsModHom.smul_hom (A := fieldConstantSheaf Λ V) (f := ψ.hom)

omit [IsUltrametricDist Λ] in
lemma unitEndFun_injective : Function.Injective (unitEndFun (Λ := Λ) (V := V)) :=
  fun ψ ψ' h ↦ Mod.hom_ext _ _ (fieldConstantSheaf_end_ext (unit_hom_linear ψ)
    (unit_hom_linear ψ') h)

omit [IsUltrametricDist Λ] in
lemma unitEndFun_comp (ψ ψ' : unit Λ V ⟶ unit Λ V) :
    unitEndFun (ψ ≫ ψ') = unitEndFun ψ * unitEndFun ψ' :=
  fieldConstantSheafEndFun_comp ψ.hom ψ'.hom (unit_hom_linear ψ')

omit [IsUltrametricDist Λ] in
lemma unitEndFun_id : unitEndFun (𝟙 (unit Λ V)) = 1 :=
  rfl

omit [IsUltrametricDist Λ] in
lemma unitEndFun_add (ψ ψ' : unit Λ V ⟶ unit Λ V) :
    unitEndFun (ψ + ψ') = unitEndFun ψ + unitEndFun ψ' :=
  rfl

omit [IsUltrametricDist Λ] in
lemma unitEndFun_zero : unitEndFun (0 : unit Λ V ⟶ unit Λ V) = 0 :=
  rfl

/-- Multiplication by a continuous function, an endomorphism of the unit module. -/
noncomputable def unitMul (a : fieldFunctions Λ V) : unit Λ V ⟶ unit Λ V :=
  Mod.homMk (fieldConstantSheafMul a) (fieldConstantSheafMul_linear a)

omit [IsUltrametricDist Λ] in
lemma unitEndFun_unitMul (a : fieldFunctions Λ V) :
    unitEndFun (unitMul a) = a :=
  fieldConstantSheafEndFun_mul a

end FieldSheaf

namespace FieldSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

/-- The matrix of functions of a morphism between finite free `Λ_V`-modules. -/
noncomputable def unitMatrix (ψ : (⨁ fun _ : ι ↦ unit Λ V) ⟶ ⨁ fun _ : κ ↦ unit Λ V) :
    Matrix κ ι (fieldFunctions Λ V) :=
  fun i j ↦ unitEndFun (biproduct.ι (fun _ : ι ↦ unit Λ V) j ≫ ψ ≫
    biproduct.π (fun _ : κ ↦ unit Λ V) i)

/-- `unitEndFun` as an additive map. -/
noncomputable def unitEndFunAddHom :
    (unit Λ V ⟶ unit Λ V) →+ fieldFunctions Λ V where
  toFun := unitEndFun
  map_zero' := unitEndFun_zero
  map_add' := unitEndFun_add

omit [IsUltrametricDist Λ] in
lemma unitMatrix_comp (ψ : (⨁ fun _ : ι ↦ unit Λ V) ⟶ ⨁ fun _ : κ ↦ unit Λ V)
    (ψ' : (⨁ fun _ : κ ↦ unit Λ V) ⟶ ⨁ fun _ : ν ↦ unit Λ V) :
    unitMatrix (ψ ≫ ψ') = unitMatrix ψ' * unitMatrix ψ := by
  refine Matrix.ext fun i j ↦ ?_
  have : biproduct.ι (fun _ : ι ↦ unit Λ V) j ≫ (ψ ≫ ψ') ≫ biproduct.π (fun _ : ν ↦ unit Λ V) i =
      ∑ k, (biproduct.ι (fun _ : ι ↦ unit Λ V) j ≫ ψ ≫ biproduct.π (fun _ : κ ↦ unit Λ V) k) ≫
        (biproduct.ι (fun _ : κ ↦ unit Λ V) k ≫ ψ' ≫ biproduct.π (fun _ : ν ↦ unit Λ V) i) := by
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

omit [IsUltrametricDist Λ] in
lemma unitMatrix_id [DecidableEq ι] :
    unitMatrix (𝟙 (⨁ fun _ : ι ↦ unit Λ V)) = 1 := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [unitMatrix, Matrix.one_apply, Category.id_comp]
  by_cases h : i = j
  · subst h
    rw [biproduct.ι_π_self, ite_eq_left rfl]
    rfl
  · rw [biproduct.ι_π_ne _ (Ne.symm h), ite_eq_right h]
    rfl

omit [IsUltrametricDist Λ] in
lemma unitMatrix_injective :
    Function.Injective (unitMatrix (Λ := Λ) (V := V) (ι := ι) (κ := κ)) := by
  intro ψ ψ' h
  refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun i ↦ ?_
  have := congrFun (congrFun h i) j
  simpa only [Category.assoc] using unitEndFun_injective this

/-- The morphism between finite free `Λ_V`-modules given by a matrix of functions. -/
noncomputable def ofUnitMatrix (N : Matrix κ ι (fieldFunctions Λ V)) :
    (⨁ fun _ : ι ↦ unit Λ V) ⟶ ⨁ fun _ : κ ↦ unit Λ V :=
  biproduct.matrix fun j i ↦ unitMul (Λ := Λ) (V := V) (N i j)

omit [IsUltrametricDist Λ] in
lemma unitMatrix_ofUnitMatrix (N : Matrix κ ι (fieldFunctions Λ V)) :
    unitMatrix (ofUnitMatrix N) = N := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [unitMatrix, ofUnitMatrix, biproduct.matrix_π, biproduct.ι_desc]
  exact unitEndFun_unitMul _

end FieldSheaf

namespace FieldSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

omit [IsUltrametricDist Λ] in
lemma ofUnitMatrix_unitMatrix (ψ : (⨁ fun _ : ι ↦ unit Λ V) ⟶ ⨁ fun _ : κ ↦ unit Λ V) :
    ofUnitMatrix (unitMatrix ψ) = ψ :=
  unitMatrix_injective (unitMatrix_ofUnitMatrix _)

omit [IsUltrametricDist Λ] in
lemma ofUnitMatrix_mul (N₁ : Matrix ν κ (fieldFunctions Λ V))
    (N₂ : Matrix κ ι (fieldFunctions Λ V)) :
    ofUnitMatrix (N₁ * N₂) = ofUnitMatrix N₂ ≫ ofUnitMatrix N₁ :=
  unitMatrix_injective (by rw [unitMatrix_comp, unitMatrix_ofUnitMatrix, unitMatrix_ofUnitMatrix,
    unitMatrix_ofUnitMatrix])

omit [IsUltrametricDist Λ] in
lemma ofUnitMatrix_one [DecidableEq ι] :
    ofUnitMatrix (1 : Matrix ι ι (fieldFunctions Λ V)) = 𝟙 _ :=
  unitMatrix_injective (by rw [unitMatrix_ofUnitMatrix, unitMatrix_id])

omit [IsUltrametricDist Λ] in
lemma isIso_ofUnitMatrix [DecidableEq ι] (P : Matrix ι ι (fieldFunctions Λ V))
    (hP : IsUnit P.det) : IsIso (ofUnitMatrix P) :=
  ⟨ofUnitMatrix P⁻¹, by rw [← ofUnitMatrix_mul, Matrix.nonsing_inv_mul _ hP, ofUnitMatrix_one],
    by rw [← ofUnitMatrix_mul, Matrix.mul_nonsing_inv _ hP, ofUnitMatrix_one]⟩

section Block

variable [DecidableEq ι] [DecidableEq κ] {r : ℕ} (ρ : Fin r → κ) (γ : Fin r → ι)
  (hρ : Function.Injective ρ) (hγ : Function.Injective γ)

/-- The morphism `Λ^ι ⟶ Λ^κ` projecting onto the coordinates in the range of `γ` and
including them as the coordinates in the range of `ρ`. -/
noncomputable def blockMap : (⨁ fun _ : ι ↦ unit Λ V) ⟶ ⨁ fun _ : κ ↦ unit Λ V :=
  biproduct.toSubtype _ (· ∈ Set.range γ) ≫
    (biproduct.whiskerEquiv ((Equiv.ofInjective γ hγ).symm.trans (Equiv.ofInjective ρ hρ))
      (fun _ ↦ Iso.refl (unit Λ V))).hom ≫ biproduct.fromSubtype _ (· ∈ Set.range ρ)

omit [IsUltrametricDist Λ] in
lemma unitMatrix_blockMap :
    unitMatrix (blockMap (Λ := Λ) (V := V) ρ γ hρ hγ) =
      (Matrix.fromBlocks 1 0 0 0 : Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
        (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex (sumComplEquiv ρ hρ).symm
          (sumComplEquiv γ hγ).symm := by
  refine Matrix.ext fun i j ↦ ?_
  obtain ⟨x, rfl⟩ := (sumComplEquiv ρ hρ).symm.surjective i
  obtain ⟨y, rfl⟩ := (sumComplEquiv γ hγ).symm.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rcases y with b | ⟨j, hj⟩
  · have h1 : biproduct.ι (fun _ : ι ↦ unit Λ V) ((sumComplEquiv γ hγ).symm
        (Sum.inl b)) ≫ blockMap (Λ := Λ) (V := V) ρ γ hρ hγ =
        biproduct.ι (fun _ : κ ↦ unit Λ V) (ρ b) := by
      rw [sumComplEquiv_symm_inl, blockMap,
        biproduct.ι_toSubtype_subtype_assoc (fun _ : ι ↦ unit Λ V) (· ∈ Set.range γ) ⟨γ b, b, rfl⟩]
      simp only [biproduct.whiskerEquiv_hom, Equiv.trans_apply, Iso.refl_inv,
        biproduct.ι_desc_assoc, Category.assoc, biproduct.ι_fromSubtype,
        Equiv.ofInjective_symm_apply, Equiv.ofInjective_apply]
      exact Category.id_comp _
    rw [unitMatrix, ← Category.assoc, h1]
    rcases x with a | ⟨i, hi⟩
    · rw [sumComplEquiv_symm_inl]
      by_cases hab : b = a
      · subst hab
        rw [biproduct.ι_π_self]
        simp
        rfl
      · rw [biproduct.ι_π_ne _ (hρ.ne hab)]
        simp only [Matrix.fromBlocks_apply₁₁]
        rw [Matrix.one_apply_ne (Ne.symm hab)]
        rfl
    · have : (sumComplEquiv ρ hρ).symm (Sum.inr ⟨i, hi⟩) = i := by
        simp [sumComplEquiv]
      rw [this, biproduct.ι_π_ne _ (fun h ↦ hi ⟨b, h⟩)]
      rfl
  · have : (sumComplEquiv γ hγ).symm (Sum.inr ⟨j, hj⟩) = j := by
      simp [sumComplEquiv]
    rw [unitMatrix, this, blockMap]
    simp only [Category.assoc]
    erw [biproduct.ι_toSubtype_assoc, dite_eq_right hj]
    simp only [Limits.zero_comp]
    rcases x with a | ⟨i, hi⟩ <;> rfl

set_option linter.unusedFintypeInType false in
instance : Mono (biproduct.fromSubtype (fun _ : κ ↦ unit Λ V) (· ∈ Set.range ρ)) :=
  mono_of_mono_fac (biproduct.fromSubtype_toSubtype _ _)

set_option linter.unusedFintypeInType false in
instance : Epi (biproduct.toSubtype (fun _ : ι ↦ unit Λ V) (· ∈ Set.range γ)) :=
  epi_of_epi_fac (biproduct.fromSubtype_toSubtype _ _)

variable {ρ γ hρ hγ} in
omit [IsUltrametricDist Λ] in
lemma eq_blockMap_of_unitMatrix_eq
    (ψ : (⨁ fun _ : ι ↦ unit Λ V) ⟶ ⨁ fun _ : κ ↦ unit Λ V)
    (P : Matrix κ κ (fieldFunctions Λ V))
    (Q : Matrix ι ι (fieldFunctions Λ V))
    (h : unitMatrix ψ = P * (Matrix.fromBlocks 1 0 0 0 : Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
        (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex (sumComplEquiv ρ hρ).symm
          (sumComplEquiv γ hγ).symm * Q) :
    ψ = ofUnitMatrix Q ≫ blockMap ρ γ hρ hγ ≫ ofUnitMatrix P := by
  rw [← ofUnitMatrix_unitMatrix ψ, h, ofUnitMatrix_mul, ofUnitMatrix_mul,
    ← unitMatrix_blockMap (Λ := Λ) (V := V) ρ γ hρ hγ, ofUnitMatrix_unitMatrix]

/-- The kernel of the block map is free on the coordinates outside the range of `γ`. -/
noncomputable def kernelBlockMapIso :
    kernel (blockMap (Λ := Λ) (V := V) ρ γ hρ hγ) ≅
      ⨁ Subtype.restrict (· ∈ Set.range γ)ᶜ (fun _ : ι ↦ unit Λ V) :=
  kernelCompMono _ _ ≪≫ kernelBiproductToSubtypeIso _ _

/-- The cokernel of the block map is free on the coordinates outside the range of `ρ`. -/
noncomputable def cokernelBlockMapIso :
    cokernel (blockMap (Λ := Λ) (V := V) ρ γ hρ hγ) ≅
      ⨁ Subtype.restrict (· ∈ Set.range ρ)ᶜ (fun _ : κ ↦ unit Λ V) :=
  (cokernelIsoOfEq (Category.assoc _ _ _).symm) ≪≫ cokernelEpiComp _ _ ≪≫
    cokernelBiproductFromSubtypeIso _ _

end Block

end FieldSheaf

namespace FieldSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ : Type} [Fintype ι] [Fintype κ] {W : Scheme.{u}}

variable (Λ ι) in
/-- The pullback of a finite free module is finite free. -/
noncomputable def freeUpperStarIso (g : W ⟶ V) :
    (g)^*ᶠ[Λ].obj (⨁ fun _ : ι ↦ unit Λ V) ≅ ⨁ fun _ : ι ↦ unit Λ W :=
  (g)^*ᶠ[Λ].mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ fieldUpperStarUnitIso Λ g

lemma unitMatrix_fieldUpperStar (g : W ⟶ V) [hg : WeaklyEtale g]
    (ψ : (⨁ fun _ : ι ↦ unit Λ V) ⟶ ⨁ fun _ : κ ↦ unit Λ V) :
    unitMatrix ((freeUpperStarIso Λ ι g).inv ≫ (g)^*ᶠ[Λ].map ψ ≫ (freeUpperStarIso Λ κ g).hom) =
      (unitMatrix ψ).map (fieldFunctionsComp Λ g.base.hom) := by
  refine Matrix.ext fun i j ↦ ?_
  have h1 : biproduct.ι (fun _ : ι ↦ unit Λ W) j ≫ (freeUpperStarIso Λ ι g).inv =
      (fieldUpperStarUnitIso Λ g).inv ≫ (g)^*ᶠ[Λ].map (biproduct.ι (fun _ : ι ↦ unit Λ V) j) := by
    simp [freeUpperStarIso]
  have h2 : (freeUpperStarIso Λ κ g).hom ≫ biproduct.π (fun _ : κ ↦ unit Λ W) i =
      (g)^*ᶠ[Λ].map (biproduct.π (fun _ : κ ↦ unit Λ V) i) ≫ (fieldUpperStarUnitIso Λ g).hom := by
    simp [freeUpperStarIso]
  simp only [unitMatrix, Matrix.map_apply, Category.assoc, h2]
  rw [reassoc_of% h1]
  have := fieldConstantSheafEndFun_fieldUpperStar g hg
    (biproduct.ι (fun _ : ι ↦ unit Λ V) j ≫ ψ ≫ biproduct.π (fun _ : κ ↦ unit Λ V) i)
  simp only [Functor.map_comp, Category.assoc] at this
  exact this

end FieldSheaf

end AlgebraicGeometry.ProEtale
