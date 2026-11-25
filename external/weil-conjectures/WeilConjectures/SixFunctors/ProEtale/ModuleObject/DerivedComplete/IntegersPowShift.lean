/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.PowShift
public import WeilConjectures.NumberTheory.Padics.Exponential
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.Analysis.Normed.Ring.ContinuousMapSubMulShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer

/-!
# `𝒪_{E,V}` is complete with respect to a uniformizer

Let `ϖ ∈ 𝔪_E`. For every scheme `V`, the endomorphism `(xₙ)ₙ ↦ (xₙ - ϖ x_{n+1})ₙ` of the
countable power `∏ₙ 𝒪_{E,V}` of the regular `𝒪_{E,V}`-module is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_sub_powShift_padicIntegersCenter_unit`). Indeed `𝒪_{E,V}` is
the sheaf `U ↦ C(U, 𝒪_E)` (`AlgebraicGeometry.ProEtale.continuousMapComparison`), on which `ϖ`
acts by multiplication, and the claim can be checked on sections, where it is the bijectivity of
`(yₙ)ₙ ↦ (yₙ - ϖ y_{n+1})ₙ` on sequences of continuous maps `U → 𝒪_E`
(`ContinuousMap.bijective_sub_const_mul_succ`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Limits

/-- In abelian groups, `1 - powShift e` is an isomorphism if and only if the map
`(yₙ)ₙ ↦ (yₙ - e y_{n+1})ₙ` on sequences is bijective. -/
lemma AddCommGrpCat.isIso_sub_powShift_iff {A : AddCommGrpCat.{w}} (e : A ⟶ A) :
    IsIso (𝟙 _ - powShift e) ↔
      Function.Bijective fun y : ℕ → A ↦ fun n ↦ y n - e (y (n + 1)) := by
  have : PreservesLimitsOfSize.{0, 0} (forget AddCommGrpCat.{w}) :=
    preservesLimitsOfSize_shrink _
  rw [ConcreteCategory.isIso_iff_bijective]
  let φ := Concrete.productEquiv (fun _ : ℕ ↦ A)
  have h : (fun y : ℕ → A ↦ fun n ↦ y n - e (y (n + 1))) =
      φ ∘ (𝟙 (∏ᶜ fun _ : ℕ ↦ A) - powShift e) ∘ φ.symm := by
    funext y n
    simp only [Function.comp_apply, φ, Concrete.productEquiv_apply_apply]
    rw [← ConcreteCategory.comp_apply, Preadditive.sub_comp, Category.id_comp, powShift_π]
    simp
  rw [h]
  refine ⟨fun hb ↦ φ.bijective.comp (hb.comp φ.symm.bijective), fun hb ↦ ?_⟩
  have : ⇑(𝟙 (∏ᶜ fun _ : ℕ ↦ A) - powShift e) =
      φ.symm ∘ (φ ∘ (𝟙 (∏ᶜ fun _ : ℕ ↦ A) - powShift e) ∘ φ.symm) ∘ φ := by
    funext x
    simp
  rw [this]
  exact φ.symm.bijective.comp (hb.comp φ.bijective)

/-- For a sheaf of abelian groups `F` and an endomorphism `e`, `1 - powShift e` is an
isomorphism of `∏ₙ F` as soon as `(yₙ)ₙ ↦ (yₙ - e y_{n+1})ₙ` is bijective on sequences of
sections over every object. -/
lemma Sheaf.isIso_sub_powShift_of_bijective {C : Type*} [Category* C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}] {F : Sheaf J AddCommGrpCat.{w}}
    [HasProduct fun _ : ℕ ↦ F] (e : F ⟶ F)
    (h : ∀ U, Function.Bijective fun y : ℕ → F.obj.obj U ↦ fun n ↦ y n - e.hom.app U (y (n + 1))) :
    IsIso (𝟙 _ - powShift e) := by
  have hU (U : Cᵒᵖ) : IsIso (((sheafToPresheaf J AddCommGrpCat.{w}).map
      (𝟙 _ - powShift e)).app U) :=
    (isIso_map_sub_powShift_iff
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U) e).2
      ((AddCommGrpCat.isIso_sub_powShift_iff _).2 (h U))
  have : IsIso ((sheafToPresheaf J AddCommGrpCat.{w}).map (𝟙 _ - powShift e)) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (sheafToPresheaf J AddCommGrpCat.{w})

end CategoryTheory.Limits

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasLimitsOfShape (Discrete ℕ) C] {R : C} [MonObj R]

/-- For an endomorphism `e` of a module object, `1 - powShift e` is an isomorphism as soon as it
is one on the underlying objects. -/
lemma isIso_sub_powShift_of_isIso_hom {M : Mod C R} (e : M ⟶ M)
    (h : IsIso (𝟙 _ - powShift e.hom)) : IsIso (𝟙 _ - powShift e) := by
  have := (isIso_map_sub_powShift_iff (forget R) e).2 h
  exact isIso_of_reflects_iso _ (forget R)

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

section MulConst

variable (V : Scheme.{u}) {T : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The multiplication by a constant `t ∈ T` on the abelian sheaf `U ↦ C(U, T)` on `V_proét`. -/
noncomputable def continuousMapSheafMulConst (t : T) :
    (sheafCompose (ProEt.topology V) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf V T) ⟶
      (sheafCompose (ProEt.topology V) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf V T) :=
  ⟨{ app _ := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (ULift.up (ContinuousMap.const _ t)))
     naturality _ _ _ := rfl }⟩

lemma continuousMapSheafMulConst_hom_app_apply (t : T) (U : V.ProEtᵒᵖ)
    (a : ULift.{u + 1} C(U.unop.left, T)) :
    (continuousMapSheafMulConst V t).hom.app U a = ULift.up (ContinuousMap.const _ t * a.down) :=
  rfl

end MulConst

variable (V : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (ϖ : PadicAlgCl.integers ℓ E)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The comparison `𝒪_{E,V} ≅ C(-, 𝒪_E)_V` carries the multiplication by `ϖ` to the
multiplication by the constant `ϖ`. -/
lemma padicIntegersMulLeft_comp_continuousMapComparison :
    letI := normedFieldOfAlgebra ℓ E
    padicIntegersMulLeft V ℓ E ϖ ≫ continuousMapComparison V (integers ℓ E) =
      continuousMapComparison V (integers ℓ E) ≫ continuousMapSheafMulConst V ϖ := by
  let := normedFieldOfAlgebra ℓ E
  rw [padicIntegersMulLeft, continuousMapComparison,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1

variable {ϖ}

/-- On the sheaf `U ↦ C(U, 𝒪_E)`, the map `(xₙ)ₙ ↦ (xₙ - ϖ x_{n+1})ₙ` of the countable power is an
isomorphism, for `ϖ ∈ 𝔪_E`. -/
theorem isIso_sub_powShift_continuousMapSheafMulConst
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (integers ℓ E)) :
    letI := normedFieldOfAlgebra ℓ E
    IsIso (𝟙 _ - powShift (continuousMapSheafMulConst V ϖ)) := by
  let := normedFieldOfAlgebra ℓ E
  have := compactSpace_integers ℓ E
  refine Sheaf.isIso_sub_powShift_of_bijective _ fun U ↦ ?_
  have hT (x : integers ℓ E) : ‖x‖ ≤ 1 :=
    NNReal.coe_le_coe.2 ((mem_integers_iff ℓ E x).1 x.2)
  have ht : ‖ϖ‖ < 1 := norm_lt_one_of_mem_maximalIdeal ℓ E hϖ
  have hc : CompleteSpace (integers ℓ E) := complete_of_compact
  have key := ContinuousMap.bijective_sub_const_mul_succ (W := U.unop.left) hT ht
  let e : (ℕ → ULift.{u + 1} C(U.unop.left, integers ℓ E)) ≃
      (ℕ → C(U.unop.left, integers ℓ E)) :=
    Equiv.piCongrRight fun _ ↦ Equiv.ulift
  exact e.symm.bijective.comp (key.comp e.bijective)

/-- On the abelian sheaf `𝒪_{E,V}`, the map `(xₙ)ₙ ↦ (xₙ - ϖ x_{n+1})ₙ` of the countable power is
an isomorphism, for `ϖ ∈ 𝔪_E`. -/
theorem isIso_sub_powShift_padicIntegersMulLeft
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (integers ℓ E)) :
    IsIso (𝟙 _ - powShift (padicIntegersMulLeft V ℓ E ϖ)) := by
  let := normedFieldOfAlgebra ℓ E
  have := isUltrametricDist_ofAlgebra ℓ E
  have := isIso_sub_powShift_continuousMapSheafMulConst V ℓ E hϖ
  exact (isIso_sub_powShift_iff_of_iso (asIso (continuousMapComparison V (integers ℓ E)))
    (padicIntegersMulLeft_comp_continuousMapComparison V ℓ E ϖ)).2 this

/-- **`𝒪_{E,V}` is complete with respect to `ϖ ∈ 𝔪_E`**: on the countable power of the regular
`𝒪_{E,V}`-module, `(xₙ)ₙ ↦ (xₙ - ϖ x_{n+1})ₙ` is an isomorphism. -/
theorem isIso_sub_powShift_padicIntegersCenter_unit
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (integers ℓ E)) :
    IsIso (𝟙 _ - powShift ((padicIntegersCenter V ℓ E ϖ).app
      (𝟙_ (Mod (Sheaf (ProEt.topology V) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V))))) := by
  refine Mod.isIso_sub_powShift_of_isIso_hom _ ?_
  rw [Mod.regularEndCenter_app, Mod.regularEndSMul_unit, padicIntegersRegularEnd_hom]
  exact isIso_sub_powShift_padicIntegersMulLeft V ℓ E hϖ

/-- **Finitely presented `𝒪_{E,V}`-modules are complete with respect to `ϖ ∈ 𝔪_E`**: on the
countable power of a finitely presented `𝒪_{E,V}`-module, `(xₙ)ₙ ↦ (xₙ - ϖ x_{n+1})ₙ` is an
isomorphism. -/
theorem isIso_sub_powShift_padicIntegersCenter_of_isFinitelyPresented
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (integers ℓ E))
    {M : Mod (Sheaf (ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)}
    (hM : Mod.IsFinitelyPresented _ M) :
    IsIso (𝟙 _ - powShift ((padicIntegersCenter V ℓ E ϖ).app M)) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hM
  refine (isIso_sub_powShift_iff_of_iso e.symm
    ((padicIntegersCenter V ℓ E ϖ).naturality e.symm.hom).symm).1 ?_
  exact isIso_sub_powShift_cokernel _ (isIso_sub_powShift_padicIntegersCenter_unit V ℓ E hϖ) f

end AlgebraicGeometry.ProEtale
