/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.CategoryTheory.StageSystem.Const
public import WeilConjectures.CategoryTheory.StageSystem.Restrict
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleHeart
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsComp

/-!
# The common-stage constructible category `D^b_c(X, ℚ̄_ℓ) = 2-colim_E D^b_c(X, E)` and its heart

For `Λ = ℚ̄_ℓ`, the constructible heart is defined on the common-stage category: the `2`-colimit
over the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` of the bounded constructible derived categories
`D^b_c(X, E)` (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructible`) along the
extensions of scalars `F ⊗_E -`. This file constructs

- the transition functors `F ⊗_E - : D^b_c(X, E) ⥤ D^b_c(X, F)`, induced on derived categories by
  the exact extension of scalars of sheaves, which preserves constructibility
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructibleExtendScalars`), and the
  associativity constraints `G ⊗_F (F ⊗_E -) ≅ G ⊗_E -`, which satisfy the cocycle condition;
  together they form a stage system
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructibleStageSystem`);
- its pair category, the `2`-colimit `D^b_c(X, ℚ̄_ℓ)`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.ConstructibleTwoColimit`);
- the halves `D^{≤ n}_c(X, ℚ̄_ℓ)` and `D^{≥ n}_c(X, ℚ̄_ℓ)` of the induced `t`-structure: since the
  transition functors are `t`-exact, an object `(E, K)` lies in `D^{≤ n}_c` if `F ⊗_E K` lies in
  `D^{≤ n}_c(X, F)` at some finite stage `F ⊇ E`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitLE`);
- the constructible heart `Sh_c(X, ℚ̄_ℓ) = D^{≤ 0}_c ∩ D^{≥ 0}_c`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitHeart`), and its
  identification with the `2`-colimit of the hearts `Sh_c(X, E)` of the finite stages
  (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitHeartEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

namespace DerivedCategory

section Transition

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ)) (X : Scheme.{u})

/-- The extension of scalars `Λ' ⊗_Λ -` of derived categories preserves bounded complexes with
constructible cohomology sheaves: it is exact, so it commutes with the cohomology sheaves, and it
preserves constructible sheaves. -/
lemma boundedFieldConstructible_mapDerivedCategory_obj
    {K : _root_.DerivedCategory (FieldSheaf Λ X)} (hK : boundedFieldConstructible Λ X K) :
    boundedFieldConstructible Λ' X ((fieldExtendScalars he hc X).mapDerivedCategory.obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
    (fieldConstructibleSheaf Λ' X).prop_of_iso
      (((fieldExtendScalars he hc X).mapDerivedCategoryHomologyFunctorIso n).app K)
      (IsFieldConstructibleSheaf.extendScalars he hc (hK.2 n))⟩

/-- The extension of scalars `Λ' ⊗_Λ - : D^b_c(X, Λ) ⥤ D^b_c(X, Λ')`. -/
noncomputable def boundedFieldConstructibleExtendScalars :
    (boundedFieldConstructible Λ X).FullSubcategory ⥤
      (boundedFieldConstructible Λ' X).FullSubcategory :=
  (boundedFieldConstructible Λ X).liftFullSubcategory _
    (fieldExtendScalars he hc X).mapDerivedCategory
    fun _ hK ↦ boundedFieldConstructible_mapDerivedCategory_obj he hc X hK

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] in
/-- The extension of scalars `Λ' ⊗_Λ -` of derived categories preserves `D^{≤ n}`. -/
lemma le_mapDerivedCategory_obj {K : _root_.DerivedCategory (FieldSheaf Λ X)} {n : ℤ}
    (hK : _root_.DerivedCategory.TStructure.t.le n K) :
    _root_.DerivedCategory.TStructure.t.le n
      ((fieldExtendScalars he hc X).mapDerivedCategory.obj K) :=
  haveI : K.IsLE n := ⟨hK⟩
  ((fieldExtendScalars he hc X).isLE_mapDerivedCategory_obj K n).le

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] in
/-- The extension of scalars `Λ' ⊗_Λ -` of derived categories preserves `D^{≥ n}`. -/
lemma ge_mapDerivedCategory_obj {K : _root_.DerivedCategory (FieldSheaf Λ X)} {n : ℤ}
    (hK : _root_.DerivedCategory.TStructure.t.ge n K) :
    _root_.DerivedCategory.TStructure.t.ge n
      ((fieldExtendScalars he hc X).mapDerivedCategory.obj K) :=
  haveI : K.IsGE n := ⟨hK⟩
  ((fieldExtendScalars he hc X).isGE_mapDerivedCategory_obj K n).ge

end Transition

section Comp

variable {l : ℕ} [Fact l.Prime] {Λ₁ Λ₂ Λ₃ Λ₄ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁]
  [NormedField Λ₂] [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃]
  [NormedField Λ₄] [IsUltrametricDist Λ₄] [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂]
  [Algebra ℚ_[l] Λ₃] [Algebra ℚ_[l] Λ₄] [FiniteDimensional ℚ_[l] Λ₂] [FiniteDimensional ℚ_[l] Λ₃]
  [FiniteDimensional ℚ_[l] Λ₄] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  {e₃ : Λ₃ →ₐ[ℚ_[l]] Λ₄} (he₁ : Continuous e₁) (he₂ : Continuous e₂) (he₃ : Continuous e₃)
  (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁)) (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂))
  (hc₃ : Continuous (algebraMap ℚ_[l] Λ₃)) (X : Scheme.{u})

/-- The associativity constraint `Λ₃ ⊗_{Λ₂} (Λ₂ ⊗_{Λ₁} -) ≅ Λ₃ ⊗_{Λ₁} -` of the extensions of
scalars of `D^b_c`, induced by that of the extensions of scalars of sheaves. -/
noncomputable def boundedFieldConstructibleExtendScalarsCompIso :
    boundedFieldConstructibleExtendScalars he₁ hc₁ X ⋙
        boundedFieldConstructibleExtendScalars he₂ hc₂ X ≅
      boundedFieldConstructibleExtendScalars (e := e₂.comp e₁) (he₂.comp he₁) hc₁ X :=
  let β := Functor.mapDerivedCategoryCompNatIso
    (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).symm
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (β.app K.obj))
    fun f ↦ ObjectProperty.hom_ext _ (β.hom.naturality f.hom)

omit [IsUltrametricDist Λ₁] [IsUltrametricDist Λ₂] [IsUltrametricDist Λ₃]
  [IsUltrametricDist Λ₄] in
/-- The inverses of the associativity constraints of the extensions of scalars of sheaves satisfy
the cocycle condition. -/
lemma fieldExtendScalarsCompIso_inv_cocycle (K : FieldSheaf Λ₁ X) :
    (fieldExtendScalars he₃ hc₃ X).map ((fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).inv.app K) ≫
      (fieldExtendScalarsCompIso (e₁ := e₂.comp e₁) (he₂.comp he₁) he₃ hc₁ hc₃ X).inv.app K =
    (fieldExtendScalarsCompIso he₂ he₃ hc₂ hc₃ X).inv.app
        ((fieldExtendScalars he₁ hc₁ X).obj K) ≫
      (fieldExtendScalarsCompIso (e₂ := e₃.comp e₂) he₁ (he₃.comp he₂) hc₁ hc₂ X).inv.app K := by
  have h := congr_app (fieldExtendScalarsCompIso_cocycle X he₁ he₂ he₃ hc₁ hc₂ hc₃) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  rw [← cancel_epi ((fieldExtendScalarsCompIso (e₁ := e₂.comp e₁) (he₂.comp he₁) he₃ hc₁ hc₃
    X).hom.app K ≫ (fieldExtendScalars he₃ hc₃ X).map
      ((fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).hom.app K))]
  conv_rhs => rw [h]
  simp [← Functor.map_comp_assoc]

/-- The associativity constraints of the extensions of scalars of `D^b_c` satisfy the cocycle
condition. -/
lemma boundedFieldConstructibleExtendScalarsCompIso_cocycle
    (K : (boundedFieldConstructible Λ₁ X).FullSubcategory) :
    (boundedFieldConstructibleExtendScalars he₃ hc₃ X).map
        ((boundedFieldConstructibleExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).hom.app K) ≫
      (boundedFieldConstructibleExtendScalarsCompIso (e₁ := e₂.comp e₁) (he₂.comp he₁) he₃ hc₁
        hc₃ X).hom.app K =
    (boundedFieldConstructibleExtendScalarsCompIso he₂ he₃ hc₂ hc₃ X).hom.app
        ((boundedFieldConstructibleExtendScalars he₁ hc₁ X).obj K) ≫
      (boundedFieldConstructibleExtendScalarsCompIso (e₂ := e₃.comp e₂) he₁ (he₃.comp he₂) hc₁
        hc₂ X).hom.app K :=
  ObjectProperty.hom_ext _ (Functor.mapDerivedCategoryCompNatIso_cocycle
    (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).symm
    (fieldExtendScalarsCompIso (e₁ := e₂.comp e₁) (he₂.comp he₁) he₃ hc₁ hc₃ X).symm
    (fieldExtendScalarsCompIso he₂ he₃ hc₂ hc₃ X).symm
    (fieldExtendScalarsCompIso (e₂ := e₃.comp e₂) he₁ (he₃.comp he₂) hc₁ hc₂ X).symm
    (fieldExtendScalarsCompIso_inv_cocycle he₁ he₂ he₃ hc₁ hc₂ hc₃ X) K.obj)

end Comp

section TwoColimit

open PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The inclusion `E ⊆ F` of finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ` is continuous. -/
lemma _root_.PadicAlgCl.continuous_inclusion_finiteIntermediateField'
    {E F : FiniteIntermediateField l}
    (h : E ≤ F) : Continuous (IntermediateField.inclusion (show E.1 ≤ F.1 from h)) :=
  continuous_subtype_val.subtype_mk _

/-- The structure map `ℚ_ℓ → E` of a subextension `E ⊆ ℚ̄_ℓ` is continuous. -/
lemma _root_.PadicAlgCl.continuous_algebraMap_intermediateField'
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) : Continuous (algebraMap ℚ_[l] E) :=
  (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).subtype_mk _

/-- Algebraically closed coefficients for `D^b_c`: the stage system of the `E`-stages.

The directed system `E ↦ D^b_c(X, E)` over the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, with the
extensions of scalars `F ⊗_E -` as transition functors and the identifications
`G ⊗_F (F ⊗_E -) ≅ G ⊗_E -` as associators, which satisfy the cocycle condition. -/
noncomputable def boundedFieldConstructibleStageSystem :
    StageSystem (fun E : FiniteIntermediateField l ↦
      (boundedFieldConstructible E.1 X).FullSubcategory) where
  T h := boundedFieldConstructibleExtendScalars
    (continuous_inclusion_finiteIntermediateField' l h)
    (continuous_algebraMap_intermediateField' l _) X
  assoc h h' := boundedFieldConstructibleExtendScalarsCompIso
    (continuous_inclusion_finiteIntermediateField' l h)
    (continuous_inclusion_finiteIntermediateField' l h')
    (continuous_algebraMap_intermediateField' l _) (continuous_algebraMap_intermediateField' l _)
    X
  cocycle h h' h'' K :=
    boundedFieldConstructibleExtendScalarsCompIso_cocycle
      (continuous_inclusion_finiteIntermediateField' l h)
      (continuous_inclusion_finiteIntermediateField' l h')
      (continuous_inclusion_finiteIntermediateField' l h'')
      (continuous_algebraMap_intermediateField' l _)
      (continuous_algebraMap_intermediateField' l _)
      (continuous_algebraMap_intermediateField' l _) X K

/-- Algebraically closed coefficients for `D^b_c`: the common-stage category
`D^b_c(X, ℚ̄_ℓ) = 2-colim_E D^b_c(X, E)`.

The pair category of
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructibleStageSystem`:
objects are the pairs `(E, K)` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and `K ∈ D^b_c(X, E)`,
and the morphisms `(E, K) ⟶ (E', K')` form the filtered colimit over the common finite stages
`F ⊇ E, E'` of the morphisms `F ⊗_E K ⟶ F ⊗_{E'} K'`. -/
abbrev ConstructibleTwoColimit :=
  (boundedFieldConstructibleStageSystem l X).PairCategory

/-- `D^b_c(X, ℚ̄_ℓ)` is the filtered `2`-colimit of the `E`-stages: with the stage inclusions
`D^b_c(X, E) ⥤ D^b_c(X, ℚ̄_ℓ)`, every object and every morphism is defined at a finite stage, and
equalities of morphisms hold at a finite stage. -/
theorem ConstructibleTwoColimit.isFilteredTwoColimit :
    (boundedFieldConstructibleStageSystem l X).cocone.IsFilteredTwoColimit :=
  StageSystem.cocone_isFilteredTwoColimit _


/-- The objects of `D^b_c(X, E)` lying in `D^{≤ n}`. -/
abbrev boundedFieldConstructibleLE (E : FiniteIntermediateField l) (n : ℤ) :
    ObjectProperty (boundedFieldConstructible E.1 X).FullSubcategory :=
  (_root_.DerivedCategory.TStructure.t.le n).inverseImage (boundedFieldConstructible E.1 X).ι

/-- The objects of `D^b_c(X, E)` lying in `D^{≥ n}`. -/
abbrev boundedFieldConstructibleGE (E : FiniteIntermediateField l) (n : ℤ) :
    ObjectProperty (boundedFieldConstructible E.1 X).FullSubcategory :=
  (_root_.DerivedCategory.TStructure.t.ge n).inverseImage (boundedFieldConstructible E.1 X).ι

/-- The objects of `D^b_c(X, E)` lying in the constructible heart `Sh_c(X, E)`. -/
abbrev boundedFieldConstructibleHeart (E : FiniteIntermediateField l) :
    ObjectProperty (boundedFieldConstructible E.1 X).FullSubcategory :=
  (fieldConstructibleHeart E.1 X).inverseImage (boundedFieldConstructible E.1 X).ι

lemma boundedFieldConstructibleHeart_eq (E : FiniteIntermediateField l) :
    boundedFieldConstructibleHeart l X E =
      boundedFieldConstructibleLE l X E 0 ⊓ boundedFieldConstructibleGE l X E 0 := by
  ext K
  change (boundedFieldConstructible E.1 X K.obj ∧
      _root_.DerivedCategory.TStructure.t.le 0 K.obj) ∧
    _root_.DerivedCategory.TStructure.t.ge 0 K.obj ↔ _ ∧ _
  exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨K.property, h.1⟩, h.2⟩⟩

variable {l X}

/-- The transition functors of `D^b_c` preserve `D^{≤ n}`. -/
lemma boundedFieldConstructibleLE_T {E F : FiniteIntermediateField l} (h : E ≤ F) (n : ℤ)
    (K : (boundedFieldConstructible E.1 X).FullSubcategory)
    (hK : boundedFieldConstructibleLE l X E n K) :
    boundedFieldConstructibleLE l X F n (((boundedFieldConstructibleStageSystem l X).T h).obj K) :=
  le_mapDerivedCategory_obj _ _ X hK

/-- The transition functors of `D^b_c` preserve `D^{≥ n}`. -/
lemma boundedFieldConstructibleGE_T {E F : FiniteIntermediateField l} (h : E ≤ F) (n : ℤ)
    (K : (boundedFieldConstructible E.1 X).FullSubcategory)
    (hK : boundedFieldConstructibleGE l X E n K) :
    boundedFieldConstructibleGE l X F n (((boundedFieldConstructibleStageSystem l X).T h).obj K) :=
  ge_mapDerivedCategory_obj _ _ X hK

/-- The transition functors of `D^b_c` preserve the constructible hearts. -/
lemma boundedFieldConstructibleHeart_T {E F : FiniteIntermediateField l} (h : E ≤ F)
    (K : (boundedFieldConstructible E.1 X).FullSubcategory)
    (hK : boundedFieldConstructibleHeart l X E K) :
    boundedFieldConstructibleHeart l X F (((boundedFieldConstructibleStageSystem l X).T h).obj K) :=
  ⟨⟨(((boundedFieldConstructibleStageSystem l X).T h).obj K).property,
    le_mapDerivedCategory_obj _ _ X hK.1.2⟩, ge_mapDerivedCategory_obj _ _ X hK.2⟩

variable (l X)

/-- The half `D^{≤ n}_c(X, ℚ̄_ℓ)` of the standard `t`-structure on the common-stage category
`D^b_c(X, ℚ̄_ℓ)`. Since the transition functors are `t`-exact, it consists of the objects
`(E, K)` such that `F ⊗_E K ∈ D^{≤ n}_c(X, F)` at some finite stage `F ⊇ E` (equivalently, at
all sufficiently large stages). -/
def constructibleTwoColimitLE (n : ℤ) : ObjectProperty (ConstructibleTwoColimit l X) :=
  (boundedFieldConstructibleStageSystem l X).eventually
    fun E ↦ boundedFieldConstructibleLE l X E n

/-- The half `D^{≥ n}_c(X, ℚ̄_ℓ)` of the standard `t`-structure on the common-stage category
`D^b_c(X, ℚ̄_ℓ)`. -/
def constructibleTwoColimitGE (n : ℤ) : ObjectProperty (ConstructibleTwoColimit l X) :=
  (boundedFieldConstructibleStageSystem l X).eventually
    fun E ↦ boundedFieldConstructibleGE l X E n

instance (n : ℤ) : (constructibleTwoColimitLE l X n).IsClosedUnderIsomorphisms :=
  StageSystem.eventually_isClosedUnderIsomorphisms (S := boundedFieldConstructibleStageSystem l X)
    (P := fun E ↦ boundedFieldConstructibleLE l X E n) (fun h ↦ boundedFieldConstructibleLE_T h n)

instance (n : ℤ) : (constructibleTwoColimitGE l X n).IsClosedUnderIsomorphisms :=
  StageSystem.eventually_isClosedUnderIsomorphisms (S := boundedFieldConstructibleStageSystem l X)
    (P := fun E ↦ boundedFieldConstructibleGE l X E n) (fun h ↦ boundedFieldConstructibleGE_T h n)

/-- Constructible heart, stage `Λ = ℚ̄_ℓ`.

The constructible heart `Sh_c(X, ℚ̄_ℓ) = D^{≤ 0}_c(X, ℚ̄_ℓ) ∩ D^{≥ 0}_c(X, ℚ̄_ℓ)` of the standard
`t`-structure on the common-stage category `D^b_c(X, ℚ̄_ℓ) = 2-colim_E D^b_c(X, E)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.ConstructibleTwoColimit`). By
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitHeart_eq` its objects are the
pairs `(E, K)` with `F ⊗_E K` in the constructible heart `Sh_c(X, F)` of some finite stage
(`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`), and by
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitHeartEquiv` it is the
`2`-colimit of the hearts `Sh_c(X, E)` of the finite stages. -/
def constructibleTwoColimitHeart : ObjectProperty (ConstructibleTwoColimit l X) :=
  constructibleTwoColimitLE l X 0 ⊓ constructibleTwoColimitGE l X 0

/-- An object `(E, K)` of `D^b_c(X, ℚ̄_ℓ)` lies in the constructible heart if and only if
`F ⊗_E K` lies in the constructible heart `Sh_c(X, F)` at some finite stage `F ⊇ E`. -/
theorem constructibleTwoColimitHeart_eq :
    constructibleTwoColimitHeart l X =
      (boundedFieldConstructibleStageSystem l X).eventually
        (boundedFieldConstructibleHeart l X) := by
  rw [constructibleTwoColimitHeart, constructibleTwoColimitLE, constructibleTwoColimitGE,
    ← StageSystem.eventually_inf (S := boundedFieldConstructibleStageSystem l X)
      (P := fun E ↦ boundedFieldConstructibleLE l X E 0) (fun h ↦ boundedFieldConstructibleLE_T h 0)
      (fun E ↦ boundedFieldConstructibleGE l X E 0) (fun h ↦ boundedFieldConstructibleGE_T h 0)]
  congr 1
  funext E
  exact (boundedFieldConstructibleHeart_eq l X E).symm

instance : (constructibleTwoColimitHeart l X).IsClosedUnderIsomorphisms := by
  rw [constructibleTwoColimitHeart_eq]
  exact StageSystem.eventually_isClosedUnderIsomorphisms
    (S := boundedFieldConstructibleStageSystem l X) (P := boundedFieldConstructibleHeart l X)
    boundedFieldConstructibleHeart_T

/-- The stage system `E ↦ Sh_c(X, E)` of the constructible hearts of the finite stages, the
restriction of `AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructibleStageSystem`
(whose transition functors preserve the hearts). -/
noncomputable def constructibleHeartStageSystem :
    StageSystem (fun E : FiniteIntermediateField l ↦
      (boundedFieldConstructibleHeart l X E).FullSubcategory) :=
  (boundedFieldConstructibleStageSystem l X).restrict _ boundedFieldConstructibleHeart_T

/-- The constructible heart of the common-stage category is the `2`-colimit of the
constructible hearts of the finite stages, `2-colim_E Sh_c(X, E) ≌ Sh_c(X, ℚ̄_ℓ)`. -/
noncomputable def constructibleTwoColimitHeartEquiv :
    (constructibleHeartStageSystem l X).PairCategory ≌
      (constructibleTwoColimitHeart l X).FullSubcategory :=
  (StageSystem.restrictEquiv (boundedFieldConstructibleStageSystem l X)
    (boundedFieldConstructibleHeart l X) boundedFieldConstructibleHeart_T).trans
    ((CategoryTheory.Equivalence.refl (C := ConstructibleTwoColimit l X)).congrFullSubcategory
      (by rw [constructibleTwoColimitHeart_eq]; rfl))

end TwoColimit

end DerivedCategory

end AlgebraicGeometry.ProEtale
