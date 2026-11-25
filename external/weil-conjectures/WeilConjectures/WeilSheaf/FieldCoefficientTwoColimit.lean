/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Const
public import WeilConjectures.WeilSheaf.FieldCoefficientTransition

/-!
# `D^b_{c,W}(X, ℚ̄_ℓ)` as the `2`-colimit of the `E`-stages

Blueprint `definition-weil-structure` defines

`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`

over the directed set of the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, along the extensions of scalars
`F ⊗_E -`, with the common-stage construction: objects are pairs `(E, K)` and morphisms are
represented at a common finite stage. This file makes this a genuine definition:

- the extensions of scalars `D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, F)` form a stage system
  (`AlgebraicGeometry.FieldWeilComplex.stageSystem`, in the sense of
  `CategoryTheory.StageSystem`): the associativity constraints `G ⊗_F (F ⊗_E -) ≅ G ⊗_E -`
  (`AlgebraicGeometry.FieldWeilComplex.extendScalarsCompIso`) satisfy the cocycle condition,
  which holds for the extensions of scalars of pro-étale sheaves
  (`AlgebraicGeometry.ProEtale.fieldExtendScalarsCompIso_cocycle`) and passes to Weil sheaves and
  to derived categories (`CategoryTheory.Functor.mapDerivedCategoryCompNatIso_cocycle`);
- `AlgebraicGeometry.WeilComplexTwoColimit k₀ l X` is its pair category, the `2`-colimit;
- the functors `ℚ̄_ℓ ⊗_E - : D^b_{c,W}(X, E) ⥤ WeilComplex k₀ l X` to the `ℚ̄_ℓ`-stage of
  `WeilConjectures.WeilSheaf.Category` (`AlgebraicGeometry.FieldWeilComplex.toWeilComplex`) are
  compatible with the associativity constraints, hence induce the comparison functor
  `AlgebraicGeometry.WeilComplexTwoColimit.toWeilComplex` from the `2`-colimit.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section Comp

variable {l : ℕ} [Fact l.Prime] {Λ₁ Λ₂ Λ₃ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁]
  [NormedField Λ₂] [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃]
  [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂] [Algebra ℚ_[l] Λ₃] [FiniteDimensional ℚ_[l] Λ₂]
  [FiniteDimensional ℚ_[l] Λ₃] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  (he₁ : Continuous e₁) (he₂ : Continuous e₂) (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁))
  (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The identification `Λ₃ ⊗_{Λ₁} - ≅ Λ₃ ⊗_{Λ₂} (Λ₂ ⊗_{Λ₁} -)` is compatible with the
commutations of the extensions of scalars with the Frobenius pullbacks. -/
lemma fieldExtendScalarsCompIso_frobenius :
    Functor.whiskerRight (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom
          (FieldWeilSheaf.frobeniusPullback k₀ Λ₃ X) ≫
      (IsoAlgebra.compCommIso (fieldExtendScalarsFrobeniusIso he₁ hc₁ k₀ X)
        (fieldExtendScalarsFrobeniusIso he₂ hc₂ k₀ X)).hom =
    (fieldExtendScalarsFrobeniusIso (e := e₂.comp e₁) (he₂.comp he₁) hc₁ k₀ X).hom ≫
      Functor.whiskerLeft (FieldWeilSheaf.frobeniusPullback k₀ Λ₁ X)
        (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  have K := congr_app (fieldExtendScalarsCompIso_paste
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom he₁ he₂ hc₁ hc₂) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    IsoAlgebra.compCommIso_hom_app, fieldExtendScalarsFrobeniusIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.comp_obj, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  erw [NatTrans.naturality_assoc]
  rw [reassoc_of% K]
  congr 2
  exact ((fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom.naturality _).symm

/-- Extending scalars of pro-étale Weil sheaves from `Λ₁` to `Λ₂` and then to `Λ₃` is extending
scalars from `Λ₁` to `Λ₃`. -/
noncomputable def ProEtaleFieldWeilSheaf.extendScalarsCompIso :
    ProEtaleFieldWeilSheaf.extendScalars he₁ hc₁ k₀ X ⋙
        ProEtaleFieldWeilSheaf.extendScalars he₂ hc₂ k₀ X ≅
      ProEtaleFieldWeilSheaf.extendScalars (e := e₂.comp e₁) (he₂.comp he₁) hc₁ k₀ X :=
  IsoAlgebra.mapOfNatIsoCompIsoOfIso _ (fieldExtendScalarsCompIso_frobenius he₁ he₂ hc₁ hc₂ k₀ X)

/-- Blueprint `definition-weil-structure`: the associativity constraint of the transition
functors.

Extending scalars from `D^b_{c,W}(X, Λ₁)` to `D^b_{c,W}(X, Λ₂)` and then to `D^b_{c,W}(X, Λ₃)` is
extending scalars from `D^b_{c,W}(X, Λ₁)` to `D^b_{c,W}(X, Λ₃)`. -/
noncomputable def FieldWeilComplex.extendScalarsCompIso :
    FieldWeilComplex.extendScalars he₁ hc₁ k₀ X ⋙ FieldWeilComplex.extendScalars he₂ hc₂ k₀ X ≅
      FieldWeilComplex.extendScalars (e := e₂.comp e₁) (he₂.comp he₁) hc₁ k₀ X :=
  let β := Functor.mapDerivedCategoryCompNatIso
    (ProEtaleFieldWeilSheaf.extendScalarsCompIso he₁ he₂ hc₁ hc₂ k₀ X)
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (β.app K.obj))
    fun f ↦ ObjectProperty.hom_ext _ (β.hom.naturality f.hom)

end Comp

section Cocycle

variable {l : ℕ} [Fact l.Prime] {Λ₁ Λ₂ Λ₃ Λ₄ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁]
  [NormedField Λ₂] [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃]
  [NormedField Λ₄] [IsUltrametricDist Λ₄] [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂]
  [Algebra ℚ_[l] Λ₃] [Algebra ℚ_[l] Λ₄] [FiniteDimensional ℚ_[l] Λ₂] [FiniteDimensional ℚ_[l] Λ₃]
  [FiniteDimensional ℚ_[l] Λ₄] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  {e₃ : Λ₃ →ₐ[ℚ_[l]] Λ₄} (he₁ : Continuous e₁) (he₂ : Continuous e₂) (he₃ : Continuous e₃)
  (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁)) (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂))
  (hc₃ : Continuous (algebraMap ℚ_[l] Λ₃))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The associativity constraints of the extensions of scalars of pro-étale Weil sheaves satisfy
the cocycle condition. -/
lemma ProEtaleFieldWeilSheaf.extendScalarsCompIso_cocycle (K : ProEtaleFieldWeilSheaf k₀ Λ₁ X) :
    (ProEtaleFieldWeilSheaf.extendScalars he₃ hc₃ k₀ X).map
        ((ProEtaleFieldWeilSheaf.extendScalarsCompIso he₁ he₂ hc₁ hc₂ k₀ X).hom.app K) ≫
      (ProEtaleFieldWeilSheaf.extendScalarsCompIso (e₁ := e₂.comp e₁) (he₂.comp he₁) he₃ hc₁ hc₃
        k₀ X).hom.app K =
    (ProEtaleFieldWeilSheaf.extendScalarsCompIso he₂ he₃ hc₂ hc₃ k₀ X).hom.app
        ((ProEtaleFieldWeilSheaf.extendScalars he₁ hc₁ k₀ X).obj K) ≫
      (ProEtaleFieldWeilSheaf.extendScalarsCompIso (e₂ := e₃.comp e₂) he₁ (he₃.comp he₂) hc₁ hc₂
        k₀ X).hom.app K := by
  refine ObjectProperty.hom_ext _ (Algebra.Hom.ext ?_)
  have h := congr_app (fieldExtendScalarsCompIso_cocycle
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber he₁ he₂ he₃ hc₁ hc₂ hc₃) K.carrier
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  change (fieldExtendScalars he₃ hc₃ _).map ((fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂
      _).inv.app K.carrier) ≫ (fieldExtendScalarsCompIso (e₁ := e₂.comp e₁) (he₂.comp he₁) he₃
      hc₁ hc₃ _).inv.app K.carrier =
    (fieldExtendScalarsCompIso he₂ he₃ hc₂ hc₃ _).inv.app
      ((fieldExtendScalars he₁ hc₁ _).obj K.carrier) ≫
      (fieldExtendScalarsCompIso (e₂ := e₃.comp e₂) he₁ (he₃.comp he₂) hc₁ hc₂ _).inv.app K.carrier
  rw [← cancel_epi ((fieldExtendScalarsCompIso (e₁ := e₂.comp e₁) (he₂.comp he₁) he₃ hc₁ hc₃
    _).hom.app K.carrier ≫ (fieldExtendScalars he₃ hc₃ _).map
      ((fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ _).hom.app K.carrier))]
  conv_rhs => rw [h]
  simp [← Functor.map_comp_assoc]

variable [FiniteDimensional ℚ_[l] Λ₁]

/-- The associativity constraints of the extensions of scalars of pro-étale Weil sheaves satisfy
the cocycle condition, the last one being the extension of scalars to `ℚ̄_ℓ`. -/
lemma ProEtaleFieldWeilSheaf.extendScalarsCompIso_cocycle_adic {e₃ : Λ₃ →ₐ[ℚ_[l]] PadicAlgCl l}
    (he₃ : Continuous e₃) (K : ProEtaleFieldWeilSheaf k₀ Λ₁ X) :
    (ProEtaleFieldWeilSheaf.extendScalarsToAdic he₃ hc₃ k₀ X).map
        ((ProEtaleFieldWeilSheaf.extendScalarsCompIso he₁ he₂ hc₁ hc₂ k₀ X).hom.app K) ≫
      (ProEtaleFieldWeilSheaf.extendScalarsCompExtendScalarsToAdicIso (e := e₂.comp e₁)
        (he₂.comp he₁) hc₁ he₃ hc₃ k₀ X).hom.app K =
    (ProEtaleFieldWeilSheaf.extendScalarsCompExtendScalarsToAdicIso he₂ hc₂ he₃ hc₃ k₀ X).hom.app
        ((ProEtaleFieldWeilSheaf.extendScalars he₁ hc₁ k₀ X).obj K) ≫
      (ProEtaleFieldWeilSheaf.extendScalarsCompExtendScalarsToAdicIso (e' := e₃.comp e₂) he₁ hc₁
        (he₃.comp he₂) hc₂ k₀ X).hom.app K := by
  refine ObjectProperty.hom_ext _ (Algebra.Hom.ext ?_)
  have h := congr_app (fieldExtendScalarsCompIso_cocycle_adic
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber he₁ he₂ hc₁ hc₂ hc₃ he₃) K.carrier
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  change (fieldExtendScalarsToAdic he₃ hc₃ _).map ((fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂
      _).inv.app K.carrier) ≫ (fieldExtendScalarsCompExtendScalarsToAdicIso (e := e₂.comp e₁)
      (he₂.comp he₁) hc₁ he₃ hc₃ _).inv.app K.carrier =
    (fieldExtendScalarsCompExtendScalarsToAdicIso he₂ hc₂ he₃ hc₃ _).inv.app
      ((fieldExtendScalars he₁ hc₁ _).obj K.carrier) ≫
      (fieldExtendScalarsCompExtendScalarsToAdicIso (e' := e₃.comp e₂) he₁ hc₁ (he₃.comp he₂) hc₂
        _).inv.app K.carrier
  rw [← cancel_epi ((fieldExtendScalarsCompExtendScalarsToAdicIso (e := e₂.comp e₁)
    (he₂.comp he₁) hc₁ he₃ hc₃ _).hom.app K.carrier ≫ (fieldExtendScalarsToAdic he₃ hc₃ _).map
      ((fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ _).hom.app K.carrier))]
  conv_rhs => rw [h]
  simp [← Functor.map_comp_assoc]

end Cocycle

section TwoColimit

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `definition-weil-structure`: the stage system of the `E`-stages.

The directed system `E ↦ D^b_{c,W}(X, E)` over the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, with
the extensions of scalars `F ⊗_E -` as transition functors
(`AlgebraicGeometry.FieldWeilComplex.transition`) and the identifications
`G ⊗_F (F ⊗_E -) ≅ G ⊗_E -` as associators
(`AlgebraicGeometry.FieldWeilComplex.extendScalarsCompIso`), which satisfy the cocycle
condition. -/
noncomputable def FieldWeilComplex.stageSystem :
    StageSystem (fun E : FiniteIntermediateField l ↦ FieldWeilComplex k₀ E.1 X) where
  T h := FieldWeilComplex.transition k₀ X h
  assoc h h' := FieldWeilComplex.extendScalarsCompIso
    (continuous_inclusion_finiteIntermediateField h)
    (continuous_inclusion_finiteIntermediateField h')
    (continuous_algebraMap_intermediateField _) (continuous_algebraMap_intermediateField _) k₀ X
  cocycle h h' h'' K := ObjectProperty.hom_ext _
    (Functor.mapDerivedCategoryCompNatIso_cocycle _ _ _ _
      (ProEtaleFieldWeilSheaf.extendScalarsCompIso_cocycle
        (continuous_inclusion_finiteIntermediateField h)
        (continuous_inclusion_finiteIntermediateField h')
        (continuous_inclusion_finiteIntermediateField h'')
        (continuous_algebraMap_intermediateField _) (continuous_algebraMap_intermediateField _)
        (continuous_algebraMap_intermediateField _) k₀ X) K.obj)

/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex, the stage `ℚ̄_ℓ`.

`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`, the `2`-colimit over the finite extensions
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` of the categories of `E`-Weil complexes (`AlgebraicGeometry.FieldWeilComplex`)
along the extensions of scalars `F ⊗_E -`, with the common-stage construction: the pair category of
the stage system `AlgebraicGeometry.FieldWeilComplex.stageSystem`, whose objects are the pairs
`(E, K)` of a finite stage `E` and an `E`-Weil complex `K`, and whose morphisms `(E, K) ⟶ (E', K')`
form the filtered colimit over the common finite stages `F ⊇ E, E'` of the morphisms
`F ⊗_E K ⟶ F ⊗_{E'} K'` (`CategoryTheory.StageSystem.PairCategory`). It maps to the `ℚ̄_ℓ`-stage
`AlgebraicGeometry.WeilComplex` of `WeilConjectures.WeilSheaf.Category` by
`AlgebraicGeometry.WeilComplexTwoColimit.toWeilComplex`. -/
abbrev WeilComplexTwoColimit (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
  (FieldWeilComplex.stageSystem (l := l) k₀ X).PairCategory

/-- Blueprint `definition-weil-structure`: `D^b_{c,W}(X, ℚ̄_ℓ)` is the filtered `2`-colimit of the
`E`-stages: with the stage inclusions `D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)`, it satisfies
`CategoryTheory.CategoryCocone.IsFilteredTwoColimit` (every object and every morphism is defined
at a finite stage, and equalities of morphisms hold at a finite stage). -/
theorem WeilComplexTwoColimit.isFilteredTwoColimit :
    (FieldWeilComplex.stageSystem (l := l) k₀ X).cocone.IsFilteredTwoColimit :=
  StageSystem.cocone_isFilteredTwoColimit _

variable [Fact (ringChar k₀ ≠ l)]

/-- The functors `ℚ̄_ℓ ⊗_E -` to the `ℚ̄_ℓ`-stage are compatible with the associativity
constraints of the transition functors. -/
lemma FieldWeilComplex.cocone_iso_coherence {E F G : FiniteIntermediateField l} (h : E ≤ F)
    (h' : F ≤ G) (K : FieldWeilComplex k₀ E.1 X) :
    (FieldWeilComplex.toWeilComplex k₀ X G.1).map
        (((FieldWeilComplex.stageSystem k₀ X).assoc h h').hom.app K) ≫
      ((FieldWeilComplex.cocone k₀ X).iso (h.trans h')).hom.app K =
    ((FieldWeilComplex.cocone k₀ X).iso h').hom.app
        (((FieldWeilComplex.stageSystem k₀ X).T h).obj K) ≫
      ((FieldWeilComplex.cocone k₀ X).iso h).hom.app K :=
  ObjectProperty.hom_ext _
    (Functor.mapDerivedCategoryCompNatIso_cocycle _ _ _ _
      (ProEtaleFieldWeilSheaf.extendScalarsCompIso_cocycle_adic
        (continuous_inclusion_finiteIntermediateField h)
        (continuous_inclusion_finiteIntermediateField h')
        (continuous_algebraMap_intermediateField _) (continuous_algebraMap_intermediateField _)
        (continuous_algebraMap_intermediateField _) k₀ X continuous_subtype_val) K.obj)

/-- The comparison functor `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E) ⥤ WeilComplex k₀ l X`
from the `2`-colimit to the `ℚ̄_ℓ`-stage of `WeilConjectures.WeilSheaf.Category`, induced by the
extensions of scalars `ℚ̄_ℓ ⊗_E -` (`AlgebraicGeometry.FieldWeilComplex.cocone`):
`(E, K) ↦ ℚ̄_ℓ ⊗_E K`. -/
noncomputable def WeilComplexTwoColimit.toWeilComplex :
    WeilComplexTwoColimit k₀ l X ⥤ WeilComplex k₀ l X :=
  StageSystem.descFunctor (fun E ↦ FieldWeilComplex.toWeilComplex k₀ X E.1)
    (fun h ↦ (FieldWeilComplex.cocone k₀ X).iso h)
    (fun h h' K ↦ FieldWeilComplex.cocone_iso_coherence k₀ X h h' K)

/-- The comparison functor restricts on the stage `E` to `ℚ̄_ℓ ⊗_E -`. -/
noncomputable def WeilComplexTwoColimit.ιCompToWeilComplexIso (E : FiniteIntermediateField l) :
    (FieldWeilComplex.stageSystem k₀ X).ι E ⋙ WeilComplexTwoColimit.toWeilComplex k₀ X ≅
      FieldWeilComplex.toWeilComplex k₀ X E.1 :=
  StageSystem.ιCompDescFunctorIso _ _ _ E

end TwoColimit

end AlgebraicGeometry
