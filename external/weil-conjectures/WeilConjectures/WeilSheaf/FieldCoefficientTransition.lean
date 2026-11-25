/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCompIso
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsComp
public import WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars

/-!
# The directed system of the `E`-stages `D^b_{c,W}(X, E)` and its cocone to `D^b_{c,W}(X, ℚ̄_ℓ)`

Following blueprint `definition-weil-structure`, the `ℚ̄_ℓ`-stage of Weil complexes is the
`2`-colimit

`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`

over the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (`PadicAlgCl.FiniteIntermediateField l`), along the
extensions of scalars `F ⊗_E -` for `E ⊆ F`.
In this repository the `E`-stages are `AlgebraicGeometry.FieldWeilComplex k₀ E X` and the
`ℚ̄_ℓ`-stage is realised directly as `AlgebraicGeometry.WeilComplex k₀ l X`, with the functors
`AlgebraicGeometry.FieldWeilComplex.toWeilComplex` from the `E`-stages
(`WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars`). This file constructs

- the transition functors: for a continuous map `e : Λ → Λ'` of finite extensions of `ℚ_ℓ`, the
  extension of scalars `Λ' ⊗_Λ -` of pro-étale sheaves
  (`AlgebraicGeometry.ProEtale.fieldExtendScalars`) commutes with the Frobenius pullbacks
  (`AlgebraicGeometry.fieldExtendScalarsFrobeniusIso`), so it induces an exact functor of
  pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalars`) and a functor
  `D^b_{c,W}(X, Λ) ⥤ D^b_{c,W}(X, Λ')` (`AlgebraicGeometry.FieldWeilComplex.extendScalars`,
  and `AlgebraicGeometry.FieldWeilComplex.transition` for `E ⊆ F`);
- their compatibility with the functors to the `ℚ̄_ℓ`-stage,
  `ℚ̄_ℓ ⊗_{Λ'} (Λ' ⊗_Λ -) ≅ ℚ̄_ℓ ⊗_Λ -`, as Weil complexes
  (`AlgebraicGeometry.FieldWeilComplex.extendScalarsCompExtendScalarsToAdicIso`): on pro-étale
  sheaves this is `AlgebraicGeometry.ProEtale.fieldExtendScalarsCompExtendScalarsToAdicIso`,
  and it is compatible with the Weil structures
  (`AlgebraicGeometry.fieldExtendScalarsCompExtendScalarsToAdicIso_frobenius`);
- hence the cocone of categories `E ↦ (D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ))` on the directed
  system of the `E`-stages, with vertex the `ℚ̄_ℓ`-stage
  (`AlgebraicGeometry.FieldWeilComplex.cocone`), in the sense of
  `WeilConjectures.CategoryTheory.FilteredTwoColimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section Transition

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The extension of scalars `Λ' ⊗_Λ -` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*`. -/
noncomputable def fieldExtendScalarsFrobeniusIso :
    fieldExtendScalars he hc (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⋙
        FieldWeilSheaf.frobeniusPullback k₀ Λ' X ≅
      FieldWeilSheaf.frobeniusPullback k₀ Λ X ⋙
        fieldExtendScalars he hc (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  Functor.isoWhiskerLeft _ (fieldUpperStarIsoLowerStarInv Λ'
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).symm ≪≫
    (fieldUpperStarCompExtendScalarsIso he hc
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).symm ≪≫
    Functor.isoWhiskerRight
      (fieldUpperStarIsoLowerStarInv Λ
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso) _

/-- The extension of scalars `Λ' ⊗_Λ -` of pro-étale Weil sheaves. -/
noncomputable def ProEtaleFieldWeilSheaf.extendScalars :
    ProEtaleFieldWeilSheaf k₀ Λ X ⥤ ProEtaleFieldWeilSheaf k₀ Λ' X :=
  IsoAlgebra.mapOfNatIso (fieldExtendScalarsFrobeniusIso he hc k₀ X)

instance : (ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X).Additive :=
  IsoAlgebra.additive_mapOfNatIso _

instance : PreservesFiniteLimits (ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X) :=
  IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

instance : PreservesFiniteColimits (ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X) :=
  IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

/-- The transition functor `D^b_{c,W}(X, Λ) ⥤ D^b_{c,W}(X, Λ')`, induced on derived categories by
the exact extension of scalars `Λ' ⊗_Λ -` of pro-étale Weil sheaves, which preserves
constructibility. -/
noncomputable def FieldWeilComplex.extendScalars :
    FieldWeilComplex k₀ Λ X ⥤ FieldWeilComplex k₀ Λ' X :=
  (FieldWeilComplex.objectProperty k₀ Λ X).liftFullSubcategory
    (FieldWeilComplex.objectProperty k₀ Λ' X)
    (ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X).mapDerivedCategory
    fun K hK ↦ ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
      (FieldWeilSheaf.objectProperty k₀ Λ' X).prop_of_iso
        (((ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X
          ).mapDerivedCategoryHomologyFunctorIso n).app K) ((hK.2 n).extendScalars he hc)⟩

end Transition

section Comp

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  {e' : Λ' →ₐ[ℚ_[l]] PadicAlgCl l} (he' : Continuous e')
  (hc' : Continuous (algebraMap ℚ_[l] Λ'))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The identification `ℚ̄_ℓ ⊗_Λ - ≅ ℚ̄_ℓ ⊗_{Λ'} (Λ' ⊗_Λ -)` is compatible with the commutations
of the extensions of scalars with the Frobenius pullbacks: the commutation of `ℚ̄_ℓ ⊗_Λ -` is the
composite of those of `Λ' ⊗_Λ -` and `ℚ̄_ℓ ⊗_{Λ'} -`. This follows from the compatibility with
the pullback along the geometric Frobenius
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsCompExtendScalarsToAdicIso_paste`). -/
lemma fieldExtendScalarsCompExtendScalarsToAdicIso_frobenius :
    Functor.whiskerRight (fieldExtendScalarsCompExtendScalarsToAdicIso he hc he' hc'
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom (WeilSheaf.frobeniusPullback k₀ l X) ≫
      (IsoAlgebra.compCommIso (fieldExtendScalarsFrobeniusIso he hc k₀ X)
        (fieldExtendScalarsToAdicFrobeniusIso he' hc' k₀ X)).hom =
    (fieldExtendScalarsToAdicFrobeniusIso (e := e'.comp e) (he'.comp he) hc k₀ X).hom ≫
      Functor.whiskerLeft (FieldWeilSheaf.frobeniusPullback k₀ Λ X)
        (fieldExtendScalarsCompExtendScalarsToAdicIso he hc he' hc'
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  have K := congr_app (fieldExtendScalarsCompExtendScalarsToAdicIso_paste he hc he' hc'
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    IsoAlgebra.compCommIso_hom_app, fieldExtendScalarsFrobeniusIso,
    fieldExtendScalarsToAdicFrobeniusIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.comp_obj, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  erw [NatTrans.naturality_assoc]
  rw [reassoc_of% K]
  congr 2
  exact ((fieldExtendScalarsCompExtendScalarsToAdicIso he hc he' hc'
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom.naturality _).symm

/-- Extending scalars of pro-étale Weil sheaves from `Λ` to `Λ'` and then to `ℚ̄_ℓ` is extending
scalars from `Λ` to `ℚ̄_ℓ`. -/
noncomputable def ProEtaleFieldWeilSheaf.extendScalarsCompExtendScalarsToAdicIso :
    ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X ⋙
        ProEtaleFieldWeilSheaf.extendScalarsToAdic he' hc' k₀ X ≅
      ProEtaleFieldWeilSheaf.extendScalarsToAdic (e := e'.comp e) (he'.comp he) hc k₀ X :=
  IsoAlgebra.mapOfNatIsoCompIsoOfIso _
    (fieldExtendScalarsCompExtendScalarsToAdicIso_frobenius he hc he' hc' k₀ X)

variable [Fact (ringChar k₀ ≠ l)]

/-- Blueprint `definition-weil-structure`: the compatibility of the transition functors with
the functors to the stage `ℚ̄_ℓ`.

Extending scalars from `D^b_{c,W}(X, Λ)` to `D^b_{c,W}(X, Λ')` and then to `D^b_{c,W}(X, ℚ̄_ℓ)`
is extending scalars from `D^b_{c,W}(X, Λ)` to `D^b_{c,W}(X, ℚ̄_ℓ)`: the exact functors of
pro-étale Weil sheaves agree
(`AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalarsCompExtendScalarsToAdicIso`), hence so
do the functors they induce on derived categories. -/
noncomputable def FieldWeilComplex.extendScalarsCompExtendScalarsToAdicIso :
    FieldWeilComplex.extendScalars he hc k₀ X ⋙
        FieldWeilComplex.extendScalarsToAdic he' hc' k₀ X ≅
      FieldWeilComplex.extendScalarsToAdic (e := e'.comp e) (he'.comp he) hc k₀ X :=
  let β := Functor.mapDerivedCategoryCompNatIso
    (ProEtaleFieldWeilSheaf.extendScalarsCompExtendScalarsToAdicIso he hc he' hc' k₀ X)
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (β.app K.obj))
    fun f ↦ ObjectProperty.hom_ext _ (β.hom.naturality f.hom)

end Comp

section FiniteSubextension

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (k₀ : Type u) [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The inclusion `E ⊆ F` of finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ` is continuous. -/
lemma _root_.PadicAlgCl.continuous_inclusion_finiteIntermediateField
    {E F : FiniteIntermediateField l}
    (h : E ≤ F) : Continuous (IntermediateField.inclusion (show E.1 ≤ F.1 from h)) :=
  continuous_subtype_val.subtype_mk _

/-- The structure map `ℚ_ℓ → E` of a subextension `E ⊆ ℚ̄_ℓ` is continuous. -/
lemma _root_.PadicAlgCl.continuous_algebraMap_intermediateField
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) : Continuous (algebraMap ℚ_[l] E) :=
  (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).subtype_mk _

/-- Blueprint `definition-weil-structure`: the transition functor
`D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, F)` of the directed system of the `E`-stages, for finite
extensions `E ⊆ F` of `ℚ_ℓ` inside `ℚ̄_ℓ`: the extension of scalars `F ⊗_E -`
(`AlgebraicGeometry.FieldWeilComplex.extendScalars` along the inclusion `E → F`). -/
noncomputable def FieldWeilComplex.transition {E F : FiniteIntermediateField l} (h : E ≤ F) :
    FieldWeilComplex k₀ E.1 X ⥤ FieldWeilComplex k₀ F.1 X :=
  FieldWeilComplex.extendScalars (continuous_inclusion_finiteIntermediateField h)
    (continuous_algebraMap_intermediateField E.1) k₀ X

/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex, the `2`-colimit
`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`.

The cocone of categories, on the directed system `E ↦ D^b_{c,W}(X, E)` of the stages at the
finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` with the extensions of scalars
`F ⊗_E - : D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, F)` as transition functors
(`AlgebraicGeometry.FieldWeilComplex.transition`), with vertex the `ℚ̄_ℓ`-stage
`D^b_{c,W}(X, ℚ̄_ℓ)` (`AlgebraicGeometry.WeilComplex`): the functors to the vertex are the
extensions of scalars `ℚ̄_ℓ ⊗_E -` (`AlgebraicGeometry.FieldWeilComplex.toWeilComplex`), and
`ℚ̄_ℓ ⊗_F (F ⊗_E -) ≅ ℚ̄_ℓ ⊗_E -`
(`AlgebraicGeometry.FieldWeilComplex.extendScalarsCompExtendScalarsToAdicIso`). -/
noncomputable def FieldWeilComplex.cocone :
    CategoryCocone (fun E : FiniteIntermediateField l ↦ FieldWeilComplex k₀ E.1 X)
      (WeilComplex k₀ l X) where
  T h := FieldWeilComplex.transition k₀ X h
  Φ E := FieldWeilComplex.toWeilComplex k₀ X E.1
  iso {E F} h := FieldWeilComplex.extendScalarsCompExtendScalarsToAdicIso
    (continuous_inclusion_finiteIntermediateField h)
    (continuous_algebraMap_intermediateField E.1) continuous_subtype_val
    (continuous_algebraMap_intermediateField F.1) k₀ X

end FiniteSubextension

end AlgebraicGeometry
