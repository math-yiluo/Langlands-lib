/-
Copyright (c) 2026 The Weil conjectures formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (u9 C1)
-/
module

public import WeilConjectures.WeilSheaf.CondensedWeilUpperShriekOpenImmersion
public import WeilConjectures.WeilSheaf.CondensedModelWeilDerived

/-!
# The adic Weil `Rf^!` in the condensed model

The adic Weil complexes `WeilComplex k₀ l X` are equivalent to the bounded constructible condensed
Weil complexes (`WeilComplex.condensedWeilEquiv`, the restriction of
`ProEtaleWeilSheaf.derivedEquivCondensed`). Under this equivalence, the adic `Rf₀!`
(`WeilComplex.derivedLowerShriek`) is the condensed `Rf₀! = Rg_* ∘ D(i_!)`
(`WeilComplex.condensedDerivedLowerShriek`, from the upstream
`WeilComplex.derivedLowerShriekCompToCondensedIso`), so the adic `Rf^!` is the condensed one
(`WeilComplex.condensedUpperShriek`), by uniqueness of right adjoints.

## Main result

`WeilComplex.exists_adicSheafEquivCondensedMod_forget_upperShriek_obj_iso_isWeilEquivariant`: the
condensed model of the underlying complex of the adic `Rf^! L` is the geometric `ī^* ḡ^! L̄`, by an
isomorphism carrying the (transported) Frobenius structure of `Rf^! L` to the exceptional datum
`WeilComplex.condensedUpperShriekExceptionalDatum`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The inverse of an equivariant isomorphism is equivariant. -/
lemma IsWeilEquivariant.inv {C : Type*} [Category* C] (G : C ⥤ C) {M N : C}
    {φM : G.obj M ⟶ M} {φN : G.obj N ⟶ N} (u : M ≅ N)
    (hu : IsWeilEquivariant G φM φN u.hom) : IsWeilEquivariant G φN φM u.inv := by
  rw [IsWeilEquivariant] at hu ⊢
  rw [← cancel_mono u.hom, Category.assoc, Category.assoc, u.inv_hom_id, Category.comp_id, ← hu,
    ← Category.assoc, ← G.map_comp, u.inv_hom_id, G.map_id, Category.id_comp]

end CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

open ProEtale

attribute [local instance] Compactification.over

attribute [local instance 1100] CategoryTheory.instOverClass

section Equivalence

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀) in
/-- An object of the derived category of pro-étale Weil sheaves is a Weil complex if and only if
its condensed model is a bounded constructible condensed Weil complex. -/
theorem condensedWeilObjectProperty_derivedEquivCondensed_functor_obj_iff
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    condensedWeilObjectProperty k₀ l X
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K) ↔
      objectProperty k₀ l X K := by
  exact (ObjectProperty.prop_iff_of_iso (condensedBoundedConstructible k₀ l X)
    ((IsoAlgebra.derivedExactForgetCommIso
      (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).app K)).trans
    ((boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) _).symm.trans
      (objectProperty_iff K).symm)

variable (k₀) in
/-- **Weil complexes in the condensed model**: the adic Weil complexes on `X` are equivalent to the
bounded constructible condensed Weil complexes, by the restriction of
`ProEtaleWeilSheaf.derivedEquivCondensed`. -/
noncomputable def condensedWeilEquiv :
    WeilComplex k₀ l X ≌ (condensedWeilObjectProperty k₀ l X).FullSubcategory where
  functor := (objectProperty k₀ l X).liftFullSubcategory _
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor
    fun K hK ↦ (condensedWeilObjectProperty_derivedEquivCondensed_functor_obj_iff k₀ l X K).2 hK
  inverse := ObjectProperty.liftFullSubcategory _ _
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).inverse
    fun K hK ↦ (condensedWeilObjectProperty_derivedEquivCondensed_functor_obj_iff k₀ l X _).1
      (ObjectProperty.prop_of_iso _
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).counitIso.app K).symm hK)
  unitIso := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).unitIso.app K.obj))
    fun f ↦ ObjectProperty.hom_ext _
      ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).unit.naturality f.hom)
  counitIso := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).counitIso.app K.obj))
    fun f ↦ ObjectProperty.hom_ext _
      ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).counit.naturality f.hom)
  functor_unitIso_comp K := ObjectProperty.hom_ext _
    ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor_unit_comp K.obj)

end Equivalence

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

instance : IsOpenImmersion (shriekCompactification k₀ f).i :=
  (shriekCompactification k₀ f).isOpenImmersion

instance : IsOpenImmersion (condensedOpenImmersionMap k₀ f) :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion)
    (shriekCompactification k₀ f).i _ inferInstance

variable (k₀) in
/-- The Frobenius exchange of the condensed extension by zero along `ī`. -/
noncomputable abbrev condensedOpenImmersionShriekExchange :=
  CondensedRing.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
    (Profinite.padicAlgClRingObj l) (shriekCompactification k₀ f).i
    (comp_over (shriekCompactification k₀ f).i (Spec (CommRingCat.of k₀)))

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
variable (k₀) in
/-- The condensed Weil extension by zero `D(i_!)` along the open immersion of the
compactification preserves bounded constructible condensed Weil complexes. -/
theorem condensedWeilObjectProperty_extensionByZero
    (M : _root_.DerivedCategory (IsoAlgebra (condensedFrobenius k₀ l X)))
    (hM : condensedWeilObjectProperty k₀ l X M) :
    condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z
      ((IsoAlgebra.mapOfNatIso (condensedOpenImmersionShriekExchange k₀ l f)).mapDerivedCategory.obj
        M) := by
  have : CompactSpace ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace
      ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : IsNoetherian ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    ⟨⟩
  exact ObjectProperty.prop_of_iso (condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z)
    ((IsoAlgebra.derivedExactForgetCommIso (condensedOpenImmersionShriekExchange k₀ l f)).app M).symm
    (CondensedRing.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _
      (condensedOpenImmersionMap k₀ f) _ hM)

variable (k₀) in
/-- **The condensed `Rf₀! = Rg_* ∘ D(i_!)`** on bounded constructible condensed Weil complexes. -/
noncomputable def condensedDerivedLowerShriek :
    (condensedWeilObjectProperty k₀ l X).FullSubcategory ⥤
      (condensedWeilObjectProperty k₀ l Y).FullSubcategory :=
  ObjectProperty.liftFullSubcategory _ _
      (IsoAlgebra.mapOfNatIso (condensedOpenImmersionShriekExchange k₀ l f)).mapDerivedCategory
      (condensedWeilObjectProperty_extensionByZero k₀ l f) ⋙
    ObjectProperty.liftFullSubcategory _ _
      (IsoAlgebra.mapOfNatIso (condensedProperExchange k₀ l f)).rightDerivedFunctor
      (condensedWeilObjectProperty_rightDerivedFunctor k₀ l f (condensedProperPreserves k₀ l f))

variable (k₀) in
/-- The derived adjunction `D(i_!) ⊣ D(i^*)` of condensed Weil complexes along the open immersion
of the compactification. -/
noncomputable def condensedWeilExtensionByZeroUpperStarAdjunction :
    (IsoAlgebra.mapOfNatIso (condensedOpenImmersionShriekExchange k₀ l f)).mapDerivedCategory ⊣
      (IsoAlgebra.mapOfNatIso (condensedOpenImmersionExchange k₀ l f)).mapDerivedCategory :=
  (CondensedRing.weilExtensionByZeroUpperStarAdjunction (Profinite.padicAlgClRingObj l)
    (shriekCompactification k₀ f).i
    (comp_over (shriekCompactification k₀ f).i (Spec (CommRingCat.of k₀)))
    ).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (CondensedRing.geometricFiberMapWeilUpperStar (Profinite.padicAlgClRingObj l)
      (shriekCompactification k₀ f).i
      (comp_over (shriekCompactification k₀ f).i
        (Spec (CommRingCat.of k₀)))).rightDerivedFunctorIsoMapDerivedCategory

variable (k₀) in
/-- **The condensed adjunction `Rf₀! ⊣ Rf^!`.** -/
noncomputable def condensedDerivedLowerShriekUpperShriekAdjunction :
    condensedDerivedLowerShriek k₀ l f ⊣ condensedUpperShriek k₀ l f :=
  (ObjectProperty.liftFullSubcategoryAdjunction
    (condensedWeilExtensionByZeroUpperStarAdjunction k₀ l f)
    (condensedWeilObjectProperty_extensionByZero k₀ l f)
    (condensedWeilObjectProperty_openImmersionUpperStar k₀ l f)).comp
    (condensedWeilProperAdjunction k₀ l f)

variable (k₀) in
/-- **The adic `Rf₀!` is the condensed one** under `condensedWeilEquiv`, from the upstream
`WeilComplex.derivedLowerShriekCompToCondensedIso`. -/
noncomputable def condensedDerivedLowerShriekCompIso :
    derivedLowerShriek k₀ l f ⋙ (condensedWeilEquiv k₀ l Y).functor ≅
      (condensedWeilEquiv k₀ l X).functor ⋙ condensedDerivedLowerShriek k₀ l f :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((derivedLowerShriekCompToCondensedIso k₀ l f).app K))
    fun φ ↦ ObjectProperty.hom_ext _
      ((derivedLowerShriekCompToCondensedIso k₀ l f).hom.naturality φ)

variable [HasUpperShriek k₀ l f]

variable (k₀) in
/-- The condensed `Rf^!`, transported to adic Weil complexes, is right adjoint to the adic
`Rf₀!`. -/
noncomputable def condensedTransportedAdjunction :
    derivedLowerShriek k₀ l f ⊣
      ((condensedWeilEquiv k₀ l Y).functor ⋙ condensedUpperShriek k₀ l f) ⋙
        (condensedWeilEquiv k₀ l X).inverse :=
  ((condensedWeilEquiv k₀ l X).toAdjunction.comp
    ((condensedDerivedLowerShriekUpperShriekAdjunction k₀ l f).comp
      (condensedWeilEquiv k₀ l Y).symm.toAdjunction)).ofNatIsoLeft
    (condensedDerivedLowerShriekCompIso k₀ l f).isoCompInverse.symm

variable (k₀) in
/-- **The adic `Rf^!` is the condensed one**: `Rf^! ≅ E_Y ⋙ Rf^!_cond ⋙ E_X⁻¹`, by uniqueness of
right adjoints. -/
noncomputable def upperShriekCondensedIso :
    upperShriek (k₀ := k₀) (l := l) f ≅
      ((condensedWeilEquiv k₀ l Y).functor ⋙ condensedUpperShriek k₀ l f) ⋙
        (condensedWeilEquiv k₀ l X).inverse :=
  (derivedLowerShriekUpperShriekAdjunction f).rightAdjointUniq
    (condensedTransportedAdjunction k₀ l f)

variable (k₀) in
/-- The condensed model of `Rf^! L` is `Rf^!_cond` of the condensed model of `L`, as condensed
Weil complexes. -/
noncomputable def condensedWeilEquivUpperShriekObjIso (L : WeilComplex k₀ l Y) :
    (condensedWeilEquiv k₀ l X).functor.obj ((upperShriek f).obj L) ≅
      (condensedUpperShriek k₀ l f).obj ((condensedWeilEquiv k₀ l Y).functor.obj L) :=
  (condensedWeilEquiv k₀ l X).functor.mapIso ((upperShriekCondensedIso k₀ l f).app L) ≪≫
    (condensedWeilEquiv k₀ l X).counitIso.app _

set_option linter.style.longLine false in
variable (k₀) in
/-- **The Frobenius structure of the adic Weil `Rf^!` is the condensed exceptional datum.** For a
Weil complex `L` on `Y`, the condensed model `E (Rf^! L)` of the underlying complex of `Rf^! L` is
the geometric `ī^* ḡ^! L̄` (condensed model), by an isomorphism `θ` which carries the transport
along `E` of the Frobenius structure of `Rf^! L` to the exceptional datum
`WeilComplex.condensedUpperShriekExceptionalDatum`. -/
theorem exists_adicSheafEquivCondensedMod_forget_upperShriek_obj_iso_isWeilEquivariant
    (L : WeilComplex k₀ l Y) :
    ∃ θ : (adicSheafEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory.obj
          (forget.obj ((upperShriek f).obj L)) ≅
        ((condensedGeometricUpperShriek k₀ l f).obj
          (condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l Y).functor.obj L))).obj,
      IsWeilEquivariant (condensedFrobenius k₀ l X).mapDerivedCategory
        (transportWeilDatum
          (adicSheafEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory
          (IsoAlgebra.derivedExactCommIso
            (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).symm
          ((IsoAlgebra.derivedStrIso _).hom.app ((upperShriek f).obj L).obj))
        (condensedUpperShriekExceptionalDatum k₀ l f ((condensedWeilEquiv k₀ l Y).functor.obj L))
        θ.hom := by
  obtain ⟨θc, hθc⟩ := exists_condensedForget_upperShriek_obj_iso_isWeilEquivariant k₀ l f
    ((condensedWeilEquiv k₀ l Y).functor.obj L)
  -- the condensed structure of `E_W M` is the transport of the structure of `M`
  have h₀ := (IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app
    (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X) ((upperShriek f).obj L).obj)
  have h₀' := IsWeilEquivariant.inv _
    ((IsoAlgebra.derivedExactForgetCommIso
      (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).app ((upperShriek f).obj L).obj) h₀
  -- isomorphisms of condensed Weil complexes are equivariant
  have h₁ : IsWeilEquivariant (condensedFrobenius k₀ l X).mapDerivedCategory
      ((IsoAlgebra.derivedStrIso _).hom.app
        ((condensedWeilEquiv k₀ l X).functor.obj ((upperShriek f).obj L)).obj)
      ((IsoAlgebra.derivedStrIso _).hom.app
        ((condensedUpperShriek k₀ l f).obj ((condensedWeilEquiv k₀ l Y).functor.obj L)).obj)
      ((IsoAlgebra.forget _).mapDerivedCategory.map
        (condensedWeilEquivUpperShriekObjIso k₀ l f L).hom.hom) :=
    (IsoAlgebra.derivedStrIso _).hom.naturality
      (condensedWeilEquivUpperShriekObjIso k₀ l f L).hom.hom
  exact ⟨((IsoAlgebra.derivedExactForgetCommIso
      (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).app ((upperShriek f).obj L).obj).symm ≪≫
    (IsoAlgebra.forget _).mapDerivedCategory.mapIso
      ((ObjectProperty.ι _).mapIso (condensedWeilEquivUpperShriekObjIso k₀ l f L)) ≪≫ θc,
    h₀'.comp (h₁.comp hθc)⟩

end WeilComplex

end AlgebraicGeometry
