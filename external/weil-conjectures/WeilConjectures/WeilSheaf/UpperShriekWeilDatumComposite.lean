/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactMate
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.WeilSheaf.ExtensionByZeroAdjunction
public import WeilConjectures.WeilSheaf.UpperShriekWeilDatum
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerShriekFiniteness

/-!
# The exceptional datum is the right Weil datum of `f̄_! ⊣ f̄^!`

For the compactification `X ⟶[i] Z ⟶[g] Y` of `f` and a right adjoint `ḡ^!` of `Rḡ_*` on bounded
constructible adic complexes (`adjR'`), the functor `f̄^! := ī^* ∘ ḡ^!` is right adjoint to
`f̄_! = Rḡ_* ∘ ī_!` (the composite adjunction
`AlgebraicGeometry.WeilComplex.compactifiedAdjunction`),
and the Frobenius exchange of `f̄_!` is the composite of the exchanges of `ī_!` and `Rḡ_*`
(`AlgebraicGeometry.WeilComplex.compactifiedExchange`). The exceptional datum
`AlgebraicGeometry.WeilComplex.upperShriekExceptionalDatum` is the right Weil datum
(`CategoryTheory.Adjunction.rightWeilDatum`) of this adjunction and exchange
(`AlgebraicGeometry.WeilComplex.upperShriekExceptionalDatum_eq_rightWeilDatum`): the unique
Weil datum on `f̄^! L̄` for which the counit `f̄_! f̄^! L̄ ⟶ L̄` is Frobenius equivariant.

Combined with the trace square
(`CategoryTheory.Adjunction.isWeilEquivariant_rightWeilDatum_iff_trace`),
an orientation `o : f̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` is equivariant for the exceptional datum as soon as its
trace `f̄_! ℚ̄_ℓ(d)[2d] ⟶ ℚ̄_ℓ` is Frobenius equivariant.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

open ProEtale

attribute [local instance] Compactification.over

attribute [local instance 1100] CategoryTheory.instOverClass

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

variable (k₀) in
/-- The base change `ī : X̄ ⟶ Z̄` of the open immersion of the compactification. -/
noncomputable abbrev compactificationOpenImmersion :=
  Scheme.Hom.geometricFiberMap (shriekCompactification k₀ f).i
    (comp_over (shriekCompactification k₀ f).i (Spec (CommRingCat.of k₀)))

set_option linter.style.longLine false in
instance : IsOpenImmersion (compactificationOpenImmersion k₀ f) :=
  have : IsOpenImmersion (shriekCompactification k₀ f).i := (shriekCompactification k₀ f).isOpenImmersion
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion)
    (shriekCompactification k₀ f).i _ ‹_›

set_option linter.style.longLine false in
instance : QuasiCompact (compactificationOpenImmersion k₀ f) :=
  have : IsOpenImmersion (shriekCompactification k₀ f).i := (shriekCompactification k₀ f).isOpenImmersion
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian (shriekCompactification k₀ f).Z :=
    LocallyOfFiniteType.isLocallyNoetherian (shriekCompactification k₀ f).g
  have : CompactSpace (shriekCompactification k₀ f).Z :=
    QuasiCompact.compactSpace_of_compactSpace (shriekCompactification k₀ f).g
  have : IsNoetherian (shriekCompactification k₀ f).Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X :=
    (shriekCompactification k₀ f).i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (shriekCompactification k₀ f).i := inferInstance
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @QuasiCompact)
    (shriekCompactification k₀ f).i _ ‹_›

set_option linter.style.longLine false in
variable (k₀) in
/-- The levelwise derived adjunction `D(ī_!) ⊣ D(ī^*)`, restricted to bounded constructible adic
complexes. -/
noncomputable abbrev openImmersionBoundedConstructibleAdjunction :
    (DerivedCategory.boundedConstructibleAdic l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        ((compactificationOpenImmersion k₀ f)_!ᵃ[l]).mapDerivedCategory
        (fun _ hK ↦ boundedConstructibleAdic_mapDerivedCategory_adicOpenImmersionLowerShriek
          (compactificationOpenImmersion k₀ f) hK) ⊣
      (DerivedCategory.boundedConstructibleAdic l
          ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
          ).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (adicUpperStar l (compactificationOpenImmersion k₀ f)).mapDerivedCategory
        (fun _ hK ↦ ProEtale.DerivedCategory.boundedConstructibleAdic.mapDerivedCategory_adicUpperStar
          (compactificationOpenImmersion k₀ f) hK) :=
  ObjectProperty.liftFullSubcategoryAdjunction
    ((adicOpenImmersionLowerShriekAdjunction l
      (compactificationOpenImmersion k₀ f)).mapDerivedCategoryAdjunction) _ _

variable (k₀) in
/-- The Frobenius exchange of `D(ī_!)`, restricted to bounded constructible adic complexes. -/
noncomputable def openImmersionBoundedConstructibleExchange :
    (DerivedCategory.boundedConstructibleAdic l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        ((compactificationOpenImmersion k₀ f)_!ᵃ[l]).mapDerivedCategory
        (fun _ hK ↦ boundedConstructibleAdic_mapDerivedCategory_adicOpenImmersionLowerShriek
          (compactificationOpenImmersion k₀ f) hK) ⋙
      ObjectProperty.liftFullSubcategory _ _
        (WeilSheaf.frobeniusPullback k₀ l (shriekCompactification k₀ f).Z).mapDerivedCategory
        (fun K hK ↦ (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
          (k₀ := k₀) (l := l) (X := (shriekCompactification k₀ f).Z) K).2 hK) ≅
    ObjectProperty.liftFullSubcategory _ _
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory
        (fun K hK ↦ (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
          (k₀ := k₀) (l := l) (X := X) K).2 hK) ⋙
      (DerivedCategory.boundedConstructibleAdic l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        ((compactificationOpenImmersion k₀ f)_!ᵃ[l]).mapDerivedCategory
        (fun _ hK ↦ boundedConstructibleAdic_mapDerivedCategory_adicOpenImmersionLowerShriek
          (compactificationOpenImmersion k₀ f) hK) :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((IsoAlgebra.derivedExactCommIso
        (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l
          (shriekCompactification k₀ f).i
          (comp_over (shriekCompactification k₀ f).i (Spec (CommRingCat.of k₀))))).app K.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((IsoAlgebra.derivedExactCommIso
        (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l
          (shriekCompactification k₀ f).i
          (comp_over (shriekCompactification k₀ f).i (Spec (CommRingCat.of k₀))))).hom.naturality
            φ.hom))

variable {f} [HasUpperShriek k₀ l f]

set_option linter.style.whitespace false in
/-- The adjunction `f̄_! ⊣ f̄^!` for `f̄_! = Rḡ_* ∘ ī_!` and `f̄^! = ī^* ∘ ḡ^!`. -/
noncomputable abbrev compactifiedAdjunction
    (hR : PreservesBoundedConstructibleAdicLowerStar k₀ l f)
    {R' : (DerivedCategory.boundedConstructibleAdic l
        (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left
          ).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).FullSubcategory}
    (adjR' : (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)
        (adicLowerStar l
          (geometricFiberHomCompactification (k₀ := k₀) f).overG.left).rightDerivedFunctor
        hR ⊣ R') :=
  (openImmersionBoundedConstructibleAdjunction k₀ f).comp adjR'

/-- The Frobenius exchange of `f̄_! = Rḡ_* ∘ ī_!`: the composite of the exchanges of `ī_!` and of
`Rḡ_*`. -/
noncomputable def compactifiedExchange (hR : PreservesBoundedConstructibleAdicLowerStar k₀ l f) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (IsoAlgebra.liftedDerivedCommIso
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l (shriekCompactification k₀ f).g
        (comp_over (shriekCompactification k₀ f).g _)) _ _
      (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
        (k₀ := k₀) (l := l) (X := (shriekCompactification k₀ f).Z))
      (fun K hK ↦
        (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
          (k₀ := k₀) (l := l) (X := Y) K).2 hK) hR) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openImmersionBoundedConstructibleExchange k₀ f) _ ≪≫
    Functor.associator _ _ _

set_option linter.unusedSectionVars false in
lemma compactifiedExchange_hom_app (hR : PreservesBoundedConstructibleAdicLowerStar k₀ l f)
    (K) :
    (compactifiedExchange (f := f) hR).hom.app K =
      (IsoAlgebra.liftedDerivedCommIso
        (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l (shriekCompactification k₀ f).g
          (comp_over (shriekCompactification k₀ f).g _)) _ _
        (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
          (k₀ := k₀) (l := l) (X := (shriekCompactification k₀ f).Z))
        (fun K hK ↦
          (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
            (k₀ := k₀) (l := l) (X := Y) K).2 hK) hR).hom.app
        ((ObjectProperty.liftFullSubcategory _ _
          ((compactificationOpenImmersion k₀ f)_!ᵃ[l]).mapDerivedCategory
          (fun _ hK ↦ boundedConstructibleAdic_mapDerivedCategory_adicOpenImmersionLowerShriek
            (compactificationOpenImmersion k₀ f) hK)).obj K) ≫
      (ObjectProperty.liftFullSubcategory _ _
        (adicLowerStar l
          (geometricFiberHomCompactification (k₀ := k₀) f).overG.left).rightDerivedFunctor hR).map
        ((openImmersionBoundedConstructibleExchange k₀ f).hom.app K) := by
  simp [compactifiedExchange]
  rfl

set_option linter.style.whitespace false in
/-- **The exceptional datum is the right Weil datum of `f̄_! ⊣ f̄^!`**: the unique Weil datum on
`f̄^! L̄ = ī^* ḡ^! L̄` for which the counit `f̄_! f̄^! L̄ ⟶ L̄` is Frobenius equivariant, for the
composite exchange of `f̄_! = Rḡ_* ∘ ī_!`. -/
theorem upperShriekExceptionalDatum_eq_rightWeilDatum
    (hR : PreservesBoundedConstructibleAdicLowerStar k₀ l f)
    {R' : (DerivedCategory.boundedConstructibleAdic l
        (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left
          ).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).FullSubcategory}
    (adjR' : (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)
        (adicLowerStar l
          (geometricFiberHomCompactification (k₀ := k₀) f).overG.left).rightDerivedFunctor
        hR ⊣ R')
    (L : WeilComplex k₀ l Y) :
    upperShriekExceptionalDatum hR adjR' L =
      (Adjunction.rightWeilDatum (compactifiedAdjunction hR adjR') (compactifiedExchange hR)
        (ObjectProperty.homMk
          (X := (ObjectProperty.liftFullSubcategory _ _
            (WeilSheaf.frobeniusPullback k₀ l Y).mapDerivedCategory
            (fun K hK ↦
              (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
                (k₀ := k₀) (l := l) (X := Y) K).2 hK)).obj
              ⟨forget.obj L, (WeilComplex.objectProperty_iff _).1 L.property⟩)
          (Y := ⟨forget.obj L, (WeilComplex.objectProperty_iff _).1 L.property⟩)
          ((IsoAlgebra.derivedStrIso _).hom.app L.obj))).hom := by
  rw [Adjunction.rightWeilDatum_comp _ _ _ _ (compactifiedExchange_hom_app hR)]
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.liftFullSubcategory_map,
    ObjectProperty.homMk_hom]
  rw [Adjunction.rightAdjointExchange_liftFullSubcategory_app_hom
    (adicOpenImmersionLowerShriekAdjunction l
      (compactificationOpenImmersion k₀ f)).mapDerivedCategoryAdjunction _ _
    (IsoAlgebra.derivedExactCommIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l
        (shriekCompactification k₀ f).i
        (comp_over (shriekCompactification k₀ f).i (Spec (CommRingCat.of k₀))))) _ _
    (eP := openImmersionBoundedConstructibleExchange k₀ f) (fun _ ↦ rfl),
    ← IsoAlgebra.derivedExactCommIso_hom_eq_rightAdjointExchange _ _ _
      (ProEtale.mateEquiv_adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv l
        (shriekCompactification k₀ f).i (comp_over (shriekCompactification k₀ f).i _))]
  rfl

end WeilComplex

end AlgebraicGeometry
