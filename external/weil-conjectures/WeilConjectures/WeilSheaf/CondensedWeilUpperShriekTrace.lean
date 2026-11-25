/-
Copyright (c) 2026 The Weil conjectures formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (u9 C1)
-/
module

public import WeilConjectures.WeilSheaf.CondensedWeilUpperShriekLink
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactMate
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!
# The trace square in the condensed model

The exceptional datum `WeilComplex.condensedUpperShriekExceptionalDatum` is the right Weil datum
of the composite adjunction `f̄_! = Rḡ_* ∘ D(ī_!) ⊣ ī^* ∘ ḡ^! = f̄^!` on bounded constructible
condensed complexes (`WeilComplex.condensedCompactifiedAdjunction`), for the composite Frobenius
exchange `WeilComplex.condensedCompactifiedExchange`. Hence an orientation
`o : f̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` (condensed model of the Tate twist) whose trace `f̄_! ℚ̄_ℓ(d)[2d] ⟶
ℚ̄_ℓ`
is Frobenius equivariant gives the Weil orientation of the smooth purity leaf
`WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`
(`WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_condensed_trace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- A faithful functor commuting with the Weil functors reflects equivariance, for the
transported data. -/
lemma isWeilEquivariant_of_map_transportWeilDatum {C D : Type*} [Category* C] [Category* D]
    {G : C ⥤ C} {G' : D ⥤ D} (T : C ⥤ D) [T.Faithful] (c : G ⋙ T ≅ T ⋙ G') {M N : C}
    {φM : G.obj M ⟶ M} {φN : G.obj N ⟶ N} {u : M ⟶ N}
    (h : IsWeilEquivariant G' (transportWeilDatum T c φM) (transportWeilDatum T c φN) (T.map u)) :
    IsWeilEquivariant G φM φN u := by
  unfold IsWeilEquivariant at h ⊢
  unfold transportWeilDatum at h
  have hn := c.inv.naturality u
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn] at h
  simp only [Category.assoc] at h
  rw [← Functor.map_comp, ← Functor.map_comp] at h
  exact T.map_injective ((cancel_epi _).1 h)

/-- The left Weil datum is the transport along `L` through `e⁻¹` (definitionally). -/
lemma Adjunction.leftWeilDatum_eq_transportWeilDatum {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {G : C ⥤ C} {H : D ⥤ D} (e : L ⋙ H ≅ G ⋙ L) {c : C} (φ : G.obj c ⟶ c) :
    Adjunction.leftWeilDatum e φ = transportWeilDatum L e.symm φ :=
  rfl

/-- **Composing an orientation with an equivariant isomorphism** preserves the equivariance of
its trace: if the trace of `o : R Y ≅ T` is equivariant for `τ` and `c : T ≅ T'` is equivariant for
`τ` and `τ'`, then the trace of `o ≪≫ c` is equivariant for `τ'`. -/
lemma Adjunction.isWeilEquivariant_orientationTrace_trans {C D : Type*} [Category* C]
    [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {G : C ⥤ C} {H : D ⥤ D}
    (e : L ⋙ H ≅ G ⋙ L) {Y : D} {T T' : C} (o : R.obj Y ≅ T) (c : T ≅ T') {τ : G.obj T ⟶ T}
    {τ' : G.obj T' ⟶ T'} (hc : IsWeilEquivariant G τ τ' c.hom) {ψ : H.obj Y ⟶ Y}
    (h : IsWeilEquivariant H (Adjunction.leftWeilDatum e τ) ψ (adj.orientationTrace o)) :
    IsWeilEquivariant H (Adjunction.leftWeilDatum e τ') ψ (adj.orientationTrace (o ≪≫ c)) := by
  have hc' := (IsWeilEquivariant.inv _ c hc).map L e.symm
  rw [Adjunction.leftWeilDatum_eq_transportWeilDatum] at h ⊢
  unfold Adjunction.orientationTrace at h ⊢
  rw [Iso.trans_inv, Functor.map_comp, Category.assoc]
  exact hc'.comp h

end CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

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

set_option linter.style.longLine false in
instance : CompactSpace ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  QuasiCompact.compactSpace_of_compactSpace
    ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure

set_option linter.style.longLine false in
instance : IsNoetherian ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  ⟨⟩

set_option linter.style.longLine false in
variable (k₀) in
/-- The lift of the condensed Frobenius `(Fr_S⁻¹)_*` to bounded constructible condensed
complexes. -/
noncomputable abbrev condensedFrobeniusLift (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (S ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))] :=
  ObjectProperty.liftFullSubcategory (condensedBoundedConstructible k₀ l S)
    (condensedBoundedConstructible k₀ l S) (condensedFrobenius k₀ l S).mapDerivedCategory
    (fun K hK ↦ (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l S K).2 hK)

variable (k₀) in
/-- The levelwise derived adjunction `D(ī_!) ⊣ D(ī^*)` on bounded constructible condensed
complexes. -/
noncomputable abbrev condensedOpenImmersionGeometricAdjunction :=
  ObjectProperty.liftFullSubcategoryAdjunction
    ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj l)
      (condensedOpenImmersionMap k₀ f)).mapDerivedCategoryAdjunction)
    (P := condensedBoundedConstructible k₀ l X)
    (Q := condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z)
    (fun K hK ↦ CondensedRing.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _
      (condensedOpenImmersionMap k₀ f) K hK)
    (fun K hK ↦ CondensedRing.boundedConstructible_mapDerivedCategory_upperStar_obj _
      (condensedOpenImmersionMap k₀ f) K hK)

variable (k₀) in
/-- The Frobenius exchange of `D(ī_!)`, restricted to bounded constructible condensed
complexes. -/
noncomputable def condensedOpenImmersionGeometricExchange :
    ObjectProperty.liftFullSubcategory (condensedBoundedConstructible k₀ l X)
        (condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z)
        (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l)
          (condensedOpenImmersionMap k₀ f)).mapDerivedCategory
        (fun K hK ↦
          CondensedRing.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _
            (condensedOpenImmersionMap k₀ f) K hK) ⋙
      condensedFrobeniusLift k₀ l (shriekCompactification k₀ f).Z ≅
    condensedFrobeniusLift k₀ l X ⋙
      ObjectProperty.liftFullSubcategory (condensedBoundedConstructible k₀ l X)
        (condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z)
        (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l)
          (condensedOpenImmersionMap k₀ f)).mapDerivedCategory
        (fun K hK ↦
          CondensedRing.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _
            (condensedOpenImmersionMap k₀ f) K hK) :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((IsoAlgebra.derivedExactCommIso (condensedOpenImmersionShriekExchange k₀ l f)).app K.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((IsoAlgebra.derivedExactCommIso (condensedOpenImmersionShriekExchange k₀ l f)).hom.naturality
        φ.hom))

set_option linter.style.longLine false in
variable (k₀) in
/-- The adjunction `f̄_! ⊣ f̄^!` for `f̄_! = Rḡ_* ∘ D(ī_!)` and `f̄^! = ī^* ∘ ḡ^!`, condensed model. -/
noncomputable abbrev condensedCompactifiedAdjunction :=
  (condensedOpenImmersionGeometricAdjunction k₀ l f).comp (condensedProperAdjunction k₀ l f)

variable (k₀) in
/-- The Frobenius exchange of `f̄_! = Rḡ_* ∘ D(ī_!)`: the composite of the exchanges of `D(ī_!)`
and of `Rḡ_*`. -/
noncomputable def condensedCompactifiedExchange :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (IsoAlgebra.liftedDerivedCommIso (condensedProperExchange k₀ l f) _ _
      (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l
        (shriekCompactification k₀ f).Z)
      (fun K hK ↦ (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)
      (condensedProperPreserves k₀ l f)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (condensedOpenImmersionGeometricExchange k₀ l f) _ ≪≫
    Functor.associator _ _ _

set_option linter.style.longLine false in
lemma condensedCompactifiedExchange_hom_app (K) :
    (condensedCompactifiedExchange k₀ l f).hom.app K =
      (IsoAlgebra.liftedDerivedCommIso (condensedProperExchange k₀ l f) _ _
        (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l
          (shriekCompactification k₀ f).Z)
        (fun K hK ↦ (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)
        (condensedProperPreserves k₀ l f)).hom.app
        ((ObjectProperty.liftFullSubcategory _ _
          (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l)
            (condensedOpenImmersionMap k₀ f)).mapDerivedCategory
          (fun K hK ↦
            CondensedRing.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _
              (condensedOpenImmersionMap k₀ f) K hK)).obj K) ≫
      (ObjectProperty.liftFullSubcategory _ _
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (compactificationProperMap k₀ f)).rightDerivedFunctor
        (condensedProperPreserves k₀ l f)).map
        ((condensedOpenImmersionGeometricExchange k₀ l f).hom.app K) := by
  simp [condensedCompactifiedExchange]

set_option linter.unusedSectionVars false in
/-- The exchange of `D(ī_!)` is the left mate of the exchange of `ī^*` (at the level of
isomorphisms; stated to be rewritten before any component is unfolded). -/
lemma condensedOpenImmersionShriekExchange_eq :
    condensedOpenImmersionShriekExchange k₀ l f =
      IsoAlgebra.leftMateIso
        (CondensedRing.openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj l)
          (condensedOpenImmersionMap k₀ f)) (condensedOpenImmersionExchange k₀ l f) :=
  rfl

variable (k₀) in
/-- **The exceptional datum is the right Weil datum of `f̄_! ⊣ f̄^!`** (condensed model). -/
theorem condensedUpperShriekExceptionalDatum_eq_rightWeilDatum
    (L' : (condensedWeilObjectProperty k₀ l Y).FullSubcategory) :
    condensedUpperShriekExceptionalDatum k₀ l f L' =
      (Adjunction.rightWeilDatum (condensedCompactifiedAdjunction k₀ l f)
        (condensedCompactifiedExchange k₀ l f)
        (ObjectProperty.homMk
          (X := (condensedFrobeniusLift k₀ l Y).obj (condensedForgetObj k₀ l L'))
          (Y := condensedForgetObj k₀ l L')
          ((IsoAlgebra.derivedStrIso _).hom.app L'.obj))).hom := by
  rw [Adjunction.rightWeilDatum_comp _ _ _ _ (condensedCompactifiedExchange_hom_app l f)]
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.liftFullSubcategory_map,
    ObjectProperty.homMk_hom]
  rw [Adjunction.rightAdjointExchange_liftFullSubcategory_app_hom
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj l)
      (condensedOpenImmersionMap k₀ f)).mapDerivedCategoryAdjunction _ _
    (IsoAlgebra.derivedExactCommIso (condensedOpenImmersionShriekExchange k₀ l f)) _ _
    (eP := condensedOpenImmersionGeometricExchange k₀ l f) (fun _ ↦ rfl)]
  -- the exchanges of `ī_!` and `ī^*` are mates (iso-level rewrite first: the abbreviation must
  -- not be unfolded by `isDefEq`)
  have h : Adjunction.rightAdjointExchange
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj l)
        (condensedOpenImmersionMap k₀ f))
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj l)
        (condensedOpenImmersionMap k₀ f))
      (condensedOpenImmersionShriekExchange k₀ l f) =
        (condensedOpenImmersionExchange k₀ l f).hom := by
    rw [condensedOpenImmersionShriekExchange_eq]
    exact IsoAlgebra.mateEquiv_leftMateIso_inv _ _
  have hmate := IsoAlgebra.derivedExactCommIso_hom_eq_rightAdjointExchange
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj l)
      (condensedOpenImmersionMap k₀ f))
    (condensedOpenImmersionShriekExchange k₀ l f) (condensedOpenImmersionExchange k₀ l f) h
  exact congrArg (fun α ↦ α.app ((condensedProperRightAdjoint k₀ l f).obj
    (condensedForgetObj k₀ l L')).obj ≫ _) hmate

variable (k₀) in
/-- The condensed model `E (forget L)` of the underlying complex of an adic Weil complex, as a
bounded constructible condensed complex. -/
noncomputable abbrev condensedForgetAdic (L : WeilComplex k₀ l X) :
    (condensedBoundedConstructible k₀ l X).FullSubcategory :=
  ⟨(adicSheafEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory.obj (forget.obj L),
    (boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) _).1
      ((objectProperty_iff _).1 L.property)⟩

variable (k₀) in
/-- The condensed model of the underlying complex of `L`, computed as the underlying complex of the
condensed Weil complex `E_W L`, is `E (forget L)`. -/
noncomputable def condensedForgetObjIso (L : WeilComplex k₀ l X) :
    condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l X).functor.obj L) ≅
      condensedForgetAdic k₀ l L :=
  ObjectProperty.isoMk _ ((IsoAlgebra.derivedExactForgetCommIso
    (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).app L.obj)

variable (k₀) in
/-- The condensed Frobenius structure of `E_W L` corresponds, under `condensedForgetObjIso`, to the
transport along `E` of the structure of `L`. -/
lemma isWeilEquivariant_condensedForgetObjIso_hom (L : WeilComplex k₀ l X) :
    IsWeilEquivariant (condensedFrobeniusLift k₀ l X)
      (ObjectProperty.homMk
        (X := (condensedFrobeniusLift k₀ l X).obj
          (condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l X).functor.obj L)))
        (Y := condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l X).functor.obj L))
        ((IsoAlgebra.derivedStrIso _).hom.app ((condensedWeilEquiv k₀ l X).functor.obj L).obj))
      (ObjectProperty.homMk
        (X := (condensedFrobeniusLift k₀ l X).obj (condensedForgetAdic k₀ l L))
        (Y := condensedForgetAdic k₀ l L)
        (transportWeilDatum
          (adicSheafEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory
          (IsoAlgebra.derivedExactCommIso
            (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).symm
          ((IsoAlgebra.derivedStrIso _).hom.app L.obj)))
      (condensedForgetObjIso k₀ l L).hom := by
  unfold IsWeilEquivariant
  apply ObjectProperty.hom_ext
  exact IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app
    (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X) L.obj

variable {f} [HasUpperShriek k₀ l f]

set_option linter.style.longLine false in
/-- **The Weil orientation from the trace square, condensed model** (the uniqueness route,
blueprint `proposition-purity-trace-commute-frobenius`): let
`o : f̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` be an orientation on `X̄` in the condensed model
(`f̄^! = ī^* ∘ ḡ^!` for the compactification, `ℚ̄_ℓ(d)[2d]` the condensed model of the Tate twist),
whose trace `f̄_! ℚ̄_ℓ(d)[2d] ⟶ ℚ̄_ℓ` is Frobenius equivariant for the composite exchange of `f̄_!`
and the (transported) structures of `ℚ̄_ℓ(d)[2d]` and `ℚ̄_ℓ`. Then the underlying complex of
`Rf^! ℚ̄_ℓ` is isomorphic to that of `ℚ̄_ℓ(d)[2d]` compatibly with the Frobenius structures: the
statement of `exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_condensed_trace (d : ℕ)
    (o : (condensedGeometricUpperShriek k₀ l f).obj
        (condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l Y).functor.obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))) ≅
      condensedForgetAdic k₀ l (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧))
    (htrace : IsWeilEquivariant (condensedFrobeniusLift k₀ l Y)
      (Adjunction.leftWeilDatum (condensedCompactifiedExchange k₀ l f)
        (ObjectProperty.homMk
          (X := (condensedFrobeniusLift k₀ l X).obj (condensedForgetAdic k₀ l (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧)))
          (Y := condensedForgetAdic k₀ l (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧))
          (transportWeilDatum
            (adicSheafEquivCondensedMod l
              (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory
            (IsoAlgebra.derivedExactCommIso
              (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).symm
            ((IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj))))
      (ObjectProperty.homMk
        (X := (condensedFrobeniusLift k₀ l Y).obj (condensedForgetObj k₀ l
          ((condensedWeilEquiv k₀ l Y).functor.obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))))
        (Y := condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l Y).functor.obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))))
        ((IsoAlgebra.derivedStrIso _).hom.app ((condensedWeilEquiv k₀ l Y).functor.obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj))
      ((condensedCompactifiedAdjunction k₀ l f).orientationTrace o)) :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  -- the trace square gives the equivariance of `o` for the exceptional datum
  have h := ((condensedCompactifiedAdjunction k₀ l f).isWeilEquivariant_rightWeilDatum_iff_trace
    (condensedCompactifiedExchange k₀ l f) o _ _).2 htrace
  have ho : IsWeilEquivariant (condensedFrobenius k₀ l X).mapDerivedCategory
      (condensedUpperShriekExceptionalDatum k₀ l f ((condensedWeilEquiv k₀ l Y).functor.obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))))
      (transportWeilDatum
        (adicSheafEquivCondensedMod l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory
        (IsoAlgebra.derivedExactCommIso
          (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).symm
        ((IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj))
      o.hom.hom := by
    rw [condensedUpperShriekExceptionalDatum_eq_rightWeilDatum]
    unfold IsWeilEquivariant at h ⊢
    exact congrArg InducedCategory.Hom.hom h
  -- the structure of `Rf^! ℚ̄_ℓ` is the exceptional datum
  obtain ⟨θ, hθ⟩ := exists_adicSheafEquivCondensedMod_forget_upperShriek_obj_iso_isWeilEquivariant
    k₀ l f (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))
  -- reflect along the equivalence of the two models
  let E := adicSheafDerivedEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let g := E.functor.preimageIso (θ ≪≫ (ObjectProperty.ι _).mapIso o)
  have hg : E.functor.map g.hom = (θ ≪≫ (ObjectProperty.ι _).mapIso o).hom :=
    E.functor.map_preimage _
  refine ⟨g, (isWeilEquivariant_of_map_transportWeilDatum E.functor
    (IsoAlgebra.derivedExactCommIso
      (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)).symm ?_).symm⟩
  rw [hg]
  exact hθ.comp ho

variable (k₀ X) in
/-- The Weil complex `ℚ̄_ℓ(d)[2d]` on `X`. -/
noncomputable abbrev tateShift (d : ℕ) : WeilComplex k₀ l X :=
  ((tateTwist k₀ l X d).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧

/-- **The Weil orientation from the trace square, condensed model, with the condensed Weil
structure of the Tate twist**: as
`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_condensed_trace`,
with the orientation landing in the condensed model `E_W ℚ̄_ℓ(d)[2d]` of the Tate twist as a
condensed Weil complex, whose Frobenius structure is the derived structure isomorphism of the
condensed Weil complex. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_condensed_trace' (d : ℕ)
    (o : (condensedGeometricUpperShriek k₀ l f).obj
        (condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l Y).functor.obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))) ≅
      condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l X).functor.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧)))
    (htrace : IsWeilEquivariant (condensedFrobeniusLift k₀ l Y)
      (Adjunction.leftWeilDatum (condensedCompactifiedExchange k₀ l f)
        (ObjectProperty.homMk
          (X := (condensedFrobeniusLift k₀ l X).obj (condensedForgetObj k₀ l
            ((condensedWeilEquiv k₀ l X).functor.obj (((tateTwist k₀ l X d).obj
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧))))
          (Y := condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l X).functor.obj
            (((tateTwist k₀ l X d).obj
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧)))
          ((IsoAlgebra.derivedStrIso _).hom.app ((condensedWeilEquiv k₀ l X).functor.obj
            (((tateTwist k₀ l X d).obj
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧)).obj)))
      (ObjectProperty.homMk
        (X := (condensedFrobeniusLift k₀ l Y).obj (condensedForgetObj k₀ l
          ((condensedWeilEquiv k₀ l Y).functor.obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))))
        (Y := condensedForgetObj k₀ l ((condensedWeilEquiv k₀ l Y).functor.obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))))
        ((IsoAlgebra.derivedStrIso _).hom.app ((condensedWeilEquiv k₀ l Y).functor.obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj))
      ((condensedCompactifiedAdjunction k₀ l f).orientationTrace o)) :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  exact exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_condensed_trace l d
    (o ≪≫ condensedForgetObjIso k₀ l (tateShift k₀ l X d))
    (Adjunction.isWeilEquivariant_orientationTrace_trans _ _ o
      (condensedForgetObjIso k₀ l (tateShift k₀ l X d))
      (isWeilEquivariant_condensedForgetObjIso_hom k₀ l (tateShift k₀ l X d)) htrace)


end WeilComplex

end AlgebraicGeometry
