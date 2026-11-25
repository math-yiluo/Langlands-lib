/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.Adjunction.MateUnitIsIso
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.AlgebraicGeometry.NativeBaseChange.NativeBaseChangeForgetComparison
import WeilConjectures.AlgebraicGeometry.NativeBaseChange.GeometricSmoothBaseChange
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedForgetComparison

/-!
# Smooth base change for Weil complexes

For a commutative square of `k₀`-schemes
```
Y' --g'--> Y
|π'        |π
v          v
X' --g-->  X
```
the *base change morphism* `π^* Rg_* ⟶ Rg'_* π'^*` of Weil complexes
(`AlgebraicGeometry.WeilComplex.baseChange`) is the mate of the exchange isomorphism
`g'^* π^* ≅ (g' ≫ π)^* = (π' ≫ g)^* ≅ π'^* g^*` under the adjunctions `g^* ⊣ Rg_*` and
`g'^* ⊣ Rg'_*`.

The smooth base change theorem (blueprint `theorem-smooth-base-change-classical-torsion--1`, in its
Weil form) says that it is an isomorphism when the square is cartesian, `π` is smooth and `g` is
separated (`AlgebraicGeometry.WeilComplex.isIso_baseChange_of_smooth`). The base change morphism
lies over the native derived base-change mate of pro-étale Weil sheaves
(`AlgebraicGeometry.WeilComplex.ι_map_baseChange_app`); forgetting the Weil structure, this is
the geometric native smooth base change theorem
(`AlgebraicGeometry.NativeBaseChange.geometric_smooth_baseChange_isIso`).

The mate description gives the input to homotopy invariance: if the base change morphism is
invertible at `M` and the unit of `π'^* ⊣ Rπ'_*` is invertible at `M`, then the unit of
`π^* ⊣ Rπ_*` is invertible at `Rg_* M`
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj_of_isIso_baseChange_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X X' Y Y' : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [Y'.Over (Spec (CommRingCat.of k₀))] {g' : Y' ⟶ Y} {π' : Y' ⟶ X'} {π : Y ⟶ X}
  {g : X' ⟶ X} [g'.IsOver (Spec (CommRingCat.of k₀))] [π'.IsOver (Spec (CommRingCat.of k₀))]
  [π.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The congruence isomorphism of pullbacks of Weil complexes lies over the derived congruence
isomorphism of pullbacks of pro-étale Weil sheaves. -/
theorem ι_map_upperStarCongrIso_hom_app {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] {φ φ' : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))]
    [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') (K : WeilComplex k₀ l Y) :
    (objectProperty k₀ l X).ι.map ((upperStarCongrIso (k₀ := k₀) (l := l) h).hom.app K) =
      (Functor.mapDerivedCategoryNatIso
        (ProEtaleWeilSheaf.upperStarCongrIso k₀ l h)).hom.app K.obj := by
  subst h
  simp only [ProEtaleWeilSheaf.upperStarCongrIso, Functor.mapDerivedCategoryNatIso_refl]
  rfl

/-- The composition isomorphism of pullbacks of Weil complexes lies over the derived composition
isomorphism of pullbacks of pro-étale Weil sheaves. -/
theorem ι_map_upperStarCompIso_hom_app {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l Z) :
    (objectProperty k₀ l X).ι.map ((upperStarCompIso (k₀ := k₀) (l := l) f g).hom.app K) =
      (Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarCompIso k₀ l f g)).hom.app
          K.obj ≫
        (Functor.mapDerivedCategoryCompIso _ _).inv.app K.obj :=
  rfl

/-- The inverse of the composition isomorphism of pullbacks of Weil complexes lies over the
inverse of the derived composition isomorphism of pullbacks of pro-étale Weil sheaves. -/
theorem ι_map_upperStarCompIso_inv_app {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l Z) :
    (objectProperty k₀ l X).ι.map ((upperStarCompIso (k₀ := k₀) (l := l) f g).inv.app K) =
      (Functor.mapDerivedCategoryCompIso _ _).hom.app K.obj ≫
        (Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarCompIso k₀ l f g)).inv.app
          K.obj :=
  rfl

variable (k₀ l) in
/-- The exchange isomorphism `g'^* π^* ≅ π'^* g^*` of pullbacks of Weil complexes along a
commutative square `g' ≫ π = π' ≫ g`. -/
noncomputable def upperStarCompUpperStarIso (h : g' ≫ π = π' ≫ g) :
    upperStar π ⋙ upperStar g' ≅ upperStar (k₀ := k₀) (l := l) g ⋙ upperStar π' :=
  (upperStarCompIso g' π).symm ≪≫ upperStarCongrIso h ≪≫ upperStarCompIso π' g

/-- The exchange isomorphism `g'^* π^* ≅ π'^* g^*` of Weil complexes lies over the native
derived exchange isomorphism `AlgebraicGeometry.NativeBaseChange.pullSquare`. -/
theorem ι_map_upperStarCompUpperStarIso_hom_app (h : g' ≫ π = π' ≫ g) (K : WeilComplex k₀ l X) :
    (objectProperty k₀ l Y').ι.map ((upperStarCompUpperStarIso k₀ l h).hom.app K) =
      (NativeBaseChange.pullSquare k₀ l (CommSq.mk h.symm)).hom.app K.obj := by
  simp only [upperStarCompUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, ι_map_upperStarCongrIso_hom_app]
  change ((Functor.mapDerivedCategoryCompIso _ _).hom.app K.obj ≫
      (Functor.mapDerivedCategoryNatIso
        (ProEtaleWeilSheaf.upperStarCompIso k₀ l g' π)).inv.app K.obj) ≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtaleWeilSheaf.upperStarCongrIso k₀ l h)).hom.app K.obj ≫
    ((Functor.mapDerivedCategoryNatIso
        (ProEtaleWeilSheaf.upperStarCompIso k₀ l π' g)).hom.app K.obj ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv.app K.obj) = _
  simp [NativeBaseChange.pullSquare, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm]

variable [QuasiCompact g] [QuasiSeparated g] [LocallyOfFiniteType g]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact g'] [QuasiSeparated g']
  [LocallyOfFiniteType g'] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The base change morphism `π^* Rg_* ⟶ Rg'_* π'^*` of Weil complexes along a commutative square
```
Y' --g'--> Y
|π'        |π
v          v
X' --g-->  X
```
the mate of the exchange isomorphism `g'^* π^* ≅ π'^* g^*`
(`AlgebraicGeometry.WeilComplex.upperStarCompUpperStarIso`). -/
noncomputable def baseChange (h : g' ≫ π = π' ≫ g) :
    derivedLowerStar g ⋙ upperStar π ⟶ upperStar π' ⋙ derivedLowerStar (k₀ := k₀) (l := l) g' :=
  mateEquiv (upperStarDerivedLowerStarAdjunction g) (upperStarDerivedLowerStarAdjunction g')
    (upperStarCompUpperStarIso k₀ l h).hom

/-- The derived pushforward of a morphism of Weil complexes is the derived pushforward of the
underlying morphism. -/
theorem ι_map_derivedLowerStar_map {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] {K L : WeilComplex k₀ l X} (f : K ⟶ L) :
    (objectProperty k₀ l Y).ι.map ((derivedLowerStar φ).map f) =
      (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.map
        ((objectProperty k₀ l X).ι.map f) :=
  rfl

/-- The pullback of a morphism of Weil complexes is the derived pullback of the underlying
morphism. -/
theorem ι_map_upperStar_map {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    {K L : WeilComplex k₀ l Y} (f : K ⟶ L) :
    (objectProperty k₀ l X).ι.map ((upperStar φ).map f) =
      (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory.map
        ((objectProperty k₀ l Y).ι.map f) :=
  rfl

/-- The unit of `φ^* ⊣ Rφ_*` on Weil complexes lies over the unit of the derived adjunction of
pro-étale Weil sheaves. -/
theorem ι_map_upperStarDerivedLowerStarAdjunction_unit_app {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l Y) :
    (objectProperty k₀ l Y).ι.map ((upperStarDerivedLowerStarAdjunction φ).unit.app K) =
      (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l φ).unit.app K.obj := by
  rw [upperStarDerivedLowerStarAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  rfl

/-- The counit of `φ^* ⊣ Rφ_*` on Weil complexes lies over the counit of the derived adjunction
of pro-étale Weil sheaves. -/
theorem ι_map_upperStarDerivedLowerStarAdjunction_counit_app {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    (objectProperty k₀ l X).ι.map ((upperStarDerivedLowerStarAdjunction φ).counit.app K) =
      (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l φ).counit.app K.obj := by
  rw [upperStarDerivedLowerStarAdjunction, Adjunction.map_restrictFullyFaithful_counit_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The base change morphism of Weil complexes lies over the native derived base-change mate
`AlgebraicGeometry.NativeBaseChange.mate` of the underlying complexes. -/
theorem ι_map_baseChange_app (h : g' ≫ π = π' ≫ g) (M : WeilComplex k₀ l X') :
    (objectProperty k₀ l Y).ι.map ((baseChange k₀ l h).app M) =
      (NativeBaseChange.mate k₀ l (CommSq.mk h.symm)).app M.obj := by
  simp only [baseChange, NativeBaseChange.mate, mateEquiv_apply, Functor.comp_obj, Functor.id_obj,
    NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id, Functor.comp_map,
    Functor.map_comp, ι_map_derivedLowerStar_map, ι_map_upperStar_map,
    ι_map_upperStarDerivedLowerStarAdjunction_unit_app,
    ι_map_upperStarDerivedLowerStarAdjunction_counit_app,
    ι_map_upperStarCompUpperStarIso_hom_app]
  rfl

/-- Blueprint `theorem-smooth-base-change-classical-torsion--1` (Weil form): **smooth base change
for Weil complexes**. For a cartesian square of `k₀`-schemes `g' ≫ π = π' ≫ g` with `π` smooth and
`g` separated, quasi-compact and of finite type, the base change morphism `π^* Rg_* ⟶ Rg'_* π'^*` of
Weil complexes is an isomorphism.

Its component at a Weil complex `M` lies over the native derived base-change mate of the
underlying complex (`AlgebraicGeometry.WeilComplex.ι_map_baseChange_app`). Forgetting the Weil
structure is conservative and carries this mate to the base-change morphism of the square base
changed to the algebraic closure of `k₀` (`AlgebraicGeometry.NativeBaseChange.forget_mate`),
which is invertible on bounded complexes with constructible cohomology by geometric smooth base
change (`AlgebraicGeometry.NativeBaseChange.geometric_smooth_baseChange_isIso`). -/
theorem isIso_baseChange_of_smooth [IsSeparated g] (h : IsPullback g' π' π g) [Smooth π] :
    IsIso (baseChange k₀ l h.w) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hF⟩ :=
    Endofunctor.IsoAlgebra.fixedPair_forget_properties (WeilSheaf.frobeniusPullback k₀ l Y)
  let : (NativeBaseChange.forget k₀ l Y).ReflectsIsomorphisms := hF
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [← isIso_iff_of_reflects_iso _ (objectProperty k₀ l Y).ι, ι_map_baseChange_app,
    ← isIso_iff_of_reflects_iso _ (NativeBaseChange.forget k₀ l Y), NativeBaseChange.forget_mate]
  have hc (n : ℤ) : ProEtale.IsAdicConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((NativeBaseChange.forget k₀ l X').obj M.obj)) :=
    (ProEtale.adicConstructibleSheaf l _).prop_of_iso
      (((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X')).mapDerivedCategoryHomologyFunctorIso n).app
          M.obj) (M.property.2 n)
  have := NativeBaseChange.geometric_smooth_baseChange_isIso k₀ l h.flip
    ((NativeBaseChange.forget k₀ l X').obj M.obj)
    (Functor.bounded_mapDerivedCategory_obj _ M.property.1) hc
  infer_instance

/-- If the base change morphism `π^* Rg_* M ⟶ Rg'_* π'^* M` is invertible and the unit
`M ⟶ Rπ'_* π'^* M` is invertible, then so is the unit `Rg_* M ⟶ Rπ_* π^* Rg_* M`. -/
theorem isIso_unit_app_derivedLowerStar_obj_of_isIso_baseChange_app (h : g' ≫ π = π' ≫ g)
    [QuasiCompact π] [QuasiSeparated π] [LocallyOfFiniteType π] [QuasiCompact π']
    [QuasiSeparated π'] [LocallyOfFiniteType π']
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))] (M : WeilComplex k₀ l X')
    [IsIso ((baseChange k₀ l h).app M)]
    [IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π').unit.app M)] :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app
      ((derivedLowerStar g).obj M)) :=
  have : IsIso ((mateEquiv (upperStarDerivedLowerStarAdjunction g)
      (upperStarDerivedLowerStarAdjunction g') (upperStarCompUpperStarIso k₀ l h).hom).app M) :=
    inferInstanceAs (IsIso ((baseChange k₀ l h).app M))
  isIso_unit_app_of_isIso_mateEquiv_app (upperStarDerivedLowerStarAdjunction g)
    (upperStarDerivedLowerStarAdjunction g') (upperStarDerivedLowerStarAdjunction π)
    (upperStarDerivedLowerStarAdjunction π') (upperStarCompUpperStarIso k₀ l h).hom M

end AlgebraicGeometry.WeilComplex
