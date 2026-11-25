/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.HomologySequence
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.WeilSheaf.TraceFunctionCongr

/-!
# Weil sheaves placed in degree `-1`

The functor `G ↦ G[1]` from Weil sheaves to Weil complexes places a Weil sheaf in degree `-1`.
It is fully faithful, its `𝓗⁻¹` is the identity, and its image consists, up to isomorphism, of the
Weil complexes whose cohomology sheaves vanish outside degree `-1`. Isomorphisms of Weil sheaves
preserve lisseness and weight bounds.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.toShiftedComplex`: the functor `G ↦ G[1]`.
- `AlgebraicGeometry.WeilSheaf.toShiftedComplexCompHomologySheafIso`: `𝓗⁻¹(G[1]) ≅ G`.
- `AlgebraicGeometry.WeilComplex.nonempty_iso_toShiftedComplex`: a Weil complex with cohomology
  concentrated in degree `-1` is `𝓗⁻¹(K)[1]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

/-- The functor `G ↦ G[1]`: a Weil sheaf placed in degree `-1`. -/
noncomputable abbrev toShiftedComplex : WeilSheaf k₀ l X ⥤ WeilComplex k₀ l X :=
  toComplex ⋙ shiftFunctor _ (1 : ℤ)

/-- The underlying complex of `G[1]` is the underlying pro-étale Weil sheaf of `G` placed in
degree `-1`. -/
noncomputable def toShiftedComplexCompιIso :
    toShiftedComplex ⋙ (WeilComplex.objectProperty k₀ l X).ι ≅
      (objectProperty k₀ l X).ι ⋙ _root_.DerivedCategory.singleFunctor _ (-1) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((WeilComplex.objectProperty k₀ l X).ι.commShiftIso (1 : ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((_root_.DerivedCategory.singleFunctors _).shiftIso 1 (-1) 0
      (by norm_num))

/-- `𝓗⁻¹(G[1]) ≅ G`, naturally in the Weil sheaf `G`. -/
noncomputable def toShiftedComplexCompHomologySheafIso :
    toShiftedComplex ⋙ WeilComplex.homologySheaf (-1) ≅ 𝟭 (WeilSheaf k₀ l X) :=
  ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight toShiftedComplexCompιIso _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-1)) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The cohomology sheaves of `G[1]` vanish outside degree `-1`. -/
theorem isZero_homologySheaf_toShiftedComplex {a : ℤ} (ha : a ≠ -1) (G : WeilSheaf k₀ l X) :
    IsZero ((WeilComplex.homologySheaf a).obj (toShiftedComplex.obj G)) := by
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  refine IsZero.of_iso ?_
    ((_root_.DerivedCategory.homologyFunctor _ a).mapIso (toShiftedComplexCompιIso.app G))
  obtain h | h := ha.lt_or_gt
  · exact (_root_.DerivedCategory.isGE_iff
      ((_root_.DerivedCategory.singleFunctor _ (-1)).obj G.obj) (-1)).1 inferInstance a h
  · exact (_root_.DerivedCategory.isLE_iff
      ((_root_.DerivedCategory.singleFunctor _ (-1)).obj G.obj) (-1)).1 inferInstance a h

/-- Isomorphic Weil sheaves have the same upper weight bounds. -/
theorem HasWeightsAtMost.of_iso {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    {w : ℝ} (hF : F.HasWeightsAtMost ι w) : G.HasWeightsAtMost ι w := fun x ↦
  (hF x).of_equiv (nonempty_equiv_stalkAt_of_iso _ _ _ e.symm).some

end WeilSheaf

namespace WeilComplex

/-- A Weil complex whose cohomology sheaves vanish outside degree `-1` is its `𝓗⁻¹` placed in
degree `-1`. -/
theorem nonempty_iso_toShiftedComplex (K : WeilComplex k₀ l X)
    (hK : ∀ a ≠ -1, IsZero ((homologySheaf a).obj K)) :
    Nonempty (K ≅ WeilSheaf.toShiftedComplex.obj ((homologySheaf (-1)).obj K)) := by
  have : K.obj.IsGE (-1) := (_root_.DerivedCategory.isGE_iff _ _).2 fun i hi ↦
    (isZero_homologySheaf_obj_iff _ _).1 (hK i hi.ne)
  have : K.obj.IsLE (-1) := (_root_.DerivedCategory.isLE_iff _ _).2 fun i hi ↦
    (isZero_homologySheaf_obj_iff _ _).1 (hK i hi.ne')
  obtain ⟨A, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj (-1)
  let eA : A ≅ ((homologySheaf (-1)).obj K).obj :=
    ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-1)).app A).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ (-1)).mapIso e.symm
  exact ⟨ObjectProperty.isoMk _ (e ≪≫ (_root_.DerivedCategory.singleFunctor _ (-1)).mapIso eA ≪≫
    ((WeilSheaf.toShiftedComplexCompιIso (k₀ := k₀) (l := l) (X := X)).app
      ((homologySheaf (-1)).obj K)).symm)⟩

/-- Isomorphic Weil complexes have the same trace function. -/
theorem traceFunction_eq_of_iso {K L : WeilComplex k₀ l X} (e : K ≅ L) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    K.traceFunction n y = L.traceFunction n y :=
  finsum_congr fun a ↦ by rw [WeilSheaf.traceFunction_eq_of_iso ((homologySheaf a).mapIso e)]

/-- The trace function of `G[1]` is the negative of that of the Weil sheaf `G`. -/
theorem traceFunction_toShiftedComplex (G : WeilSheaf k₀ l X) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (WeilSheaf.toShiftedComplex.obj G).traceFunction n y = -G.traceFunction n y := by
  have e : (homologySheaf (-1)).obj (WeilSheaf.toShiftedComplex.obj G) ≅ G :=
    WeilSheaf.toShiftedComplexCompHomologySheafIso.app G
  rw [traceFunction_eq_sum _ {-1} (fun a ha ↦
      WeilSheaf.isZero_homologySheaf_toShiftedComplex (Finset.notMem_singleton.1 ha) G),
    Finset.sum_singleton, WeilSheaf.traceFunction_eq_of_iso e]
  simp

end WeilComplex

end AlgebraicGeometry
