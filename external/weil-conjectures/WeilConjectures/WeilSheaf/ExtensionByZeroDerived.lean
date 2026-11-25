/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.WeilSheaf.ExtensionByZeroAdjunction
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.UpperStarComp

/-!
# The derived extension by zero of pro-étale Weil sheaves

Let `j : U ⟶ X` be an open immersion of `k₀`-schemes. The exact functors `j_!` and `j^*` of
pro-étale Weil sheaves induce an adjunction `D(j_!) ⊣ D(j^*)` on the derived categories
(`AlgebraicGeometry.ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction`) whose unit is an
isomorphism, `j_!` being fully faithful. Moreover:

- the extension by zero along a composite of open immersions is the composite of the extensions
  by zero (`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroCompIso`);
- the pullback of `j_! F` along a morphism whose range misses that of `j` vanishes
  (`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_upperStar_obj_extensionByZero_obj`);
- for a closed immersion `i` and an open immersion `j` with complementary ranges, a morphism of
  the derived category whose pullbacks along `i` and `j` are isomorphisms is an isomorphism
  (`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_of_isIso_upperStar_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- For an adjunction `L ⊣ R` of exact functors with invertible unit, the unit of the derived
adjunction `D(L) ⊣ RR` is invertible: on the image of a complex `X` it is, up to the
isomorphisms `D(L) ∘ Q ≅ Q ∘ L` and `Q ∘ R ≅ RR ∘ Q`, the image of the unit of `L ⊣ R`. -/
instance isIso_mapDerivedCategoryRightDerivedAdjunction_unit (adj : L ⊣ R) [IsIso adj.unit] :
    IsIso adj.mapDerivedCategoryRightDerivedAdjunction.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨X, ⟨e⟩⟩ : ∃ X, Nonempty (DerivedCategory.Qh.obj X ≅ K) :=
    ⟨_, ⟨(Localization.essSurj DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))).mem_essImage K |>.getIso⟩⟩
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have h := Adjunction.derivedη_fac_app (adj.mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)
  have hu : IsIso ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    have : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M) := by
      have (n : ℤ) : IsIso (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M).f n) := by
        dsimp [Adjunction.mapHomologicalComplex]
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  have hα : IsIso (L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) := inferInstance
  rw [← IsIso.eq_comp_inv] at h
  change IsIso ((Adjunction.derivedη (adj.mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit).app _)
  rw [h]
  infer_instance

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open ProEtale Pretriangulated

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section Adjunction

variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The adjunction `D(j_!) ⊣ D(j^*)` on the derived categories of pro-étale Weil sheaves, derived
from `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction`, the total right
derived functor of the exact functor `j^*` being `D(j^*)`. -/
noncomputable def ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction :
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⊣
      (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory :=
  (ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l
    j).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (ProEtaleWeilSheaf.upperStar k₀ l j).rightDerivedFunctorIsoMapDerivedCategory

/-- The derived extension by zero `D(j_!)` of pro-étale Weil sheaves is fully faithful: the unit
of `D(j_!) ⊣ R(j^*)` is invertible, as is the unit of `j_! ⊣ j^*`. -/
noncomputable def ProEtaleWeilSheaf.fullyFaithfulMapDerivedCategoryExtensionByZero :
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory.FullyFaithful :=
  (ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l
    j).mapDerivedCategoryRightDerivedAdjunction.fullyFaithfulLOfIsIsoUnit

/-- The unit `K ⟶ D(j^*) D(j_!) K` of the derived adjunction is an isomorphism. -/
instance ProEtaleWeilSheaf.isIso_derivedExtensionByZeroUpperStarAdjunction_unit :
    IsIso (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l j).unit :=
  have := (ProEtaleWeilSheaf.fullyFaithfulMapDerivedCategoryExtensionByZero (k₀ := k₀) (l := l)
    j).full
  have := (ProEtaleWeilSheaf.fullyFaithfulMapDerivedCategoryExtensionByZero (k₀ := k₀) (l := l)
    j).faithful
  Adjunction.unit_isIso_of_L_fully_faithful _

end Adjunction

section Vanishing

variable {U X W : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (g : W ⟶ X) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of an extension by zero `j_! F` of pro-étale Weil sheaves along a morphism `g`
whose range misses that of `j` vanishes, as it does on the underlying sheaves
(`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek`). -/
lemma ProEtaleWeilSheaf.isZero_upperStar_obj_extensionByZero_obj
    (h : Disjoint (Set.range j.base) (Set.range g.base)) (F : ProEtaleWeilSheaf k₀ l U) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l g).obj
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j).obj F)) := by
  refine (ProEtaleWeilSheaf.isZero_iff _).2
    (isZero_adicUpperStar_adicOpenImmersionLowerShriek _ _ ?_ F.carrier)
  rw [Scheme.Hom.range_geometricFiberMap, Scheme.Hom.range_geometricFiberMap,
    ← Set.preimage_inter, Set.disjoint_iff_inter_eq_empty.1 h, Set.preimage_empty]

/-- The pullback of a derived extension by zero `D(j_!) K` along a morphism `g` whose range
misses that of `j` vanishes. -/
lemma ProEtaleWeilSheaf.isZero_mapDerivedCategory_upperStar_obj_extensionByZero_obj
    (h : Disjoint (Set.range j.base) (Set.range g.base))
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l U)) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory.obj K)) :=
  DerivedCategory.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj
    (fun F ↦ ProEtaleWeilSheaf.isZero_upperStar_obj_extensionByZero_obj j g h F) K

end Vanishing

section Conservative

variable {Z U X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

/-- For a closed immersion `i` and a quasi-compact `j` with complementary ranges, a morphism `φ`
of the derived category of pro-étale Weil sheaves is an isomorphism as soon as its pullbacks
`D(i^*) φ` and `D(j^*) φ` are: the cone of `φ` is killed by `D(i^*)` and `D(j^*)`, which jointly
detect zero objects. -/
lemma ProEtaleWeilSheaf.isIso_of_isIso_upperStar_map
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K L : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)} (φ : K ⟶ L)
    (hi : IsIso ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.map φ))
    (hj : IsIso ((ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.map φ)) :
    IsIso φ := by
  obtain ⟨W, v, w, h⟩ := distinguished_cocone_triangle φ
  have hW : IsZero W := DerivedCategory.isZero_of_isZero_mapDerivedCategory_obj
    (fun F hi hj ↦ ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij F hi hj)
    ((Triangle.isZero₃_iff_isIso₁ _
      ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.map_distinguished _ h)).2 hi)
    ((Triangle.isZero₃_iff_isIso₁ _
      ((ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.map_distinguished _ h)).2 hj)
  exact (Triangle.isZero₃_iff_isIso₁ _ h).1 hW

end Conservative

section Comp

variable {U V X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [V.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (a : U ⟶ V) [IsOpenImmersion a] [a.IsOver (Spec (CommRingCat.of k₀))]
  (b : V ⟶ X) [IsOpenImmersion b] [b.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The extension by zero along a composite of open immersions is the composite of the
extensions by zero: both are left adjoint to `(a ≫ b)^* ≅ b^* ⋙ a^*`. -/
noncomputable def ProEtaleWeilSheaf.extensionByZeroCompIso :
    ProEtaleWeilSheaf.extensionByZero k₀ l (a ≫ b) ≅
      ProEtaleWeilSheaf.extensionByZero k₀ l a ⋙ ProEtaleWeilSheaf.extensionByZero k₀ l b :=
  (conjugateIsoEquiv ((ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l a).comp
      (ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l b))
    (ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l (a ≫ b))).symm
    (ProEtaleWeilSheaf.upperStarCompIso k₀ l a b).symm

variable (k₀ l) in
/-- The derived extension by zero along a composite of open immersions is the composite of the
derived extensions by zero. -/
noncomputable def ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroCompIso :
    (ProEtaleWeilSheaf.extensionByZero k₀ l (a ≫ b)).mapDerivedCategory ≅
      (ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l b).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.extensionByZeroCompIso k₀ l a b) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end Comp

end AlgebraicGeometry
