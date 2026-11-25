/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.SmoothBaseChange

/-!
# Auxiliary facts for homotopy invariance of Weil complexes

Facts used in the dévissage proving homotopy invariance along trivial line bundles
(`WeilConjectures.WeilSheaf.HomotopyInvariance`):

- Weil complexes on an empty scheme vanish (`AlgebraicGeometry.WeilComplex.isZero_of_isEmpty`);
- the trivial line bundle `X ×_{k₀} 𝔸¹ ⟶ X` is smooth
  (`AlgebraicGeometry.WeilComplex.smooth_of_isPullback`);
- a Weil complex on a reduced scheme has lisse cohomology sheaves on a dense open subscheme
  (`AlgebraicGeometry.WeilComplex.exists_dense_isLisse_homologySheaf_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Every Weil complex on an empty scheme is zero. -/
lemma isZero_of_isEmpty {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [IsEmpty X]
    (K : WeilComplex k₀ l X) : IsZero K := by
  have : IsEmpty (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    ⟨fun x ↦ isEmptyElim ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.base x)⟩
  have h (i : ℤ) : IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj) :=
    (isZero_homologySheaf_obj_iff i K).1
      (WeilSheaf.isZero_iff_isZero_carrier.2 (ProEtale.isZero_adicSheaf_of_isEmpty l _))
  have : K.obj.IsLE 0 := (K.obj.isLE_iff 0).2 fun i _ ↦ h i
  have : K.obj.IsGE 1 := (K.obj.isGE_iff 1).2 fun i _ ↦ h i
  exact IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
    (_root_.DerivedCategory.TStructure.t.isZero K.obj 0 1)

omit [Finite k₀] in
/-- A trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` is smooth, as a base change of the smooth
morphism `𝔸¹ ⟶ Spec k₀`. -/
lemma smooth_of_isPullback {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] {π : Y ⟶ X}
    {s : Y ⟶ affineLine k₀}
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀))) : Smooth π := by
  have : Smooth (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using (AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1}
      (Spec (.of k₀))).smooth
  exact MorphismProperty.of_isPullback hπ.flip this

/-- Lissity of Weil sheaves is invariant under isomorphism. -/
private lemma isLisse_of_iso {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    {F G : WeilSheaf k₀ l X} (e : F ≅ G) (hF : F.IsLisse) : G.IsLisse :=
  ProEtale.IsAdicLisseSheaf.of_iso
    ((ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).mapIso e) hF

/-- A zero Weil sheaf is lisse. -/
private lemma isLisse_of_isZero {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} (hF : IsZero F) : F.IsLisse :=
  ProEtale.IsAdicLisseSheaf.of_isZero (WeilSheaf.isZero_iff_isZero_carrier.1 hF)

/-- The underlying object of the cohomology sheaf `𝓗ⁿ(K)`. -/
private noncomputable def homologySheafObjIso' {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (n : ℤ) (K : WeilComplex k₀ l X) :
    ((homologySheaf n).obj K).obj ≅ (_root_.DerivedCategory.homologyFunctor _ n).obj K.obj :=
  Iso.refl _

/-- The underlying object of the pullback `φ^* K` of a Weil complex. -/
private noncomputable def upperStarObjIso' {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l Y) :
    ((upperStar φ).obj K).obj ≅
      (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory.obj K.obj :=
  Iso.refl _

/-- The underlying object of the pullback `φ^* F` of a Weil sheaf. -/
private noncomputable def weilSheafUpperStarObjIso' {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y) :
    ((WeilSheaf.upperStar φ).obj F).obj ≅ (ProEtaleWeilSheaf.upperStar k₀ l φ).obj F.obj :=
  Iso.refl _

/-- Pullback commutes with the cohomology sheaves: `𝓗ⁿ(φ^* K) ≅ φ^* 𝓗ⁿ(K)`. -/
private noncomputable def homologySheafUpperStarIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (n : ℤ) (K : WeilComplex k₀ l Y) :
    (homologySheaf n).obj ((upperStar φ).obj K) ≅
      (WeilSheaf.upperStar φ).obj ((homologySheaf n).obj K) :=
  ObjectProperty.isoMk _
    (homologySheafObjIso' n _ ≪≫ (_root_.DerivedCategory.homologyFunctor _ n).mapIso
      (upperStarObjIso' φ K) ≪≫
    ((Functor.mapDerivedCategoryHomologyFunctorIso (ProEtaleWeilSheaf.upperStar k₀ l φ) n).app
      K.obj).symm ≪≫
    (ProEtaleWeilSheaf.upperStar k₀ l φ).mapIso (homologySheafObjIso' n K).symm ≪≫
    (weilSheafUpperStarObjIso' φ _).symm)

/-- A Weil sheaf lisse on an open `V` is lisse on every smaller open `U ≤ V`. -/
private lemma isLisse_upperStar_of_le {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    {U V : X.Opens} (hle : U ≤ V) {G : WeilSheaf k₀ l X}
    (hV : ((WeilSheaf.upperStar V.ι).obj G).IsLisse) :
    ((WeilSheaf.upperStar U.ι).obj G).IsLisse := by
  have : (X.homOfLE hle).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [← comp_over V.ι, Scheme.homOfLE_ι_assoc, comp_over U.ι]⟩
  exact (WeilSheaf.isLisse_upperStar_congr (Scheme.homOfLE_ι X hle) _).1
    ((WeilSheaf.isLisse_upperStar_comp_iff _ V.ι _).2 (hV.upperStar _))

/-- A finite intersection of dense open subsets is dense. -/
private lemma dense_finsetInf {X : Scheme.{u}} {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, Dense (V i : Set X)) (s : Finset ι) : Dense ((s.inf V : X.Opens) : Set X) :=
  Finset.inf_induction (p := fun W : X.Opens ↦ Dense (W : Set X)) (by simp)
    (fun W₁ h₁ W₂ h₂ ↦ by simpa using h₁.inter_of_isOpen_left h₂ W₁.isOpen) fun i _ ↦ hV i

/-- The cohomology sheaves of a Weil complex concentrated in degrees `[a, b]` vanish outside
`[a, b]`. -/
private lemma isZero_homologySheaf_of_notMem_Icc {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) {a b n : ℤ} (ha : K.obj.IsGE a)
    (hb : K.obj.IsLE b) (hn : n ∉ Finset.Icc a b) : IsZero ((homologySheaf n).obj K) := by
  rw [isZero_homologySheaf_obj_iff]
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · exact _root_.DerivedCategory.isZero_of_isGE _ a n hn
  · exact _root_.DerivedCategory.isZero_of_isLE _ b n hn

/-- **Generic lissity for Weil complexes.** A Weil complex on a reduced `k₀`-scheme of finite type
has lisse cohomology sheaves on a dense open subscheme: it has finitely many nonzero cohomology
sheaves, each lisse on a dense open subscheme
(`AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar`), and the pullback commutes with
the cohomology sheaves. -/
lemma exists_dense_isLisse_homologySheaf_upperStar {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsReduced X] (K : WeilComplex k₀ l X) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      ∀ n : ℤ, ((homologySheaf n).obj ((upperStar U.ι).obj K)).IsLisse := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  have h (n : ℤ) := WeilSheaf.exists_dense_isLisse_upperStar ((homologySheaf n).obj K)
  refine ⟨(Finset.Icc a b).inf fun n ↦ (h n).choose,
    dense_finsetInf _ (fun n ↦ (h n).choose_spec.1) _,
    fun n ↦ isLisse_of_iso (homologySheafUpperStarIso _ n K).symm ?_⟩
  by_cases hn : n ∈ Finset.Icc a b
  · exact isLisse_upperStar_of_le (Finset.inf_le hn) (h n).choose_spec.2
  · exact isLisse_of_isZero ((WeilSheaf.upperStar _).map_isZero
      (isZero_homologySheaf_of_notMem_Icc K ha hb hn))

/-- If `X` is empty, the unit `K ⟶ Rφ_* φ^* K` is an isomorphism for every `φ : Y ⟶ X`, both
sides being zero. -/
lemma isIso_unit_app_of_isEmpty {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsEmpty X] (K : WeilComplex k₀ l X) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) φ).unit.app K) :=
  isIso_of_source_target_iso_zero _ (isZero_of_isEmpty _).isoZero
    (isZero_of_isEmpty _).isoZero

end AlgebraicGeometry.WeilComplex
