/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
public import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingCompactification
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-! # Finite internal-etale realization with fixed Tor intervals

proof.md, paragraph (3); Stacks 09AL, 09C2, 09A6;
Bhatt--Scholze, Lemma 5.4.3
(auxiliary; not a blueprint node).

The fixed-scalar presentation of the normalized section-action encoding is used here.
It is the same intrinsic constant-ring comparison, followed by its fixed-scalar
coefficient equivalence. No derived category or tensor product is redefined.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

/-- The specified realization `E_T⁻¹ ν_T^*`, in the fixed-scalar presentation of the
normalized section-action equivalence. The additional fixed-scalar equivalence cancels
between `ν_T^*` and `E_T⁻¹`.
Source: blueprint direct-image proof, paragraph (3), finite coefficient comparison
(auxiliary; not a blueprint node). -/
def internalEtaleRealization (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (T : Scheme.{u}) (e : Encoding A T) :
    Etale.DerivedCategoryModule (ULift.{u + 1} A) T ⥤
      DerivedCategory (Internal A T) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory ⋙
    e.fixedDerived.inverse

private theorem etaleBC_iff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T) :
    Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T K ↔
      Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hv⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 ?_⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 ?_⟩⟩, ?_⟩
    · exact fun i hi ↦ hv i (Or.inl hi)
    · exact fun i hi ↦ hv i (Or.inr hi)
    · exact fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (hc i), min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).mp ha i (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).mp hb i (lt_of_le_of_lt (le_max_right _ _) hi)

private theorem ordinary_constructible_iff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    ordinaryConstructible A T M ↔ IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [ordinaryConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩), fun i ↦ by
        obtain ⟨P, _, e⟩ := hC i.down
        exact ⟨P, Module.Finite.of_finite, e⟩⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    refine ⟨C.restrictIndexOfSmall.{u}, fun i ↦ ?_⟩
    obtain ⟨P, _, e⟩ := h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)
    exact ⟨P, Module.finite_of_finite (ULift.{u + 1} A), e⟩

private theorem ordinaryBC_iff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    ordinaryBoundedConstructible A T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
  constructor
  · rintro ⟨hb, hc⟩
    apply DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} A) hb
    intro n
    exact exists_isConstructibleSheaf_iso_comparisonUpperStar_obj (ULift.{u + 1} A)
      ((ordinary_constructible_iff A T _).mp (hc n))
  · intro h
    have hi := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ h
    exact ⟨hi.1, fun n ↦ (ordinary_constructible_iff A T _).mpr (hi.2 n)⟩

/-- Finite internal-etale realization restricts to an equivalence for every ordered
Tor interval and commutes naturally with the specified unbounded total direct images
on all bounded-below etale inputs. The encodings are normalized section-action
encodings; thus the assertion applies to each choice of the equivalence in the node.

proof.md,
paragraph (3); Stacks 09AL, 09C2, 09A6; Bhatt--Scholze, Lemma 5.4.3
(auxiliary; not a blueprint node).

Proof:
1. The standing geometric hypotheses make T qcqs. Match the ordinary fixed-scalar
constructibility convention with the source's finite-stratification convention by resizing
cover indices; the etale boundedness conventions agree by isGE_iff and isLE_iff.
2. Apply the existing fixed-module bounded constructible descent theorem to the
constructible cohomology sheaves. Bounded-below derived Hom bijectivity gives full
faithfulness on the etale source subcategory.
3. The existing fixed-module Tor comparison preserves and reflects each interval.
4. encoding_constructibility and encoding_tensor_tor give the same two identifications
for every supplied normalized encoding E T. Lift the composite of site comparison and
its inverse encoding to the two full subcategories. The counit proves membership;
descent and the unit prove essential surjectivity. Its ambient functor is definitionally
the specified realization.
5. Reuse encodingDerivedPushforwardIso, the proved comparison of the separately specified
unbounded direct images. It derives the normalized sectionwise action comparison by
exact-equivalence transport through K-injective resolutions.
6. Apply the existing fixed-module bounded-below direct-image comparison, then use
rightDerivedFunctorPlusCompatibility and mapDerivedCategoryPlusCompatibility to view it
in the full unbounded derived categories.
7. Conjugate step 5 by the inverse encodings and compose it with step 6. All factors are
natural isomorphisms. Zero rings, empty schemes and degenerate intervals need no exclusions.
-/
theorem finiteCtfInternalEtaleRealization_of_field
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (E : ∀ T : Scheme.{u}, Encoding A T) :
    (∀ (T : Over (Spec (.of k)))
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      (a b : ℤ), a ≤ b →
      ∃ e : ObjectProperty.FullSubcategory
        (fun K ↦ Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1} A) T.left K ∧
          Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ≌
        ObjectProperty.FullSubcategory
          (fun K ↦ constantModelBoundedConstructible (coefficient A) T.left K ∧
            DerivedCategory.torAmplitudeIn (Internal A T.left) a b K),
        Nonempty (e.functor ⋙ ObjectProperty.ι (fun K ↦
            constantModelBoundedConstructible (coefficient A) T.left K ∧
              DerivedCategory.torAmplitudeIn (Internal A T.left) a b K) ≅
          ObjectProperty.ι (fun K ↦ Etale.DerivedCategory.isBoundedConstructible
              (ULift.{u + 1} A) T.left K ∧
            Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ⋙
              internalEtaleRealization A T.left (E T.left))) ∧
    (∀ (V T : Over (Spec (.of k)))
      [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      (f : V ⟶ T) [QuasiCompact f.left] [QuasiSeparated f.left],
      Nonempty (DerivedCategory.Plus.ι ⋙
          (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.left).rightDerivedFunctor ⋙
            internalEtaleRealization A T.left (E T.left) ≅
        DerivedCategory.Plus.ι ⋙ internalEtaleRealization A V.left (E V.left) ⋙
          CondensedRing.moduleObjectDerivedPushforward (coefficient A) f.left)) := by
  classical
  constructor
  · intro T _ _ _ a b hab
    have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
    have : QuasiSeparatedSpace T.left := quasiSeparatedSpace_of_quasiSeparated T.hom
    let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T.left
    let e := (E T.left).fixedDerived
    let P : ObjectProperty (Etale.DerivedCategoryModule (ULift.{u + 1} A) T.left) :=
      fun K ↦ Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T.left K ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K
    let Q : ObjectProperty (DerivedCategory (Internal A T.left)) := fun K ↦
      constantModelBoundedConstructible (coefficient A) T.left K ∧
        _root_.DerivedCategory.torAmplitudeIn (Internal A T.left) a b K
    have hb := (encoding_constructibility A T.left (E T.left)).2
    have ht := (encoding_tensor_tor A T.left (E T.left)).2.2
    have htC (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T.left) :
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K ↔
          _root_.DerivedCategory.torAmplitudeIn _ a b (C.mapDerivedCategory.obj K) :=
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.trans
        (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K).symm
    let F := P.ι ⋙ C.mapDerivedCategory
    have hplus (K : P.FullSubcategory) : DerivedCategory.TStructure.t.plus K.obj := by
      obtain ⟨c, d, _, hv⟩ := K.property.1.2
      exact ⟨c, (DerivedCategory.isGE_iff K.obj c).2 fun i hi ↦ hv i (Or.inl hi)⟩
    have : F.Full := ⟨fun {K L} f ↦ by
      obtain ⟨g, hg⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj (hplus L)).2 f
      exact ⟨ObjectProperty.homMk g, hg⟩⟩
    have : F.Faithful := ⟨fun {K L} f g h ↦ ObjectProperty.hom_ext _
      ((bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj (hplus L)).1 h)⟩
    let R := Q.lift (F ⋙ e.inverse) (fun K ↦ by
      have hbc := DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
        ((etaleBC_iff A T.left _).mp K.property.1)
      have htor := (htC K.obj).mp K.property.2
      have he := e.counitIso.app (C.mapDerivedCategory.obj K.obj)
      exact ⟨(hb _).mpr ((ordinaryBC_iff A T.left _).mpr
        ((DerivedCategory.boundedConstructible _ _).prop_of_iso he.symm
          hbc)),
        (ht _ a b hab).mpr ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
          he.symm htor)⟩)
    have : R.Full := by dsimp [R]; infer_instance
    have : R.Faithful := by dsimp [R]; infer_instance
    have : R.EssSurj := by
      constructor
      intro K
      obtain ⟨L, hL, ⟨j⟩⟩ := (ordinaryBC_iff A T.left _).mp ((hb K.obj).mp K.property.1)
      have htor := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso j.symm
        ((ht K.obj a b hab).mp K.property.2)
      let L' : P.FullSubcategory :=
        ⟨L, (etaleBC_iff A T.left L).mpr hL, (htC L).mpr htor⟩
      exact ⟨L', ⟨Q.isoMk (e.inverse.mapIso j ≪≫ (e.unitIso.app K.obj).symm)⟩⟩
    have : R.IsEquivalence := {}
    exact ⟨R.asEquivalence, ⟨Iso.refl _⟩⟩
  · intro V T _ _ _ _ _ _ f _ _
    let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let g := Etale.lowerStar C f.left
    let h := lowerStar C f.left
    let v := comparisonUpperStar C V.left
    let t := comparisonUpperStar C T.left
    let eV := (E V.left).fixedDerived
    let eT := (E T.left).fixedDerived
    obtain ⟨c⟩ := nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar C f.left
    let j : DerivedCategory.Plus.ι ⋙ g.rightDerivedFunctor ⋙ t.mapDerivedCategory ≅
        DerivedCategory.Plus.ι ⋙ v.mapDerivedCategory ⋙ h.rightDerivedFunctor :=
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight g.rightDerivedFunctorPlusCompatibility.symm
        t.mapDerivedCategory ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft g.rightDerivedFunctorPlus
        t.mapDerivedCategoryPlusCompatibility.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight c DerivedCategory.Plus.ι ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft v.mapDerivedCategoryPlus h.rightDerivedFunctorPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight v.mapDerivedCategoryPlusCompatibility h.rightDerivedFunctor ≪≫
      Functor.associator _ _ _
    let d := encodingDerivedPushforwardIso A f.left (E T.left) (E V.left)
    let di := Iso.inverseCompIso (G := eV)
      (Iso.isoCompInverse (H := eT) d ≪≫ Functor.associator _ _ _)
    exact ⟨Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight j eT.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.isoWhiskerLeft v.mapDerivedCategory di.symm)⟩

/-- The finite internal-etale realization over a field `k` of characteristic `p ≠ ℓ`: the case
of `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization_of_field`
with the characteristic of `k` recorded. -/
theorem finiteCtfInternalEtaleRealization
    (ℓ p : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ)
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (E : ∀ T : Scheme.{u}, Encoding A T) :
    (∀ (T : Over (Spec (.of k)))
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      (a b : ℤ), a ≤ b →
      ∃ e : ObjectProperty.FullSubcategory
        (fun K ↦ Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1} A) T.left K ∧
          Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ≌
        ObjectProperty.FullSubcategory
          (fun K ↦ constantModelBoundedConstructible (coefficient A) T.left K ∧
            DerivedCategory.torAmplitudeIn (Internal A T.left) a b K),
        Nonempty (e.functor ⋙ ObjectProperty.ι (fun K ↦
            constantModelBoundedConstructible (coefficient A) T.left K ∧
              DerivedCategory.torAmplitudeIn (Internal A T.left) a b K) ≅
          ObjectProperty.ι (fun K ↦ Etale.DerivedCategory.isBoundedConstructible
              (ULift.{u + 1} A) T.left K ∧
            Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ⋙
              internalEtaleRealization A T.left (E T.left))) ∧
    (∀ (V T : Over (Spec (.of k)))
      [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      (f : V ⟶ T) [QuasiCompact f.left] [QuasiSeparated f.left],
      Nonempty (DerivedCategory.Plus.ι ⋙
          (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.left).rightDerivedFunctor ⋙
            internalEtaleRealization A T.left (E T.left) ≅
        DerivedCategory.Plus.ι ⋙ internalEtaleRealization A V.left (E V.left) ⋙
          CondensedRing.moduleObjectDerivedPushforward (coefficient A) f.left)) :=
  finiteCtfInternalEtaleRealization_of_field k A E

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
