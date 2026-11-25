/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.Integral.IntegralQuotientRoosHomotopy
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Localization.Triangulated

/-! # Exactness of normalized integral quotient completion

Source: Stacks Project, Tags 06XN and 05SE; the signed Roos cone calculus,
Stacks Tags 014A, 014E and 08TC.
(blueprint: lem-sf-integral-quotient-completion-exact)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.IntegralOnSlice.abSheafify
  WeilConjectures.IntegralOnSlice.abLocallyBijective
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace WeilConjectures
open IntegralOnSlice

private theorem kanUnit_commShift
    {K L B : Type*} [Category K] [Category L] [Category B]
    [HasShift K ℤ] [HasShift L ℤ] [HasShift B ℤ]
    (Q : K ⥤ L) [Q.CommShift ℤ] (H : K ⥤ B) [H.CommShift ℤ]
    (F G : L ⥤ B) [F.CommShift ℤ] [G.CommShift ℤ]
    (ε : Q ⋙ F ⟶ H) [F.IsRightKanExtension ε] [NatTrans.CommShift ε ℤ]
    (β : Q ⋙ G ⟶ H) [NatTrans.CommShift β ℤ]
    (δ : G ⟶ F) (hδ : Functor.whiskerLeft Q δ ≫ ε = β) :
    NatTrans.CommShift δ ℤ := by
  constructor
  intro n
  let S := shiftFunctor B n
  let γ := (Functor.associator Q F S).inv ≫ Functor.whiskerRight ε S
  let : (F ⋙ S).IsRightKanExtension γ :=
    Functor.kanPostShift H Q F ε n
  apply (F ⋙ S).hom_ext_of_isRightKanExtension γ
  ext X
  have hd (X : K) : δ.app (Q.obj X) ≫ ε.app X = β.app X :=
    congrArg (fun a ↦ a.app X) hδ
  simp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp]
  apply (cancel_epi (G.map ((Q.commShiftIso n).hom.app X))).1
  symm
  simp only [Category.assoc]
  change G.map ((Q.commShiftIso n).hom.app X) ≫
      δ.app ((Q.obj X)⟦n⟧) ≫ (F.commShiftIso n).hom.app (Q.obj X) ≫
        S.map (ε.app X) =
    G.map ((Q.commShiftIso n).hom.app X) ≫
      (G.commShiftIso n).hom.app (Q.obj X) ≫ S.map (δ.app (Q.obj X)) ≫
      S.map (ε.app X)
  rw [reassoc_of% (δ.naturality ((Q.commShiftIso n).hom.app X))]
  have he := NatTrans.shift_app_comm ε n X
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at he
  rw [he, ← Category.assoc, hd, ← S.map_comp, hd]
  simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
    (NatTrans.shift_app_comm β n X).symm

/-- The quotient-Roos descent is additive and exact, and its specified quotient
augmentation commutes with the same exact functor's integer shifts.

Source: Stacks Project, Tags 06XN and 05SE; signed Roos cone and augmentation
calculus, Tags 014A, 014E and 08TC
(blueprint: lem-sf-integral-quotient-completion-exact).

Proof: assemble ordinary reduction followed by restriction of scalars into the
additive module-valued tower functor. Its degreewise extension to complexes
preserves homotopies, shifts and mapping-cone triangles. The signed Roos
comparison preserves cone inclusion and boundary, so its homotopy descent is an
exact functor. Choose K-flat resolutions with flat terms. Each finite quotient
functor inverts quasi-isomorphisms between these representatives, and exact
countable products on the pro-etale site show that Roos also does so. The
resolving-class left-derived theorem therefore supplies an exact derived functor.
Its comparison on good representatives identifies it uniquely with
IntegralOnSlice.completion, by completion_exists. Transfer additivity and its
coherent shift structure along this normalized isomorphism. At the complex
level, the quotient augmentation has zero shifted-product coordinate. The Roos
shift-augmentation identity carries this map to the shifted augmentation; the
termwise quotient units commute with shifts because they come from a natural
transformation on modules. The derived counit and its coherent Kan shift
structure carry this identity to the derived category. The localization of good
representatives detects equality of natural transformations, so the descended
augmentation is precisely completionUnit by completionUnit_existsUnique and
commutes with the transported shifts. Cone compatibility proves exactness for
these same shifts, rather than an independently chosen exact structure. -/
theorem integralQuotientCompletion_exact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : AlgebraicGeometry.Scheme.{t}) [CompactSpace T] [QuasiSeparatedSpace T]
    (_hl : ∀ x : T, IsUnit (l : T.residueField x)) :
    (completion l E T none).Additive ∧
      ∃ (_ : (completion l E T none).CommShift ℤ),
        (completion l E T none).IsTriangulated ∧
          NatTrans.CommShift (completionUnit l E T none) ℤ := by
  classical
  let A := Mod l E T none
  let q := HomotopyCategory.quotient A (.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  obtain ⟨H, sH, eH, β, hH, hβ, hnormal⟩ := integralQuotientRoos_homotopy l E T
  let : H.CommShift ℤ := sH
  let : H.IsTriangulated := hH
  let : NatTrans.CommShift β ℤ := hβ
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : Cx l E T none, Good l E T none K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (a : Y ⟶ X), Y ∈ P ∧ W a := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    let : EssentiallySmall.{max u (t + 1)} (Site T none) := essentiallySmallSelf _
    obtain ⟨L, a, hL, hflat, ha, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := ring l E T none) K
    have hs : ∀ i, SheafOfModules.IsFlatOnSite
        (J := topology T none) (R := ring l E T none) (L.X i) :=
      fun i ↦ (exactFunctor A A).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (ring l E T none) (L.X i)).symm (hflat i)
    exact ⟨q.obj L, q.map a, ⟨L, ⟨hL, hs⟩, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff a).2 ha⟩
  have hinv : ∀ X Y : HomotopyCategory A (.up ℤ), ∀ a : X ⟶ Y,
      X ∈ P → Y ∈ P → W a → IsIso (H.map a) := by
    rintro X Y a ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ ha
    obtain ⟨f, rfl⟩ := q.map_surjective a
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 ha
    let f' : (⟨K, hK⟩ : (Good l E T none).FullSubcategory) ⟶ ⟨L, hL⟩ :=
      ObjectProperty.homMk f
    have hr := IntegralOnSlice.roosGoodInverts l E T none f' hf
    exact (NatIso.isIso_map_iff eH f).2 hr
  obtain ⟨_, F, ε, hF, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (D l E T none) H P hres hinv
  let : F.IsRightKanExtension ε := hF.isRightKanExtension
  obtain ⟨sF, hε⟩ := Functor.rightKanExtension_coherentShift H Q F ε inferInstance
  let : F.CommShift ℤ := sF
  let : NatTrans.CommShift ε ℤ := hε
  obtain ⟨hleft, hright, htri, hsat, _, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : W.HasRightCalculusOfFractions := hright
  have hW : W.IsSaturatedTriangulatedMultiplicativeSystem :=
    ⟨⟨⟨hleft, hright⟩, fun _ _ _ _ f g k ↦ hsat _ _ _ _ g f k⟩, htri⟩
  have hdefined : ∀ X, H.IsTriangulatedLeftDerivedDefinedAt W hW X := by
    intro X
    obtain ⟨Y, _, hc, _, _⟩ :=
      Functor.resolvingClass_essentialConstancy W H P hres hinv X
    exact ⟨Y, hc⟩
  let : (Q ⋙ F).IsTriangulated := ⟨fun V hV ↦
    Functor.leftDerived_kan_map_source_distinguished _ _ _ H W hW Q F ε
      inferInstance hdefined hε V hV⟩
  let := Localization.essSurj_mapArrow Q W
  let : F.IsTriangulated := Functor.isTriangulated_of_precomp Q F
  let δ : 𝟭 (D l E T none) ⟶ F :=
    F.liftOfIsRightKanExtension ε _ ((Functor.rightUnitor Q).hom ≫ β)
  have hδ := F.liftOfIsRightKanExtension_fac ε _ ((Functor.rightUnitor Q).hom ≫ β)
  let : NatTrans.CommShift δ ℤ := kanUnit_commShift Q H F _ ε
    ((Functor.rightUnitor Q).hom ≫ β) δ hδ
  let i := DerivedCategory.quotientCompQhIso A
  let α : DerivedCategory.Q ⋙ F ⟶ roos l E T none ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv F ≫ (Functor.associator q Q F).hom ≫
      Functor.whiskerLeft q ε ≫ eH.hom
  have hα (K : (Good l E T none).FullSubcategory) :
      IsIso (α.app K.obj) := by
    let := hcomp (q.obj K.obj) ⟨K.obj, K.property, rfl⟩
    dsimp only [α, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app]
    infer_instance
  let c : qGood l E T none ⋙ F ≅ roosGood l E T none :=
    NatIso.ofComponents (fun K : (Good l E T none).FullSubcategory ↦ by
      letI := hα K
      exact asIso (α.app K.obj)) (by
        intro K L f
        change F.map (DerivedCategory.Q.map f.hom) ≫ α.app L.obj =
          α.app K.obj ≫ DerivedCategory.Q.map ((roos l E T none).map f.hom)
        exact α.naturality f.hom)
  obtain ⟨a, ha, _⟩ := (completion_exists l E T none).choose_spec.2 F
    (completionComparison l E T none) c
  let e : F ≅ completion l E T none := a.symm
  let : (completion l E T none).CommShift ℤ := Functor.CommShift.ofIso e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  let : (completion l E T none).IsTriangulated := Functor.isTriangulated_of_iso e
  have hunit : δ ≫ e.hom = completionUnit l E T none := by
    apply (completionUnit_existsUnique l E T none).unique
    · intro K
      have he : e.hom.app ((qGood l E T none).obj K) ≫
          (completionComparison l E T none).hom.app K = α.app K.obj := by
        have hh := congrArg (fun z ↦ z.app K) ha
        change a.hom.app ((qGood l E T none).obj K) ≫ α.app K.obj =
          (completionComparison l E T none).hom.app K at hh
        dsimp only [e, Iso.symm_hom]
        rw [← hh, ← Category.assoc, a.inv_hom_id_app, Category.id_comp]
      change (δ.app _ ≫ e.hom.app _) ≫ _ = _
      rw [Category.assoc, he]
      change δ.app (DerivedCategory.Q.obj K.obj) ≫ α.app K.obj = _
      have hd : δ.app (Q.obj (q.obj K.obj)) ≫ ε.app (q.obj K.obj) =
          β.app (q.obj K.obj) := by
        have hh := congrArg (fun z ↦ z.app (q.obj K.obj)) hδ
        change δ.app _ ≫ ε.app _ = 𝟙 _ ≫ β.app _ at hh
        simpa only [Category.id_comp] using hh
      have hn := δ.naturality (i.inv.app K.obj)
      change i.inv.app K.obj ≫ δ.app (Q.obj (q.obj K.obj)) =
        δ.app (DerivedCategory.Q.obj K.obj) ≫ F.map (i.inv.app K.obj) at hn
      calc
        δ.app (DerivedCategory.Q.obj K.obj) ≫ α.app K.obj =
            (δ.app (DerivedCategory.Q.obj K.obj) ≫ F.map (i.inv.app K.obj)) ≫
              ε.app (q.obj K.obj) ≫ eH.hom.app K.obj := by
          dsimp only [α, NatTrans.comp_app, Functor.whiskerRight_app,
            Functor.whiskerLeft_app, Functor.associator_hom_app]
          simp only [Category.assoc]
          erw [Category.id_comp]
        _ = (i.inv.app K.obj ≫ δ.app (Q.obj (q.obj K.obj))) ≫
            ε.app (q.obj K.obj) ≫ eH.hom.app K.obj := by rw [← hn]
        _ = i.inv.app K.obj ≫ β.app (q.obj K.obj) ≫ eH.hom.app K.obj := by
          simpa only [Category.assoc] using
            congrArg (fun z ↦ i.inv.app K.obj ≫ z ≫ eH.hom.app K.obj) hd
        _ = DerivedCategory.Q.map (roosUnit l E T none K.obj) := hnormal K.obj
    · exact (completionUnit_existsUnique l E T none).exists.choose_spec
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← hunit]
  infer_instance

end WeilConjectures
