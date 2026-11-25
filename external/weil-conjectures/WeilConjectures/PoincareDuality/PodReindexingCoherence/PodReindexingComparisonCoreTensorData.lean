/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.Algebra.Homology.SixFunctors.SectionwiseTensorComparison
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement

/-! Tensor-side component data for the core reindexing comparison.
(blueprint: lem-pod-reindexing-comparison-core-tensor-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory

universe u u₁ v₁ u₂ v₂ c v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.MonoidalCategory CategoryTheory.Functor
-- The two generic helpers follow AdicCochainTensorReindexing; that specialization
-- already imports this item transitively, so its module cannot be imported here.
private theorem exists_total_tensor_comparison
    {M : Type u₁} [Category.{v₁} M] [Abelian M] [MonoidalCategory M]
    {N : Type u₂} [Category.{v₂} N] [Abelian N] [MonoidalCategory N]
    [MonoidalPreadditive M] [MonoidalPreadditive N]
    [HasCoproducts.{0} M] [HasCoproducts.{0} N]
    (U : M ⥤ N) [U.Additive] [U.IsLeftAdjoint]
    (e : ∀ A B : M, U.obj (A ⊗ B) ≅ U.obj A ⊗ U.obj B)
    (he : ∀ {A A' B B'} (f : A ⟶ A') (h : B ⟶ B'),
      U.map (f ⊗ₘ h) ≫ (e A' B').hom = (e A B).hom ≫ (U.map f ⊗ₘ U.map h)) :
    let F := U.mapHomologicalComplex (.up ℤ)
    let tY := Functor.uncurry.obj (Functor.map₂HomologicalComplex
      (curriedTensor M) (.up ℤ) (.up ℤ) (.up ℤ))
    let tX := Functor.uncurry.obj (Functor.map₂HomologicalComplex
      (curriedTensor N) (.up ℤ) (.up ℤ) (.up ℤ))
    ∃ chain : tY ⋙ F ≅ (F.prod F) ⋙ tX,
      ∀ (P Q : CochainComplex M ℤ) (p q : ℤ),
        U.map (CochainComplex.ιMapBifunctor P Q (curriedTensor M) p q (p + q) rfl) ≫
            (chain.hom.app (P, Q)).f (p + q) =
          (e (P.X p) (Q.X q)).hom ≫ CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q)
            (curriedTensor N) p q (p + q) rfl := by
  let F := U.mapHomologicalComplex (.up ℤ)
  let tY := Functor.uncurry.obj (Functor.map₂HomologicalComplex
    (curriedTensor M) (.up ℤ) (.up ℤ) (.up ℤ))
  let tX := Functor.uncurry.obj (Functor.map₂HomologicalComplex
    (curriedTensor N) (.up ℤ) (.up ℤ) (.up ℤ))
  have hiso (P Q : CochainComplex M ℤ) :
      IsIso (tensorPullbackTotal U e he P Q) :=
    tensorPullbackTotal_isIso U e he U.rightAdjoint (Adjunction.ofIsLeftAdjoint U) P Q
  let b0 : (F.prod F) ⋙ tX ≅ tY ⋙ F := NatIso.ofComponents
    (fun Z ↦ @asIso _ _ _ _ (tensorPullbackTotal U e he Z.1 Z.2) (hiso Z.1 Z.2)) (by
      intro Z W h
      dsimp only [F, tY, tX, Functor.comp_map, Functor.prod_map]
      simp only [Functor.uncurry_obj_map,
        Functor.map₂HomologicalComplex,
        SheafOfModules.CanonicalTensorPullbackProof.tensorMap_factor]
      exact SheafOfModules.CanonicalTensorPullbackProof.tensorPullbackTotal_naturality
        U e he h.1 h.2)
  refine ⟨b0.symm, ?_⟩
  intro P Q p q
  let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor M)
    p q (p + q) rfl
  let ι' := CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q)
    (curriedTensor N) p q (p + q) rfl
  let z := (HomologicalComplex.eval N (.up ℤ) (p + q)).mapIso
    (b0.app (P, Q))
  have hz : ι' ≫ z.hom = (e (P.X p) (Q.X q)).inv ≫ U.map ι := by
    change ι' ≫ tensorPullbackTotalComponent U e P Q (p + q) = _
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q rfl
  have hi : U.map ι ≫ z.inv = (e (P.X p) (Q.X q)).hom ≫ ι' := by
    apply (cancel_mono z.hom).1
    erw [Category.assoc, z.inv_hom_id, Category.comp_id, Category.assoc, hz,
      Iso.hom_inv_id_assoc]
  exact hi

open WeilConjectures in
private theorem exists_sectionwise_cochain_tensor_comparison
    {C : Type c} [Category.{v} C] {D : Type c} [Category.{v} D]
    [EssentiallySmall.{max c v w} C] [EssentiallySmall.{max c v w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})]
    [HasSheafify J AddCommGrpCat.{max c v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}]
    [HasSheafify K AddCommGrpCat.{max c v w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c v w}]
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf J CommRingCat.{max c v w}) (S : Sheaf K CommRingCat.{max c v w})
    (a : (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R ≅
      (f.sheafPushforwardContinuous RingCat.{max c v w} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj S))
    [(SheafOfModules.pushforward.{max c v w} a.hom).Additive]
    [(SheafOfModules.pushforward.{max c v w} a.hom).IsLeftAdjoint] :
    let U := SheafOfModules.pushforward.{max c v w} a.hom
    let F := U.mapHomologicalComplex (.up ℤ)
    ∃ chain : coefficientTotalTensor.{w, c, v} K S ⋙ F ≅
        (F.prod F) ⋙ coefficientTotalTensor.{w, c, v} J R,
      ∀ (P Q : CochainComplex (SheafOfModules.scalarModules K S) ℤ)
        (p q : ℤ) (V : Cᵒᵖ) (x : (P.X p).val.obj (f.op.obj V))
        (y : (Q.X q).val.obj (f.op.obj V)),
        ((chain.hom.app (P, Q)).f (p + q)).val.app V
          (coefficientTensorGenerator.{w, c, v} K S
            P Q p q (p + q) rfl (f.op.obj V) x y) =
        coefficientTensorGenerator.{w, c, v} J R
          (F.obj P) (F.obj Q) p q (p + q) rfl V x y := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.monoidalCategory R
  have := SheafOfModules.cochainModulesPreadditive S
  have := SheafOfModules.cochainModulesPreadditive R
  let U := SheafOfModules.pushforward.{max c v w} a.hom
  obtain ⟨e, he, hgen⟩ := SheafOfModules.sectionwiseTensorComparison f R S a
  obtain ⟨chain, hchain⟩ := exists_total_tensor_comparison U e he
  refine ⟨chain, ?_⟩
  intro P Q p q V x y
  change ((chain.hom.app (P, Q)).f (p + q)).val.app V
    ((CochainComplex.ιMapBifunctor P Q (curriedTensor (SheafOfModules.scalarModules K S))
      p q (p + q) rfl).val.app (f.op.obj V)
        (SheafOfModules.ScalarHomOrdinary.pure S (P.X p) (Q.X q) (f.op.obj V) x y)) =
    (CochainComplex.ιMapBifunctor ((U.mapHomologicalComplex (.up ℤ)).obj P)
      ((U.mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor (SheafOfModules.scalarModules J R)) p q (p + q) rfl).val.app V
        (SheafOfModules.ScalarHomOrdinary.pure R (U.obj (P.X p)) (U.obj (Q.X q)) V x y)
  have hh := congrArg (fun h ↦ h.val.app V
    (SheafOfModules.ScalarHomOrdinary.pure S (P.X p) (Q.X q) (f.op.obj V) x y))
    (hchain P Q p q)
  exact hh.trans (congrArg ((CochainComplex.ιMapBifunctor
    ((U.mapHomologicalComplex (.up ℤ)).obj P) ((U.mapHomologicalComplex (.up ℤ)).obj Q)
    (curriedTensor (SheafOfModules.scalarModules J R)) p q (p + q) rfl).val.app V)
    (hgen _ _ V x y))

-- Reuse the small-site composition witness instead of expanding its construction.
set_option linter.defProp false in
@[instance_reducible]
private def cachedCompose {C : Type*} [Category C] (J : GrothendieckTopology C)
    [EssentiallySmall.{u + 1} C] :
    J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  (equivSmallModel.{u + 1} C).hasSheafCompose J
    ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

attribute [local instance 1000001] cachedCompose
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  WeilConjectures.podReindexingCoefficient WeilConjectures.coefficientTotalTensor
  WeilConjectures.coefficientTensorGenerator

set_option allowUnsafeReducibility true in
attribute [local semireducible] WeilConjectures.podReindexingFunctor
  WeilConjectures.podReindexingComplexFunctor WeilConjectures.podReindexingDerivedFunctor
  WeilConjectures.podReindexingDerivedFactors

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

structure ComparisonCoreTensorData {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) where
  tensorChain : ∀ P L : K l E Y s,
    (podReindexingComplexFunctor l E g s).obj ((total l E Y s).obj (P, L)) ≅
      (total l E X s).obj ((podReindexingComplexFunctor l E g s).obj P,
        (podReindexingComplexFunctor l E g s).obj L)
  tensorChain_pure : ∀ (P L : K l E Y s) (p q k : ℤ) (h : p+q=k) (U : X.ProEt)
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (y : (L.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((tensorChain P L).hom.f k).val.app (op U))
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
        (podReindexingRing l E Y s) P L p q k h
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X s) ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj L) p q k h (op U) x y
  tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
    ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
      SX.tensor

/-- The tensor-side fields can be chosen simultaneously.
Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 03EL and 07A4
(blueprint: lem-pod-reindexing-comparison-core-tensor-data).
-/
theorem comparison_core_tensor_data_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    Nonempty (ComparisonCoreTensorData l E g s SX SY TX TY) := by
  classical
  let F := podReindexingComplexFunctor l E g s
  let RX := podReindexingRing l E X s
  let RY := podReindexingRing l E Y s
  obtain ⟨e, he, hi⟩ := (podReindexing_resolution_preservation.{u, 0, 0} l E g s).1
  have hEquiv : (podReindexingFunctor l E g s).IsEquivalence := by
    rw [← he]
    infer_instance
  have hAdd := (podReindexing_resolution_preservation.{u, 0, 0} l E g s).2.1
  let f := proEtaleIsoPostcompose g
  have := sectionwisePostcompose_cocontinuous g
  let ci : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ≅
      (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (podReindexingCoefficient l E g s)
  let a := asIso (inv ci.hom)
  have : (SheafOfModules.pushforward.{u + 1} a.hom).Additive :=
    inferInstanceAs (podReindexingFunctor l E g s).Additive
  have : (SheafOfModules.pushforward.{u + 1} a.hom).IsLeftAdjoint :=
    inferInstanceAs (podReindexingFunctor l E g s).IsLeftAdjoint
  obtain ⟨chain, hpure⟩ :=
    exists_sectionwise_cochain_tensor_comparison.{u + 1, u, u} f RX RY a
  let PY : ObjectProperty (K l E Y s) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := RY)
  let PX : ObjectProperty (K l E X s) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := RX)
  have hkflat : ∀ P, PY P → PX (F.obj P) :=
    (podReindexing_resolution_preservation.{u, 0, 0} l E g s).2.2.2.2.2.2.2.1
  let H : ObjectProperty (HomotopyCategory (podReindexingModules l E Y s) (.up ℤ)) :=
    fun P ↦ PY P.as
  have hres : ∀ P : HomotopyCategory (podReindexingModules l E Y s) (.up ℤ),
      ∃ (L : H.FullSubcategory) (b : L.obj ⟶ P),
        HomotopyCategory.quasiIso (podReindexingModules l E Y s) (.up ℤ) b := by
    intro P
    obtain ⟨L, b, hL, _, hb, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients P.as
    refine ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj L, hL⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map b, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff b).2 hb
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := K l E Y s) (H := HomotopyCategory (podReindexingModules l E Y s) (.up ℤ))
    (D := podReindexingDerived l E Y s) (podReindexingDerived l E X s)
    (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh PY H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (podReindexingDerived l E X s)).mapIso
    (NatIso.prod (isoWhiskerLeft PY.ι (DerivedCategory.quotientCompQhIso _))
      (isoWhiskerLeft PY.ι (DerivedCategory.quotientCompQhIso _))))
  obtain ⟨tensor, _, _⟩ := tensorComparisonDescent
    (podReindexingQ l E Y s) (podReindexingQ l E X s) F
    (podReindexingDerivedFunctor l E g s) (podReindexingDerivedFactors l E g s).hom
    PY PX hkflat ff' (total l E Y s) (total l E X s) SY.tensor SX.tensor
    TY.comparison TX.comparison chain (fun _ _ ↦ inferInstance)
    (fun _ _ _ _ ↦ inferInstance)
  refine ⟨{ tensorChain := fun P L ↦ chain.app (P, L)
            tensorChain_pure := ?_
            tensor := tensor }⟩
  intro P L p q k h U x y
  subst k
  exact hpure P L p q (op U) x y

end WeilConjectures.PodReindexingCoherence
