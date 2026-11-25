/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.InternalScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientProjectionEncoding
import WeilConjectures.SixFunctors.FiniteCtfInternalEtaleRealization
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionObjectConstantProjection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.SmoothPurity.KunnethDerivedTensorTEst
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteScalarConstantModels
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel

/-! # The finite discrete coefficient projection case -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

private theorem projection_app_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {F G : C ⥤ D ⥤ H} (τ : F ⟶ G)
    {K K' : C} (eK : K ≅ K') {M M' : D} (eM : M ≅ M')
    [IsIso ((τ.app K).app M)] : IsIso ((τ.app K').app M') := by
  let t := Functor.whiskerRight τ ((evaluation D H).obj M)
  have ht : IsIso ((τ.app K').app M) :=
    (NatTrans.isIso_app_iff_of_iso t eK).1
      (show IsIso ((τ.app K).app M) from inferInstance)
  exact (NatTrans.isIso_app_iff_of_iso (τ.app K') eM).1 ht

-- Elaborate the derived comparisons without unfolding the resolving constructions.
private theorem ordinary_constant_projection
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (C : Etale.DerivedCategoryModule A X.left)
    (hC : Etale.DerivedCategory.isBoundedConstructible A X.left C)
    (a b : ℤ)
    (hTor : Etale.DerivedCategory.hasTorAmplitudeIn A X.left a b C)
    (P : ModuleCat.{u + 1} A) :
    ordinaryFiniteCoefficientProjectionIsIso A f.left
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X.left).mapDerivedCategory.obj C)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology Y.left) (ModuleCat.{u + 1} A)).obj P)) := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  have : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  have : IsSeparated (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : IsSeparated f.left := .of_comp f.left Y.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : QuasiSeparated f.left := inferInstance
  obtain ⟨c, _, _, hv⟩ := hC.2
  have hc : C.IsGE c := (DerivedCategory.isGE_iff C c).2 fun i hi ↦ hv i (Or.inl hi)
  obtain ⟨n, hn⟩ := hA
  let N := ell ^ (n + 1)
  have hN : (N : A) = 0 := by simp [N, pow_succ, hn]
  have hpos : 1 ≤ N := pow_pos (Fact.out : ell.Prime).pos _
  let D := (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj P)
  have hD : D.IsGE 0 := by dsimp [D]; infer_instance
  have : ((Etale.upperStar (ModuleCat.{u + 1} A) f.left).mapDerivedCategory.obj D).IsGE 0 :=
    Functor.isGE_mapDerivedCategory_obj _ D 0
  have hPull : ((Etale.upperStar (ModuleCat.{u + 1} A) f.left).leftDerivedFunctor.obj
      D).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (((Etale.upperStar (ModuleCat.{u + 1} A) f.left).leftDerivedFunctorIsoMapDerivedCategory).app
        D).symm 0
  have hTensor : ∃ n : ℤ,
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X.left).obj C).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) f.left).leftDerivedFunctor.obj D)).IsGE n := by
    refine ⟨a + 0, (DerivedCategory.isGE_iff _ _).2 ?_⟩
    exact Etale.derivedTensor_isZero_homology_of_torAmplitudeGE A X.left C _ a 0
      (fun M i hi ↦ hTor M i (Or.inl hi))
      ((DerivedCategory.isGE_iff _ _).1 hPull)
  have : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) f.left).app C).app D) :=
    Etale.isIso_rightDerivedLowerStarProjectionMap_constant_of_torsion_object
      A k f.left C N hpos
      (Etale.nsmul_id_eq_zero_of_natCast_eq_zero hN C) P
  have := ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived
    (ModuleCat.{u + 1} A) f.left C D ⟨c, hc⟩ hTensor
  apply (ordinaryFiniteCoefficientProjectionIsIso_iff A f.left _ _).2
  exact projection_app_iso
    (ProEtale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f.left)
    (((comparisonUpperStar (ModuleCat.{u + 1} A) X.left).leftDerivedFunctorIsoMapDerivedCategory
     ).app C)
    ((((comparisonUpperStar (ModuleCat.{u + 1} A) Y.left).leftDerivedFunctorIsoMapDerivedCategory
   ).app D) ≪≫
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y.left).mapDerivedCategorySingleFunctor
        0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((ProEtale.constantSheafCompComparisonUpperStarIso
          (ModuleCat.{u + 1} A) Y.left).app P))

private theorem scalar_projection_isIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (QuotientChange.Modules Λ X))
    (h : finiteCoefficientProjectionIsIso Λ f K (QuotientChange.B a Y)) :
    IsIso (QuotientChange.scalarProjection a f K) := by
  have hProjection := (finiteCoefficientProjectionIsIso_iff Λ f K _).1 h
  have hPost : IsIso ((QuotientChange.F Λ f).map (((derivedTensor Λ X).obj K).map
      (QuotientChange.scalarCoefficientPull a f).hom)) := by infer_instance
  unfold QuotientChange.scalarProjection moduleObjectProjectionMap moduleObjectProjectionData
  unfold QuotientChange.F QuotientChange.L moduleObjectDerivedPushforward
    moduleObjectDerivedPullback derivedTensor at *
  simp only at *
  infer_instance

section PointModels

variable (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

private theorem point_counit_isIso :
    IsIso ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app (coefficient A)) := by
  let J := coherentTopology Profinite.{u}
  have hφ : J.W (A := Ab.{u + 1}) (FiniteDiscreteOrdinary.pointConstants A) :=
    J.W_of_isLocallyBijective (FiniteDiscreteOrdinary.pointConstants A)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map (FiniteDiscreteOrdinary.pointConstants A)) :=
    (J.W_iff _).mp hφ
  have h : IsIso ((constantSheaf J Ab.{u + 1}).map (scalarHom A) ≫
      (constantSheafAdj J Ab.{u + 1} Profinite.isTerminalPUnit).counit.app
        (coefficient A)) := by
    rw [pointScalar_counit A]
    change IsIso ((presheafToSheaf J Ab.{u + 1}).map (FiniteDiscreteOrdinary.pointConstants A) ≫
      (sheafificationAdjunction J Ab.{u + 1}).counit.app (coefficient A))
    infer_instance
  exact (isIso_comp_left_iff _ _).mp h

-- Elaborate the derived comparisons without unfolding the resolving constructions.
private theorem point_module_model
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (coefficient A))
    (hM : IsIso ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app M.X))
    (T : Scheme.{u}) :
    ∃ Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A)),
      Nonempty ((finiteConstantScalarExtension (coefficient A) T).obj Q ≅
        ((upperStarFromPoint T).mapMod (coefficient A)).obj M) := by
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let : F.LaxBraided := constantScalarSheaf_laxBraided.{u}
  let adj : F ⊣ scalarSections.{u} := constantSheafAdj
    (coherentTopology Profinite.{u}) Ab.{u + 1} Profinite.isTerminalPUnit
  let R := scalarRingObj (coefficient A)
  let ε : F.obj R ⟶ coefficient A := adj.counit.app (coefficient A)
  have : IsMonHom ε := adj.isMonHom_counitAlgHom (coefficient A)
  let N := (Mod.comap ε).obj M
  let adjM := adj.mapModAdjunction R
  let Q := ((scalarSections.mapMod (F.obj R)) ⋙
    Mod.comap (adj.unitAlgHom R)).obj N
  have : IsIso (adjM.counit.app N) := by
    have : IsIso ((Mod.forget (F.obj R)).map (adjM.counit.app N)) := by
      change IsIso (adjM.counit.app N).hom
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      exact hM
    exact isIso_of_reflects_iso _ (Mod.forget _)
  let i : (F.mapMod R).obj Q ≅ N := asIso (adjM.counit.app N)
  let H := upperStarFromPoint T
  let φ := scalarCoefficientHom (coefficient A) T
  have : IsIso φ := scalarCoefficient_isIso A T
  let θ := Functor.compAlgHom F H (Iso.refl (scalarConstant T)).hom R
  let ψ : H.obj (F.obj R) ⟶ H.obj (coefficient A) := H.map ε
  have : IsIso ψ := by
    have : IsIso ε := point_counit_isIso A
    dsimp only [ψ]
    infer_instance
  have : NatTrans.IsMonoidal (Iso.refl (scalarConstant T)).hom := by
    change NatTrans.IsMonoidal (𝟙 (F ⋙ H))
    infer_instance
  let j := (Functor.mapModCompExtendScalarsIso F H
    (Iso.refl (scalarConstant T)).hom R).app Q
  have hθ : θ ≫ φ = ψ := by
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp]
    rfl
  let α : Mod.extendScalars (θ ≫ φ) ≅ Mod.extendScalars ψ :=
    (Mod.extendRestrictAdjunction (θ ≫ φ)).leftAdjointUniq
      ((Mod.extendRestrictAdjunction ψ).ofNatIsoRight (Mod.comapCongr hθ).symm)
  refine ⟨Q, ⟨?_⟩⟩
  change (Mod.extendScalars φ).obj (((scalarConstant T).mapMod R).obj Q) ≅ _
  refine (Mod.extendScalars φ).mapIso j.symm ≪≫
    (Mod.extendScalarsComp θ φ).symm.app _ ≪≫ α.app _ ≪≫
    (Mod.extendScalars ψ).mapIso
      ((H.mapMod (F.obj R)).mapIso i ≪≫ (H.mapModComapIso ε).app M) ≪≫ ?_
  exact (Mod.extendScalarsIsoComapInv ψ).app _ ≪≫
    (Mod.comapEquivalenceOfIsIso ψ).unitIso.symm.app ((H.mapMod _).obj M)

end PointModels

section EncodedConstants

variable (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalRing B]

-- Elaborate the derived comparisons without unfolding the resolving constructions.
private theorem encoded_restricted_regular
    (a : coefficient A ⟶ coefficient B) [IsMonHom a]
    (T : Scheme.{u}) (e : Encoding A T) :
    ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A),
      Nonempty (e.fixedDerived.functor.obj (QuotientChange.B a T) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)) := by
  let M := (Mod.comap a).obj (Mod.regular (coefficient B))
  obtain ⟨Q, ⟨i⟩⟩ := point_module_model A M (point_counit_isIso B) T
  let H := upperStarFromPoint T
  let j : (H.mapMod (coefficient A)).obj M ≅ QuotientChange.B₀ a T :=
    (H.mapModComapIso a).app (Mod.regular (coefficient B)) ≪≫
      (Mod.comap (coefficientMap a T)).mapIso (Mod.isoMk (Iso.refl _) (by simp))
  let F := e.ordinary.functor ⋙ e.fixed.functor
  let ec : F.obj (QuotientChange.B₀ a T) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj ((scalarEncoding A).obj Q) :=
    F.mapIso (j.symm ≪≫ i.symm) ≪≫ scalarConstantEncodedIso A T e Q
  refine ⟨(scalarEncoding A).obj Q, ⟨?_⟩⟩
  exact (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ec

end EncodedConstants

section SelfEncoding

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private def coefficientEncoding_self (T : Scheme.{u}) (e : Encoding A T) :
    coefficientEncoding A (Iso.refl (Mon.mk (coefficient A))) T e ≅
      e.fixedDerived.functor :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (Mod.comapCongr (coefficientMap_id (Λ := coefficient A) T) ≪≫ Mod.comapId _) ≪≫
        Functor.mapDerivedCategoryIdIso _) e.fixedDerived.functor ≪≫
    Functor.leftUnitor _

end SelfEncoding

-- The proof combines several equivalences between large derived module categories.
/-- Projection for the restricted regular module of a nonflat finite-ring map.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-direct-image.proof.md, paragraph "Finite rings A to B";
Stacks 0F12 and the relative torsion projection theorem.
(blueprint: lem-s3-finite-discrete-scalar-projection-case).

Proof: give A and B their discrete topologies and choose normalized coefficient
encodings. The constant-sheaf counits at these finite discrete coefficient rings are
isomorphisms. Lift the point constant-sheaf adjunction to module objects and apply its
counit to the restricted regular B-module. Its underlying counit is invertible, so this
module comes from a scalar module. Pull the resulting isomorphism to Y and use the
scalar-constant encoding comparison. Thus its encoded degree-zero complex is a constant
ordinary A-module in degree zero. This construction works for every morphism `a` of
coefficient rings; no sectionwise normalization is needed.

The fixed-interval finite comparison realizes K as the inverse encoding of nu^* J, where
J is bounded constructible etale with the same finite Tor interval. If ell^n annihilates
A, choose N = ell^(n+1). It is positive, annihilates J, and is a unit on Y because char(k)
is a different prime. Apply the relative torsion constant-module projection theorem to
J and the ordinary constant module constructed above. The lower Tor bound makes the
tensor input bounded below, so the canonical etale/pro-etale projection comparison
applies. Exact-functor and constant-sheaf comparisons and naturality transport its
invertibility to the encoded K and restricted regular module. The normalized projection
encoding reflects invertibility of the actual internal projection. Its composite with
Rf_* of the cartesian coefficient-pullback isomorphism is scalarProjection. This uses
no flatness assumption on B and includes zero rings and empty schemes. -/
theorem isIso_scalarProjection_cartesianFinitePointRing
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (a : (⟨cartesianFinitePointRing A⟩ : ScalarSixRing.{u}) ⟶ ⟨cartesianFinitePointRing B⟩)
    (K : DerivedCategory (ModuleRingedComparison.internalModules
      (cartesianFinitePointRing A) X.left))
    (hK : constantModelBoundedConstructible (cartesianFinitePointRing A) X.left K ∧
      _root_.DerivedCategory.finiteTorAmplitude _ K) :
    letI : IsMonHom a.hom.hom := a.hom.isMonHom_hom
    IsIso (QuotientChange.scalarProjection (Λ := cartesianFinitePointRing A)
      (Λ' := cartesianFinitePointRing B) a.hom.hom f.left K) := by
  classical
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := discreteTopology_bot A
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := discreteTopology_bot B
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  let E (T : Scheme.{u}) : Encoding A T := Classical.choice (encoding_exists A T)
  obtain ⟨P, ⟨eB⟩⟩ := encoded_restricted_regular A B a.hom.hom Y.left (E Y.left)
  obtain ⟨lo, hi, hTor⟩ := hK.2
  let lo' := min lo hi
  have hTor' : _root_.DerivedCategory.torAmplitudeIn _ lo' hi K :=
    hTor.mono (min_le_left _ _) le_rfl
  obtain ⟨hreal, _⟩ := finiteCtfInternalEtaleRealization ell (ringChar k) k
    ((Fact.out : (ringChar k).Prime).pos) Fact.out A E
  obtain ⟨eT, ⟨heT⟩⟩ := hreal X lo' hi (min_le_right _ _)
  let L := eT.inverse.obj ⟨K, hK.1, hTor'⟩
  let ec : (internalEtaleRealization A X.left (E X.left)).obj L.obj ≅ K :=
    (heT.app L).symm ≪≫ (ObjectProperty.ι _).mapIso
      (eT.counitIso.app ⟨K, hK.1, hTor'⟩)
  let eK : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
      X.left).mapDerivedCategory.obj L.obj ≅ (E X.left).fixedDerived.functor.obj K :=
    ((E X.left).fixedDerived.counitIso.app _).symm ≪≫
      (E X.left).fixedDerived.functor.mapIso ec
  have hA' : ∃ n : ℕ, (ell ^ n : ULift.{u + 1} A) = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n, ?_⟩
    apply ULift.down_injective
    change (ell ^ n : A) = 0
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hn 1
  have hOrd := ordinary_constant_projection ell k f (ULift.{u + 1} A) hA'
    L.obj L.property.1 lo' hi L.property.2 P
  have hEncoded := ordinaryFiniteCoefficientProjectionIsIso_of_iso
    (ULift.{u + 1} A) f.left
    (eK ≪≫ (coefficientEncoding_self A X.left (E X.left)).symm.app K)
    (eB.symm ≪≫ (coefficientEncoding_self A Y.left (E Y.left)).symm.app
      (QuotientChange.B a.hom.hom Y.left)) hOrd
  have hProj := (finiteCoefficientProjectionEncoding A (Iso.refl _) E f.left K
    (QuotientChange.B a.hom.hom Y.left)).2 hEncoded
  exact scalar_projection_isIso (Λ := coefficient A) (Λ' := coefficient B)
    a.hom.hom f.left K hProj

end AlgebraicGeometry.ProEtale.CondensedRing
