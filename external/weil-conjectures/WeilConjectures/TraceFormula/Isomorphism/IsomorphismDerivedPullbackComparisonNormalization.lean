/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.TraceFormula.Isomorphism.IsomorphismRoosUnitCancellation
import WeilConjectures.TraceFormula.Supporting.StrictQuotientCompletionUnit

/-!
# The specified inverse-image comparison is the completion unit

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
  sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md, clauses (2)--(3)
  (blueprint: lem-weil-isomorphism-derived-pullback-comparison-normalization).

For a scheme isomorphism `g : X ⟶ Y`, the specified comparison
`inverseImagePullbackComparisonDerived` from exact inverse image `G` to completed
integral pullback `P_g` is related to `G` of the actual completion unit
`S.adjunction.unit` of the canonical reduction/strict-system-limit calculus `S`
by a natural isomorphism `θ : P_g ≅ G ∘ completion`.  For a derived-complete object
the comparison is invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit

section Model
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private def comparisonFromModel (S : CoefficientDerivedSystemCalculus l E W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (D : CompletionUnit.DerivedModel l E W S M) :
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q := by
  refine D.roos.symm ≪≫ NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro A B f
  simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.comp_map]
  apply congrArg DerivedCategory.Q.map
  unfold roosF roosConeFunctor integralOperationsRoosFunctor integralOperationsRoosMap
  dsimp only [Functor.comp_map]
  apply congrArg ((shiftFunctor _ (-1 : ℤ)).map)
  ext i : 1
  rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc_f _ _ _ _ i (i + 1) rfl]
  rw [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f _ _ _ i (i + 1) rfl]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.inr]
  simp only [CochainComplex.HomComplex.Cocycle.mk_coe,
    CochainComplex.HomComplex.Cochain.mk_v, Int.reduceNeg,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.ofHoms_v, HomologicalComplex.comp_f,
    HomologicalComplex.homotopyCofiber.inr_f, Pi.zero_apply, Arrow.homMk_left,
    add_zero, zero_add, Arrow.mk_right, Arrow.homMk_right]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ _ _ rfl]
  rfl

private def roosModel (S : CoefficientDerivedSystemCalculus l E W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (D : CompletionUnit.DerivedModel l E W S M) : IntegralComparisonRoosModel l E W where
  comparison := comparisonFromModel l E W S M D
  computes I := by
    intro _
    have hi : integralComparisonLimitToRoos l E W I =
        D.towerLimitComparison.hom.app I ≫ roosι I := by
      symm
      apply (integralComparisonLimitToRoos_existsUnique l E W I).unique
        _ ((integralComparisonLimitToRoos_existsUnique l E W I).exists.choose_spec)
      constructor
      · intro n
        have hh : roosι I ≫ CochainComplex.mappingCocone.fst
            (scalarRoosBoundary I.asFunctor) ≫
            Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n =
            limit.π I.asFunctor (op n) := by
          exact roosι_eval I n
        rw [Category.assoc, hh]
        ext p : 1
        exact D.towerLimitComparison_projection I n p
      · intro i j h
        have hh : (roosι I).f i ≫
            (CochainComplex.mappingCocone.snd (scalarRoosBoundary I.asFunctor)).v i j h = 0 := by
          change (roosι I).f i ≫
            (CochainComplex.mappingCocone.snd (roosU I)).v i j h = 0
          simp [roosι, roosLift]
        rw [HomologicalComplex.comp_f, Category.assoc, hh, comp_zero]
    change D.roos.inv.app I ≫ 𝟙 _ = _
    rw [Category.comp_id, hi, Functor.map_comp]
    apply (cancel_mono (D.roos.hom.app I ≫
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).rightDerivedFunctorObjQIso I).hom)).1
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc (DerivedCategory.Q.map (roosι I)), D.roos_normalization,
      D.limitUnit_normalization]
    simp only [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

attribute [local irreducible] comparisonFromModel roosModel
end Model

/-- The specified inverse-image comparison is normalized by the actual completion unit.
Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
  sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md, clauses (2)--(3)
  (blueprint: lem-weil-isomorphism-derived-pullback-comparison-normalization).

The hypotheses bind the prime, the finite coefficient extension, the scheme
isomorphism and invertibility of `l` on both schemes.  `S` with `hS` is the canonical
calculus of `coefficientDerivedSystemEvaluationCalculus`: `S.reduction` is the
simultaneous derived reduction, left adjoint to the specified total limit
`coefficientSequenceLimit`, and `S.adjunction.unit` is the actual unit `u`.  The
conclusion gives one family `θ` of isomorphisms `P_g M ≅ G (L (R M))` with
`κ_M ≫ θ_M = G(u_M)` for every ambient `M` (an equality of whole derived morphisms),
naturality of `θ` in every derived morphism, and, for the derived-complete `N`, a
two-sided inverse `κinv` of `κ_N` with `κinv ≫ G(u_N) = θ_N`.

Proof:
1. Choose compatible canonical ordinary and derived completion models and construct
   the normalized Roos model from the inverse of the derived model's comparison.
2. Apply multiplication-cone descent to obtain j, eta, rho and the descended natural
   isomorphism Theta, with their generator, coordinate and representative equations.
3. On a good representative, identify the actual unit followed by rho with the
   strict quotient augmentation. The ordinary tensor-unit section formula fixes
   its first coordinate; both shifted coordinates are zero.
4. Multiplication cancels each finite pullback generator. The two cone coordinates
   identify the specified comparison followed by H(j) and eta inverse with the
   inverse image of this augmentation. Localize this strict equality.
5. Cancel the representative rho comparison to obtain the normalization on good
   complexes. Naturality transports it through the very K-flat resolution used by
   the specified derived comparison, proving equality for every ambient object.
6. Uniqueness of left adjoints transports the identity from the chosen canonical
   calculus to the given S, preserving the actual adjunction unit.
7. The actual reconstruction-maps theorem makes the unit invertible on each
   derived-complete N. Compose Theta with its inverse and cancel to obtain both
   inverse identities and the required normalized inverse equation. -/
theorem isomorphismDerivedPullbackComparisonNormalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{t}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : CoefficientDerivedSystemCalculus l E Y)
    (hS : Nonempty (CoefficientDerivedSystemCoherence l E Y S))
    (N :
      DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
        (integralTowerModules.{t, u} l E Y))
    (hN : IsDerivedCompleteUnrestricted.{t, u} l E Y N) :
    ∃ θ : ∀ M :
      DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
        (integralTowerModules.{t, u} l E Y),
      (integralDerivedPullback l E g).obj M ≅
        (inverseImageIntegralDerived l E g).obj
          ((S.reduction ⋙ coefficientSequenceLimit l E Y).obj M),
      (∀ M :
        DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
          (integralTowerModules.{t, u} l E Y),
        inverseImagePullbackComparisonDerived l E g hX hY M ≫
            (θ M).hom =
          (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app M)) ∧
      (∀ (M M' :
        DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
          (integralTowerModules.{t, u} l E Y))
        (f : M ⟶ M'),
        (integralDerivedPullback l E g).map f ≫ (θ M').hom =
          (θ M).hom ≫
            (inverseImageIntegralDerived l E g).map
              ((S.reduction ⋙ coefficientSequenceLimit l E Y).map f)) ∧
      ∃ κinv : (integralDerivedPullback l E g).obj N ⟶
          (inverseImageIntegralDerived l E g).obj N,
        κinv ≫ inverseImagePullbackComparisonDerived l E g hX hY N =
            𝟙 _ ∧
          inverseImagePullbackComparisonDerived l E g hX hY N ≫ κinv =
            𝟙 _ ∧
          κinv ≫ (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app N) =
            (θ N).hom := by
  obtain ⟨_coherence⟩ := hS
  let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    ((map_natCast (Y.residue y).hom l) ▸ ((hY y).map (Y.residue y).hom)).invertible
  obtain ⟨S₀, hS₀, M, ⟨D⟩⟩ := CompletionUnit.canonicalModels l E Y
  let r := roosModel l E Y S₀ M D
  obtain ⟨_, _, _, _, j, eta, rho, Theta, hj, _, _, heta₁, heta₂, hrho, hTheta, _⟩ :=
    isomorphismMultiplicationConeDescent l E g hX hY S₀ r
  let G := inverseImageIntegralDerived l E g
  let F := inverseImageIntegralModules l E g
  have hrep (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      F.mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj) ≫
          (integralDerivedPullbackComparison l E g).inv.app P ≫
          Theta.hom.app (DerivedCategory.Q.obj P.obj) =
        G.map (S₀.adjunction.unit.app (DerivedCategory.Q.obj P.obj)) := by
    apply (Iso.cancel_iso_hom_right _ _ (G.mapIso (rho.app P))).1
    apply (Iso.cancel_iso_hom_right _ _ (F.mapDerivedCategoryFactors.app
      (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj)))).1
    simp only [Category.assoc]
    dsimp only [CategoryTheory.Functor.mapIso_hom, Iso.app]
    erw [hTheta P]
    simp only [Iso.inv_hom_id_app_assoc]
    have hu := strictQuotientCompletionUnit l E Y S₀ M D r rho (fun I ↦ by
      dsimp only [r, roosModel, comparisonFromModel, Iso.trans_hom, NatTrans.comp_app,
        Iso.symm_hom, NatIso.ofComponents_hom_app, Iso.refl_hom]
      exact Category.comp_id _) hrho P
    have hc : F.mapDerivedCategoryFactors.hom.app P.obj ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj ≫
          integralOperationsRoosFunctor.map (j.hom.app P) ≫ eta.inv.app P) =
      G.map (S₀.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ rho.hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app
          (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj)) := by
      have hcancel : inverseImageRoosComparisonComplex l E g P.obj ≫
          integralOperationsRoosFunctor.map (j.hom.app P) ≫ eta.inv.app P =
        (trfInverseImageComplex l E g).map
          (trfStrictQuotientConeAugmentation l E Y P.obj) := by
        with_unfolding_all
          exact isomorphismRoosUnitCancellation l E g P.obj (j.hom.app P)
            (eta.app P) (hj P) (heta₁ P) (heta₂ P)
      have hchain := congrArg (fun f ↦
        F.mapDerivedCategoryFactors.hom.app P.obj ≫ DerivedCategory.Q.map f) hcancel
      have hn := F.mapDerivedCategoryFactors.hom.naturality
        (trfStrictQuotientConeAugmentation l E Y P.obj)
      dsimp only [CategoryTheory.Functor.comp_map] at hn
      have hunit := congrArg (fun f ↦ G.map f ≫
        F.mapDerivedCategoryFactors.hom.app
          (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj))) hu
      with_unfolding_all exact hchain.trans (hn.symm.trans hunit.symm)
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using hc
  have hres (K : CochainComplex (integralTowerModules l E Y) ℤ)
      (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (q : P.obj ⟶ K) [QuasiIso q] :
      inverseImagePullbackComparison l E g hX hY K P q ≫
          Theta.hom.app (DerivedCategory.Q.obj K) =
        G.map (S₀.adjunction.unit.app (DerivedCategory.Q.obj K)) := by
    apply (cancel_epi (G.map (DerivedCategory.Q.map q))).1
    unfold inverseImagePullbackComparison
    simp only [Category.assoc]
    have hn := F.mapDerivedCategoryFactors.hom.naturality q
    dsimp only [CategoryTheory.Functor.comp_map] at hn
    rw [reassoc_of% hn]
    erw [IsIso.hom_inv_id_assoc]
    erw [Theta.hom.naturality (DerivedCategory.Q.map q)]
    dsimp only [CategoryTheory.Functor.comp_map]
    erw [reassoc_of% (hrep P)]
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg G.map (S₀.adjunction.unit.naturality (DerivedCategory.Q.map q)).symm
  have hnormal (K : DerivedCategory (integralTowerModules l E Y)) :
      inverseImagePullbackComparisonDerived l E g hX hY K ≫ Theta.hom.app K =
        G.map (S₀.adjunction.unit.app K) := by
    unfold inverseImagePullbackComparisonDerived
    extract_lets K₀ e hp P q hq
    let P' : (integralOperationsGoodComplex l E Y).FullSubcategory :=
      ⟨P, hq.1, fun i ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (P.X i)).symm (hq.2.1 i)⟩
    let : QuasiIso q := hq.2.2.1
    change (G.map e.inv ≫ inverseImagePullbackComparison l E g hX hY K₀ P' q ≫
      (integralDerivedPullback l E g).map e.hom) ≫ Theta.hom.app K = _
    simp only [Category.assoc]
    erw [Theta.hom.naturality e.hom]
    dsimp only [CategoryTheory.Functor.comp_map]
    erw [reassoc_of% (hres K₀ P' q)]
    rw [← G.map_comp, ← G.map_comp]
    have hn := S₀.adjunction.unit.naturality e.hom
    dsimp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hn
    rw [← hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let Theta' := Theta ≪≫ CategoryTheory.Functor.isoWhiskerRight
    (CategoryTheory.Functor.isoWhiskerRight (S₀.adjunction.leftAdjointUniq S.adjunction)
      (coefficientSequenceLimit l E Y)) G
  have hnormal' (K : DerivedCategory (integralTowerModules l E Y)) :
      inverseImagePullbackComparisonDerived l E g hX hY K ≫ Theta'.hom.app K =
        G.map (S.adjunction.unit.app K) := by
    change _ ≫ Theta.hom.app K ≫ G.map
      ((coefficientSequenceLimit l E Y).map
        ((S₀.adjunction.leftAdjointUniq S.adjunction).hom.app K)) = _
    rw [← Category.assoc, hnormal, ← G.map_comp,
      Adjunction.unit_leftAdjointUniq_hom_app]
  refine ⟨fun K ↦ Theta'.app K, hnormal', ?_, ?_⟩
  · intro K K' f
    exact Theta'.hom.naturality f
  · have hl : IsUnit (l : Γ(Y, ⊤)) := by
      apply Y.toRingedSpace.isUnit_of_isUnit_germ
      intro y hy
      simpa using hY y
    let := (purNormalizedReconstruction l E Y hl S).2 N hN
    let u := G.map (S.adjunction.unit.app N)
    refine ⟨Theta'.hom.app N ≫ inv u, ?_, ?_, ?_⟩
    · apply (Iso.cancel_iso_hom_right _ _ (Theta'.app N)).1
      dsimp only [Iso.app]
      simp only [Category.assoc, hnormal' N, Category.id_comp]
      change Theta'.hom.app N ≫ inv u ≫ u = Theta'.hom.app N
      rw [IsIso.inv_hom_id, Category.comp_id]
    · rw [← Category.assoc, hnormal' N]
      exact IsIso.hom_inv_id u
    · change (Theta'.hom.app N ≫ inv u) ≫ u = Theta'.hom.app N
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end WeilConjectures
