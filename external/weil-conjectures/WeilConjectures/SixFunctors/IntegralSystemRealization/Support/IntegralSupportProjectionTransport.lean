/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralProperFiniteProjection
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenFiniteEvaluation

/-! # Projection transport for proper/open realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  WeilConjectures.scalarReductionDerivedExtension WeilConjectures.scalarReductionDerivedRestriction
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.IntegralSystemRealization.RealizationModel.push
  WeilConjectures.IntegralSystemRealization.RealizationModel.openReduction
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem reconstruction_finite_map
    {A C D : Type*} [Category A] [Category C] [Category D]
    {R : A ⥤ C} {L : C ⥤ A} (adj : R ⊣ L)
    {F : A ⥤ D} {V : C ⥤ D} (e : R ⋙ V ≅ F)
    {M : C} {H : A} (r : M ⟶ R.obj H) [IsIso (adj.unit.app H)] :
    F.map (L.map r ≫ inv (adj.unit.app H)) =
      e.inv.app (L.obj M) ≫ V.map (adj.counit.app M) ≫ V.map r ≫ e.hom.app H := by
  have hε : R.map (inv (adj.unit.app H)) = adj.counit.app (R.obj H) := by
    apply (cancel_epi (R.map (adj.unit.app H))).1
    rw [← R.map_comp, IsIso.hom_inv_id, R.map_id]
    exact (adj.left_triangle_components H).symm
  have h : R.map (L.map r ≫ inv (adj.unit.app H)) = adj.counit.app M ≫ r := by
    rw [R.map_comp, hε]
    exact adj.counit.naturality r
  calc
    F.map (L.map r ≫ inv (adj.unit.app H)) =
        e.inv.app (L.obj M) ≫ V.map (R.map (L.map r ≫ inv (adj.unit.app H))) ≫
          e.hom.app H := by
      have hn := e.hom.naturality (L.map r ≫ inv (adj.unit.app H))
      dsimp only [Functor.comp_map] at hn
      simpa only [Category.assoc, e.inv_hom_id_app_assoc, Functor.id_obj]
        using (congrArg (fun k ↦ e.inv.app (L.obj M) ≫ k) hn).symm
    _ = _ := by rw [h, V.map_comp, Category.assoc]

private theorem finite_coordinates_paste
    {C D : Type*} [Category C] [Category D] {P Q : C ⥤ D} (e : P ≅ Q)
    {A : D} {Z Z' Z₁ Z₂ Z₃ : C} (a : A ⟶ P.obj Z) (t : Z ≅ Z')
    (b : Z ⟶ Z₁) (c : Z₁ ⟶ Z₂) (d : Z₂ ⟶ Z₃) :
    a ≫ P.map b ≫ P.map c ≫ e.hom.app Z₂ ≫ Q.map d =
      (a ≫ e.hom.app Z ≫ Q.map t.hom) ≫ Q.map (t.inv ≫ b ≫ c ≫ d) := by
  simp only [Q.map_comp, Category.assoc]
  rw [← Q.map_comp_assoc t.hom t.inv, t.hom_inv_id, Q.map_id, Category.id_comp]
  rw [e.hom.naturality_assoc c, e.hom.naturality_assoc b]

private theorem scalar_projection_paste
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {R : D ⥤ C}
    (adj : F ⊣ R) {A B : C} {U T : D} (g : A ⟶ B)
    (z : F.obj B ⟶ T) (μ : F.obj A ⟶ U) (v : U ⟶ T) (p : A ⟶ R.obj U)
    (hp : adj.homEquiv A U μ = p) (he : F.map g ≫ z = μ ≫ v) :
    g ≫ adj.homEquiv B T z = p ≫ R.map v := by
  rw [← adj.homEquiv_naturality_left, he, adj.homEquiv_naturality_right, hp]

private theorem support_finite_factorization
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Integral l E X) (n : ℕ) :
    (PurCompactSupport.finiteReductionIso l E Y n).inv.app
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K) ≫
      (PurCompactSupport.comparison
        (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K ≫
      (PurCompactSupport.finiteImageIso l E n c).hom.app
        ((pbcDerivedExtend
          (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K) ≫
      (sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((PurCompactSupport.finiteReductionIso l E X n).hom.app K) =
    (properFiniteReduction l E c.g n).app ((ringedOpen l E c.i).obj K) ≫
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing l E (n + 1))).map
          ((openFiniteReduction l E c.i n).app K) := by
  let := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).1
  let := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  let := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let := (proEtaleConstantModuleDirectImage_additive_leftExact c.g
    (Padic.coefficientExtensionRing l E (n + 1))).1
  rw [PurCompactSupport.comparison_factorization]
  simpa only [properFiniteReduction, openFiniteReduction, PurCompactSupport.finiteImageIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.comp_map, sfAmbientCompactSupportCandidate,
    proEtaleRingDerivedDirectImage, proEtaleConstantDerivedDirectImage,
    PurCompactSupport.image, PurCompactSupport.push, PurCompactSupport.reduction,
    ringedOpen, ringedPush, Functor.comp_obj,
    Iso.app_hom, Iso.app_inv, Category.assoc] using
    finite_coordinates_paste
      (Functor.rightDerivedFunctorNatIso
        (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n c.g)))
      ((PurCompactSupport.finiteReductionIso l E Y n).inv.app
          ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K) ≫
        (PurCompactSupport.properComparison
          (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) c.g).app
            ((ringedOpen l E c.i).obj K))
      ((PurCompactSupport.finiteReductionIso l E c.Z n).app ((ringedOpen l E c.i).obj K))
      ((PurCompactSupport.openComparison
        (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) c.i).app K)
      ((Functor.mapDerivedCategoryNatIso (PurCompactSupport.finiteOpenIso l E n c.i)).hom.app
        ((pbcDerivedExtend
          (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K))
      ((sfIntrinsicExtensionByZero c.i
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
          ((PurCompactSupport.finiteReductionIso l E X n).hom.app K))

/-- The actual total-limit projection commutes with the normalized proper/open
comparison, before identifying its integral image with the constructible action.
Source: Stacks 07A7, 0941 and 0D6E; fix-prop-coherence.proof.md, preservation of
adjunction units and counits; primitive support realization Step 2
(blueprint: lem-sf-integral-support-projection-transport).

Proof: start with the ordinary sectionwise direct-image/limit comparison in
model.ordinary. Its projections are exactly the direct-image evaluation maps.
Its adjoint conjugate gives reductionPull; the whole K-flat model equation of model
identifies that conjugate with the derived reduction comparison, before evaluation.
Derive the ordinary projection identity using K-injective resolutions and the
universal right-derived comparison. Conjugation then gives the proper projection
identity for model.push. Apply it to the open system of reduction K. The inverse
open-adjunction mate defining model.openReduction and the transpose equation of
o.openEvaluation give the open projection identity. The scalar-adjunction triangle
identities identify its completed-to-finite map with PurCompactSupport.openComparison.
Compose the proper and open identities, in that order; the reduction model contributes
reductionEvaluation on the input. Naturality with respect to the actual open-output
reconstruction unit cancels that unit against its specified inverse. The remaining
finite scalar-adjunction mate is precisely finiteReductionIso inverse, the geometric
proper/open comparison, finiteImageIso, and finiteReductionIso on the input. This
is the displayed equation. This uses only invertibility of the specified unit;
no constructibility, faithfulness of evaluation, or uniqueness of a triangulated
limit cone is invoked. It applies equally to zero objects and empty opens. -/
theorem integralSupportProjectionTransport (o : Operations l E)
    (model : RealizationModel l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Integral l E X)
    (hunit : IsIso ((calculus l E c.Z).adjunction.unit.app ((ringedOpen l E c.i).obj K)))
    (n : ℕ) :
    (model.push l E c.g).hom.app
        ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K)) ≫
      (ringedPush l E c.g).map
        ((coefficientSequenceLimit l E c.Z).map ((model.openReduction l E c.i).app K) ≫
          @inv _ _ _ _ ((calculus l E c.Z).adjunction.unit.app
            ((ringedOpen l E c.i).obj K)) hunit) ≫
      ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _)
        ((PurCompactSupport.finiteReductionIso l E Y n).inv.app
            ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K) ≫
          (PurCompactSupport.comparison
            (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K ≫
          (PurCompactSupport.finiteImageIso l E n c).hom.app
            ((pbcDerivedExtend
              (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K) ≫
          (sfAmbientCompactSupportCandidate
            (Padic.coefficientExtensionRing l E (n + 1)) c).map
              ((PurCompactSupport.finiteReductionIso l E X n).hom.app K)) =
      (coefficientSequenceProjection l E Y n).app
          ((Operations.push l E o c.g).obj
            ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K))) ≫
        (scalarReductionDerivedRestriction l E Y n).map
          ((supportEvaluation l E o c n).hom.app ((calculus l E X).reduction.obj K) ≫
            (sfAmbientCompactSupportCandidate
              (Padic.coefficientExtensionRing l E (n + 1)) c).map
                (((calculus l E X).reductionEvaluation n).hom.app K)) := by
  let := hunit
  let J := Operations.shriek l E o c.i
  let P := Operations.push l E o c.g
  let B := ringedOpen l E c.i
  let Q := ringedPush l E c.g
  let M := J.obj ((calculus l E X).reduction.obj K)
  let H := B.obj K
  let L := coefficientSequenceLimit l E c.Z
  let F := scalarReductionDerivedExtension l E Y n
  let G := scalarReductionDerivedExtension l E c.Z n
  let R := proEtaleConstantDerivedDirectImage c.g
    (Padic.coefficientExtensionRing l E (n + 1))
  let V := (sfIntrinsicExtensionByZero c.i
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  let a := (model.push l E c.g).hom.app M
  let r := (model.openReduction l E c.i).app K
  let h := L.map r ≫ inv ((calculus l E c.Z).adjunction.unit.app H)
  let μ := ((calculus l E c.Z).reductionEvaluation n).inv.app (L.obj M) ≫
    (coefficientSequenceDerivedEvaluation l E c.Z n).map
      ((calculus l E c.Z).adjunction.counit.app M)
  let ν := ((calculus l E Y).reductionEvaluation n).inv.app
      ((coefficientSequenceLimit l E Y).obj (P.obj M)) ≫
    (coefficientSequenceDerivedEvaluation l E Y n).map
      ((calculus l E Y).adjunction.counit.app (P.obj M))
  let v := (supportEvaluation l E o c n).hom.app ((calculus l E X).reduction.obj K) ≫
    (sfAmbientCompactSupportCandidate
      (Padic.coefficientExtensionRing l E (n + 1)) c).map
        (((calculus l E X).reductionEvaluation n).hom.app K)
  let z := (properFiniteReduction l E c.g n).app H ≫
    R.map ((openFiniteReduction l E c.i n).app K)
  have hG : G.map h = μ ≫
      (coefficientSequenceDerivedEvaluation l E c.Z n).map r ≫
        ((calculus l E c.Z).reductionEvaluation n).hom.app H := by
    simpa only [μ, G, h, L, M, H, B, J, ringedOpen, Functor.comp_obj,
      coefficientFiniteDerivedExtension,
      Functor.id_obj, Category.assoc] using
      reconstruction_finite_map (calculus l E c.Z).adjunction
        ((calculus l E c.Z).reductionEvaluation n) r
  have hopen : G.map h ≫ (openFiniteReduction l E c.i n).app K =
      μ ≫ ((o.openEvaluation c.i).evaluation n).hom.app
          ((calculus l E X).reduction.obj K) ≫
        V.map (((calculus l E X).reductionEvaluation n).hom.app K) := by
    rw [hG]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ μ ≫ t) (integralOpenFiniteEvaluation l E o model c.i K n)
  have hp : F.map a ≫ (properFiniteReduction l E c.g n).app (L.obj M) ≫ R.map μ =
      ν ≫ ((o.evaluation c.g).evaluation n).hom.app M := by
    simpa only [a, μ, ν, Category.assoc] using
      integralProperFiniteProjection l E o model c.g M n
  have hfinite : F.map (a ≫ Q.map h) ≫ z = ν ≫ v := by
    calc
      F.map (a ≫ Q.map h) ≫ z =
          F.map a ≫ (properFiniteReduction l E c.g n).app (L.obj M) ≫
            R.map (G.map h ≫ (openFiniteReduction l E c.i n).app K) := by
        simpa only [Functor.comp_map, Functor.map_comp, Functor.id_obj,
          F, Q, G, R, z, M, Functor.comp_obj, Category.assoc] using
          congrArg (fun t ↦ F.map a ≫ t ≫
            R.map ((openFiniteReduction l E c.i n).app K))
              ((properFiniteReduction l E c.g n).naturality h)
      _ = F.map a ≫ (properFiniteReduction l E c.g n).app (L.obj M) ≫ R.map μ ≫
          R.map (((o.openEvaluation c.i).evaluation n).hom.app
            ((calculus l E X).reduction.obj K)) ≫
          R.map (V.map (((calculus l E X).reductionEvaluation n).hom.app K)) := by
        rw [hopen]
        simp only [Functor.map_comp]
      _ = ν ≫ v := by
        have hh := congrArg (fun t ↦ t ≫
          R.map (((o.openEvaluation c.i).evaluation n).hom.app
            ((calculus l E X).reduction.obj K)) ≫
          R.map (V.map (((calculus l E X).reductionEvaluation n).hom.app K))) hp
        simpa only [v, M, J, R, V, sfAmbientCompactSupportCandidate,
          Functor.comp_map, supportEvaluation, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
          Functor.associator_hom_app, Functor.associator_inv_app,
          Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
          Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Category.id_comp, Category.comp_id, Category.assoc] using hh
  have hpν :
      ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _) ν =
        (coefficientSequenceProjection l E Y n).app (P.obj M) := by
    exact (calculus l E Y).counit_projection (P.obj M) n
  have ht := scalar_projection_paste
    (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
    (a ≫ Q.map h) z ν v _ hpν hfinite
  change a ≫ Q.map h ≫ _ = _
  have hz := support_finite_factorization l E c K n
  have hh := congrArg (fun t ↦ a ≫ Q.map h ≫
    ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _) t) hz
  exact hh.trans (by
    simpa only [z, H, B, R, v, P, M, J, sfAmbientCompactSupportCandidate,
      Functor.comp_obj, Functor.comp_map, Functor.id_obj, Category.assoc] using ht)

end WeilConjectures.IntegralSystemRealization
