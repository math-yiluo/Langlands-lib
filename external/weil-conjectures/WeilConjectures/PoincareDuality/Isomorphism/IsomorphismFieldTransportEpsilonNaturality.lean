/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportClauses
import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent

/-! # A finite-stage compatibility for normalized isomorphism transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.privateModule false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients (inclusion)

attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
  ObjectProperty.FullSubcategory.category

private theorem inverse_square_transport
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (F : A ⥤ B) (G : B ⥤ A) (F' : C ⥤ D) (G' : D ⥤ C)
    (U U' : A ⥤ C) (V V' : B ⥤ D) (i : U ≅ U') (j : V ≅ V')
    (a : F ⋙ V' ≅ U' ⋙ F') (b : G ⋙ U' ≅ V' ⋙ G')
    (ε : F ⋙ G ≅ 𝟭 A) (ε' : F' ⋙ G' ≅ 𝟭 C)
    (h : ∀ K, b.hom.app (F.obj K) ≫ G'.map (a.hom.app K) ≫
      ε'.hom.app (U'.obj K) = U'.map (ε.hom.app K)) (K : A) :
    (Functor.isoWhiskerLeft G i ≪≫ b ≪≫ Functor.isoWhiskerRight j.symm G').hom.app
        (F.obj K) ≫
      G'.map ((Functor.isoWhiskerLeft F j ≪≫ a ≪≫
        Functor.isoWhiskerRight i.symm F').hom.app K) ≫ ε'.hom.app (U.obj K) =
      U.map (ε.hom.app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := ε'.hom.naturality (i.inv.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, reassoc_of% (h K), ← i.hom.naturality_assoc]
  simp

/-- Own-stage epsilon components are natural on common-stage quotient arrows.
Source: current blueprint sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, inverse automorphism paragraph;
step 2 of the common-stage transport argument.
(blueprint: lem-pod-isomorphism-field-transport-epsilon-naturality).

Proof: represent f over one finite field L containing both endpoint fields. The
published representative formula for each of the two pullbacks conjugates the
finite-stage image by the rational scalar comparisons. The scalar inverse law hS
at each endpoint rewrites its own-stage epsilon after passage to L as the composite
of these two scalar comparisons and epsilon at L. Substitute these two equations
in the desired square. Finite-stage naturality of (S L).rationalEpsilon at the
representative of f identifies the middle terms; the adjacent inverse scalar
comparisons cancel. Include the resulting equality from L into the quotient.
The common-stage functor's representative independence makes it an equality for
f itself. The heterogeneous component formula he merely transports the endpoints
along the published object formulas, so the same equation holds for the supplied
e. No inverse family, coherent shift, or triangle preservation is assumed. -/
theorem isomorphismFieldTransportEpsilonNaturality
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY)
    (hS : ∀ (E L : Index l Ω) (h : E ≤ L),
      isomorphismFieldTransportRationalScalarLaw l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) g hX hY (S E) (S L))
    (e : ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      (commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω (inv g)).obj P ≅ P)
    (he : ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      HEq (e P).hom
        ((inclusion (Y := Y) P.stage).map ((S P.stage).rationalEpsilon.hom.app P.obj))) :
    ∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y) (f : P ⟶ Q),
      (commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω (inv g)).map f ≫
        (e Q).hom = (e P).hom ≫ f := by
  obtain ⟨hcoh, hM⟩ := commonStagePullbackNormalizedDescent l Ω g
  obtain ⟨hcoh', hN⟩ := commonStagePullbackNormalizedDescent l Ω (inv g)
  let U := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y
  let V := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X
  let M : U.Morphism V :=
    ⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) g,
      commonStagePullbackTransition l Ω g, hcoh⟩
  let N : V.Morphism U :=
    ⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) (inv g),
      commonStagePullbackTransition l Ω (inv g), hcoh'⟩
  have square {E L : Index l Ω} (h : E ≤ L)
      (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
      (U.T h).map ((S E).rationalEpsilon.hom.app K) =
        ((M.comp N).β h).hom.app K ≫
          (S L).rationalEpsilon.hom.app ((U.T h).obj K) := by
    rw [StageSystem.Morphism.comp_β_hom_app]
    simpa only [M, N, commonStagePullbackTransition, Category.assoc] using (inverse_square_transport
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) g)
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) (inv g))
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) g)
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) (inv g))
      (U.T h) (GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h)
      (V.T h) (GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h)
      (operationStageTransitionIso l Ω Y E L h)
      (operationStageTransitionIso l Ω X E L h)
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g)
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (inv g))
      (S E).rationalEpsilon (S L).rationalEpsilon (hS E L h) K).symm
  let τ : StageSystem.Morphism.Hom (M.comp N) (StageSystem.Morphism.id U) :=
    { τ := fun E ↦ (S E).rationalEpsilon.hom
      comm := by
        intro E L h K
        change (U.T h).map ((S E).rationalEpsilon.hom.app K) ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact square h K }
  have desc : ∃ ε : commonStageDerivedPullback l Ω g ⋙
        commonStageDerivedPullback l Ω (inv g) ≅
          𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω Y),
      ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
        HEq (ε.hom.app P)
          ((inclusion (Y := Y) P.stage).map ((S P.stage).rationalEpsilon.hom.app P.obj)) := by
    rw [hM, hN]
    refine ⟨NatIso.ofComponents
      (fun P ↦ (inclusion (Y := Y) P.stage).mapIso ((S P.stage).rationalEpsilon.app P.obj))
      (fun {P Q} f ↦ ?_), fun P ↦ HEq.rfl⟩
    change N.functor.map (M.functor.map f) ≫
        (U.ι Q.stage).map ((S Q.stage).rationalEpsilon.hom.app Q.obj) =
      (U.ι P.stage).map ((S P.stage).rationalEpsilon.hom.app P.obj) ≫ f
    simpa only [StageSystem.Morphism.descNatTrans_app,
      StageSystem.Morphism.functor_comp_map, StageSystem.Morphism.functor_id_map, τ] using
        (StageSystem.Morphism.descNatTrans τ).naturality f
  obtain ⟨ε, hε⟩ := desc
  have hh (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
      (e P).hom = ε.hom.app P := eq_of_heq ((he P).trans (hε P).symm)
  intro P Q f
  rw [hh P, hh Q]
  exact ε.hom.naturality f

end WeilConjectures
