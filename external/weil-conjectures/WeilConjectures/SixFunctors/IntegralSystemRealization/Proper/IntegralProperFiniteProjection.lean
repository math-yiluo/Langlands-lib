/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFinitePullbackCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFinitePullbackNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteProperMate
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Proper finite projection in scalar reduction coordinates -/

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
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Proper scalar comparison in the published finite constant-ring coordinates.
Source: Stacks 07A7; normalized proper mate in fix-prop-coherence
(blueprint: lem-sf-integral-proper-finite-projection). -/
@[irreducible] def properFiniteReduction {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ringedPush l E f ⋙ scalarReductionDerivedExtension l E Y n ⟶
      scalarReductionDerivedExtension l E X n ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  letI := (proEtaleConstantModuleDirectImage_additive_leftExact f
    (Padic.coefficientExtensionRing l E (n + 1))).1
  Functor.whiskerLeft _ (PurCompactSupport.finiteReductionIso l E Y n).inv ≫
    PurCompactSupport.properComparison
      (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f ≫
    Functor.whiskerLeft _
      (Functor.rightDerivedFunctorNatIso
        (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n f))).hom ≫
    Functor.whiskerRight (PurCompactSupport.finiteReductionIso l E X n).hom _

private theorem projection_mate
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {p : A ⥤ B} {q : B ⥤ A} {r : A ⥤ C} {s : C ⥤ A}
    {t : B ⥤ D} {u : D ⥤ B} {v : C ⥤ D} {w : D ⥤ C}
    {e : C ⥤ E} {g : D ⥤ F} {P : E ⥤ F} {Q : F ⥤ E}
    {RY : A ⥤ E} {RX : B ⥤ F}
    (a : p ⊣ q) (b : v ⊣ w) (c : r ⊣ s) (d : t ⊣ u) (z : P ⊣ Q)
    (h : p ⋙ t ≅ r ⋙ v) (k : v ⋙ g ≅ e ⋙ P)
    (ρY : r ⋙ e ≅ RY) (ρX : t ⋙ g ≅ RX)
    (θ : RY ⋙ P ⟶ p ⋙ RX) (β : q ⋙ RY ⟶ RX ⋙ Q)
    (α : w ⋙ e ⟶ g ⋙ Q)
    (hθ : ∀ K, θ.app K ≫ ρX.inv.app (p.obj K) =
      P.map (ρY.inv.app K) ≫ k.inv.app (r.obj K) ≫ g.map (h.inv.app K))
    (hβ : ∀ K, P.map (β.app K) ≫ z.counit.app (RX.obj K) =
      θ.app (q.obj K) ≫ RX.map (a.counit.app K))
    (hα : ∀ M, P.map (α.app M) ≫ z.counit.app (g.obj M) =
      k.inv.app (w.obj M) ≫ g.map (b.counit.app M)) (M : D) :
    RY.map ((conjugateIsoEquiv (c.comp b) (a.comp d) h).hom.app M) ≫
        β.app (u.obj M) ≫ Q.map (ρX.inv.app (u.obj M) ≫ g.map (d.counit.app M)) =
      ρY.inv.app (s.obj (w.obj M)) ≫ e.map (c.counit.app (w.obj M)) ≫ α.app M := by
  let δ := (conjugateIsoEquiv (c.comp b) (a.comp d) h).hom.app M
  have hc := conjugateEquiv_counit (c.comp b) (a.comp d) h.hom M
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] at hc
  change t.map (p.map δ) ≫
      (t.map (a.counit.app (u.obj M)) ≫ d.counit.app M) =
    h.hom.app (s.obj (w.obj M)) ≫
      (v.map (c.counit.app (w.obj M)) ≫ b.counit.app M) at hc
  have hh : v.map (r.map δ) ≫ h.inv.app (q.obj (u.obj M)) ≫
      t.map (a.counit.app (u.obj M)) ≫ d.counit.app M =
      v.map (c.counit.app (w.obj M)) ≫ b.counit.app M := by
    have hn := h.inv.naturality δ
    change v.map (r.map δ) ≫ h.inv.app (q.obj (u.obj M)) =
      h.inv.app (s.obj (w.obj M)) ≫ t.map (p.map δ) at hn
    rw [← Category.assoc, ← Category.assoc, hn]
    simp only [Category.assoc]
    rw [hc]
    simp only [Iso.inv_hom_id_app_assoc]
  apply (z.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hz {U V : F} (f : U ⟶ V) :
      P.map (Q.map f) ≫ z.counit.app V = z.counit.app U ≫ f := by
    simpa only [Functor.comp_map, Functor.id_map] using z.counit.naturality f
  rw [hz (g.map (d.counit.app M))]
  simp only [Functor.comp_obj, Functor.id_obj]
  rw [reassoc_of% (hz (ρX.inv.app (u.obj M)))]
  rw [← Category.assoc (P.map (β.app (u.obj M))), hβ]
  have hnX := ρX.inv.naturality (a.counit.app (u.obj M))
  change RX.map (a.counit.app (u.obj M)) ≫ ρX.inv.app (u.obj M) =
    ρX.inv.app (p.obj (q.obj (u.obj M))) ≫ g.map (t.map (a.counit.app (u.obj M))) at hnX
  simp only [Category.assoc]
  rw [reassoc_of% hnX]
  rw [← Category.assoc (θ.app (q.obj (u.obj M))), hθ]
  have hnY := ρY.inv.naturality δ
  change RY.map δ ≫ ρY.inv.app (q.obj (u.obj M)) =
    ρY.inv.app (s.obj (w.obj M)) ≫ e.map (r.map δ) at hnY
  simp only [Category.assoc]
  rw [← P.map_comp_assoc, hnY, P.map_comp]
  have hnk := k.inv.naturality (r.map δ)
  change P.map (e.map (r.map δ)) ≫ k.inv.app (r.obj (q.obj (u.obj M))) =
    k.inv.app (r.obj (s.obj (w.obj M))) ≫ g.map (v.map (r.map δ)) at hnk
  simp only [Category.assoc]
  rw [reassoc_of% hnk]
  rw [← g.map_comp, ← g.map_comp, ← g.map_comp, hh, g.map_comp]
  have hnk' := k.inv.naturality (c.counit.app (w.obj M))
  change P.map (e.map (c.counit.app (w.obj M))) ≫ k.inv.app (w.obj M) =
    k.inv.app (r.obj (s.obj (w.obj M))) ≫ g.map (v.map (c.counit.app (w.obj M))) at hnk'
  rw [← reassoc_of% hnk', ← hα]

private theorem app_eq_of_iso {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (α β : F ⟶ G) {P K : A} (e : P ≅ K)
    (h : α.app P = β.app P) : α.app K = β.app K := by
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality, β.naturality, h]

private theorem goodRepresentative (X : Scheme.{u}) (K : Integral l E X) :
    ∃ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : q.IsLocalization W := goodComplexes_isLocalization
    (completedIntegralCommRingSheafUnrestricted l E X)
    (integralOperationsGoodComplex l E X) (fun _ ↦ Iff.rfl)
  let : q.EssSurj := Localization.essSurj q W
  exact ⟨q.objPreimage K, ⟨q.objObjPreimageIso K⟩⟩

private theorem finitePullback_normalization (o : Operations l E)
    (model : RealizationModel l E o) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (K : Integral l E Y) :
    (finiteScalarPullback l E f n).inv.app K ≫
        ((calculus l E X).reductionEvaluation n).inv.app ((ringedPull l E f).obj K) =
      (finiteDerivedPullback l E n f).map
          (((calculus l E Y).reductionEvaluation n).inv.app K) ≫
        (pullbackTensorDerivedEvaluation l E f n).inv.app
          ((calculus l E Y).reduction.obj K) ≫
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((model.reductionPull f).inv.app K) := by
  let α := (finiteScalarPullback l E f n).inv ≫
    Functor.whiskerLeft (ringedPull l E f) ((calculus l E X).reductionEvaluation n).inv
  let β := Functor.whiskerRight ((calculus l E Y).reductionEvaluation n).inv
      (finiteDerivedPullback l E n f) ≫
    Functor.whiskerLeft (calculus l E Y).reduction
      (pullbackTensorDerivedEvaluation l E f n).inv ≫
    Functor.whiskerRight (model.reductionPull f).inv
      (coefficientSequenceDerivedEvaluation l E X n)
  change α.app K = β.app K
  obtain ⟨P, ⟨eP⟩⟩ := goodRepresentative l E Y K
  apply app_eq_of_iso α β eP
  exact integralFinitePullback_onGood l E o model f P n

/-- Finite projection of the proper realization, before any open extension.
There is no completeness or constructibility assumption on the system M.
Source: Stacks 07A7 and 0941; fix-prop-coherence.proof.md, preservation of
adjunction units and counits; Step 1 of integral support projection transport
(blueprint: lem-sf-integral-proper-finite-projection).

Proof: first identify inverse pullback/reduction in finite coordinates on a
flat-term K-flat representative, by integralFinitePullback_onGood. Naturality
and the essential surjectivity of good-complex localization extend that equality
to arbitrary integral derived objects. integralFiniteProperMate identifies the
canonical proper finite comparison by its geometric-adjunction counit equation.
Transpose the desired equality through the finite geometric adjunction. Naturality
moves the finite coordinate isomorphisms past model.push and the geometric
counits. The conjugateEquiv_counit identity for the two composite adjunctions
then cancels the inverse reduction/pullback comparison against the comparison
whose conjugate defines model.push. DirectEvaluation.counit identifies the
remaining finite transpose. Injectivity of the adjunction bijection gives the
claimed equality. This is the explicit private projection_mate calculation.
No faithfulness of derived evaluations or invertible reconstruction unit is used;
the zero system and exponent one obey the same adjunction identities. -/
theorem integralProperFiniteProjection (o : Operations l E)
    (model : RealizationModel l E o) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : System l E X) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).map ((model.push l E f).hom.app M) ≫
      (properFiniteReduction l E f n).app ((coefficientSequenceLimit l E X).obj M) ≫
      (proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))).map
          (((calculus l E X).reductionEvaluation n).inv.app
              ((coefficientSequenceLimit l E X).obj M) ≫
            (coefficientSequenceDerivedEvaluation l E X n).map
              ((calculus l E X).adjunction.counit.app M)) =
    ((calculus l E Y).reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E Y).obj ((Operations.push l E o f).obj M)) ≫
      (coefficientSequenceDerivedEvaluation l E Y n).map
        ((calculus l E Y).adjunction.counit.app ((Operations.push l E o f).obj M)) ≫
      ((o.evaluation f).evaluation n).hom.app M := by
  apply projection_mate
    (ringedAdj l E f) (o.direct f).adj
    (calculus l E Y).adjunction (calculus l E X).adjunction (finiteAdj l E f n)
    (model.reductionPull f) (pullbackTensorDerivedEvaluation l E f n)
    ((calculus l E Y).reductionEvaluation n) ((calculus l E X).reductionEvaluation n)
    (finiteScalarPullback l E f n).inv (properFiniteReduction l E f n)
    ((o.evaluation f).evaluation n).hom
  · exact finitePullback_normalization l E o model f n
  · intro K
    simpa only [properFiniteReduction, coefficientFiniteDerivedExtension, ringedPush,
      PurCompactSupport.push] using integralFiniteProperMate l E f n K
  · intro N
    have h := congrArg
      (fun v ↦ (pullbackTensorDerivedEvaluation l E f n).inv.app
        ((Operations.push l E o f).obj N) ≫ v) ((o.evaluation f).counit n N)
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using h

end WeilConjectures.IntegralSystemRealization
