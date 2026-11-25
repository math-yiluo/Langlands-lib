/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemScalarCoreData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.CategoryTheory.AdjointEquivalenceConjugation.AdjointEquivalenceConjugation
import WeilConjectures.SixFunctors.ExceptionalScalarTransport.ScalarComparisonTransport

/-! # Whole-system scalar transport before selected finite-level compatibility
Source: Zheng, Construction 4.1, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-system-scalar-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
attribute [local instance] Scalar.commShift Scalar.additive
  Operation.leftShift Operation.rightShift
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section
universe a b x y av bv xv yv
open CategoryTheory CategoryTheory.Functor
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  (eX : A ≌ X) (eY : B ≌ Y) {F : X ⥤ Y} {G : Y ⥤ X} (adj : F ⊣ G)
  {F₀ : A ⥤ B} {G₀ : B ⥤ A}
  (rF : F₀ ≅ eX.functor ⋙ F ⋙ eY.inverse)
  (rG : G₀ ≅ eY.functor ⋙ G ⋙ eX.inverse)

private theorem conjugatedCounit (N : B) :
    (eY.functor.map (rF.hom.app (G₀.obj N)) ≫
      eY.counit.app (F.obj (eX.functor.obj (G₀.obj N)))) ≫
      F.map (eX.functor.map (rG.hom.app N) ≫
        eX.counit.app (G.obj (eY.functor.obj N))) ≫
      adj.counit.app (eY.functor.obj N) =
    eY.functor.map
      (((((eX.toAdjunction.comp adj).comp eY.symm.toAdjunction).ofNatIsoLeft
        rF.symm).ofNatIsoRight rG.symm).counit.app N) := by
  simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Iso.symm_inv,
    AdjointEquivalenceConjugation.conjugation_counit, Functor.map_comp,
    Equivalence.counit, Equivalence.symm_inverse]
  have hr := rF.hom.naturality (rG.hom.app N)
  dsimp only [Functor.comp_map] at hr
  have hc (Z : Y) (k : Z ⟶ eY.functor.obj N) :
      eY.functor.map (eY.inverse.map k) ≫ eY.functor.map (eY.unitIso.inv.app N) =
        eY.counit.app Z ≫ k := by
    rw [← eY.counit_app_functor N]
    exact eY.counit_naturality k
  symm
  calc
    _ = eY.functor.map (rF.hom.app (G₀.obj N)) ≫
        eY.functor.map (eY.inverse.map
          (F.map (eX.functor.map (rG.hom.app N)) ≫
            F.map (eX.counit.app (G.obj (eY.functor.obj N))) ≫
              adj.counit.app (eY.functor.obj N))) ≫
        eY.functor.map (eY.unitIso.inv.app N) := by
      simpa only [Functor.map_comp, Category.assoc, Functor.comp_map] using
        congrArg (fun k ↦ eY.functor.map k ≫
          eY.functor.map (eY.inverse.map
            (F.map (eX.counit.app (G.obj (eY.functor.obj N))))) ≫
          eY.functor.map (eY.inverse.map (adj.counit.app (eY.functor.obj N))) ≫
          eY.functor.map (eY.unitIso.inv.app N)) hr
    _ = _ := by rw [hc]; simp only [Category.assoc]

end

private theorem reductionCounit
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (E : FieldStage.{u} l) (N : C.{u} l Ω Y (.integral E)) :
    (transport.reductionF E).hom.app ((operation (.integral E)).G.obj N) ≫
      (transport.F E).map ((transport.reductionG E).hom.app N) ≫
      (transport.adjunction E).counit.app
        ((transport.reconstruction E false).equivalence.functor.obj N) =
      (transport.reconstruction E false).equivalence.functor.map
        ((operation (.integral E)).adjunction.counit.app N) := by
  rw [transport.reductionF_eq, transport.reductionG_eq, transport.adjunction_eq]
  exact conjugatedCounit (transport.reconstruction E true).equivalence
    (transport.reconstruction E false).equivalence (transport.adjunction E)
    (transport.realizeF E) (transport.realizeG E) N

@[irreducible] private def chosenCoefficientSystems
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) (T : Scheme.{u}) :
    CoefficientExtensionSystems l E.carrier L.carrier i T :=
    (SemilinearSections.semilinearDerivedSections.{u + 1, u, u}
      (Scheme.ProEt.topology T)
      (integralCoefficientCommRingSheaf l E.carrier T)
      (coefficientSequenceCommRingTransition l E.carrier T)).some
      |>.coefficientExtension
        (integralCoefficientCommRingSheaf l L.carrier T)
        (coefficientSequenceCommRingTransition l L.carrier T)
        (integralScalarQuotientSheafMap l E.carrier L.carrier i T)
        (coefficientExtensionQuotient_naturality l E.carrier L.carrier i T)

@[irreducible] private def chosenReductionModel
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) (T : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus l E.carrier T)
    (SL : CoefficientDerivedSystemCalculus l L.carrier T)
    (A : CoefficientExtensionSystems l E.carrier L.carrier i T)
    (hu : IsUnit (l : Γ(T, ⊤))) :
    CoefficientExtensionReductionData l E.carrier L.carrier i T SE SL A :=
  (coefficientExtensionReductionModel l E.carrier L.carrier i T SE SL A hu).some

private theorem sequenceNormalized_of_iso (l : ℕ) [Fact l.Prime]
    (E : FieldStage.{u} l) (W : Scheme.{u})
    {X Y : coefficientSequenceDerived l E.carrier W} (e : X ≅ Y)
    (hX : IsNormalizedCoefficientSequence l E.carrier W X) :
    IsNormalizedCoefficientSequence l E.carrier W Y := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation l E.carrier W n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation l E.carrier W m).mapIso e
  let G := normalizedDVRRes l E.carrier W h
  have hn := (coefficientSequenceDerivedTransition l E.carrier W h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition l E.carrier W h).app Y =
    (coefficientSequenceDerivedTransition l E.carrier W h).app X ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hX h P).injective
    change (coefficientSequenceDerivedTransition l E.carrier W h).app X ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition l E.carrier W h).app X ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition l E.carrier W h).app Y ≫ G.map x =
      (coefficientSequenceDerivedTransition l E.carrier W h).app Y ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hX h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition l E.carrier W h).app Y ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs

private theorem tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro N P hN f hf hP M i hi
  exact h.2 N P (hN.map (fun q ↦ q ≪≫ e.symm)) f hf hP M i hi

private theorem fiber_bounds_iso (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    (T : Scheme.{u}) (n : ℕ)
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E.carrier (n + 1))}
    (e : K ≅ L) (a b c d : ℤ)
    (h : finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T K ∧
      K.IsGE a ∧ K.IsLE b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (n + 1))
        K c d) :
    finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T L ∧
      L.IsGE a ∧ L.IsLE b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (n + 1))
        L c d := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T) :=
    (finite_ctf_isTriangulated l E.carrier (n + 1) (Nat.succ_pos _) T).1
  have : K.IsGE a := h.2.1
  have : K.IsLE b := h.2.2.1
  exact ⟨ObjectProperty.prop_of_iso _ e h.1,
    DerivedCategory.TStructure.t.isGE_of_iso e a,
    DerivedCategory.TStructure.t.isLE_of_iso e b, tor_iso T _ e c d h.2.2.2⟩

private theorem sequence_of_iso (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    (T : Scheme.{u}) {M N : coefficientSequenceDerived l E.carrier T}
    (e : M ≅ N) (hM : sequenceProperty l E T M)
     : sequenceProperty l E T N := by
  have hN : IsNormalizedCoefficientSequence l E.carrier T N :=
    fun h P ↦ sequenceNormalized_of_iso l E T e hM.1 h P
  obtain ⟨a, b, c, d, hab, hcd, h⟩ := hM.2
  exact ⟨hN, a, b, c, d, hab, hcd, fun n ↦
    fiber_bounds_iso l E T n
      ((coefficientSequenceDerivedEvaluation l E.carrier T n).mapIso e) a b c d (h n)⟩

section
universe a b c d e f av bv cv dv ev fv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {E : Type e} [Category.{ev} E] {F : Type f} [Category.{fv} F]
@[irreducible] private def ambientComposite (S : A ⥤ C) (IE : A ⥤ B) (IL : C ⥤ D)
    (T : B ⥤ D) (RE : B ⥤ E) (RL : D ⥤ F) (U : E ⥤ F)
    (rE : A ⥤ E) (rL : C ⥤ F)
    (hL : rL = IL ⋙ RL) (hS : S ⋙ IL = IE ⋙ T) (hE : rE = IE ⋙ RE)
    (m : T ⋙ RL ≅ RE ⋙ U) : S ⋙ rL ≅ rE ⋙ U :=
  isoWhiskerLeft S (eqToIso hL) ≪≫
    isoWhiskerRight (eqToIso hS) RL ≪≫ isoWhiskerLeft IE m ≪≫
    isoWhiskerRight (eqToIso hE).symm U

private theorem normalizedComposite (S : A ⥤ C) (IE : A ⥤ B) (IL : C ⥤ D)
    (T : B ⥤ D) (RE : B ⥤ E) (RL : D ⥤ F) (U : E ⥤ F)
    (rE : A ⥤ E) (rL : C ⥤ F)
    (hL : rL = IL ⋙ RL) (hS : S ⋙ IL = IE ⋙ T) (hE : rE = IE ⋙ RE)
    (m : T ⋙ RL ≅ RE ⋙ U) (K : A) :
    HEq ((ambientComposite S IE IL T RE RL U rE rL hL hS hE m).hom.app K)
      (m.hom.app (IE.obj K)) := by
  unfold ambientComposite
  dsimp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, eqToIso.hom,
    Iso.symm_hom, eqToIso.inv]
  simp only [eqToHom_app, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl
end

section
universe a b c d av bv cv dv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
private theorem restrictScalar (P : ObjectProperty C) (Q : ObjectProperty D)
    (re : A ≌ P.FullSubcategory) (rl : B ≌ Q.FullSubcategory)
    (S : A ⥤ B) (T : C ⥤ D)
    (ambient : S ⋙ rl.functor ⋙ Q.ι ≅ re.functor ⋙ P.ι ⋙ T)
    (hQ : ∀ {M N : D}, (M ≅ N) → Q M → Q N) :
    ∃ (scalar : P.FullSubcategory ⥤ Q.FullSubcategory)
      (_ : scalar ⋙ Q.ι = P.ι ⋙ T)
      (reduction : S ⋙ rl.functor ≅ re.functor ⋙ scalar),
      ∀ K, HEq (Q.ι.map (reduction.hom.app K)) (ambient.hom.app K) := by
  have preserve (N : P.FullSubcategory) : Q (T.obj N.obj) := by
    let K := re.inverse.obj N
    let e := ambient.app K ≪≫ T.mapIso (P.ι.mapIso (re.counitIso.app N))
    exact hQ e ((rl.functor.obj (S.obj K)).property)
  let scalar := Q.lift (P.ι ⋙ T) preserve
  let reduction : S ⋙ rl.functor ≅ re.functor ⋙ scalar :=
    Functor.fullyFaithfulCancelRight Q.ι ambient
  refine ⟨scalar, rfl, reduction, ?_⟩
  intro K
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
end

private structure ScalarModel (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (tr : Transported l Ω D hl c operation left) (d : Mates l Ω c operation left)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) where
  coefficient (side : Bool) : CoefficientExtensionSystems l E.carrier L.carrier i
    (endpoint X Y side)
  coefficient_model (side : Bool) : CoefficientExtensionReductionData
    l E.carrier L.carrier i (endpoint X Y side)
    (tr.reconstruction E side).calculus (tr.reconstruction L side).calculus (coefficient side)
  scalar (side : Bool) : (sequenceProperty l E (endpoint X Y side)).FullSubcategory ⥤
    (sequenceProperty l L (endpoint X Y side)).FullSubcategory
  scalar_eq (side : Bool) : scalar side ⋙ (sequenceProperty l L (endpoint X Y side)).ι =
    (sequenceProperty l E (endpoint X Y side)).ι ⋙ (coefficient side).scalar.T
  reduction (side : Bool) :
    (d.scalar (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i) side).functor ⋙
        (tr.reconstruction L side).equivalence.functor ≅
      (tr.reconstruction E side).equivalence.functor ⋙ scalar side
  reduction_normalized (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((sequenceProperty l L (endpoint X Y side)).ι.map ((reduction side).hom.app K))
      ((coefficientExtensionReductionIso l E.carrier L.carrier i (endpoint X Y side)
        (tr.reconstruction E side).calculus (tr.reconstruction L side).calculus
        (coefficient side) (coefficient_model side)).hom.app K.obj)

private theorem scalarModel_exists
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    Nonempty (ScalarModel l Ω D hl c operation left transport d E L i) := by
  classical
  let A (side : Bool) := chosenCoefficientSystems l E L i (endpoint X Y side)
  have hunit (side : Bool) : IsUnit (l : Γ(endpoint X Y side, ⊤)) := by
    cases side
    · simpa only [map_natCast] using
        ((PurCompactSupport.coefficientPrimeUnit l D hl).map
          (Scheme.ΓSpecIso (.of D.k)).inv.hom).map ((Y ↘ Spec (.of D.k)).appTop.hom)
    · simpa only [map_natCast] using
        ((PurCompactSupport.coefficientPrimeUnit l D hl).map
          (Scheme.ΓSpecIso (.of D.k)).inv.hom).map ((X ↘ Spec (.of D.k)).appTop.hom)
  let model (side : Bool) := chosenReductionModel l E L i
    (endpoint X Y side) (transport.reconstruction E side).calculus
    (transport.reconstruction L side).calculus (A side) (hunit side)
  let S (side : Bool) := (d.scalar (s := .integral E) (t := .integral L)
    (PurCompactSupport.completedChange l E.carrier L.carrier i)
    (Allowed.integral E L i) side).functor
  let re (side : Bool) := (transport.reconstruction E side).equivalence
  let rl (side : Bool) := (transport.reconstruction L side).equivalence
  let P (side : Bool) := sequenceProperty l E (endpoint X Y side)
  let Q (side : Bool) := sequenceProperty l L (endpoint X Y side)
  let ambient (side : Bool) :
      S side ⋙ (rl side).functor ⋙ (Q side).ι ≅
        (re side).functor ⋙ (P side).ι ⋙ (A side).scalar.T :=
    ambientComposite (S side)
      (finiteTorConstructibleIntegral l E.carrier (endpoint X Y side)).ι
      (finiteTorConstructibleIntegral l L.carrier (endpoint X Y side)).ι
      (integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side))
      (transport.reconstruction E side).calculus.reduction
      (transport.reconstruction L side).calculus.reduction (A side).scalar.T
      ((re side).functor ⋙ (P side).ι) ((rl side).functor ⋙ (Q side).ι)
      (transport.reconstruction L side).reduction (d.integralScalar_eq E L i side)
      (transport.reconstruction E side).reduction
      (coefficientExtensionReductionIso l E.carrier L.carrier i (endpoint X Y side)
        (transport.reconstruction E side).calculus
        (transport.reconstruction L side).calculus (A side) (model side))
  have restricted (side : Bool) := restrictScalar (P side) (Q side)
    (re side) (rl side) (S side) (A side).scalar.T (ambient side)
    (fun e h ↦ sequence_of_iso l L (endpoint X Y side) e h)
  choose scalar scalar_eq reduction reduction_eq using restricted
  refine ⟨{ coefficient := A, coefficient_model := model, scalar := scalar
            scalar_eq := scalar_eq, reduction := reduction
            reduction_normalized := ?_ }⟩
  · intro side K
    exact (reduction_eq side K).trans (normalizedComposite (S side)
      (finiteTorConstructibleIntegral l E.carrier (endpoint X Y side)).ι
      (finiteTorConstructibleIntegral l L.carrier (endpoint X Y side)).ι
      (integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side))
      (transport.reconstruction E side).calculus.reduction
      (transport.reconstruction L side).calculus.reduction (A side).scalar.T
      ((re side).functor ⋙ (P side).ι) ((rl side).functor ⋙ (Q side).ι)
      (transport.reconstruction L side).reduction (d.integralScalar_eq E L i side)
      (transport.reconstruction E side).reduction
      (coefficientExtensionReductionIso l E.carrier L.carrier i (endpoint X Y side)
        (transport.reconstruction E side).calculus
        (transport.reconstruction L side).calculus (A side) (model side)) K)

/-- Construct whole-system scalar transport from the normalized coefficient reduction
model, before comparing selected ramified levels.
Source: Zheng, Construction 4.1 and Lemma 5.22.
Proof: compose the coefficient reduction model with the two reconstruction equalities.
Transport normalized sequence membership and the original four bounds along the resulting
isomorphism, and restrict the actual scalar functor. Cancel the full inclusion for reduction.
Conjugate the integral q and b with reductionF/G and the scalar reduction comparison, then
descend along the fully faithful reconstruction functor. Inverse-factor cancellation gives
the two reduction equations. The integral counit equation and both reconstruction counit
identities imply the new counit on the equivalence image; naturality and its counit iso
extend it to every sequence. The image reduction map is the specified model up to eqToHom.
(blueprint: lem-sf-exceptional-integral-system-scalar-core). -/
theorem exceptionalIntegralSystemScalarCore
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    Nonempty (SystemScalarCore l Ω D hl c operation left transport d E L i) := by
  obtain ⟨model⟩ := scalarModel_exists l Ω D hl c operation left transport d E L i
  let re (side : Bool) := (transport.reconstruction E side).equivalence
  let := (d.scalar (s := .integral E) (t := .integral L)
    (PurCompactSupport.completedChange l E.carrier L.carrier i)
    (Allowed.integral E L i) true).commShift
  let := (d.scalar (s := .integral E) (t := .integral L)
    (PurCompactSupport.completedChange l E.carrier L.carrier i)
    (Allowed.integral E L i) false).commShift
  let q₀ := Mates.q l Ω d (s := .integral E) (t := .integral L)
    (PurCompactSupport.completedChange l E.carrier L.carrier i) (Allowed.integral E L i)
  let b₀ := Mates.b l Ω d (s := .integral E) (t := .integral L)
    (PurCompactSupport.completedChange l E.carrier L.carrier i) (Allowed.integral E L i)
  obtain ⟨q, b, hc, hqr, hbr⟩ := ExceptionalScalarTransport.transportComparisons
    (operation (.integral E)).adjunction (transport.adjunction E)
    (operation (.integral L)).adjunction (transport.adjunction L)
    (re true) (re false) (transport.reductionF E) (transport.reductionG E)
    (transport.reductionF L) (transport.reductionG L) (model.reduction true) (model.reduction false)
    q₀ b₀
    (d.comparison (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i)).counit
    (reductionCounit l Ω D hl c operation left transport E)
    (reductionCounit l Ω D hl c operation left transport L)
  exact ⟨{ coefficient := model.coefficient, coefficient_model := model.coefficient_model
           scalar := model.scalar, scalar_eq := model.scalar_eq
           reduction := model.reduction, reduction_normalized := model.reduction_normalized
           q := q, b := b, counit := hc, q_reduction := hqr, b_reduction := hbr }⟩

end WeilConjectures.ExceptionalIntegralScalar
