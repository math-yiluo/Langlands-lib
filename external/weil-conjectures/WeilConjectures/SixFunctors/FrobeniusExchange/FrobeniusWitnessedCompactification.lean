/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Witnessed finite-coefficient compactification origins

The finite-origin constructions and refinement normalization are retained verbatim
from coefficient exchange, with the same public names and formulas.
Source: blueprint def:weil-compact-support-object and prop-compactification-coherence
(blueprint: def-weil-frobenius-witnessed-compactification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option Elab.async true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.FrobeniusExchange

section CoordinateTransport
universe uC uD uB uZ vC vD vB vZ
variable {C : Type uC} {D : Type uD} {B : Type uB} {Z : Type uZ}
  [Category.{vC} C] [Category.{vD} D] [Category.{vB} B] [Category.{vZ} Z]

private theorem conjugate_refinement
    (Jc : C ⥤ B) (Jd : C ⥤ D) (R : B ⥤ D) (P : D ⥤ Z) (S : B ⥤ Z)
    (z : S ≅ R ⋙ P) {K K' : C} (a : K ≅ K')
    (w : Jd.obj K ≅ R.obj (Jc.obj K)) :
    z.app (Jc.obj K') ≪≫
        P.mapIso (Jd.mapIso a.symm ≪≫ w ≪≫ R.mapIso (Jc.mapIso a)).symm =
      (Jc ⋙ S).mapIso a.symm ≪≫
        (z.app (Jc.obj K) ≪≫ P.mapIso w.symm) ≪≫ (Jd ⋙ P).mapIso a := by
  apply Iso.ext
  have hz := z.hom.naturality (Jc.map a.inv)
  dsimp only [Functor.comp_map] at hz
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.comp_map, Iso.app_hom, Iso.trans_inv, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hz]
  rfl

private theorem conjugate_refinement_pair
    (Jc : C ⥤ B) (Jd : C ⥤ D) (R : B ⥤ D) (P : D ⥤ Z) (S T : B ⥤ Z)
    (z₁ : S ≅ T) (z₂ : T ≅ R ⋙ P) {K K' : C} (a : K ≅ K')
    (w : Jd.obj K ≅ R.obj (Jc.obj K)) :
    z₁.app (Jc.obj K') ≪≫ z₂.app (Jc.obj K') ≪≫
        P.mapIso (Jd.mapIso a.symm ≪≫ w ≪≫ R.mapIso (Jc.mapIso a)).symm =
      (Jc ⋙ S).mapIso a.symm ≪≫
        (z₁.app (Jc.obj K) ≪≫ z₂.app (Jc.obj K) ≪≫ P.mapIso w.symm) ≪≫
          (Jd ⋙ P).mapIso a := by
  simpa only [NatIso.trans_app, Iso.trans_assoc] using
    (conjugate_refinement Jc Jd R P S (z₁ ≪≫ z₂) a w)

private theorem cancel_recorded_witness (e : C ≌ D) {L K : C} {S : D}
    (a : S ≅ e.functor.obj L) (w : L ≅ K) :
    e.unitIso.app L ≪≫ e.inverse.mapIso
        (a.symm ≪≫ (Iso.refl S).symm ≪≫ (a ≪≫ e.functor.mapIso w)) =
      w ≪≫ e.unitIso.app K := by
  simp only [Iso.refl_symm, Iso.refl_trans]
  apply Iso.ext
  change e.unitIso.hom.app _ ≫ e.inverse.map
    (a.inv ≫ (a.hom ≫ e.functor.map w.hom)) = w.hom ≫ e.unitIso.hom.app _
  rw [Iso.inv_hom_id_assoc]
  exact (e.unitIso.hom.naturality w.hom).symm

private theorem conjugate_witness
    (Jc : C ⥤ B) (Jd : C ⥤ D) (R : B ⥤ D) {L K K' : C}
    (w : L ≅ K) (a : K ≅ K') (w' : L ≅ K') (h : w' = w ≪≫ a)
    (t : Jd.obj L ≅ R.obj (Jc.obj L)) :
    Jd.mapIso w'.symm ≪≫ t ≪≫ R.mapIso (Jc.mapIso w') =
      Jd.mapIso a.symm ≪≫
        (Jd.mapIso w.symm ≪≫ t ≪≫ R.mapIso (Jc.mapIso w)) ≪≫
          R.mapIso (Jc.mapIso a) := by
  rw [h]
  simp only [Iso.trans_symm, Functor.mapIso_trans, Iso.trans_assoc]

private theorem cancel_coordinate_units
    (q : B ⥤ Z) (U V : C ⥤ B) {K K' : C} (a : K ≅ K')
    (t : U.obj K ≅ V.obj K) {W W' W₀ W₀' : Z}
    (p : W ≅ W₀) (b : W₀ ≅ q.obj (U.obj K))
    (p' : W' ≅ W₀') (b' : W₀' ≅ q.obj (V.obj K)) :
    (p ≪≫ b ≪≫ q.mapIso (U.mapIso a)) ≪≫
        q.mapIso (U.mapIso a.symm ≪≫ t ≪≫ V.mapIso a) ≪≫
        (p' ≪≫ b' ≪≫ q.mapIso (V.mapIso a)).symm =
      p ≪≫ b ≪≫ q.mapIso t ≪≫ b'.symm ≪≫ p'.symm := by
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm,
    Iso.trans_assoc, Iso.self_symm_id_assoc]

private theorem cancel_coordinate_units_of
    (q : B ⥤ Z) (U V : C ⥤ B) {K K' : C} (a : K ≅ K')
    (t : U.obj K ≅ V.obj K) {W W' W₀ W₀' : Z}
    (p : W ≅ W₀) (b : W₀ ≅ q.obj (U.obj K))
    (p' : W' ≅ W₀') (b' : W₀' ≅ q.obj (V.obj K))
    (s : U.obj K' ≅ V.obj K') (m : W ≅ q.obj (U.obj K'))
    (m' : W' ≅ q.obj (V.obj K'))
    (hs : s = U.mapIso a.symm ≪≫ t ≪≫ V.mapIso a)
    (hm : m = p ≪≫ b ≪≫ q.mapIso (U.mapIso a))
    (hm' : m' = p' ≪≫ b' ≪≫ q.mapIso (V.mapIso a)) :
    m ≪≫ q.mapIso s ≪≫ m'.symm = p ≪≫ b ≪≫ q.mapIso t ≪≫ b'.symm ≪≫ p'.symm := by
  rw [hs, hm, hm']
  exact cancel_coordinate_units q U V a t p b p' b'

private def candidate_model
    {I : Type v} [Category I] (e : C ≌ D) (q : B ⥤ Z)
    (k : I ⥤ D) (v : I ⥤ C) (h : v ≅ k ⋙ e.inverse)
    (H : D ⥤ Z) (U : C ⥤ B) (a : e.functor ⋙ H ≅ U ⋙ q) :
    k ⋙ H ≅ v ⋙ U ⋙ q :=
  let t : k ≅ v ⋙ e.functor :=
    (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft k e.counitIso.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight h.symm e.functor
  isoWhiskerRight t H ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft v a

private theorem candidate_model_app
    {I : Type v} [Category I] (e : C ≌ D) (q : B ⥤ Z)
    (k : I ⥤ D) (v : I ⥤ C) (h : v ≅ k ⋙ e.inverse)
    (H : D ⥤ Z) (U : C ⥤ B) (a : e.functor ⋙ H ≅ U ⋙ q) (O : I) :
    (candidate_model e q k v h H U a).app O =
      H.mapIso (e.counitIso.app (k.obj O)).symm ≪≫
        a.app (e.inverse.obj (k.obj O)) ≪≫ q.mapIso (U.mapIso (h.app O).symm) := by
  apply Iso.ext
  simp only [candidate_model, NatIso.trans_app, Iso.app_hom, Iso.app_inv,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Category.id_comp,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  exact congrArg (fun t ↦ H.map (e.counitIso.app (k.obj O)).inv ≫ t)
    (a.hom.naturality (h.app O).inv)

private theorem transport_coherence
    {I : Type v} [Category I]
    (F : C ⥤ D) (q : B ⥤ Z) (U : I → D ⥤ B) (V : I → C ⥤ Z)
    (b : ∀ i, V i ≅ F ⋙ U i ⋙ q)
    (theta : ∀ (i j : I) (_r : i ⟶ j), U i ≅ U j)
    (hid : ∀ i, theta i i (𝟙 i) = Iso.refl _)
    (hcomp : ∀ (i j k : I) (r : i ⟶ j) (s : j ⟶ k),
      theta i k (r ≫ s) = theta i j r ≪≫ theta j k s)
    (hfinite : ∀ (m : ℕ) (c : Fin m → I), ∃ d : I, ∀ i, Nonempty (d ⟶ c i))
    (comparison : ∀ i j : I, U i ≅ U j)
    (hcomparison : ∀ (i j k : I) (r : k ⟶ i) (s : k ⟶ j),
      comparison i j = (theta k i r).symm ≪≫ theta k j s) :
    ∃ theta' : ∀ (i j : I) (_r : i ⟶ j), V i ≅ V j,
      (∀ (i j : I) (r : i ⟶ j) (O : C),
        (theta' i j r).app O =
          (b i).app O ≪≫ q.mapIso ((theta i j r).app (F.obj O)) ≪≫ ((b j).app O).symm) ∧
      (∀ i, theta' i i (𝟙 i) = Iso.refl _) ∧
      (∀ (i j k : I) (r : i ⟶ j) (s : j ⟶ k),
        theta' i k (r ≫ s) = theta' i j r ≪≫ theta' j k s) ∧
      ∃! comparison' : ∀ i j : I, V i ≅ V j,
        ∀ (i j k : I) (r : k ⟶ i) (s : k ⟶ j),
          comparison' i j = (theta' k i r).symm ≪≫ theta' k j s := by
  let transport {i j : I} (t : U i ≅ U j) : V i ≅ V j :=
    b i ≪≫ isoWhiskerLeft F (isoWhiskerRight t q) ≪≫ (b j).symm
  have transport_id (i : I) : transport (Iso.refl (U i)) = Iso.refl _ := by
    have hi : isoWhiskerLeft F (isoWhiskerRight (Iso.refl (U i)) q) = Iso.refl _ := by
      apply Iso.ext
      ext O
      exact q.map_id _
    change b i ≪≫ isoWhiskerLeft F (isoWhiskerRight (Iso.refl (U i)) q) ≪≫
      (b i).symm = Iso.refl _
    rw [hi, Iso.refl_trans]
    exact Iso.self_symm_id (b i)
  have transport_comp {i j k : I} (t : U i ≅ U j) (s : U j ≅ U k) :
      transport (t ≪≫ s) = transport t ≪≫ transport s := by
    ext O
    simp [transport]
  have transport_symm {i j : I} (t : U i ≅ U j) :
      transport t.symm = (transport t).symm := by
    ext O
    simp [transport]
  refine ⟨fun i j r ↦ transport (theta i j r), ?_, ?_, ?_, ?_⟩
  · intro i j r O
    rfl
  · intro i
    change transport (theta i i (𝟙 i)) = Iso.refl _
    rw [hid, transport_id]
  · intro i j k r s
    change transport (theta i k (r ≫ s)) = transport (theta i j r) ≪≫
      transport (theta j k s)
    rw [hcomp, transport_comp]
  · refine ⟨fun i j ↦ transport (comparison i j), ?_, ?_⟩
    · intro i j k r s
      change transport (comparison i j) = (transport (theta k i r)).symm ≪≫
        transport (theta k j s)
      rw [hcomparison i j k r s, transport_comp, transport_symm]
    · intro comparison' hcomparison'
      funext i j
      obtain ⟨k, hk⟩ := hfinite 2 ![i, j]
      obtain ⟨r⟩ := hk 0
      obtain ⟨s⟩ := hk 1
      rw [hcomparison' i j k r s, hcomparison i j k r s,
        transport_comp, transport_symm]

end CoordinateTransport

section FiniteGeometry
variable (A : Type u) [CommRing A] [Finite A]

/-- The published comparison inverse image followed by its canonical realization.
Source: Stacks 099R; blueprint compact-support etale-origin paragraph
(blueprint: def-weil-frobenius-witnessed-compactification). -/
def originUnderlying (X : Scheme.{u}) :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
    (sfIntrinsicModuleEquivalence X A).functor

/-- Additivity of the specified comparison and realization composite.
Source: Stacks 099R (blueprint: def-weil-frobenius-witnessed-compactification). -/
instance originUnderlyingAdditive (X : Scheme.{u}) : (originUnderlying A X).Additive :=
  inferInstanceAs ((ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
      (sfIntrinsicModuleEquivalence X A).functor).Additive)

/-- Exact comparison preserves finite limits.
Source: Stacks 099R (blueprint: def-weil-frobenius-witnessed-compactification). -/
instance originUnderlyingLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (originUnderlying A X) :=
  inferInstanceAs (PreservesFiniteLimits (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
      (sfIntrinsicModuleEquivalence X A).functor))

/-- Exact comparison preserves finite colimits.
Source: Stacks 099R (blueprint: def-weil-frobenius-witnessed-compactification). -/
instance originUnderlyingColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (originUnderlying A X) :=
  inferInstanceAs (PreservesFiniteColimits (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
      (sfIntrinsicModuleEquivalence X A).functor))

/-- The inverse image from the etale site, in the actual intrinsic derived category.
Source: Stacks 099R (blueprint: def-weil-frobenius-witnessed-compactification). -/
def origin (X : Scheme.{u}) := (originUnderlying A X).mapDerivedCategory

/-- An actual retained etale-origin triple, in the intrinsic constant-ring category.
Its morphisms below will be all ambient morphisms between its underlying objects.
Source: blueprint order 1472 (blueprint: def-weil-frobenius-witnessed-compactification). -/
structure CompactOrigin (X : Scheme.{u}) where
  /-- The original pro-etale object. -/
  K : proEtaleDerivedCategory X A
  /-- Its bounded below etale antecedent. -/
  L : DerivedCategory.Plus
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
  /-- The retained comparison, with no new antecedent chosen. -/
  alpha : (origin A X).obj L.obj ≅ K

/-- The induced category retains every ambient map, without requiring a map of witnesses.
Source: blueprint order 1472 (blueprint: def-weil-frobenius-witnessed-compactification). -/
abbrev CompactOriginCategory (X : Scheme.{u}) :=
  InducedCategory (proEtaleDerivedCategory X A) (fun O : CompactOrigin A X ↦ O.K)

/-- Forget only the retained witness, and preserve its actual underlying object and map.
Source: blueprint order 1472 (blueprint: def-weil-frobenius-witnessed-compactification). -/
def compactOriginForget (X : Scheme.{u}) :
    CompactOriginCategory A X ⥤ proEtaleDerivedCategory X A :=
  inducedFunctor (fun O : CompactOrigin A X ↦ O.K)

/-- Cancel the realization unit in ordinary open extension, before exact descent.
Source: Stacks 00YV, 03DI (blueprint: def-weil-frobenius-witnessed-compactification). -/
def fixedOpenModel {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    (sfIntrinsicModuleEquivalence X A).functor ⋙ sfIntrinsicExtensionByZero j A ≅
      ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
          (sfIntrinsicModuleEquivalence B A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (sfIntrinsicModuleEquivalence X A).unitIso.symm _ ≪≫
      Functor.leftUnitor _

/-- The exact-derived open model is fixed by the same ordinary realization unit.
Source: Stacks 00YV, 03DI (blueprint: def-weil-frobenius-witnessed-compactification). -/
def fixedDerivedOpenModel {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicDerivedOpen A j ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
          (sfIntrinsicDerivedEquivalence B A).functor :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (fixedOpenModel A j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The fixed-scalar candidate, using precisely exact open extension then proper image.
Source: blueprint order 1485 (blueprint: def-weil-frobenius-witnessed-compactification). -/
def fixedCompact {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).rightDerivedFunctor

/-- The explicit coordinate change is open-unit cancellation followed by the recorded
section-normalized direct-image comparison. It contains no freely chosen isomorphism.
Source: blueprint order 1485 (blueprint: def-weil-frobenius-witnessed-compactification). -/
def fixedCompactModel {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicCompactSupport c A ≅
      fixedCompact A c ⋙ (sfIntrinsicDerivedEquivalence Y A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (fixedDerivedOpenModel A c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

/-- The fixed antecedent comparison retains the given alpha and the exact-derived
composition map, with the canonical realization unit.
Source: blueprint order 1485 (blueprint: def-weil-frobenius-witnessed-compactification). -/
def fixedOriginWitness (X : Scheme.{u}) (O : CompactOrigin A X) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj O.L.obj ≅
      (sfIntrinsicDerivedEquivalence X A).inverse.obj O.K :=
  (sfIntrinsicDerivedEquivalence X A).unitIso.app _ ≪≫
    (sfIntrinsicDerivedEquivalence X A).inverse.mapIso
      (((Functor.mapDerivedCategoryCompIso
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X)
        (sfIntrinsicModuleEquivalence X A).functor).app O.L.obj) ≪≫ O.alpha)

/-- The proper-open comparison conjugated by this very retained witness.
Source: blueprint order 1485 part (a); proposition-construction-independence-rf-shriek--7
(blueprint: def-weil-frobenius-witnessed-compactification). -/
def fixedRefinementOpen {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOrigin A X) :
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) d.i).mapDerivedCategory.obj
        ((sfIntrinsicDerivedEquivalence X A).inverse.obj O.K) ≅
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r.hom).rightDerivedFunctor.obj
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj
          ((sfIntrinsicDerivedEquivalence X A).inverse.obj O.K)) :=
  (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) d.i).mapDerivedCategory.mapIso
        (fixedOriginWitness A X O).symm ≪≫
    ProEtale.properOpenProEtaleIso _ r.hom c.i d.i r.i_hom O.L ≪≫
    (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r.hom).rightDerivedFunctor.mapIso
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.mapIso
            (fixedOriginWitness A X O))

/-- The actual refinement isomorphism: proper compositor followed by proper
pushforward of the inverse proper-open map, transported to intrinsic coordinates.
Source: blueprint order 1485 part (b)
(blueprint: def-weil-frobenius-witnessed-compactification). -/
def intrinsicRefinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOrigin A X) :
    (sfIntrinsicCompactSupport c A).obj O.K ≅ (sfIntrinsicCompactSupport d A).obj O.K :=
  let e := sfIntrinsicDerivedEquivalence X A
  let q := sfIntrinsicDerivedEquivalence Y A
  let K := e.inverse.obj O.K
  let fixed : (fixedCompact A c).obj K ≅ (fixedCompact A d).obj K :=
    (eqToIso (congrArg
      (fun h ↦ (ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).rightDerivedFunctor)
      r.hom_g.symm)).app _ ≪≫
      (ProEtale.finiteDirectImageComposition _ r.hom d.g).app _ ≪≫
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) d.g).rightDerivedFunctor.mapIso
          (fixedRefinementOpen A r O).symm
  (sfIntrinsicCompactSupport c A).mapIso (e.counitIso.app O.K).symm ≪≫
    (fixedCompactModel A c).app K ≪≫ q.functor.mapIso fixed ≪≫
    ((fixedCompactModel A d).app K).symm ≪≫
    (sfIntrinsicCompactSupport d A).mapIso (e.counitIso.app O.K)

/-- The candidate restricted to witnessed objects, with all ambient morphisms.
Source: blueprint order 1485 (blueprint: def-weil-frobenius-witnessed-compactification). -/
def intrinsicOriginCandidate {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  compactOriginForget A X ⋙ sfIntrinsicCompactSupport c A

section CoherenceCoordinates
variable (X : Scheme.{u})
@[instance_reducible] private def recordedTopology : TopologicalSpace (ULift.{u + 1} A) := ⊥
attribute [local instance] recordedTopology

private theorem recordedDiscrete : @DiscreteTopology (ULift.{u + 1} A) (recordedTopology A) :=
  discreteTopology_bot _
attribute [local instance] recordedDiscrete

private def recordedOrigin (O : CompactOriginCategory A X) :
    ProEtale.EtaleOriginDerivedCategory X (ULift.{u + 1} A) := by
  let e := sfIntrinsicDerivedEquivalence X A
  let R := ProEtale.finiteCoefficientRealization X (ULift.{u + 1} A)
  let eR := ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)
  let a : eR.functor.obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.obj
        O.L.obj) ≅ eR.functor.obj (e.inverse.obj O.K) :=
    eR.functor.mapIso (fixedOriginWitness A X O)
  let w := ((Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)
      R).app O.L.obj).symm ≪≫ a
  let K : ProEtale.FiniteCoefficientDerivedCategoryPlus X (ULift.{u + 1} A) :=
    ⟨eR.functor.obj (e.inverse.obj O.K),
      DerivedCategory.TStructure.t.plus.prop_of_iso w
        ((ProEtale.finiteCoefficientComparison X (ULift.{u + 1} A)).mapDerivedCategoryPlus.obj
          O.L).property⟩
  exact ⟨K, ⟨O.L, ObjectProperty.isoMk _ w⟩⟩

private def recordedOriginFunctor :
    CompactOriginCategory A X ⥤ ProEtale.EtaleOriginDerivedCategory X (ULift.{u + 1} A) where
  obj O := recordedOrigin A X O
  map k := InducedCategory.homMk (ObjectProperty.homMk
    ((ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map
      ((sfIntrinsicDerivedEquivalence X A).inverse.map k.hom)))
  map_id O := by
    apply InducedCategory.hom_ext
    apply ObjectProperty.hom_ext
    change (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map
      ((sfIntrinsicDerivedEquivalence X A).inverse.map (𝟙 O.K)) = 𝟙 _
    exact (congrArg
      (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map
      ((sfIntrinsicDerivedEquivalence X A).inverse.map_id O.K)).trans
        ((ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map_id _)
  map_comp k h := by
    apply InducedCategory.hom_ext
    apply ObjectProperty.hom_ext
    change (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map
      ((sfIntrinsicDerivedEquivalence X A).inverse.map (k.hom ≫ h.hom)) =
        (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map
          ((sfIntrinsicDerivedEquivalence X A).inverse.map k.hom) ≫
        (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map
          ((sfIntrinsicDerivedEquivalence X A).inverse.map h.hom)
    exact (congrArg
      (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map
      ((sfIntrinsicDerivedEquivalence X A).inverse.map_comp k.hom h.hom)).trans
        ((ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).functor.map_comp _ _)

private def recordedFixedModel :
    recordedOriginFunctor A X ⋙ ProEtale.etaleOriginForgetful X (ULift.{u + 1} A) ⋙
        (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).inverse ≅
      compactOriginForget A X ⋙ (sfIntrinsicDerivedEquivalence X A).inverse :=
  NatIso.ofComponents
    (fun O ↦ ((ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).unitIso.app
      ((sfIntrinsicDerivedEquivalence X A).inverse.obj O.K)).symm)
    (fun k ↦ (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).unitIso.inv.naturality
      ((sfIntrinsicDerivedEquivalence X A).inverse.map k.hom))

private def recordedUnit (O : CompactOriginCategory A X) :
    (sfIntrinsicDerivedEquivalence X A).inverse.obj O.K ≅
      ProEtale.refinementFixedObject X (ULift.{u + 1} A) (recordedOrigin A X O) :=
  ((recordedFixedModel A X).app O).symm

private def recordedCompactModel {Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    intrinsicOriginCandidate A c ≅
      (recordedOriginFunctor A X ⋙ ProEtale.etaleOriginForgetful X (ULift.{u + 1} A) ⋙
        (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).inverse) ⋙
          fixedCompact A c ⋙ (sfIntrinsicDerivedEquivalence Y A).functor :=
  candidate_model (sfIntrinsicDerivedEquivalence X A)
    (sfIntrinsicDerivedEquivalence Y A).functor (compactOriginForget A X)
    (recordedOriginFunctor A X ⋙ ProEtale.etaleOriginForgetful X (ULift.{u + 1} A) ⋙
      (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).inverse)
    (recordedFixedModel A X) (sfIntrinsicCompactSupport c A) (fixedCompact A c)
    (fixedCompactModel A c)

private theorem recordedOrigin_witness (O : CompactOriginCategory A X) :
    ProEtale.refinementFixedWitnessIso X (ULift.{u + 1} A) (recordedOrigin A X O) =
      fixedOriginWitness A X O ≪≫ recordedUnit A X O := by
  let e := ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)
  let w := fixedOriginWitness A X O
  let a := ((Functor.mapDerivedCategoryCompIso
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)
    (ProEtale.finiteCoefficientRealization X (ULift.{u + 1} A))).app O.L.obj).symm
  change e.unitIso.app _ ≪≫ e.inverse.mapIso
    (a.symm ≪≫ (Iso.refl _).symm ≪≫ (a ≪≫ e.functor.mapIso w)) = _
  exact cancel_recorded_witness e a w

private theorem recordedProperOpen {Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOriginCategory A X) :
    let a := recordedUnit A X O
    let Jc := (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.i).mapDerivedCategory
    let Jd := (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) d.i).mapDerivedCategory
    let R := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) r.hom).rightDerivedFunctor
    ProEtale.refinementProperOpenIso (ULift.{u + 1} A) r (recordedOrigin A X O) =
      Jd.mapIso a.symm ≪≫ fixedRefinementOpen A r O ≪≫ R.mapIso (Jc.mapIso a) := by
  exact conjugate_witness
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.i).mapDerivedCategory
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) d.i).mapDerivedCategory
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) r.hom).rightDerivedFunctor
    (fixedOriginWitness A X O)
    (recordedUnit A X O)
    (ProEtale.refinementFixedWitnessIso X (ULift.{u + 1} A) (recordedOrigin A X O))
    (recordedOrigin_witness A X O)
    (ProEtale.properOpenProEtaleIso (ULift.{u + 1} A) r.hom c.i d.i r.i_hom O.L)

private def recordedRefinementCore {Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOriginCategory A X) :=
  let K := (sfIntrinsicDerivedEquivalence X A).inverse.obj O.K
  let Jc := (ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.i).mapDerivedCategory
  let P := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) d.g).rightDerivedFunctor
  let z₁ := eqToIso (congrArg
    (fun g ↦ (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).rightDerivedFunctor)
    r.hom_g.symm)
  let z₂ := ProEtale.finiteDirectImageComposition (ULift.{u + 1} A) r.hom d.g
  z₁.app (Jc.obj K) ≪≫ z₂.app (Jc.obj K) ≪≫ P.mapIso (fixedRefinementOpen A r O).symm

private theorem recordedFixedRefinement {Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOriginCategory A X) :
    let a := recordedUnit A X O
    ProEtale.refinementComparisonAtWitness (ULift.{u + 1} A) r (recordedOrigin A X O) =
      (fixedCompact A c).mapIso a.symm ≪≫ recordedRefinementCore A X r O ≪≫
        (fixedCompact A d).mapIso a := by
  let Jc := (ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.i).mapDerivedCategory
  let Jd := (ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) d.i).mapDerivedCategory
  let R := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) r.hom).rightDerivedFunctor
  let P := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) d.g).rightDerivedFunctor
  let S := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.g).rightDerivedFunctor
  let T := (ProEtale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (r.hom ≫ d.g)).rightDerivedFunctor
  let z₁ := eqToIso (congrArg
    (fun g ↦ (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).rightDerivedFunctor)
    r.hom_g.symm)
  let z₂ := ProEtale.finiteDirectImageComposition (ULift.{u + 1} A) r.hom d.g
  dsimp only [ProEtale.refinementComparisonAtWitness, recordedRefinementCore, fixedCompact]
  rw [recordedProperOpen]
  exact conjugate_refinement_pair Jc Jd R P S T z₁ z₂ (recordedUnit A X O)
    (fixedRefinementOpen A r O)

private theorem recordedCompactModel_app {Y : Scheme.{u}} {f : X ⟶ Y}
    (b : Compactification f) (O : CompactOriginCategory A X) :
    let e := sfIntrinsicDerivedEquivalence X A
    let a := recordedUnit A X O
    (recordedCompactModel A X b).app O =
      ((sfIntrinsicCompactSupport b A).mapIso (e.counitIso.app O.K)).symm ≪≫
        (fixedCompactModel A b).app (e.inverse.obj O.K) ≪≫
        (sfIntrinsicDerivedEquivalence Y A).functor.mapIso ((fixedCompact A b).mapIso a) := by
  exact candidate_model_app (sfIntrinsicDerivedEquivalence X A)
    (sfIntrinsicDerivedEquivalence Y A).functor (compactOriginForget A X)
    (recordedOriginFunctor A X ⋙ ProEtale.etaleOriginForgetful X (ULift.{u + 1} A) ⋙
      (ProEtale.refinementCoefficientEquivalence X (ULift.{u + 1} A)).inverse)
    (recordedFixedModel A X) (sfIntrinsicCompactSupport b A) (fixedCompact A b)
    (fixedCompactModel A b) O

private theorem recordedCore_intrinsic {Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOriginCategory A X) :
    let e := sfIntrinsicDerivedEquivalence X A
    let q := (sfIntrinsicDerivedEquivalence Y A).functor
    let K := e.inverse.obj O.K
    ((sfIntrinsicCompactSupport c A).mapIso (e.counitIso.app O.K)).symm ≪≫
        (fixedCompactModel A c).app K ≪≫ q.mapIso (recordedRefinementCore A X r O) ≪≫
        ((fixedCompactModel A d).app K).symm ≪≫
        (sfIntrinsicCompactSupport d A).mapIso (e.counitIso.app O.K) =
      intrinsicRefinement A r O := by
  dsimp only [intrinsicRefinement, recordedRefinementCore]
  rfl

private theorem recordedRefinement {Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOriginCategory A X) :
    (recordedCompactModel A X c).app O ≪≫
        (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
          (ProEtale.refinementComparisonAtWitness (ULift.{u + 1} A) r (recordedOrigin A X O)) ≪≫
        ((recordedCompactModel A X d).app O).symm = intrinsicRefinement A r O := by
  let e := sfIntrinsicDerivedEquivalence X A
  let q := (sfIntrinsicDerivedEquivalence Y A).functor
  let a := recordedUnit A X O
  exact (cancel_coordinate_units_of q (fixedCompact A c) (fixedCompact A d) a
    (recordedRefinementCore A X r O)
    ((sfIntrinsicCompactSupport c A).mapIso (e.counitIso.app O.K)).symm
    ((fixedCompactModel A c).app (e.inverse.obj O.K))
    ((sfIntrinsicCompactSupport d A).mapIso (e.counitIso.app O.K)).symm
    ((fixedCompactModel A d).app (e.inverse.obj O.K))
    (ProEtale.refinementComparisonAtWitness (ULift.{u + 1} A) r (recordedOrigin A X O))
    ((recordedCompactModel A X c).app O) ((recordedCompactModel A X d).app O)
    (recordedFixedRefinement A X r O) (recordedCompactModel_app A X c O)
    (recordedCompactModel_app A X d O)).trans (recordedCore_intrinsic A X r O)

end CoherenceCoordinates

section Coherence
variable (K₀ : Type u) [Field K₀]
  (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : K₀))
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [fo : f.IsOver (Spec (.of K₀))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include hl xo yo xft xqc yft yqc fo fs fft fqc
/-- The canonical refinement maps are natural, unital and transitive; finite
families have common refinements and comparisons are independent of all choices.
Source: blueprint prop-compactification-coherence, proof paragraphs 1--4
(blueprint: def-weil-frobenius-witnessed-compactification).
Proof: proper-open comparison is natural for maps of etale antecedents. Full
faithfulness of etale comparison transports this naturality to every ambient
map between witnessed objects and proves witness independence. Its identity
and composition laws, together with the proper compositor, give the refinement
laws. Over a field the compactification category is cofiltered. Take a common
refinement and form theta(d,c1) inverse followed by theta(d,c2). To compare
two choices, refine both and equalize their arrows; transitivity cancels the
extra factors. A common refinement for three compactifications proves the
cocycle. Nonemptiness handles the empty finite family. Transport through the
explicit fixedCompactModel preserves every equality. -/
theorem intrinsicCompactificationCoherence :
    let A := Padic.coefficientExtensionRing l E n
    letI := Padic.finite_coefficientExtensionRing l E n hn
    ∃ theta : ∀ (c d : Compactification f) (_r : c ⟶ d),
        intrinsicOriginCandidate A c ≅ intrinsicOriginCandidate A d,
      (∀ (c d : Compactification f) (r : c ⟶ d) (O : CompactOriginCategory A X),
        (theta c d r).app O = intrinsicRefinement A r O) ∧
      (∀ c, theta c c (𝟙 c) = Iso.refl _) ∧
      (∀ (c d e : Compactification f) (r : c ⟶ d) (s : d ⟶ e),
        theta c e (r ≫ s) = theta c d r ≪≫ theta d e s) ∧
      (∀ (m : ℕ) (c : Fin m → Compactification f),
        ∃ d : Compactification f, ∀ i : Fin m, Nonempty (d ⟶ c i)) ∧
      ∃! comparison : ∀ c d : Compactification f,
          intrinsicOriginCandidate A c ≅ intrinsicOriginCandidate A d,
        ∀ (c d b : Compactification f) (r : b ⟶ c) (s : b ⟶ d),
          comparison c d = (theta b c r).symm ≪≫ theta b d s := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  let := Padic.finite_coefficientExtensionRing l E n hn
  let F := recordedOriginFunctor A X
  let q := (sfIntrinsicDerivedEquivalence Y A).functor
  let B : ∀ c : Compactification f,
      intrinsicOriginCandidate A c ≅
        F ⋙ ProEtale.compactificationOriginCandidate l E n hn c ⋙ q :=
    fun c ↦ recordedCompactModel A X c
  obtain ⟨theta, htheta, hid, hcomp, hfinite, comparison, hcomparison, _hcocycle⟩ :=
    ProEtale.compactification_coherence K₀ l hl E n hn f
  obtain ⟨theta', htheta', hid', hcomp', hcomparison'⟩ :=
    transport_coherence F q
      (fun c ↦ ProEtale.compactificationOriginCandidate l E n hn c)
      (fun c ↦ intrinsicOriginCandidate A c) B theta hid hcomp hfinite comparison hcomparison
  refine ⟨theta', ?_, hid', hcomp', hfinite, hcomparison'⟩
  intro c d r O
  exact (htheta' c d r O).trans
    ((congrArg (fun t ↦ (B c).app O ≪≫ q.mapIso t ≪≫ ((B d).app O).symm)
      (htheta c d r (F.obj O))).trans (recordedRefinement A X r O))

end Coherence

variable (A : Type u) [CommRing A] [Finite A]

section Geometry
variable (D : FiniteFieldDatum.{u})

/-- The base change of the given model morphism, with the dependency's chosen fibers.
Source: blueprint `def:weil-direct-image-object`
(blueprint: def-weil-frobenius-witnessed-compactification). -/
abbrev fiberMap {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  zlFiberMap D f₀

/-- The coefficient action of geometric field Frobenius, including non-finite-type models.
Source: Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-witnessed-compactification). -/
abbrev galois (X₀ : Over (Spec (.of D.k₀))) :=
  D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _)

end Geometry

section EtaleOrigin
variable (A : Type u) [CommRing A] [Finite A]

end EtaleOrigin

section CompactificationTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c d : Compactification f)
  (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
  (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)

variable (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

end CompactificationTransport
end FiniteGeometry

end WeilConjectures.FrobeniusExchange
