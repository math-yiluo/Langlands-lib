/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all WeilConjectures.SixFunctors.CanonicalOpenRestriction.OpenRestrictionGoodComplex
import all WeilConjectures.SmoothPurity.Integral.Open.IntegralOpenScalarRestrictionComparison
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionModels
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IsomorphismOrdinaryCompletionChain
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.SixFunctors.OpenRoosRestriction.OpenRestrictionQuotientTower
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison

/-! # Descent of the normalized open Roos comparison

Source: Stacks Project, proetale.tex, Tag 099N (2),(5), and Tag 0941.
(blueprint: lem-sf-open-roos-restriction-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance_reducible] WeilConjectures.IntegralOnSlice.Site
  WeilConjectures.IntegralOnSlice.topology WeilConjectures.IntegralOnSlice.restrict
  WeilConjectures.IntegralOnSlice.ring
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.IntegralOnSlice.completion WeilConjectures.IntegralOnSlice.completionUnit
  WeilConjectures.IntegralOnSlice.completionComparison WeilConjectures.IntegralOnSlice.roosUnit
  WeilConjectures.IntegralOnSlice.tower WeilConjectures.IntegralOnSlice.Good

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenRoosRestriction

private theorem iso_trans_cancel {A : Type*} [Category* A] {X Y Z H : A}
    (c : X ≅ Y) (d : Y ≅ Z) (b : H ≅ Z) :
    (c ≪≫ d ≪≫ b.symm).hom ≫ b.hom = c.hom ≫ d.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem map_factor_normalization
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (Q : A ⥤ B) (S : B ⥤ D) (G : A ⥤ C) (R : C ⥤ D)
    (κ : Q ⋙ S ≅ G ⋙ R) {P Z : A} {H : B} {L : C}
    (u : Q.obj P ⟶ H) (v : H ⟶ Q.obj Z) (γ : P ⟶ Z)
    (h : u ≫ v = Q.map γ) (r : G.obj Z ⟶ L) :
    S.map u ≫ (S.map v ≫ κ.hom.app Z ≫ R.map r) =
      κ.hom.app P ≫ R.map (G.map γ ≫ r) := by
  have hn : S.map (Q.map γ) ≫ κ.hom.app Z =
      κ.hom.app P ≫ R.map (G.map γ) := κ.hom.naturality γ
  rw [← Category.assoc, ← S.map_comp, h, ← Category.assoc,
    hn, Category.assoc, ← R.map_comp]

private theorem descend_unit
    {A : Type*} {B : Type*} {C : Type*}
    [Category* A] [Category* B] [Category* C]
    (q : A ⥤ B) (ff : ((Functor.whiskeringLeft A B C).obj q).FullyFaithful)
    (CW : B ⥤ B) (CV : C ⥤ C) (S : B ⥤ C)
    (u : 𝟭 B ⟶ CW) (v : 𝟭 C ⟶ CV) (R T : A ⥤ C)
    (c : q ⋙ CW ⋙ S ≅ R) (b : q ⋙ S ⋙ CV ≅ T) (δ : R ≅ T)
    (h : ∀ P, (S.map (u.app (q.obj P)) ≫ c.hom.app P) ≫ δ.hom.app P =
      v.app (S.obj (q.obj P)) ≫ b.hom.app P) :
    ∃ ρ : CW ⋙ S ≅ S ⋙ CV,
      ∀ H, S.map (u.app H) ≫ ρ.hom.app H = v.app (S.obj H) := by
  let a := c ≪≫ δ ≪≫ b.symm
  let ρ := ff.preimageIso a
  have hρ (P : A) : ρ.hom.app (q.obj P) = a.hom.app P :=
    NatTrans.congr_app (ff.map_preimage a.hom) P
  refine ⟨ρ, ?_⟩
  have hu : Functor.whiskerRight u S ≫ ρ.hom = Functor.whiskerLeft S v := by
    apply ff.map_injective
    ext P
    change S.map (u.app (q.obj P)) ≫ ρ.hom.app (q.obj P) = v.app (S.obj (q.obj P))
    apply (cancel_mono (b.hom.app P)).1
    rw [hρ, Category.assoc]
    have ha := NatTrans.congr_app (iso_trans_cancel c δ b) P
    change a.hom.app P ≫ b.hom.app P = c.hom.app P ≫ δ.hom.app P at ha
    rw [ha, ← Category.assoc]
    exact h P
  exact fun H ↦ NatTrans.congr_app hu H

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

/-- Exactness inherited from the actual ordinary right adjunction.
Source: Stacks 03DJ (blueprint: lem-sf-open-roos-restriction-descent). -/
local instance descentRestrictionLimits :
    PreservesFiniteLimits (IntegralOpenReduction.restriction l E e o) := by
  let : PreservesLimitsOfSize.{0, 0} (IntegralOpenReduction.restriction l E e o) :=
    (IntegralOpenReduction.ordinaryAdjunction l E e o).rightAdjoint_preservesLimits
  infer_instance

/-- Exactness inherited from slice restriction and the coefficient equivalence.
Source: Stacks 03DJ (blueprint: lem-sf-open-roos-restriction-descent). -/
local instance descentRestrictionColimits :
    PreservesFiniteColimits (IntegralOpenReduction.restriction l E e o) := by
  let hL : PreservesFiniteColimits (SheafOfModules.localizedSystemRestriction.{t+1, t,
      max u (t+1)} (completedIntegralCommRingSheafUnrestricted l E W)
      (IntegralOpenReduction.openObject e)) :=
    SheafOfModules.localizedSystemRestrictionColimits _ _
  let : PreservesColimitsOfSize.{0, 0} o.integral.inverse :=
    o.integral.symm.toAdjunction.leftAdjoint_preservesColimits
  let hI : PreservesFiniteColimits o.integral.inverse := inferInstance
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ hL hI

private theorem completionUnit_normalization (X : Scheme.{t})
    (P : (IntegralOnSlice.Good l E X none).FullSubcategory) :
    (IntegralOnSlice.completionUnit l E X none).app
        ((IntegralOnSlice.qGood l E X none).obj P) ≫
      (IntegralOnSlice.completionComparison l E X none).hom.app P =
        DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none P.obj) := by
  unfold IntegralOnSlice.completionUnit
  exact (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec P

/-- The strict restriction comparison descends to the published completion and its
actual quotient-augmentation unit, for any normalized presentation of open operations.

Source: Stacks Project, Tag 099N (2),(5), Tag 0941; the strict tensor comparison of
Tags 0G7E and 07A4 (blueprint: lem-sf-open-roos-restriction-descent).

Proof: the finite and completed coefficient maps are the canonical slice
isomorphisms by their normalization equalities, and naturality of systemMap gives
the finite transition square. Restriction preserves the uniformizer endomorphism
and its cokernel. The unique cokernel comparisons therefore identify the ordinary
quotient towers with their actual quotient augmentations. Restriction is a right
adjoint, so it preserves countable products and the specified scalarRoosMap is
invertible. Compose this map with the published completionComparison on good
representatives to obtain c. The tower isomorphism and the good-representative
comparison on V then give the full completion comparison. Fully faithful
whiskering along qGood descends it to derived objects. The generic augmented Roos
map lemma identifies the first coordinates with the quotient units and the shifted
coordinates with zero. The completionUnit normalization gives the unit square on
good representatives, and faithfulness gives it on all derived objects. All maps
are determined by these normalizations, including for the empty open. -/
theorem restrictionDescent
    (_d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (_hd : _d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) :
(∀ n : ℕ, IsIso (o.finiteMap n)) ∧ IsIso o.completedMap ∧
      (∀ n : ℕ,
        o.finiteMap (n + 1) ≫
          ((IntegralOpenReduction.sliceSite e).sheafPushforwardContinuous
            CommRingCat.{max u (t + 1)} ((ProEt.topology W).over
              (IntegralOpenReduction.openObject e)) (ProEt.topology V)).map
                (coefficientSequenceCommRingTransition l E V n) =
        ((ProEt.topology W).overPullback CommRingCat.{max u (t + 1)}
          (IntegralOpenReduction.openObject e)).map
            (coefficientSequenceCommRingTransition l E W n) ≫ o.finiteMap n) ∧
    ∃ (rho : IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o ≅
        IntegralOpenReduction.star l E e o ⋙ IntegralOnSlice.completion l E V none)
      (c : IntegralOnSlice.qGood l E W none ⋙
          (IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o) ≅
        (IntegralOnSlice.Good l E W none).ι ⋙ IntegralOnSlice.tower l E W none ⋙
          (Functor.whiskeringRight ℕᵒᵖ _ _).obj
            ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)) ⋙
          integralOperationsRoosFunctor ⋙ DerivedCategory.Q),
      (∀ H : IntegralOnSlice.D l E W none,
        (IntegralOpenReduction.star l E e o).map
            ((IntegralOnSlice.completionUnit l E W none).app H) ≫ rho.hom.app H =
          (IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H)) ∧
      (∀ P : (IntegralOnSlice.Good l E W none).FullSubcategory,
        (IntegralOpenReduction.star l E e o).map
            ((IntegralOnSlice.completionUnit l E W none).app (DerivedCategory.Q.obj P.obj)) ≫
            c.hom.app P =
          (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map
              (((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)).map
                  (IntegralOnSlice.roosUnit l E W none P.obj) ≫
                scalarRoosMap (IntegralOpenReduction.restriction l E e o)
                  ((IntegralOnSlice.tower l E W none).obj P.obj))) := by
  classical
  have hf (n : ℕ) : IsIso (o.finiteMap n) := by
    rw [CanonicalOpenRestriction.finiteMap_eq l E e o n]
    infer_instance
  have hc : IsIso o.completedMap := by
    rw [CanonicalOpenRestriction.completedMap_eq l E e o]
    infer_instance
  refine ⟨hf, hc, ?_, ?_⟩
  · exact fun n ↦ finiteTransportSquare l E e o n
  · let F : IntegralOnSlice.Mod l E W none ⥤ IntegralOnSlice.Mod l E V none :=
      IntegralOpenReduction.restriction l E e o
    let : F.Additive := IntegralOpenReduction.restrictionAdditive l E e o
    let G := F.mapHomologicalComplex (.up ℤ)
    let S : IntegralOnSlice.D l E W none ⥤ IntegralOnSlice.D l E V none :=
      IntegralOpenReduction.star l E e o
    let I := (IntegralOnSlice.Good l E W none).ι
    let q := IntegralOnSlice.qGood l E W none
    let T := IntegralOnSlice.tower l E W none
    let U := IntegralOnSlice.tower l E V none
    let : PreservesLimitsOfSize.{0, 0} F :=
      (IntegralOpenReduction.ordinaryAdjunction l E e o).rightAdjoint_preservesLimits
    let : PreservesFiniteLimits F := inferInstance
    let : PreservesFiniteColimits F := descentRestrictionColimits l E e o
    let : PreservesLimitsOfShape (Discrete ℕ) F :=
      (IntegralOpenReduction.ordinaryAdjunction l E e o).rightAdjoint_preservesLimits
        |>.preservesLimitsOfShape
    let κ : DerivedCategory.Q ⋙ S ≅ G ⋙ DerivedCategory.Q := F.mapDerivedCategoryFactors
    obtain ⟨τ₀, hτ₀⟩ := quotientTower l E e o
    let τ : T ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ≅ G ⋙ U := τ₀
    have hτ (P : IntegralOnSlice.Cx l E W none) (n : ℕ) :
        G.map (((IntegralOnSlice.augmentation l E W none).app P).app (op n)) ≫
            (τ.hom.app P).app (op n) =
          ((IntegralOnSlice.augmentation l E V none).app (G.obj P)).app (op n) := hτ₀ P n
    let χ : (T ⋙ integralOperationsRoosFunctor) ⋙ G ≅
        T ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ⋙ integralOperationsRoosFunctor :=
      NatIso.ofComponents
        (fun P ↦ @asIso _ _ _ _ (scalarRoosMap F (T.obj P))
          (IntegralOnSlice.restrictionRoosIsIso F _)) (by
        intro P Q a
        exact podReindexingRoosNaturality F (T.map a))
    let c : q ⋙ (IntegralOnSlice.completion l E W none ⋙ S) ≅
        I ⋙ T ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ⋙
          integralOperationsRoosFunctor ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerRight (IntegralOnSlice.completionComparison l E W none) S ≪≫
        Functor.isoWhiskerLeft (I ⋙ T ⋙ integralOperationsRoosFunctor) κ ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft I χ) DerivedCategory.Q
    have hgood (P : (IntegralOnSlice.Good l E W none).FullSubcategory) :
        IntegralOnSlice.Good l E V none (G.obj P.obj) := by
      unfold IntegralOnSlice.Good
      have hp := P.property
      unfold IntegralOnSlice.Good at hp
      exact CanonicalOpenRestriction.restriction_preservesGood l E e o P.obj hp
    let k := (IntegralOnSlice.Good l E V none).lift (I ⋙ G) hgood
    let η : q ⋙ S ≅ k ⋙ IntegralOnSlice.qGood l E V none :=
      Functor.isoWhiskerLeft I κ
    let b : q ⋙ (S ⋙ IntegralOnSlice.completion l E V none) ≅
        I ⋙ G ⋙ U ⋙ integralOperationsRoosFunctor ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerRight η (IntegralOnSlice.completion l E V none) ≪≫
        Functor.isoWhiskerLeft k (IntegralOnSlice.completionComparison l E V none)
    let z : I ⋙ T ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ≅ I ⋙ G ⋙ U :=
      Functor.isoWhiskerLeft I τ
    let δ : I ⋙ T ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q ≅
        I ⋙ G ⋙ U ⋙ integralOperationsRoosFunctor ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight z integralOperationsRoosFunctor) DerivedCategory.Q
    let : q.IsLocalization
        ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E W none) (.up ℤ)).inverseImage I) :=
      IntegralOnSlice.goodLocalization l E W none
    let ff := Localization.fullyFaithfulWhiskeringLeft q
      ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E W none) (.up ℤ)).inverseImage I)
      (IntegralOnSlice.D l E V none)
    have hrep (P : (IntegralOnSlice.Good l E W none).FullSubcategory) :
        S.map ((IntegralOnSlice.completionUnit l E W none).app (q.obj P)) ≫
            c.hom.app P =
          κ.hom.app P.obj ≫ DerivedCategory.Q.map
            (G.map (IntegralOnSlice.roosUnit l E W none P.obj) ≫
              scalarRoosMap F (T.obj P.obj)) := by
      exact map_factor_normalization DerivedCategory.Q S G DerivedCategory.Q κ
        ((IntegralOnSlice.completionUnit l E W none).app (q.obj P))
        ((IntegralOnSlice.completionComparison l E W none).hom.app P)
        (IntegralOnSlice.roosUnit l E W none P.obj)
        (completionUnit_normalization l E W P) (scalarRoosMap F (T.obj P.obj))
    have hchain (P : IntegralOnSlice.Cx l E W none) :
        G.map (IntegralOnSlice.roosUnit l E W none P) ≫
            scalarRoosMap F (T.obj P) ≫
            integralOperationsRoosMap (τ.hom.app P) =
          IntegralOnSlice.roosUnit l E V none (G.obj P) := by
      have h := IntegralOnSlice.augmentedRoosMap F P (G.obj P) (T.obj P) (U.obj (G.obj P))
        (𝟙 _) (τ.hom.app P) (IntegralOnSlice.roosUnit l E W none P)
        (IntegralOnSlice.roosUnit l E V none (G.obj P)) ?_ ?_ ?_
      · simpa only [Category.id_comp, Functor.comp_obj] using h
      · intro n
        have hγ : IntegralOnSlice.roosUnit l E W none P ≫
            CochainComplex.mappingCocone.fst (scalarRoosBoundary (T.obj P)) ≫
              Pi.π (fun n : ℕ ↦ (T.obj P).obj (op n)) n =
            ((IntegralOnSlice.augmentation l E W none).app P).app (op n) := by
          erw [← Category.assoc, IntegralAmbient.roosUnit_fst]
          exact Pi.lift_comp_π _ _
        have hθ : IntegralOnSlice.roosUnit l E V none (G.obj P) ≫
            CochainComplex.mappingCocone.fst (scalarRoosBoundary (U.obj (G.obj P))) ≫
              Pi.π (fun n : ℕ ↦ (U.obj (G.obj P)).obj (op n)) n =
            ((IntegralOnSlice.augmentation l E V none).app (G.obj P)).app (op n) := by
          erw [← Category.assoc, IntegralAmbient.roosUnit_fst]
          exact Pi.lift_comp_π _ _
        erw [hγ, hθ, Category.id_comp]
        exact hτ P n
      · intro i
        exact IntegralAmbient.roosUnit_snd l E W P i (i - 1) (by omega)
      · intro i
        exact IntegralAmbient.roosUnit_snd l E V (G.obj P) i (i - 1) (by omega)
    have hunit (P : (IntegralOnSlice.Good l E W none).FullSubcategory) :
        (S.map ((IntegralOnSlice.completionUnit l E W none).app (q.obj P)) ≫
            c.hom.app P) ≫ δ.hom.app P =
          (IntegralOnSlice.completionUnit l E V none).app (S.obj (q.obj P)) ≫
            b.hom.app P := by
      change (S.map ((IntegralOnSlice.completionUnit l E W none).app (q.obj P)) ≫
          c.hom.app P) ≫
        DerivedCategory.Q.map (integralOperationsRoosMap (τ.hom.app P.obj)) = _
      erw [hrep, Category.assoc, ← DerivedCategory.Q.map_comp, Category.assoc, hchain]
      change _ = (IntegralOnSlice.completionUnit l E V none).app (S.obj (q.obj P)) ≫
        ((IntegralOnSlice.completion l E V none).map (η.hom.app P) ≫
          (IntegralOnSlice.completionComparison l E V none).hom.app (k.obj P))
      erw [← Category.assoc, ← (IntegralOnSlice.completionUnit l E V none).naturality]
      erw [Category.assoc, completionUnit_normalization l E V (k.obj P)]
      rfl
    obtain ⟨ρ, hρ⟩ := descend_unit q ff (IntegralOnSlice.completion l E W none)
      (IntegralOnSlice.completion l E V none) S
      (IntegralOnSlice.completionUnit l E W none) (IntegralOnSlice.completionUnit l E V none)
      _ _ c b δ hunit
    exact ⟨ρ, c, hρ, hrep⟩

end WeilConjectures.OpenRoosRestriction
