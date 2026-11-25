/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientCompletionRoosTransport
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Nat.Prime.Infinite
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransport

/-! # Completeness under normalized integral coefficient transport

These coefficient equivalences and completeness comparisons are independent of
bounded constructibility and the stratified-perfect characterization.
Source: Stacks 099N; Bhatt--Scholze, Section 6.5
(blueprint: def-pur-completed-coefficient-presentation-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section CoefficientPresentation
variable (W : Scheme.{u})

end CoefficientPresentation

/-- The actual coefficient transport on ordinary module sheaves.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
abbrev purOrdinaryCoefficientModel (W : Scheme.{u}) :
    pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)) ⥤
      integralTowerModules.{u, u} l E W :=
  pbcRestrict (purCoefficientIso l E W).inv

/-- Additivity of the specified exact coefficient restriction.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_additive (W : Scheme.{u}) :
    (purOrdinaryCoefficientModel l E W).Additive := pbcRestrict_additive _

/-- Exactness of the specified coefficient restriction on finite limits.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (purOrdinaryCoefficientModel l E W) := pbcRestrict_limits _

/-- Exactness of the specified coefficient restriction on finite colimits.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (purOrdinaryCoefficientModel l E W) := pbcRestrict_colimits _

/-- The ordinary restriction round trip is the identity on every section.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: the CommRing lift forgets to the landed ring isomorphism. Restricting along
its inverse and then its forward map restores the same scalar action. Identity
section functions are linear and natural, with identity inverses. Sections detect
module morphisms, so this normalization determines the isomorphism uniquely. -/
theorem purOrdinaryCoefficientRoundTrip_existsUnique (W : Scheme.{u}) :
    ∃! e : purOrdinaryCoefficientModel l E W ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison W l E).hom ≅
      𝟭 (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))),
      ∀ (M : pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
        (U : W.ProEtᵒᵖ) (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  let e := purCoefficientIso l E W
  have he : (adicLisseForget W).mapIso e =
      integralDetailedCoefficientComparison W l E :=
    (purCoefficientIso_existsUnique l E W).exists.choose_spec
  rw [← he]
  obtain ⟨c, hc, _⟩ := pbcRestrictComp_exists e.hom e.inv (𝟙 _) e.hom_inv_id
  let R := pbcAdicCompletion W (pbcIntegralDatum l E)
  let dM (M : pbcModules W R) : (pbcRestrict (𝟙 R)).obj M ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))
  let d : pbcRestrict (𝟙 R) ≅ 𝟭 _ :=
    NatIso.ofComponents dM (fun f ↦ by ext U x; rfl)
  have hd : ∀ M U x, (d.hom.app M).val.app U x = x := by intros; rfl
  refine ⟨c ≪≫ d, ?_, ?_⟩
  · intro M U x
    change (d.hom.app M).val.app U ((c.hom.app M).val.app U x) = x
    rw [hc, hd]
  · intro e' he'
    apply Iso.ext
    ext M U x
    change (e'.hom.app M).val.app U x =
      (d.hom.app M).val.app U ((c.hom.app M).val.app U x)
    rw [he', hc, hd]

/-- The uniquely section-normalized ordinary restriction round trip.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purOrdinaryCoefficientRoundTrip (W : Scheme.{u}) :=
  (purOrdinaryCoefficientRoundTrip_existsUnique l E W).exists.choose

section RestrictionEquivalence
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{u + 1}}

private def restrictionRoundTrip (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle (c : R ≅ S) (M : SheafOfModules.{u + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private def restrictionEquivalence (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

private theorem restriction_isEquivalence (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
  (restrictionEquivalence c).isEquivalence_functor

private theorem restrictionEquivalence_unit (c : R ≅ S)
    (M : SheafOfModules.{u + 1} S) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((restrictionEquivalence c).unit.app M).val.app U x = x := by
  rfl

end RestrictionEquivalence

/-- The landed integralDetailedTransport is an equivalence.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: restriction along the inverse coefficient ring isomorphism is an exact
inverse to the landed restriction functor. Both ordinary round trips are identity
on sections. Termwise round trips descend through derived localization, proving
full faithfulness and essential surjectivity of the existing functor. -/
@[instance] theorem purDetailedTransport_isEquivalence (W : Scheme.{u}) :
    (integralDetailedTransport W l E).IsEquivalence := by
  have := restriction_isEquivalence (integralDetailedCoefficientComparison W l E)
  have := (integralDetailedCoefficientRestriction_exact W l E).1
  have := (integralDetailedCoefficientRestriction_exact W l E).2
  exact Functor.isEquivalence_mapDerivedCategory _

/-- The exact restriction round trip, descended by the published localization API.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purDerivedCoefficientRoundTrip (W : Scheme.{u}) :
    pbcDerivedRestrict (purCoefficientIso l E W).inv ⋙
      integralDetailedTransport W l E ≅
        𝟭 (PbcCompletedDerived W (pbcIntegralDatum l E)) :=
  have := (integralDetailedCoefficientRestriction_exact W l E).1
  have := (integralDetailedCoefficientRestriction_exact W l E).2
  (Functor.mapDerivedCategoryCompIso (purOrdinaryCoefficientModel l E W)
    (SheafOfModules.restrictScalars.{u + 1}
      (integralDetailedCoefficientComparison W l E).hom)) ≪≫
    Functor.mapDerivedCategoryNatIso (purOrdinaryCoefficientRoundTrip l E W) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- Reuse the inverse of the landed transport. changeFunctor gives its explicit
CommRing restriction model via the identity-on-sections round trip; the inverse
functor remains exactly integralDetailedTransport.
Source: Stacks 099N (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCoefficientModel (W : Scheme.{u}) :
    PbcCompletedDerived W (pbcIntegralDatum l E) ≌
      DerivedCategory (integralTowerModules.{u, u} l E W) :=
  (integralDetailedTransport W l E).asEquivalence.symm.changeFunctor
    ((Iso.isoCompInverse
      (H := (integralDetailedTransport W l E).asEquivalence)
      (purDerivedCoefficientRoundTrip l E W) ≪≫ Functor.leftUnitor _).symm)

/-- Completeness alone is invariant under the existing coefficient transport.
Source: Stacks 099N, Bhatt--Scholze 6.5
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: normalized coefficient projections identify the finite reductions and
quotient units. Exact restriction preserves the product and Roos descriptions of
the completion unit, so its being invertible is unchanged. The recorded intrinsic
and slice completeness predicates test this same unit, without geometric bounds. -/
theorem purCoefficientModel_predicates (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E) K ↔
      IntegralOnSlice.IsComplete l E W none ((purCoefficientModel l E W).functor.obj K)) ∧
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E) K ↔
      IsSfDerivedComplete l E W ((purCoefficientModel l E W).functor.obj K)) := by
  let d := pbcIntegralDatum l E
  let Φ := purCoefficientModel l E W
  let C := pbcActualCompletion d W
  let η := pbcActualCompletionUnit d W
  let P : ObjectProperty (PbcCompletedDerived W d) := PbcIsIntrinsicallyComplete W d
  have hP : P.IsClosedUnderIsomorphisms := by
    constructor
    intro A B e hA
    obtain ⟨r, f, hf, A', eA, hA'⟩ := hA
    refine ⟨r, f, hf, A', eA ≪≫
      (pbcDerivedExtend (pbcCompletedComparison W d).inv).mapIso e, ?_⟩
    change IsIso (eA.inv ≫ _) at hA'
    have hu := (isIso_comp_left_iff eA.inv _).mp hA'
    change IsIso ((_ ≫ eA.inv) ≫ _)
    infer_instance
  have := hP
  obtain ⟨hp, p, δ, ht, hu⟩ := completedCoefficientCompletionRoosTransport l E W
    (purCoefficientIso l E W) (purCoefficientIso_existsUnique l E W).exists.choose_spec K
  have := hp
  have hsf : P K ↔ IsSfDerivedComplete l E W (Φ.functor.obj K) := by
    constructor
    · intro hK
      let adj := Adjunction.ofIsRightAdjoint (ObjectProperty.ι P)
      have : IsIso (η.app K) :=
        adj.isIso_unit_app_of_iso (X := ⟨K, hK⟩) (Iso.refl K)
      let i := asIso (Φ.functor.map (η.app K))
      let δ' := δ ≫ (shiftFunctor _ (1 : ℤ)).map i.inv
      refine ⟨hp, δ', ?_⟩
      let T := Pretriangulated.Triangle.mk
        (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app (Φ.functor.obj K)))
        (towerTransitionEndomorphism
          (fun n ↦ (sfDerivedReductionTransition l E W n).app (Φ.functor.obj K))) δ'
      let T' := Pretriangulated.Triangle.mk p
        (towerTransitionEndomorphism
          (fun n ↦ (sfDerivedReductionTransition l E W n).app (Φ.functor.obj K))) δ
      let e : T ≅ T' := Pretriangulated.Triangle.isoMk T T' i (Iso.refl _) (Iso.refl _)
        (by
          change (Pi.lift _) ≫ 𝟙 _ = i.hom ≫ p
          exact (Category.comp_id _).trans hu.symm)
        (by
          change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
          exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by
          change (δ ≫ (shiftFunctor _ (1 : ℤ)).map i.inv) ≫
            (shiftFunctor _ (1 : ℤ)).map i.hom = 𝟙 _ ≫ δ
          rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
            CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])
      exact (Pretriangulated.distinguished_iff_of_iso e).mpr ht
    · rintro ⟨hp', δ', ht'⟩
      have := hp'
      let T := Pretriangulated.Triangle.mk
        (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app (Φ.functor.obj K)))
        (towerTransitionEndomorphism
          (fun n ↦ (sfDerivedReductionTransition l E W n).app (Φ.functor.obj K))) δ'
      let T' := Pretriangulated.Triangle.mk p
        (towerTransitionEndomorphism
          (fun n ↦ (sfDerivedReductionTransition l E W n).app (Φ.functor.obj K))) δ
      let e := Pretriangulated.isoTriangleOfIso₁₂ T.rotate T'.rotate
        (Pretriangulated.rot_of_distTriang T ht')
        (Pretriangulated.rot_of_distTriang T' ht) (Iso.refl _) (Iso.refl _)
        (by
          change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
          exact (Category.comp_id _).trans (Category.id_comp _).symm)
      let i : Φ.functor.obj K ≅ Φ.functor.obj (C.obj K) :=
        (shiftFunctor _ (1 : ℤ)).preimageIso (Pretriangulated.Triangle.π₃.mapIso e)
      let j : K ≅ C.obj K := Φ.functor.preimageIso i
      exact ObjectProperty.prop_of_iso P j.symm
        (((ObjectProperty.ι P).leftAdjoint.obj K).property)
  have hlegacy : IsSfDerivedComplete l E W (Φ.functor.obj K) ↔
      IntegralOnSlice.IsComplete l E W none (Φ.functor.obj K) := by
    change IsSfDerivedComplete l E W (Φ.functor.obj K) ↔
      ∃ (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p),
        IsDerivedComplete l E W D hl (Φ.functor.obj K)
    constructor
    · intro hK
      obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
      have : Fact p.Prime := ⟨hprime⟩
      let D : FiniteFieldDatum.{0} :=
        { p := p
          a := 1
          q := p
          prime := hprime
          exponent_pos := by decide
          cardinality_eq := by simp
          k₀ := ZMod p
          card_base := by simp [Nat.card_eq_fintype_card]
          k := AlgebraicClosure (ZMod p) }
      have hl : l ≠ D.p := by change l ≠ p; omega
      exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E W D hl _).mp hK⟩
    · rintro ⟨D, hl, hK⟩
      exact (sfDerivedComplete_iff_legacy l E W D hl _).mpr hK
  exact ⟨hsf.trans hlegacy, hsf⟩

private theorem complete_of_iso (W : Scheme.{u})
    {K L : DerivedCategory (scalarReductionSource.{u, u} l E W)} (e : K ≅ L)
    (hK : IsSfDerivedComplete l E W K) : IsSfDerivedComplete l E W L := by
  unfold IsSfDerivedComplete at hK ⊢
  apply roos_transport _ _ e
    (fun n ↦ (sfDerivedReductionRestricted l E W n).mapIso e)
    (fun n ↦ (sfDerivedReductionUnit l E W n).app K)
    (fun n ↦ (sfDerivedReductionUnit l E W n).app L) _ _ hK
  · intro n
    exact ((sfDerivedReductionTransition l E W n).naturality e.hom).symm
  · intro n
    exact ((sfDerivedReductionUnit l E W n).naturality e.hom).symm

/-- Completeness for the forward normalized integral transport.
Source: Stacks 099N; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-pbc-integral-coefficient-completeness-transport).
Proof: apply the completeness comparison to the transported complex and use the
counit of the coefficient equivalence. An isomorphism of augmented reduction
towers transports the defining Roos triangle in either direction. -/
theorem purDetailedTransport_complete_iff (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    IsSfDerivedComplete l E W K ↔ PbcIsIntrinsicallyComplete W
      (pbcIntegralDatum l E) ((integralDetailedTransport W l E).obj K) := by
  let Φ := purCoefficientModel l E W
  have h := (purCoefficientModel_predicates l E W (Φ.inverse.obj K)).2
  let e := Φ.counitIso.app K
  exact ⟨fun hK ↦ h.mpr (complete_of_iso l E W e.symm hK),
    fun hK ↦ complete_of_iso l E W e (h.mp hK)⟩

end WeilConjectures
