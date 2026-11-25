/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRFlatCokernel
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarCone
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAdjoint
import all WeilConjectures.SmoothPurity.Integral.IntegralPrincipalConeQuotientAugmentation
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Normalized adjoints of strict DVR coefficient maps

Source: Stacks Tags 06YS, 06YY, 03EK and 05RT; blueprint DVR effectivity,
proof paragraphs 3--4. (blueprint: lem-coef-normalized-dvr-strict-coefficient-adjoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

local instance instNormalizedDVRStrictCoefficientAdjoint1
    : HasDerivedCategory (scalarReductionSource l E X) :=
  HasDerivedCategory.standard _
local instance (priority := 10000) instNormalizedDVRStrictCoefficientAdjoint2
    : EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
local instance (priority := 10000) instNormalizedDVRStrictCoefficientAdjoint3
    : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
local instance (priority := 10000) instNormalizedDVRStrictCoefficientAdjoint4 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

local instance scalarLinear :
    Linear (normalizedDVRScalars l E X) (scalarReductionSource l E X) :=
  SheafOfModules.homLinear (completedIntegralCommRingSheafUnrestricted l E X).obj
    (completedIntegralCoefficientSheafUnrestricted l E X).property

local instance scalarRestrictionAdditive (n : ℕ) :
    (scalarReductionRestriction l E X n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
      (forget₂ CommRingCat RingCat)).map
        (completedIntegralCommRingProjectionUnrestricted l E X n))).Additive

local instance restrictionLimits (n : ℕ) :
    PreservesFiniteLimits (scalarReductionRestriction l E X n) :=
  scalarReductionRestrictionLimits l E X n
local instance restrictionColimits (n : ℕ) :
    PreservesFiniteColimits (scalarReductionRestriction l E X n) :=
  scalarReductionRestrictionColimits l E X n
local instance finiteDerived (n : ℕ) : HasDerivedCategory (scalarReductionTarget l E X n) :=
  HasDerivedCategory.standard _

private theorem inverse_factor {C : Type*} [Category C]
    {X Y Z : C} (r : X ≅ Y) (f : Y ≅ Z) (v : X ≅ Z)
    (h : v.hom = r.hom ≫ f.hom) : f.hom ≫ v.inv = r.inv := by
  calc
    f.hom ≫ v.inv = r.inv ≫ (r.hom ≫ f.hom) ≫ v.inv := by simp
    _ = r.inv := by rw [← h]; simp

private theorem map_adjunct_comparison
    {C B : Type*} [Category C] [Category B]
    {L T : C ⥤ B} {R V : B ⥤ C}
    (adj : L ⊣ R) (badj : T ⊣ V) (v : V ≅ R)
    (X : C) (Y : B) (a : X ⟶ R.obj Y) :
    R.map ((adj.homEquiv X Y).symm a) =
      R.map ((adj.leftAdjointUniq (badj.ofNatIsoRight v)).hom.app X) ≫
        v.inv.app (T.obj X) ≫
        V.map ((badj.homEquiv X Y).symm (a ≫ v.inv.app Y)) ≫ v.hom.app Y := by
  let ba := badj.ofNatIsoRight v
  let k := adj.leftAdjointUniq ba
  have hk : (adj.homEquiv X Y).symm a =
      k.hom.app X ≫ (ba.homEquiv X Y).symm a := by
    apply (adj.homEquiv X Y).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
    exact ((ba.homEquiv X Y).apply_symm_apply a).symm
  rw [hk, Functor.map_comp]
  dsimp only [ba]
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  have hn (g : T.obj X ⟶ Y) :
      R.map g = v.inv.app _ ≫ V.map g ≫ v.hom.app _ := by
    rw [v.hom.naturality]
    simp
  rw [hn]

private theorem inv_hom_factor {C : Type*} [Category C]
    {X Y Z : C} (r : X ≅ Y) (f : Y ≅ Z) (v : X ≅ Z)
    (h : v.hom = r.hom ≫ f.hom) : r.inv ≫ v.hom = f.hom := by
  rw [h]
  simp

private theorem map_desc_eq {C : Type*} [Category C] [Abelian C]
    {P N : CochainComplex C ℤ} {s t : P ⟶ P} (h : s = t)
    (f : P ⟶ N) (hf : t ≫ f = 0) :
    CochainComplex.mappingCone.map s t (𝟙 P) (𝟙 P) (by simpa using h) ≫
        CochainComplex.mappingCone.desc t 0 f (by simp [hf]) =
      CochainComplex.mappingCone.desc s 0 f (by simp [h, hf]) := by
  subst t
  simp only [CochainComplex.mappingCone.map_id, Category.id_comp]

private theorem comparison_formula
    {C B : Type*} [Category C] [Category B]
    {L T : C ⥤ B} {R V : B ⥤ C} {D G : C ⥤ C}
    (adj : L ⊣ R) (badj : T ⊣ V) (v : V ≅ R)
    (bA : D ≅ T ⋙ V) (e : D ≅ G)
    (X : C) (Y : B) (a : X ⟶ R.obj Y) (q : X ⟶ V.obj Y)
    (g : D.obj X ⟶ V.obj Y) (z : G.obj X ⟶ R.obj Y)
    (hq : a ≫ v.inv.app Y = q)
    (hb : V.map ((badj.homEquiv X Y).symm q) = bA.inv.app X ≫ g)
    (hz : e.hom.app X ≫ z = g ≫ v.hom.app Y) :
    R.map ((adj.homEquiv X Y).symm a) =
      (Functor.isoWhiskerRight (adj.leftAdjointUniq (badj.ofNatIsoRight v)) R ≪≫
        (bA ≪≫ Functor.isoWhiskerLeft T v).symm ≪≫ e).hom.app X ≫ z := by
  rw [map_adjunct_comparison adj badj v, hq, hb]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hz]

private theorem composition_comparison {C : Type*} [Category C]
    {X Y Z W A B H : C} (e : X ⟶ Y) (c : Y ⟶ Z)
    (u : X ⟶ W) (v : W ⟶ Z) (z : Z ⟶ A) (z' : W ⟶ A)
    (r : A ⟶ B) (s : B ⟶ H) (t : A ⟶ H)
    (he : e ≫ c = u ≫ v) (hz : v ≫ z = z') (hr : r ≫ s = t) :
    e ≫ (c ≫ z ≫ t) = (u ≫ z' ≫ r) ≫ s := by
  calc
    e ≫ (c ≫ z ≫ t) = (e ≫ c) ≫ z ≫ t := by simp only [Category.assoc]
    _ = (u ≫ v) ≫ z ≫ t := by rw [he]
    _ = u ≫ (v ≫ z) ≫ t := by simp only [Category.assoc]
    _ = u ≫ z' ≫ t := by rw [hz]
    _ = (u ≫ z' ≫ r) ≫ s := by rw [Category.assoc, Category.assoc, hr]

private def powerSection (n : ℕ) :
    (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X))).sections :=
  uniformizerPower l E X n

private theorem coefficient_exact (n : ℕ) :
    ∃ ht : (SheafOfModules.RegularQuotientCone.scalar
        (completedIntegralCommRingSheafUnrestricted l E X) (powerSection l E X n)).app
        (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients
          (AlgebraicGeometry.Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X))) ≫
      SheafOfModules.RegularQuotientCone.ringMap
        (completedIntegralCommRingProjectionUnrestricted l E X n) = 0,
      (ShortComplex.mk _ _ ht).ShortExact := by
  exact regularExact l E X n

private theorem scalar_eq (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (SheafOfModules.RegularQuotientCone.complexScalar
      (completedIntegralCommRingSheafUnrestricted l E X)
      (powerSection l E X n)).app P =
        normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P := by
  apply HomologicalComplex.hom_ext
  intro q
  ext U x
  rfl

private def cone_iso (n : ℕ) :
    SheafOfModules.RegularQuotientCone.cone
      (completedIntegralCommRingSheafUnrestricted l E X)
      (powerSection l E X n) ≅
        CochainComplex.LinearScalarCone.cochain
          (A := scalarReductionSource l E X)
          (normalizedDVRUniformizer l E X ^ (n + 1)) := by
  let a : 𝟭 (CochainComplex (scalarReductionSource l E X) ℤ) ⟶
      𝟭 (CochainComplex (scalarReductionSource l E X) ℤ) :=
    SheafOfModules.RegularQuotientCone.complexScalar
    (completedIntegralCommRingSheafUnrestricted l E X) (powerSection l E X n)
  let H : CochainComplex (scalarReductionSource l E X) ℤ ⥤
      Arrow (CochainComplex (scalarReductionSource l E X) ℤ) := {
    obj := fun P ↦ Arrow.mk (a.app P)
    map := fun f ↦ Arrow.homMk f f (by
      simpa only [Functor.id_map, Arrow.mk_hom] using a.naturality f) }
  let e : H ≅ CochainComplex.smulArrow
      (𝒜 := scalarReductionSource l E X)
      (normalizedDVRUniformizer l E X ^ (n + 1)) :=
    NatIso.ofComponents (fun P ↦ Arrow.isoMk (Iso.refl _) (Iso.refl _)
      (by
        change (𝟙 P) ≫ (normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P) =
          a.app P ≫ (𝟙 P)
        exact (Category.id_comp _).trans
          ((scalar_eq l E X n P).symm.trans (Category.comp_id _).symm))) (by
        intro P Q f
        ext <;> simp [H])
  exact Functor.isoWhiskerRight e CochainComplex.ConeCoimage.cone

/-- The strict finite-coefficient adjoint is the cone map with shifted component
zero and unshifted component f, for one natural comparison of derived functors.

Source: Stacks 06YY and 07A6 and the blueprint DVR effectivity regular quotient
calculation. (blueprint: lem-coef-normalized-dvr-strict-coefficient-adjoint).

Proof: apply the normalized regular quotient augmentation to the completed
uniformizer power and its actual finite quotient. The strict adjoint formula
computes the map on K-flat resolutions and transports it by naturality. Identify
the regular scalar cone with the linear scalar cone by sectionwise equality of
scalar multiplication. Localization uniqueness lifts this comparison to every
derived morphism and identifies the two exact restriction lifts. Uniqueness of
left adjoints transports the formula to the specified adjunction. This calculation
has no tower, no limit and no fullness of derived restriction hypothesis. -/
private theorem strict_coefficient_adjoint_core (n : ℕ)
    (adj : scalarReductionDerivedExtension l E X n ⊣
      scalarReductionDerivedRestriction l E X n) :
    ∃ A : scalarReductionDerivedExtension l E X n ⋙
        scalarReductionDerivedRestriction l E X n ≅
      CochainComplex.LinearScalarCone.derived
        (A := scalarReductionSource l E X)
        (normalizedDVRUniformizer l E X ^ (n + 1)),
    ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ)
      (N : CochainComplex (scalarReductionTarget l E X n) ℤ)
      (f : P ⟶ ((scalarReductionRestriction l E X n).mapHomologicalComplex
        (.up ℤ)).obj N)
      (hf : (normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P) ≫ f = 0),
      (scalarReductionDerivedRestriction l E X n).map
        ((adj.homEquiv (DerivedCategory.Q.obj P)
          ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj N)).symm
          (DerivedCategory.Q.map f ≫
            (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N)) =
      A.hom.app (DerivedCategory.Q.obj P) ≫
        (CochainComplex.LinearScalarCone.comparison
          (normalizedDVRUniformizer l E X ^ (n + 1))).hom.app P ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.desc
          (normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P) 0 f (by simp [hf])) ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N := by
  classical
  let φ := completedIntegralCommRingProjectionUnrestricted l E X n
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)))
  obtain ⟨d⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (C := X.ProEt) (J := AlgebraicGeometry.Scheme.ProEt.topology X) φ
  obtain ⟨ht, hexact⟩ := coefficient_exact l E X n
  obtain ⟨b⟩ := SheafOfModules.RegularQuotientCone.nonempty_augmentation
    (C := X.ProEt) (J := AlgebraicGeometry.Scheme.ProEt.topology X)
    φ (powerSection l E X n) ht hexact d
  let G := CochainComplex.LinearScalarCone.derived
    (A := scalarReductionSource l E X)
    (normalizedDVRUniformizer l E X ^ (n + 1))
  let comp := CochainComplex.LinearScalarCone.comparison
    (A := scalarReductionSource l E X)
    (normalizedDVRUniformizer l E X ^ (n + 1))
  let e : DerivedCategory.Q ⋙ b.D ≅ DerivedCategory.Q ⋙ G :=
    b.cone_factor ≪≫ Functor.isoWhiskerRight (cone_iso l E X n) DerivedCategory.Q ≪≫
      comp.symm
  let FF := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (scalarReductionSource l E X) (.up ℤ))
    (DerivedCategory (scalarReductionSource l E X))
  let e' : b.D ≅ G := FF.preimageIso e
  have he (P : CochainComplex (scalarReductionSource l E X) ℤ) :
      e'.hom.app (DerivedCategory.Q.obj P) ≫ comp.hom.app P =
        b.cone_factor.hom.app P ≫ DerivedCategory.Q.map ((cone_iso l E X n).hom.app P) := by
    have h : e'.hom.app (DerivedCategory.Q.obj P) = e.hom.app P :=
      NatTrans.congr_app (FF.map_preimage e.hom) P
    rw [h]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  let V := scalarReductionDerivedRestriction l E X n
  let v0 : DerivedCategory.Q ⋙ b.V ≅ DerivedCategory.Q ⋙ V :=
    b.restriction_factor ≪≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.symm
  let FV := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (scalarReductionTarget l E X n) (.up ℤ))
    (DerivedCategory (scalarReductionSource l E X))
  let v : b.V ≅ V := FV.preimageIso v0
  have hv (N : CochainComplex (scalarReductionTarget l E X n) ℤ) :
      v.hom.app (DerivedCategory.Q.obj N) = b.restriction_factor.hom.app N ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N := by
    have h : v.hom.app (DerivedCategory.Q.obj N) = v0.hom.app N :=
      NatTrans.congr_app (FV.map_preimage v0.hom) N
    rw [h]
    rfl
  let ba : d.T ⊣ V := b.adjunction.ofNatIsoRight v
  let k := adj.leftAdjointUniq ba
  let A : scalarReductionDerivedExtension l E X n ⋙ V ≅ G :=
    Functor.isoWhiskerRight k V ≪≫
      (b.A ≪≫ Functor.isoWhiskerLeft d.T v).symm ≪≫ e'
  refine ⟨A, ?_⟩
  intro P N f hf
  have hreg : (SheafOfModules.RegularQuotientCone.complexScalar
      (completedIntegralCommRingSheafUnrestricted l E X) (powerSection l E X n)).app P ≫
        f = 0 := by
    rw [scalar_eq l E X n P]
    exact hf
  let z := CochainComplex.mappingCone.desc
    (normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P) 0 f (by simp [hf])
  let z' := CochainComplex.mappingCone.desc
    ((SheafOfModules.RegularQuotientCone.complexScalar
      (completedIntegralCommRingSheafUnrestricted l E X) (powerSection l E X n)).app P)
      0 f (by simp [hreg])
  have hz : (cone_iso l E X n).hom.app P ≫ z = z' := by
    simpa [cone_iso, z, z', SheafOfModules.RegularQuotientCone.cone] using
      map_desc_eq (scalar_eq l E X n P) f hf
  let a : DerivedCategory.Q.obj P ⟶ V.obj (DerivedCategory.Q.obj N) :=
    DerivedCategory.Q.map f ≫
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N
  have hai : a ≫ v.inv.app (DerivedCategory.Q.obj N) =
      DerivedCategory.Q.map f ≫ b.restriction_factor.inv.app N := by
    have hi := inverse_factor (b.restriction_factor.app N)
      ((scalarReductionRestriction l E X n).mapDerivedCategoryFactors.app N).symm
      (v.app (DerivedCategory.Q.obj N)) (hv N)
    exact (Category.assoc _ _ _).trans (congrArg (fun z ↦ DerivedCategory.Q.map f ≫ z) hi)
  have hb := SheafOfModules.RegularQuotientCone.augmentation_adjoint
    φ (powerSection l E X n) d b P N f hreg
  change V.map ((adj.homEquiv _ _).symm a) =
    A.hom.app (DerivedCategory.Q.obj P) ≫ comp.hom.app P ≫
      DerivedCategory.Q.map z ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N
  have hr : b.restriction_factor.inv.app N ≫ v.hom.app (DerivedCategory.Q.obj N) =
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N :=
    inv_hom_factor (b.restriction_factor.app N)
      ((scalarReductionRestriction l E X n).mapDerivedCategoryFactors.app N).symm
      (v.app (DerivedCategory.Q.obj N)) (hv N)
  let Q : CochainComplex (scalarReductionSource l E X) ℤ ⥤
      DerivedCategory (scalarReductionSource l E X) := DerivedCategory.Q
  have hmap : Q.map ((cone_iso l E X n).hom.app P) ≫ Q.map z = Q.map z' :=
    (Q.map_comp _ _).symm.trans (congrArg (fun w ↦ Q.map w) hz)
  have hc : e'.hom.app (DerivedCategory.Q.obj P) ≫
      (comp.hom.app P ≫ DerivedCategory.Q.map z ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N) =
      (b.cone_factor.hom.app P ≫ DerivedCategory.Q.map z' ≫
        b.restriction_factor.inv.app N) ≫ v.hom.app (DerivedCategory.Q.obj N) :=
    composition_comparison (e'.hom.app (DerivedCategory.Q.obj P)) (comp.hom.app P)
      (b.cone_factor.hom.app P) (Q.map ((cone_iso l E X n).hom.app P))
      (Q.map z) (Q.map z') (b.restriction_factor.inv.app N)
      (v.hom.app (DerivedCategory.Q.obj N))
      ((scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N)
      (he P) hmap hr
  exact comparison_formula adj b.adjunction v b.A e'
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) a
    (DerivedCategory.Q.map f ≫ b.restriction_factor.inv.app N)
    (b.cone_factor.hom.app P ≫ DerivedCategory.Q.map z' ≫ b.restriction_factor.inv.app N)
    (comp.hom.app P ≫ DerivedCategory.Q.map z ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app N)
    hai hb hc

local instance completedSourceDerived :
    HasDerivedCategory (completedIntegralModuleSheaves l E X D hl) :=
  HasDerivedCategory.standard _
local instance completedRestrictionAdditive (n : ℕ) :
    (completedIntegralRestrictScalars l E X D hl n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl n)).Additive
local instance completedRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E X D hl n) :=
  (completedIntegralRestrictScalars_exact l E X D hl n).1
local instance completedRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (completedIntegralRestrictScalars l E X D hl n) :=
  (completedIntegralRestrictScalars_exact l E X D hl n).2
local instance normalizedFiniteDerived (n : ℕ) :
    HasDerivedCategory (normalizedDVRModules l E X n) := HasDerivedCategory.standard _

/-- The strict finite-coefficient adjoint formula in the completed-coefficient
presentation used by normalized DVR towers.

Source: Stacks 06YY and 07A6, the regular quotient calculation in DVR effectivity.
(blueprint: lem-coef-normalized-dvr-strict-coefficient-adjoint).

Proof: the core calculation uses the identical scalar-reduction source and target
categories. Its natural comparison is obtained from the normalized regular
quotient augmentation by localization and uniqueness of adjoints. On a strict map
f its cone map is (0,f), by the K-flat adjoint calculation and naturality. Unfolding
the category abbreviations gives the displayed completed-coefficient presentation;
the completed and scalar-reduction restriction factorizations agree definitionally. -/
theorem normalizedDVR_strict_coefficient_adjoint (n : ℕ)
    (adj : scalarReductionDerivedExtension l E X n ⊣
      scalarReductionDerivedRestriction l E X n) :
    ∃ A : scalarReductionDerivedExtension l E X n ⋙
        scalarReductionDerivedRestriction l E X n ≅
      CochainComplex.LinearScalarCone.derived
        (A := completedIntegralModuleSheaves l E X D hl)
        (normalizedDVRUniformizer l E X ^ (n + 1)),
    ∀ (P : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
      (N : CochainComplex (normalizedDVRModules l E X n) ℤ)
      (f : P ⟶ ((completedIntegralRestrictScalars l E X D hl n).mapHomologicalComplex
        (.up ℤ)).obj N)
      (hf : (normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P) ≫ f = 0),
      (scalarReductionDerivedRestriction l E X n).map
        ((adj.homEquiv (DerivedCategory.Q.obj P)
          ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj N)).symm
          (DerivedCategory.Q.map f ≫
            (completedIntegralRestrictScalars l E X D hl n).mapDerivedCategoryFactors.inv.app N)) =
      A.hom.app (DerivedCategory.Q.obj P) ≫
        (CochainComplex.LinearScalarCone.comparison
          (normalizedDVRUniformizer l E X ^ (n + 1))).hom.app P ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.desc
          (normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P) 0 f (by simp [hf])) ≫
        (completedIntegralRestrictScalars l E X D hl n).mapDerivedCategoryFactors.inv.app N := by
  exact strict_coefficient_adjoint_core l E X n adj

end WeilConjectures
