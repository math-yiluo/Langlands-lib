/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Integral.Open.IntegralOpenTensorRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Quotient transitions on the canonical K-flat finite-reduction model

Source: Stacks 06YY and 0941; Step 4 of the open tensor quotient-model argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

/-- Apply the ordinary mate's unit equation degreewise before specializing coefficients. -/
private theorem quotient_chain_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    {F : A ⥤ B} {R : B ⥤ A} (a : F ⊣ R)
    {G : A ⥤ C} {T : C ⥤ A} (b : G ⊣ T)
    [F.Additive] [R.Additive] [G.Additive] [T.Additive]
    (S : C ⥤ B) [S.Additive] (e : S ⋙ R ≅ T) (τ : F ⟶ G ⋙ S)
    (hτ : τ = coefficientQuotientNatTrans a b S e) (Q : CochainComplex A ℤ) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app Q ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app Q) =
    (b.mapHomologicalComplex (.up ℤ)).unit.app Q ≫
      (NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) := by
  subst τ
  apply HomologicalComplex.hom_ext
  intro i
  exact (a.homEquiv _ _).apply_symm_apply _

/-- The exact-localization factors of an inverse restriction comparison. -/
private theorem restriction_factors
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (S : C ⥤ B) (R : B ⥤ A) (T : C ⥤ A)
    [S.Additive] [R.Additive] [T.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : S ⋙ R ≅ T) (Z : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso S R ≪≫
        Functor.mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Q.obj Z) ≫
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app Z) ≫
      R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj Z) =
    T.mapDerivedCategoryFactors.hom.app Z ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app Z) := by
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors S R Z,
    ← Functor.mapDerivedCategoryNatIso_symm e]
  exact Functor.mapDerivedCategoryNatIso_fac e.symm Z

/-- Compare two quotient-model arrows after their normalized adjoint transposes. -/
private theorem quotient_model
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {R : B ⥤ A} (a : F ⊣ R)
    {G : A ⥤ C} {T : C ⥤ A} (b : G ⊣ T)
    (S : C ⥤ B) (e : S ⋙ R ≅ T)
    (M : A) (X : B) (Y : C) (Z : B) (P P₀ P₁ : A)
    (k : F.obj M ⟶ X) (c : G.obj M ⟶ Y) (τ : X ⟶ Z) (f : S.obj Y ⟶ Z)
    (r : R.obj Z ≅ P) (t : T.obj Y ⟶ P₀) (x : R.obj X ⟶ P₁)
    (u₀ : M ⟶ P₀) (u₁ : M ⟶ P₁) (v : P₀ ⟶ P) (w : P₁ ⟶ P)
    (hc : e.inv.app Y ≫ R.map f ≫ r.hom = t ≫ v)
    (hτ : R.map τ ≫ r.hom = x ≫ w)
    (h₀ : b.unit.app M ≫ T.map c ≫ t = u₀)
    (h₁ : a.unit.app M ≫ R.map k ≫ x = u₁)
    (ho : u₀ ≫ v = u₁ ≫ w) :
    (coefficientQuotientNatTrans a b S e).app M ≫ S.map c ≫ f = k ≫ τ := by
  apply (a.homEquiv _ _).injective
  apply (cancel_mono r.hom).mp
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  have hd : a.homEquiv _ _ ((coefficientQuotientNatTrans a b S e).app M) =
      b.unit.app M ≫ e.inv.app (G.obj M) := (a.homEquiv _ _).apply_symm_apply _
  rw [hd, Adjunction.homEquiv_unit]
  have hn := e.inv.naturality c
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, hc, hτ]
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ f ≫ v) h₀).trans
      (ho.trans (congrArg (fun f ↦ f ≫ w) h₁).symm)

/-- Localizing an ordinary quotient mate respects any normalized derived units. -/
private theorem localized_quotient_model
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F : A ⥤ B} {R : B ⥤ A} (a : F ⊣ R)
    {G : A ⥤ C} {T : C ⥤ A} (b : G ⊣ T)
    [F.Additive] [R.Additive] [G.Additive] [T.Additive]
    (S : C ⥤ B) [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : S ⋙ R ≅ T) (τ : F ⟶ G ⋙ S)
    (hτ : τ = coefficientQuotientNatTrans a b S e)
    {Fd : DerivedCategory A ⥤ DerivedCategory B}
    {Gd : DerivedCategory A ⥤ DerivedCategory C}
    (ad : Fd ⊣ R.mapDerivedCategory) (bd : Gd ⊣ T.mapDerivedCategory)
    (Q : CochainComplex A ℤ)
    (k : Fd.obj (DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (c : Gd.obj (DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q))
    (hk : ad.unit.app (DerivedCategory.Q.obj Q) ≫ R.mapDerivedCategory.map k ≫
      R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q))
    (hc : bd.unit.app (DerivedCategory.Q.obj Q) ≫ T.mapDerivedCategory.map c ≫
      T.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
      DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).unit.app Q)) :
    (coefficientQuotientNatTrans ad bd S.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso S R ≪≫
        Functor.mapDerivedCategoryNatIso e)).app (DerivedCategory.Q.obj Q) ≫
      S.mapDerivedCategory.map c ≫
      S.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    k ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app Q) := by
  let Z := (G.mapHomologicalComplex (.up ℤ)).obj Q
  have hfac := restriction_factors S R T e Z
  have hn := R.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app Q)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  refine quotient_model ad bd S.mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso S R ≪≫
      Functor.mapDerivedCategoryNatIso e)
    (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (DerivedCategory.Q.obj Z)
    (DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj Z))
    (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj
      ((S.mapHomologicalComplex (.up ℤ)).obj Z)))
    (DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj Z))
    (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    k c (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app Q))
    (S.mapDerivedCategoryFactors.hom.app Z)
    (R.mapDerivedCategoryFactors.app ((S.mapHomologicalComplex (.up ℤ)).obj Z))
    (T.mapDerivedCategoryFactors.hom.app Z)
    (R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).unit.app Q))
    (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q))
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app Z))
    (DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app Q)))
    hfac hn hc hk ?_
  have ho := quotient_chain_unit a b S e τ hτ Q
  exact (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map ho.symm).trans (DerivedCategory.Q.map_comp _ _))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] coefficientFiniteReductionModel scalarReductionExtension

/-- Localization of a termwise adjunction unit agrees in the two quotient coordinates. -/
private theorem localized_unit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F : A ⥤ B} {R : B ⥤ A} [F.Additive] [R.Additive] (a : F ⊣ R)
    (Q : CochainComplex A ℤ) :
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  rfl

/-- The finite scalar unit on a K-flat complex in the cochain localization coordinates. -/
private theorem finiteModel_unit
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          (coefficientFiniteReductionModel l E W Q hQ n).hom ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) := by
  have h := (derivedScalarExtensionRestrictionAdjunction l E W n).choose_spec Q hQ
  have hfac := (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh_hom_app
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
  have hfac' : (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) := by
    erw [hfac]
    change (scalarReductionDerivedRestriction l E W n).map (𝟙 _) ≫ _ ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [(scalarReductionRestriction l E W n).mapDerivedCategory.map_id,
      DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]
  have hunit : DerivedCategory.Qh.map
      ((((scalarReductionExtension_adjunction l E W n).choose).mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) :=
    localized_unit (scalarReductionExtension_adjunction l E W n).choose Q
  have hmodel : (coefficientFiniteReductionModel l E W Q hQ n).hom =
      (scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) := by
    unfold coefficientFiniteReductionModel
    dsimp only [coefficientLocalizedCounitModel, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app, asIso_hom]
    change (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    erw [Category.comp_id, (coefficientFiniteDerivedExtension l E W n).map_id,
      Category.id_comp]
    rfl
  refine (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (coefficientFiniteDerivedRestriction l E W n).map f ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))
          hmodel).trans ?_
  exact (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (scalarReductionDerivedRestriction l E W n).map
        ((scalarReductionCounit l E W n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) ≫ f) hfac'.symm).trans
      (h.trans hunit)

attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
  compactSupportSystemRestrictionComp coefficientFiniteAdjunction

/-- The chosen ordinary quotient is the explicitly constructed natural mate. -/
private theorem ordinary_quotient_eq {m n : ℕ} (h : n ≤ m) :
    coefficientOrdinaryQuotient l E W h =
      coefficientOrdinaryQuotientNaturalTransformation l E W h := by
  exact ((coefficientOrdinaryQuotient_exists l E W h).choose_spec.2
    (coefficientOrdinaryQuotientNaturalTransformation l E W h) (fun _ ↦ rfl)).symm

/-- Identify the chosen quotient with the explicit mate through the defining equation. -/
private theorem ordinary_quotient_mate_eq {m n : ℕ} (h : n ≤ m) :
    coefficientOrdinaryQuotient l E W h =
      coefficientQuotientNatTrans (coefficientOrdinaryScalarAdjunction l E W m)
        (coefficientOrdinaryScalarAdjunction l E W n)
        (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h)) := by
  exact (ordinary_quotient_eq l E W h).trans
    (coefficientOrdinaryQuotientNaturalTransformation.eq_1 l E W h)

/-- The scalar-unit quotient transition is computed by the ordinary quotient chain map.
Source: Stacks 06YY (K-flat computation) and 0941 (quotient systems), parent Step 4.
(blueprint: lem-coef-integral-reduction-quotient-model).

Proof: transpose the left-hand composite under the larger finite scalar adjunction.
The defining mate formula for integralOpenReductionStep replaces its transpose by
unit_n followed by inverse successive restriction. Naturality of this restriction
comparison moves the smaller K-flat model through it. The specified derived unit
normalization identifies both finite units, through their K-flat models and exact
restriction factors, with the localized ordinary scalar units. The ordinary quotient
is itself the transpose of unit_n followed by inverse ordinary successive restriction.
Exact-localization composition compatibility identifies the two restriction factors.
The ordinary and derived adjunction bijections therefore identify the two composites.
Only K-flatness of Q is used, with no flatness assumption on the quotient ring, no
bound on Q, and no requirement that each term be flat. The same proof applies to
n=0, zero complexes and empty schemes. -/
theorem integralReductionQuotientModel
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) :
    (integralOpenReductionStep l E W n).app (DerivedCategory.Q.obj Q) ≫
        (normalizedDVRRes l E W (Nat.le_succ n)).map
          (coefficientFiniteReductionModel l E W Q hQ n).hom ≫
        (normalizedDVRModuleRes l E W (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) =
      (coefficientFiniteReductionModel l E W Q hQ (n + 1)).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (coefficientOrdinaryQuotient l E W (Nat.le_succ n)) (.up ℤ)).app Q) := by
  unfold integralOpenReductionStep compactSupportSystemRestrictionComp
  exact localized_quotient_model
    (coefficientOrdinaryScalarAdjunction l E W (n + 1))
    (coefficientOrdinaryScalarAdjunction l E W n)
    (normalizedDVRModuleRes l E W (Nat.le_succ n))
    (eqToIso (coefficientRestrictionComp l E W (Nat.le_succ n)))
    (coefficientOrdinaryQuotient l E W (Nat.le_succ n))
    (ordinary_quotient_mate_eq l E W (Nat.le_succ n))
    (coefficientFiniteAdjunction l E W (n + 1)) (coefficientFiniteAdjunction l E W n)
    Q (coefficientFiniteReductionModel l E W Q hQ (n + 1)).hom
    (coefficientFiniteReductionModel l E W Q hQ n).hom
    (finiteModel_unit l E W Q hQ (n + 1)) (finiteModel_unit l E W Q hQ n)

end WeilConjectures
