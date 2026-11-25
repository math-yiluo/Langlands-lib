/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientTrace
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionConstructible
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import Mathlib.CategoryTheory.Yoneda

/-! # Objectwise trace splitting for rational scalar extension

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
finite-free trace coordinates.
(blueprint: new-sf-rational-scalar-extension-counit-objectwise-split)
-/
@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

private theorem iso_of_natural_homEquiv
    {C : Type*} [Category C] {A B : C}
    (e : ∀ X : C, (A ⟶ X) ≃ (B ⟶ X))
    (he : ∀ {X Y : C} (f : X ⟶ Y) (g : A ⟶ X),
      e Y (g ≫ f) = e X g ≫ f) : Nonempty (A ≅ B) := by
  let α : coyoneda.obj (op A) ≅ coyoneda.obj (op B) :=
    NatIso.ofComponents (fun X ↦ (e X).toIso) (by
      intro X Y f
      ext g
      exact he f g)
  exact ⟨(Coyoneda.fullyFaithful.preimageIso α).unop.symm⟩

private theorem section_of_retract
    {C D : Type*} [Category C] [Category D]
    (U : C ⥤ D) (T : D ⥤ C) (b : U ⊣ T)
    (M : D) (K : C) (i : M ⟶ U.obj K) (p : U.obj K ⟶ M)
    (hip : i ≫ p = 𝟙 M) :
    ∃ s : M ⟶ U.obj (T.obj M), s ≫ b.counit.app M = 𝟙 M := by
  refine ⟨i ≫ U.map (b.unit.app K) ≫ U.map (T.map p), ?_⟩
  have hn : U.map (T.map p) ≫ b.counit.app M = b.counit.app (U.obj K) ≫ p := by
    exact b.counit.naturality p
  rw [Category.assoc, Category.assoc, hn]
  rw [← Category.assoc (U.map (b.unit.app K))]
  have ht : U.map (b.unit.app K) ≫ b.counit.app (U.obj K) = 𝟙 (U.obj K) :=
    b.left_triangle_components K
  rw [ht]
  exact (congrArg (fun f ↦ i ≫ f) (Category.id_comp p)).trans hip

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})

private theorem restriction_represents
    (U : sfRationalConstructibleCategory l F W ⥤ sfRationalConstructibleCategory l E W)
    (b : U ⊣ sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι)
    (K : sfRationalConstructibleCategory l F W) :
    Nonempty (U.obj K ≅
      (⟨⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
        rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩⟩ :
          sfRationalConstructibleCategory l E W)) := by
  let A : sfRationalConstructibleCategory l E W :=
    ⟨⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
      rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩⟩
  let IE := rationalScalarAmbientInclusion l E W
  let IF := rationalScalarAmbientInclusion l F W
  let fE := ScalarLocalization.fullyFaithfulFullSubcategoryInclusion
    (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E W)) (sfIntegralConstructible l E W)
    (Padic.coefficientExtensionUniformizer l E)
  let fF := ScalarLocalization.fullyFaithfulFullSubcategoryInclusion
    (Padic.coefficientExtensionIntegers l F)
    (DerivedCategory (scalarReductionSource l F W)) (sfIntegralConstructible l F W)
    (Padic.coefficientExtensionUniformizer l F)
  obtain ⟨t, ht⟩ := rationalScalarAmbientTrace l E W F ι K.obj.obj
  let e (M : sfRationalConstructibleCategory l E W) :
      (A ⟶ M) ≃ (K ⟶ (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M) :=
    fE.homEquiv.trans ((t M).trans fF.homEquiv.symm)
  have he (M N : sfRationalConstructibleCategory l E W) (g : M ⟶ N) (h : A ⟶ M) :
      e N (h ≫ g) = e M h ≫ (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map g := by
    apply fF.map_injective
    change IF.map (fF.preimage (t N (IE.map (h ≫ g)))) =
      IF.map (fF.preimage (t M (IE.map h)) ≫
        (sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map g)
    rw [fF.map_preimage, IF.map_comp, fF.map_preimage, IE.map_comp]
    exact ht M N g (IE.map h)
  obtain ⟨a⟩ := iso_of_natural_homEquiv
    (fun M ↦ (e M).trans (b.homEquiv K M).symm) (by
      intro M N g h
      dsimp only [Equiv.trans_apply]
      rw [he, b.homEquiv_naturality_right_symm])
  exact ⟨a.symm⟩

private theorem integral_restriction_retract
    (K : sfIntegralConstructibleCategory l E W) :
    ∃ i : K.obj ⟶ (rationalScalarDerivedRestriction l E F ι W).obj
        ((integralScalarExtension l E F ι W).obj K.obj),
      ∃ p : (rationalScalarDerivedRestriction l E F ι W).obj
          ((integralScalarExtension l E F ι W).obj K.obj) ⟶ K.obj,
        i ≫ p = 𝟙 K.obj := by
  classical
  letI : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} W
  letI : (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} W
  letI : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  letI := ι.toAlgebra
  haveI : FiniteDimensional E F := Module.Finite.right ℚ_[l] E F
  let d := Module.finrank E F
  have hd : 0 < d := Module.finrank_pos
  let j : Fin d := ⟨0, hd⟩
  let φ := integralCompletedScalarMap l E F ι W
  have hφ : integralCompletedScalarMap l E F ι W =
      completedCoefficientMap l E F ι W := by
    apply (completedCoefficientMap_existsUnique l E F ι W).unique
    · exact (integralCompletedScalarMap_existsUnique l E F ι W).exists.choose_spec
    · exact (completedCoefficientMap_existsUnique l E F ι W).exists.choose_spec
  let R := rationalScalarModuleRestriction l E F ι W
  haveI : PreservesFiniteLimits R := (rationalScalarModuleRestriction_exact l E F ι W).1
  haveI : PreservesFiniteColimits R := (rationalScalarModuleRestriction_exact l E F ι W).2
  let S := integralOrdinaryScalar l E F ι W
  obtain ⟨β⟩ := completedIntegralFiniteFree.{u, u} l E W F ι φ
    (integralCompletedScalarMap_projection l E F ι W)
  have hR : R = SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) := by
    dsimp only [R, rationalScalarModuleRestriction]
    rw [← hφ]
  let α : S ⋙ R ≅ finitePowerFunctor (A := integralTowerModules l E W) d := by
    rw [hR]
    exact NatIso.ofComponents (fun M ↦
      (SheafOfModules.restrictScalars _).mapIso
        (eqToIso (integralOrdinaryScalar_obj l E F ι W M)) ≪≫
      SheafOfModules.scalarExtensionIso φ d β.symm M) (by
        intro M N f
        dsimp only [CategoryTheory.Functor.comp_map, Iso.trans_hom,
          CategoryTheory.Functor.mapIso_hom, eqToIso.hom]
        rw [integralOrdinaryScalar_map l E F ι W f, CategoryTheory.Functor.map_comp,
          CategoryTheory.Functor.map_comp]
        simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, eqToHom_trans,
          eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
        exact congrArg (fun k ↦ (SheafOfModules.restrictScalars _).map
          (eqToHom (integralOrdinaryScalar_obj l E F ι W M)) ≫ k)
          (SheafOfModules.scalarExtensionIso_naturality φ d β.symm f))
  letI : PreservesFiniteLimits
      (finitePowerFunctor (A := integralTowerModules l E W) d) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let δ := CategoryTheory.Functor.mapDerivedCategoryCompIso S R ≪≫
    CategoryTheory.Functor.mapDerivedCategoryNatIso α
  let P := DerivedCategory.Q.objPreimage K.obj
  let eP : DerivedCategory.Q.obj P ≅ K.obj := DerivedCategory.Q.objObjPreimageIso K.obj
  let e : (rationalScalarDerivedRestriction l E F ι W).obj
      ((integralScalarExtension l E F ι W).obj K.obj) ≅
        DerivedCategory.Q.obj (∏ᶜ fun _ : Fin d ↦ P) :=
    (rationalScalarDerivedRestriction l E F ι W).mapIso
      (scalarCompletionIso l E F ι W K.obj K.property.1).symm ≪≫
    δ.app K.obj ≪≫
    ((finitePowerFunctor (A := integralTowerModules l E W) d).mapDerivedCategory).mapIso
      eP.symm ≪≫
    (finitePowerFunctor (A := integralTowerModules l E W) d).mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso (finitePowerComplexIso d P)
  refine ⟨eP.inv ≫ DerivedCategory.Q.map (Pi.lift (fun _ : Fin d ↦ 𝟙 P)) ≫ e.inv,
    e.hom ≫ DerivedCategory.Q.map (Pi.π (fun _ : Fin d ↦ P) j) ≫ eP.hom, ?_⟩
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Pi.lift_comp_π]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id]

/-- The counit of the restriction--extension adjunction is split at every rational
E-object. The splitting is induced by a trace-dual basis of the finite separable
coefficient extension and is the objectwise part of the conservativity argument.

Proof: choose an E-basis of F and its trace-dual basis. On complete integral
representatives, send an E-vector to the finite sum of the basis tensors with
its dual-basis coefficients. The trace identity says that composing with the
restriction--extension counit is the identity. Clear one common denominator in
this finite sum, then pass through the finite-free completed comparison and the
raw localization. The resulting localized morphism is the required section;
its equation is preserved by the comparison isomorphisms.
(blueprint: new-sf-rational-scalar-extension-counit-objectwise-split). -/
theorem rationalScalarExtension_counit_objectwise_split
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (U : sfRationalConstructibleCategory l F W ⥤ sfRationalConstructibleCategory l E W)
    (b : U ⊣ sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι) :
    ∀ M : sfRationalConstructibleCategory l E W,
      ∃ s : M ⟶ ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι) ⋙ U).obj M,
        s ≫ b.counit.app M = 𝟙 M := by
  intro M
  let T := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let K := T.obj M
  let A₀ : sfIntegralConstructibleCategory l E W :=
    ⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
      rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩
  obtain ⟨i, p, hip⟩ := integral_restriction_retract l E F ι W M.obj
  have hK : K.obj.obj = (integralScalarExtension l E F ι W).obj M.obj.obj := by
    exact congrArg (fun Z : sfRationalConstructibleCategory l F W ↦ Z.obj.obj)
      (sfRationalScalarExtension_obj l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι M)
  let c := eqToIso (congrArg (rationalScalarDerivedRestriction l E F ι W).obj hK)
  let i₀ : M.obj ⟶ A₀ := ObjectProperty.homMk (i ≫ c.inv)
  let p₀ : A₀ ⟶ M.obj := ObjectProperty.homMk (c.hom ≫ p)
  have h₀ : i₀ ≫ p₀ = 𝟙 M.obj := by
    apply ObjectProperty.hom_ext
    change (i ≫ c.inv) ≫ (c.hom ≫ p) = 𝟙 M.obj.obj
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hip
  let L := sfRationalConstructibleLocalization l E W
  have h : L.map i₀ ≫ L.map p₀ = 𝟙 M := by
    rw [← L.map_comp, h₀, L.map_id]
    rfl
  obtain ⟨e⟩ := restriction_represents l E F ι W U b K
  have h' : (L.map i₀ ≫ e.inv) ≫ (e.hom ≫ L.map p₀) = 𝟙 M := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  exact section_of_retract U T b M K (L.map i₀ ≫ e.inv) (e.hom ≫ L.map p₀) h'

end WeilConjectures
