/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Normalized scalar tensor comparison on unbounded derived categories

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u u' v' a b d x y
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor
open SheafOfModules WeilConjectures
namespace CategoryTheory.ScalarHomTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)]
  (s : ScalarDerivedPair a)
  (SR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
  (SS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
  (TR : CoefficientTensorModels.{r, c, v, w} J R SR)
  (TS : CoefficientTensorModels.{r, c, v, w} J S SS)

/-- A compatible adjunction-unit square also identifies every transpose.
Source: Stacks 07A6 (blueprint: lem-coef-actual-scalar-derived-pair).
Proof: apply the derived adjunction bijection, rewrite both transposes using their
units, and use naturality of the restriction comparison and the ordinary triangle law. -/
theorem adjunctionTranspose_of_unit
    {C : Type a} {D : Type b} {C' : Type c} {D' : Type d}
    [Category.{v} C] [Category.{w} D] [Category.{x} C'] [Category.{y} D']
    {E : C ⥤ D} {U : D ⥤ C} (am : E ⊣ U)
    (A : C ⥤ C') (B : D ⥤ D')
    {F : C' ⥤ D'} {R : D' ⥤ C'} (ad : F ⊣ R)
    (ε : A ⋙ F ⟶ E ⋙ B) (ρ : B ⋙ R ≅ U ⋙ A)
    (P : C)
    (hu : ad.unit.app (A.obj P) ≫ R.map (ε.app P) ≫ ρ.hom.app (E.obj P) =
      A.map (am.unit.app P))
    (H : D) (g : P ⟶ U.obj H) :
    (ad.homEquiv (A.obj P) (B.obj H)).symm (A.map g ≫ ρ.inv.app H) =
      ε.app P ≫ B.map ((am.homEquiv P H).symm g) := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, ad.homEquiv_unit]
  rw [R.map_comp, ← Category.assoc]
  have hu' : ad.unit.app (A.obj P) ≫ R.map (ε.app P) =
      A.map (am.unit.app P) ≫ ρ.inv.app (E.obj P) := by
    apply (cancel_mono (ρ.hom.app (E.obj P))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact hu.trans (Category.comp_id _).symm
  rw [hu', Category.assoc]
  have hn := ρ.inv.naturality ((am.homEquiv P H).symm g)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← A.map_comp]
  have hg : am.unit.app P ≫ U.map ((am.homEquiv P H).symm g) = g := by
    exact (am.homEquiv_unit P H ((am.homEquiv P H).symm g)).symm.trans
      ((am.homEquiv P H).apply_symm_apply g)
  rw [hg]

theorem scalarPairWithAdjunction_normalization
    (E : scalarModules J R ⥤ scalarModules J S) (hadd : E.Additive)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶ scalarHomotopy E hadd ⋙ DerivedCategory.Qh)
    (am : E ⊣ scalarRestriction a) (d : F ⊣ scalarDerivedRestriction a)
    (hd : ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      d.unit.app (DerivedCategory.Q.obj P) ≫
        (scalarDerivedRestriction a).map
          (cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≫
        (scalarRestriction a).mapDerivedCategoryFactorsh.hom.app
          ((E.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        cast (by rfl) (DerivedCategory.Qh.map ((am.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))) :
    ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      ∀ (H : CochainComplex (scalarModules J S) ℤ)
        (g : P ⟶ ((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H),
        (d.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj H)).symm
            (DerivedCategory.Q.map g ≫ (scalarRestrictionComparison a).inv.app H) =
          scalarPairComplexComparison E hadd F ε P ≫
            DerivedCategory.Q.map (scalarChainTranspose a E hadd am P H g) := by
  classical
  have := hadd
  intro P hP hflat H g
  let q := HomotopyCategory.quotient (scalarModules J R) (.up ℤ)
  let q' := HomotopyCategory.quotient (scalarModules J S) (.up ℤ)
  have hh := adjunctionTranspose_of_unit (am.mapHomotopyCategory (.up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh d ε
    (scalarRestriction a).mapDerivedCategoryFactorsh (q.obj P) (hd P hP)
    (q'.obj H) (q.map g)
  clear hd
  have hfac : (scalarRestriction a).mapDerivedCategoryFactorsh.inv.app (q'.obj H) =
      (scalarRestriction a).mapDerivedCategoryFactors.inv.app H := by
    apply (Iso.inv_eq_inv
      ((scalarRestriction a).mapDerivedCategoryFactorsh.app (q'.obj H))
      ((scalarRestriction a).mapDerivedCategoryFactors.app H)).2
    change (scalarRestriction a).mapDerivedCategoryFactorsh.hom.app (q'.obj H) =
      (scalarRestriction a).mapDerivedCategoryFactors.hom.app H
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change (scalarRestriction a).mapDerivedCategory.map (𝟙 _) ≫
      (scalarRestriction a).mapDerivedCategoryFactors.hom.app H ≫ 𝟙 _ ≫
        DerivedCategory.Qh.map (𝟙 _) = _
    erw [(scalarRestriction a).mapDerivedCategory.map_id (DerivedCategory.Q.obj H),
      DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H))]
    simp only [Category.id_comp]
    exact Category.comp_id ((scalarRestriction a).mapDerivedCategoryFactors.hom.app H)
  have ht : ((am.mapHomotopyCategory (.up ℤ)).homEquiv (q.obj P) (q'.obj H)).symm
      (q.map g) = q'.map (((am.mapHomologicalComplex (.up ℤ)).homEquiv P H).symm g) := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    erw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    rw [Functor.mapHomotopyCategory_map, q'.map_comp]
  rw [hfac, ht] at hh
  change (d.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj H)).symm
      (DerivedCategory.Q.map g ≫ (scalarRestrictionComparison a).inv.app H) =
    ε.app (q.obj P) ≫ DerivedCategory.Q.map
      (scalarChainTranspose a E hadd am P H g) at hh
  have hcP : scalarPairComplexComparison E hadd F ε P = ε.app (q.obj P) := by
    dsimp only [scalarPairComplexComparison]
    change F.map (𝟙 _) ≫ ε.app (q.obj P) ≫ 𝟙 _ = ε.app (q.obj P)
    simp
  rw [hcP]
  exact hh

/-- Construct the scalar-derived pair from the specified ordinary and derived adjunctions.
Source: Stacks 07A4 and 0D6D (blueprint: lem-coef-actual-scalar-derived-pair).
The object data are the given extension and derived functors; only their normalization
proofs are assembled here. The homotopy adjunction unit formula identifies the derived
transpose, using the canonical localization comparison. -/
noncomputable def scalarPairWithAdjunction
    (E : scalarModules J R ⥤ scalarModules J S)
    (hobj : ∀ M, E.obj M = changeOfRings a M)
    (hmap : ∀ {M N : scalarModules J R} (f : M ⟶ N),
      E.map f = eqToHom (hobj M) ≫ changeOfRingsHom a M f ≫
        eqToHom (hobj N).symm)
    (hadd : E.Additive)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶ scalarHomotopy E hadd ⋙ DerivedCategory.Qh)
    (hF : F.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ)))
    (hc : ∀ P : CochainComplex (scalarModules J R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (am : E ⊣ scalarRestriction a)
    (hu : ∀ (M : scalarModules J R) (V : Cᵒᵖ) (x : M.val.obj V),
      ((eqToHom (hobj M)).val.app V) ((am.unit.app M).val.app V x) =
        (toSheafify J (changeOfRingsPresheaf a M).presheaf).app V
          ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app
            (M.val.obj V) x))
    (d : F ⊣ scalarDerivedRestriction a)
    (hd : ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      d.unit.app (DerivedCategory.Q.obj P) ≫
        (scalarDerivedRestriction a).map
          (cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≫
        (scalarRestriction a).mapDerivedCategoryFactorsh.hom.app
          ((E.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        cast (by rfl) (DerivedCategory.Qh.map ((am.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))) :
    ScalarDerivedPair a := by
  classical
  have := hadd
  refine
    { extension := E
      extension_obj := hobj
      extension_map := hmap
      extension_additive := hadd
      derived := F
      counit := ε
      isLeftDerived := hF
      computes := ?_
      ordinaryAdjunction := am
      ordinaryUnit := ?_
      adjunction := d
      normalization := ?_ }
  · intro P hP
    have := hc P hP
    dsimp only [scalarPairComplexComparison]
    infer_instance
  · exact hu
  · exact scalarPairWithAdjunction_normalization.{c, v, r, w} a E hadd F ε am d hd

end CategoryTheory.ScalarHomTensor

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures
universe t
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : AlgebraicGeometry.Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  HasDerivedCategory.standard

theorem coefficientFiniteAdjunction_unit (n : ℕ) :
    ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients P →
      (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj P) ≫
        (scalarReductionDerivedRestriction l E W n).map
          (cast (by rfl) ((scalarReductionCounit l E W n).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh.hom.app
          (((scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        cast (by rfl) (DerivedCategory.Qh.map
          (((scalarReductionExtension_adjunction l E W n).choose.mapHomotopyCategory
            (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by
  exact (derivedScalarExtensionRestrictionAdjunction l E W n).choose_spec

-- The normalized unit compares the explicit scalar extension on sections.
/-- The actual integral-to-finite scalar pair, with the recorded adjunctions.
Source: Stacks 03CZ, 07A4 (blueprint: lem-coef-actual-scalar-derived-pair).
The scalar-extension existence theorem determines its ordinary functor by its object
and morphism equations. Its derived universal property and normalized adjunction then
supply precisely the fields of the scalar pair; no arbitrary object is chosen. -/
noncomputable def coefficientActualScalarDerivedPair (n : ℕ) :
    SheafOfModules.ScalarDerivedPair
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W)
      (S := integralCoefficientCommRingSheaf l E W n)
      (completedIntegralCommRingProjectionUnrestricted l E W n) := by
  let hobj := (scalarReductionExistence l E W n).choose_spec.choose
  exact CategoryTheory.ScalarHomTensor.scalarPairWithAdjunction.{t+1, t, u, max (t+2) (u+1)}
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (scalarReductionExtension l E W n) hobj
    (scalarReductionExistence l E W n).choose_spec.choose_spec.choose
    (scalarReductionExtensionAdditive l E W n)
    (coefficientFiniteDerivedExtension l E W n) (scalarReductionCounit l E W n)
    (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.1
    (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.2
    (scalarReductionExtension_adjunction l E W n).choose
    (by
      intro M V x
      rw [(scalarReductionExtension_adjunction l E W n).choose_spec]
      have hi := congrArg (fun f ↦ f.val.app V
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
          (changeOfRingsPresheaf
            (completedIntegralCommRingProjectionUnrestricted l E W n) M).presheaf).app V
            ((ModuleCat.extendRestrictScalarsAdj
              ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V).hom).unit.app
                (M.val.obj V) x)))
        (eqToIso (hobj M)).inv_hom_id
      exact hi)
    (coefficientFiniteAdjunction l E W n)
    (coefficientFiniteAdjunction_unit l E W n)

/-- The constructed pair retains the prescribed ordinary extension.
Source: Stacks 07A6 (blueprint: lem-coef-actual-scalar-derived-pair).
Proof: the extension field of scalarPairWithAdjunction is its given extension. -/
theorem coefficientActualScalarDerivedPair_extension (n : ℕ) :
    (coefficientActualScalarDerivedPair l E W n).extension =
      scalarReductionExtension l E W n := rfl

/-- The ordinary adjunction agrees heterogeneously without unfolding its extension.
Source: Stacks 07A6 (blueprint: lem-coef-actual-scalar-derived-pair).
Proof: the adjunction is the supplied normalized adjunction by construction. -/
theorem coefficientActualScalarDerivedPair_ordinaryAdjunction_heq (n : ℕ) :
    HEq (coefficientActualScalarDerivedPair l E W n).ordinaryAdjunction
      (scalarReductionExtension_adjunction l E W n).choose := HEq.rfl

/-- The constructed pair retains the prescribed derived extension.
Source: Stacks 07A6 (blueprint: lem-coef-actual-scalar-derived-pair).
Proof: the derived field is exactly its supplied functor. -/
theorem coefficientActualScalarDerivedPair_derived (n : ℕ) :
    (coefficientActualScalarDerivedPair l E W n).derived =
      coefficientFiniteDerivedExtension l E W n := rfl

end WeilConjectures
