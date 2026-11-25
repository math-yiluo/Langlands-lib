/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import all WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility

/-! # Tensor comparison for the strict finite-reduction towers

Source: Stacks Project, Modules on Sites, Tag 03EL; Cohomology on Sites,
Tags 06YM and 06YY; Bhatt--Scholze, Definition 3.4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

attribute [local irreducible] SheafOfModules.monoidalCategory
  constantSheaf HasDerivedCategory.standard unrestrictedIntegralReductionExistence

universe a₁ b₁ a₂ b₂

-- Totalization uses only the additive tensor comparison and the adjunction.
private theorem tensorTotalComparisonOfAdjunction
    {A : Type a₁} [Category.{b₁} A] [Abelian A] [MonoidalCategory A]
    {B : Type a₂} [Category.{b₂} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (F : A ⥤ B) [F.Additive]
    (e : ∀ M N : A, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (he : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (G : B ⥤ A) (adj : F ⊣ G) :
    ∃ b : Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex) ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex),
      ∀ (P Q : CochainComplex A ℤ) (p q k : ℤ) (h : p + q = k),
        F.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q k h) ≫
          (b.hom.app (P, Q)).f k =
        (e (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B) p q k h := by
  let EC := F.mapHomologicalComplex (.up ℤ)
  let tR := Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)
  let tS := Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex)
  have hiso (P Q : CochainComplex A ℤ) : IsIso (tensorPullbackTotal F e he P Q) :=
    tensorPullbackTotal_isIso F e he G adj P Q
  let b0 : (EC.prod EC) ⋙ tS ≅ tR ⋙ EC := NatIso.ofComponents
    (fun P ↦ @asIso _ _ _ _ (tensorPullbackTotal F e he P.1 P.2) (hiso P.1 P.2)) (by
      intro P Q f
      dsimp only [EC, tR, tS, Functor.comp_map, Functor.prod_map, Functor.prod_obj]
      simp only [Functor.uncurry_obj_map, Functor.map₂CochainComplex,
        Functor.map₂HomologicalComplex, asIso_hom,
        ScalarHomTensor.tensorMap_factor]
      exact ScalarHomTensor.tensorPullbackTotal_naturality F e he f.1 f.2)
  refine ⟨b0.symm, ?_⟩
  intro P Q p q k h
  let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q k h
  let ι' := CochainComplex.ιMapBifunctor (EC.obj P) (EC.obj Q) (curriedTensor B) p q k h
  let z := (HomologicalComplex.eval B (.up ℤ) k).mapIso (b0.app (P, Q))
  have hz : ι' ≫ z.hom = (e (P.X p) (Q.X q)).inv ≫ F.map ι := by
    change ι' ≫ tensorPullbackTotalComponent F e P Q k = _
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
  exact (Iso.comp_inv_eq z).2
    (((Iso.eq_inv_comp (e (P.X p) (Q.X q))).1 hz).symm.trans (Category.assoc _ _ _).symm)

section ScalarTotal
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

private abbrev ScalarMod (R : Sheaf J CommRingCat.{max c v r}) :=
  SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

private def scalarSection
    (F : ScalarMod.{c, v, r} R ⥤ ScalarMod.{c, v, r} S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (M : ScalarMod.{c, v, r} R) (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) :
    (F.obj M).val.obj V :=
  (eqToHom (hF M).symm).val.app V
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app V
      (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))

section

attribute [local implicit_reducible] SheafOfModules.restrictScalars
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  PresheafOfModules.presheaf ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

-- Separate the ordinary unit and tensor identities from the total-complex construction.
private theorem scalarTensorAdjunctionComparison
    (F : ScalarMod.{c, v, r} R ⥤ ScalarMod.{c, v, r} S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hF N).symm)
    [F.Additive] :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.isMonoidal_W_independentCoefficients S
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.monoidalCategory S
    ∃ (am : F ⊣ SheafOfModules.restrictScalars.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a))
      (e : ∀ M N : ScalarMod.{c, v, r} R, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N),
      (∀ {M M' N N' : ScalarMod.{c, v, r} R} (f : M ⟶ M') (g : N ⟶ N'),
        F.map (f ⊗ₘ g) ≫ (e M' N').hom =
          (e M N).hom ≫ (F.map f ⊗ₘ F.map g)) ∧
      (∀ (M : ScalarMod.{c, v, r} R) (V : Cᵒᵖ) (x : M.val.obj V),
        scalarSection.{c, v, r} a F hF M V 1 x = (am.unit.app M).val.app V x) ∧
      ∀ (M N : ScalarMod.{c, v, r} R) (V : Cᵒᵖ)
        (x : M.val.obj V) (y : N.val.obj V),
        (e M N).hom.val.app V
          ((am.unit.app _).val.app V (SheafOfModules.ScalarHomOrdinary.pure R M N V x y)) =
        SheafOfModules.ScalarHomOrdinary.pure S _ _ V
          ((am.unit.app M).val.app V x) ((am.unit.app N).val.app V y) := by
  classical
  dsimp only
  let A := ScalarMod.{c, v, r} R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  obtain ⟨_, _, hAdj⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a
  obtain ⟨am, hUnit⟩ := hAdj F hF hmF
  have unit_normalized (M : A) (V : Cᵒᵖ) (x : M.val.obj V) :
      (eqToHom (hF M)).val.app V ((am.unit.app M).val.app V x) =
        (toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) := by
    have hh := hUnit M (F.obj M) (eqToHom (hF M).symm) V x
    simp only [eqToHom_trans, eqToHom_refl, am.homEquiv_id] at hh
    exact (congrArg ((eqToHom (hF M)).val.app V) hh).trans
      (ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.val.app V) (eqToHom_trans (hF M).symm (hF M))) _)
  let eF (M : A) := eqToIso (hF M) ≪≫
    SheafOfModules.ScalarHomOrdinary.extensionIso a M
  have eF_unit (M : A) (V : Cᵒᵖ) (x : M.val.obj V) :
      (eF M).hom.val.app V ((am.unit.app M).val.app V x) =
        SheafOfModules.scalarExtensionSection a M V 1 x := by
    change (SheafOfModules.ScalarHomOrdinary.extensionIso a M).hom.val.app V
      ((eqToHom (hF M)).val.app V ((am.unit.app M).val.app V x)) = _
    rw [unit_normalized]
    exact SheafOfModules.ScalarHomOrdinary.extensionIso_unit a M V x
  have eF_inv_unit (M : A) (V : Cᵒᵖ) (x : M.val.obj V) :
      (eF M).inv.val.app V (SheafOfModules.scalarExtensionSection a M V 1 x) =
        (am.unit.app M).val.app V x := by
    rw [← eF_unit]
    exact congrArg (fun f ↦ f.val.app V ((am.unit.app M).val.app V x))
      (eF M).hom_inv_id
  obtain ⟨core⟩ := SheafOfModules.exists_scalarExtensionTensorCore R S a
  let e (M N : A) : F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N :=
    eF _ ≪≫ (SheafOfModules.ScalarHomOrdinary.extensionFunctor a).mapIso
      (SheafOfModules.ScalarHomOrdinary.tensorIsoSite R M N) ≪≫
    core.tensorComparison M N ≪≫
      (SheafOfModules.ScalarHomOrdinary.tensorIsoSite S _ _).symm ≪≫
        tensorIso (eF M).symm (eF N).symm
  have hgen (M N : A) (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
      (e M N).hom.val.app V
        ((am.unit.app _).val.app V (SheafOfModules.ScalarHomOrdinary.pure R M N V x y)) =
      SheafOfModules.ScalarHomOrdinary.pure S _ _ V
        ((am.unit.app M).val.app V x) ((am.unit.app N).val.app V y) := by
    change ((SheafOfModules.monoidalCategory S).tensorHom (eF M).inv
      (eF N).inv).val.app V
      ((SheafOfModules.ScalarHomOrdinary.tensorIsoSite S _ _).inv.val.app V
        ((core.tensorComparison M N).hom.val.app V
          ((SheafOfModules.changeOfRingsHomOfUniverses a _
            (SheafOfModules.ScalarHomOrdinary.tensorIsoSite R M N).hom).val.app V
            ((eF _).hom.val.app V _)))) = _
    rw [eF_unit,
      SheafOfModules.scalarExtension_map_tmul a
        (SheafOfModules.ScalarHomOrdinary.tensorIsoSite R M N).hom V 1
        (SheafOfModules.ScalarHomOrdinary.pure R M N V x y),
      SheafOfModules.ScalarHomOrdinary.tensorIsoSite_pure R M N V x y,
      core.tensor_tmul M N V 1 x y,
      SheafOfModules.ScalarHomOrdinary.tensorIsoSite_inv_pure S _ _ V _ _,
      SheafOfModules.ScalarHomOrdinary.pure_map S (eF M).inv (eF N).inv V _ _,
      eF_inv_unit, eF_inv_unit]
  have he {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N') :
      F.map (f ⊗ₘ g) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map f ⊗ₘ F.map g) := by
    apply (am.homEquiv _ _).injective
    apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext R M N
      ((SheafOfModules.scalarRestriction a).obj _)
    intro V x y
    have hun (P Q : A) (h : P ⟶ Q) (z : P.val.obj V) :
        (F.map h).val.app V ((am.unit.app P).val.app V z) =
          (am.unit.app Q).val.app V (h.val.app V z) :=
      (congrArg (fun k ↦ k.val.app V z) (am.unit.naturality h)).symm
    change (e M' N').hom.val.app V
      ((F.map (f ⊗ₘ g)).val.app V
        ((am.unit.app _).val.app V (SheafOfModules.ScalarHomOrdinary.pure R M N V x y))) =
      (F.map f ⊗ₘ F.map g).val.app V
        ((e M N).hom.val.app V
          ((am.unit.app _).val.app V (SheafOfModules.ScalarHomOrdinary.pure R M N V x y)))
    rw [hun, SheafOfModules.ScalarHomOrdinary.pure_map R f g V x y, hgen, hgen,
      SheafOfModules.ScalarHomOrdinary.pure_map S (F.map f) (F.map g) V _ _, hun, hun]
  have hu (M : A) (V : Cᵒᵖ) (x : M.val.obj V) :
      scalarSection.{c, v, r} a F hF M V 1 x =
        (am.unit.app M).val.app V x := by
    have hh := congrArg ((eqToHom (hF M).symm).val.app V) (unit_normalized M V x)
    change (eqToHom (hF M).symm).val.app V
      ((eqToHom (hF M)).val.app V ((am.unit.app M).val.app V x)) =
        scalarSection.{c, v, r} a F hF M V 1 x at hh
    rw [← hh]
    change ((eqToHom (hF M) ≫ eqToHom (hF M).symm).val.app V)
      ((am.unit.app M).val.app V x) = _
    simp only [eqToHom_trans, eqToHom_refl]
    rfl
  exact ⟨am, e, he, hu, hgen⟩

private theorem scalarTensorTotal
    (F : ScalarMod.{c, v, r} R ⥤ ScalarMod.{c, v, r} S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hF N).symm)
    [F.Additive] :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients S
    letI := SheafOfModules.monoidalCategory S
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
    ∃ b : coefficientTotalTensor.{r, c, v} J R ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj
          ((MonoidalCategory.curriedTensor (ScalarMod.{c, v, r} S)).map₂CochainComplex),
    ∀ (P Q : CochainComplex (ScalarMod.{c, v, r} R) ℤ) (p q k : ℤ) (h : p + q = k)
      (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      ((b.hom.app (P, Q)).f k).val.app V
        (scalarSection.{c, v, r} a F hF _ V 1
          (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
      coefficientTensorGenerator.{r, c, v} J S
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k h V
        (scalarSection.{c, v, r} a F hF _ V 1 x) (scalarSection.{c, v, r} a F hF _ V 1 y) := by
  classical
  dsimp only
  let A := ScalarMod.{c, v, r} R
  let B := ScalarMod.{c, v, r} S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.tensorPreadditive R
  let := SheafOfModules.tensorPreadditive S
  have := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  have := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  have := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  obtain ⟨am, e, he, hu, hgen⟩ := scalarTensorAdjunctionComparison.{c, v, r} a F hF hmF
  obtain ⟨b, hb⟩ := tensorTotalComparisonOfAdjunction F e he _ am
  refine ⟨b, ?_⟩
  intro P Q p q k h V x y
  rw [hu, hu, hu]
  let EC := F.mapHomologicalComplex (.up ℤ)
  let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q k h
  let ι' := CochainComplex.ιMapBifunctor (EC.obj P) (EC.obj Q) (curriedTensor B) p q k h
  have hi : F.map ι ≫ (b.hom.app (P, Q)).f k = (e (P.X p) (Q.X q)).hom ≫ ι' :=
    hb P Q p q k h
  have hu' := congrArg (fun f ↦ f.val.app V
    (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))
    (am.unit.naturality ι)
  have hh := congrArg (fun f ↦ f.val.app V
    (((am.unit.app _).val.app V)
      (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) hi
  change ((b.hom.app (P, Q)).f k).val.app V
    (((am.unit.app _).val.app V)
      (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) = _
  change ((am.unit.app _).val.app V)
    (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) =
    (F.map ι).val.app V (((am.unit.app _).val.app V)
      (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) at hu'
  erw [hu']
  exact hh.trans (congrArg (ι'.val.app V) (hgen _ _ V x y))

end

end ScalarTotal

universe a b d e f g

private theorem strictTowerComparison
    {A : Type a} [Category.{b} A] {B : Type d} [Category.{e} B]
    {C : Type f} [Category.{g} C] (L : A ⥤ B)
    (F : ℕ → B ⥤ C) (t : ∀ n, F (n + 1) ⟶ F n)
    (G : ℕ → A ⥤ C) (s : ∀ n, G (n + 1) ⟶ G n)
    (c : ∀ n, L ⋙ F n ≅ G n)
    (hc : ∀ n, Functor.whiskerLeft L (t n) ≫ (c n).hom =
      (c (n + 1)).hom ≫ s n) :
    Nonempty (L ⋙ (Functor.ofOpSequence t).flip ≅ (Functor.ofOpSequence s).flip) := by
  let α (P : A) : (L ⋙ (Functor.ofOpSequence t).flip).obj P ⟶
      (Functor.ofOpSequence s).flip.obj P :=
    NatTrans.ofOpSequence (fun n ↦ (c n).hom.app P) (by
      intro n
      have hh := congrArg (fun φ ↦ NatTrans.app φ P) (hc n)
      simpa only [Functor.comp_obj, Functor.flip_obj_map,
        Functor.ofOpSequence_map_homOfLE_succ, NatTrans.comp_app,
        Functor.whiskerLeft_app] using hh)
  have hα (P : A) : IsIso (α P) := by
    have hn (n : ℕᵒᵖ) : IsIso ((α P).app n) := by
      change IsIso ((c n.unop).hom.app P)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  refine ⟨NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (α P) (hα P)) ?_⟩
  intro P Q φ
  apply NatTrans.ext
  funext n
  exact (c n.unop).hom.naturality φ

universe h i j k

private theorem restrictedTowerComparison
    {A : Type a} [Category.{b} A] {B : Type d} [Category.{e} B]
    {C : Type f} [Category.{g} C]
    {D : ℕ → Type h} [∀ n, Category.{i} (D n)]
    {E' : ℕ → Type j} [∀ n, Category.{k} (E' n)]
    (L : A ⥤ B) (F : ∀ n, B ⥤ D n)
    (K : ∀ n, A ⥤ E' n) (M : ∀ n, E' n ⥤ D n) (R : ∀ n, D n ⥤ C)
    (t : ∀ n, F (n + 1) ⋙ R (n + 1) ⟶ F n ⋙ R n)
    (s : ∀ n, K (n + 1) ⋙ M (n + 1) ⋙ R (n + 1) ⟶ K n ⋙ M n ⋙ R n)
    (b : ∀ n, L ⋙ F n ≅ K n ⋙ M n)
    (hb : ∀ n, Functor.whiskerLeft L (t n) ≫
      (Functor.isoWhiskerRight (b n) (R n)).hom =
      (Functor.isoWhiskerRight (b (n + 1)) (R (n + 1))).hom ≫ s n) :
    Nonempty (L ⋙ (Functor.ofOpSequence (X := fun n ↦ F n ⋙ R n) t).flip ≅
      (Functor.ofOpSequence (X := fun n ↦ K n ⋙ M n ⋙ R n) s).flip) := by
  let c n : L ⋙ (F n ⋙ R n) ≅ K n ⋙ M n ⋙ R n :=
    (Functor.associator L (F n) (R n)).symm ≪≫
      Functor.isoWhiskerRight (b n) (R n) ≪≫ Functor.associator (K n) (M n) (R n)
  apply strictTowerComparison L (fun n ↦ F n ⋙ R n) t
    (fun n ↦ K n ⋙ M n ⋙ R n) s c
  intro n
  apply NatTrans.ext
  funext P
  have hh := congrArg (fun φ ↦ NatTrans.app φ P) (hb n)
  simpa only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using hh

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  SheafOfModules.changeOfRings PresheafOfModules.sheafification

private theorem finiteTensorComparison (n : ℕ) :
    ∃ b : coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X) ⋙
        unrestrictedIntegralFiniteComplex l E X n ≅
      (unrestrictedIntegralFiniteComplex l E X n).prod
        (unrestrictedIntegralFiniteComplex l E X n) ⋙
          Functor.uncurry.obj
            ((MonoidalCategory.curriedTensor
              (integralOperationsFiniteModules l E X n)).map₂CochainComplex),
    ∀ (P Q : CochainComplex (integralTowerModules l E X) ℤ) (p q : ℤ)
      (V : X.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      ((b.hom.app (P, Q)).f (p + q)).val.app V
        (unrestrictedIntegralTensorSection l E X n _ V 1
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl V x y)) =
      integralOperationsTotalTensorSection l E X n P Q p q V
        (unrestrictedIntegralTensorSection l E X n _ V 1 x)
        (unrestrictedIntegralTensorSection l E X n _ V 1 y) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : (unrestrictedIntegralReductionFunctor l E X n).Additive :=
    (unrestrictedIntegralReductionExistence l E X n).choose_spec.choose_spec.choose_spec.choose
  obtain ⟨b, hb⟩ := scalarTensorTotal.{t + 1, t, u}
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (unrestrictedIntegralReductionFunctor l E X n)
    (fun M ↦ (unrestrictedIntegralReductionExistence l E X n).choose_spec.choose M)
    (fun f ↦ (unrestrictedIntegralReductionExistence l E X n).choose_spec.choose_spec.choose f)
  refine ⟨b, ?_⟩
  intro P Q p q V x y
  exact hb P Q p q (p + q) rfl V x y

attribute [local irreducible] coefficientTotalTensor

/-- Scalar extension of the ordinary total tensor identifies its strict quotient
 tower with the tower of the two separately reduced total tensors.
Source: Stacks 03EL, 06YM, 06YY; Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-integral-tensor-reduction-tower-comparison).
Proof: in bidegree (p,q) send s tensor (x tensor y) to
(s tensor x) tensor (1 tensor y). The inverse multiplies the two scalar factors.
The balanced tensor identities give inverse linear maps. Sheafify and sum over
p+q=k; these maps commute with each signed differential summand. They are natural
in chain maps. Consecutive quotient maps send each scalar to its reduction, so
both routes send s tensor (x tensor y) to (rho(s) tensor x) tensor (1 tensor y).
Pure tensors, sheafification and the total coproduct determine the equality.
Thus the level isomorphisms give the asserted natural isomorphism of strict towers. -/
theorem integralTensorReductionTowerComparison :
    Nonempty (coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X) ⋙
        (Functor.ofOpSequence
          (X := fun n ↦ unrestrictedIntegralComplexFunctor l E X n)
          (unrestrictedIntegralTransition l E X)).flip ≅
      integralOperationsTensorTowerFunctor l E X) := by
  have h (n : ℕ) := finiteTensorComparison l E X n
  let b n := (h n).choose
  have hb (n : ℕ) (P Q : CochainComplex (integralTowerModules l E X) ℤ)
      (p q : ℤ) (V : X.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :=
    (h n).choose_spec P Q p q V x y
  have hc (n : ℕ) := integralTensorTransitionCompatibility l E X b hb n
  exact restrictedTowerComparison
    (coefficientTotalTensor.{u, t + 1, t} (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X))
    (fun n ↦ unrestrictedIntegralFiniteComplex l E X n)
    (fun n ↦ (unrestrictedIntegralFiniteComplex l E X n).prod
      (unrestrictedIntegralFiniteComplex l E X n))
    (fun n ↦ Functor.uncurry.obj ((MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E X n)).map₂CochainComplex))
    (fun n ↦ integralOperationsRestrict l E X n)
    (unrestrictedIntegralTransition l E X) (integralOperationsTensorTransition l E X) b hc

end WeilConjectures
