/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import Mathlib.CategoryTheory.Sites.LocallyBijective
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
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Compatibility of the normalized tensor comparison with quotient transitions

Source: Stacks Project, Modules on Sites, tensor-product section, Tag 03EL;
Bhatt--Scholze, Definition 3.4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory constantSheaf
  completedIntegralCoefficientSheafUnrestricted HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence

private theorem pure_local_ext
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r})
    (M N H : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : Cᵒᵖ ⥤ AddCommGrpCat.{r})
    (f g : ∀ V : Cᵒᵖ, T.obj V →
      ((SheafOfModules.monoidalCategory
        R).tensorObj M N).val.obj V →+
        H.val.obj V)
    (hf : ∀ {V W : Cᵒᵖ} (i : V ⟶ W) (s : T.obj V) (z),
      H.val.map i (f V s z) = f W (T.map i s)
        (((SheafOfModules.monoidalCategory
          R).tensorObj M N).val.map i z))
    (hg : ∀ {V W : Cᵒᵖ} (i : V ⟶ W) (s : T.obj V) (z),
      H.val.map i (g V s z) = g W (T.map i s)
        (((SheafOfModules.monoidalCategory
          R).tensorObj M N).val.map i z))
    (h : ∀ (V : Cᵒᵖ) (s : T.obj V) (x : M.val.obj V) (y : N.val.obj V),
      f V s (SheafOfModules.ScalarHomOrdinary.pure
        R M N V x y) =
      g V s (SheafOfModules.ScalarHomOrdinary.pure
        R M N V x y))
    (V : Cᵒᵖ) (s : T.obj V) (z) : f V s z = g V s z := by
  let := PresheafOfModules.monoidalCategory (R := R.obj)
  let W := (MonoidalCategory.tensorObj M.val N.val).presheaf
  let e := SheafOfModules.tensorObjIsoSheafification (R := R) M N
  let η := toSheafify J W
  let z' := e.hom.val.app V z
  have hH : Presieve.IsSheaf J (H.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{r}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf J H.val.presheaf
        (CategoryTheory.forget AddCommGrpCat.{r}) H.isSheaf)
  apply (hH.isSeparated _ (Presheaf.imageSieve_mem J η z')).ext
  intro U i hi
  obtain ⟨w, hw⟩ := hi
  change H.val.map i.op (f V s z) = H.val.map i.op (g V s z)
  rw [hf, hg]
  have hz : ((SheafOfModules.monoidalCategory R).tensorObj M N).val.map i.op z =
      e.inv.val.app (op U) (η.app (op U) w) := by
    have hn := PresheafOfModules.naturality_apply e.hom.val i.op z
    have he := congrArg (e.inv.val.app (op U)) (hw.trans hn.symm)
    have hh (a) : e.inv.val.app (op U) (e.hom.val.app (op U) a) = a :=
      ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.val.app (op U)) e.hom_inv_id) a
    exact (he.trans (hh _)).symm
  rw [hz]
  clear hw hz
  induction w using TensorProduct.inductionOn with
  | tmul x y => exact h (op U) (T.map i.op s) x y
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

section ExtensionGenerators
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)

private abbrev GMod (A : Sheaf J CommRingCat.{r}) := SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)

private def extensionSectionAdd (M : GMod R) (V : Cᵒᵖ) (s : S.obj.obj V) :
    M.val.obj V →+ (SheafOfModules.changeOfRings a M).val.obj V where
  toFun := SheafOfModules.UnrestrictedTowerProof.tensorSection a M V s
  map_zero' := by
    unfold SheafOfModules.UnrestrictedTowerProof.tensorSection
    simp only [TensorProduct.tmul_zero, map_zero]
  map_add' := by
    intro x y
    unfold SheafOfModules.UnrestrictedTowerProof.tensorSection
    simp only [TensorProduct.tmul_add, map_add]

omit [EssentiallySmall.{r} C] in
private theorem extensionSection_naturality (M : GMod R)
    {V W : Cᵒᵖ} (i : V ⟶ W) (s : S.obj.obj V) (z : M.val.obj V) :
    (SheafOfModules.changeOfRings a M).val.map i
      (SheafOfModules.UnrestrictedTowerProof.tensorSection a M V s z) =
    SheafOfModules.UnrestrictedTowerProof.tensorSection a M W
      (S.obj.map i s) (M.val.map i z) := by
  let η := toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf
  have hn := NatTrans.naturality_apply η i
    (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] z)
  exact hn.symm.trans (congrArg (η.app W)
    (SheafOfModules.UnrestrictedTowerProof.restriction_tmul a M i s z))

private theorem extended_tensor_hom_ext (M N H : GMod R)
    {f g : (SheafOfModules.UnrestrictedTowerProof.res a).obj
      (SheafOfModules.changeOfRings a ((SheafOfModules.monoidalCategory R).tensorObj M N)) ⟶ H}
    (h : ∀ (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) (y : N.val.obj V),
      f.val.app V (SheafOfModules.UnrestrictedTowerProof.tensorSection a _ V s
        (SheafOfModules.ScalarHomOrdinary.pure R M N V x y)) =
      g.val.app V (SheafOfModules.UnrestrictedTowerProof.tensorSection a _ V s
        (SheafOfModules.ScalarHomOrdinary.pure R M N V x y))) : f = g := by
  apply SheafOfModules.UnrestrictedTowerProof.restricted_hom_ext a _ H
  intro V s z
  let f' (W : Cᵒᵖ) (t : S.obj.obj W) :=
    (f.val.app W).hom.toAddMonoidHom.comp (extensionSectionAdd a _ W t)
  let g' (W : Cᵒᵖ) (t : S.obj.obj W) :=
    (g.val.app W).hom.toAddMonoidHom.comp (extensionSectionAdd a _ W t)
  have hf {V W : Cᵒᵖ} (i : V ⟶ W) (s : S.obj.obj V) (z) :
      H.val.map i (f' V s z) = f' W (S.obj.map i s)
        (((SheafOfModules.monoidalCategory R).tensorObj M N).val.map i z) := by
    change H.val.map i (f.val.app V
      (SheafOfModules.UnrestrictedTowerProof.tensorSection a _ V s z)) =
      f.val.app W (SheafOfModules.UnrestrictedTowerProof.tensorSection a _ W
        (S.obj.map i s) (((SheafOfModules.monoidalCategory R).tensorObj M N).val.map i z))
    rw [← PresheafOfModules.naturality_apply f.val i]
    exact congrArg (f.val.app W) (extensionSection_naturality a _ i s z)
  have hg {V W : Cᵒᵖ} (i : V ⟶ W) (s : S.obj.obj V) (z) :
      H.val.map i (g' V s z) = g' W (S.obj.map i s)
        (((SheafOfModules.monoidalCategory R).tensorObj M N).val.map i z) := by
    change H.val.map i (g.val.app V
      (SheafOfModules.UnrestrictedTowerProof.tensorSection a _ V s z)) =
      g.val.app W (SheafOfModules.UnrestrictedTowerProof.tensorSection a _ W
        (S.obj.map i s) (((SheafOfModules.monoidalCategory R).tensorObj M N).val.map i z))
    rw [← PresheafOfModules.naturality_apply g.val i]
    exact congrArg (g.val.app W) (extensionSection_naturality a _ i s z)
  exact pure_local_ext R M N H (S.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r} ⋙
      forget₂ RingCat.{r} AddCommGrpCat.{r})
    f' g' hf hg h V s z

private def identifiedSection (F : GMod R ⥤ GMod S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (M : GMod R) (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) :
    (F.obj M).val.obj V :=
  (eqToHom (hF M).symm).val.app V
    (SheafOfModules.UnrestrictedTowerProof.tensorSection a M V s x)

omit [EssentiallySmall.{r} C] in
private theorem identified_map_section (F : GMod R ⥤ GMod S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hF N).symm)
    {M N : GMod R} (f : M ⟶ N) (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) :
    (F.map f).val.app V (identifiedSection a F hF M V s x) =
      identifiedSection a F hF N V s (f.val.app V x) := by
  have hc (z : (SheafOfModules.changeOfRings a M).val.obj V) :
      (eqToHom (hF M)).val.app V ((eqToHom (hF M).symm).val.app V z) = z :=
    ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app V) (eqToHom_trans (hF M).symm (hF M))) z
  rw [hmF]
  change (eqToHom (hF N).symm).val.app V
    ((SheafOfModules.changeOfRingsHom a M f).val.app V
      ((eqToHom (hF M)).val.app V ((eqToHom (hF M).symm).val.app V
        (SheafOfModules.UnrestrictedTowerProof.tensorSection a M V s x)))) = _
  rw [hc]
  exact congrArg ((eqToHom (hF N).symm).val.app V)
    (SheafOfModules.UnrestrictedTowerProof.map_tensorSection a M f V s x)

private theorem identified_tensor_hom_ext (F : GMod R ⥤ GMod S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (M N H : GMod R)
    {f g : (F ⋙ SheafOfModules.UnrestrictedTowerProof.res a).obj
      ((SheafOfModules.monoidalCategory R).tensorObj M N) ⟶ H}
    (h : ∀ (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) (y : N.val.obj V),
      f.val.app V (identifiedSection a F hF _ V s
        (SheafOfModules.ScalarHomOrdinary.pure R M N V x y)) =
      g.val.app V (identifiedSection a F hF _ V s
        (SheafOfModules.ScalarHomOrdinary.pure R M N V x y))) : f = g := by
  let e := (SheafOfModules.UnrestrictedTowerProof.res a).map
    (eqToHom (hF ((SheafOfModules.monoidalCategory R).tensorObj M N)).symm)
  apply (cancel_epi e).mp
  exact extended_tensor_hom_ext a M N H h

omit [EssentiallySmall.{r} C] in
private theorem identifiedSection_smul (F : GMod R ⥤ GMod S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (M : GMod R) (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) :
    identifiedSection a F hF M V s x = s • identifiedSection a F hF M V 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf a M)
  change (eqToHom (hF M).symm).val.app V
    ((η.app V) (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)) =
      s • (eqToHom (hF M).symm).val.app V
        ((η.app V) ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))
  erw [← map_smul, ← map_smul]
  congr 2
  change s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x =
    (s * 1) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x
  rw [mul_one]

private theorem pure_smul_left (M N : GMod R) (V : Cᵒᵖ) (s : R.obj.obj V)
    (x : M.val.obj V) (y : N.val.obj V) :
    SheafOfModules.ScalarHomOrdinary.pure R M N V (s • x) y =
      s • SheafOfModules.ScalarHomOrdinary.pure R M N V x y := by
  let := PresheafOfModules.monoidalCategory (R := R.obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).unit.app
      (MonoidalCategory.tensorObj M.val N.val)
  let e := SheafOfModules.tensorObjIsoSheafification (R := R) M N
  change e.inv.val.app V (η.app V ((s • x) ⊗ₜ[R.obj.obj V] y)) =
    s • e.inv.val.app V (η.app V (x ⊗ₜ[R.obj.obj V] y))
  erw [← map_smul, ← map_smul, TensorProduct.smul_tmul']
  rfl

end ExtensionGenerators

section TotalGenerators
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

private theorem total_extension_hom_ext (F : GMod R ⥤ GMod S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hF N).symm)
    [PreservesColimitsOfSize.{0, 0} F]
    (P Q : CochainComplex (GMod R) ℤ) (k : ℤ) (H : GMod R)
    {f g : (F ⋙ SheafOfModules.UnrestrictedTowerProof.res a).obj
      (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X k) ⟶ H}
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (V : Cᵒᵖ) (s : S.obj.obj V)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      f.val.app V (identifiedSection a F hF _ V s
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq V x y)) =
      g.val.app V (identifiedSection a F hF _ V s
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq V x y))) : f = g := by
  let A := GMod R
  let := SheafOfModules.monoidalCategory R
  have := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  have := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let U := SheafOfModules.UnrestrictedTowerProof.res a
  have hU (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
    have : PreservesColimitsOfShape D (U ⋙ SheafOfModules.toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape D (SheafOfModules.toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))
    have : ReflectsColimitsOfShape D (SheafOfModules.toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves U (SheafOfModules.toSheaf _)
  have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {D} instD ↦ @hU D instD⟩
  let B := (((MonoidalCategory.curriedTensor A).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj P).obj Q
  let π := ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)
  have hc := isColimitOfPreserves (F ⋙ U) (B.toGradedObject.isColimitCofanMapObj π k)
  apply hc.hom_ext
  intro j
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩⟩
  let ι := CochainComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor A) p q k hpq
  change (F ⋙ U).map ι ≫ f = (F ⋙ U).map ι ≫ g
  apply identified_tensor_hom_ext a F hF (P.X p) (Q.X q) H
  intro V s x y
  change f.val.app V ((F.map ι).val.app V
      (identifiedSection a F hF _ V s
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) =
    g.val.app V ((F.map ι).val.app V
      (identifiedSection a F hF _ V s
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)))
  rw [identified_map_section a F hF hmF]
  exact h p q hpq V s x y

private theorem tensorGenerator_smul_left (P Q : CochainComplex (GMod R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ) (s : R.obj.obj V)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    coefficientTensorGenerator.{r, c, v} J R P Q p q k h V (s • x) y =
      s • coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y := by
  let := SheafOfModules.monoidalCategory R
  have := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  have := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let ι := CochainComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor (GMod R))
    p q k h
  change ι.val.app V
    (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V (s • x) y) =
      s • ι.val.app V
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)
  rw [pure_smul_left, map_smul]

omit [EssentiallySmall.{max c v r} C] in
private theorem extension_preserves_small_colimits (F : GMod R ⥤ GMod S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hF N).symm) :
    PreservesColimitsOfSize.{0, 0} F := by
  let e : F ≅ SheafOfModules.CoefficientOrdinaryProof.tensorFunctor a :=
    NatIso.ofComponents (fun M ↦ eqToIso (hF M)) (by
      intro M N f
      change F.map f ≫ eqToHom (hF N) =
        eqToHom (hF M) ≫ SheafOfModules.changeOfRingsHom a M f
      rw [hmF]
      simp)
  let := ((SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction a).ofNatIsoLeft
    e.symm).isLeftAdjoint
  infer_instance

end TotalGenerators

private theorem reduction_transition_apply (n : ℕ)
    (P : CochainComplex (integralTowerModules l E X) ℤ) (i : ℤ) (V : X.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E X (n + 1)).obj.obj V)
    (x : (P.X i).val.obj V) :
    (((unrestrictedIntegralTransition l E X n).app P).f i).val.app V
      (unrestrictedIntegralTensorSection l E X (n + 1) (P.X i) V s x) =
    unrestrictedIntegralTensorSection l E X n (P.X i) V
      ((integralCoefficientSheafTransition l E X n).hom.app V s) x :=
  (unrestrictedIntegralTransition_existsUnique l E X n).exists.choose_spec P i V s x

private theorem tensor_transition_apply (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) (p q : ℤ) (V : X.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E X (n + 1)).obj P).X p).val.obj V)
    (y : (((unrestrictedIntegralFiniteComplex l E X (n + 1)).obj Q).X q).val.obj V) :
    (((integralOperationsTensorTransition l E X n).app (P, Q)).f (p + q)).val.app V
      (integralOperationsTotalTensorSection l E X (n + 1) P Q p q V x y) =
    integralOperationsTotalTensorSection l E X n P Q p q V
      ((((unrestrictedIntegralTransition l E X n).app P).f p).val.app V x)
      ((((unrestrictedIntegralTransition l E X n).app Q).f q).val.app V y) :=
  (integralOperationsTensorTransition_existsUnique l E X n).exists.choose_spec P Q p q V x y

-- Check scalar normalization separately so the transition proof can reuse it directly.
private theorem integralTensorComparison_apply_scalar
    (b : ∀ m : ℕ, coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X) ⋙
        unrestrictedIntegralFiniteComplex l E X m ≅
      (unrestrictedIntegralFiniteComplex l E X m).prod
        (unrestrictedIntegralFiniteComplex l E X m) ⋙
          Functor.uncurry.obj
            ((MonoidalCategory.curriedTensor
              (integralOperationsFiniteModules l E X m)).map₂CochainComplex))
    (hb : ∀ (m : ℕ) (P Q : CochainComplex (integralTowerModules l E X) ℤ)
      (p q : ℤ) (V : X.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      (((b m).hom.app (P, Q)).f (p + q)).val.app V
        (unrestrictedIntegralTensorSection l E X m _ V 1
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl V x y)) =
        integralOperationsTotalTensorSection l E X m P Q p q V
          (unrestrictedIntegralTensorSection l E X m _ V 1 x)
          (unrestrictedIntegralTensorSection l E X m _ V 1 y))
    (m : ℕ)
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) (p q : ℤ)
    (V : X.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l E X m).obj.obj V)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((b m).hom.app (P, Q)).f (p + q)).val.app V
      (unrestrictedIntegralTensorSection l E X m _ V s
        (coefficientTensorGenerator.{u, t + 1, t}
          (AlgebraicGeometry.Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl V x y)) =
      integralOperationsTotalTensorSection l E X m P Q p q V
        (unrestrictedIntegralTensorSection l E X m _ V s x)
        (unrestrictedIntegralTensorSection l E X m _ V 1 y) := by
  classical
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let F := (unrestrictedIntegralReductionExistence l E X m).choose
  let hF := (unrestrictedIntegralReductionExistence l E X m).choose_spec.choose
  have hs := identifiedSection_smul
    (completedIntegralCommRingProjectionUnrestricted l E X m) F hF
    (((coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q)).X (p + q)) V s
    (coefficientTensorGenerator.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl V x y)
  have hx := identifiedSection_smul
    (completedIntegralCommRingProjectionUnrestricted l E X m) F hF
    (P.X p) V s x
  have hg := tensorGenerator_smul_left.{t + 1, t, u}
    (R := integralCoefficientCommRingSheaf l E X m)
    ((unrestrictedIntegralFiniteComplex l E X m).obj P)
    ((unrestrictedIntegralFiniteComplex l E X m).obj Q) p q (p + q) rfl V s
    (unrestrictedIntegralTensorSection l E X m _ V 1 x)
    (unrestrictedIntegralTensorSection l E X m _ V 1 y)
  calc
    _ = (((b m).hom.app (P, Q)).f (p + q)).val.app V
        (s • unrestrictedIntegralTensorSection l E X m _ V 1
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            P Q p q (p + q) rfl V x y)) :=
      congrArg ((((b m).hom.app (P, Q)).f (p + q)).val.app V) hs
    _ = s • (((b m).hom.app (P, Q)).f (p + q)).val.app V
        (unrestrictedIntegralTensorSection l E X m _ V 1
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            P Q p q (p + q) rfl V x y)) := map_smul _ s _
    _ = s • integralOperationsTotalTensorSection l E X m P Q p q V
        (unrestrictedIntegralTensorSection l E X m _ V 1 x)
        (unrestrictedIntegralTensorSection l E X m _ V 1 y) := by rw [hb]
    _ = integralOperationsTotalTensorSection l E X m P Q p q V
        (s • unrestrictedIntegralTensorSection l E X m _ V 1 x)
        (unrestrictedIntegralTensorSection l E X m _ V 1 y) := hg.symm
    _ = _ := congrArg
      (fun z ↦ integralOperationsTotalTensorSection l E X m P Q p q V z
        (unrestrictedIntegralTensorSection l E X m _ V 1 y)) hx.symm

-- Compare the two scalar presentations and their maps on total summand generators.
/-- The generator-normalized total scalar-extension comparison commutes with the
actual consecutive quotient transitions.
Source: Stacks 03EL, tensor-product section; Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-integral-tensor-transition-compatibility).
Proof: work in a fixed degree and precompose with each extended total summand.
The extension functor and scalar restriction preserve these coproducts. On each
summand, sheafification and tensor generation reduce the equation to the sections
s tensor (x tensor y). Linearity over the finite coefficient ring extends the
normalization from scalar 1 to scalar s. The left route reduces s and then sends
it to (rho(s) tensor x) tensor (1 tensor y). The right route first sends it to
(s tensor x) tensor (1 tensor y), then applies the two normalized reduction maps,
with exactly the same result. The generator equations of the recorded tensor
transition give this last assertion for all finite sections. The generators
locally generate the sheafified tensors, so the maps on each summand agree;
the coproduct injections give equality in every degree, hence of chain maps.
Naturality gives the displayed equality of natural transformations. No boundedness
or flatness assumption is used; the proof also applies to the zero ring or empty site. -/
theorem integralTensorTransitionCompatibility
    (b : ∀ n : ℕ, coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X) ⋙
        unrestrictedIntegralFiniteComplex l E X n ≅
      (unrestrictedIntegralFiniteComplex l E X n).prod
        (unrestrictedIntegralFiniteComplex l E X n) ⋙
          Functor.uncurry.obj
            ((MonoidalCategory.curriedTensor
              (integralOperationsFiniteModules l E X n)).map₂CochainComplex))
    (hb : ∀ (n : ℕ) (P Q : CochainComplex (integralTowerModules l E X) ℤ)
      (p q : ℤ) (V : X.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      (((b n).hom.app (P, Q)).f (p + q)).val.app V
        (unrestrictedIntegralTensorSection l E X n _ V 1
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl V x y)) =
        integralOperationsTotalTensorSection l E X n P Q p q V
          (unrestrictedIntegralTensorSection l E X n _ V 1 x)
          (unrestrictedIntegralTensorSection l E X n _ V 1 y)) (n : ℕ) :
    Functor.whiskerLeft (coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X))
      (unrestrictedIntegralTransition l E X n) ≫
        (Functor.isoWhiskerRight (b n) (integralOperationsRestrict l E X n)).hom =
    (Functor.isoWhiskerRight (b (n + 1)) (integralOperationsRestrict l E X (n + 1))).hom ≫
      integralOperationsTensorTransition l E X n := by
  classical
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let F (m : ℕ) := (unrestrictedIntegralReductionExistence l E X m).choose
  let hF (m : ℕ) := (unrestrictedIntegralReductionExistence l E X m).choose_spec.choose
  let hmF (m : ℕ) {M N : integralTowerModules l E X} (f : M ⟶ N) :
      (F m).map f = eqToHom (hF m M) ≫
        SheafOfModules.changeOfRingsHom
          (completedIntegralCommRingProjectionUnrestricted l E X m) M f ≫
          eqToHom (hF m N).symm :=
    (unrestrictedIntegralReductionExistence l E X m).choose_spec.choose_spec.choose f
  let hcolim (m : ℕ) : PreservesColimitsOfSize.{0, 0} (F m) :=
    extension_preserves_small_colimits.{t + 1, t, u}
      (completedIntegralCommRingProjectionUnrestricted l E X m) (F m) (hF m) (hmF m)
  have hbs (m : ℕ) (P Q : CochainComplex (integralTowerModules l E X) ℤ)
      (p q : ℤ) (V : X.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf l E X m).obj.obj V)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :=
    integralTensorComparison_apply_scalar l E X b hb m P Q p q V s x y
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro k
  apply total_extension_hom_ext.{t + 1, t, u}
    (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
    (F (n + 1)) (hF (n + 1)) (hmF (n + 1)) P Q k
  intro p q hpq V s x y
  subst k
  change (((b n).hom.app (P, Q)).f (p + q)).val.app V
      ((((unrestrictedIntegralTransition l E X n).app
        ((coefficientTotalTensor.{u, t + 1, t}
          (AlgebraicGeometry.Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q))).f (p + q)).val.app V
        (unrestrictedIntegralTensorSection l E X (n + 1) _ V s
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl V x y))) =
    (((integralOperationsTensorTransition l E X n).app (P, Q)).f (p + q)).val.app V
      ((((b (n + 1)).hom.app (P, Q)).f (p + q)).val.app V
        (unrestrictedIntegralTensorSection l E X (n + 1) _ V s
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl V x y)))
  rw [reduction_transition_apply, hbs, hbs, tensor_transition_apply,
    reduction_transition_apply, reduction_transition_apply]
  simp only [map_one]

end WeilConjectures
