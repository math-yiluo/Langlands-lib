/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower

/-!
# Canonical reduction towers without a finite-field datum

Source: Bhatt--Scholze, Definition 3.5.2, p. 24; Stacks Tags 03EK and 06YY
(blueprint: def-weil-integral-reduction-tower).
The index n means the positive exponent n+1. All scalar extensions are the published
universal derived scalar extensions, with their specified K-flat comparisons.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kanRightAdjoint
    {C : Type*} {D : Type*} {H : Type*} {H' : Type*}
    [Category C] [Category D] [Category H] [Category H']
    {S : H' ⥤ H} {R : H ⥤ H'} (a : S ⊣ R)
    (q : C ⥤ D) (F : C ⥤ H) (RF : D ⥤ H)
    (ε : q ⋙ RF ⟶ F) [RF.IsRightKanExtension ε] :
    (RF ⋙ R).IsRightKanExtension
      ((Functor.associator q RF R).inv ≫ Functor.whiskerRight ε R) := by
  classical
  let ε' := (Functor.associator q RF R).inv ≫ Functor.whiskerRight ε R
  let lift (G : D ⥤ H') (b : q ⋙ G ⟶ F ⋙ R) : G ⟶ RF ⋙ R :=
    ((a.whiskerRight D).homEquiv G RF)
      (RF.liftOfIsRightKanExtension ε (G ⋙ S)
        (((a.whiskerRight C).homEquiv (q ⋙ G) F).symm b))
  have mate (G : D ⥤ H') (t : G ⟶ RF ⋙ R) :
      ((a.whiskerRight C).homEquiv (q ⋙ G) F).symm
          (Functor.whiskerLeft q t ≫ ε') =
        Functor.whiskerLeft q (((a.whiskerRight D).homEquiv G RF).symm t) ≫ ε := by
    ext X
    dsimp [Adjunction.homEquiv, Adjunction.whiskerRight, ε']
    simp only [Category.id_comp, Category.comp_id]
    rw [S.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
      Category.assoc] using
      congrArg (fun f ↦ S.map (t.app (q.obj X)) ≫ f)
        (a.counit.naturality (ε.app X))
  have fac (G : D ⥤ H') (b : q ⋙ G ⟶ F ⋙ R) :
      Functor.whiskerLeft q (lift G b) ≫ ε' = b := by
    apply ((a.whiskerRight C).homEquiv (q ⋙ G) F).symm.injective
    rw [mate]
    dsimp only [lift]
    rw [Equiv.symm_apply_apply]
    exact RF.liftOfIsRightKanExtension_fac ε (G ⋙ S) _
  have uniq (G : D ⥤ H') (b : q ⋙ G ⟶ F ⋙ R) (t : G ⟶ RF ⋙ R)
      (ht : Functor.whiskerLeft q t ≫ ε' = b) : t = lift G b := by
    apply ((a.whiskerRight D).homEquiv G RF).symm.injective
    apply RF.hom_ext_of_isRightKanExtension ε
    have h := congrArg (((a.whiskerRight C).homEquiv (q ⋙ G) F).symm) ht
    rw [mate] at h
    dsimp only [lift]
    rw [Equiv.symm_apply_apply]
    exact h.trans (RF.liftOfIsRightKanExtension_fac ε (G ⋙ S) _).symm
  constructor
  refine ⟨IsTerminal.ofUniqueHom
    (fun Z ↦ CostructuredArrow.homMk (lift Z.left Z.hom) (fac Z.left Z.hom)) ?_⟩
  intro Z m
  apply CostructuredArrow.hom_ext
  exact uniq Z.left Z.hom m.left (by simpa using m.w)

private theorem kanRightAdjointIso
    {C : Type*} {D : Type*} {H : Type*} {H' : Type*}
    [Category C] [Category D] [Category H] [Category H']
    {S : H' ⥤ H} {R : H ⥤ H'} (a : S ⊣ R)
    (q : C ⥤ D) (F : C ⥤ H) (RF : D ⥤ H)
    (ε : q ⋙ RF ⟶ F) [RF.IsRightKanExtension ε]
    (G : C ⥤ H') (e : F ⋙ R ≅ G) :
    (RF ⋙ R).IsRightKanExtension
      (((Functor.associator q RF R).inv ≫ Functor.whiskerRight ε R) ≫ e.hom) := by
  have h := kanRightAdjoint a q F RF ε
  apply (Functor.isRightKanExtension_iff_of_iso₂
    ((Functor.associator q RF R).inv ≫ Functor.whiskerRight ε R)
    (((Functor.associator q RF R).inv ≫ Functor.whiskerRight ε R) ≫ e.hom)
    e (Iso.refl _) ?_).1 h
  ext X
  simp

private theorem mappedCompositeEq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' : C} (a : A ⟶ B) (b : B ⟶ C') (c : A ⟶ C')
    (h : a ≫ b = c) : F.map a ≫ F.map b = F.map c :=
  (F.map_comp a b).symm.trans (congrArg F.map h)

private theorem unitCompatibilityOfComparisons
    {C : Type*} [Category C] {K A B U V : C}
    (a : K ⟶ A) (b : K ⟶ B) (t : A ⟶ B)
    (c : A ⟶ U) (d : B ⟶ V) [Mono d]
    (v : K ⟶ U) (w : K ⟶ V) (s : U ⟶ V)
    (ht : t ≫ d = c ≫ s) (ha : a ≫ c = v) (hb : b ≫ d = w)
    (hv : v ≫ s = w) : a ≫ t = b := by
  apply (cancel_mono d).1
  calc
    (a ≫ t) ≫ d = (a ≫ c) ≫ s := by rw [Category.assoc, ht, Category.assoc]
    _ = b ≫ d := by rw [ha, hv, hb]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{u})

local instance (priority := 4000) instSfIntegralReductionTowerSupplement1
    : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _

/-- Ordinary reduction read as a completed-coefficient module.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable abbrev sfReductionRestricted (n : ℕ) :=
  scalarReductionExtension.{u, u} l E X n ⋙ scalarReductionRestriction.{u, u} l E X n

private noncomputable instance sfRestrictionAdditive (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E X n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The ordinary reduction followed by restriction is additive.
Source: Stacks Tag 03CZ (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance sfReductionRestrictedAdditive (n : ℕ) :
    (sfReductionRestricted l E X n).Additive :=
  letI := scalarReductionExtensionAdditive.{u, u} l E X n
  letI := sfRestrictionLimits l E X n
  Functor.additive_of_preserves_binary_products _

/-- Derived reduction read as a completed-coefficient complex.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable abbrev sfDerivedReductionRestricted (n : ℕ) :=
  scalarReductionDerivedExtension.{u, u} l E X n ⋙ scalarReductionDerivedRestriction.{u, u} l E X n

/-- The sheafified pure tensor in the actual scalar-extension construction.
Source: Stacks Tag 03EK (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfReductionTensor (n : ℕ) (M : scalarReductionSource.{u, u} l E X)
    (U : X.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
    (x : M.val.obj U) : ((scalarReductionExtension.{u, u} l E X n).obj M).val.obj U :=
  (eqToHom ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose M).symm).val.app U
    ((CategoryTheory.toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E X n) M).presheaf).app U
        (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
          ((completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U).hom] x))

private noncomputable def sfZeroDifferentialComplex :
    scalarReductionSource.{u, u} l E X ⥤
      CochainComplex (scalarReductionSource.{u, u} l E X) ℤ where
  obj M :=
    { X := fun _ ↦ M
      d := fun _ _ ↦ 0
      shape := fun _ _ _ ↦ rfl
      d_comp_d' := fun _ _ _ _ _ ↦ by simp }
  map a := { f := fun _ ↦ a }

private theorem sfReductionTensor_hom_ext (n : ℕ)
    (M N : scalarReductionSource.{u, u} l E X)
    (a b : (sfReductionRestricted l E X n).obj M ⟶ N)
    (h : ∀ U s x, a.val.app U (sfReductionTensor l E X n M U s x) =
      b.val.app U (sfReductionTensor l E X n M U s x)) : a = b := by
  let e := (scalarReductionRestriction.{u, u} l E X n).map
    (eqToHom ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose M).symm)
  have he : e ≫ a = e ≫ b := by
    apply (SheafOfModules.toSheaf _).map_injective
    apply Sheaf.hom_ext
    apply CategoryTheory.sheafify_hom_ext _ _ _ N.isSheaf
    ext U z
    induction z using TensorProduct.inductionOn with
    | tmul s x => exact h U s x
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  exact (cancel_epi e).1 he

/-- The unique ordinary transition sends s tensor x to rho(s) tensor x.
Source: Stacks Tag 03EK; Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower).
Proof: the quotient projections commute, so the displayed formula is balanced over
completed coefficients. It commutes with restrictions and defines a sheafified tensor
map. Naturality follows on pure tensors. Tensor generation and sheafification give
uniqueness on each module, and hence uniqueness of the natural transformation. -/
theorem sfReductionTransition_existsUnique (n : ℕ) :
    ∃! τ : sfReductionRestricted l E X (n + 1) ⟶ sfReductionRestricted l E X n,
      ∀ (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E X (n + 1)).obj.obj U)
        (x : M.val.obj U),
        (τ.app M).val.app U (sfReductionTensor l E X (n + 1) M U s x) =
          sfReductionTensor l E X n M U
            ((integralCoefficientSheafTransition l E X n).hom.app U s) x := by
  let σ := (unrestrictedIntegralTransition_existsUnique.{u, u} l E X n).exists.choose
  let τ : sfReductionRestricted l E X (n + 1) ⟶ sfReductionRestricted l E X n :=
    { app := fun M ↦ (σ.app ((sfZeroDifferentialComplex l E X).obj M)).f 0
      naturality := fun M N a ↦ by
        exact congrArg (fun k ↦ k.f 0) (σ.naturality ((sfZeroDifferentialComplex l E X).map a)) }
  have hτ : ∀ (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf l E X (n + 1)).obj.obj U)
      (x : M.val.obj U),
      (τ.app M).val.app U (sfReductionTensor l E X (n + 1) M U s x) =
        sfReductionTensor l E X n M U
          ((integralCoefficientSheafTransition l E X n).hom.app U s) x := by
    intro M U s x
    exact (unrestrictedIntegralTransition_existsUnique.{u, u} l E X n).exists.choose_spec
      ((sfZeroDifferentialComplex l E X).obj M) 0 U s x
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext M
  apply sfReductionTensor_hom_ext l E X (n + 1) M
  intro U s x
  exact (hτ' M U s x).trans (hτ M U s x).symm

/-- The transition selected by its unique pure-tensor characterization.
Source: Stacks Tag 03EK (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfReductionTransition (n : ℕ) :
    sfReductionRestricted l E X (n + 1) ⟶ sfReductionRestricted l E X n :=
  (sfReductionTransition_existsUnique l E X n).exists.choose

attribute [local irreducible] sfReductionTransition

/-- The fixed derived comparison to termwise reduction, invertible on K-flat complexes.
Source: Stacks Tag 06YY (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfReductionRepresentativeComparison (n : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) :
    (sfDerivedReductionRestricted l E X n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((sfReductionRestricted l E X n).mapHomologicalComplex (.up ℤ)).obj P) :=
  cast (by rfl) ((scalarReductionDerivedRestriction.{u, u} l E X n).map
      ((scalarReductionCounit.{u, u} l E X n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension.{u, u} l E X n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))

/-- The reduction unit, normalized by the published tensor/restriction adjunction.
Source: Stacks Tags 03CZ and 06YY
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfDerivedReductionUnit (n : ℕ) :
    𝟭 (DerivedCategory (scalarReductionSource.{u, u} l E X)) ⟶
      sfDerivedReductionRestricted l E X n :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.unit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem sfUnitComparison (n : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P) :
    (sfDerivedReductionUnit l E X n).app (DerivedCategory.Q.obj P) ≫
        sfReductionRepresentativeComparison l E X n P =
      (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E X)).map
        (((scalarReductionExtension_adjunction.{u, u} l E X n).choose.mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  have h := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose_spec P hP
  have hu := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (scalarReductionExtension_adjunction.{u, u} l E X n).choose P
  have hq : (DerivedCategory.Qh (C := scalarReductionSource.{u, u} l E X)).map
      (((scalarReductionExtension_adjunction.{u, u} l E X n).choose.mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E X)).map
        (((scalarReductionExtension_adjunction.{u, u} l E X n).choose.mapHomologicalComplex
          (.up ℤ)).unit.app P) :=
    congrArg (DerivedCategory.Qh (C := scalarReductionSource.{u, u} l E X)).map hu
  dsimp only [sfDerivedReductionUnit, sfReductionRepresentativeComparison]
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact h.trans hq

private noncomputable def sfComparison (n : ℕ) :
    DerivedCategory.Qh ⋙ sfDerivedReductionRestricted l E X n ⟶
      (sfReductionRestricted l E X n).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  ((Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (scalarReductionCounit.{u, u} l E X n)
      (scalarReductionDerivedRestriction.{u, u} l E X n)) ≫
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((scalarReductionExtension.{u, u} l E X n).mapHomotopyCategory
        (.up ℤ)) (scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (sfReductionRestricted l E X n)) (.up ℤ)) DerivedCategory.Qh).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sfComparison_app (n : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) :
    (sfComparison l E X n).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      sfReductionRepresentativeComparison l E X n P := by
  simp only [sfComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.assoc]
  have hc :
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (sfReductionRestricted l E X n)) (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) = 𝟙 _ := by
    change (HomotopyCategory.quotient _ (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (sfReductionRestricted l E X n)) (.up ℤ)).hom.app P) = _
    have hi : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (sfReductionRestricted l E X n)) (.up ℤ)).hom.app P = 𝟙 _ := by
      ext i
      rfl
    rw [hi]
    exact (HomotopyCategory.quotient _ (.up ℤ)).map_id _
  rw [hc, DerivedCategory.Qh.map_id]
  exact congrArg
    (fun k ↦ (scalarReductionDerivedRestriction.{u, u} l E X n).map
      ((scalarReductionCounit.{u, u} l E X n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ k)
    ((Category.id_comp _).trans (Category.comp_id
      ((scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactorsh.hom.app
        (((scalarReductionExtension.{u, u} l E X n).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem sfComparison_universal (n : ℕ) :
    (sfDerivedReductionRestricted l E X n).IsLeftDerivedFunctor
      (sfComparison l E X n)
      (HomotopyCategory.quasiIso (scalarReductionSource.{u, u} l E X) (.up ℤ)) := by
  let L := scalarReductionDerivedExtension.{u, u} l E X n
  let R := scalarReductionDerivedRestriction.{u, u} l E X n
  let H := (scalarReductionExtension.{u, u} l E X n).mapHomotopyCategory (.up ℤ)
  let ε := scalarReductionCounit.{u, u} l E X n
  have : L.IsRightKanExtension ε :=
    (scalarReductionDerivedExistence.{u, u} l E X n).choose_spec.choose_spec.1.isRightKanExtension
  constructor
  exact kanRightAdjointIso
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    DerivedCategory.Qh (H ⋙ DerivedCategory.Qh) L ε _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sfComparison_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P) :
    IsIso (sfReductionRepresentativeComparison l E X n P) := by
  have hε : IsIso ((scalarReductionCounit.{u, u} l E X n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (scalarReductionDerivedExistence.{u, u} l E X n).choose_spec.choose_spec.2.2 P hP
  unfold sfReductionRepresentativeComparison
  exact IsIso.comp_isIso'
    (@Functor.map_isIso _ _ _ _ _ _ _ _ hε)
    (NatIso.hom_app_isIso _ _)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem sfDerived_natTrans_ext
    {F G : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E X)}
    (a b : F ⟶ G)
    (h : ∀ (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := AlgebraicGeometry.Scheme.ProEt.topology X)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P →
      a.app (DerivedCategory.Q.obj P) = b.app (DerivedCategory.Q.obj P)) : a = b := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  obtain ⟨T, q, hT, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P
  have : QuasiIso q := hq
  apply (cancel_epi (F.map (DerivedCategory.Q.map q))).1
  rw [a.naturality, b.naturality,
    h T hT]

attribute [local irreducible] sfComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived transition is uniquely determined by termwise quotient maps on K-flat
representatives. Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tag 06YY
(blueprint: def-weil-integral-reduction-tower).
Proof: compute both derived reductions on a K-flat resolution. The ordinary transition
commutes with differentials and homotopies. A comparison of K-flat resolutions is a
quasi-isomorphism preserved by both reductions, so conjugation by the derived counits
is independent of the resolution and natural in roofs. These conjugates give the
transformation. Every derived object has a K-flat representative, where the counits
are invertible; the displayed equation therefore proves uniqueness. -/
theorem sfDerivedReductionTransition_existsUnique (n : ℕ) :
    ∃! τ : sfDerivedReductionRestricted l E X (n + 1) ⟶
        sfDerivedReductionRestricted l E X n,
      ∀ (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ),
        CochainComplex.IsAcyclicTensorKFlat
          (J := AlgebraicGeometry.Scheme.ProEt.topology X)
          (R := completedIntegralCommRingSheafUnrestricted l E X) P →
        τ.app (DerivedCategory.Q.obj P) ≫ sfReductionRepresentativeComparison l E X n P =
          sfReductionRepresentativeComparison l E X (n + 1) P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app P) := by
  have := sfComparison_universal l E X n
  let t := Functor.whiskerRight
    (NatTrans.mapHomotopyCategory (sfReductionTransition l E X n) (.up ℤ))
      (DerivedCategory.Qh (C := scalarReductionSource.{u, u} l E X))
  let τ := Functor.leftDerivedNatTrans
    (sfDerivedReductionRestricted l E X (n + 1)) (sfDerivedReductionRestricted l E X n)
    (sfComparison l E X (n + 1)) (sfComparison l E X n)
    (HomotopyCategory.quasiIso _ (.up ℤ)) t
  have hτ : ∀ P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ,
      τ.app (DerivedCategory.Q.obj P) ≫ sfReductionRepresentativeComparison l E X n P =
        sfReductionRepresentativeComparison l E X (n + 1) P ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app P) := by
    intro P
    have h := Functor.leftDerivedNatTrans_app
        (sfDerivedReductionRestricted l E X (n + 1)) (sfDerivedReductionRestricted l E X n)
        (sfComparison l E X (n + 1)) (sfComparison l E X n)
        (HomotopyCategory.quasiIso _ (.up ℤ)) t
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    rw [sfComparison_app, sfComparison_app] at h
    exact h
  refine ⟨τ, fun P _ ↦ hτ P, ?_⟩
  intro τ' hτ'
  apply sfDerived_natTrans_ext l E X
  intro P hP
  have := sfComparison_isIso l E X n P hP
  apply (cancel_mono (sfReductionRepresentativeComparison l E X n P)).1
  exact (hτ' P ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)).trans
    (hτ P).symm

/-- The canonical derived quotient transition, with its representative normalization.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfDerivedReductionTransition (n : ℕ) :
    sfDerivedReductionRestricted l E X (n + 1) ⟶ sfDerivedReductionRestricted l E X n :=
  (sfDerivedReductionTransition_existsUnique l E X n).exists.choose

attribute [local irreducible] sfDerivedReductionTransition

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sfOrdinaryUnit_step (n : ℕ) :
    (scalarReductionExtension_adjunction.{u, u} l E X (n + 1)).choose.unit ≫
        sfReductionTransition l E X n =
      (scalarReductionExtension_adjunction.{u, u} l E X n).choose.unit := by
  have hu (k : ℕ) (M : scalarReductionSource.{u, u} l E X)
      (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
      (((scalarReductionExtension_adjunction.{u, u} l E X k).choose.unit.app M).val.app U) x =
        sfReductionTensor l E X k M U 1 x := by
    exact (scalarReductionExtension_adjunction.{u, u} l E X k).choose_spec M U x
  ext M U x
  change ((sfReductionTransition l E X n).app M).val.app U
      (((scalarReductionExtension_adjunction.{u, u} l E X (n + 1)).choose.unit.app M).val.app U x) =
    _
  have ht : ((sfReductionTransition l E X n).app M).val.app U
      (sfReductionTensor l E X (n + 1) M U 1 x) =
        sfReductionTensor l E X n M U 1 x := by
    simpa only [sfReductionTransition, map_one] using
      (sfReductionTransition_existsUnique l E X n).exists.choose_spec M U 1 x
  exact (congrArg (((sfReductionTransition l E X n).app M).val.app U)
    (hu (n + 1) M U x)).trans (ht.trans (hu n M U x).symm)

attribute [local irreducible] sfReductionRepresentativeComparison sfDerivedReductionUnit
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sfDerivedUnit_step (n : ℕ) :
    sfDerivedReductionUnit l E X (n + 1) ≫ sfDerivedReductionTransition l E X n =
      sfDerivedReductionUnit l E X n := by
  apply sfDerived_natTrans_ext l E X
  intro P hP
  have := sfComparison_isIso l E X n P hP
  have ht := (sfDerivedReductionTransition_existsUnique l E X n).exists.choose_spec P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)
  have ht' : (sfDerivedReductionTransition l E X n).app (DerivedCategory.Q.obj P) ≫
      sfReductionRepresentativeComparison l E X n P =
      sfReductionRepresentativeComparison l E X (n + 1) P ≫
        (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E X)).map
        ((NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app P) := by
    simpa only [sfDerivedReductionTransition] using ht
  apply unitCompatibilityOfComparisons
    ((sfDerivedReductionUnit l E X (n + 1)).app (DerivedCategory.Q.obj P))
    ((sfDerivedReductionUnit l E X n).app (DerivedCategory.Q.obj P))
    ((sfDerivedReductionTransition l E X n).app (DerivedCategory.Q.obj P))
    (sfReductionRepresentativeComparison l E X (n + 1) P)
    (sfReductionRepresentativeComparison l E X n P) _ _ _ ht'
    (sfUnitComparison l E X (n + 1) P hP) (sfUnitComparison l E X n P hP)
  apply mappedCompositeEq
  apply HomologicalComplex.Hom.ext
  funext i
  exact NatTrans.congr_app (sfOrdinaryUnit_step l E X n) (P.X i)

/-- The canonical derived reduction tower at all positive coefficient levels.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfIntegralReductionTower
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    ℕᵒᵖ ⥤ DerivedCategory (scalarReductionSource.{u, u} l E X) :=
  Functor.ofOpSequence (X := fun n ↦ (sfDerivedReductionRestricted l E X n).obj K)
    (fun n ↦ (sfDerivedReductionTransition l E X n).app K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The reduction units form a cone over the actual derived quotient transitions.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower).
Proof: on a K-flat representative, the tensor/restriction adjunction unit is the
sheafified map x ↦ 1 tensor x. The quotient transition sends 1 tensor x to
1 tensor x. Thus adjacent transitions commute with the units on representatives,
and hence after localization. Every arrow in the opposite natural-number category
is a composite of consecutive arrows, so induction gives the displayed equation. -/
theorem sfIntegralReductionUnit_naturality
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (i j : ℕᵒᵖ) (g : i ⟶ j) :
    ((Functor.const ℕᵒᵖ).obj K).map g ≫
        (sfDerivedReductionUnit l E X j.unop).app K =
      (sfDerivedReductionUnit l E X i.unop).app K ≫
        (sfIntegralReductionTower l E X K).map g := by
  let α : (Functor.const ℕᵒᵖ).obj K ⟶ sfIntegralReductionTower l E X K :=
    NatTrans.ofOpSequence (fun n ↦ (sfDerivedReductionUnit l E X n).app K) (by
      intro n
      simpa only [sfIntegralReductionTower, Functor.const_obj_map,
        Functor.ofOpSequence_map_homOfLE_succ, Functor.const_obj_obj,
        Category.id_comp, NatTrans.comp_app] using
        (NatTrans.congr_app (sfDerivedUnit_step l E X n) K).symm)
  exact α.naturality g

/-- The reduction tower together with its canonical compatible maps from K.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfIntegralReductionCone
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    Cone (sfIntegralReductionTower l E X K) where
  pt := K
  π :=
    { app := fun n ↦ (sfDerivedReductionUnit l E X n.unop).app K
      naturality := sfIntegralReductionUnit_naturality l E X K }

end WeilConjectures
