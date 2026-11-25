/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import all WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all WeilConjectures.SixFunctors.Etale.Derived.Hom
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.Algebra.Category.Grp.Abelian
import all WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexProjections
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import all Mathlib.Algebra.Category.Grp.EpiMono
import all WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import all Mathlib.Algebra.Homology.QuasiIso
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.Algebra.Homology.Functor
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses
import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorDifferential

/-! # Currying chain maps by the signed sheaf tensor and Hom complex

Source: Stacks Project, Tags 03EO, 0A8X and 0A90.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local irreducible] homComplexFunctor coefficientHomComponent
  coefficientTotalTensor coefficientTensorGenerator

section

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
/-- Evaluate a local internal-Hom section on the identity object of its slice.
Source: Stacks 03EO (blueprint: lem-sf-coefficient-cochain-tensor-curry). -/
noncomputable def coefficientHomSectionApply (L M : Mod) (U : Cᵒᵖ)
    (φ : (SheafOfModules.homObj (R := R) L M).val.obj U) (y : L.val.obj U) :
    M.val.obj U :=
  (φ.app (op (Over.mk (𝟙 U.unop)))) y

/-- Literal evaluation of the curried chain map, before sheafification of each
summand. Source: Stacks 03EO, 0A90
(blueprint: lem-sf-coefficient-cochain-tensor-curry). -/
def IsCoefficientTensorCurry (P Q I : CochainComplex Mod ℤ)
    (f : (coefficientTotalTensor.{u, c, v} J R).obj (P, Q) ⟶ I)
    (g : P ⟶ homComplex (R := R) Q I) : Prop :=
  ∀ (a b : ℤ) (U : Cᵒᵖ) (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U),
    (f.f (a + b)).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P Q a b (a + b) rfl U x y) =
      coefficientHomSectionApply.{u, c, v} J R (Q.X b) (I.X (a + b)) U
        ((coefficientHomComponent.{u, c, v} J R Q I a b (a + b)
          (add_comm b a)).val.app U ((g.f a).val.app U x)) y

end

attribute [local irreducible] coefficientHomSectionApply

private theorem pullback_closed {A : Type*} [Category* A] [Preadditive A]
    {P Q : CochainComplex A ℤ} (e : P ≅ Q) {N : A} (t : N ⟶ Q.X 0)
    (ht : t ≫ Q.d 0 1 = 0) : (t ≫ e.inv.f 0) ≫ P.d 0 1 = 0 := by
  rw [Category.assoc, e.inv.comm 0 1, ← Category.assoc, ht, zero_comp]

private theorem iso_cancel {A : Type*} [Category* A] [HasZeroMorphisms A]
    {P Q : CochainComplex A ℤ} (e : P ≅ Q) {N : A} (t : N ⟶ Q.X 0) :
    (t ≫ e.inv.f 0) ≫ e.hom.f 0 = t := by
  rw [Category.assoc, ← HomologicalComplex.comp_f, e.inv_hom_id,
    HomologicalComplex.id_f, Category.comp_id]

section SiteSized

attribute [local semireducible] coefficientTotalTensor coefficientTensorGenerator

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] rhomNormalizedHomFactorEquiv rhomNormalizedHomGlobalCochainsOfFan
  rhomNormalizedHomGlobalCochains
  homTensorDegreewiseMap

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{u + 1}
  ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private noncomputable def unitSection (N : Mod)
    (z : SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶ N) (U : Cᵒᵖ) :
    N.val.obj U :=
  z.val.app U (1 : R.obj.obj U)

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem unitSection_comp (M N : Mod)
    (z : SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶ M)
    (f : M ⟶ N) (U : Cᵒᵖ) :
    unitSection J R N (z ≫ f) U = f.val.app U (unitSection J R M z U) := rfl

attribute [local irreducible] unitSection

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem projection_native (A B : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    homTensorCurryProjection R A B n p q h =
      coefficientHomComponent.{0, u + 1, u} J R A B n p q h := by
  unfold homTensorCurryProjection coefficientHomComponent homComplexπ homComplex
  with_unfolding_all rfl

attribute [local irreducible] homTensorCurryProjection

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem factor_eval (A B : Mod)
    (s : SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
        SheafOfModules.homObj (R := R) A B)
    (U : Cᵒᵖ) (x : A.val.obj U) :
    (rhomNormalizedHomFactorEquiv.{u + 1, u, 0} A B s).val.app U x =
      coefficientHomSectionApply.{0, u + 1, u} J R A B U
        (unitSection J R (SheafOfModules.homObj (R := R) A B) s U) x := by
  unfold rhomNormalizedHomFactorEquiv coefficientHomSectionApply unitSection
  rfl

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem component_cached (A B : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    coefficientHomComponent.{0, u + 1, u} J R A B n p q h =
      homComplexπ (R := R) A B n p q h := by
  unfold coefficientHomComponent
  rfl

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem normalizedProjection_cached (A B : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    rhomNormalizedHomProjection.{u + 1, u, 0} (R := R) A B n p q h =
      coefficientHomComponent.{0, u + 1, u} J R A B n p q h := by
  unfold coefficientHomComponent rhomNormalizedHomProjection homComplexπ
  with_unfolding_all exact Eq.refl (homComplexπ (R := R) A B n p q h)

private noncomputable def globalCochainEquiv (A B : CochainComplex Mod ℤ) (n : ℤ) :
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
        (homComplex (R := R) A B).X n) ≃+ CochainComplex.HomComplex.Cochain A B n :=
  rhomNormalizedHomGlobalCochains.{u + 1, u, 0} R A B n

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem globalCochainEquiv_v_apply
    (A B : CochainComplex Mod ℤ) (n : ℤ)
    (z : SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      (homComplex (R := R) A B).X n)
    (a b : ℤ) (hab : a + n = b) (U : Cᵒᵖ) (x : (A.X a).val.obj U) :
    (((globalCochainEquiv J R A B n z).v a b hab).val.app U) x =
      coefficientHomSectionApply.{0, u + 1, u} J R (A.X a) (B.X b) U
        ((coefficientHomComponent.{0, u + 1, u} J R A B n a b hab).val.app U
          (unitSection J R ((homComplex (R := R) A B).X n) z U)) x := by
  dsimp only [globalCochainEquiv]
  rw [rhomNormalizedHomGlobalCochains_v]
  rw [factor_eval J R (A.X a) (B.X b)
    (z ≫ rhomNormalizedHomProjection.{u + 1, u, 0} A B n a b hab) U x]
  rw [unitSection_comp]
  erw [normalizedProjection_cached]

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem globalCochainEquiv_d
    (A B : CochainComplex Mod ℤ) (i j : ℤ) (_hij : i + 1 = j)
    (z : SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      (homComplex (R := R) A B).X i) :
    globalCochainEquiv J R A B j (z ≫ (homComplex (R := R) A B).d i j) =
      CochainComplex.HomComplex.δ i j (globalCochainEquiv J R A B i z) := by
  exact rhomNormalizedHomGlobalCochains_comm.{u + 1, u, 0} R A B i j z

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private noncomputable def chainTensorHomIso (P Q I : CochainComplex Mod ℤ) :
    homComplex (R := R) P (homComplex (R := R) Q I) ≅
      homComplex (R := R) ((coefficientTotalTensor.{0, u + 1, u} J R).obj (P, Q)) I := by
  unfold coefficientTotalTensor
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ @CategoryTheory.asIso _ _ _ _
      (homTensorDegreewiseMap.{u + 1, u} R P Q I n)
      (homTensorDegreewiseMap_spec.{u + 1, u} R P Q I n).2)
    (fun n m _ ↦ homTensorDegreewiseMap_comm R P Q I n m)

attribute [local irreducible] chainTensorHomIso globalCochainEquiv

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem sheafHom_ext (A B N : Mod)
    (f g : A ⟶ SheafOfModules.homObj (R := R) B N)
    (h : ∀ (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U),
      coefficientHomSectionApply.{0, u + 1, u} J R B N U (f.val.app U x) y =
        coefficientHomSectionApply.{0, u + 1, u} J R B N U (g.val.app U x) y) : f = g := by
  apply SheafOfModules.hom_ext
  apply (IsoTensorHom.homObjEquiv.{u + 1, u, 0} B.val A.val N.val).symm.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro y x
  with_unfolding_all exact h U x y

/-- Currying on complexes, with literal componentwise evaluation.
Source: Stacks Project, Modules on Sites, Tag 03EO, and Cohomology on Sites,
Tags 0A8X and 0A90
(blueprint: lem-sf-coefficient-cochain-tensor-curry).

Proof: the normalized degreewise tensor-Hom maps are isomorphisms and commute
with the signed differentials. They assemble into a chain isomorphism from
Hom(P,Hom(Q,I)) to Hom(Tot(P,Q),I). The product projections identify global
sections of each Hom-complex term with ordinary cochains, and this identification
commutes with differentials. Regard f as a closed degree-zero cochain. Transfer
it to a global section, pull that section back through the chain isomorphism,
and transfer back to a closed degree-zero cochain. Its associated chain map is g.
The component formula for the global-section identification and the normalized
degreewise tensor-Hom equation give exactly the displayed evaluation formula;
transport along a+0=a aligns the dependent component indices. For uniqueness,
identity evaluations determine a local Hom section: apply the presheaf tensor-Hom
adjunction and test pure tensors. Thus all product projections of the two maps
agree, and product extensionality gives equality. The construction works for
unbounded complexes and zero summands without a boundedness or generation assumption. -/
theorem coefficientCochainTensorCurry_exists
    (P Q I : CochainComplex Mod ℤ)
    (f : (coefficientTotalTensor.{0, u + 1, u} J R).obj (P, Q) ⟶ I) :
    ∃! g : P ⟶ homComplex (R := R) Q I, IsCoefficientTensorCurry.{0, u + 1, u} J R P Q I f g := by
  let T := (coefficientTotalTensor.{0, u + 1, u} J R).obj (P, Q)
  let e := chainTensorHomIso J R P Q I
  let t := (globalCochainEquiv J R T I 0).symm
    (CochainComplex.HomComplex.Cochain.ofHom f)
  have ht : t ≫ (homComplex (R := R) T I).d 0 1 = 0 := by
    apply (globalCochainEquiv J R T I 1).injective
    rw [globalCochainEquiv_d J R T I 0 1 (by omega)]
    simp [t]
  let z := t ≫ e.inv.f 0
  have hz : z ≫ (homComplex (R := R) P (homComplex (R := R) Q I)).d 0 1 = 0 :=
    pullback_closed e t ht
  let c := CochainComplex.HomComplex.Cocycle.mk
    (globalCochainEquiv J R P (homComplex (R := R) Q I) 0 z) 1 (by omega) (by
      rw [← globalCochainEquiv_d J R P (homComplex (R := R) Q I) 0 1 (by omega), hz,
        map_zero])
  let g := CochainComplex.HomComplex.Cocycle.homOf c
  have hg : IsCoefficientTensorCurry.{0, u + 1, u} J R P Q I f g := by
    intro a b U x y
    have he : z ≫ e.hom.f 0 = t := iso_cancel e t
    have hf := congrArg
      (fun k : CochainComplex.HomComplex.Cochain T I 0 ↦
        ((k.v (a + b) (a + b) (add_zero _)).val.app U)
          (coefficientTensorGenerator.{0, u + 1, u} J R P Q a b (a + b) rfl U x y))
      ((globalCochainEquiv J R T I 0).apply_symm_apply
        (CochainComplex.HomComplex.Cochain.ofHom f))
    have hf' := globalCochainEquiv_v_apply J R T I 0 t
      (a + b) (a + b) (add_zero _) U
      (coefficientTensorGenerator.{0, u + 1, u} J R P Q a b (a + b) rfl U x y)
    have hf := hf'.symm.trans hf
    have heU := congrArg
      (fun k ↦ unitSection J R ((homComplex (R := R) T I).X 0) k U) he
    simp only [unitSection_comp] at heU
    rw [← heU] at hf
    change _ = _ at hf
    dsimp only [e] at hf
    have hgU : (g.f a).val.app U x =
        coefficientHomSectionApply.{0, u + 1, u} J R (P.X a)
          ((homComplex (R := R) Q I).X a) U
          ((coefficientHomComponent.{0, u + 1, u} J R P
            (homComplex (R := R) Q I) 0 a a (add_zero a)).val.app U
            (unitSection J R ((homComplex (R := R) P (homComplex (R := R) Q I)).X 0) z U)) x :=
      globalCochainEquiv_v_apply J R P (homComplex (R := R) Q I) 0 z a a (add_zero a) U x
    have hs := (homTensorDegreewiseMap_spec R P Q I 0).1
      a b U (unitSection J R ((homComplex (R := R) P
        (homComplex (R := R) Q I)).X 0) z U) (op (Over.mk (𝟙 U.unop))) x y
    dsimp only at hs
    simp only [projection_native] at hs
    with_unfolding_all
      change (coefficientHomSectionApply.{0, u + 1, u} J R (T.X (a + b))
        (I.X (a + b + 0)) U
        ((coefficientHomComponent.{0, u + 1, u} J R T I 0 (a + b) (a + b + 0)
          rfl).val.app U
          (((chainTensorHomIso J R P Q I).hom.f 0).val.app U
            (unitSection J R ((homComplex (R := R) P (homComplex (R := R) Q I)).X 0) z U)))
        (coefficientTensorGenerator.{0, u + 1, u} J R P Q a b (a + b) rfl U x y) =
      coefficientHomSectionApply.{0, u + 1, u} J R (Q.X b) (I.X (a + b + 0)) U
        ((coefficientHomComponent.{0, u + 1, u} J R Q I (a + 0) b (a + b + 0)
          (by omega)).val.app U
          (coefficientHomSectionApply.{0, u + 1, u} J R (P.X a)
            ((homComplex (R := R) Q I).X (a + 0)) U
            ((coefficientHomComponent.{0, u + 1, u} J R P
              (homComplex (R := R) Q I) 0 a (a + 0) rfl).val.app U
              (unitSection J R ((homComplex (R := R) P
                (homComplex (R := R) Q I)).X 0) z U)) x)) y) at hs
    have hs' : ∀ (i k : ℤ) (hi : a + 0 = i) (hk : a + b + 0 = k),
      (coefficientHomSectionApply.{0, u + 1, u} J R (T.X (a + b))
        (I.X k) U
        ((coefficientHomComponent.{0, u + 1, u} J R T I 0 (a + b) k
          hk).val.app U
          (((chainTensorHomIso J R P Q I).hom.f 0).val.app U
            (unitSection J R ((homComplex (R := R) P (homComplex (R := R) Q I)).X 0) z U)))
        (coefficientTensorGenerator.{0, u + 1, u} J R P Q a b (a + b) rfl U x y) =
      coefficientHomSectionApply.{0, u + 1, u} J R (Q.X b) (I.X k) U
        ((coefficientHomComponent.{0, u + 1, u} J R Q I i b k
          (by omega)).val.app U
          (coefficientHomSectionApply.{0, u + 1, u} J R (P.X a)
            ((homComplex (R := R) Q I).X i) U
            ((coefficientHomComponent.{0, u + 1, u} J R P
              (homComplex (R := R) Q I) 0 a i hi).val.app U
              (unitSection J R ((homComplex (R := R) P
                (homComplex (R := R) Q I)).X 0) z U)) x)) y) := by
      intro i k hi hk
      subst i
      subst k
      exact hs
    have hs' := hs' a (a + b) (add_zero a) (add_zero (a + b))
    rw [← hgU] at hs'
    exact hf.symm.trans hs'
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  apply HomologicalComplex.hom_ext
  intro a
  apply homComplex_hom_ext
  intro b k hbk
  erw [← component_cached J R Q I a b k hbk]
  have hk : k = a + b := by omega
  cases hk
  apply sheafHom_ext J R (P.X a) (Q.X b) (I.X (a + b))
  intro U x y
  exact (hg' a b U x y).symm.trans (hg a b U x y)

end SiteSized

end WeilConjectures
