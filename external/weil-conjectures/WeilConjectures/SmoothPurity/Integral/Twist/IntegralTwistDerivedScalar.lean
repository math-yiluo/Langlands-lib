/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists

import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
import all WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineRestrictions
import all WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineChainEvaluations
import all WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineNormalizedEvaluations
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic

/-!
# Integral twisting and completed derived scalar extension

Source: blueprint `sec-smooth-purity/sk-prop-sf-existence/prop-weil-twist-preserves.md`,
proof, final integral/common-stage sentence
(blueprint: lem-weil-integral-twist-derived-scalar).

The ordinary and completed comparisons below use the published functors. The equality
with their K-flat counits specifies descent of the displayed chain map. The equation
with the published completion map specifies its conjugation. Membership of the two
endpoints makes the natural isomorphism an isomorphism in the full integral categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

private theorem conjugate_cancel {C : Type*} [Category C] {X Y Z W : C}
    (f : X ⟶ Y) (b : Z ≅ Y) (c : W ≅ Z) :
    f = (f ≫ b.inv ≫ c.inv) ≫ c.hom ≫ b.hom := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (S : Scheme.{u})

section
attribute [-instance] IntegralOnSlice.abLocallyBijective IntegralOnSlice.abSheafify
open CategoryTheory.Limits
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 50000] WeilConjectures.integralTowerHasDerivedCategory

private local instance (priority := 100000) : EssentiallySmall.{u + 1} S.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private local instance (priority := 100000) :
    HasSheafify (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} S

private local instance (priority := 100000) :
    (Scheme.ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} S

attribute [local irreducible] completedScalarChangeData integralOrdinaryScalar
  completedIntegralCoefficientSheafUnrestricted

private noncomputable def ordinaryScalarIso :
    completedOrdinaryScalarExtension.{u, u} l E F ι S ≅ integralOrdinaryScalar l E F ι S :=
  (integralScalarOrdinaryModelComparison l E F ι S).choose.symm

private noncomputable def scalarCounitIso :
    DerivedCategory.Q ⋙ completedDerivedScalarExtension.{u, u} l E F ι S ≅
      completedOrdinaryScalarComplex.{u, u} l E F ι S ⋙ DerivedCategory.Q := by
  let d := integralScalarOrdinaryModelComparison l E F ι S
  let t := NatIso.mapHomologicalComplex d.choose (.up ℤ)
  let e := d.choose_spec.choose
  exact Functor.isoWhiskerLeft DerivedCategory.Q e.symm ≪≫
    (integralOrdinaryScalar l E F ι S).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight t DerivedCategory.Q

private theorem scalarCounitIso_hom_app
    (P : CochainComplex (integralTowerModules.{u, u} l E S) ℤ) :
    (scalarCounitIso l E F ι S).hom.app P =
      completedScalarCounit.{u, u} l E F ι S P := by
  let d := integralScalarOrdinaryModelComparison l E F ι S
  let e := d.choose_spec.choose
  have he := d.choose_spec.choose_spec.2.1 P
  change e.inv.app (DerivedCategory.Q.obj P) ≫
    (integralOrdinaryScalar l E F ι S).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex d.choose (.up ℤ)).hom.app P) = _
  apply (cancel_epi (e.hom.app (DerivedCategory.Q.obj P))).mp
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using he.symm

attribute [local irreducible] scalarCounitIso

private theorem scalarIso_section
    (M : integralTowerModules.{u, u} l E S) (U : S.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted.{u, u} l F S).obj.obj U)
    (x : M.val.obj U) :
    ((ordinaryScalarIso l E F ι S).hom.app M).val.app U
        (completedScalarTensorSection.{u, u} l E F ι S M U s x) =
      integralOrdinaryTensorSection l E F ι S M U s x := by
  have h := (integralScalarOrdinaryModelComparison l E F ι S).choose_spec.choose_spec.1
    M U s x
  rw [← h]
  change (((ordinaryScalarIso l E F ι S).inv.app M ≫
    (ordinaryScalarIso l E F ι S).hom.app M).val.app U _) = _
  rw [Iso.inv_hom_id_app]
  rfl

variable [∀ x : S, Invertible (l : S.residueField x)]

private noncomputable def sheafScalarComparison (m : ℤ) :
    integralSheafTwist l E S m ⋙ completedOrdinaryScalarExtension.{u, u} l E F ι S ≅
      completedOrdinaryScalarExtension.{u, u} l E F ι S ⋙ integralSheafTwist l F S m :=
  Functor.isoWhiskerLeft _ (ordinaryScalarIso l E F ι S) ≪≫
    twistSheafScalarComparison l E S F ι m ≪≫
      Functor.isoWhiskerRight (ordinaryScalarIso l E F ι S).symm _

private theorem sheafScalarComparison_spec (m : ℤ)
    (M : integralTowerModules.{u, u} l E S) (U : S.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted.{u, u} l F S).obj.obj U)
    (x : M.val.obj U) (y : (integralTwistLine l E S m).val.obj U) :
    ((sheafScalarComparison l E F ι S m).hom.app M).val.app U
        (completedScalarTensorSection.{u, u} l E F ι S _ U s
          (SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) M _ U x y)) =
      SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l F S) _ _ U
        (completedScalarTensorSection.{u, u} l E F ι S M U s x)
        ((twistScalarMaps l E S F ι m).val.app U y) := by
  let e := ordinaryScalarIso l E F ι S
  have hi : (e.inv.app M).val.app U (integralOrdinaryTensorSection l E F ι S M U s x) =
      completedScalarTensorSection.{u, u} l E F ι S M U s x := by
    rw [← scalarIso_section l E F ι S M U s x]
    exact congrArg (fun f ↦ f.val.app U
      (completedScalarTensorSection.{u, u} l E F ι S M U s x)) (e.hom_inv_id_app M)
  change ((integralSheafTwist l F S m).map (e.inv.app M)).val.app U
    (((twistSheafScalarComparison l E S F ι m).hom.app M).val.app U
      ((e.hom.app _).val.app U _)) = _
  rw [scalarIso_section]
  erw [(twistSheafScalarComparison_existsUnique l E S F ι m).exists.choose_spec M U s x y]
  calc
    _ = SheafOfModules.siteSheafTensorTmul _ _ U
        ((e.inv.app M).val.app U (integralOrdinaryTensorSection l E F ι S M U s x))
        (@id ((integralTwistLine l F S m).val.obj U)
          ((twistScalarMaps l E S F ι m).val.app U y)) :=
      SheafOfModules.scalarTensor_first_tmul
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l F S)
        (e.inv.app M) (integralTwistLine l F S m) U
        (integralOrdinaryTensorSection l E F ι S M U s x)
        (@id ((integralTwistLine l F S m).val.obj U)
          ((twistScalarMaps l E S F ι m).val.app U y))
    _ = _ := by
      rw [hi]
      rfl

private noncomputable def chainScalarComparison (m : ℤ) :
    (integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ) ⋙
        completedOrdinaryScalarComplex.{u, u} l E F ι S ≅
      completedOrdinaryScalarComplex.{u, u} l E F ι S ⋙
        (integralSheafTwist l F S m).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (sheafScalarComparison l E F ι S m) (.up ℤ)

private noncomputable def derivedScalarComparison (m : ℤ) :
    (integralSheafTwist l E S m).mapDerivedCategory ⋙
        completedDerivedScalarExtension.{u, u} l E F ι S ≅
      completedDerivedScalarExtension.{u, u} l E F ι S ⋙
        (integralSheafTwist l F S m).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (integralSheafTwist l E S m).mapDerivedCategoryFactors
        (completedDerivedScalarExtension.{u, u} l E F ι S) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ))
        (scalarCounitIso l E F ι S) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (chainScalarComparison l E F ι S m) DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (completedOrdinaryScalarComplex.{u, u} l E F ι S)
        (integralSheafTwist l F S m).mapDerivedCategoryFactors.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (scalarCounitIso l E F ι S).symm
        (integralSheafTwist l F S m).mapDerivedCategory ≪≫
      Functor.associator _ _ _)

private theorem derivedScalarComparison_spec (m : ℤ)
    (P : CochainComplex (integralTowerModules.{u, u} l E S) ℤ) :
    (completedDerivedScalarExtension.{u, u} l E F ι S).map
        ((integralSheafTwist l E S m).mapDerivedCategoryFactors.hom.app P) ≫
      completedScalarCounit.{u, u} l E F ι S
        (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((chainScalarComparison l E F ι S m).hom.app P) =
    (derivedScalarComparison l E F ι S m).hom.app (DerivedCategory.Q.obj P) ≫
      (integralSheafTwist l F S m).mapDerivedCategory.map
        (completedScalarCounit.{u, u} l E F ι S P) ≫
      (integralSheafTwist l F S m).mapDerivedCategoryFactors.hom.app
        ((completedOrdinaryScalarComplex.{u, u} l E F ι S).obj P) := by
  rw [← scalarCounitIso_hom_app l E F ι S P,
    ← scalarCounitIso_hom_app l E F ι S
      (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P)]
  let TE := integralSheafTwist l E S m
  let TF := integralSheafTwist l F S m
  let CE := TE.mapHomologicalComplex (.up ℤ)
  let CS := completedOrdinaryScalarComplex.{u, u} l E F ι S
  let D := completedDerivedScalarExtension.{u, u} l E F ι S
  let v := scalarCounitIso l E F ι S
  let a := D.map (TE.mapDerivedCategoryFactors.hom.app P) ≫
    v.hom.app (CE.obj P) ≫ DerivedCategory.Q.map
      ((chainScalarComparison l E F ι S m).hom.app P)
  let b := TF.mapDerivedCategoryFactors.app (CS.obj P)
  let c := TF.mapDerivedCategory.mapIso (v.app P)
  have h : (derivedScalarComparison l E F ι S m).hom.app (DerivedCategory.Q.obj P) =
      a ≫ b.inv ≫ c.inv := by
    simp only [derivedScalarComparison, a, b, c, TE, TF, CE, CS, D, v,
      Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Iso.app_inv, Functor.mapIso_inv, Functor.comp_obj,
      Category.id_comp, Category.comp_id, Category.assoc]
  rw [h]
  exact conjugate_cancel a b c

private theorem twist_mem (m : ℤ) (C : sfIntegralConstructibleCategory l E S) :
    sfIntegralConstructible l E S
      ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj) := by
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E S
  let L := S.purTwistIntegralModule l E
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  obtain ⟨c, _⟩ := IntegralLineReduction.chain_comparison l E S L m
  let a := IntegralLineReduction.chainCollapse l E S L m
  have hp : IntegralLineReduction.power l E S L m = integralTwistLine l E S m := by
    rw [IntegralLineReduction.power_eq_coefficient]
  let b : IntegralLineReduction.chainTensor l E S L m ≅
      (integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ) :=
    a ≪≫ NatIso.mapHomologicalComplex
      (SheafOfModules.siteSheafTensorRightIso R
        (IntegralLineReduction.power l E S L m)).symm (.up ℤ) ≪≫
      eqToIso (by rw [hp]; rfl)
  let z : IntegralLineReduction.ordinary l E S L m ≅
      (integralSheafTwist l E S m).mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _
      (c ≪≫ Functor.isoWhiskerRight b DerivedCategory.Q ≪≫
        (integralSheafTwist l E S m).mapDerivedCategoryFactors.symm)
  let := sfIntegralConstructible_isClosedUnderIsomorphisms l E S
  exact (sfIntegralConstructible l E S).prop_of_iso (z.app C.obj)
    ((IntegralLineReduction.preserves_integral l E S inferInstance L m C).1)

end

variable [∀ x : S, Invertible (l : S.residueField x)]

/-- Twisting commutes with completed integral scalar extension by the specified chain map.
Source: blueprint `definition-tate-twists--10`, final integral/common-stage sentence
(blueprint: lem-weil-integral-twist-derived-scalar).

Proof:
1. Use `integral_twist_base_change` and `pur_twist_sheaf_locally_free` to identify
   the base change of each signed line with the target line. Tensor powers reduce
   by balancing; dual bases reduce to dual bases. Thus each signed line and its
   dual are locally the coefficient ring, and all finite reductions have rank one.
2. Tensor with a line and its dual gives inverse additive equivalences by
   `SheafOfModules.tensorClosed`. They are exact, so the lines are flat and tensor
   preserves cohomology and each vanishing interval.
3. The given flat-term K-flat representative stays K-flat with flat terms after
   twisting. Associativity identifies its tensor with an acyclic complex with the
   twist of an acyclic tensor. Closedness justifies rebracketing the total sums;
   the line is in degree zero, so there is no additional differential sign.
4. The balanced map sends (x tensor y) tensor b to (x tensor b) tensor (y tensor 1).
   Its inverse sends (x tensor b) tensor (y tensor c) to (x tensor y) tensor bc.
   The bilinear universal property and sheafification extend these formulas and
   prove that the composites are identities. Compose with `twistLineScalarIso`.
   Both formulas commute with differentials, giving the chain isomorphism below.
5. Site derived-tensor descent and derived change of rings identify the two sides
   on K-flat representatives. Change of rings preserves K-flat flat-term models.
   The pure-tensor formula commutes with every chain map; localization extends
   naturality to derived arrows and makes the comparison independent of P.
6. `integralLineTensorComparison` identifies ordinary tensor by a line with the
   completed reduction tower. Its reduction maps are precisely the balanced maps
   above, so its first Roos map is the required completeness map. Thus twists of
   complete objects are complete.
7. Exact tensor with the finite rank-one reductions preserves the common support
   interval. On each constructible stratum refine the local trivializing covers;
   tensor with the finite free rank-one line preserves the finite constant model.
   Hence twists preserve `sfIntegralConstructible`, with the same uniform interval.
8. Apply `finiteFreeCompletedScalarComparison.{u, u}` to C and C(m). Conjugate the ordinary
   comparison by its specified completion maps chi. Naturality and invertibility
   follow factor by factor. `sfIntegralScalarExtension_constructible` and step 7
   put both endpoints in the full integral category, whose inclusion is fully faithful.
-/
theorem integral_twist_derived_scalar (m : ℤ) :
    ∃ (α : (sfIntegralConstructible l E S).ι ⋙
        (integralSheafTwist l E S m).mapDerivedCategory ⋙
        completedDerivedScalarExtension l E F ι S ≅
      (sfIntegralConstructible l E S).ι ⋙ completedDerivedScalarExtension l E F ι S ⋙
        (integralSheafTwist l F S m).mapDerivedCategory)
      (β : (sfIntegralConstructible l E S).ι ⋙
        (integralSheafTwist l E S m).mapDerivedCategory ⋙
        integralScalarExtensionOfUniverses l E F ι S ≅
      (sfIntegralConstructible l E S).ι ⋙ integralScalarExtensionOfUniverses l E F ι S ⋙
        (integralSheafTwist l F S m).mapDerivedCategory),
      (∀ (C : sfIntegralConstructibleCategory l E S)
        (P : (integralOperationsGoodComplex l E S).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ C.obj),
        ∃ a : (completedOrdinaryScalarComplex l E F ι S).obj
            (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj) ≅
          ((integralSheafTwist l F S m).mapHomologicalComplex (.up ℤ)).obj
            ((completedOrdinaryScalarComplex l E F ι S).obj P.obj),
          (∀ (i : ℤ) (U : S.ProEtᵒᵖ)
            (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U)
            (x : (P.obj.X i).val.obj U) (y : (integralTwistLine l E S m).val.obj U),
            (a.hom.f i).val.app U
                (completedScalarTensorSection l E F ι S _ U b
                  (SheafOfModules.siteSheafTensorTmul
                    (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x y)) =
              SheafOfModules.siteSheafTensorTmul
                (A := completedIntegralCommRingSheafUnrestricted l F S) _ _ U
                (completedScalarTensorSection l E F ι S (P.obj.X i) U b x)
                ((twistScalarMaps l E S F ι m).val.app U y)) ∧
          (completedDerivedScalarExtension l E F ι S).map
              ((integralSheafTwist l E S m).mapDerivedCategory.map e.inv) ≫
            (completedDerivedScalarExtension l E F ι S).map
              ((integralSheafTwist l E S m).mapDerivedCategoryFactors.hom.app P.obj) ≫
            completedScalarCounit l E F ι S
              (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
            DerivedCategory.Q.map a.hom =
          α.hom.app C ≫ (integralSheafTwist l F S m).mapDerivedCategory.map
              ((completedDerivedScalarExtension l E F ι S).map e.inv) ≫
            (integralSheafTwist l F S m).mapDerivedCategory.map
              (completedScalarCounit l E F ι S P.obj) ≫
            (integralSheafTwist l F S m).mapDerivedCategoryFactors.hom.app
              ((completedOrdinaryScalarComplex l E F ι S).obj P.obj)) ∧
      (∀ C : sfIntegralConstructibleCategory l E S,
        (completedScalarComparison l E F ι S).app
            ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj) ≫ β.hom.app C =
          α.hom.app C ≫ (integralSheafTwist l F S m).mapDerivedCategory.map
            ((completedScalarComparison l E F ι S).app C.obj)) ∧
      ∀ C : sfIntegralConstructibleCategory l E S,
        sfIntegralConstructible l E S
            ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj) ∧
          sfIntegralConstructible l F S
            ((integralScalarExtensionOfUniverses l E F ι S).obj
              ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj)) ∧
          sfIntegralConstructible l F S
            ((integralScalarExtensionOfUniverses l E F ι S).obj C.obj) ∧
          sfIntegralConstructible l F S
            ((integralSheafTwist l F S m).mapDerivedCategory.obj
              ((integralScalarExtensionOfUniverses l E F ι S).obj C.obj)) := by
  classical
  let : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} S
  let : (Scheme.ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} S
  let I := (sfIntegralConstructible l E S).ι
  let T := (integralSheafTwist l E S m).mapDerivedCategory
  let U := (integralSheafTwist l F S m).mapDerivedCategory
  let D := completedDerivedScalarExtension.{u, u} l E F ι S
  let B := integralScalarExtensionOfUniverses l E F ι S
  let α : I ⋙ T ⋙ D ≅ I ⋙ D ⋙ U :=
    Functor.isoWhiskerLeft I (derivedScalarComparison l E F ι S m)
  have ht (C : sfIntegralConstructibleCategory l E S) :
      sfIntegralConstructible l E S (T.obj C.obj) := twist_mem l E S m C
  have hχ (C : sfIntegralConstructibleCategory l E S) :
      IsIso ((completedScalarComparison.{u, u} l E F ι S).app C.obj) :=
    ((finiteFreeCompletedScalarComparison.{u, u} l E F ι S).2.1 C.obj
      (IntegralLineReduction.intrinsic_complete l E S C)).1
  have hχT (C : sfIntegralConstructibleCategory l E S) :
      IsIso ((completedScalarComparison.{u, u} l E F ι S).app (T.obj C.obj)) :=
    ((finiteFreeCompletedScalarComparison.{u, u} l E F ι S).2.1 (T.obj C.obj)
      (IntegralLineReduction.intrinsic_complete l E S ⟨T.obj C.obj, ht C⟩)).1
  have : ∀ C, IsIso ((Functor.whiskerLeft I
      (completedScalarComparison.{u, u} l E F ι S)).app C) := hχ
  have : IsIso (Functor.whiskerLeft I (completedScalarComparison.{u, u} l E F ι S)) :=
    NatIso.isIso_of_isIso_app _
  have : ∀ C, IsIso ((Functor.whiskerLeft I
      (Functor.whiskerLeft T (completedScalarComparison.{u, u} l E F ι S))).app C) := hχT
  have : IsIso (Functor.whiskerLeft I
      (Functor.whiskerLeft T (completedScalarComparison.{u, u} l E F ι S))) :=
    NatIso.isIso_of_isIso_app _
  let χ : I ⋙ D ≅ I ⋙ B :=
    asIso (Functor.whiskerLeft I (completedScalarComparison.{u, u} l E F ι S))
  let χT : I ⋙ T ⋙ D ≅ I ⋙ T ⋙ B :=
    asIso (Functor.whiskerLeft I
      (Functor.whiskerLeft T (completedScalarComparison.{u, u} l E F ι S)))
  let β : I ⋙ T ⋙ B ≅ I ⋙ B ⋙ U :=
    χT.symm ≪≫ α ≪≫ (Functor.associator I D U).symm ≪≫ Functor.isoWhiskerRight χ U ≪≫
      Functor.associator I B U
  refine ⟨α, β, ?_, ?_, ?_⟩
  · intro C P e
    refine ⟨(chainScalarComparison l E F ι S m).app P.obj, ?_, ?_⟩
    · intro i V b x y
      exact sheafScalarComparison_spec l E F ι S m (P.obj.X i) V b x y
    · have hn : D.map (T.map e.inv) ≫ (derivedScalarComparison l E F ι S m).hom.app
            (DerivedCategory.Q.obj P.obj) = α.hom.app C ≫ U.map (D.map e.inv) :=
        (derivedScalarComparison l E F ι S m).hom.naturality e.inv
      have hh := congrArg (fun f ↦ f ≫
        U.map (completedScalarCounit.{u, u} l E F ι S P.obj) ≫
          (integralSheafTwist l F S m).mapDerivedCategoryFactors.hom.app
            ((completedOrdinaryScalarComplex.{u, u} l E F ι S).obj P.obj)) hn
      simp only [Category.assoc] at hh
      rw [← hh]
      exact congrArg (D.map (T.map e.inv) ≫ ·) (derivedScalarComparison_spec l E F ι S m P.obj)
  · intro C
    change χT.hom.app C ≫ β.hom.app C = α.hom.app C ≫ U.map (χ.hom.app C)
    simp only [β, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.hom_inv_id_app_assoc,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  · intro C
    have scalar_mem (K : sfIntegralConstructibleCategory l E S) :
        sfIntegralConstructible l F S (B.obj K.obj) := by
      exact sfIntegralScalarExtension_constructible 0 l
        (Fact.out : l.Prime).ne_zero E F ι S K.obj K.property
    exact ⟨ht C, scalar_mem ⟨T.obj C.obj, ht C⟩, scalar_mem C,
      twist_mem l F S m ⟨B.obj C.obj, scalar_mem C⟩⟩

end WeilConjectures
