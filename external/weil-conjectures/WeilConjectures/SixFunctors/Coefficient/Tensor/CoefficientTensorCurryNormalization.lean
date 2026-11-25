/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientCochainTensorCurry
import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! # Derived normalization of componentwise tensor currying

Source: Stacks Project, Tags 0A90, 0A95 and 08J7.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

open SheafOfModules

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)

/-- The augmentation into the K-injective replacement used by the recorded Hom.
Source: Stacks 0A95 (blueprint: lem-sf-coefficient-tensor-curry-normalization). -/
noncomputable def coefficientHomAugmentation :
    𝟭 (CochainComplex Mod ℤ) ⟶ coefficientHomResolution.{u, c, v} J R :=
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  CochainComplex.toKInjectiveResolution.{max c v u} _

variable [HasDerivedCategory.{w} Mod]

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

omit [HasDerivedCategory.{w} Mod] in
private theorem coefficient_total_ext (P Q I : CochainComplex Mod ℤ)
    (f g : (coefficientTotalTensor.{u, c, v} J R).obj (P, Q) ⟶ I)
    (h : ∀ (a b : ℤ) (U : Cᵒᵖ) (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U),
      (f.f (a + b)).val.app U
          (coefficientTensorGenerator.{u, c, v} J R P Q a b (a + b) rfl U x y) =
        (g.f (a + b)).val.app U
          (coefficientTensorGenerator.{u, c, v} J R P Q a b (a + b) rfl U x y)) :
    f = g := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  change a + b = k at hab
  subst k
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := R) (P.X a) (Q.X b)).inv).1
  apply ((PresheafOfModules.sheafificationAdjunction.{max c v u}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)).homEquiv
        ((P.X a).val ⊗ (Q.X b).val) (I.X (a + b))).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h a b U

private theorem augmentation_inverse (I : CochainComplex Mod ℤ) :
    DerivedCategory.Q.map ((coefficientHomAugmentation.{u, c, v} J R).app I) ≫
      coefficientHomResolutionInverse.{u, c, v, w} J R I = 𝟙 (DerivedCategory.Q.obj I) := by
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
    J R).1
  have : QuasiIso ((coefficientHomAugmentation.{u, c, v} J R).app I) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ I).2
  have : IsIso (DerivedCategory.Q.map
      ((coefficientHomAugmentation.{u, c, v} J R).app I)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact IsIso.hom_inv_id (DerivedCategory.Q.map
    ((coefficientHomAugmentation.{u, c, v} J R).app I))

attribute [local irreducible] coefficientHomResolution coefficientHomResolutionIso
  coefficientHomResolutionInverse coefficientHomAugmentation

omit [HasDerivedCategory.{w} Mod] [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private theorem nativeHomObjMap (L M M' : CochainComplex Mod ℤ)
    (g : M ⟶ M') (n p q : ℤ) (hpq : p + n = q) :
    (((homComplexFunctor (R := R)).obj (op L)).map g).f n ≫
        coefficientHomComponent.{u, c, v} J R L M' n p q hpq =
      coefficientHomComponent.{u, c, v} J R L M n p q hpq ≫
        SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (g.f q) := by
  unfold coefficientHomComponent
  exact homComplexFunctor_obj_map_f_π g n p q hpq

attribute [local irreducible] homComplexFunctor coefficientHomComponent

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The representative uncurrying normalization also applies before replacing its target.
Source: Stacks Project, Tags 0A90, 0A95 and 08J7
(blueprint: lem-sf-coefficient-tensor-curry-normalization).

Proof: write eta for the fixed K-injective augmentation I to I(I). Postcompose
f with eta and c with Hom(Q,eta). Functoriality of the Hom projections shows that
their evaluation formula remains the same after applying eta. Apply
CoefficientTensorModels.uncurry_model to this map into Hom(Q,I(I)), obtaining
psi. Its section formula equals that of f followed by eta. To identify the two
chain maps, test on each total tensor summand, use the sheafification adjunction,
and then test the presheaf tensor map on pure tensors. Thus psi = f composed
with eta. Substitute this into the derived normalization from uncurry_model.
The image of eta under Q is invertible, and coefficientHomResolutionInverse is
its inverse, so Q(eta) cancels. Precompose with the inverse representative tensor
comparison. This is the asserted equality. The proof uses no injectivity of I,
no boundedness and no termwise flatness beyond the two stated K-flat hypotheses. -/
theorem coefficientTensorCurry_normalize
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (P Q I : CochainComplex Mod ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (f : (coefficientTotalTensor.{u, c, v} J R).obj (P, Q) ⟶ I)
    (g : P ⟶ homComplex (R := R) Q I)
    (hg : IsCoefficientTensorCurry.{u, c, v} J R P Q I f g) :
    (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj I)).symm
      (DerivedCategory.Q.map
          (g ≫ ((homComplexFunctor (R := R)).obj (op Q)).map
            ((coefficientHomAugmentation.{u, c, v} J R).app I)) ≫
        (coefficientHomResolutionIso.{u, c, v, w} J R Q I).inv) =
      (CoefficientTensorModels.iso.{u, c, v, w} J R S T P Q hP hQ).inv ≫
        DerivedCategory.Q.map f := by
  let eta := (coefficientHomAugmentation.{u, c, v} J R).app I
  let phi := g ≫ ((homComplexFunctor (R := R)).obj (op Q)).map eta
  obtain ⟨psi, hpsi, hn⟩ := T.uncurry_model ⟨P, hP⟩ ⟨Q, hQ⟩ I phi
  have heq : psi = f ≫ eta := by
    apply coefficient_total_ext.{u, c, v} J R P Q _ psi (f ≫ eta)
    intro a b U x y
    rw [hpsi a b (a + b) rfl (add_comm b a) U x y]
    have hp :
        (((homComplexFunctor (R := R)).obj (op Q)).map eta).f a ≫
            coefficientHomComponent.{u, c, v} J R Q _ a b (a + b) (add_comm b a) =
          coefficientHomComponent.{u, c, v} J R Q I a b (a + b) (add_comm b a) ≫
            SheafOfModules.homObjMap (R := R) (𝟙 (Q.X b)) (eta.f (a + b)) := by
      exact nativeHomObjMap.{u, c, v} J R Q I _ eta a b (a + b) (add_comm b a)
    have he := congrArg
      (fun k : P.X a ⟶ SheafOfModules.homObj (R := R) (Q.X b)
          (((coefficientHomResolution.{u, c, v} J R).obj I).X (a + b)) ↦
        ((k.val.app U x).app (op (Over.mk (𝟙 U.unop)))) y)
      (congrArg (fun k ↦ g.f a ≫ k) hp)
    change coefficientHomSectionEvaluation.{u, c, v} J R P Q I phi
        a b (a + b) (add_comm b a) U x y =
      (eta.f (a + b)).val.app U
        (((coefficientHomComponent.{u, c, v} J R Q I a b (a + b)
          (add_comm b a)).val.app U ((g.f a).val.app U x)).app
            (op (Over.mk (𝟙 U.unop))) y) at he
    rw [he]
    simpa only [coefficientHomSectionApply, HomologicalComplex.comp_f,
      SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] using
      congrArg ((eta.f (a + b)).val.app U) (hg a b U x y).symm
  rw [heq] at hn
  have hi : DerivedCategory.Q.map eta ≫
      coefficientHomResolutionInverse.{u, c, v, w} J R I = 𝟙 (DerivedCategory.Q.obj I) :=
    augmentation_inverse.{u, c, v, w} J R I
  have hn' :
      (CoefficientTensorModels.iso.{u, c, v, w} J R S T P Q hP hQ).hom ≫
        (S.transpose _ _ _).symm
          (DerivedCategory.Q.map phi ≫
            (coefficientHomResolutionIso.{u, c, v, w} J R Q I).inv) =
        DerivedCategory.Q.map f := by
    change T.comparison.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
      (S.transpose _ _ _).symm
        (DerivedCategory.Q.map phi ≫
          (coefficientHomResolutionIso.{u, c, v, w} J R Q I).inv) =
        DerivedCategory.Q.map f
    simp only [phi, Functor.map_comp,
      coefficientKFlatInclusion, ObjectProperty.ι, inducedFunctor_obj,
      Functor.comp_obj, Functor.prod_obj,
      Category.assoc, hi, Category.comp_id] at hn
    with_unfolding_all exact hn
  exact (Iso.eq_inv_comp _).2 hn'

end WeilConjectures
