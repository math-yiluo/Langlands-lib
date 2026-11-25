/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted

/-! # Integral reduction towers without a finite-field datum

Source: Bhatt--Scholze, Definition 3.5.2; Stacks Project, Tags 03EK and 06YY
(blueprint: def-weil-integral-reduction-tower).

The completion and its projections already have unrestricted versions. This supplies
the same reduction tower without the irrelevant global finite-field datum. The completed
coefficient sheaf is shared with the finite-field interface.
Index n means exponent n+1.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules.UnrestrictedTowerProof

universe a b r
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]

private noncomputable abbrev res {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)

variable {R S T : Sheaf J CommRingCat.{r}}
  (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T) (hq : f ≫ q = g)
  (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
include hq in
private theorem coefficient_comp (U : Cᵒᵖ) (x : R.obj.obj U) :
    q.hom.app U (f.hom.app U x) = g.hom.app U x :=
  ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hq) x

private noncomputable def sectionMap (U : Cᵒᵖ) :
    (changeOfRingsPresheaf f M).obj U ⟶
      (ModuleCat.restrictScalars (q.hom.app U).hom).obj
        ((changeOfRingsPresheaf g M).obj U) := by
  letI : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (f.hom.app U).hom
  letI : Module (R.obj.obj U) (T.obj.obj U) := Module.compHom _ (g.hom.app U).hom
  let h : S.obj.obj U →ₗ[R.obj.obj U] T.obj.obj U :=
    { toFun := q.hom.app U
      map_add' := map_add _
      map_smul' := fun x s ↦ by
        change q.hom.app U (f.hom.app U x * s) = g.hom.app U x * q.hom.app U s
        rw [map_mul, coefficient_comp f g q hq] }
  exact ModuleCat.ofHom
    (X := (changeOfRingsPresheaf f M).obj U)
    (Y := (ModuleCat.restrictScalars (q.hom.app U).hom).obj
      ((changeOfRingsPresheaf g M).obj U))
    { toFun := TensorProduct.map h (LinearMap.id : M.val.obj U →ₗ[R.obj.obj U] M.val.obj U)
      map_add' := map_add _
      map_smul' := fun s z ↦ by
        induction z using TensorProduct.inductionOn with
        | tmul t x =>
          change S.obj.obj U at t
          change q.hom.app U (s * t) ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x =
            (q.hom.app U s * q.hom.app U t) ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x
          rw [map_mul]
        | add z w hz hw => simp only [smul_add, map_add, hz, hw] }

private theorem sectionMap_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    sectionMap f g q hq M U (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x) =
      (show (changeOfRingsPresheaf g M).obj U from
        q.hom.app U s ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x) := rfl

private local instance {A : Sheaf J CommRingCat.{r}}
    {N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)}
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    Module (A.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.map i).hom).obj
          (N.val.obj V)) :=
  inferInstanceAs (Module (A.obj.obj V) (N.val.obj V))

private theorem restriction_tmul {A B : Sheaf J CommRingCat.{r}} (c : A ⟶ B)
    (N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : B.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsPresheaf c N).map i (s ⊗ₜ[A.obj.obj U,(c.hom.app U).hom] x) =
      B.obj.map i s ⊗ₜ[A.obj.obj V,(c.hom.app V).hom] N.val.map i x :=
  Classical.choose_spec (exists_changeOfRingsMap c N i) s x

private noncomputable def presheafMap :
    changeOfRingsPresheaf f M ⟶
      (PresheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat RingCat)).map q).hom).obj (changeOfRingsPresheaf g M) where
  app := sectionMap f g q hq M
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change sectionMap f g q hq M V ((changeOfRingsPresheaf f M).map i
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) =
      (changeOfRingsPresheaf g M).map i
        (sectionMap f g q hq M U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x))
    rw [restriction_tmul, sectionMap_tmul, sectionMap_tmul, restriction_tmul]
    simp only [map_one]

private noncomputable def sheafMap : changeOfRings f M ⟶ (res q).obj (changeOfRings g M) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).symm
    (presheafMap f g q hq M ≫
      (PresheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat RingCat)).map q).hom).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj)).unit.app
              (changeOfRingsPresheaf g M)))

private noncomputable def tensorSection (c : R ⟶ S)
    (N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRings c N).val.obj U :=
  (toSheafify J (changeOfRingsPresheaf c N).presheaf).app U
    (s ⊗ₜ[R.obj.obj U,(c.hom.app U).hom] x)

include f g q hq M in
private theorem sheafMap_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (sheafMap f g q hq M).val.app U (tensorSection f M U s x) =
      tensorSection g M U (q.hom.app U s) x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (F := (res q).obj (changeOfRings g M))
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).apply_symm_apply
      (presheafMap f g q hq M ≫
        (PresheafOfModules.restrictScalars ((sheafCompose J
          (forget₂ CommRingCat RingCat)).map q).hom).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj)).unit.app
                (changeOfRingsPresheaf g M)))
  exact congrArg (fun k ↦ k.app U (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) h

private noncomputable def restrictedMap :
    (res f).obj (changeOfRings f M) ⟶ (res g).obj (changeOfRings g M) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((res f).obj (changeOfRings f M)).val.obj U)
        (Y := ((res g).obj (changeOfRings g M)).val.obj U)
        { toFun := (sheafMap f g q hq M).val.app U
          map_add' := map_add _
          map_smul' := fun r x ↦ by
            change (changeOfRings f M).val.obj U at x
            change (sheafMap f g q hq M).val.app U (f.hom.app U r • x) =
              g.hom.app U r • (show (changeOfRings g M).val.obj U from
                (sheafMap f g q hq M).val.app U x)
            rw [map_smul]
            change q.hom.app U (f.hom.app U r) •
              (show (changeOfRings g M).val.obj U from
                (sheafMap f g q hq M).val.app U x) = _
            rw [coefficient_comp f g q hq] }
      naturality := by
        intro U V i
        ext x
        exact PresheafOfModules.naturality_apply (sheafMap f g q hq M).val i x }

private theorem restrictedMap_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (restrictedMap f g q hq M).val.app U (tensorSection f M U s x) =
      tensorSection g M U (q.hom.app U s) x :=
  sheafMap_tmul f g q hq M U s x

private theorem restricted_hom_ext
    (N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (a b : (res f).obj (changeOfRings f M) ⟶ N)
    (h : ∀ U s x, a.val.app U (tensorSection f M U s x) =
      b.val.app U (tensorSection f M U s x)) : a = b := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ N.isSheaf
  ext U z
  induction z using TensorProduct.inductionOn with
  | tmul s x => exact h U s x
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

private theorem map_tensorSection
    {N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M ⟶ N) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRingsHom f M a).val.app U (tensorSection f M U s x) =
      tensorSection f N U s (a.val.app U x) := by
  let k : changeOfRingsPresheaf f M ⟶ changeOfRingsPresheaf f N :=
    { app := fun V ↦ (ModuleCat.extendScalars (f.hom.app V).hom).map (a.val.app V)
      naturality := changeOfRingsHom_naturality f M a }
  let z : (changeOfRingsPresheaf f M).presheaf.obj U :=
    s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x
  have hn := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map k)
  have h := congrArg (fun η ↦ (η.app U).hom z) hn
  change (toSheafify J (changeOfRingsPresheaf f N).presheaf).app U
      ((ModuleCat.extendScalars (f.hom.app U).hom).map (a.val.app U)
        (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) = _ at h
  erw [ModuleCat.ExtendScalars.map_tmul] at h
  exact h.symm

attribute [local irreducible] sectionMap presheafMap sheafMap restrictedMap

private theorem restrictedMap_naturality
    {N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M ⟶ N) :
    (res f).map (changeOfRingsHom f M a) ≫ restrictedMap f g q hq N =
      restrictedMap f g q hq M ≫ (res g).map (changeOfRingsHom g M a) := by
  apply restricted_hom_ext f M
  intro U s x
  change (restrictedMap f g q hq N).val.app U
      ((changeOfRingsHom f M a).val.app U (tensorSection f M U s x)) =
    (changeOfRingsHom g M a).val.app U
      ((restrictedMap f g q hq M).val.app U (tensorSection f M U s x))
  rw [map_tensorSection]
  rw [show (restrictedMap f g q hq M).val.app U (tensorSection f M U s x) =
      tensorSection g M U (q.hom.app U s) x from restrictedMap_tmul f g q hq M U s x]
  rw [map_tensorSection]
  exact restrictedMap_tmul f g q hq N U s (a.val.app U x)

variable
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (G : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
  (hf : ∀ N, F.obj N = changeOfRings f N)
  (hg : ∀ N, G.obj N = changeOfRings g N)

private noncomputable def identifiedMap :
    (F ⋙ res f).obj M ⟶ (G ⋙ res g).obj M :=
  (res f).map (eqToHom (hf M)) ≫ restrictedMap f g q hq M ≫
    (res g).map (eqToHom (hg M).symm)

private theorem identifiedMap_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (identifiedMap f g q hq M F G hf hg).val.app U
      ((eqToHom (hf M).symm).val.app U (tensorSection f M U s x)) =
      (eqToHom (hg M).symm).val.app U (tensorSection g M U (q.hom.app U s) x) := by
  have hc : ∀ z : (changeOfRings f M).val.obj U,
      (eqToHom (hf M)).val.app U ((eqToHom (hf M).symm).val.app U z) = z := by
    intro z
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app U) (eqToHom_trans (hf M).symm (hf M))) z
  change (eqToHom (hg M).symm).val.app U
    ((restrictedMap f g q hq M).val.app U
      ((eqToHom (hf M)).val.app U
        ((eqToHom (hf M).symm).val.app U (tensorSection f M U s x)))) = _
  rw [hc]
  exact congrArg ((eqToHom (hg M).symm).val.app U) (restrictedMap_tmul f g q hq M U s x)

private theorem identified_hom_ext
    (N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (a b : (F ⋙ res f).obj M ⟶ N)
    (h : ∀ U s x, a.val.app U
        ((eqToHom (hf M).symm).val.app U (tensorSection f M U s x)) =
      b.val.app U ((eqToHom (hf M).symm).val.app U (tensorSection f M U s x))) : a = b := by
  let e := (res f).map (eqToHom (hf M).symm)
  have he : e ≫ a = e ≫ b := restricted_hom_ext f M N (e ≫ a) (e ≫ b) h
  have hi := congrArg (fun k ↦ (res f).map (eqToHom (hf M)) ≫ k) he
  dsimp only [e] at hi
  simp only [← Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl] at hi
  simpa only [(res f).map_id, Category.id_comp] using hi

private theorem identifiedMap_naturality
    (hmf : ∀ {N N'} (a : N ⟶ N'), F.map a =
      eqToHom (hf N) ≫ changeOfRingsHom f N a ≫ eqToHom (hf N').symm)
    (hmg : ∀ {N N'} (a : N ⟶ N'), G.map a =
      eqToHom (hg N) ≫ changeOfRingsHom g N a ≫ eqToHom (hg N').symm)
    {N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M ⟶ N) :
    (F ⋙ res f).map a ≫ identifiedMap f g q hq N F G hf hg =
      identifiedMap f g q hq M F G hf hg ≫ (G ⋙ res g).map a := by
  dsimp only [Functor.comp_map, identifiedMap]
  rw [hmf, hmg]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (res f).map_comp_assoc (eqToHom (hf N).symm) (eqToHom (hf N)),
    ← (res g).map_comp_assoc (eqToHom (hg M).symm) (eqToHom (hg M))]
  simp only [eqToHom_trans, eqToHom_refl]
  rw [(res f).map_id, (res g).map_id]
  simp only [Category.id_comp]
  rw [← Category.assoc ((res f).map (changeOfRingsHom f M a)),
    restrictedMap_naturality f g q hq M a]
  simp only [Category.assoc]

attribute [local irreducible] identifiedMap

end SheafOfModules.UnrestrictedTowerProof

namespace WeilConjectures
attribute [local irreducible] scalarReductionExistence HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

set_option linter.defProp false in
private noncomputable def unrestrictedCoefficientStep (n : ℕ) :
    integralCoefficientCommRingSheaf l E Y (n + 1) ⟶ integralCoefficientCommRingSheaf l E Y n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

private theorem unrestrictedCoefficientStep_comp (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E Y (n + 1) ≫
      unrestrictedCoefficientStep l E Y n =
        completedIntegralCommRingProjectionUnrestricted l E Y n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
  change (limit.π (integralCoefficientSheafSystem l E Y) (op (n + 1))).hom.app U ≫
      (integralCoefficientSheafTransition l E Y n).hom.app U =
    (limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U
  have h := congrArg (fun k ↦ k.hom.app U)
    (limit.w (integralCoefficientSheafSystem l E Y) (homOfLE (Nat.le_succ n)).op)
  simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h

attribute [local irreducible] unrestrictedIntegralReductionExistence
  completedIntegralCoefficientSheafUnrestricted constantSheaf
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private theorem unrestrictedReduction_obj (n : ℕ) (M : integralTowerModules l E Y) :
    (unrestrictedIntegralReductionFunctor l E Y n).obj M =
      SheafOfModules.changeOfRings
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M :=
  by
    change (scalarReductionExistence l E Y n).choose.obj M = _
    exact (scalarReductionExistence l E Y n).choose_spec.choose M

private theorem unrestrictedReduction_map (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N) :
    (unrestrictedIntegralReductionFunctor l E Y n).map a =
      eqToHom (unrestrictedReduction_obj l E Y n M) ≫
        SheafOfModules.changeOfRingsHom
          (completedIntegralCommRingProjectionUnrestricted l E Y n) M a ≫
        eqToHom (unrestrictedReduction_obj l E Y n N).symm :=
  by
    change (scalarReductionExistence l E Y n).choose.map a = _
    exact (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose a

private noncomputable def unrestrictedModuleStep (n : ℕ)
    (M : integralTowerModules l E Y) :
    (SheafOfModules.UnrestrictedTowerProof.res
      (completedIntegralCommRingProjectionUnrestricted l E Y (n + 1))).obj
        ((unrestrictedIntegralReductionFunctor l E Y (n + 1)).obj M) ⟶
      (SheafOfModules.UnrestrictedTowerProof.res
        (completedIntegralCommRingProjectionUnrestricted l E Y n)).obj
          ((unrestrictedIntegralReductionFunctor l E Y n).obj M) :=
  SheafOfModules.UnrestrictedTowerProof.identifiedMap
    (completedIntegralCommRingProjectionUnrestricted l E Y (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
    (unrestrictedCoefficientStep l E Y n) (unrestrictedCoefficientStep_comp l E Y n) M
    (unrestrictedIntegralReductionFunctor l E Y (n + 1))
    (unrestrictedIntegralReductionFunctor l E Y n)
    (unrestrictedReduction_obj l E Y (n + 1))
    (unrestrictedReduction_obj l E Y n)

private theorem unrestrictedModuleStep_naturality (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N) :
    (SheafOfModules.UnrestrictedTowerProof.res
      (completedIntegralCommRingProjectionUnrestricted l E Y (n + 1))).map
        ((unrestrictedIntegralReductionFunctor l E Y (n + 1)).map a) ≫
      unrestrictedModuleStep l E Y n N =
    unrestrictedModuleStep l E Y n M ≫
      (SheafOfModules.UnrestrictedTowerProof.res
        (completedIntegralCommRingProjectionUnrestricted l E Y n)).map
          ((unrestrictedIntegralReductionFunctor l E Y n).map a) :=
  SheafOfModules.UnrestrictedTowerProof.identifiedMap_naturality
    (completedIntegralCommRingProjectionUnrestricted l E Y (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
    (unrestrictedCoefficientStep l E Y n) (unrestrictedCoefficientStep_comp l E Y n) M
    (unrestrictedIntegralReductionFunctor l E Y (n + 1))
    (unrestrictedIntegralReductionFunctor l E Y n)
    (unrestrictedReduction_obj l E Y (n + 1))
    (unrestrictedReduction_obj l E Y n)
    (unrestrictedReduction_map l E Y (n + 1))
    (unrestrictedReduction_map l E Y n) a

private theorem unrestrictedModuleStep_tmul (n : ℕ) (M : integralTowerModules l E Y)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj U) (x : M.val.obj U) :
    (unrestrictedModuleStep l E Y n M).val.app U
      (unrestrictedIntegralTensorSection l E Y (n + 1) M U s x) =
    unrestrictedIntegralTensorSection l E Y n M U
      ((integralCoefficientSheafTransition l E Y n).hom.app U s) x :=
  SheafOfModules.UnrestrictedTowerProof.identifiedMap_tmul
    (completedIntegralCommRingProjectionUnrestricted l E Y (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
    (unrestrictedCoefficientStep l E Y n) (unrestrictedCoefficientStep_comp l E Y n) M
    (unrestrictedIntegralReductionFunctor l E Y (n + 1))
    (unrestrictedIntegralReductionFunctor l E Y n)
    (unrestrictedReduction_obj l E Y (n + 1))
    (unrestrictedReduction_obj l E Y n) U s x

private theorem unrestrictedReduction_hom_ext (n : ℕ) (M N : integralTowerModules l E Y)
    (a b : (SheafOfModules.UnrestrictedTowerProof.res
      (completedIntegralCommRingProjectionUnrestricted l E Y n)).obj
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M) ⟶ N)
    (h : ∀ U s x, a.val.app U (unrestrictedIntegralTensorSection l E Y n M U s x) =
      b.val.app U (unrestrictedIntegralTensorSection l E Y n M U s x)) : a = b :=
  SheafOfModules.UnrestrictedTowerProof.identified_hom_ext
    (completedIntegralCommRingProjectionUnrestricted l E Y n) M
    (unrestrictedIntegralReductionFunctor l E Y n)
    (unrestrictedReduction_obj l E Y n) N a b h

attribute [local irreducible] unrestrictedModuleStep

/-- The strict reduction tower before localization, retaining its canonical transitions.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def unrestrictedIntegralComplexTower
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E Y) ℤ :=
  Functor.ofOpSequence
    (X := fun n ↦ (unrestrictedIntegralComplexFunctor l E Y n).obj P)
    (fun n ↦ (unrestrictedIntegralTransition l E Y n).app P)

end WeilConjectures
