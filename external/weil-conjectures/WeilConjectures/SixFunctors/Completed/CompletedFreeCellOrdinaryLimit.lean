/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralReductionTower
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.Limits

/-! # The ordinary quotient-tower limit of a finite free cell

Source: Stacks Project, Tag 099I; Bhatt--Scholze, Propositions 3.1.9--3.1.10.
(blueprint: lem-sf-completed-free-cell-ordinary-limit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u d a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local instance] scalarReductionExtensionAdditive
  scalarReductionRestrictionLimits scalarReductionRestrictionColimits
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The actual chain-level quotient units commute with the successor transitions.
Source: Stacks Tag 06YL (blueprint: lem-sf-completed-free-cell-ordinary-limit).
Proof: the transition sends 1 tensor x to 1 tensor x, because its coefficient map
preserves one; the specified tensor-generator formulas therefore give equality. -/
theorem completedFreeCellCone_compatibility
    (P : CochainComplex (completedIntegralModuleSheaves l E T D hl) ℤ) (n : ℕ) :
    𝟙 P ≫ integralTowerUnit l E T D hl P n =
      integralTowerUnit l E T D hl P (n + 1) ≫
        integralTowerTransition l E T D hl P n := by
  rw [Category.id_comp]
  have hunit : integralTowerUnitCondition l E T D hl P
      (integralTowerUnit l E T D hl P) :=
    (integralTowerMaps_existUnique l E T D hl P).exists.choose_spec.1
  have hstep : integralTowerTransitionCondition l E T D hl P
      (integralTowerTransition l E T D hl P) :=
    (integralTowerMaps_existUnique l E T D hl P).exists.choose_spec.2
  ext i U x
  change (((integralTowerUnit l E T D hl P n).f i).val.app U) x =
    (((integralTowerTransition l E T D hl P n).f i).val.app U)
      ((((integralTowerUnit l E T D hl P (n + 1)).f i).val.app U) x)
  erw [hunit n i U x, hunit (n + 1) i U x]
  simpa only [map_one] using (hstep n i U 1 x).symm

/-- The explicit cone of the specified quotient-unit chain maps.
Source: Stacks Tag 06YL (blueprint: lem-sf-completed-free-cell-ordinary-limit). -/
def completedFreeCellCone
    (P : CochainComplex (completedIntegralModuleSheaves l E T D hl) ℤ) :
    Cone (Functor.ofOpSequence (X := fun n ↦ integralTowerComplex l E T D hl n P)
      (integralTowerTransition l E T D hl P)) where
  pt := P
  π := NatTrans.ofOpSequence (integralTowerUnit l E T D hl P)
    (by
      intro n
      simpa only [Functor.const_obj_map, Functor.ofOpSequence_map_homOfLE_succ] using
        completedFreeCellCone_compatibility l E T D hl P n)

private def coefficientUnitProjection (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T) ⟶
      (scalarReductionRestriction l E T n).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E T n)) :=
  ((scalarReductionRestriction l E T n).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E T n))).unitHomEquiv.symm
      ((SheafOfModules.unit (integralCoefficientSheaf l E T n)).unitHomEquiv (𝟙 _))

private theorem coefficientUnitProjection_apply (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) :
    (coefficientUnitProjection l E T n).val.app U x =
      (limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U x := by
  have h := congrArg (fun s ↦ s.val U)
    (((scalarReductionRestriction l E T n).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E T n))).unitHomEquiv.apply_symm_apply
        ((SheafOfModules.unit (integralCoefficientSheaf l E T n)).unitHomEquiv (𝟙 _)))
  change (coefficientUnitProjection l E T n).val.app U
    (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) =
      (1 : (integralCoefficientSheaf l E T n).obj.obj U) at h
  let x₁ : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U := 1
  let y₁ : (integralCoefficientSheaf l E T n).obj.obj U :=
    (coefficientUnitProjection l E T n).val.app U x₁
  have hx := ((coefficientUnitProjection l E T n).val.app U).hom.map_smul x x₁
  change (coefficientUnitProjection l E T n).val.app U (x * x₁) =
    @id ((integralCoefficientSheaf l E T n).obj.obj U)
      ((limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U x) * y₁ at hx
  change y₁ = 1 at h
  simpa only [x₁, mul_one, h, id_eq] using hx

private theorem projection_step (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) :
    (integralCoefficientSheafTransition l E T n).hom.app U
      ((limit.π (integralCoefficientSheafSystem l E T) (op (n + 1))).hom.app U x) =
        (limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U x := by
  have h := limit.w (integralCoefficientSheafSystem l E T) (homOfLE n.le_succ).op
  simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg (fun f ↦ f.hom.app U x) h

private def coefficientStep (n : ℕ) :
    (scalarReductionRestriction l E T (n + 1)).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E T (n + 1))) ⟶
      (scalarReductionRestriction l E T n).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E T n)) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((scalarReductionRestriction l E T (n + 1)).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E T (n + 1)))).val.obj U)
        (Y := ((scalarReductionRestriction l E T n).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E T n))).val.obj U)
        { toFun := (integralCoefficientSheafTransition l E T n).hom.app U
          map_add' := map_add _
          map_smul' := by
            intro a x
            change (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U at a
            change (integralCoefficientSheaf l E T (n + 1)).obj.obj U at x
            change (integralCoefficientSheafTransition l E T n).hom.app U
              (@id ((integralCoefficientSheaf l E T (n + 1)).obj.obj U)
                ((limit.π (integralCoefficientSheafSystem l E T) (op (n + 1))).hom.app U a) * x) =
                @id ((integralCoefficientSheaf l E T n).obj.obj U)
                  ((limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U a) *
                  (integralCoefficientSheafTransition l E T n).hom.app U x
            rw [map_mul]
            congr 1
            exact projection_step l E T n U a }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom
          ((integralCoefficientSheafTransition l E T n).hom.naturality f) x }

private def coefficientDiagram : ℕᵒᵖ ⥤ scalarReductionSource l E T :=
  Functor.ofOpSequence (X := fun n ↦ (scalarReductionRestriction l E T n).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E T n))) (coefficientStep l E T)

private def coefficientCone : Cone (coefficientDiagram l E T) where
  pt := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
  π := NatTrans.ofOpSequence (coefficientUnitProjection l E T) (by
    intro n
    simp only [Functor.const_obj_map, coefficientDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (coefficientUnitProjection l E T n).val.app U x =
      (integralCoefficientSheafTransition l E T n).hom.app U
        ((coefficientUnitProjection l E T (n + 1)).val.app U x)
    rw [coefficientUnitProjection_apply, coefficientUnitProjection_apply]
    exact (projection_step l E T n U x).symm)

private theorem coefficientCone_isLimit : Nonempty (IsLimit (coefficientCone l E T)) := by
  classical
  refine ⟨?_⟩
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects
    (forget₂ (ModuleCat.{max u (t + 1)}
      ((completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)) AddCommGrpCat)
  let F := coefficientDiagram l E T ⋙ SheafOfModules.evaluation
    (completedIntegralCoefficientSheafUnrestricted l E T) U ⋙
    forget₂ _ AddCommGrpCat
  let G₀ := sheafToPresheaf (AlgebraicGeometry.Scheme.ProEt.topology T)
      RingCat.{max u (t + 1)} ⋙
    (evaluation T.ProEtᵒᵖ RingCat.{max u (t + 1)}).obj U ⋙
      forget₂ RingCat AddCommGrpCat
  let G := integralCoefficientSheafSystem l E T ⋙ G₀
  let α : F ⟶ G := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro n
    simp only [F, G, G₀, coefficientDiagram, integralCoefficientSheafSystem,
      Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
      Category.id_comp, Category.comp_id]
    ext x
    rfl)
  have (n : ℕᵒᵖ) : IsIso (α.app n) := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let c := (forget₂ (ModuleCat.{max u (t + 1)}
      ((completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)) AddCommGrpCat).mapCone
    ((PresheafOfModules.evaluation
      (completedIntegralCoefficientSheafUnrestricted l E T).obj U).mapCone
      ((SheafOfModules.forget _).mapCone (coefficientCone l E T)))
  apply (IsLimit.postcomposeHomEquiv (asIso α) c).toFun
  exact (isLimitOfPreserves G₀ (limit.isLimit (integralCoefficientSheafSystem l E T))).ofIsoLimit
    (Cone.ext (Iso.refl _) (by
      intro n
      ext x
      exact (coefficientUnitProjection_apply l E T n.unop U x).symm))

private theorem coefficientUnitProjection_epi (n : ℕ) :
    Epi (coefficientUnitProjection l E T n) := by
  let F := SheafOfModules.forget (completedIntegralCoefficientSheafUnrestricted l E T)
  have : Epi (F.map (coefficientUnitProjection l E T n)) := by
    apply PresheafOfModules.epi_of_surjective
    intro U x
    obtain ⟨y, hy⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E T n U x
    refine ⟨(integralConstantToCompletionOfUniverses l E T).hom.app U y, ?_⟩
    change (coefficientUnitProjection l E T n).val.app U _ = x
    rw [coefficientUnitProjection_apply]
    exact (congrArg (fun h ↦ h.hom.app U y)
      (limit.lift_π (integralConstantConeOfUniverses l E T) (op n))).trans hy
  exact F.epi_of_epi_map inferInstance

private theorem coefficientStep_epi (n : ℕ) : Epi (coefficientStep l E T n) := by
  have := coefficientUnitProjection_epi l E T n
  have h : coefficientUnitProjection l E T (n + 1) ≫ coefficientStep l E T n =
      coefficientUnitProjection l E T n := by
    simpa only [Functor.const_obj_map, coefficientDiagram, coefficientCone,
      NatTrans.ofOpSequence_app, Functor.ofOpSequence_map_homOfLE_succ,
      Category.id_comp] using
      ((coefficientCone l E T).w (homOfLE n.le_succ).op)
  have : Epi (coefficientUnitProjection l E T (n + 1) ≫ coefficientStep l E T n) :=
    h.symm ▸ inferInstance
  exact epi_of_epi (coefficientUnitProjection l E T (n + 1)) (coefficientStep l E T n)

private theorem extensionUnit_normalized (n : ℕ) :
    ∃ e : (scalarReductionExtension l E T n).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) ≅
          SheafOfModules.unit (integralCoefficientSheaf l E T n),
      (scalarReductionExtension_adjunction l E T n).choose.unit.app _ ≫
        (scalarReductionRestriction l E T n).map e.hom = coefficientUnitProjection l E T n := by
  let B := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
  let S := SheafOfModules.unit (integralCoefficientSheaf l E T n)
  let E₀ := scalarReductionExtension l E T n
  let R₀ := scalarReductionRestriction l E T n
  let adj := (scalarReductionExtension_adjunction l E T n).choose
  let q := coefficientUnitProjection l E T n
  let f : E₀.obj B ⟶ S := (adj.homEquiv B S).symm q
  let η := adj.unit.app B
  let g : S ⟶ E₀.obj B := (E₀.obj B).unitHomEquiv.symm
    ((R₀.obj (E₀.obj B)).unitHomEquiv η)
  have hq (U : T.ProEtᵒᵖ) : q.val.app U
      (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) =
        (1 : (integralCoefficientSheaf l E T n).obj.obj U) :=
    congrArg (fun s ↦ s.val U)
      ((R₀.obj S).unitHomEquiv.apply_symm_apply (S.unitHomEquiv (𝟙 _)))
  have hg (U : T.ProEtᵒᵖ) : g.val.app U
      (1 : (integralCoefficientSheaf l E T n).obj.obj U) =
        η.val.app U (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) :=
    congrArg (fun s ↦ s.val U)
      ((E₀.obj B).unitHomEquiv.apply_symm_apply ((R₀.obj (E₀.obj B)).unitHomEquiv η))
  have hf : η ≫ R₀.map f = q := by
    exact (adj.homEquiv B S).apply_symm_apply q
  have hfg : f ≫ g = 𝟙 _ := by
    apply (adj.homEquiv B (E₀.obj B)).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Adjunction.homEquiv_id]
    apply (R₀.obj (E₀.obj B)).unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    change g.val.app U (q.val.app U
      (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)) =
        η.val.app U (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    rw [hq, hg]
  have hgf : g ≫ f = 𝟙 _ := by
    apply S.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    change f.val.app U (g.val.app U
      (1 : (integralCoefficientSheaf l E T n).obj.obj U)) =
        (1 : (integralCoefficientSheaf l E T n).obj.obj U)
    rw [hg]
    have h := congrArg (fun k ↦ k.val.app U
      (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)) hf
    exact h.trans (hq U)
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

private theorem normalizedUnit_products
    {A : Type a} {B : Type b} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) (R : B ⥤ A) [F.Additive] [R.Additive]
    (η : 𝟭 A ⟶ F ⋙ R) (X : A) (Y : B) (e : F.obj X ≅ Y) (p : X ⟶ R.obj Y)
    (he : η.app X ≫ R.map e.hom = p) (r : ℕ) :
    ∃ eP : (F ⋙ R).obj (∏ᶜ fun _ : Fin r ↦ X) ≅ ∏ᶜ fun _ : Fin r ↦ R.obj Y,
      η.app _ ≫ eP.hom = Limits.Pi.map (fun _ : Fin r ↦ p) := by
  classical
  let eP := PreservesProduct.iso (F ⋙ R) (fun _ : Fin r ↦ X) ≪≫
    Limits.Pi.mapIso (fun _ : Fin r ↦ R.mapIso e)
  refine ⟨eP, ?_⟩
  apply Limits.Pi.hom_ext
  intro j
  simp only [eP, Iso.trans_hom, Category.assoc, Limits.Pi.mapIso_hom_π,
    Functor.mapIso_hom, Limits.Pi.map_π]
  rw [PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  rw [← Category.assoc, ← η.naturality]
  simpa only [Functor.id_map, Category.assoc] using congrArg
    (fun k ↦ Pi.π (fun _ : Fin r ↦ X) j ≫ k) he

private theorem freePower_normalized (n r : ℕ) :
    let B : scalarReductionSource l E T :=
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
    let S := (scalarReductionRestriction l E T n).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E T n))
    ∃ e : (scalarReductionRestriction l E T n).obj
        ((scalarReductionExtension l E T n).obj (∏ᶜ fun _ : Fin r ↦ B)) ≅
          ∏ᶜ fun _ : Fin r ↦ S,
      (scalarReductionExtension_adjunction l E T n).choose.unit.app _ ≫ e.hom =
        Limits.Pi.map (fun _ : Fin r ↦ coefficientUnitProjection l E T n) := by
  let X : scalarReductionSource l E T :=
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
  exact (extensionUnit_normalized l E T n).elim fun e he ↦
    normalizedUnit_products (scalarReductionExtension l E T n)
      (scalarReductionRestriction l E T n)
      (scalarReductionExtension_adjunction l E T n).choose.unit X _ e _ he r

private def finitePower {A : Type a} [Category.{b} A] [HasFiniteProducts A]
    (r : ℕ) : A ⥤ A where
  obj M := ∏ᶜ fun _ : Fin r ↦ M
  map f := Limits.Pi.map (fun _ : Fin r ↦ f)
  map_id _ := Limits.Pi.map_id
  map_comp _ _ := (Limits.Pi.map_comp_map _ _).symm

private def finitePowerIso {A : Type a} [Category.{b, a} A] [HasFiniteProducts A]
    (r : ℕ) : (Functor.const (Discrete (Fin r)) ⋙ lim : A ⥤ A) ≅ finitePower r := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact (HasLimit.isoOfNatIso
      (Discrete.natIsoFunctor (F := (Functor.const (Discrete (Fin r))).obj M)))
  · intro X Y f
    apply Limits.Pi.hom_ext
    intro j
    simp only [finitePower, Limits.Pi.map_π, Category.assoc]
    rw [HasLimit.isoOfNatIso_hom_π, HasLimit.isoOfNatIso_hom_π_assoc]
    dsimp only [Discrete.natIsoFunctor, Discrete.natIso, NatIso.ofComponents]
    simp only [Iso.refl_hom, Category.comp_id, Functor.comp_map]
    simpa only [limMap_eq, Functor.const_map_app, Category.id_comp] using
      (limMap_π ((Functor.const (Discrete (Fin r))).map f) ⟨j⟩)

private instance finitePower_limits {A : Type a} [Category.{b} A] [HasFiniteProducts A]
    (r : ℕ) : PreservesLimitsOfSize.{0, 0} (finitePower (A := A) r) :=
  preservesLimits_of_natIso (finitePowerIso r)

private instance finitePower_epi {A : Type a} [Category.{b} A] [Abelian A]
    (r : ℕ) : (finitePower (A := A) r).PreservesEpimorphisms := by
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : (Functor.const (Discrete (Fin r)) ⋙ lim : A ⥤ A).PreservesEpimorphisms :=
    inferInstance
  exact Functor.PreservesEpimorphisms.of_iso (finitePowerIso r)

private theorem integralUnit_eq (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (n : ℕ) :
    integralTowerUnit l E T D hl P n =
      (NatTrans.mapHomologicalComplex
        (scalarReductionExtension_adjunction l E T n).choose.unit (.up ℤ)).app P := by
  have hunit : integralTowerUnitCondition l E T D hl P
      (integralTowerUnit l E T D hl P) :=
    (integralTowerMaps_existUnique l E T D hl P).exists.choose_spec.1
  ext i U x
  exact (hunit n i U x).trans
    ((scalarReductionExtension_adjunction l E T n).choose_spec (P.X i) U x).symm

private theorem normalizedUnit_single
    {A : Type a} [Category.{b, a} A] [Abelian A] (F : A ⥤ A) [F.Additive]
    (η : 𝟭 A ⟶ F) (X Y : A) (e : F.obj X ≅ Y) (p : X ⟶ Y)
    (he : η.app X ≫ e.hom = p) (d : ℤ) :
    (NatTrans.mapHomologicalComplex η (.up ℤ)).app
        ((CochainComplex.singleFunctor A d).obj X) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) d).app X).hom ≫
      (CochainComplex.singleFunctor A d).map e.hom =
        (CochainComplex.singleFunctor A d).map p := by
  dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, Iso.app_hom,
    NatTrans.mapHomologicalComplex_app_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← η.naturality]
  simpa only [Functor.id_map, Category.assoc] using congrArg
    (fun f ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) d X).hom ≫ f ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) d Y).inv) he

private theorem freeCell_normalized (r : ℕ) (d : ℤ) (n : ℕ) :
    let B := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
    let P := (CochainComplex.singleFunctor (scalarReductionSource l E T) d).obj
      (∏ᶜ fun _ : Fin r ↦ B)
    ∃ e : integralTowerComplex l E T D hl n P ≅
        (CochainComplex.singleFunctor _ d).obj
          (∏ᶜ fun _ : Fin r ↦ (coefficientDiagram l E T).obj (op n)),
      integralTowerUnit l E T D hl P n ≫ e.hom =
        (CochainComplex.singleFunctor _ d).map
          (Limits.Pi.map (fun _ : Fin r ↦ coefficientUnitProjection l E T n)) := by
  classical
  let B := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
  let F := scalarReductionExtension l E T n ⋙ scalarReductionRestriction l E T n
  let S := HomologicalComplex.single (scalarReductionSource l E T) (.up ℤ) d
  obtain ⟨e, he⟩ := freePower_normalized l E T n r
  let eC := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) d).app
      (∏ᶜ fun _ : Fin r ↦ B) ≪≫ S.mapIso e
  refine ⟨eC, ?_⟩
  rw [integralUnit_eq]
  exact normalizedUnit_single F
    (scalarReductionExtension_adjunction l E T n).choose.unit _ _ e _ he d

/-- Ordinary finite free quotient towers have their specified augmentation as a limit
cone and epimorphic transitions in every degree.

Source: Stacks Project, algebraization.tex, Tag 099I; Bhatt--Scholze, Propositions
3.1.9--3.1.10 (blueprint: lem-sf-completed-free-cell-ordinary-limit).

Proof: ordinary scalar extension of the unit is the unit of the quotient coefficient
ring, by the balanced multiplication isomorphism. Its inverse sends a to a tensor 1.
The specified augmentation is the limit projection under this isomorphism, since it
sends b to 1 tensor b, hence to its residue. Scalar extension is additive and preserves
finite biproducts. Thus extension of the product indexed by Fin r is the product of
r quotient units, coordinate by coordinate, also when r is zero. The comparisons
commute with all quotient transitions, by their defining pure-tensor formulas.
A compatible family of r-tuples is r compatible families, so finite products preserve
the defining limit of the completed coefficient ring. The module forgetful functors
reflect these limits and preserve the projections. The single-complex functor in any
integer degree preserves limits, yielding precisely the displayed cone. Quotient ring
transitions are surjective; their constant sheaf maps are surjective on sections by
lifting through a set-theoretic section of the ring quotient. They are epimorphic as
module maps. Finite products are finite biproducts and preserve epimorphisms; placing
these maps in a single degree gives epimorphisms in every degree, with zero maps between
zero objects in all other degrees. No derived-limit assertion is assumed here. -/
theorem completedFreeCell_ordinaryLimit (r : ℕ) (d : ℤ) :
    let P := (CochainComplex.singleFunctor (scalarReductionSource l E T) d).obj
      (∏ᶜ fun _ : Fin r ↦
        SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T))
    Nonempty (IsLimit (completedFreeCellCone l E T D hl P)) ∧
      ∀ (n : ℕ) (i : ℤ), Epi ((integralTowerTransition l E T D hl P n).f i) := by
  classical
  let A := scalarReductionSource l E T
  let : Abelian A := inferInstanceAs (Abelian (scalarReductionSource l E T))
  let : HasFiniteProducts A := inferInstance
  let B := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
  let S := HomologicalComplex.single A (.up ℤ) d
  let F : A ⥤ A := finitePower r
  let P := S.obj (F.obj B)
  let T₁ := Functor.ofOpSequence (X := fun n ↦ integralTowerComplex l E T D hl n P)
    (integralTowerTransition l E T D hl P)
  let T₂ := coefficientDiagram l E T ⋙ F ⋙ S
  let c := (F ⋙ S).mapCone (coefficientCone l E T)
  choose e he using fun n ↦ freeCell_normalized l E T D hl r d n
  have he' (n : ℕ) : integralTowerUnit l E T D hl P n ≫ (e n).hom =
      S.map (F.map (coefficientUnitProjection l E T n)) := by
    exact he n
  have hunit_epi (n : ℕ) : Epi (integralTowerUnit l E T D hl P n) := by
    have := coefficientUnitProjection_epi l E T n
    have : F.PreservesEpimorphisms := by dsimp only [F]; infer_instance
    have h : integralTowerUnit l E T D hl P n ≫ (e n).hom =
        S.map (F.map (coefficientUnitProjection l E T n)) := by
      exact he' n
    have : Epi (integralTowerUnit l E T D hl P n ≫ (e n).hom) := h.symm ▸ inferInstance
    exact (epi_comp_iff_of_isIso _ (e n).hom).1 inferInstance
  let α : T₁ ⟶ T₂ := NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
    intro n
    simp only [T₁, T₂, Functor.comp_map, coefficientDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply (cancel_epi (integralTowerUnit l E T D hl P (n + 1))).1
    rw [← Category.assoc, ← completedFreeCellCone_compatibility, Category.id_comp]
    rw [he', ← Category.assoc, he', ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun f ↦ S.map (F.map f))
      (by simpa only [coefficientDiagram, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.const_obj_map, coefficientCone, NatTrans.ofOpSequence_app,
        Category.id_comp] using
        ((coefficientCone l E T).w (homOfLE n.le_succ).op).symm))
  have (n : ℕᵒᵖ) : IsIso (α.app n) := inferInstanceAs (IsIso (e n.unop).hom)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have hc : IsLimit c := isLimitOfPreserves (F ⋙ S) (coefficientCone_isLimit l E T).some
  have hcone : (Cone.postcompose α).obj (completedFreeCellCone l E T D hl P) ≅ c :=
    Cone.ext (Iso.refl _) (by
      intro n
      change integralTowerUnit l E T D hl P n.unop ≫ (e n.unop).hom =
        𝟙 _ ≫ S.map (F.map (coefficientUnitProjection l E T n.unop))
      rw [Category.id_comp]
      exact he' n.unop)
  refine ⟨⟨(IsLimit.postcomposeHomEquiv (asIso α) _).toFun
    (hc.ofIsoLimit hcone.symm)⟩, ?_⟩
  intro n i
  have := coefficientStep_epi l E T n
  have : F.PreservesEpimorphisms := by dsimp only [F]; infer_instance
  have ht : Epi ((T₂.map (homOfLE n.le_succ).op).f i) := by
    simp only [T₂, Functor.comp_map, coefficientDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    have : Epi (F.map (coefficientStep l E T n)) := Functor.map_epi _ _
    have : Epi (S.map (F.map (coefficientStep l E T n))) := Functor.map_epi S _
    exact Functor.map_epi (HomologicalComplex.eval A (.up ℤ) i)
      (S.map (F.map (coefficientStep l E T n)))
  have := ht
  have h := congrArg (fun f ↦ f.f i) (α.naturality (homOfLE n.le_succ).op)
  have : IsIso ((α.app (op n)).f i) := inferInstance
  have : IsIso ((α.app (op (n + 1))).f i) := inferInstance
  have hcomp : Epi ((T₁.map (homOfLE n.le_succ).op).f i ≫ (α.app (op n)).f i) := by
    rw [show (T₁.map (homOfLE n.le_succ).op).f i ≫ (α.app (op n)).f i =
      (α.app (op (n + 1))).f i ≫ (T₂.map (homOfLE n.le_succ).op).f i from h]
    infer_instance
  simpa only [T₁, Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_obj,
    P, S, F, finitePower, B, CochainComplex.singleFunctor, CochainComplex.singleFunctors] using
    (epi_comp_iff_of_isIso ((T₁.map (homOfLE n.le_succ).op).f i)
      ((α.app (op n)).f i)).1 hcomp

end WeilConjectures
