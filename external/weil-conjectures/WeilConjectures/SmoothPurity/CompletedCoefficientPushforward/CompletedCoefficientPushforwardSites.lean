/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Site-side coefficient restrictions and derived tower limits

Source: Stacks Tags 03DA, 0D6E and 0941; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b av bv c cv z zv d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
private noncomputable def exactImage
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ExactImage F :=
  ⟨F.mapDerivedCategory, F.mapDerivedCategoryFactors⟩

private noncomputable def exactComposition
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
    {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) :
    ExactComposition F G H (exactImage H) (exactImage F) (exactImage G) := by
  letI : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G
  letI : PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G
  refine ⟨e, Functor.mapDerivedCategoryCompIso F G ≪≫
    Functor.mapDerivedCategoryNatIso e, ?_⟩
  intro K
  exact Functor.exactDerivedRestrictionComposition_hom_factors F G H e K

private noncomputable def exactIdentity
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
    (F : A ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 A) : ExactIdentity F (exactImage F) := by
  refine ⟨e, Functor.exactDerivedRestrictionUnit F e, ?_⟩
  intro K
  dsimp only [exactImage, Functor.exactDerivedRestrictionUnit, Iso.trans_hom,
    NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Q_obj,
    Functor.mapDerivedCategoryNatIso_fac]
  rfl

private instance restrictionLimits
    {C : Type a} [Category.{av} C] {J : GrothendieckTopology C}
    {B D : Sheaf J RingCat.{u}} (α : B ⟶ D)
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} α) :=
  (normalizedDVRRestrictionExact α).1

private instance restrictionColimits
    {C : Type a} [Category.{av} C] {J : GrothendieckTopology C}
    {B D : Sheaf J RingCat.{u}} (α : B ⟶ D)
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} α) :=
  (normalizedDVRRestrictionExact α).2

private noncomputable def restrictionImage (W : Scheme.{t})
    {B C : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}} (a : B ⟶ C) :
    ExactImage (SheafOfModules.restrictScalars.{max u (t + 1)} a) :=
  exactImage _

private noncomputable def restrictionComp (W : Scheme.{t})
    {B C D : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}}
    (a : B ⟶ C) (b : C ⟶ D) (c : B ⟶ D) (h : a ≫ b = c) :
    ExactComposition (SheafOfModules.restrictScalars.{max u (t + 1)} b)
      (SheafOfModules.restrictScalars.{max u (t + 1)} a)
      (SheafOfModules.restrictScalars.{max u (t + 1)} c)
      (restrictionImage W c) (restrictionImage W b) (restrictionImage W a) :=
  exactComposition _ _ _ (normalizedDVRRestrictionCompIso a b ≪≫
    eqToIso (congrArg (fun k ↦ SheafOfModules.restrictScalars.{max u (t + 1)} k) h))

private theorem restrictionComp_sections (W : Scheme.{t})
    {B C D : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}}
    (a : B ⟶ C) (b : C ⟶ D) (c : B ⟶ D) (h : a ≫ b = c) :
    IsSectionwiseIdentity W B (restrictionComp W a b c h).ordinary.hom := by
  subst c
  intro M U x
  rfl

private noncomputable def restrictionUnit (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)})
    (a : B ⟶ B) (h : a = 𝟙 B) :
    ExactIdentity (SheafOfModules.restrictScalars.{max u (t + 1)} a)
      (restrictionImage W a) :=
  exactIdentity _ (eqToIso
    (congrArg (fun k ↦ SheafOfModules.restrictScalars.{max u (t + 1)} k) h))

private theorem restrictionUnit_sections (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)})
    (a : B ⟶ B) (h : a = 𝟙 B) :
    IsSectionwiseIdentity W B (restrictionUnit W B a h).ordinary.hom := by
  subst a
  intro M U x
  rfl

private noncomputable def finiteCoefficientEquiv (n : ℕ) :
    (systemRing.{t, u} l E ⧸
      (Ideal.span ({systemUniformizer.{t, u} l E} : Set (systemRing.{t, u} l E))) ^
        (n + 1)) ≃+* ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)) :=
  (Ideal.quotientEquiv _ (Padic.coefficientExtensionIdeal l E (n + 1))
    ULift.ringEquiv (by
      rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
      rfl)).trans ULift.ringEquiv.symm

private noncomputable def finiteCoefficientIso (W : Scheme.{t}) (n : ℕ) :
    modelRing l E W n ≅ N l E W n :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso
      ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).mapIso
        (finiteCoefficientEquiv.{t, u} l E n).toCommRingCatIso)

private theorem finiteCoefficientIso_generator (W : Scheme.{t}) (n : ℕ)
    (U : W.ProEtᵒᵖ) (a : systemRing.{t, u} l E) :
    ((finiteCoefficientIso l E W n).hom.hom.app U)
        ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (systemRing.{t, u} l E ⧸
            (Ideal.span ({systemUniformizer.{t, u} l E} : Set (systemRing.{t, u} l E))) ^
              (n + 1))))).app U (Ideal.Quotient.mk _ a)) =
      (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U
          (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down)) := by
  have h := congrArg (fun k ↦ k.app U (Ideal.Quotient.mk _ a))
    (toSheafify_naturality (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).map
        (finiteCoefficientEquiv.{t, u} l E n).toCommRingCatIso.hom))
  exact h.symm

private abbrev modelTransition (W : Scheme.{t}) (n : ℕ) :
    modelRing l E W (n + 1) ⟶ modelRing l E W n :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (SheafOfModules.coefficientQuotientMap (J := ProEt.topology W)
        (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E) (Nat.le_succ n))

private theorem finiteCoefficientIso_transition (W : Scheme.{t}) (n : ℕ) :
    (finiteCoefficientIso l E W (n + 1)).hom ≫ integralCoefficientSheafTransition l E W n =
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (SheafOfModules.coefficientQuotientMap (J := ProEt.topology W)
            (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E) (Nat.le_succ n)) ≫
        (finiteCoefficientIso l E W n).hom := by
  dsimp only [finiteCoefficientIso, Functor.mapIso_hom, integralCoefficientSheafTransition,
    SheafOfModules.coefficientQuotientMap]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  ext x
  rfl

private noncomputable def systemLeg (W : Scheme.{t}) (n : ℕ) :
    R l E W ⟶ modelRing l E W n :=
  projection l E W n ≫ (finiteCoefficientIso l E W n).inv

private theorem systemLeg_transition (W : Scheme.{t}) (n : ℕ) :
    systemLeg l E W (n + 1) ≫
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (SheafOfModules.coefficientQuotientMap (J := ProEt.topology W)
            (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E) (Nat.le_succ n)) =
      systemLeg l E W n := by
  apply (cancel_mono (finiteCoefficientIso l E W n).hom).mp
  dsimp only [systemLeg]
  rw [Category.assoc, Category.assoc, ← finiteCoefficientIso_transition,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [projection, R, completedIntegralCoefficientSheafUnrestricted, N,
    integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ] using
    limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op

-- Keep quotient sheafification out of module-functor unification.
attribute [local irreducible] SheafOfModules.coefficientQuotientSheaf
  SheafOfModules.coefficientQuotientMap finiteCoefficientIso integralCoefficientSheaf

private noncomputable def restrictSemilinear (W : Scheme.{t})
    {B S T : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}}
    (a : B ⟶ S) (b : B ⟶ T) (c : S ⟶ T) (h : a ≫ c = b)
    {M : Mod W S} {N : Mod W T} (q : M ⟶ (SheafOfModules.restrictScalars c).obj N) :
    (SheafOfModules.restrictScalars a).obj M ⟶ (SheafOfModules.restrictScalars b).obj N :=
  (SheafOfModules.restrictScalars a).map q ≫
    eqToHom (congrArg (fun k ↦ (SheafOfModules.restrictScalars.{max u (t + 1)} k).obj N) h)

private theorem restrictSemilinear_sections (W : Scheme.{t})
    {B S T : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}}
    (a : B ⟶ S) (b : B ⟶ T) (c : S ⟶ T) (h : a ≫ c = b)
    {M : Mod W S} {N : Mod W T} (q : M ⟶ (SheafOfModules.restrictScalars c).obj N)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (restrictSemilinear W a b c h q).val.app U x = q.val.app U x := by
  subst b
  rfl

private noncomputable def restrictedSystem (W : Scheme.{t}) (M : Systems l E W) :
    ℕᵒᵖ ⥤ Mod W (R l E W) :=
  Functor.ofOpSequence
    (X := fun n ↦ (SheafOfModules.restrictScalars (systemLeg l E W n)).obj (M.level n))
    (fun n ↦ restrictSemilinear W (systemLeg l E W (n + 1)) (systemLeg l E W n)
          (modelTransition l E W n) (systemLeg_transition l E W n) (M.transition n))

private theorem restrictSemilinear_naturality (W : Scheme.{t})
    {B S T : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}}
    (a : B ⟶ S) (b : B ⟶ T) (c : S ⟶ T) (h : a ≫ c = b)
    {M M' : Mod W S} {N N' : Mod W T} (q : M ⟶ (SheafOfModules.restrictScalars c).obj N)
    (q' : M' ⟶ (SheafOfModules.restrictScalars c).obj N') (u : M ⟶ M') (v : N ⟶ N')
    (hq : u ≫ q' = q ≫ (SheafOfModules.restrictScalars c).map v) :
    (SheafOfModules.restrictScalars a).map u ≫ restrictSemilinear W a b c h q' =
      restrictSemilinear W a b c h q ≫ (SheafOfModules.restrictScalars b).map v := by
  subst b
  ext U x
  change q'.val.app U (u.val.app U x) = v.val.app U (q.val.app U x)
  exact congrArg (fun k ↦ k.val.app U x) hq

private theorem restrictedSystem_map_comm (W : Scheme.{t})
    {M N : Systems l E W} (h : M ⟶ N) (n : ℕ) :
    (SheafOfModules.restrictScalars (systemLeg l E W (n + 1))).map (h.app (n + 1)) ≫
        restrictSemilinear W (systemLeg l E W (n + 1)) (systemLeg l E W n)
          (modelTransition l E W n) (systemLeg_transition l E W n) (N.transition n) =
      restrictSemilinear W (systemLeg l E W (n + 1)) (systemLeg l E W n)
          (modelTransition l E W n) (systemLeg_transition l E W n) (M.transition n) ≫
        (SheafOfModules.restrictScalars (systemLeg l E W n)).map (h.app n) :=
  restrictSemilinear_naturality W (systemLeg l E W (n + 1)) (systemLeg l E W n)
    (modelTransition l E W n) (systemLeg_transition l E W n)
    (M.transition n) (N.transition n) (h.app (n + 1)) (h.app n) (h.comm n)

private noncomputable def restrictSystems (W : Scheme.{t}) :
    Systems l E W ⥤ (ℕᵒᵖ ⥤ Mod W (R l E W)) where
  obj := restrictedSystem l E W
  map {M N} h := NatTrans.ofOpSequence (F := restrictedSystem l E W M)
    (G := restrictedSystem l E W N) (fun n ↦
    (SheafOfModules.restrictScalars (systemLeg l E W n)).map (h.app n))
    (by
      intro n
      dsimp only [restrictedSystem]
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      exact (restrictedSystem_map_comm l E W h n).symm)
  map_id M := by
    ext n U x
    rfl
  map_comp h k := by
    ext n U x
    rfl

private instance restrictSystemsAdditive (W : Scheme.{t}) :
    (restrictSystems l E W).Additive where
  map_add := by
    intro M N h k
    apply NatTrans.ext
    funext n
    change (SheafOfModules.restrictScalars (systemLeg l E W n.unop)).map
        ((SheafOfModules.coefficientEvaluation (J := ProEt.topology W)
          (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n.unop).map
            (h + k)) = _
    rw [Functor.map_add, Functor.map_add]
    rfl

private instance restrictSystemsLimits (W : Scheme.{t}) :
    PreservesFiniteLimits (restrictSystems l E W) where
  preservesFiniteLimits J _ _ := by
    apply preservesLimitsOfShape_of_evaluation
    intro n
    let := integralCoefficientAbSheafify.{t, u} W
    let := integralCoefficientAbLocallyBijective.{t, u} W
    have := (SheafOfModules.coefficientEvaluation_exact
      (J := ProEt.topology W) (O := systemRing.{t, u} l E)
      (ell := systemUniformizer.{t, u} l E) n.unop).1
    exact inferInstanceAs (PreservesLimitsOfShape J
      (SheafOfModules.coefficientEvaluation (J := ProEt.topology W)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n.unop ⋙
          SheafOfModules.restrictScalars (systemLeg l E W n.unop)))

private instance restrictSystemsColimits (W : Scheme.{t}) :
    PreservesFiniteColimits (restrictSystems l E W) where
  preservesFiniteColimits J _ _ := by
    apply preservesColimitsOfShape_of_evaluation
    intro n
    let := integralCoefficientAbSheafify.{t, u} W
    let := integralCoefficientAbLocallyBijective.{t, u} W
    have := (SheafOfModules.coefficientEvaluation_exact
      (J := ProEt.topology W) (O := systemRing.{t, u} l E)
      (ell := systemUniformizer.{t, u} l E) n.unop).2
    exact inferInstanceAs (PreservesColimitsOfShape J
      (SheafOfModules.coefficientEvaluation (J := ProEt.topology W)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n.unop ⋙
          SheafOfModules.restrictScalars (systemLeg l E W n.unop)))

private noncomputable def siteCoefficients (W : Scheme.{t}) : SiteCoefficientData l E W where
  U := restrictionImage W (integralConstantToCompletionOfUniverses l E W)
  V n := restrictionImage W (projection l E W n)
  restriction h := restrictionImage W (quotientMap l E W h)
  finiteIso := finiteCoefficientIso l E W
  finiteIso_generator := finiteCoefficientIso_generator l E W
  restrictionComposition hkm hmn := restrictionComp W _ _ _
    ((integralCoefficientSheafSystem l E W).map_comp (homOfLE hkm).op (homOfLE hmn).op).symm
  restrictionComposition_identity _hkm _hmn := restrictionComp_sections W _ _ _ _
  restrictionIdentity n := restrictionUnit W _ _
    ((integralCoefficientSheafSystem l E W).map_id (op n))
  restrictionIdentity_sections _n := restrictionUnit_sections W _ _ _
  projectionComposition h := restrictionComp W _ _ _
    (limit.w (integralCoefficientSheafSystem l E W) (homOfLE h).op)
  projectionComposition_identity _h := restrictionComp_sections W _ _ _ _

-- Avoid expanding chosen coefficient sheafification in record comparison.
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private noncomputable def systemEvaluationIso (W : Scheme.{t}) (n : ℕ) :
    restrictSystems l E W ⋙ (evaluation ℕᵒᵖ (Mod W (R l E W))).obj (op n) ≅
      SheafOfModules.coefficientEvaluation (J := ProEt.topology W)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
          model l E W n (finiteCoefficientIso l E W n) ⋙
            SheafOfModules.restrictScalars (projection l E W n) :=
  (Functor.isoWhiskerLeft
    (SheafOfModules.coefficientEvaluation (J := ProEt.topology W)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n)
    (normalizedDVRRestrictionCompIso (projection l E W n)
      (finiteCoefficientIso l E W n).inv)).symm

private theorem systemEvaluationIso_sections (W : Scheme.{t}) (n : ℕ) :
    IsSectionwiseIdentity W (R l E W) (systemEvaluationIso l E W n).hom := by
  intro M U x
  exact HEq.rfl

private theorem sequence_successor_sections
    {C : Type a} [Category.{av} C] {J : GrothendieckTopology C}
    (B : Sheaf J RingCat.{u}) (M : ℕ → SheafOfModules.{u} B)
    (q : ∀ n, M (n + 1) ⟶ M n) (n : ℕ) (U : Cᵒᵖ) :
    (fun x ↦ (((Functor.ofOpSequence q).map
      (homOfLE (Nat.le_succ n)).op).val.app U) x) =
      (fun x ↦ ((q n).val.app U) x) := by
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private theorem systemTransition_sections (W : Scheme.{t})
    (M : Systems l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    HEq (fun x ↦ (((restrictedSystem l E W M).map
      (homOfLE (Nat.le_succ n)).op).val.app U) x)
      (fun x ↦ ((M.transition n).val.app U) x) := by
  apply heq_of_eq
  exact (sequence_successor_sections (R l E W)
    (fun k ↦ (SheafOfModules.restrictScalars (systemLeg l E W k)).obj (M.level k))
    (fun k ↦ restrictSemilinear W (systemLeg l E W (k + 1)) (systemLeg l E W k)
      (modelTransition l E W k) (systemLeg_transition l E W k) (M.transition k)) n U).trans
        (funext (restrictSemilinear_sections W (systemLeg l E W (n + 1))
          (systemLeg l E W n) (modelTransition l E W n) (systemLeg_transition l E W n)
          (M.transition n) U))

private noncomputable def siteSystems (W : Scheme.{t}) : SystemRestrictionData l E W where
  toSiteCoefficientData := siteCoefficients l E W
  systemRestriction := restrictSystems l E W
  systemEvaluation := systemEvaluationIso l E W
  systemEvaluation_identity := systemEvaluationIso_sections l E W
  systemTransition := systemTransition_sections l E W
  systemMap _M _M' _h _n _U := HEq.rfl
  systemFactors := exactImage _

private instance moduleGrothendieck (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    IsGrothendieckAbelian.{max u (t + 1)} (Mod W B) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let := integralCoefficientAbSheafify.{t, u} W
  let := integralCoefficientAbLocallyBijective.{t, u} W
  exact CategoryTheory.moduleSheaves_grothendieck (ProEt.topology W) B

private instance towersGrothendieck (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ Mod W B) :=
  CategoryTheory.tower_grothendieck _

private instance towerLimitAdditive (W : Scheme.{t}) : (ordinaryTowerLimit l E W).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp only [ordinaryTowerLimit, lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
    Preadditive.comp_add]

private theorem siteLimits (W : Scheme.{t}) : Nonempty (SiteLimitData l E W) := by
  obtain ⟨L, η, hL, hI, _⟩ := CategoryTheory.totalDerivedData (ordinaryTowerLimit l E W)
  have := hL
  let : HasFiniteColimits (Mod W (R l E W)) := Abelian.hasFiniteColimits
  let : HasFiniteLimits (Mod W (R l E W)) := Abelian.hasFiniteLimits
  let V (n : ℕ) := exactImage ((evaluation ℕᵒᵖ (Mod W (R l E W))).obj (op n))
  let β (n : ℕ) : (ordinaryTowerLimit l E W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (V n).functor :=
    Functor.whiskerRight (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ))
      DerivedCategory.Q ≫ (V n).factors.inv
  let p (n : ℕ) := L.rightDerivedDesc η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod W (R l E W)) (.up ℤ)) (V n).functor (β n)
  refine ⟨{ limit := ⟨L, η, hL, hI⟩
            evaluation := V
            limitProjection := p
            limitProjection_normalization := ?_ }⟩
  intro M n
  change η.app M ≫ (p n).app (DerivedCategory.Q.obj M) ≫ (V n).factors.hom.app M = _
  rw [← Category.assoc, Functor.rightDerived_fac_app]
  dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The exact restrictions, strict coefficient-system restriction and normalized total
inverse limit exist on the original pro-etale site with independent coefficient universes.

Source: Stacks Tags 03DA, 0D6E and 0941; Zheng, Construction 4.1
(blueprint: lem-pur-completed-coefficient-site-data).
Proof: identify the two finite quotient rings by the quotient of the ULift ring
isomorphism. Quotient generators show that these identifications commute with successive
reductions. Restrict each level along its completed-ring projection and this isomorphism;
restriction of the semilinear transition then gives a strict completed-module tower.
This functor is additive and exact, since evaluation is exact and jointly reflects
finite limits and finite colimits. Localize the exact restrictions and their ordinary
identity and composition isomorphisms. The localization factorization equations give
all recorded normalizations. Module sheaves and their tower category are Grothendieck,
so inverse limit has a K-injective total right derived functor. Its universal property
applied to each ordinary projection gives the normalized derived projections. -/
theorem siteData_exists (W : Scheme.{t}) : Nonempty (SiteData l E W) := by
  obtain ⟨L⟩ := siteLimits l E W
  exact ⟨{ toSystemRestrictionData := siteSystems l E W, toSiteLimitData := L }⟩

end WeilConjectures.CompletedCoefficientPushforward
