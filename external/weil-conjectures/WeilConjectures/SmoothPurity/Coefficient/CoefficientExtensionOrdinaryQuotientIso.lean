/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel

/-! # Ordinary quotient association for a strict scalar tensor complex

Source: Stacks 03D7, 03D8, and 03EK; the ordinary part of steps 1--2 of
stage3-pur-extension-strict-tensor-normalized.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard integralScalarReduction
  constantSheaf coefficientSequenceTransition coefficientSequenceEvaluation
  completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientFiniteQuotientExtension coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence coefficientFiniteQuotientDerived
section GenericAssociation
variable {A B C : Type*} [Category A] [Category B] [Category C]
  {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
  {R : B ⥤ A} {S : C ⥤ B} {T : C ⥤ A}

private def association (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ T) (r : S ⋙ R ≅ T) :
    F ⋙ G ≅ H :=
  ((a.comp b).ofNatIsoRight r).leftAdjointUniq c

attribute [local irreducible] association

private theorem association_unit (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ T)
    (r : S ⋙ R ≅ T) (M : A) :
    a.unit.app M ≫ R.map (b.unit.app (F.obj M)) ≫
      r.hom.app ((F ⋙ G).obj M) ≫ T.map ((association a b c r).hom.app M) =
        c.unit.app M := by
  have hh := ((a.comp b).ofNatIsoRight r).unit_leftAdjointUniq_hom_app c M
  simpa only [association, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Category.assoc] using hh

end GenericAssociation

section GenericRestriction
universe c v r s
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  {R S T : Sheaf J RingCat.{r}}

private def restrictionTriangle (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T)
    (hk : f ≫ g = k) :
    SheafOfModules.restrictScalars.{s} g ⋙ SheafOfModules.restrictScalars.{s} f ≅
      SheafOfModules.restrictScalars.{s} k :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
        (k.hom.app U).hom (congrArg (fun z ↦ (z.hom.app U).hom) hk.symm)
          (M.val.obj U)).symm) (by intros; ext x; rfl))) (by intros; ext U x; rfl)

private theorem restrictionTriangle_hom_apply (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T)
    (hk : f ≫ g = k) (M : SheafOfModules.{s} T) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((restrictionTriangle f g k hk).hom.app M).val.app U x = x := by
  unfold restrictionTriangle
  rfl

attribute [local irreducible] restrictionTriangle
end GenericRestriction

section GenericAssociationData
universe c v r s
variable {D : Type c} [Category.{v} D] {J : GrothendieckTopology D}
private structure UnitAssociation
    {A B C : Sheaf J RingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C)
    (F : SheafOfModules.{s} A ⥤ SheafOfModules.{s} B)
    (G : SheafOfModules.{s} B ⥤ SheafOfModules.{s} C)
    (H : SheafOfModules.{s} A ⥤ SheafOfModules.{s} C)
    (a : F ⊣ SheafOfModules.restrictScalars f)
    (b : G ⊣ SheafOfModules.restrictScalars g)
    (c : H ⊣ SheafOfModules.restrictScalars k) where
  iso : F ⋙ G ≅ H
  unit : ∀ (M : SheafOfModules.{s} A) (U : Dᵒᵖ) (x : M.val.obj U),
    (iso.hom.app M).val.app U
      ((b.unit.app (F.obj M)).val.app U ((a.unit.app M).val.app U x)) =
        (c.unit.app M).val.app U x

private def associationWithUnit
    {A B C : Sheaf J RingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (hk : f ≫ g = k)
    (F : SheafOfModules.{s} A ⥤ SheafOfModules.{s} B)
    (G : SheafOfModules.{s} B ⥤ SheafOfModules.{s} C)
    (H : SheafOfModules.{s} A ⥤ SheafOfModules.{s} C)
    (a : F ⊣ SheafOfModules.restrictScalars f)
    (b : G ⊣ SheafOfModules.restrictScalars g)
    (c : H ⊣ SheafOfModules.restrictScalars k) : UnitAssociation f g k F G H a b c := by
  let e := association a b c (restrictionTriangle f g k hk)
  refine ⟨e, ?_⟩
  intro M U x
  have hu := association_unit a b c (restrictionTriangle f g k hk) M
  have hx := congrArg (fun z ↦ (z.val.app U) x) hu
  change (e.hom.app M).val.app U
    (((restrictionTriangle f g k hk).hom.app ((F ⋙ G).obj M)).val.app U
      ((b.unit.app (F.obj M)).val.app U ((a.unit.app M).val.app U x))) =
        (c.unit.app M).val.app U x at hx
  simpa only [restrictionTriangle_hom_apply] using hx

attribute [local irreducible] associationWithUnit
private theorem UnitAssociation.complex_iso
    {A B C : Sheaf J RingCat.{r}}
    {f : A ⟶ B} {g : B ⟶ C} {k : A ⟶ C}
    {F : SheafOfModules.{s} A ⥤ SheafOfModules.{s} B}
    {G : SheafOfModules.{s} B ⥤ SheafOfModules.{s} C}
    {H : SheafOfModules.{s} A ⥤ SheafOfModules.{s} C}
    {a : F ⊣ SheafOfModules.restrictScalars f}
    {b : G ⊣ SheafOfModules.restrictScalars g}
    {c : H ⊣ SheafOfModules.restrictScalars k}
    [F.Additive] [G.Additive] [H.Additive]
    (data : UnitAssociation f g k F G H a b c)
    (P : CochainComplex (SheafOfModules.{s} A) ℤ)
    (M : CochainComplex (SheafOfModules.{s} B) ℤ)
    (N : CochainComplex (SheafOfModules.{s} C) ℤ)
    (eM : M ≅ (F.mapHomologicalComplex (.up ℤ)).obj P)
    (eN : N ≅ (H.mapHomologicalComplex (.up ℤ)).obj P)
    (τ : M ⟶ ((SheafOfModules.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj N)
    (y : ∀ (i : ℤ) (U : Dᵒᵖ), (P.X i).val.obj U → (F.obj (P.X i)).val.obj U)
    (z : ∀ (i : ℤ) (U : Dᵒᵖ), (P.X i).val.obj U → (H.obj (P.X i)).val.obj U)
    (hy : ∀ i U x, (a.unit.app (P.X i)).val.app U x = y i U x)
    (hz : ∀ i U x, (c.unit.app (P.X i)).val.app U x = z i U x)
    (hτ : ∀ (i : ℤ) (U : Dᵒᵖ) (x : (P.X i).val.obj U),
      (τ.f i).val.app U ((eM.inv.f i).val.app U (y i U x)) =
        (eN.inv.f i).val.app U (z i U x)) :
    ∃ q : (G.mapHomologicalComplex (.up ℤ)).obj M ≅ N,
      (b.mapHomologicalComplex (.up ℤ)).unit.app M ≫
        ((SheafOfModules.restrictScalars g).mapHomologicalComplex (.up ℤ)).map q.hom = τ := by
  let q := (G.mapHomologicalComplex (.up ℤ)).mapIso eM ≪≫
    (NatIso.mapHomologicalComplex data.iso (.up ℤ)).app P ≪≫ eN.symm
  refine ⟨q, ?_⟩
  apply (cancel_epi eM.inv).mp
  apply HomologicalComplex.hom_ext
  intro i
  apply (a.homEquiv (P.X i) _).injective
  simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
    Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f]
  ext U x
  let z := (a.unit.app (P.X i)).val.app U x
  have he := congrArg (fun v ↦ (v.f i).val.app U z) eM.inv_hom_id
  change (eM.hom.f i).val.app U ((eM.inv.f i).val.app U z) = z at he
  have hn := congrArg (fun v ↦ (v.val.app U) ((eM.inv.f i).val.app U z))
    (b.unit.naturality (eM.hom.f i))
  change (b.unit.app (F.obj (P.X i))).val.app U
      ((eM.hom.f i).val.app U ((eM.inv.f i).val.app U z)) =
    (G.map (eM.hom.f i)).val.app U
      ((b.unit.app (M.X i)).val.app U ((eM.inv.f i).val.app U z)) at hn
  rw [he] at hn
  change (eN.inv.f i).val.app U
      ((data.iso.hom.app (P.X i)).val.app U
        ((G.map (eM.hom.f i)).val.app U
          ((b.unit.app (M.X i)).val.app U ((eM.inv.f i).val.app U z)))) =
    (τ.f i).val.app U ((eM.inv.f i).val.app U z)
  rw [← hn]
  change (eN.inv.f i).val.app U
      ((data.iso.hom.app (P.X i)).val.app U
        ((b.unit.app (F.obj (P.X i))).val.app U
          ((a.unit.app (P.X i)).val.app U x))) = _
  rw [data.unit]
  exact ((congrArg (fun v ↦ (τ.f i).val.app U ((eM.inv.f i).val.app U v))
    (hy i U x)).trans ((hτ i U x).trans
      (congrArg (fun v ↦ (eN.inv.f i).val.app U v) (hz i U x).symm))).symm

end GenericAssociationData

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

private def scalarRingMap (n : ℕ) :
    SheafOfModules.derivedChangeRingIndependentCoefficients
        (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      integralCoefficientSheaf l L W n :=
  (sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat RingCat)).map
    (X := completedIntegralCommRingSheafUnrestricted l E W)
    (Y := integralCoefficientCommRingSheaf l L W n) (integralScalarRho l E L ι W n)

private abbrev scalarRes (n : ℕ) :=
  SheafOfModules.restrictScalars.{max u (t + 1)}
    (scalarRingMap l E L ι W n)

private def scalarAdjunction (n : ℕ) :
    integralScalarReduction l E L ι W n ⊣
      scalarRes l E L ι W n :=
  let : (integralScalarReduction l E L ι W n).Additive :=
    integralScalarReduction_additive l E L ι W n
  ((SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralScalarRho l E L ι W n)).choose_spec.choose_spec
      (integralScalarReduction l E L ι W n)
      (integralScalarReduction_obj l E L ι W n)
      (fun f ↦ integralScalarReduction_map l E L ι W n f)).choose

private theorem scalarAdjunction_unit (n : ℕ)
    (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((scalarAdjunction l E L ι W n).unit.app M).val.app U x =
      integralScalarTensorSection l E L ι W n M U 1 x := by
  let : (integralScalarReduction l E L ι W n).Additive :=
    integralScalarReduction_additive l E L ι W n
  have ht := ((SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralScalarRho l E L ι W n)).choose_spec.choose_spec
      (integralScalarReduction l E L ι W n)
      (integralScalarReduction_obj l E L ι W n)
      (fun f ↦ integralScalarReduction_map l E L ι W n f)).choose_spec M
        ((integralScalarReduction l E L ι W n).obj M)
        (eqToHom (integralScalarReduction_obj l E L ι W n M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at ht
  have he : (integralScalarReductionIso l E L ι W n).inv.app M =
      eqToHom (integralScalarReduction_obj l E L ι W n M).symm := by
    dsimp only [integralScalarReductionIso, eqToIso.inv]
    rw [eqToHom_app]
  unfold integralScalarTensorSection
  rw [he]
  exact ht

private theorem quotient_refl (n : ℕ) :
    coefficientFiniteQuotient l L W (Nat.le_refl n) = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply (forget₂ CommRingCat RingCat).map_injective
  change (normalizedDVRQuotient l L W (Nat.le_refl n)).hom.app U = 𝟙 _
  exact congrArg (fun f ↦ f.hom.app U)
    ((integralCoefficientSheafSystem l L W).map_id (op n))

private theorem quotient_comp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    coefficientFiniteQuotient l L W hrm ≫ coefficientFiniteQuotient l L W hmn =
      coefficientFiniteQuotient l L W (hmn.trans hrm) := by
  have he := (integralCoefficientSheafSystem l L W).map_comp
    (homOfLE hrm).op (homOfLE hmn).op
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply (forget₂ CommRingCat RingCat).map_injective
  exact (congrArg (fun f ↦ f.hom.app U) he).symm

private theorem quotient_succ (n : ℕ) :
    coefficientFiniteQuotient l L W (Nat.le_succ n) =
      unrestrictedCoefficientStep l L W n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply (forget₂ CommRingCat RingCat).map_injective
  change (normalizedDVRQuotient l L W (Nat.le_succ n)).hom.app U = _
  simp only [normalizedDVRQuotient, integralCoefficientSheafSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private theorem rho_comp {m n : ℕ} (h : n ≤ m) :
    integralScalarRho l E L ι W m ≫ coefficientFiniteQuotient l L W h =
      integralScalarRho l E L ι W n := by
  induction m, h using Nat.le_induction with
  | base => rw [quotient_refl, Category.comp_id]
  | succ m h ih =>
    rw [← quotient_comp l L W (Nat.le_succ m) h, ← Category.assoc,
      quotient_succ, integralScalarRho_transition, ih]

attribute [local irreducible] scalarAdjunction

private theorem transitionAb_id (M : coefficientSequenceModules l L W)
    (n : ℕ) (U : W.ProEtᵒᵖ) :
    transitionAb l L W M (Nat.le_refl n) U = 𝟙 _ := by
  have hf := transitionAb_fac l L W M (Nat.le_refl n) U
  have hid : (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op =
      𝟙 (op (n, U.unop)) := rfl
  rw [hid, CategoryTheory.Functor.map_id] at hf
  apply (cancel_epi (eqToHom (coefficientSequenceEvaluationAb_eq l L W M n U).symm)).mp
  apply (cancel_mono (eqToHom (coefficientSequenceEvaluationAb_eq l L W M n U))).mp
  simpa only [Category.assoc, Category.id_comp, Category.comp_id,
    eqToHom_trans, eqToHom_refl] using hf

private theorem transition_units
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (X : CochainComplex (coefficientSequenceModules l L W) ℤ)
    (e : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj X ≅
        ((integralScalarReduction l E L ι W n).mapHomologicalComplex (.up ℤ)).obj P)
    (ht : ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
      (x : (((coefficientSequenceEvaluation l L W (n + 1)).obj (X.X i)).val.obj U)),
      HEq ((((coefficientSequenceTransition l L W (Nat.le_succ n)).app
          (X.X i)).val.app U).hom x)
        (((((e n).inv).f i).val.app U).hom
          ((((integralScalarTransition l E L ι W n).app P).f i).val.app U
            ((((e (n + 1)).hom).f i).val.app U x))))
    {m n : ℕ} (h : n ≤ m) (i : ℤ) (U : W.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) :
    transitionAb l L W (X.X i) h U
        ((((e m).inv).f i).val.app U
          (integralScalarTensorSection l E L ι W m (P.X i) U 1 x)) =
      (((e n).inv).f i).val.app U
        (integralScalarTensorSection l E L ι W n (P.X i) U 1 x) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [transitionAb_id]
    rfl
  | succ m h ih =>
    have he := congrArg (fun f ↦ (f.f i).val.app U
      (integralScalarTensorSection l E L ι W (m + 1) (P.X i) U 1 x))
        (e (m + 1)).inv_hom_id
    change (((e (m + 1)).hom).f i).val.app U
      ((((e (m + 1)).inv).f i).val.app U _) = _ at he
    have hs := eq_of_heq (ht m i U
      ((((e (m + 1)).inv).f i).val.app U
        (integralScalarTensorSection l E L ι W (m + 1) (P.X i) U 1 x)))
    change transitionAb l L W (X.X i) (Nat.le_succ m) U _ = _ at hs
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at he
    rw [he] at hs
    have hτ := (integralScalarTransition_existsUnique l E L ι W m).exists.choose_spec
      P i U 1 x
    change (((integralScalarTransition l E L ι W m).app P).f i).val.app U
      (integralScalarTensorSection l E L ι W (m + 1) (P.X i) U 1 x) = _ at hτ
    simp only [map_one] at hτ
    rw [hτ] at hs
    rw [transitionAb_comp l L W (X.X i) (Nat.le_succ m) h]
    change transitionAb l L W (X.X i) h U
      (transitionAb l L W (X.X i) (Nat.le_succ m) U _) = _
    rw [hs]
    exact ih

private theorem quotient_forget {m n : ℕ} (h : n ≤ m) :
    (sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat RingCat)).map
      (coefficientFiniteQuotient l L W h) = normalizedDVRQuotient l L W h := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

private instance scalarAdditive (n : ℕ) :
    (integralScalarReduction l E L ι W n).Additive :=
  integralScalarReduction_additive l E L ι W n

private theorem scalarRingTriangle {m n : ℕ} (h : n ≤ m) :
    scalarRingMap l E L ι W m ≫ normalizedDVRQuotient l L W h =
      scalarRingMap l E L ι W n := by
  have hh := congrArg
    ((sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat RingCat)).map)
    (rho_comp l E L ι W h)
  simpa only [scalarRingMap, CategoryTheory.Functor.map_comp, quotient_forget] using hh

attribute [local irreducible] scalarRingMap

private def scalarAssociationData {m n : ℕ} (h : n ≤ m)
    (adj : coefficientFiniteQuotientExtension l L W h ⊣ normalizedDVRModuleRes l L W h) :=
  associationWithUnit (scalarRingMap l E L ι W m) (normalizedDVRQuotient l L W h)
    (scalarRingMap l E L ι W n) (scalarRingTriangle l E L ι W h)
    (integralScalarReduction l E L ι W m) (coefficientFiniteQuotientExtension l L W h)
    (integralScalarReduction l E L ι W n)
    (scalarAdjunction l E L ι W m) adj (scalarAdjunction l E L ι W n)

attribute [local irreducible] scalarAssociationData

/-- Ordinary scalar association transposes to the actual strict transition.

Source: Stacks Tags 03D7, 03D8, and 03EK; ordinary parts of steps 1--2 of
stage3-pur-extension-strict-tensor-normalized
(blueprint: stage3-pur-extension-ordinary-quotient-iso).

Proof: the completed coefficient map to level m followed by the quotient to n is
its level-n map. This follows by induction from the successor formula and the
functoriality of the actual quotient maps. Restriction along these maps therefore
composes canonically. Compose the ordinary level-m scalar adjunction with the
supplied quotient adjunction and use uniqueness of left adjoints to obtain the
scalar associator. Its unit equation identifies the image of the level-m unit
under the quotient unit and associator with the level-n unit.

For successors, the given transition compatibility, the tensor formula, and the
inverse evaluation isomorphism identify the actual transition on 1 tensor x.
The actual sequence identity and composition equations extend this to all n ≤ m.
Map the associator to complexes and conjugate by the evaluation isomorphisms.
Precompose the desired equation by the inverse level-m evaluation isomorphism
and apply the injective level-m adjunction Hom equivalence in each degree.
Naturality of the quotient unit and the associator unit equation reduce its
left side to the inverse level-n evaluation of 1 tensor x; the transition
calculation gives its right side. Since the associator uses the supplied
adjunction, its extra normalization hypothesis hunit is unnecessary here.
No boundedness, flatness, or ramification condition is used. -/
theorem coefficientExtensionOrdinaryQuotientIso
    {m n : ℕ} (h : n ≤ m)
    (adj : coefficientFiniteQuotientExtension l L W h ⊣ normalizedDVRModuleRes l L W h)
    (hunit : ∀ (M : normalizedDVRModules l L W m) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      coefficientRestrictionSection (normalizedDVRQuotient l L W h)
        ((coefficientFiniteQuotientExtension l L W h).obj M) U
        (((adj.unit.app M).val.app U) x) = coefficientFiniteQuotientUnitSection l L W h M U x)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (X : CochainComplex (coefficientSequenceModules l L W) ℤ)
    (e : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj X ≅
        (integralScalarFiniteComplex l E L ι W n).obj P)
    (htransition : ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
      (x : (((coefficientSequenceEvaluation l L W (n + 1)).obj (X.X i)).val.obj U)),
      HEq ((((coefficientSequenceTransition l L W (Nat.le_succ n)).app
          (X.X i)).val.app U).hom x)
        (((((e n).inv).f i).val.app U).hom
          ((((integralScalarTransition l E L ι W n).app P).f i).val.app U
            ((((e (n + 1)).hom).f i).val.app U x))))
    : ∃ a : ((coefficientFiniteQuotientExtension l L W h).mapHomologicalComplex
          (.up ℤ)).obj
        (((coefficientSequenceEvaluation l L W m).mapHomologicalComplex (.up ℤ)).obj X) ≅
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj X,
      (adj.mapHomologicalComplex (.up ℤ)).unit.app
          (((coefficientSequenceEvaluation l L W m).mapHomologicalComplex (.up ℤ)).obj X) ≫
        ((normalizedDVRModuleRes l L W h).mapHomologicalComplex (.up ℤ)).map a.hom =
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l L W h)
        (.up ℤ)).app X := by
  classical
  have _hunit := hunit
  exact (scalarAssociationData l E L ι W h adj).complex_iso P _ _ (e m) (e n)
    ((NatTrans.mapHomologicalComplex (coefficientSequenceTransition l L W h)
      (.up ℤ)).app X)
    (fun i U x ↦ integralScalarTensorSection l E L ι W m (P.X i) U 1 x)
    (fun i U x ↦ integralScalarTensorSection l E L ι W n (P.X i) U 1 x)
    (fun i U x ↦ scalarAdjunction_unit l E L ι W m (P.X i) U x)
    (fun i U x ↦ scalarAdjunction_unit l E L ι W n (P.X i) U x)
    (transition_units l E L ι W P X e htransition h)

end WeilConjectures
