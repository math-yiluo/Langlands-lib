/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExactIntrinsic
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

import WeilConjectures.SmoothPurity.Sf.SfRationalScalarExactOfIntegral
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Scalar.ScalarShiftNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SmoothPurity.Rational.RationalAssociatorShiftCompat

/-! Intrinsic finite coefficient stages and their scalar coherence.
This file contains the finite-stage part of SfAlgebraicallyClosedCoefficients,
separated so its compilation is independent of the pair-category construction
(blueprint: lem-pur-intrinsic-coefficient-stage-shift-coherence).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace WeilConjectures
namespace SfAlgebraicallyClosedCoefficients

section
attribute [local irreducible] sfRationalTriangulationDatum sfRationalScalarExtension

open TensorProduct

private theorem normalized_compatibility
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (I : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [I.CommShift ℤ] [H.CommShift ℤ] (e : F ⋙ I ≅ H)
    (hc : ∀ (n : ℤ) (X : C), HEq (I.map ((F.commShiftIso n).hom.app X) ≫
        (I.commShiftIso n).hom.app (F.obj X))
      (e.hom.app ((shiftFunctor C n).obj X) ≫ (H.commShiftIso n).hom.app X ≫
        (shiftFunctor E n).map (e.inv.app X))) :
    NatTrans.CommShift e.hom ℤ := by
  apply NatTrans.CommShift.of_core
  intro n
  constructor
  ext X
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [Functor.commShiftIso_comp_hom_app, eq_of_heq (hc n X)]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simp only [Functor.comp_obj, CategoryTheory.Category.comp_id]

private theorem integer_commShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

end

private theorem normalized_shift_existsUnique
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (I : D ⥤ E) [I.Full] [I.Faithful] [I.CommShift ℤ]
    (H : C ⥤ E) [H.CommShift ℤ] (e : F ⋙ I ≅ H) :
    ∃! c : F.CommShift ℤ, ∀ n X,
      HEq (I.map ((Functor.commShiftIso F (self := c) n).hom.app X) ≫
        (I.commShiftIso n).hom.app (F.obj X))
        (e.hom.app ((shiftFunctor C n).obj X) ≫ (H.commShiftIso n).hom.app X ≫
          (shiftFunctor E n).map (e.inv.app X)) := by
  let c : F.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  have hc (n : ℤ) (X : C) :
      HEq (I.map ((Functor.commShiftIso F (self := c) n).hom.app X) ≫
        (I.commShiftIso n).hom.app (F.obj X))
        (e.hom.app ((shiftFunctor C n).obj X) ≫ (H.commShiftIso n).hom.app X ≫
          (shiftFunctor E n).map (e.inv.app X)) := by
    change HEq (I.map ((Functor.CommShift.OfComp.iso e n).hom.app X) ≫
      (I.commShiftIso n).hom.app (F.obj X)) _
    simp [Category.assoc]
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply integer_commShift_ext
  intro n
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app (F.obj X))).mp
  exact eq_of_heq ((hc' n X).trans (hc n X).symm)

section ScalarShiftCoherence

attribute [local irreducible] ScalarLocalization.composition
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar
  sfIntegralOrdinaryComparison sfIntegralScalarComp sfRationalScalarComp
  sfRationalTriangulationDatum sfRationalScalarExtension

open TensorProduct

private theorem normalized_comparison_commShift
    {C D A : Type*} [Category C] [Category D] [Category A]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift A ℤ]
    (F : C ⥤ D) (I : D ⥤ A) (H : C ⥤ A)
    [F.CommShift ℤ] [I.CommShift ℤ] [H.CommShift ℤ]
    (e : H ≅ F ⋙ I)
    (h : ∀ (n : ℤ) (X : C),
      I.map ((F.commShiftIso n).hom.app X) ≫
          (I.commShiftIso n).hom.app (F.obj X) =
        e.inv.app (X⟦n⟧) ≫ (H.commShiftIso n).hom.app X ≫
          (shiftFunctor A n).map (e.hom.app X)) :
    NatTrans.CommShift e.hom ℤ := by
  constructor
  intro n
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app]
  have hh := congrArg (fun f ↦ e.hom.app (X⟦n⟧) ≫ f) (h n X)
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hh.symm

section Integral

variable (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

@[instance_reducible]
private noncomputable def normalizedIntegralShift :
    (sfConstructibleIntegralScalarExtension p l hl E L i Y).CommShift ℤ :=
  (normalized_shift_existsUnique
    (sfConstructibleIntegralScalarExtension p l hl E L i Y)
    (sfIntegralConstructible l L Y).ι
    ((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L i Y)
    (sfIntegralOrdinaryComparison l E L i Y).symm).exists.choose

attribute [local instance] normalizedIntegralShift

private noncomputable def normalizedComparison :
    (sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L i Y ≅
      sfConstructibleIntegralScalarExtension p l hl E L i Y ⋙ (sfIntegralConstructible l L Y).ι :=
  sfIntegralOrdinaryComparison l E L i Y

attribute [local irreducible] normalizedComparison

private theorem integral_comparison_commShift :
    NatTrans.CommShift (normalizedComparison p l hl E L i Y).hom ℤ := by
  apply normalized_comparison_commShift
    (sfConstructibleIntegralScalarExtension p l hl E L i Y)
    (sfIntegralConstructible l L Y).ι
    ((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L i Y)
    (normalizedComparison p l hl E L i Y)
  intro n K
  simp only [normalizedComparison, ObjectProperty.ι_map, ObjectProperty.ι_obj]
  exact eq_of_heq ((normalized_shift_existsUnique
    (sfConstructibleIntegralScalarExtension p l hl E L i Y)
    (sfIntegralConstructible l L Y).ι
    ((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L i Y)
    (sfIntegralOrdinaryComparison l E L i Y).symm).exists.choose_spec n K)

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

private theorem ordinary_comp_commShift :
    NatTrans.CommShift (integralOrdinaryDerivedScalarComp l E L i Y M j).hom ℤ := by
  have := Functor.commShift_mapDerivedCategoryCompIso_hom
    (integralOrdinaryScalar l E L i Y) (integralOrdinaryScalar l L M j Y)
  have := Functor.commShift_mapDerivedCategoryNatIso_hom
    (integralOrdinaryScalarComp l E L i Y M j)
  change NatTrans.CommShift
    ((Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L i Y)
      (integralOrdinaryScalar l L M j Y)).hom ≫
      (Functor.mapDerivedCategoryNatIso (integralOrdinaryScalarComp l E L i Y M j)).hom) ℤ
  infer_instance

private theorem integral_comp_commShift :
    NatTrans.CommShift (sfIntegralScalarComp l E L i Y p hl M j).hom ℤ := by
  have := integral_comparison_commShift p l hl E L i Y
  have := integral_comparison_commShift p l hl L M j Y
  have := integral_comparison_commShift p l hl E M (j.comp i) Y
  have := ordinary_comp_commShift l E L i Y M j
  have he : Functor.whiskerRight
      (sfIntegralScalarComp l E L i Y p hl M j).hom
      (sfIntegralConstructible l M Y).ι =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (normalizedComparison p l hl L M j Y).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (normalizedComparison p l hl E L i Y).inv
          (integralOrdinaryDerivedScalar l L M j Y) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (integralOrdinaryDerivedScalarComp l E L i Y M j).hom ≫
        (normalizedComparison p l hl E M (j.comp i) Y).hom := by
    ext K
    simp only [sfIntegralScalarComp, normalizedComparison, ObjectProperty.ι_map,
      ObjectProperty.ι_obj, Functor.comp_obj, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    exact (sfIntegralScalarComp_existsUnique l E L i Y p hl M j).exists.choose_spec K
  have : NatTrans.CommShift (Functor.whiskerRight
      (sfIntegralScalarComp l E L i Y p hl M j).hom
      (sfIntegralConstructible l M Y).ι) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ (sfIntegralConstructible l M Y).ι

private theorem integral_corrected_comp_commShift
    (q : E →ₐ[Padic l] M) (hq : j.comp i = q) :
    NatTrans.CommShift
      (sfIntegralScalarComp l E L i Y p hl M j ≪≫
        eqToIso (congrArg
          (fun f ↦ sfConstructibleIntegralScalarExtension p l hl E M f Y) hq)).hom ℤ := by
  subst q
  simpa only [eqToIso_refl, Iso.trans_refl] using integral_comp_commShift p l hl E L i Y M j

end Integral

end ScalarShiftCoherence

private noncomputable def correctedAssociator
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (ι : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : E →ₐ[Padic l] M)
    (h : j.comp ι = k) (Y : AlgebraicGeometry.Scheme.{u}) :
    sfRationalScalarExtension l E Y p hl L ι ⋙
        sfRationalScalarExtension l L Y p hl M j ≅
      sfRationalScalarExtension l E Y p hl M k :=
  sfRationalScalarComp l E L ι Y p hl M j ≪≫
    eqToIso (congrArg
      (sfRationalScalarExtension l E Y p hl M) h)

attribute [local irreducible] correctedAssociator

private theorem correctedAssociator_pentagon
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (Y : AlgebraicGeometry.Scheme.{u})
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : M →ₐ[Padic l] N)
    (ij : E →ₐ[Padic l] M) (jk : L →ₐ[Padic l] N) (ijk : E →ₐ[Padic l] N)
    (hij : j.comp i = ij) (hjk : k.comp j = jk)
    (hijk : k.comp ij = ijk) (hijk' : jk.comp i = ijk)
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l M Y p hl N k).map
        ((correctedAssociator p l hl E L M i j ij hij Y).hom.app K) ≫
        (correctedAssociator p l hl E M N ij k ijk hijk Y).hom.app K =
      (correctedAssociator p l hl L M N j k jk hjk Y).hom.app
          ((sfRationalScalarExtension l E Y p hl L i).obj K) ≫
        (correctedAssociator p l hl E L N i jk ijk hijk' Y).hom.app K := by
  subst ij
  subst jk
  subst ijk
  have hcast : (eqToIso (congrArg
      (sfRationalScalarExtension l E Y p hl N)
      hijk')).hom.app K = 𝟙 _ := by
    rfl
  unfold correctedAssociator
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [hcast]
  simp only [eqToIso.hom, eqToHom_refl, NatTrans.id_app,
    Category.comp_id]
  have hp := (sfRationalScalar_coherence l E L i Y p hl M j).2.2 N k K
  exact hp.trans (congrArg
    (fun f ↦ (sfRationalScalarComp l L M j Y p hl N k).hom.app
        ((sfRationalScalarExtension l E Y p hl L i).obj K) ≫ f)
    (Category.comp_id ((sfRationalScalarComp l E L i Y p hl N (k.comp j)).hom.app K))).symm

private theorem correctedAssociator_pentagon_nat
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (Y : AlgebraicGeometry.Scheme.{u})
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : M →ₐ[Padic l] N)
    (ij : E →ₐ[Padic l] M) (jk : L →ₐ[Padic l] N) (ijk : E →ₐ[Padic l] N)
    (hij : j.comp i = ij) (hjk : k.comp j = jk)
    (hijk : k.comp ij = ijk) (hijk' : jk.comp i = ijk)
    :
    Functor.whiskerRight (correctedAssociator p l hl E L M i j ij hij Y).hom
        (sfRationalScalarExtension l M Y p hl N k) ≫
        (correctedAssociator p l hl E M N ij k ijk hijk Y).hom =
      (Functor.associator
        (sfRationalScalarExtension l E Y p hl L i)
        (sfRationalScalarExtension l L Y p hl M j)
        (sfRationalScalarExtension l M Y p hl N k)).hom ≫
      Functor.whiskerLeft
        (sfRationalScalarExtension l E Y p hl L i)
        (correctedAssociator p l hl L M N j k jk hjk Y).hom ≫
      (correctedAssociator p l hl E L N i jk ijk hijk' Y).hom := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
    correctedAssociator_pentagon p l hl E L M N Y i j k ij jk ijk hij hjk hijk hijk' K

attribute [local irreducible] ScalarLocalization.category sfRationalTriangulationDatum
  sfRationalScalarExtension sfRationalScalarComp sfRationalScalarUnit
  sfIntegralScalarComp sfIntegralScalarUnit sfIntegralOrdinaryComparison
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

-- Match the transported field and module structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The specified raw rational stage, using its equivalent small coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def Stage (E : Index l Ω) :=
  D.sfRationalCategory l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage D l hl Ω Y E) :=
  ScalarLocalization.category (Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E))
    (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω E))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stagePreadditive (E : Index l Ω) :
    Preadditive (Stage D l hl Ω Y E) :=
  inferInstanceAs (Preadditive
    (D.sfRationalCategory l hl (Coefficient.{u} l Ω E) Y))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageZero (E : Index l Ω) :
    HasZeroObject (Stage D l hl Ω Y E) :=
  sfRationalConstructibleZero l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShift (E : Index l Ω) :
    HasShift (Stage D l hl Ω Y E) ℤ :=
  sfRationalConstructibleShift l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShiftAdditive (E : Index l Ω) (n : ℤ) :
    (shiftFunctor (Stage D l hl Ω Y E) n).Additive :=
  sfRationalConstructibleShiftAdditive l (Coefficient.{u} l Ω E) Y n

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stagePretriangulated (E : Index l Ω) :
    Pretriangulated (Stage D l hl Ω Y E) :=
  sfRationalConstructiblePretriangulated l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTriangulated (E : Index l Ω) :
    IsTriangulated (Stage D l hl Ω Y E) :=
  sfRationalConstructibleTriangulated l (Coefficient.{u} l Ω E) Y

/-- The actual finite-field scalar transition, with both coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transition (E L : Index l Ω) (h : E ≤ L) :
    Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L :=
  sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y D.p hl
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- The integral transition inherits the ordinary tensor shift through its canonical
quotient-completion comparison, not through an arbitrary exact-functor witness.
Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: conjugate the ordinary derived tensor shift by sfIntegralOrdinaryComparison.
The full intrinsic subcategory inherits the ambient shift. The inclusion's shift
comparisons identify its shifted objects with ambient shifts on both sides. Full
faithfulness lifts each component and its inverse. Naturality, the zero equation and
the addition equation follow from the ordinary ones by cancellation of the comparisons.
The formula fixes all components,
so extensionality of natural isomorphisms and proof irrelevance prove uniqueness. -/
theorem integralTransitionCommShift_existsUnique (E L : Index l Ω) (h : E ≤ L) :
    ∃! c : (sfConstructibleIntegralScalarExtension D.p l hl
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) Y).CommShift ℤ,
      (fun [commInst : (sfConstructibleIntegralScalarExtension D.p l hl
          (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) Y).CommShift ℤ] ↦
        ∀ (n : ℤ) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
          HEq ((((sfConstructibleIntegralScalarExtension D.p l hl
            (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y).commShiftIso n).hom.app K).hom ≫
              ((sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι.commShiftIso n).hom.app
                ((sfConstructibleIntegralScalarExtension D.p l hl
                  (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
                  (coefficientInclusion l Ω E L h) Y).obj K))
            ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E)
                (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).inv.app
                  ((shiftFunctor (sfIntegralConstructibleCategory l
                    (Coefficient.{u} l Ω E) Y) n).obj K) ≫
              (Functor.commShiftIso
                ((sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙
                  integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E)
                    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y) n).hom.app K ≫
              (shiftFunctor (DerivedCategory (scalarReductionSource.{u, u} l
                (Coefficient.{u} l Ω L) Y)) n).map
                  ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E)
                    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).hom.app K)))
        (commInst := c) := by
  exact normalized_shift_existsUnique
    (sfConstructibleIntegralScalarExtension D.p l hl
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y)
    (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι
    ((sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙
      integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y)
    (sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).symm

/-- The fixed ordinary-to-completed normalization of the integral transition shift.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance integralTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (sfConstructibleIntegralScalarExtension D.p l hl
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) Y).CommShift ℤ :=
  (integralTransitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose

set_option linter.unusedVariables false in
/-- The rational transition shift is uniquely fixed by localizing the normalized integral
shift. Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: tensor the integral components and inverses with one. On pure tensors, integral
naturality gives rational naturality; generation gives it on every Hom. The recorded
rational shift and localization comparison are normalized to the integral shift and
identity at one. Thus the displayed HEq gives the shift-by-one comparison. Iteration and
inverse shifts give all integer comparisons and their coherence. A coherent integer-shift
comparison is determined at one, which also proves uniqueness. -/
theorem transitionCommShift_existsUnique (E L : Index l Ω) (h : E ≤ L) :
    ∃! c : (transition D l hl Ω Y E L h).CommShift ℤ,
      (fun [commInst : (transition D l hl Ω Y E L h).CommShift ℤ] ↦
        ∀ K : Stage D l hl Ω Y E,
          HEq (((transition D l hl Ω Y E L h).commShiftIso (1 : ℤ)).hom.app K)
            ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
              (((sfConstructibleIntegralScalarExtension D.p l hl
                (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
                (coefficientInclusion l Ω E L h) Y).commShiftIso (1 : ℤ)).hom.app K.obj)))
        (commInst := c) := by
  dsimp only [transition]
  exact sfRationalScalarCommShift_existsUnique D.p l hl
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y

/-- The canonical, integral-image-normalized shift comparison of the rational transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).CommShift ℤ :=
  (transitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose

section

/-- Exactness for the normalized shift comparison on the recorded intrinsic rational stages.
Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: use the exactness argument of sfScalarExtension_exact_triangulated: the Roos cone
shift is conjugate through the quotient-completion comparison to the ordinary tensor
shift. Full intrinsic subcategories inherit distinguished triangles, and rationalization
has precisely the isomorphic integral image triangles. The preceding normalization is
that same comparison, so the finite scalar transition preserves distinguished triangles
including their connecting arrows. -/
@[instance]
theorem transitionExact (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).IsTriangulated := by
  let : ∀ n : ℤ, (shiftFunctor
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) n).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) Y) n).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y) n).Additive :=
    fun n ↦ sfRationalConstructibleShiftAdditive l (Coefficient.{u} l Ω E) Y n
  let : ∀ n : ℤ, (shiftFunctor
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) Y) n).Additive :=
    fun n ↦ sfRationalConstructibleShiftAdditive l (Coefficient.{u} l Ω L) Y n
  let T := sfConstructibleIntegralScalarExtension D.p l hl
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y
  let : T.CommShift ℤ := integralTransitionCommShift D l hl Ω Y E L h
  let I := (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι
  let H := (sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙
    integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y
  let e : T ⋙ I ≅ H := (sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).symm
  have : NatTrans.CommShift e.hom ℤ := normalized_compatibility T I H e
    (integralTransitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose_spec
  have hI : I.IsTriangulated := by
    change (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι.IsTriangulated
    infer_instance
  have hH : H.IsTriangulated := by
    dsimp only [H]
    infer_instance
  have hT : T.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right (F := T) (G := I) (H := H) e).2
      hH
  let : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y D.p hl
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)).CommShift ℤ :=
    transitionCommShift D l hl Ω Y E L h
  exact sfRationalScalarExactOfIntegral D.p l hl
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y
    (t := integralTransitionCommShift D l hl Ω Y E L h)
    (ht := hT) (s := transitionCommShift D l hl Ω Y E L h)
    (transitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose_spec

end

/-- Additivity of the published intrinsic rational scalar-extension functor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionAdditive (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).Additive :=
  sfRationalScalarExtension_additive l (Coefficient.{u} l Ω E) Y D.p hl
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The canonical scalar associator, with its tensor-generator normalization.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition D l hl Ω Y E L h ⋙ transition D l hl Ω Y L M k ≅
      transition D l hl Ω Y E M (h.trans k) :=
  sfRationalScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y D.p hl (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω L M k) ≪≫
    eqToIso (congrArg (sfRationalScalarExtension l
      (Coefficient.{u} l Ω E) Y D.p hl (Coefficient.{u} l Ω M))
      ((coefficientInclusion_laws l Ω).2 E L M h k))

/-- The normalized scalar unit, transported through the coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def unitor (E : Index l Ω) : transition D l hl Ω Y E E le_rfl ≅
    𝟭 (Stage D l hl Ω Y E) :=
  eqToIso (congrArg (sfRationalScalarExtension l
    (Coefficient.{u} l Ω E) Y D.p hl (Coefficient.{u} l Ω E))
    ((coefficientInclusion_laws l Ω).1 E)) ≪≫
    sfRationalScalarUnit l (Coefficient.{u} l Ω E) Y D.p hl

private theorem associator_eq_corrected (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    associator D l hl Ω Y E L M h k =
      correctedAssociator D.p l hl
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
        (coefficientInclusion l Ω E L h) (coefficientInclusion l Ω L M k)
        (coefficientInclusion l Ω E M (h.trans k))
        ((coefficientInclusion_laws l Ω).2 E L M h k) Y := by
  unfold associator correctedAssociator
  rfl

/-- The prescribed finite-stage scalar associator commutes with its normalized shifts.
Source: the integral/rational normalization step in the common-stage shift argument
(blueprint: lem-pur-intrinsic-coefficient-stage-shift-coherence).
Proof: the ordinary derived tensor compositor commutes with shifts. The defining
comparison equations reflect this square through the fully faithful intrinsic
integral inclusions, with equality induction for the composite coefficient map.
Apply the rational localization square to the supplied degree-one normalizations.
Equality of the whole corrected associators transports that square to the prescribed
small coefficient models; no component conversion at a Shrink model is needed. -/
theorem associator_commShift (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    NatTrans.CommShift (associator D l hl Ω Y E L M h k).hom ℤ := by
  let α := sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y D.p hl
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
      eqToIso (congrArg
        (fun i ↦ sfConstructibleIntegralScalarExtension D.p l hl (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω M) i Y)
        ((coefficientInclusion_laws l Ω).2 E L M h k))
  have : NatTrans.CommShift α.hom ℤ :=
    integral_corrected_comp_commShift D.p l hl (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) Y (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
      ((coefficientInclusion_laws l Ω).2 E L M h k)
  have hc := rational_corrected_comp_commShift D.p l hl
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω E L h) (coefficientInclusion l Ω L M k)
    (coefficientInclusion l Ω E M (h.trans k))
    ((coefficientInclusion_laws l Ω).2 E L M h k) Y
    (sE := stageShift D l hl Ω Y E) (sL := stageShift D l hl Ω Y L)
    (sM := stageShift D l hl Ω Y M)
    (tE := integralTransitionCommShift D l hl Ω Y E L h)
    (tL := integralTransitionCommShift D l hl Ω Y L M k)
    (tM := integralTransitionCommShift D l hl Ω Y E M (h.trans k))
    (cE := transitionCommShift D l hl Ω Y E L h)
    (cL := transitionCommShift D l hl Ω Y L M k)
    (cM := transitionCommShift D l hl Ω Y E M (h.trans k))
    (show NatTrans.CommShift α.hom ℤ from this)
    (sfRationalTriangulationDatum l (Coefficient.{u} l Ω E) Y).choose_spec.choose_spec.1
    (sfRationalTriangulationDatum l (Coefficient.{u} l Ω L) Y).choose_spec.choose_spec.1
    (sfRationalTriangulationDatum l (Coefficient.{u} l Ω M) Y).choose_spec.choose_spec.1
    (transitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose_spec
    (transitionCommShift_existsUnique D l hl Ω Y L M k).exists.choose_spec
    (transitionCommShift_existsUnique D l hl Ω Y E M (h.trans k)).exists.choose_spec
  rw [associator_eq_corrected D l hl Ω Y E L M h k]
  unfold correctedAssociator transition Stage stageCategory at *
  exact hc

attribute [local irreducible] transition associator unitor
  stagePreadditive stageShift stagePretriangulated

section

attribute [local irreducible] stageCategory

-- Compare whole natural transformations before taking components. This keeps the
-- proof-irrelevant inclusion witnesses out of large functor-object conversions.
private theorem associator_pentagon
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) :
    Functor.whiskerRight (associator D l hl Ω Y E L M h k).hom (transition D l hl Ω Y M N m) ≫
        (associator D l hl Ω Y E M N (h.trans k) m).hom =
      (Functor.associator (transition D l hl Ω Y E L h) (transition D l hl Ω Y L M k)
        (transition D l hl Ω Y M N m)).hom ≫
      Functor.whiskerLeft (transition D l hl Ω Y E L h) (associator D l hl Ω Y L M N k m).hom ≫
        (associator D l hl Ω Y E L N h (k.trans m)).hom := by
  have hp := correctedAssociator_pentagon_nat D.p l hl
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (Coefficient.{u} l Ω M) (Coefficient.{u} l Ω N) Y
      (coefficientInclusion l Ω E L h) (coefficientInclusion l Ω L M k)
      (coefficientInclusion l Ω M N m) (coefficientInclusion l Ω E M (h.trans k))
      (coefficientInclusion l Ω L N (k.trans m))
      (coefficientInclusion l Ω E N ((h.trans k).trans m))
      ((coefficientInclusion_laws l Ω).2 E L M h k)
      ((coefficientInclusion_laws l Ω).2 L M N k m)
      ((coefficientInclusion_laws l Ω).2 E M N (h.trans k) m)
      ((coefficientInclusion_laws l Ω).2 E L N h (k.trans m))
  unfold associator transition Stage stageCategory
  unfold correctedAssociator at hp
  exact hp

/-- The normalized tensor associators satisfy the stage-system cocycle.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: sfRationalScalar_coherence proves the tensor pentagon. The small
coefficient inclusions compose by coefficientInclusion_laws. Substitution gives the
displayed cocycle, including repeated fields and identity inclusions. -/
theorem associator_cocycle
    (D : WeilConjectures.FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) (K : SfAlgebraicallyClosedCoefficients.Stage D l hl Ω Y E) :
    (SfAlgebraicallyClosedCoefficients.transition D l hl Ω Y M N m).map
        ((SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E L M h k).hom.app K) ≫
        (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E M N (h.trans k) m).hom.app K =
      (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y L M N k m).hom.app
          ((SfAlgebraicallyClosedCoefficients.transition D l hl Ω Y E L h).obj K) ≫
        (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E L N h (k.trans m)).hom.app K :=
            by
  have hc := NatTrans.congr_app (associator_pentagon D l hl Ω Y E L M N h k m) K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using hc

end

end SfAlgebraicallyClosedCoefficients
end WeilConjectures
