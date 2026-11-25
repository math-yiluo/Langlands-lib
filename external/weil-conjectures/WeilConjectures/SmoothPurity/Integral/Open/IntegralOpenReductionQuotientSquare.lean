/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SmoothPurity.Integral.Open.IntegralOpenTensorQuotientModel
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The consecutive quotient square for normalized open reduction

Source: Stacks Tags 0E8I, 0GL1, 06YY and 0941; the strict-model normalization in
`lem-sf-integral-open-reduction-comparison`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X V : Scheme.{t}} (j : X ⟶ V) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

private theorem square_of_iso
    {C A B D E : Type*} [Category* C] [Category* A] [Category* B]
    [Category* D] [Category* E]
    (F : C ⥤ A) (G : C ⥤ B) (H : C ⥤ D) (I : C ⥤ E)
    (R : B ⥤ A) (S : E ⥤ D) (J : D ⥤ A) (L : E ⥤ B)
    (d : F ⟶ G ⋙ R) (c : H ⟶ I ⋙ S)
    (a : F ⟶ H ⋙ J) (b : G ⟶ I ⋙ L) (e : S ⋙ J ⟶ L ⋙ R)
    {Q K : C} (q : Q ≅ K)
    (h : d.app Q ≫ R.map (b.app Q) =
      a.app Q ≫ J.map (c.app Q) ≫ e.app (I.obj Q)) :
    d.app K ≫ R.map (b.app K) =
      a.app K ≫ J.map (c.app K) ≫ e.app (I.obj K) := by
  apply (cancel_epi (F.map q.hom)).mp
  have hd := d.naturality q.hom
  have hc := c.naturality q.hom
  have ha := a.naturality q.hom
  have hb := b.naturality q.hom
  have he := e.naturality (I.map q.hom)
  dsimp only [Functor.comp_map] at hd hc ha hb he
  calc
    F.map q.hom ≫ d.app K ≫ R.map (b.app K) =
        d.app Q ≫ R.map (G.map q.hom ≫ b.app K) := by
      rw [← Category.assoc, hd, Category.assoc, ← R.map_comp]
    _ = d.app Q ≫ R.map (b.app Q) ≫ R.map (L.map (I.map q.hom)) := by
      rw [hb, R.map_comp]
    _ = a.app Q ≫ J.map (c.app Q) ≫ e.app (I.obj Q) ≫
        R.map (L.map (I.map q.hom)) := by
      rw [← Category.assoc, h]
      simp only [Category.assoc]
    _ = a.app Q ≫ J.map (c.app Q ≫ S.map (I.map q.hom)) ≫
        e.app (I.obj K) := by rw [← he, J.map_comp]; simp only [Category.assoc]
    _ = F.map q.hom ≫ a.app K ≫ J.map (c.app K) ≫ e.app (I.obj K) := by
      rw [← hc, J.map_comp, ← Category.assoc, ← Category.assoc, ← ha]
      simp only [Category.assoc]

private theorem complete_of_iso (W : Scheme.{t})
    {A B : DerivedCategory (scalarReductionSource l E W)} (e : A ≅ B)
    (hA : IntegralOpenReduction.complete l E W A) :
    IntegralOpenReduction.complete l E W B := by
  obtain ⟨D, hlD, P, G, q, hq, a, hprod, δ, hδ⟩ := hA
  let := hprod
  refine ⟨D, hlD, P, G, q, hq, a ≪≫ e, hprod,
    δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · apply Pi.hom_ext
    intro n
    simp [Category.assoc]
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

private def alphaIso
    (SV : CoefficientDerivedSystemCalculus l E V)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (tensor : IntegralOpenReduction.TensorComparison l E j o)
    (r : IntegralOpenReduction.Comparison l E j o SV SX tensor) (n : ℕ) :
    (IntegralOpenReduction.complete l E X).ι ⋙ IntegralOpenReduction.shriek l E j o ⋙
        coefficientFiniteDerivedExtension l E V n ≅
      (IntegralOpenReduction.complete l E X).ι ⋙ coefficientFiniteDerivedExtension l E X n ⋙
        compactSupportCanonicalJLevel l E j o n :=
  Functor.isoWhiskerLeft
      ((IntegralOpenReduction.complete l E X).ι ⋙ IntegralOpenReduction.shriek l E j o)
      (SV.reductionEvaluation n).symm ≪≫
    Functor.isoWhiskerRight r.r (coefficientSequenceDerivedEvaluation l E V n) ≪≫
    Functor.isoWhiskerLeft ((IntegralOpenReduction.complete l E X).ι ⋙ SX.reduction)
      (compactSupportCanonicalJEvaluation l E j o n) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (IntegralOpenReduction.complete l E X).ι (SX.reductionEvaluation n))
      (compactSupportCanonicalJLevel l E j o n)

/-- Finite open extension commutes with successive scalar restriction, and the
strict open-reduction comparison respects the actual adjunction-transpose quotient maps.
Source: Stacks Tags 0E8I (open tensor compatibility), 06YY (K-flat scalar change),
and 0941 (strict coefficient systems); proof Step 1 of
`lem-sf-compact-support-proper-image-tower`.
(blueprint: lem-sf-integral-open-reduction-quotient-square).

Proof: integralOpenTensorQuotientModel constructs the ordinary finite restriction
square with its generator normalization and proves the quotient square on the
explicit tensor isomorphisms beta_n(Q), independently of a strict comparison.
Choose a flat-term K-flat resolution Q representing K. Transport completeness along
the localization isomorphism. integralOpenTensorRepresentative, using r.strictModel,
identifies alpha_n with beta_n(Q) at every level. Substitution gives the required
square on the representative. The alpha components form a natural isomorphism:
whisker and compose the inverse target reduction evaluation, r, canonical open
evaluation, and source reduction evaluation. The two quotient maps and the exact
open restriction comparison are natural transformations. Apply their naturality
equations to the representative isomorphism, and cancel the image of that
isomorphism under the larger-level reduction of open extension. The resulting
equality is the required square on K. This uses no finite-evaluation faithfulness,
boundedness, or flatness of a coefficient quotient. Empty opens, zero complexes,
and n=0 are included in the two model statements. -/
theorem integralOpenReductionQuotientSquare
    (SV : CoefficientDerivedSystemCalculus l E V)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (tensor : IntegralOpenReduction.TensorComparison l E j o)
    (r : IntegralOpenReduction.Comparison l E j o SV SX tensor) :
    ∃ ordinary : ∀ n : ℕ,
      normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
          IntegralOpenReduction.finiteExtension l E j o (n + 1) ≅
        IntegralOpenReduction.finiteExtension l E j o n ⋙
          normalizedDVRModuleRes l E V (Nat.le_succ n),
      (∀ (n : ℕ) (M : normalizedDVRModules l E X n) (W : V.ProEt)
        (a : W ⟶ IntegralOpenReduction.openObject j),
        HEq (fun x : ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M).val.obj
            (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
          ((ordinary n).hom.app M).val.app (op W)
            (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1)
              ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x))
          (fun x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
            IntegralOpenReduction.finiteExtensionSection l E j o n M W a x)) ∧
      let reductionMap (W : Scheme.{t}) (K : DerivedCategory (scalarReductionSource l E W))
          (n : ℕ) :
          (coefficientFiniteDerivedExtension l E W (n + 1)).obj K ⟶
            (normalizedDVRRes l E W (Nat.le_succ n)).obj
              ((coefficientFiniteDerivedExtension l E W n).obj K) :=
        ((coefficientFiniteAdjunction l E W (n + 1)).homEquiv _ _).symm
          ((coefficientFiniteAdjunction l E W n).unit.app K ≫
            (compactSupportSystemRestrictionComp l E W (Nat.le_succ n)).inv.app
              ((coefficientFiniteDerivedExtension l E W n).obj K))
      let alpha (K : (IntegralOpenReduction.complete l E X).FullSubcategory) (n : ℕ) :
          (coefficientFiniteDerivedExtension l E V n).obj
              ((IntegralOpenReduction.shriek l E j o).obj K.obj) ≅
            (compactSupportCanonicalJLevel l E j o n).obj
              ((coefficientFiniteDerivedExtension l E X n).obj K.obj) :=
        ((SV.reductionEvaluation n).app ((IntegralOpenReduction.shriek l E j o).obj K.obj)).symm ≪≫
          (coefficientSequenceDerivedEvaluation l E V n).mapIso (r.r.app K) ≪≫
          (compactSupportCanonicalJEvaluation l E j o n).app (SX.reduction.obj K.obj) ≪≫
          (compactSupportCanonicalJLevel l E j o n).mapIso ((SX.reductionEvaluation n).app K.obj)
      let openRestriction (n : ℕ) :
          normalizedDVRRes l E X (Nat.le_succ n) ⋙
              compactSupportCanonicalJLevel l E j o (n + 1) ≅
            compactSupportCanonicalJLevel l E j o n ⋙
              normalizedDVRRes l E V (Nat.le_succ n) := by
        letI := normalizedDVRModuleRes_limits l E X (Nat.le_succ n)
        letI := normalizedDVRModuleRes_colimits l E X (Nat.le_succ n)
        letI := normalizedDVRModuleRes_limits l E V (Nat.le_succ n)
        letI := normalizedDVRModuleRes_colimits l E V (Nat.le_succ n)
        exact Functor.mapDerivedCategorySquareIso (ordinary n)
  ∀ (K : (IntegralOpenReduction.complete l E X).FullSubcategory) (n : ℕ),
    reductionMap V ((IntegralOpenReduction.shriek l E j o).obj K.obj) n ≫
        (normalizedDVRRes l E V (Nat.le_succ n)).map (alpha K n).hom =
      (alpha K (n + 1)).hom ≫
        (compactSupportCanonicalJLevel l E j o (n + 1)).map (reductionMap X K.obj n) ≫
        (openRestriction n).hom.app
          ((coefficientFiniteDerivedExtension l E X n).obj K.obj) := by
  classical
  obtain ⟨ordinary, hgen, hsquare⟩ := integralOpenTensorQuotientModel l E j o tensor
  refine ⟨ordinary, hgen, ?_⟩
  change ∀ K n,
    (integralOpenReductionStep l E V n).app
        ((IntegralOpenReduction.shriek l E j o).obj K.obj) ≫
      (normalizedDVRRes l E V (Nat.le_succ n)).map
        (integralOpenReductionAlpha l E j o SV SX tensor r K n).hom =
    (integralOpenReductionAlpha l E j o SV SX tensor r K (n + 1)).hom ≫
      (compactSupportCanonicalJLevel l E j o (n + 1)).map
        ((integralOpenReductionStep l E X n).app K.obj) ≫ _
  intro K n
  let G := DerivedCategory.Q.objPreimage K.obj
  obtain ⟨Q, q, hQ, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E X) G
  have : QuasiIso q := hq
  let e : DerivedCategory.Q.obj Q ≅ K.obj :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K.obj
  have hc := complete_of_iso l E X e.symm K.property
  have hf (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X)
      (Q.X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E X) _).symm (hflat i)
  obtain ⟨hJQ, ha⟩ := integralOpenTensorRepresentative l E j o SV SX tensor r Q hQ hf hc
  have h := hsquare Q hQ hJQ n
  rw [← ha n, ← ha (n + 1)] at h
  let Jm := compactSupportCanonicalJLevel l E j o (n + 1)
  let Jn := compactSupportCanonicalJLevel l E j o n
  let R := normalizedDVRRes l E V (Nat.le_succ n)
  let S := normalizedDVRRes l E X (Nat.le_succ n)
  let ei : S ⋙ Jm ≅ Jn ⋙ R := by
    letI := normalizedDVRModuleRes_limits l E X (Nat.le_succ n)
    letI := normalizedDVRModuleRes_colimits l E X (Nat.le_succ n)
    letI := normalizedDVRModuleRes_limits l E V (Nat.le_succ n)
    letI := normalizedDVRModuleRes_colimits l E V (Nat.le_succ n)
    exact Functor.mapDerivedCategorySquareIso (ordinary n)
  exact square_of_iso
    ((IntegralOpenReduction.complete l E X).ι ⋙ IntegralOpenReduction.shriek l E j o ⋙
      coefficientFiniteDerivedExtension l E V (n + 1))
    ((IntegralOpenReduction.complete l E X).ι ⋙ IntegralOpenReduction.shriek l E j o ⋙
      coefficientFiniteDerivedExtension l E V n)
    ((IntegralOpenReduction.complete l E X).ι ⋙ coefficientFiniteDerivedExtension l E X (n + 1))
    ((IntegralOpenReduction.complete l E X).ι ⋙ coefficientFiniteDerivedExtension l E X n)
    R S Jm Jn
    (Functor.whiskerLeft
      ((IntegralOpenReduction.complete l E X).ι ⋙ IntegralOpenReduction.shriek l E j o)
      (integralOpenReductionStep l E V n))
    (Functor.whiskerLeft (IntegralOpenReduction.complete l E X).ι
      (integralOpenReductionStep l E X n))
    (alphaIso l E j o SV SX tensor r (n + 1)).hom
    (alphaIso l E j o SV SX tensor r n).hom ei.hom
    (ObjectProperty.isoMk (IntegralOpenReduction.complete l E X)
      (X := ⟨DerivedCategory.Q.obj Q, hc⟩) (Y := K) e) h

end WeilConjectures
