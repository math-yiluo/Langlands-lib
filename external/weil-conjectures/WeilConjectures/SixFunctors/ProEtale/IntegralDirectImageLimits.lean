/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageReductionTower
import WeilConjectures.SixFunctors.ProEtale.InternalRoosCompleteness

/-! # Integral direct image and the canonical finite reduction

Source: Stacks 099N and blueprint direct-image-limits, finite-projection and completion clauses.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem inverseMate_eq_of_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}
    (r : R ⋙ G ⟶ H ⋙ R') (b : G ⋙ L' ≅ L ⋙ H)
    (hb : ∀ M, G.map (adj.unit.app M) ≫ r.app (L.obj M) =
      adj'.unit.app (G.obj M) ≫ R'.map (b.hom.app M)) :
    ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ r)) = b.hom := by
  ext M
  apply (adj'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ r) M).symm.trans (hb M)

private theorem reductionPullback_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    IsIso (integralReductionPullbackMap l E j n) := by
  obtain ⟨b, hb⟩ := integral_reduction_pullback_normalization l E j n
  have h := inverseMate_eq_of_unit
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n))
    (CondensedRing.derivedComapUpperStarIso
      (DerivedNakayama.reductionRing l E (n + 1)) j).inv b hb
  change IsIso (((mateEquiv _ _).symm (TwoSquare.mk _ _ _ _ _)))
  rw [h]
  infer_instance

private theorem reflectsDerivedIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] {K L : DerivedCategory C} (f : K ⟶ L)
    [IsIso (F.mapDerivedCategory.map f)] : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro i
  have hF : IsIso ((DerivedCategory.homologyFunctor D i).map
      (F.mapDerivedCategory.map f)) := inferInstance
  have : IsIso ((DerivedCategory.homologyFunctor C i ⋙ F).map f) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) f).2 hF
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C i).map f)) := by
    change IsIso ((DerivedCategory.homologyFunctor C i ⋙ F).map f)
    infer_instance
  exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor C i).map f) F

private theorem finiteProjection_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)
    [IsIso (integralReductionPullbackMap l E j n)]
    (K : DerivedCategory (AdicCompletion.Modules l E U)) :
    IsIso (integralFiniteProjection l E j n K) := by
  obtain ⟨s, q, δ, q', δ', hT, hT', hq, hδ⟩ :=
    integral_direct_image_reduction_cone l E j n K
  let φ : Pretriangulated.Triangle.mk s q δ ⟶
      Pretriangulated.Triangle.mk s q' δ' :=
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := (AdicCompletion.restrict l E X n).map (integralFiniteProjection l E j n K)
      comm₁ := by simp
      comm₂ := by simpa using hq
      comm₃ := by simpa using hδ.symm }
  have : IsIso φ.hom₃ :=
    Pretriangulated.isIso₃_of_isIso₁₂ φ hT hT' (IsIso.id _) (IsIso.id _)
  exact reflectsDerivedIso (Mod.comap (AdicCompletion.quotient l E X n))
    (integralFiniteProjection l E j n K)

private theorem internal_roos_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : AlgebraicGeometry.ProEtale.IsDerivedComplete l E X K)
    [HasProduct (AdicCompletion.integralLevel l E X K)] :
    ∃ δ : (∏ᶜ (AdicCompletion.integralLevel l E X K)) ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (AdicCompletion.integralStep l E X K) K
        (Pi.lift (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient l E X n)).unit.app K)) δ := by
  obtain ⟨P, hP, ⟨e⟩, hη⟩ := hK
  obtain ⟨p, δ, hT, hp⟩ := AdicCompletion.roos_isDerivedLimit l E X K P hP e
  let : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) := hη
  let v : K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P) :=
    e.symm ≪≫ asIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P))
  refine ⟨δ ≫ (shiftFunctor _ (1 : ℤ)).map v.inv, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hT _
  refine Pretriangulated.Triangle.isoMk _ _ v (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change Pi.lift _ ≫ 𝟙 _ = v.hom ≫ p
    exact (Category.comp_id _).trans hp.symm
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

private theorem map_roos_complete
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    [PreservesLimit (Discrete.functor V) F]
    [HasProduct (fun n ↦ F.obj (V n))]
    (t : ∀ n, V (n + 1) ⟶ V n) (s : ∀ n, W (n + 1) ⟶ W n)
    (a : ∀ n, F.obj (V n) ≅ W n)
    (K : C) (p : ∀ n, K ⟶ V n) (q : ∀ n, F.obj K ⟶ W n)
    (ht : ∀ n, F.map (t n) ≫ (a n).hom = (a (n + 1)).hom ≫ s n)
    (hp : ∀ n, F.map (p n) ≫ (a n).hom = q n)
    (δ : (∏ᶜ V) ⟶ K⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle t K (Pi.lift p) δ) :
    ∃ δ' : (∏ᶜ W) ⟶ (F.obj K)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle s (F.obj K) (Pi.lift q) δ' := by
  let B : F.obj (∏ᶜ V) ≅ ∏ᶜ W := PreservesProduct.iso F V ≪≫
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }
  have hB (n : ℕ) : B.hom ≫ Pi.π W n = F.map (Pi.π V n) ≫ (a n).hom := by
    simp [B]
  have hfirst : F.map (Pi.lift p) ≫ B.hom = Pi.lift q := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, Pi.lift_comp_π]
    rw [← Category.assoc, ← F.map_comp, Pi.lift_comp_π, hp]
  have hmiddle : F.map (towerTransitionEndomorphism t) ≫ B.hom =
      B.hom ≫ towerTransitionEndomorphism s := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_comp_π, Functor.map_sub]
    simp only [reassoc_of% hB]
    erw [F.map_id, Category.id_comp]
    congr 1
    rw [← F.map_comp_assoc, Pi.lift_comp_π, Functor.map_comp, Category.assoc, ht]
  refine ⟨B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ (F.map_distinguished _ hT) _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) B.symm B.symm ?_ ?_ ?_
  · change Pi.lift q ≫ B.inv = 𝟙 _ ≫ F.map (Pi.lift p)
    rw [← hfirst]
    simp
  · change towerTransitionEndomorphism s ≫ B.inv =
      B.inv ≫ F.map (towerTransitionEndomorphism t)
    apply (cancel_mono B.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun f ↦ B.inv ≫ f) hmiddle.symm
  · change (B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ≫
        (shiftFunctor D (1 : ℤ)).map (𝟙 (F.obj K)) =
      B.inv ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)
    erw [(shiftFunctor D (1 : ℤ)).map_id]
    simpa only [Category.assoc, Functor.comp_obj] using
      Category.comp_id (B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)

/-- Direct image preserves canonical integral completeness and its specified residue mate
is invertible, without a finiteness or properness hypothesis on the scheme morphism.
Source: Stacks 099N; blueprint proposition-proper-base-change-complete-integral--1, finite-reduction
and completion-unit clauses.
(auxiliary; not a blueprint node).

Proof: pass from internal modules to sectionwise modules by the exact section-action
 equivalence. The integral coefficient limit identifies the ring with the completed adic
 ring for the lifted ring of integers and the principal uniformizer ideal. Quotient
 isomorphisms are induced by ULift.down and fix all scalar representatives. Each quotient
 is finite and perfect, by its two-term finite free resolution; the residue is torsion.
 These data form the adic coefficient datum of CompletedDirectImageLimits.
 Normalize the finite restriction squares by the identity on underlying sections. Their
 derived left-adjoint comparisons identify the actual finite reductions. The geometric
 adjunction comparisons identify the inverse scalar mate displayed here with the
 coefficient reduction/pullback isomorphism chi. In particular it is invertible.
 The finiteProjection_isIso theorem then identifies its geometric mate, computed as
 the residue homEquiv of inverse chi followed by reduction of the integral counit,
 with the invertible finite projection. This equality follows by the scalar and
 geometric adjunction Hom bijections; it retains the quotient action and fixes the
 displayed morphism rather than choosing an arbitrary isomorphism of cones.
 For completeness, use all positive finite projections, with their quotient transitions.
 Exact equivalences transport products and the signed Roos cone. The theorem push_complete
 applies to the resulting reduction tower. The completion-unit equation in
 towerProjection_properties identifies the transported map with the canonical
 augmentation used by IsDerivedComplete. Thus completeness of K implies completeness
 of its direct image. This argument applies to unbounded complexes, arbitrary scheme
 morphisms, empty schemes and zero complexes. -/
theorem internal_integral_direct_image_limits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    let χ :
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙
            AdicCompletion.derivedReduction l E U 0 ⟶
          AdicCompletion.derivedReduction l E X 0 ⋙
            (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory :=
      ((mateEquiv
          (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X 0))
          (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U 0))).symm
            (TwoSquare.mk _ _ _ _
              (CondensedRing.derivedComapUpperStarIso (DerivedNakayama.reductionRing l E 1) j).inv)
          )
    ∃ hχ : IsIso χ, letI := hχ; ∀ K : DerivedCategory (AdicCompletion.Modules l E U),
      (IsDerivedComplete l E U K → IsDerivedComplete l E X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K)) ∧
      IsIso (((CondensedRing.derivedUpperStarLowerStarAdjunction
        (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.quotientRing l E 1) j)).homEquiv _ _
        (inv (χ.app ((CondensedRing.moduleObjectDerivedPushforward
            (DerivedNakayama.integerRing l E) j).obj K)) ≫
          (AdicCompletion.derivedReduction l E U 0).map
            (((CondensedRing.derivedUpperStarLowerStarAdjunction
              (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
                (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                  (DerivedNakayama.integerRing l E) j)).counit.app K))) := by
  dsimp only
  have hχ := reductionPullback_isIso l E j 0
  refine ⟨hχ, ?_⟩
  intro K
  constructor
  · intro hK
    let F := CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j
    let : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E U)) :=
      ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete _ I⟩
    let : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)) :=
      ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete _ I⟩
    let : F.IsRightAdjoint :=
      ((CondensedRing.derivedUpperStarLowerStarAdjunction
        (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.integerRing l E) j)).isRightAdjoint
    let : F.CommShift ℤ := by
      change (CondensedRing.lowerStar
        (DerivedNakayama.integerRing l E) j).rightDerivedFunctor.CommShift ℤ
      infer_instance
    let : F.IsTriangulated := by
      change (CondensedRing.lowerStar
        (DerivedNakayama.integerRing l E) j).rightDerivedFunctor.IsTriangulated
      infer_instance
    have hχn (n : ℕ) := reductionPullback_isIso l E j n
    have hprojn (n : ℕ) : letI := hχn n; IsIso (integralFiniteProjection l E j n K) := by
      let := hχn n
      exact finiteProjection_isIso l E j n K
    obtain ⟨a, ht, hp⟩ := integral_direct_image_reduction_tower l E j K hχn hprojn
    obtain ⟨δ, hδ⟩ := internal_roos_complete l E U K hK
    obtain ⟨δ', hδ'⟩ := map_roos_complete F
      (AdicCompletion.integralStep l E U K)
      (AdicCompletion.integralStep l E X (F.obj K)) a K
      (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E U n)).unit.app K)
      (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E X n)).unit.app (F.obj K)) ht hp δ hδ
    exact AdicCompletion.isDerivedComplete_of_roos l E X (F.obj K) δ' hδ'
  · exact finiteProjection_isIso l E j 0 K

end AlgebraicGeometry.ProEtale
