/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRFlatCokernel
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarCone
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRStrictCoefficientAdjoint

/-! # Coefficient augmentation of the canonical strict DVR Roos object

Source: Stacks Tags 06YS, 06YY, 03EK and 05RT; blueprint DVR effectivity,
proof paragraphs 3--4. (blueprint: lem-coef-normalized-dvr-roos-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

local instance instNormalizedDVRRoosAugmentation1
    : HasDerivedCategory (completedIntegralModuleSheaves l E X D hl) :=
  HasDerivedCategory.standard _
local instance (priority := 10000) instNormalizedDVRRoosAugmentation2
    : EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
local instance (priority := 10000) instNormalizedDVRRoosAugmentation3
    : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
local instance (priority := 10000) instNormalizedDVRRoosAugmentation4 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X

local instance roosRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (scalarReductionRestriction l E X n) :=
  scalarReductionRestrictionLimits l E X n
local instance roosRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (scalarReductionRestriction l E X n) :=
  scalarReductionRestrictionColimits l E X n
local instance roosCompletedRestrictionAdditive (n : ℕ) :
    (completedIntegralRestrictScalars l E X D hl n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl n)).Additive
local instance roosCompletedRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E X D hl n) :=
  (completedIntegralRestrictScalars_exact l E X D hl n).1
local instance roosCompletedRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (completedIntegralRestrictScalars l E X D hl n) :=
  (completedIntegralRestrictScalars_exact l E X D hl n).2
local instance roosFiniteDerived (n : ℕ) : HasDerivedCategory (normalizedDVRModules l E X n) :=
  HasDerivedCategory.standard _

private theorem zeroSandwich
    {C : Type*} [Category C] [HasZeroMorphisms C] {P K I Z W : C}
    (a : P ⟶ K) (b : K ⟶ I) (c : I ⟶ Z) (d : Z ⟶ W) (h : b ≫ c = 0) :
    a ≫ b ≫ c ≫ d = 0 := by
  rw [← Category.assoc b c d, h, zero_comp, comp_zero]

private theorem coneCokernelDesc
    {C : Type*} [Category C] [Abelian C]
    (a : Arrow (CochainComplex C ℤ)) {N : CochainComplex C ℤ}
    (g : (CochainComplex.ConeCoimage.coker.obj a) ⟶ N)
    (f : a.right ⟶ N) (hf : a.hom ≫ f = 0) (hg : cokernel.π a.hom ≫ g = f) :
    CochainComplex.ConeCoimage.ρ.app a ≫ CochainComplex.ConeCoimage.desc.app a ≫ g =
      CochainComplex.mappingCone.desc a.hom 0 f (by simp [hf]) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply CochainComplex.mappingCone.ext_from _ (q + 1) q rfl
  · simp only [HomologicalComplex.comp_f, ← Category.assoc]
    rw [CochainComplex.ConeCoimage.inl_v_ρ_app_f]
    simp only [Category.assoc, CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.zero_v]
    change (Abelian.coimage.π a.hom).f (q + 1) ≫
      (CochainComplex.mappingCone.inl (CochainComplex.ConeCoimage.cokerSequence a).f).v
        (q + 1) q (by omega) ≫
      (CochainComplex.mappingCone.descShortComplex
        (CochainComplex.ConeCoimage.cokerSequence a)).f q ≫ g.f q = 0
    exact zeroSandwich _ _ _ _
      (CochainComplex.mappingCone.inl_v_descShortComplex_f
        (CochainComplex.ConeCoimage.cokerSequence a) (q + 1) q (by omega))
  · have h := congrArg (· ≫ g) (CochainComplex.ConeCoimage.inr_ρ_desc a)
    simpa only [HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f] using
      congrArg (fun z ↦ z.f q) (h.trans hg)

private theorem appendLast
    {C : Type*} [Category C] {P K I Z W : C}
    (a : P ⟶ K) (b : K ⟶ I) (c : I ⟶ Z) (d : Z ⟶ W) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem mapCompositeTarget
    {C B : Type*} [Category C] [Category B] (Q : C ⥤ B)
    {P K I : C} {Z Y : B} (a : P ⟶ K) (i : K ⟶ I)
    (r : Q.obj I ⟶ Z) (v : Z ⟶ Y) (z : Q.obj K ⟶ Y)
    (h : z = Q.map i ≫ r ≫ v) :
    Q.map a ≫ z = (Q.map (a ≫ i) ≫ r) ≫ v := by
  rw [h, Q.map_comp]
  simp only [Category.assoc]

private theorem rightAdjointTransport
    {C B : Type*} [Category C] [Category B] {L : C ⥤ B} {R : B ⥤ C}
    (adj : L ⊣ R) {G : C ⥤ C} (A : L ⋙ R ≅ G)
    {P K : C} {N Y : B} (f : P ⟶ R.obj N) (d : G.obj P ⟶ K)
    (g : K ⟶ R.obj N)
    (h : R.map ((adj.homEquiv P N).symm f) = A.hom.app P ≫ d ≫ g)
    (v : N ⟶ Y) (u : K ⟶ R.obj Y) (hu : u = g ≫ R.map v)
    (k : P ⟶ R.obj Y) (hk : k = f ≫ R.map v) :
    R.map ((adj.homEquiv P Y).symm k) = A.hom.app P ≫ d ≫ u := by
  rw [hk, adj.homEquiv_naturality_right_symm, Functor.map_comp, h, hu]
  simp only [Category.assoc]

private theorem appendTwo
    {C : Type*} [Category C] {P K I Z W : C}
    {a : P ⟶ K} {b : K ⟶ I} {c : P ⟶ I}
    (h : a ≫ b = c) (x : I ⟶ Z) (y : Z ⟶ W) :
    a ≫ b ≫ x ≫ y = c ≫ x ≫ y := by
  rw [← Category.assoc, ← Category.assoc, h, Category.assoc]

private theorem adjointProjectionTransport
    {C B : Type*} [Category C] [Category B] {L : C ⥤ B} {R : B ⥤ C}
    (adj : L ⊣ R) {G : C ⥤ C} (A : L ⋙ R ≅ G)
    {M N : C} (e : M ⟶ N) {Y : B} (f : N ⟶ R.obj Y)
    (g : G.obj N ⟶ R.obj Y)
    (h : R.map ((adj.homEquiv N Y).symm f) = A.hom.app N ≫ g)
    (fM : M ⟶ R.obj Y) (hf : e ≫ f = fM) :
    R.map ((adj.homEquiv M Y).symm fM) =
      A.hom.app M ≫ G.map e ≫ g := by
  rw [← hf, adj.homEquiv_naturality_left_symm, Functor.map_comp, h]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z ↦ z ≫ g) (A.hom.naturality e)

private theorem factorThroughCone
    {C B : Type*} [Category C] [Category B] (Q : C ⥤ B)
    {P K I : C} {J M Z : B} (a : P ⟶ K) (i : K ⟶ I) (f : P ⟶ I)
    (h : f = a ≫ i) (w : M ⟶ J) (b : J ⟶ Q.obj P) (r : Q.obj I ⟶ Z) :
    w ≫ b ≫ Q.map f ≫ r = w ≫ (b ≫ Q.map a) ≫ (Q.map i ≫ r) := by
  rw [h, Q.map_comp]
  simp only [Category.assoc]

/- STATEMENT-DISPUTED (pre-repair): successor-compatible D(R) level isomorphisms
allow Bockstein twists. The finite coefficient compatibility below repairs this;
see coord/changes/W3-DVR-strict-coefficient-augmentation.md for the counterexample. -/

/-- The coefficient interpretation of the scalar cone on the canonical Roos
object, with its specified augmentation. This statement supplies no assertion
about preservation of homotopy limits by the scalar cone functor.

Source: blueprint DVR effectivity proof, paragraphs 1 and 4; Stacks 06YY, 07A6 and
0941. (blueprint: lem-coef-normalized-dvr-roos-augmentation).

Proof: apply the strict finite-coefficient adjoint calculation to the normalized
reduction from the zeroth tail term followed by iN. Its cone map has zero shifted
component and unshifted component the reduction followed by iN. The normalized
cokernel augmentation has those same components after iN, by the cokernel descent
equation. The finite-derived compatibility hN identifies its target with T.M n;
right naturality of the adjunction transports the calculation through eN. Finally
precompose with the canonical homotopy-limit projection and use left naturality
of the adjunction and naturality of the coefficient comparison A.

The finite-coefficient compatibility is essential: completed-derived successor
compatibility alone permits off-diagonal Bockstein twists of the level comparison.
The canonical strict model supplies N, iN and eN by its finiteModel construction.
The argument includes exponent one, the zero tower and the empty site. -/
theorem normalizedDVR_roos_augmentation
    (T : NormalizedDVRTower l E X D hl) (n : ℕ)
    (adj : scalarReductionDerivedExtension l E X n ⊣
      scalarReductionDerivedRestriction l E X n)
    [HasLimitsOfShape (Discrete ℕ) (completedIntegralDerivedCategory l E X D hl)]
    (U : ℕᵒᵖ ⥤ CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
    (hU : CochainComplex.IsNormalizedAdicTower (normalizedDVRUniformizer l E X) U)
    (eU : ∀ j : ℕ, DerivedCategory.Q.obj (U.obj (op (j + 1))) ≅
      (normalizedDVRTowerEvaluation l E X D hl j).obj T.tower)
    (_heU : ∀ j : ℕ,
      DerivedCategory.Q.map (U.map (homOfLE (Nat.succ_le_succ j.le_succ)).op) ≫
          (eU j).hom = (eU (j + 1)).hom ≫
        (normalizedDVRTowerTransition l E X D hl j.le_succ).app T.tower)
    (N : CochainComplex (normalizedDVRModules l E X n) ℤ)
    (iN : U.obj (op (n + 1)) ≅
      ((completedIntegralRestrictScalars l E X D hl n).mapHomologicalComplex
        (.up ℤ)).obj N)
    (eN : (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj N ≅ T.M n)
    (hN : (eU n).hom ≫ (T.evaluationIso n).hom =
      DerivedCategory.Q.map iN.hom ≫
        (completedIntegralRestrictScalars l E X D hl n).mapDerivedCategoryFactors.inv.app N ≫
        (normalizedDVRResCompleted l E X D hl n).map eN.hom) :
    ∃ A : scalarReductionDerivedExtension l E X n ⋙
          scalarReductionDerivedRestriction l E X n ≅
        CochainComplex.LinearScalarCone.derived
          (A := completedIntegralModuleSheaves l E X D hl)
          (normalizedDVRUniformizer l E X ^ (n + 1)),
      let c := CategoryTheory.Pretriangulated.homotopyLimitCone (U ⋙ DerivedCategory.Q)
      let k := (CategoryTheory.Pretriangulated.addOpFunctor (n + 1)).obj (op 0)
      (scalarReductionDerivedRestriction l E X n).map
          ((adj.homEquiv c.pt (T.M n)).symm
            (c.π.app (op (n + 1)) ≫ (eU n).hom ≫ (T.evaluationIso n).hom)) =
        A.hom.app c.pt ≫
          (CochainComplex.LinearScalarCone.derived
            (normalizedDVRUniformizer l E X ^ (n + 1))).map (c.π.app k) ≫
          CochainComplex.LinearScalarCone.derivedAugmentation hU (n + 1) (op 0) ≫
          (eU n).hom ≫
          (T.evaluationIso n).hom := by
  let := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  obtain ⟨A, hA⟩ := normalizedDVR_strict_coefficient_adjoint l E X D hl n adj
  let Q := DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)
  let c := CategoryTheory.Pretriangulated.homotopyLimitCone (U ⋙ Q)
  let k := (CategoryTheory.Pretriangulated.addOpFunctor (n + 1)).obj (op 0)
  let P := U.obj k
  let red : P ⟶ U.obj (op (n + 1)) :=
    (CochainComplex.IsNormalizedAdicTower.red (T := U) (n + 1)).app (op 0)
  let aug := CochainComplex.LinearScalarCone.augmentation hU (n + 1) (op 0)
  let G := CochainComplex.LinearScalarCone.derived
    (A := completedIntegralModuleSheaves l E X D hl)
    (normalizedDVRUniformizer l E X ^ (n + 1))
  let comp := CochainComplex.LinearScalarCone.comparison
    (A := completedIntegralModuleSheaves l E X D hl)
    (normalizedDVRUniformizer l E X ^ (n + 1))
  let V := scalarReductionDerivedRestriction l E X n
  let r := (completedIntegralRestrictScalars l E X D hl n).mapDerivedCategoryFactors.inv.app N
  let f : P ⟶ ((completedIntegralRestrictScalars l E X D hl n).mapHomologicalComplex
      (.up ℤ)).obj N := red ≫ iN.hom
  have hf : (normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P) ≫ f = 0 := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ iN.hom) (hU.smul_comp_red (n + 1) (op 0))).trans (zero_comp))
  have hlevel := hA P N f hf
  have hdesc : CochainComplex.mappingCone.desc
      (normalizedDVRUniformizer l E X ^ (n + 1) • 𝟙 P) 0 f (by simp [hf]) =
      aug ≫ iN.hom := by
    have hred : cokernel.π
        ((CochainComplex.IsNormalizedAdicTower.arrowTower
          (ϖ := normalizedDVRUniformizer l E X) (T := U) (n + 1)).obj (op 0)).hom ≫
        (hU.cokerDesc (n + 1) (op 0) ≫ iN.hom) = f :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ iN.hom) (hU.π_cokerDesc (n + 1) (op 0)))
    have h := coneCokernelDesc
      ((CochainComplex.IsNormalizedAdicTower.arrowTower
        (ϖ := normalizedDVRUniformizer l E X) (T := U) (n + 1)).obj (op 0))
      (hU.cokerDesc (n + 1) (op 0) ≫ iN.hom) f hf hred
    exact h.symm.trans (appendLast _ _ _ _)
  let d : G.obj (Q.obj P) ⟶ Q.obj (U.obj (op (n + 1))) :=
    comp.hom.app P ≫ Q.map aug
  have hbase : V.map ((adj.homEquiv (Q.obj P) (DerivedCategory.Q.obj N)).symm
      (Q.map f ≫ r)) =
      A.hom.app (Q.obj P) ≫ d ≫ (Q.map iN.hom ≫ r) :=
    hlevel.trans (factorThroughCone Q aug iN.hom _ hdesc (A.hom.app (Q.obj P))
      (comp.hom.app P) r)
  let e : Q.obj P ⟶ V.obj (T.M n) := Q.map red ≫ (eU n).hom ≫ (T.evaluationIso n).hom
  have he : e = (Q.map f ≫ r) ≫ V.map eN.hom :=
    mapCompositeTarget Q red iN.hom r (V.map eN.hom)
      ((eU n).hom ≫ (T.evaluationIso n).hom) hN
  have hb : V.map ((adj.homEquiv (Q.obj P) (T.M n)).symm e) =
      A.hom.app (Q.obj P) ≫ d ≫ (eU n).hom ≫ (T.evaluationIso n).hom := by
    have hu : (eU n).hom ≫ (T.evaluationIso n).hom =
        (Q.map iN.hom ≫ r) ≫ V.map eN.hom :=
      hN.trans (Category.assoc _ _ _).symm
    exact rightAdjointTransport adj A (Q.map f ≫ r) d (Q.map iN.hom ≫ r)
      hbase eN.hom ((eU n).hom ≫ (T.evaluationIso n).hom) hu e he
  let fM : c.pt ⟶ V.obj (T.M n) :=
    c.π.app (op (n + 1)) ≫ (eU n).hom ≫ (T.evaluationIso n).hom
  have hp : c.π.app k ≫ e = fM := by
    have hn : c.π.app k ≫ Q.map red = c.π.app (op (n + 1)) :=
      c.w (homOfLE (Nat.le_add_left (n + 1) 0)).op
    exact appendTwo hn (eU n).hom (T.evaluationIso n).hom
  refine ⟨A, ?_⟩
  exact adjointProjectionTransport adj A (c.π.app k) e
    (d ≫ (eU n).hom ≫ (T.evaluationIso n).hom) hb fM hp

end WeilConjectures
