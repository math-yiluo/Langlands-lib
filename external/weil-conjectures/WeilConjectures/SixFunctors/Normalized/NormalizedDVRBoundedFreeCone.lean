/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRFlatCokernel
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarConeExactProducts
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosAugmentation
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists

/-! # Bounded-free comparison for a strict DVR model

Source: Stacks Tags 06YS, 06YY, 03EK and 05RT; blueprint DVR effectivity,
proof paragraphs 3--4. (blueprint: lem-coef-normalized-dvr-bounded-free-cone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

local instance instNormalizedDVRBoundedFreeCone1
    : HasDerivedCategory (completedIntegralModuleSheaves l E X D hl) :=
  HasDerivedCategory.standard _
local instance (priority := 10000) instNormalizedDVRBoundedFreeCone2
    : EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
local instance (priority := 10000) instNormalizedDVRBoundedFreeCone3
    : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
local instance (priority := 10000) instNormalizedDVRBoundedFreeCone4 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X

local instance boundedConeFiniteDerived (n : ℕ) :
    HasDerivedCategory (normalizedDVRModules l E X n) :=
  HasDerivedCategory.standard _
local instance boundedConeCompletedRestrictionAdditive (n : ℕ) :
    (completedIntegralRestrictScalars l E X D hl n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl n)).Additive
local instance boundedConeCompletedRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E X D hl n) :=
  (completedIntegralRestrictScalars_exact l E X D hl n).1
local instance boundedConeCompletedRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (completedIntegralRestrictScalars l E X D hl n) :=
  (completedIntegralRestrictScalars_exact l E X D hl n).2

private theorem roosConeExists
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ i : ℤ, (shiftFunctor C i).Additive] [CategoryTheory.Pretriangulated C]
    {V : ℕ → C} [HasProduct V] (f : ∀ j, V (j + 1) ⟶ V j)
    (M : C) (p : M ⟶ ∏ᶜ V) (δ : (∏ᶜ V) ⟶ M⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f M p δ) :
    ∃ q : (Functor.const ℕᵒᵖ).obj M ⟶ Functor.ofOpSequence f,
      CategoryTheory.Pretriangulated.IsHomotopyLimit (Cone.mk M q) ∧
      ∀ j, q.app (op j) = p ≫ Pi.π V j := by
  let F := Functor.ofOpSequence f
  let P : Fan (fun j : ℕ ↦ F.obj (op j)) := Fan.mk _ (Pi.π V)
  let hp : IsLimit P := productIsProduct V
  have ht : CategoryTheory.Pretriangulated.towerShift (F := F) hp =
      towerProductShift f := by
    apply (towerProductShift_eq_iff f _).2
    intro j
    simpa only [P, fan_mk_proj, F, Functor.ofOpSequence_map_homOfLE_succ] using
      CategoryTheory.Pretriangulated.towerShift_proj hp j
  have hT : CategoryTheory.Pretriangulated.Triangle.mk p
      (𝟙 _ - CategoryTheory.Pretriangulated.towerShift (F := F) hp) δ ∈
      distTriang C := by
    rw [ht]
    exact h
  exact ⟨(CategoryTheory.Pretriangulated.coneOfComp hp p
      (CategoryTheory.Pretriangulated.comp_towerShift_of_distinguished hp hT)).π,
    CategoryTheory.Pretriangulated.isHomotopyLimit_coneOfComp hp hT, fun j ↦ rfl⟩

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

private theorem isoLeg {C : Type*} [Category C] {X Y Z W : C}
    (e : X ≅ Y) (q : X ⟶ Z) (r : Y ⟶ W) (i : W ≅ Z)
    (h : e.hom ≫ r = q ≫ i.inv) : e.hom ≫ r ≫ i.hom = q := by
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Tensoring the Roos limit with the principal two-term resolution gives the
homotopy limit of multiplication cones, preserving the augmented projection.
Source: Bhatt--Scholze, Lemmas 3.5.4--3.5.5; Stacks Tags 0941, 07KC and 06YS;
blueprint DVR effectivity, bounded-free tensor calculation.
(blueprint: lem-coef-normalized-dvr-bounded-free-cone).

Proof: form the universal localization G of the explicit scalar cone. The generic
bounded-free lemma gives its commutative shift, exactness and preservation of
countable products. The separate coefficient-augmentation lemma identifies
restricted derived scalar reduction with G, naturally on the canonical Roos
object, and fixes its augmented projection. The selected level is supplied as a
strict finite-coefficient complex with its compatible finite-derived comparison;
this is passed unchanged to the augmentation lemma.

The given Roos triangle supplies a homotopy-limit cone with vertex exactly M and
legs p followed by the product projections. The successor equations heU make eU
a natural tower isomorphism from the one-step tail of U. Homotopy-limit uniqueness
and finite-tail invariance give e from M to the canonical Roos object, with its
projection equations. Apply G to the (n+1)-step tail of the canonical cone and
transport its representative comparison to the multiplication-cone tower. This
constructs c and proves its homotopy-limit property. Compose the coefficient
comparison with G(e) to construct a. Adjoint naturality in the source and
naturality of the coefficient comparison transport the canonical augmented
projection equation along e to the required equality. No assertion of
invertibility of that projection or nilpotent-fibre calculation is used.
Exponent n+1 is positive even at n=0, and the same construction handles zero
towers and the empty scheme. -/
theorem normalizedDVR_bounded_free_cone
    (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ) (n : ℕ)
    (adj : scalarReductionDerivedExtension l E X n ⊣
      scalarReductionDerivedRestriction l E X n)
    [HasLimitsOfShape (Discrete ℕ) (completedIntegralDerivedCategory l E X D hl)]
    (U : ℕᵒᵖ ⥤ CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
    (hU : CochainComplex.IsNormalizedAdicTower (normalizedDVRUniformizer l E X) U)
    (eU : ∀ j : ℕ, DerivedCategory.Q.obj (U.obj (op (j + 1))) ≅
      (normalizedDVRTowerEvaluation l E X D hl j).obj T.tower)
    (heU : ∀ j : ℕ,
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
    ∃ (c : Cone (CochainComplex.IsNormalizedAdicTower.arrowTower
      (ϖ := normalizedDVRUniformizer l E X) (T := U) (n + 1) ⋙
        CochainComplex.ConeCoimage.cone ⋙ DerivedCategory.Q)),
    CategoryTheory.Pretriangulated.IsHomotopyLimit c ∧
    ∃ (a : (scalarReductionDerivedRestriction l E X n).obj
          ((scalarReductionDerivedExtension l E X n).obj M) ≅ c.pt),
      (scalarReductionDerivedRestriction l E X n).map
          ((adj.homEquiv M (T.M n)).symm
            (p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom)) =
        a.hom ≫ c.π.app (op 0) ≫ DerivedCategory.Q.map
          (CochainComplex.ConeCoimage.ρ.app _ ≫ CochainComplex.ConeCoimage.desc.app _ ≫
            hU.cokerDesc (n + 1) (op 0)) ≫ (eU n).hom ≫
            (T.evaluationIso n).hom :=
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in by
  let F := U ⋙ DerivedCategory.Q
  let cU := CategoryTheory.Pretriangulated.homotopyLimitCone F
  have hcU : CategoryTheory.Pretriangulated.IsHomotopyLimit cU :=
    CategoryTheory.Pretriangulated.isHomotopyLimit_homotopyLimitCone F
  let V : ℕᵒᵖ ⥤ completedIntegralDerivedCategory l E X D hl :=
    Functor.ofOpSequence (X := fun j : ℕ ↦
      (normalizedDVRTowerEvaluation l E X D hl j).obj T.tower)
    (fun j : ℕ ↦ (normalizedDVRTowerTransition l E X D hl j.le_succ).app T.tower)
  let eVhom : (CategoryTheory.Pretriangulated.addOpFunctor 1 ⋙ F) ⟶ V :=
    NatTrans.ofOpSequence (fun j ↦ (eU j).hom) (by
      intro j
      dsimp only [F, V, Functor.comp_map]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      have hm : (CategoryTheory.Pretriangulated.addOpFunctor 1).map
          (homOfLE j.le_succ).op = (homOfLE (Nat.succ_le_succ j.le_succ)).op :=
        Subsingleton.elim _ _
      rw [hm]
      exact heU j)
  let eV : (CategoryTheory.Pretriangulated.addOpFunctor 1 ⋙ F) ≅ V :=
    NatIso.ofComponents (fun j ↦ eU j.unop) (by
      intro i j f
      exact eVhom.naturality f)
  obtain ⟨q, hcM, hp⟩ := roosConeExists _ M p δ hc
  let cM := Cone.mk M q
  obtain ⟨e, hb⟩ := hcM.exists_iso_of_iso eV.symm (hcU.whiskerAdd 1)
  have he (j : ℕ) : e.hom ≫ cU.π.app (op (j + 1)) ≫ (eU j).hom =
      p ≫ Pi.π _ j := by
    have hbj := hb j
    change e.hom ≫ cU.π.app (op (j + 1)) = q.app (op j) ≫ (eU j).inv at hbj
    exact (isoLeg e (q.app (op j)) (cU.π.app (op (j + 1))) (eU j) hbj).trans (hp j)
  let s := normalizedDVRUniformizer l E X ^ (n + 1)
  let G := CochainComplex.LinearScalarCone.derived
    (A := completedIntegralModuleSheaves l E X D hl) s
  obtain ⟨hshift, htri, hprod⟩ := CochainComplex.LinearScalarCone.exact_products
    (A := completedIntegralModuleSheaves l E X D hl) s
  let := hshift
  let := htri
  let := hprod
  let c0 := G.mapCone (cU.whisker (CategoryTheory.Pretriangulated.addOpFunctor (n + 1)))
  have hc0 : CategoryTheory.Pretriangulated.IsHomotopyLimit c0 :=
    (hcU.whiskerAdd (n + 1)).map G
  let K := CochainComplex.IsNormalizedAdicTower.arrowTower
    (ϖ := normalizedDVRUniformizer l E X) (T := U) (n + 1) ⋙
      CochainComplex.ConeCoimage.cone ⋙ DerivedCategory.Q
  let w : (CategoryTheory.Pretriangulated.addOpFunctor (n + 1) ⋙ F) ⋙ G ≅ K :=
    Functor.isoWhiskerLeft
      (CategoryTheory.Pretriangulated.addOpFunctor (n + 1) ⋙ U)
      (CochainComplex.LinearScalarCone.comparison s)
  let c : Cone K := { pt := c0.pt, π := c0.π ≫ w.hom }
  have hcl : CategoryTheory.Pretriangulated.IsHomotopyLimit c :=
    hc0.of_iso w c (Iso.refl _) (fun j ↦ by simp [c])
  obtain ⟨A, hA⟩ := normalizedDVR_roos_augmentation l E X D hl T n adj U hU eU heU N iN eN hN
  let a : (scalarReductionDerivedRestriction l E X n).obj
      ((scalarReductionDerivedExtension l E X n).obj M) ≅ c.pt :=
    A.app M ≪≫ G.mapIso e
  refine ⟨c, hcl, a, ?_⟩
  have hf : e.hom ≫ (cU.π.app (op (n + 1)) ≫
      (eU n).hom ≫ (T.evaluationIso n).hom) =
      p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom := by
    simpa only [Category.assoc] using
      congrArg (fun z ↦ z ≫ (T.evaluationIso n).hom) (he n)
  have h := adjointProjectionTransport adj A e.hom
    (cU.π.app (op (n + 1)) ≫ (eU n).hom ≫ (T.evaluationIso n).hom)
    (G.map (cU.π.app ((CategoryTheory.Pretriangulated.addOpFunctor (n + 1)).obj (op 0))) ≫
      CochainComplex.LinearScalarCone.derivedAugmentation hU (n + 1) (op 0) ≫
      (eU n).hom ≫ (T.evaluationIso n).hom) hA
    (p ≫ Pi.π (fun j : ℕ ↦
      (normalizedDVRTowerEvaluation l E X D hl j).obj T.tower) n ≫
      (T.evaluationIso n).hom) hf
  dsimp only [a]
  dsimp only [c, c0, w]
  set_option backward.isDefEq.respectTransparency false in
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.comp_obj, G, s,
    NatTrans.comp_app, Functor.mapCone_π_app, Cone.whisker_π,
    Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom,
    CochainComplex.LinearScalarCone.derivedAugmentation,
    CochainComplex.LinearScalarCone.augmentation, Category.assoc] using h

end WeilConjectures
