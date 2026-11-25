/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.AugmentedReductionNaturality
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.StrictReductionPresentationMap
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OpenSystemCounitEvaluation

/-! # The restriction counit on good complexes

Source: Stacks Project, Tags 0E8I, 0GL1, 03DJ, 06YY and 0941.
This isolates the representative construction, independently of reconstruction or
realization through total limits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
attribute [local irreducible] HasDerivedCategory.standard
universe t u v h w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (SX : CoefficientDerivedSystemCalculus l E X)

local instance counitRestrictionLimits : PreservesFiniteLimits (restriction l E j o) := by
  let : PreservesLimitsOfSize.{0, 0} o.integral.inverse :=
    o.integral.toAdjunction.rightAdjoint_preservesLimits
  have h : PreservesFiniteLimits o.integral.inverse :=
    PreservesLimitsOfSize.preservesFiniteLimits o.integral.inverse
  dsimp only [restriction]
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ (by infer_instance) h

local instance counitRestrictionColimits : PreservesFiniteColimits (restriction l E j o) := by
  let : PreservesColimitsOfSize.{0, 0} o.integral.inverse :=
    o.integral.symm.toAdjunction.leftAdjoint_preservesColimits
  have h : PreservesFiniteColimits o.integral.inverse :=
    PreservesColimitsOfSize.preservesFiniteColimits o.integral.inverse
  dsimp only [restriction]
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ (by infer_instance) h

local instance counitSystemRestrictionLimits :
    PreservesFiniteLimits (systemRestriction l E j o) := by
  let : PreservesLimitsOfSize.{0, 0} o.systems.inverse :=
    o.systems.toAdjunction.rightAdjoint_preservesLimits
  have h : PreservesFiniteLimits o.systems.inverse :=
    PreservesLimitsOfSize.preservesFiniteLimits o.systems.inverse
  dsimp only [systemRestriction]
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ (by infer_instance) h

local instance counitSystemRestrictionColimits :
    PreservesFiniteColimits (systemRestriction l E j o) := by
  let : PreservesColimitsOfSize.{0, 0} o.systems.inverse :=
    o.systems.symm.toAdjunction.leftAdjoint_preservesColimits
  have h : PreservesFiniteColimits o.systems.inverse :=
    PreservesColimitsOfSize.preservesFiniteColimits o.systems.inverse
  dsimp only [systemRestriction]
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ (by infer_instance) h

private theorem exactCounit_model
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (Q : CochainComplex D ℤ) :
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).counit.app
        (DerivedCategory.Q.obj Q) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app Q) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app Q) := by
  simp only [SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction,
    Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
  rfl

private theorem finiteCounit_calculation
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {V C₀ C₁ : C} {T W D₀ X₀ : D}
    (κC : C₀ ≅ V) (κU : C₁ ≅ V) (κX : X₀ ≅ W) (κD : D₀ ≅ T)
    (t : T ≅ F.obj V) (a : D₀ ⟶ F.obj C₀)
    (k : C₀ ⟶ C₁) (b : C₁ ⟶ G.obj X₀) (q : T ⟶ W)
    (ha : a ≫ F.map κC.hom = κD.hom ≫ t.hom)
    (hk : k ≫ κU.hom = κC.hom)
    (hb : b ≫ G.map κX.hom =
      κU.hom ≫ adj.unit.app V ≫ G.map t.inv ≫ G.map q) :
    a ≫ F.map k ≫ F.map b ≫ adj.counit.app X₀ ≫ κX.hom = κD.hom ≫ q := by
  have hn := adj.counit.naturality κX.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← hn]
  rw [← F.map_comp_assoc b, hb]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc k, hk]
  rw [reassoc_of% ha]
  have ht := adj.counit.naturality t.inv
  have hq := adj.counit.naturality q
  dsimp only [Functor.comp_map, Functor.id_map] at ht hq
  rw [hq, reassoc_of% ht, adj.left_triangle_components_assoc]
  simp only [Iso.hom_inv_id_assoc]

private theorem system_hom_ext {C D : coefficientSequenceModules l E X}
    {f g : C ⟶ D}
    (h : ∀ n : ℕ, (coefficientSequenceEvaluation l E X n).map f =
      (coefficientSequenceEvaluation l E X n).map g) : f = g := by
  ext V x
  exact congrArg (fun k ↦ k.val.app (op V.unop.2) x) (h V.unop.1)

private theorem finiteCounit_evaluation_chain
    {C D c d : Type*} [Category C] [Category D] [Category c] [Category d]
    {JF : C ⥤ D} {EU : C ⥤ c} {EX : D ⥤ d} {F : c ⥤ d} {G : d ⥤ c}
    (η : JF ⋙ EX ≅ EU ⋙ F)
    {C₀ C₁ U₀ : C} {D₀ X : D}
    (fd : D₀ ⟶ JF.obj C₀) (k : C₀ ⟶ C₁) (fu : C₁ ⟶ U₀)
    (ε : JF.obj U₀ ⟶ X) (ρ : EU.obj U₀ ⟶ G.obj (EX.obj X))
    (δ : F.obj (G.obj (EX.obj X)) ⟶ EX.obj X)
    (hε : EX.map ε = η.hom.app U₀ ≫ F.map ρ ≫ δ) :
    EX.map (fd ≫ JF.map k ≫ JF.map fu ≫ ε) =
      (EX.map fd ≫ η.hom.app C₀) ≫ F.map (EU.map k) ≫
        F.map (EU.map fu ≫ ρ) ≫ δ := by
  have hk := η.hom.naturality k
  have hf := η.hom.naturality fu
  dsimp only [Functor.comp_map] at hk hf
  simp only [Functor.map_comp, hε, Category.assoc]
  rw [reassoc_of% hf, reassoc_of% hk]

private theorem mapped_chain_equality
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' E' : C} (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ D')
    (d : D' ⟶ E') (z : A ⟶ E') (h : a ≫ b ≫ c ≫ d = z) :
    F.map a ≫ F.map b ≫ F.map c ≫ F.map d = F.map z := by
  simpa only [Functor.map_comp] using congrArg (fun f ↦ F.map f) h

private theorem derivedCounit_calculation
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {J : C ⥤ D} {P : D ⥤ C}
    (SU : A ⥤ C) (SX : B ⥤ D)
    (r : F ⋙ SX ≅ SU ⋙ J) (s : G ⋙ SU ⟶ SX ⋙ P)
    (ε : G ⋙ F ⟶ 𝟭 B) (δ : P ⋙ J ⟶ 𝟭 D)
    (Q Y : B) (R : A) (g : G.obj Q ⟶ R) (e : F.obj R ⟶ Y) (q : Y ⟶ Q)
    {C₀ C₁ U₀ : C} {D₀ X₀ V₀ V₁ V₂ : D}
    (eC : SU.obj R ≅ C₀) (eU : SU.obj R ≅ C₁)
    (eD : SX.obj Y ≅ D₀) (eX : SX.obj Q ≅ X₀)
    (k : C₀ ⟶ C₁) (fU : C₁ ⟶ U₀) (p : P.obj X₀ ⟶ U₀)
    (a : J.obj C₀ ⟶ V₀) (b : J.obj C₁ ⟶ V₁) (c : J.obj U₀ ⟶ V₂)
    (fD : D₀ ⟶ V₀) (jk : V₀ ⟶ V₁) (jf : V₁ ⟶ V₂) (d : V₂ ⟶ X₀)
    (z : D₀ ⟶ X₀)
    (hg : ε.app Q = F.map g ≫ e ≫ q)
    (hδ : δ.app X₀ = J.map p ≫ c ≫ d)
    (hk : eU.hom = eC.hom ≫ k)
    (hz : SX.map q ≫ eX.hom = eD.hom ≫ z)
    (hr : r.hom.app R ≫ J.map eC.hom ≫ a = SX.map e ≫ eD.hom ≫ fD)
    (hs : SU.map g ≫ eU.hom ≫ fU = s.app Q ≫ P.map eX.hom ≫ p)
    (hak : J.map k ≫ b = a ≫ jk) (hbf : J.map fU ≫ c = b ≫ jf)
    (hd : fD ≫ jk ≫ jf ≫ d = z) :
    J.map (s.app Q) ≫ δ.app (SX.obj Q) = r.inv.app (G.obj Q) ≫ SX.map (ε.app Q) := by
  apply (cancel_epi (r.hom.app (G.obj Q))).1
  apply (cancel_mono eX.hom).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have hn := δ.naturality eX.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← hn, hδ]
  simp only [← J.map_comp_assoc]
  rw [← hs, hk]
  simp only [Functor.map_comp, Category.assoc]
  have hnr := r.hom.naturality g
  dsimp only [Functor.comp_map] at hnr
  rw [← reassoc_of% hnr, reassoc_of% hbf, reassoc_of% hak, reassoc_of% hr]
  rw [hd, ← hz, hg]
  simp only [Functor.map_comp, Category.assoc]

/-- The counit square for any normalized strict restriction comparison, on good complexes.
This asserts one equality and does not assert existence or invertibility of a comparison.
Source: Stacks sites-modules.tex, Tags 03DJ and 0E8I; sites-cohomology.tex,
Tags 06YY, 0GL1 and 0941; the counit calculation in transport steps 2--4.
(blueprint: lem-sf-open-restriction-counit-on-good-complexes).

Proof: fix Q and take the augmented presentations supplied by hs and hr. Their
restricted complexes have the same integral source but may have different strict
system models. Assemble the identity on that source into a strict comparison
between the two models. Assemble the ordinary integral counit into a second
strict map from the extension model to the X model. Naturality of augmented
presentations identifies the localizations of these two maps with the identity
on reduction and with reduction of the ordinary counit, respectively.

At every degree and finite coefficient, substitute the extension square from hr
and the unit/inverse-tensor/counit expression from hs. Naturality of the finite
counit and the triangle identity cancel the finite unit and counit, followed by
the tensor isomorphism and its inverse. Ordinary system evaluations are jointly
faithful, so this proves an equality of strict chain-system maps. Localize that
equality, substitute the two representative squares and the two augmentation
identifications, and cancel their isomorphisms. The localization formula for an
exact adjunction counit gives precisely the two counits in the conclusion.
No detection of arbitrary derived arrows by finite evaluation is used. -/
theorem openRestrictionCounitOnGoodComplexes
    (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o)
    (tensor : TensorComparison l E j o)
    (hr :
      ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (hQ : integralOperationsGoodComplex l E U Q),
    ∃ (hJQ : integralOperationsGoodComplex l E X
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (D : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (eC : SU.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
      (eD : SX.reduction.obj (DerivedCategory.Q.obj
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q)) ≅ DerivedCategory.Q.obj D)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E U n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E U n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj
            (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (f : D ≅ ((systemExtension l E j o).mapHomologicalComplex (.up ℤ)).obj C),
      CoefficientReductionPresentation l E U SU.toCoefficientDerivedSystemReduction
        Q hQ.1 C eC κC ∧
      AugmentedPresentation l E U SU Q C eC κC ∧
      CoefficientReductionPresentation l E X SX.toCoefficientDerivedSystemReduction
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) hJQ.1 D eD κD ∧
      AugmentedPresentation l E X SX
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) D eD κD ∧
      (r.hom.app (DerivedCategory.Q.obj Q) ≫ (J l E j o).map eC.hom ≫
        (systemExtension l E j o).mapDerivedCategoryFactors.hom.app C =
      SX.reduction.map ((extension l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        eD.hom ≫ DerivedCategory.Q.map f.hom) ∧
      (∀ (n : ℕ) (i : ℤ),
        (coefficientSequenceEvaluation l E X n).map (f.hom.f i) ≫
          (extensionEvaluation l E j o n).hom.app (C.X i) ≫
          (finiteExtension l E j o n).map ((κC n).hom.f i) =
        (κD n).hom.f i ≫ (tensor.ordinary n).hom.app (Q.X i)))
    (s : star l E j o ⋙ SU.reduction ⟶ SX.reduction ⋙ P l E j o)
    (hs : (∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : integralOperationsGoodComplex l E X Q),
    ∃ (hRes : integralOperationsGoodComplex l E U
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (CX : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (CU : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (eX : SX.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj CX)
      (eU : SU.reduction.obj (DerivedCategory.Q.obj
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q)) ≅ DerivedCategory.Q.obj CU)
      (κX : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj CX ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κU : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E U n).mapHomologicalComplex (.up ℤ)).obj CU ≅
          ((scalarReductionExtension l E U n).mapHomologicalComplex (.up ℤ)).obj
            (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (f : CU ≅ ((systemRestriction l E j o).mapHomologicalComplex (.up ℤ)).obj CX),
      CoefficientReductionPresentation l E X SX.toCoefficientDerivedSystemReduction
        Q hQ.1 CX eX κX ∧
      AugmentedPresentation l E X SX Q CX eX κX ∧
      CoefficientReductionPresentation l E U SU.toCoefficientDerivedSystemReduction
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) hRes.1 CU eU κU ∧
      AugmentedPresentation l E U SU
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) CU eU κU ∧
      (SU.reduction.map ((restriction l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        eU.hom ≫ DerivedCategory.Q.map f.hom =
      s.app (DerivedCategory.Q.obj Q) ≫ (P l E j o).map eX.hom ≫
        (systemRestriction l E j o).mapDerivedCategoryFactors.hom.app CX) ∧
      (∀ (n : ℕ) (i : ℤ),
        (coefficientSequenceEvaluation l E U n).map (f.hom.f i) ≫
          ((o.finite n).unitIso.app _ ≪≫
    (o.finite n).inverse.mapIso
      ((o.transportEvaluation n).app ((systemRestriction l E j o).obj (CX.X i))).symm ≪≫
    (o.finite n).inverse.mapIso
      ((SemilinearSections.evaluation.{t+1, t, max u (t+1)}
        ((ProEt.topology X).over (openObject j))
        (fun k ↦ (rings l E X k).over (openObject j))
        (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
          (openObject j)).map (transitions l E X k)) n).mapIso
        (o.systems.counitIso.app _)) ≪≫
    (o.finite n).inverse.mapIso ((o.openSystems.restrictionEvaluation n).app (CX.X i))).hom ≫
          (finiteRestriction l E j o n).map ((κX n).hom.f i) =
        (κU n).hom.f i ≫ (((o.finite n).toAdjunction.comp
          (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
            (rings l E X n) (openObject j))).unit.app _ ≫
    (finiteRestriction l E j o n).map
      ((tensor.ordinary n).inv.app ((restriction l E j o).obj (Q.X i))) ≫
    (finiteRestriction l E j o n).map
      ((scalarReductionExtension l E X n).map
        ((ordinaryAdjunction l E j o).counit.app (Q.X i))))))) :
    ∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ),
      integralOperationsGoodComplex l E X Q →
        (J l E j o).map (s.app (DerivedCategory.Q.obj Q)) ≫
          (systemAdjunction l E j o).counit.app
            (SX.reduction.obj (DerivedCategory.Q.obj Q)) =
        r.inv.app ((star l E j o).obj (DerivedCategory.Q.obj Q)) ≫
          SX.reduction.map ((openAdjunction l E j o).counit.app
            (DerivedCategory.Q.obj Q)) := by
  intro Q hQ
  let JF : coefficientSequenceModules l E U ⥤ coefficientSequenceModules l E X :=
    systemExtension l E j o
  let PF : coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E U :=
    systemRestriction l E j o
  have : JF.Additive := (inferInstance : (systemExtension l E j o).Additive)
  have : PF.Additive := (inferInstance : (systemRestriction l E j o).Additive)
  have : PreservesFiniteLimits JF :=
    (inferInstance : PreservesFiniteLimits (systemExtension l E j o))
  have : PreservesFiniteColimits JF :=
    (inferInstance : PreservesFiniteColimits (systemExtension l E j o))
  have : PreservesFiniteLimits PF :=
    (inferInstance : PreservesFiniteLimits (systemRestriction l E j o))
  have : PreservesFiniteColimits PF :=
    (inferInstance : PreservesFiniteColimits (systemRestriction l E j o))
  let aSys : JF ⊣ PF := ordinarySystemAdjunction l E j o
  obtain ⟨hRes, CX, CU, eX, eU, κX, κU, fU, hX, aX, hU, aU, hsQ, hsfin⟩ := hs Q hQ
  let R := ((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q
  obtain ⟨hExt, C, D, eC, eD, κC, κD, fD, hC, aC, hD, aD, hrQ, hrfin⟩ := hr R hRes
  obtain ⟨k, hk⟩ := strictReductionPresentationMap l E U R R C CU κC κU
    hC.2 hU.2 (𝟙 R)
  have hke := augmentedReductionNaturality l E U SU R R C CU eC eU κC κU
    aC aU (𝟙 R) k hk
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hke
  let ε : ((extension l E j o).mapHomologicalComplex (.up ℤ)).obj R ⟶ Q :=
    ((ordinaryAdjunction l E j o).mapHomologicalComplex (.up ℤ)).counit.app Q
  obtain ⟨c, hc⟩ := strictReductionPresentationMap l E X _ Q D CX κD κX hD.2 hX.2 ε
  have hce := augmentedReductionNaturality l E X SX _ Q D CX eD eX κD κX
    aD aX ε c hc
  let εS : (JF.mapHomologicalComplex (.up ℤ)).obj
      ((PF.mapHomologicalComplex (.up ℤ)).obj CX) ⟶ CX :=
    (aSys.mapHomologicalComplex (.up ℤ)).counit.app CX
  have hstrict : fD.hom ≫
      (JF.mapHomologicalComplex (.up ℤ)).map k ≫
      (JF.mapHomologicalComplex (.up ℤ)).map fU.hom ≫ εS = c := by
    apply HomologicalComplex.hom_ext
    intro i
    apply system_hom_ext l E
    intro n
    let evX := coefficientSequenceEvaluation l E X n
    let evU := coefficientSequenceEvaluation l E U n
    let sx := scalarReductionExtension l E X n
    let su := scalarReductionExtension l E U n
    let F : normalizedDVRModules l E U n ⥤ normalizedDVRModules l E X n :=
      finiteExtension l E j o n
    let G : normalizedDVRModules l E X n ⥤ normalizedDVRModules l E U n :=
      finiteRestriction l E j o n
    let adj := (o.finite n).toAdjunction.comp
      (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
        (rings l E X n) (openObject j))
    let κCn : evU.obj (C.X i) ≅ su.obj (R.X i) :=
      (HomologicalComplex.eval _ _ i).mapIso (κC n)
    let κUn : evU.obj (CU.X i) ≅ su.obj (R.X i) :=
      (HomologicalComplex.eval _ _ i).mapIso (κU n)
    let κXn : evX.obj (CX.X i) ≅ sx.obj (Q.X i) :=
      (HomologicalComplex.eval _ _ i).mapIso (κX n)
    let κDn : evX.obj (D.X i) ≅ sx.obj ((extension l E j o).obj (R.X i)) :=
      (HomologicalComplex.eval _ _ i).mapIso (κD n)
    let fd : D.X i ⟶ JF.obj (C.X i) := fD.hom.f i
    let fk : C.X i ⟶ CU.X i := k.f i
    let fu : CU.X i ⟶ PF.obj (CX.X i) := fU.hom.f i
    let η : JF ⋙ evX ≅ evU ⋙ F := extensionEvaluation l E j o n
    let ρ : evU.obj (PF.obj (CX.X i)) ≅ G.obj (evX.obj (CX.X i)) :=
      counitRestrictionEvaluation l E j o n (CX.X i)
    let a := evX.map fd ≫ η.hom.app (C.X i)
    let b := evU.map fu ≫ ρ.hom
    let q : sx.obj ((extension l E j o).obj (R.X i)) ⟶ sx.obj (Q.X i) :=
      sx.map ((ordinaryAdjunction l E j o).counit.app (Q.X i))
    have hkn : evU.map fk ≫ κUn.hom = κCn.hom := by
      have hh := hk n i
      change evU.map fk ≫ κUn.hom = κCn.hom ≫ su.map (𝟙 (R.X i)) at hh
      simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hh
    have han : a ≫ F.map κCn.hom = κDn.hom ≫
        (tensor.ordinary n).hom.app (R.X i) := hrfin n i
    have hbn : b ≫ G.map κXn.hom =
        κUn.hom ≫ adj.unit.app _ ≫
          G.map ((tensor.ordinary n).inv.app (R.X i)) ≫ G.map q := hsfin n i
    have hfn := finiteCounit_calculation adj κCn κUn κXn κDn
      ((tensor.ordinary n).app (R.X i)) a (evU.map fk) b q han hkn hbn
    have hε : evX.map (aSys.counit.app (CX.X i)) =
        η.hom.app (PF.obj (CX.X i)) ≫ F.map ρ.hom ≫
          adj.counit.app (evX.obj (CX.X i)) := by
      exact (Iso.inv_comp_eq (η.app (PF.obj (CX.X i)))).1
        (openSystemCounitEvaluation l E j o n (CX.X i)).symm
    have hcn : evX.map (c.f i) ≫ κXn.hom = κDn.hom ≫ q := hc n i
    apply (cancel_mono κXn.hom).1
    change evX.map (fd ≫ JF.map fk ≫ JF.map fu ≫
      aSys.counit.app (CX.X i)) ≫ κXn.hom = evX.map (c.f i) ≫ κXn.hom
    exact (congrArg (fun f ↦ f ≫ κXn.hom)
      (finiteCounit_evaluation_chain η fd fk fu
        (aSys.counit.app (CX.X i)) ρ.hom _ hε)).trans (hfn.trans hcn.symm)
  exact derivedCounit_calculation SU.reduction SX.reduction r s
    (openAdjunction l E j o).counit (systemAdjunction l E j o).counit
    (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj R))
    (DerivedCategory.Q.obj R)
    ((restriction l E j o).mapDerivedCategoryFactors.hom.app Q)
    ((extension l E j o).mapDerivedCategoryFactors.hom.app R)
    (DerivedCategory.Q.map ε) eC eU eD eX (DerivedCategory.Q.map k)
    (DerivedCategory.Q.map fU.hom) (PF.mapDerivedCategoryFactors.hom.app CX)
    (JF.mapDerivedCategoryFactors.hom.app C) (JF.mapDerivedCategoryFactors.hom.app CU)
    (JF.mapDerivedCategoryFactors.hom.app
      ((PF.mapHomologicalComplex (.up ℤ)).obj CX))
    (DerivedCategory.Q.map fD.hom)
    (DerivedCategory.Q.map ((JF.mapHomologicalComplex (.up ℤ)).map k))
    (DerivedCategory.Q.map ((JF.mapHomologicalComplex (.up ℤ)).map fU.hom))
    (DerivedCategory.Q.map εS) (DerivedCategory.Q.map c)
    (exactCounit_model (ordinaryAdjunction l E j o) Q)
    (exactCounit_model aSys CX) hke hce hrQ hsQ
    (JF.mapDerivedCategoryFactors.hom.naturality k)
    (JF.mapDerivedCategoryFactors.hom.naturality fU.hom)
    (mapped_chain_equality DerivedCategory.Q _ _ _ _ _ hstrict)

end WeilConjectures.CanonicalOpenRestriction
