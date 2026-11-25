/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonPasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import all WeilConjectures.CategoryTheory.Cochain.CochainInverseMateComparison
import all WeilConjectures.CategoryTheory.Derived.DerivedMateUnitComparison

/-! # Open scalar mates on strict coefficient systems

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory WeilConjectures.integralComparisonSequenceScalarModel

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FrobeniusExchange

/-- A morphism of sheaves of modules whose section maps are bijective is invertible. -/
theorem sheafOfModules_isIso_of_bijective {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Sheaf J RingCat}
    {M N : SheafOfModules A} (f : M ⟶ N)
    (hf : ∀ U, Function.Bijective (f.val.app U)) : IsIso f := by
  have : IsIso ((PresheafOfModules.toPresheaf A.obj).map f.val) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact hf U
  have : IsIso ((SheafOfModules.forget A).map f) := by
    change IsIso f.val
    exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf A.obj)
  exact isIso_of_reflects_iso f (SheafOfModules.forget A)

/-- Inverse mates are invertible independently of the chosen left adjoints. -/
theorem inverseMate_isIso_of_left_adjoints
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (b₁ : L₁' ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₂ : L₂' ⊣ R₂)
    (w : TwoSquare R₁ H G R₂)
    [IsIso ((mateEquiv b₁ b₂).symm w)] :
    IsIso ((mateEquiv a₁ a₂).symm w) := by
  have hw : (mateEquiv a₁ a₂).symm w = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G (a₂.leftAdjointUniq b₂).hom ≫
        ((mateEquiv b₁ b₂).symm w) ≫
          Functor.whiskerRight (a₁.leftAdjointUniq b₁).inv H) := by
    apply (mateEquiv a₁ a₂).injective
    rw [Equiv.apply_symm_apply, mateEquiv_leftAdjointUniq, Equiv.apply_symm_apply]
  rw [hw]
  dsimp only [TwoSquare.mk]
  apply IsIso.comp_isIso'
  · exact (Functor.isoWhiskerLeft G (a₂.leftAdjointUniq b₂)).isIso_hom
  · apply IsIso.comp_isIso'
    · infer_instance
    · exact (Functor.isoWhiskerRight (a₁.leftAdjointUniq b₁).symm H).isIso_hom

/-- Cancel the outer factors of an equality between composites of isomorphisms. -/
private theorem inverse_square_factors
    {C : Type*} [Category C] {A B D E F G : C}
    (q : A ≅ B) (i : B ≅ D) (r : D ≅ E) (g : A ≅ F) (s : F ≅ G) (t : G ≅ E)
    (h : q.hom ≫ i.hom ≫ r.hom = g.hom ≫ s.hom ≫ t.hom) :
    i.inv ≫ q.inv ≫ g.hom = r.hom ≫ t.inv ≫ s.inv := by
  apply (cancel_mono (s.hom ≫ t.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

section Ordinary

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ordinary restriction of scalars along the quotient coefficient map. -/
abbrev sequenceRestriction (X : Scheme.{u}) :=
  SheafOfModules.restrictScalars.{u + 1} ((sheafCompose
    (coefficientSequenceTopology (ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralComparisonSequenceScalarMap l E L ι X))

/-- The coefficient rings of the sequence site. -/
abbrev sequenceRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The quotient transitions of the sequence site. -/
abbrev sequenceQuotient (n : ℕ) : sequenceRings l E (n + 1) ⟶ sequenceRings l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift

/-- The ordinary restriction/pullback comparison: the inverse-image mate of the
identity-on-sections restriction/direct-image square.
Source: Stacks 03D3 and 06YY. -/
private def sequenceRestrictionPullbackInv {X B : Scheme.{u}} (j : X ⟶ B) :
    sequenceRestriction l E L ι B ⋙ integralComparisonSequencePullback l E j ⟶
      integralComparisonSequencePullback l L j ⋙ sequenceRestriction l E L ι X :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L j))
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E j))).symm
    (TwoSquare.mk _ _ _ _ (sequenceScalarPullbackRight l E L ι j).inv))

section OpenRestriction

open AlgebraicGeometry.ProEtale.VaryingRing

attribute [local instance] openMapContinuous prodOpenContinuous

/-- The open restriction mate is the identity on sections. -/
private theorem openRestrictionMate_app_apply {X B : Scheme.{u}} (j : X ⟶ B)
    [IsOpenImmersion j] (M : coefficientSequenceModules l L B) (U : (ℕ × X.ProEt)ᵒᵖ)
    (x : M.val.obj (op (((𝟭 ℕ).prod (openMap j)).obj U.unop))) :
    ((((mateEquiv (openPullAdj (sequenceRings l L) (sequenceQuotient l L) j)
        (openPullAdj (sequenceRings l E) (sequenceQuotient l E) j)).symm
        (TwoSquare.mk _ _ _ _ (sequenceScalarPullbackRight l E L ι j).inv)).app
          M).val.app U) x = x := by
  change M.val.presheaf.map (((𝟭 ℕ).prod (openMap j)).map
      ((prodAdj (openAdj j)).unit.app U.unop)).op
    (M.val.presheaf.map ((prodAdj (openAdj j)).counit.app
      (((𝟭 ℕ).prod (openMap j)).obj U.unop)).op x) = x
  have ht : ((prodAdj (openAdj j)).counit.app (((𝟭 ℕ).prod (openMap j)).obj U.unop)).op ≫
      (((𝟭 ℕ).prod (openMap j)).map ((prodAdj (openAdj j)).unit.app U.unop)).op = 𝟙 _ := by
    rw [← op_comp]
    exact (congrArg Quiver.Hom.op
      ((prodAdj (openAdj j)).left_triangle_components U.unop)).trans op_id
  have hm := M.val.presheaf.map_comp
    ((prodAdj (openAdj j)).counit.app (((𝟭 ℕ).prod (openMap j)).obj U.unop)).op
    (((𝟭 ℕ).prod (openMap j)).map ((prodAdj (openAdj j)).unit.app U.unop)).op
  rw [ht, M.val.presheaf.map_id] at hm
  exact (ConcreteCategory.congr_hom hm x).symm

private theorem openRestrictionMate_isIso {X B : Scheme.{u}} (j : X ⟶ B)
    [IsOpenImmersion j] :
    IsIso ((mateEquiv (openPullAdj (sequenceRings l L) (sequenceQuotient l L) j)
      (openPullAdj (sequenceRings l E) (sequenceQuotient l E) j)).symm
      (TwoSquare.mk _ _ _ _ (sequenceScalarPullbackRight l E L ι j).inv)) := by
  have h (M : coefficientSequenceModules l L B) :
      IsIso (((mateEquiv (openPullAdj (sequenceRings l L) (sequenceQuotient l L) j)
        (openPullAdj (sequenceRings l E) (sequenceQuotient l E) j)).symm
        (TwoSquare.mk _ _ _ _ (sequenceScalarPullbackRight l E L ι j).inv)).app M) := by
    apply sheafOfModules_isIso_of_bijective
    intro U
    have key := openRestrictionMate_app_apply l E L ι j M U
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨y, key y⟩⟩
    exact (key x).symm.trans (hxy.trans (key y))
  exact NatIso.isIso_of_isIso_app _

end OpenRestriction

/-- The sectionwise argument with the sequence direct-image functors fixed explicitly. -/
private theorem sequenceOpenRestrictionMate_isIso {X B : Scheme.{u}} (j : X ⟶ B)
    [IsOpenImmersion j] :
    IsIso ((mateEquiv
      (R₁ := integralComparisonSequenceDirectImage l L j)
      (R₂ := integralComparisonSequenceDirectImage l E j)
      (AlgebraicGeometry.ProEtale.VaryingRing.openPullAdj (sequenceRings l L)
        (sequenceQuotient l L) j)
      (AlgebraicGeometry.ProEtale.VaryingRing.openPullAdj (sequenceRings l E)
        (sequenceQuotient l E) j)).symm
      (TwoSquare.mk _ _ _ _ (sequenceScalarPullbackRight l E L ι j).inv)) := by
  have h (M : coefficientSequenceModules l L B) : IsIso
      (((mateEquiv
        (R₁ := integralComparisonSequenceDirectImage l L j)
        (R₂ := integralComparisonSequenceDirectImage l E j)
        (AlgebraicGeometry.ProEtale.VaryingRing.openPullAdj (sequenceRings l L)
          (sequenceQuotient l L) j)
        (AlgebraicGeometry.ProEtale.VaryingRing.openPullAdj (sequenceRings l E)
          (sequenceQuotient l E) j)).symm
        (TwoSquare.mk _ _ _ _ (sequenceScalarPullbackRight l E L ι j).inv)).app M) := by
    apply sheafOfModules_isIso_of_bijective
    intro U
    have key := openRestrictionMate_app_apply l E L ι j M U
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨y, key y⟩⟩
    exact (key x).symm.trans (hxy.trans (key y))
  exact NatIso.isIso_of_isIso_app _

/-- The ordinary restriction/pullback comparison is invertible for an open immersion. -/
private theorem sequenceRestrictionPullbackInv_isIso {X B : Scheme.{u}} (j : X ⟶ B)
    [IsOpenImmersion j] : IsIso (sequenceRestrictionPullbackInv l E L ι j) := by
  have := sequenceOpenRestrictionMate_isIso l E L ι j
  exact inverseMate_isIso_of_left_adjoints
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L j))
    (AlgebraicGeometry.ProEtale.VaryingRing.openPullAdj (sequenceRings l L)
      (sequenceQuotient l L) j)
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E j))
    (AlgebraicGeometry.ProEtale.VaryingRing.openPullAdj (sequenceRings l E)
      (sequenceQuotient l E) j)
    (TwoSquare.mk _ _ _ _ (sequenceScalarPullbackRight l E L ι j).inv)

/-- The normalized adjoint comparison is the conjugate of the given isomorphism. -/
private theorem normalizedAdjointComparison_choose_eq
    {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) (R T : B ⥤ A)
    (adj₁ : F ⊣ R) (adj₂ : G ⊣ T) (e : R ≅ T) :
    (normalizedAdjointComparison F G R T adj₁ adj₂ e).choose =
      (conjugateIsoEquiv adj₂ adj₁).symm e.symm :=
  ((normalizedAdjointComparison F G R T adj₁ adj₂ e).choose_spec.2 _
    (fun X ↦ unit_conjugateEquiv_symm adj₂ adj₁ e.inv X)).symm

-- elaborating the mate of the restriction adjunction is slow
/-- The ordinary scalar/pullback comparison is the scalar mate of the
restriction/pullback comparison. -/
private theorem sequenceScalarPullback_hom_eq {X B : Scheme.{u}} (j : X ⟶ B) :
    (integralComparisonSequenceScalarPullback l E L ι j).hom =
      ((mateEquiv (sequenceScalarAdjunction l E L ι B).choose
        (sequenceScalarAdjunction l E L ι X).choose).symm
        (TwoSquare.mk (sequenceRestriction l E L ι B) (integralComparisonSequencePullback l L j)
          (integralComparisonSequencePullback l E j) (sequenceRestriction l E L ι X)
          (sequenceRestrictionPullbackInv l E L ι j))) := by
  let adjY := (sequenceScalarAdjunction l E L ι B).choose
  have hY := sequenceScalarAdjunction_unit l E L ι B
  let adjZ := (sequenceScalarAdjunction l E L ι X).choose
  have hZ := sequenceScalarAdjunction_unit l E L ι X
  let pE := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E j)
  let pL := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L j)
  let adj₁ := pE.comp adjZ
  let adj₂ := adjY.comp pL
  let e := sequenceScalarPullbackRight l E L ι j
  let h := normalizedAdjointComparison _ _ _ _ adj₁ adj₂ e
  have hunit := h.choose_spec.1
  have ha (N : coefficientSequenceModules l E B) (n : ℕ) (U : B.ProEt)
      (x : N.val.obj (op (n, U))) :
      (h.choose.hom.app N).val.app (op (n, (proEtaleBaseChange j).obj U))
        (integralComparisonSequenceTensorSection l E L ι X
          ((integralComparisonSequencePullback l E j).obj N)
          (op (n, (proEtaleBaseChange j).obj U)) 1
          (integralComparisonSequenceGenerator l E j N n U x)) =
        integralComparisonSequenceGenerator l L j
          ((integralComparisonSequenceScalarModel l E L ι B).E.obj N) n U
          (integralComparisonSequenceTensorSection l E L ι B N (op (n, U)) 1 x) := by
    have hh := hunit N
    have hv := congrArg (fun q ↦ q.val.app (op (n, U)) x) hh
    dsimp only [Adjunction.comp_unit_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply] at hv
    change (e.inv.app _).val.app (op (n, U))
        ((pL.unit.app _).val.app (op (n, U))
          ((adjY.unit.app N).val.app (op (n, U)) x)) =
      (h.choose.hom.app N).val.app (op (n, (proEtaleBaseChange j).obj U))
        ((adjZ.unit.app _).val.app (op (n, (proEtaleBaseChange j).obj U))
          ((pE.unit.app N).val.app (op (n, U)) x)) at hv
    rw [sequenceScalarPullbackRight_inv_app, hY, hZ] at hv
    exact hv.symm
  have heq : integralComparisonSequenceScalarPullback l E L ι j = h.choose :=
    (integralComparisonSequenceScalarPullback_existsUnique l E L ι j).unique
      (integralComparisonSequenceScalarPullback_existsUnique l E L ι j).exists.choose_spec ha
  have hc : h.choose = (conjugateIsoEquiv adj₂ adj₁).symm e.symm :=
    normalizedAdjointComparison_choose_eq _ _ _ _ adj₁ adj₂ e
  rw [heq, hc]
  have hi := 
    (iterated_mateEquiv_conjugateEquiv_symm adjY adjZ pE pL (TwoSquare.mk _ _ _ _ e.inv))
  exact hi.symm


section Derived

/-- Natural transformations out of the derived system category are determined on
K-flat complexes. -/
private theorem sequenceDerived_kflat_ext (W : Scheme.{u}) {D : Type*} [Category D]
    {F G : coefficientSequenceDerived l E W ⥤ D} (α β : F ⟶ G)
    (h : ∀ P : CochainComplex (coefficientSequenceModules l E W) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) P →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  obtain ⟨P, r, hP, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) K
  let := hr
  apply (cancel_epi (F.map (DerivedCategory.Q.map r))).mp
  rw [α.naturality, β.naturality, h P hP]

/-- The derived scalar/pullback comparison is the derived scalar mate of the
restriction/pullback comparison, for any scalar models with normalized adjunctions. -/
private theorem systemScalarPullback_eq_mate {X B : Scheme.{u}} (j : X ⟶ B)
    (MB : type_of% (integralComparisonSequenceScalarModel l E L ι B))
    (MX : type_of% (integralComparisonSequenceScalarModel l E L ι X))
    (hAB : ∃ A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (integralComparisonSequenceScalarMap l E L ι B), A.model = MB)
    (hAX : ∃ A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (integralComparisonSequenceScalarMap l E L ι X), A.model = MX)
    (oB : MB.E ⊣ sequenceRestriction l E L ι B) (oX : MX.E ⊣ sequenceRestriction l E L ι X)
    (huB : ∀ P U x, (oB.unit.app P).val.app U x = SheafOfModules.systemModelTmul MB P U 1 x)
    (huX : ∀ P U x, (oX.unit.app P).val.app U x = SheafOfModules.systemModelTmul MX P U 1 x)
    (q : integralComparisonSequencePullback l L j ⋙ sequenceRestriction l E L ι X ≅
      sequenceRestriction l E L ι B ⋙ integralComparisonSequencePullback l E j)
    (a : integralComparisonSequencePullback l E j ⋙ MX.E ≅
      MB.E ⋙ integralComparisonSequencePullback l L j)
    (ha : a.hom = ((mateEquiv oB oX).symm (TwoSquare.mk _ _ _ _ q.inv)))
    (S : integralComparisonDerivedSequencePullback l E j ⋙ MX.T ≅
      MB.T ⋙ integralComparisonDerivedSequencePullback l L j)
    (hS : ∀ (P : CochainComplex (coefficientSequenceModules l E B) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E B) P →
      MX.T.map ((integralComparisonSequencePullback l E j).mapDerivedCategoryFactors.hom.app P) ≫
        MX.ε.app (((integralComparisonSequencePullback l E j).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P) =
      S.hom.app (DerivedCategory.Q.obj P) ≫
        (integralComparisonDerivedSequencePullback l L j).map (MB.ε.app P) ≫
        (integralComparisonSequencePullback l L j).mapDerivedCategoryFactors.hom.app
          ((MB.E.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ (σB : MB.T ⊣ (sequenceRestriction l E L ι B).mapDerivedCategory)
      (σX : MX.T ⊣ (sequenceRestriction l E L ι X).mapDerivedCategory),
      S.hom = ((mateEquiv σB σX).symm (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso q).inv)) := by
  obtain ⟨AB, rfl⟩ := hAB
  obtain ⟨AX, rfl⟩ := hAX
  have hoB : oB.unit = AB.ordinaryAdj.unit := by
    ext P U x
    rw [huB, AB.unit_normalized]
  have hoX : oX.unit = AX.ordinaryAdj.unit := by
    ext P U x
    rw [huX, AX.unit_normalized]
  have hoB' : oB = AB.ordinaryAdj := Adjunction.ext hoB
  have hoX' : oX = AX.ordinaryAdj := Adjunction.ext hoX
  subst oB oX
  refine ⟨AB.adjunction, AX.adjunction, ?_⟩
  unfold integralComparisonDerivedSequencePullback at S hS ⊢
  apply sequenceDerived_kflat_ext l E B
  intro P hP
  have : IsIso (AB.model.ε.app P) := AB.model.computes P hP
  let K := (AB.model.E.mapHomologicalComplex (.up ℤ)).obj P
  apply (cancel_mono
    ((integralComparisonSequencePullback l L j).mapDerivedCategory.map (AB.model.ε.app P) ≫
    (integralComparisonSequencePullback l L j).mapDerivedCategoryFactors.hom.app K)).1
  rw [← hS P hP]
  symm
  refine CategoryTheory.unitComparison_aux
    (AB.ordinaryAdj.mapHomologicalComplex (.up ℤ))
    (AX.ordinaryAdj.mapHomologicalComplex (.up ℤ)) AB.adjunction AX.adjunction
    AB.model.ε AX.model.ε
    (sequenceRestriction l E L ι B).mapDerivedCategoryFactors.inv
    (sequenceRestriction l E L ι X).mapDerivedCategoryFactors.inv
    (integralComparisonSequencePullback l E j).mapDerivedCategoryFactors
    (integralComparisonSequencePullback l L j).mapDerivedCategoryFactors
    AB.transpose AX.transpose
    (TwoSquare.mk _ _ _ _ (NatTrans.mapHomologicalComplex q.inv (.up ℤ)))
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso q).inv)
    ?_ (NatIso.mapHomologicalComplex a (.up ℤ)).hom ?_ P
  · intro K
    exact inverse_square_factors ((Functor.mapDerivedCategorySquareIso q).app
        (DerivedCategory.Q.obj K))
      ((integralComparisonSequencePullback l E j).mapDerivedCategory.mapIso
        ((sequenceRestriction l E L ι B).mapDerivedCategoryFactors.app K))
      ((integralComparisonSequencePullback l E j).mapDerivedCategoryFactors.app
        (((sequenceRestriction l E L ι B).mapHomologicalComplex (.up ℤ)).obj K))
      ((sequenceRestriction l E L ι X).mapDerivedCategory.mapIso
        ((integralComparisonSequencePullback l L j).mapDerivedCategoryFactors.app K))
      ((sequenceRestriction l E L ι X).mapDerivedCategoryFactors.app
        (((integralComparisonSequencePullback l L j).mapHomologicalComplex (.up ℤ)).obj K))
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex q (.up ℤ)).app K))
      (AlgebraicGeometry.Scheme.mapDerivedCategorySquareIso_hom_app_factors
        (integralComparisonSequencePullback l L j) (sequenceRestriction l E L ι X)
        (sequenceRestriction l E L ι B) (integralComparisonSequencePullback l E j) q K)
  · intro K
    have hc := CategoryTheory.cochainMate_unit AB.ordinaryAdj AX.ordinaryAdj q.inv K
    rw [← ha] at hc
    exact hc

end Derived

/-- The left mate of the system scalar/pullback comparison along any adjunctions of the
open restriction functors is invertible.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 06YY.
Proof: the ordinary scalar/pullback comparison is the scalar mate of the
restriction/pullback comparison, which is the identity on sections for an open
immersion. Localizing on K-flat complexes identifies the derived comparison with the
derived scalar mate of its localization. The iterated mate is then a conjugate of an
isomorphism. -/
theorem systemScalarPullback_leftMate_isIso {X B : Scheme.{u}} (j : X ⟶ B)
    [IsOpenImmersion j]
    {JE : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E B}
    {JL : coefficientSequenceDerived l L X ⥤ coefficientSequenceDerived l L B}
    (adjE : JE ⊣ integralComparisonDerivedSequencePullback l E j)
    (adjL : JL ⊣ integralComparisonDerivedSequencePullback l L j) :
    IsIso ((mateEquiv adjE adjL).symm (TwoSquare.mk _ _ _ _
      (integralComparisonSystemScalarPullback l E L ι j).hom)) := by
  have : IsIso (sequenceRestrictionPullbackInv l E L ι j) :=
    sequenceRestrictionPullbackInv_isIso l E L ι j
  let q := (asIso (sequenceRestrictionPullbackInv l E L ι j)).symm
  obtain ⟨σB, σX, hS⟩ := systemScalarPullback_eq_mate l E L ι j _ _
    (SequenceScalarProof.scalarPackageExists.{u + 1, u, u + 1} _ _)
    (SequenceScalarProof.scalarPackageExists.{u + 1, u, u + 1} _ _)
    (sequenceScalarAdjunction l E L ι B).choose (sequenceScalarAdjunction l E L ι X).choose
    (fun P U x ↦ (sequenceScalarAdjunction_unit l E L ι B P U x).trans
      (sequenceTensorSection_eq l E L ι B P U 1 x))
    (fun P U x ↦ (sequenceScalarAdjunction_unit l E L ι X P U x).trans
      (sequenceTensorSection_eq l E L ι X P U 1 x))
    q (integralComparisonSequenceScalarPullback l E L ι j)
    (sequenceScalarPullback_hom_eq l E L ι j)
    (integralComparisonSystemScalarPullback l E L ι j)
    (integralComparisonSystemScalarPullback_existsUnique l E L ι j).exists.choose_spec
  rw [hS]
  have h := (iterated_mateEquiv_conjugateEquiv_symm adjE adjL σX σB
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso q).inv))
  erw [h]
  change IsIso ((conjugateEquiv (adjE.comp σB) (σX.comp adjL)).symm
    (Functor.mapDerivedCategorySquareIso q).inv)
  infer_instance


end Ordinary

end WeilConjectures.FrobeniusExchange
