/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfFiniteOpenPresentation

/-! # Transport of the compact-support adjacent coefficient square

Source: Stacks Tags 03DI, 0E8I, 06YY and 0D6E; Bhatt--Scholze, Definition 6.7.6.
(blueprint: lem-sf-support-adjacent-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The level comparison is constructed by exact localization, direct image and restriction.
It uses a supplied finite comparison, and chooses no data from an existence theorem.
Source: Stacks 015F, 03DI (blueprint: lem-sf-support-adjacent-presentation). -/
def sfSupportPresentationLevel (c : Compactification f)
    (o : IntegralOpenReduction.Operations l E c.i)
    (d : CompactSupportProperImageTower.DirectData l E c.g)
    (ι : ∀ n : ℕ, IntegralOpenReduction.finiteExtension l E c.i o n ≅
      sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E (n + 1)))
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    CompactSupportProperImageTower.supportLevel l E c.i c.g o (d := d) K n ≅
      sfCompactSupportTerm l E c K n := by
  letI : (IntegralOpenReduction.finiteExtension l E c.i o n).Additive :=
    IntegralOpenReduction.finiteExtensionAdditive l E c.i o n
  letI : PreservesFiniteLimits (IntegralOpenReduction.finiteExtension l E c.i o n) := by
    dsimp only [IntegralOpenReduction.finiteExtension]
    infer_instance
  letI : PreservesFiniteColimits (IntegralOpenReduction.finiteExtension l E c.i o n) := by
    dsimp only [IntegralOpenReduction.finiteExtension]
    infer_instance
  letI : (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
    Functor.additive_of_iso (ι n)
  letI : PreservesFiniteLimits (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (n + 1))) :=
    preservesFiniteLimits_of_natIso (ι n)
  letI : PreservesFiniteColimits (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (n + 1))) :=
    preservesFiniteColimits_of_natIso (ι n)
  exact (coefficientFiniteDerivedRestriction l E Y n).mapIso
    ((compactSupportLevelDirectImage l E c.g n).rightDerivedFunctor.mapIso
      ((Functor.mapDerivedCategoryNatIso (ι n)).app
        ((coefficientFiniteDerivedExtension l E X n).obj K)))

attribute [local irreducible] scalarReductionDerivedExtension
  sfIntrinsicExtensionByZero completedIntegralCommRingSheafUnrestricted

private theorem quotientMate_change
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : A ⥤ C} {R' : C ⥤ A}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (S S' : C ⥤ B)
    (ρ : S ≅ S') (g : S ⋙ R ≅ R') (g' : S' ⋙ R ≅ R')
    (h : g = Functor.isoWhiskerRight ρ R ≪≫ g') (K : A) :
    (adj.homEquiv K _).symm
        (adj'.unit.app K ≫ g.inv.app (L'.obj K)) ≫ ρ.hom.app (L'.obj K) =
      (adj.homEquiv K _).symm (adj'.unit.app K ≫ g'.inv.app (L'.obj K)) := by
  apply (adj.homEquiv K _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Equiv.apply_symm_apply]
  rw [h]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Category.assoc, ← R.map_comp,
    Iso.inv_hom_id_app, R.map_id]
  erw [CategoryTheory.Category.comp_id]

private theorem scalarComp_eqToIso
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (hF : pbcRestrict ψ ⋙ pbcRestrict φ = pbcRestrict χ) :
    pbcRestrictComp φ ψ χ h = eqToIso hF := by
  subst χ
  change pbcRestrictComp φ ψ (φ ≫ ψ) rfl = Iso.refl _
  apply (pbcRestrictComp_exists φ ψ (φ ≫ ψ) rfl).unique
  · exact (pbcRestrictComp_exists φ ψ (φ ≫ ψ) rfl).exists.choose_spec
  · intro M U x
    rfl

private theorem eqIso_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F' : A ⥤ B} (G : B ⥤ C) {H : A ⥤ C}
    (h : F = F') (h' : F' ⋙ G = H) (h'' : F ⋙ G = H) :
    eqToIso h'' = Functor.isoWhiskerRight (eqToIso h) G ≪≫ eqToIso h' := by
  subst F'
  subst H
  apply Iso.ext
  ext X
  simp

private theorem derivedComp_change
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F F' : A ⥤ B} (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [F'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ F') (a : F ⋙ G ≅ H) (b : F' ⋙ G ≅ H)
    (h : a = Functor.isoWhiskerRight e G ≪≫ b) :
    Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso a =
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) G.mapDerivedCategory ≪≫
        Functor.mapDerivedCategoryCompIso F' G ≪≫
          Functor.mapDerivedCategoryNatIso b := by
  apply Iso.ext
  rw [h]
  simp only [Iso.trans_hom, Functor.mapDerivedCategoryNatIso_trans]
  have hc := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e G
  have hc' : (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e G)).hom =
      (Functor.mapDerivedCategoryCompIso F G).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom G.mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso F' G).hom := by
    rw [← reassoc_of% hc]
    simp only [Iso.inv_hom_id, Category.comp_id]
  rw [hc']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.isoWhiskerRight_hom]

private theorem restrictionComp (T : Scheme.{u}) (n : ℕ) :
    compactSupportSystemRestrictionComp l E T (Nat.le_succ n) =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso (sfFiniteOpenPresentationRestriction l E T n))
        (scalarReductionDerivedRestriction l E T (n + 1)) ≪≫
      sfCompactSupportDerivedRestrictionComp l E T n := by
  let h := sfFiniteOpenPresentation_restriction_eq l E T n
  let h₀ := coefficientRestrictionComp l E T (Nat.le_succ n)
  have h₁ : sfCompactSupportFiniteRestriction l E T n ⋙
      scalarReductionRestriction l E T (n + 1) = scalarReductionRestriction l E T n :=
    (congrArg (fun F ↦ F ⋙ scalarReductionRestriction l E T (n + 1)) h).symm.trans h₀
  have he : sfCompactSupportRestrictionComp l E T n = eqToIso h₁ := by
    apply scalarComp_eqToIso
  unfold compactSupportSystemRestrictionComp sfCompactSupportDerivedRestrictionComp
  rw [he]
  exact derivedComp_change _ _ _ _ _ (eqIso_comp _ h h₁ h₀)

private theorem reductionMap_change (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E T)) (n : ℕ) :
    CompactSupportProperImageTower.reductionMap l E T K n ≫
        (Functor.mapDerivedCategoryNatIso
          (sfFiniteOpenPresentationRestriction l E T n)).hom.app
            ((coefficientFiniteDerivedExtension l E T n).obj K) =
      sfCompactSupportReductionTransition l E T K n := by
  exact quotientMate_change (coefficientFiniteAdjunction l E T (n + 1))
    (coefficientFiniteAdjunction l E T n)
    (normalizedDVRRes l E T (Nat.le_succ n))
    (sfCompactSupportFiniteRestriction l E T n).mapDerivedCategory
    (Functor.mapDerivedCategoryNatIso (sfFiniteOpenPresentationRestriction l E T n))
    (compactSupportSystemRestrictionComp l E T (Nat.le_succ n))
    (sfCompactSupportDerivedRestrictionComp l E T n) (restrictionComp l E T n) K

private theorem derivedSquare_change
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F F' : A ⥤ B} {G G' : B ⥤ D} {H H' : A ⥤ C} {I I' : C ⥤ D}
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
    [H.Additive] [H'.Additive] [I.Additive] [I'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H') (eI : I ≅ I')
    (a : F ⋙ G ≅ H ⋙ I) (b : F' ⋙ G' ≅ H' ⋙ I')
    (h : Functor.isoWhiskerLeft F eG ≪≫ Functor.isoWhiskerRight eF G' ≪≫ b =
      a ≪≫ Functor.isoWhiskerRight eH I ≪≫ Functor.isoWhiskerLeft H' eI) :
    Functor.isoWhiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso eG) ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso eF) G'.mapDerivedCategory ≪≫
        Functor.mapDerivedCategorySquareIso b =
      Functor.mapDerivedCategorySquareIso a ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso eH) I.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft H'.mapDerivedCategory (Functor.mapDerivedCategoryNatIso eI) := by
  have hh := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) h
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hh
  have hFG := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F eG
  have hFG' := Functor.mapDerivedCategoryNatIso_isoWhiskerRight eF G'
  have hHI := Functor.mapDerivedCategoryNatIso_isoWhiskerRight eH I
  have hHI' := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft H' eI
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  apply (cancel_epi (Functor.mapDerivedCategoryCompIso F G).inv).mp
  apply (cancel_mono (Functor.mapDerivedCategoryCompIso H' I').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at *
  rw [← reassoc_of% hFG, ← reassoc_of% hFG', Iso.inv_hom_id_assoc, hh]
  rw [← reassoc_of% hHI, ← reassoc_of% hHI']
  simp only [Iso.inv_hom_id, Category.comp_id]

private theorem normalizedComparison_unique
    {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [HasDerivedCategory A] [HasDerivedCategory A']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']
    (G : A ⥤ B) (G' : A' ⥤ B') (H : A ⥤ A') (V : B ⥤ B')
    [G.Additive] [G'.Additive] [H.Additive] [V.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (a : H ⋙ G' ≅ G ⋙ V)
    (b c : H.mapDerivedCategory ⋙ G'.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ V.mapDerivedCategory)
    (hb : CompactSupportDerivedSquareNormalization G G' H V a b)
    (hc : CompactSupportDerivedSquareNormalization G G' H V a c) : b = c := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  let := hJ
  obtain ⟨I, hI, r, _, hr⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    ((H.mapHomologicalComplex (.up ℤ)).obj J)
  let := hI
  let := hr
  let t := V.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso J).hom ≫
    V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).inv.app J) ≫
    DerivedCategory.Q.map ((G'.mapHomologicalComplex (.up ℤ)).map r)
  have ht : IsIso (b.hom.app (DerivedCategory.Q.obj J) ≫ t) := by
    change IsIso (_ ≫ _ ≫ _ ≫ _ ≫ _)
    rw [hb J I r]
    infer_instance
  have : IsIso t := IsIso.of_isIso_comp_left (b.hom.app (DerivedCategory.Q.obj J)) t
  have he : b.hom.app (DerivedCategory.Q.obj J) = c.hom.app (DerivedCategory.Q.obj J) :=
    (cancel_mono t).mp ((hb J I r).trans (hc J I r).symm)
  apply (cancel_mono ((G.rightDerivedFunctor ⋙ V.mapDerivedCategory).map e.hom)).mp
  rw [← b.hom.naturality, ← c.hom.naturality, he]

private theorem normalizedComparison_change
    {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [HasDerivedCategory A] [HasDerivedCategory A']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']
    (G : A ⥤ B) (G' : A' ⥤ B') (H H' : A ⥤ A') (V V' : B ⥤ B')
    [G.Additive] [G'.Additive] [H.Additive] [H'.Additive] [V.Additive] [V'.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    (hH : H = H') (hV : V = V')
    (a : H ⋙ G' ≅ G ⋙ V) (a' : H' ⋙ G' ≅ G ⋙ V')
    (ha : Functor.isoWhiskerRight (eqToIso hH) G' ≪≫ a' =
      a ≪≫ Functor.isoWhiskerLeft G (eqToIso hV))
    (b : H.mapDerivedCategory ⋙ G'.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ V.mapDerivedCategory)
    (c : H'.mapDerivedCategory ⋙ G'.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ V'.mapDerivedCategory)
    (hb : CompactSupportDerivedSquareNormalization G G' H V a b)
    (hc : CompactSupportDerivedSquareNormalization G G' H' V' a' c)
    (M : DerivedCategory A) :
    G'.rightDerivedFunctor.map ((Functor.mapDerivedCategoryNatIso (eqToIso hH)).hom.app M) ≫
        c.hom.app M =
      b.hom.app M ≫ (Functor.mapDerivedCategoryNatIso (eqToIso hV)).hom.app
        (G.rightDerivedFunctor.obj M) := by
  subst H'
  subst V'
  have haa : a' = a := by simpa using ha
  subst a'
  have hbc := normalizedComparison_unique G G' H V a b c hb hc
  rw [hbc]
  simp only [eqToIso_refl, Functor.mapDerivedCategoryNatIso_refl, NatTrans.id_app]
  erw [G'.rightDerivedFunctor.map_id, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id]

private theorem ordinaryDirectComparison_change
    {Z T : Scheme.{u}} (p : Z ⟶ T) {A B : Type u}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (H : proEtaleRingModules Z (proEtaleConstantRing Z B) ⥤
      proEtaleRingModules Z (proEtaleConstantRing Z A))
    (V : proEtaleRingModules T (proEtaleConstantRing T B) ⥤
      proEtaleRingModules T (proEtaleConstantRing T A))
    (hH : H = proEtaleCoefficientRestrictScalars Z φ)
    (hV : V = proEtaleCoefficientRestrictScalars T φ)
    (a : H ⋙ proEtaleConstantModuleDirectImage p A ≅
      proEtaleConstantModuleDirectImage p B ⋙ V)
    (ha : ∀ (N : proEtaleRingModules Z (proEtaleConstantRing Z B)) (W : T.ProEtᵒᵖ),
      HEq (fun x ↦ (a.hom.app N).val.app W x)
        (fun x : N.val.obj ((proEtaleBaseChange p).op.obj W) ↦ x)) :
    Functor.isoWhiskerRight (eqToIso hH) (proEtaleConstantModuleDirectImage p A) ≪≫
        (proEtaleCoefficientDirectImageComparison p φ).symm =
      a ≪≫ Functor.isoWhiskerLeft (proEtaleConstantModuleDirectImage p B) (eqToIso hV) := by
  subst H
  subst V
  simp only [eqToIso_refl, Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl,
    Iso.refl_trans, Iso.trans_refl]
  apply Iso.ext
  apply (cancel_mono (proEtaleCoefficientDirectImageComparison p φ).hom).mp
  simp only [Iso.symm_hom, Iso.inv_hom_id]
  ext N W x
  change x = ((proEtaleCoefficientDirectImageComparison p φ).hom.app N).val.app W
    ((a.hom.app N).val.app W x)
  rw [congrFun (eq_of_heq (ha N W))]
  exact ((Classical.choose_spec
    (proEtaleCoefficientDirectImageComparison_existsUnique p φ)).1 N W x).symm

private theorem directComparison {Z T : Scheme.{u}} (p : Z ⟶ T)
    (d : CompactSupportProperImageTower.DirectData l E p) (n : ℕ)
    (M : normalizedDVRDerived l E Z n) :
    (compactSupportLevelDirectImage l E p (n + 1)).rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryNatIso
          (sfFiniteOpenPresentationRestriction l E Z n)).hom.app M) ≫
      (sfDerivedImageRestriction p (Padic.coefficientExtensionTransition l E (n + 1))).hom.app M =
    (d.comparison n).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        (sfFiniteOpenPresentationRestriction l E T n)).hom.app
          ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj M) := by
  let := d
  let a := proEtaleCoefficientDirectImageComparison p
    (Padic.coefficientExtensionTransition l E (n + 1))
  have ha : Functor.isoWhiskerRight (sfFiniteOpenPresentationRestriction l E Z n)
        (compactSupportLevelDirectImage l E p (n + 1)) ≪≫ a.symm =
      d.ordinary n ≪≫ Functor.isoWhiskerLeft (compactSupportLevelDirectImage l E p n)
        (sfFiniteOpenPresentationRestriction l E T n) := by
    exact ordinaryDirectComparison_change p
      (Padic.coefficientExtensionTransition l E (n + 1))
      (normalizedDVRModuleRes l E Z (Nat.le_succ n))
      (normalizedDVRModuleRes l E T (Nat.le_succ n))
      (sfFiniteOpenPresentation_restriction_eq l E Z n)
      (sfFiniteOpenPresentation_restriction_eq l E T n) (d.ordinary n) (d.sections n)
  apply normalizedComparison_change
    (compactSupportLevelDirectImage l E p n)
    (compactSupportLevelDirectImage l E p (n + 1))
    (normalizedDVRModuleRes l E Z (Nat.le_succ n))
    (sfCompactSupportFiniteRestriction l E Z n)
    (normalizedDVRModuleRes l E T (Nat.le_succ n))
    (sfCompactSupportFiniteRestriction l E T n)
    (sfFiniteOpenPresentation_restriction_eq l E Z n)
    (sfFiniteOpenPresentation_restriction_eq l E T n)
    (d.ordinary n) a.symm ha (d.comparison n)
    (sfDerivedImageRestriction p (Padic.coefficientExtensionTransition l E (n + 1)))
    (d.normalization n) _ M
  intro J hJ I hI r hr
  exact ((proEtaleDerivedDirectImage_restrictScalars p
    (Padic.coefficientExtensionTransition l E (n + 1))).choose_spec J I r).2

private theorem openSquare_transport
    {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    (S S' : A ⥤ A') (T T' : B ⥤ B')
    (F G : A ⥤ B) (F' G' : A' ⥤ B')
    (ρ : S ≅ S') (σ : T ≅ T') (e : F ≅ G) (e' : F' ≅ G')
    (a : S ⋙ F' ≅ F ⋙ T) (b : S' ⋙ G' ≅ G ⋙ T')
    (h : Functor.isoWhiskerLeft S e' ≪≫ Functor.isoWhiskerRight ρ G' ≪≫ b =
      a ≪≫ Functor.isoWhiskerRight e T ≪≫ Functor.isoWhiskerLeft G σ)
    (M : A) (N : A') (r : N ⟶ S.obj M) (r' : N ⟶ S'.obj M)
    (hr : r ≫ ρ.hom.app M = r') :
    (F'.map r ≫ a.hom.app M) ≫ σ.hom.app (F.obj M) ≫ T'.map (e.hom.app M) =
      e'.hom.app N ≫ (G'.map r' ≫ b.hom.app M) := by
  have hs := congrArg (fun i ↦ i.hom.app M) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hs
  have ht := σ.hom.naturality (e.hom.app M)
  simp only [Category.assoc] at hs ⊢
  rw [← ht, ← hs, reassoc_of% e'.hom.naturality r]
  rw [← hr]
  simp only [G'.map_comp, Category.assoc]

private theorem restrictedSquare
    {C C' D D' A : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category A]
    (S : C ⥤ C') (F : C ⥤ D) (F' : C' ⥤ D') (T : D ⥤ D')
    (R : D ⥤ A) (R' : D' ⥤ A)
    (c : S ⋙ F' ≅ F ⋙ T) (g : T ⋙ R' ≅ R)
    {M N : C} {M' N' : C'} (a : M' ⟶ S.obj M) (b : N' ⟶ S.obj N)
    (e : M ≅ N) (e' : M' ≅ N')
    (h : a ≫ S.map e.hom = e'.hom ≫ b) :
    R'.map (F'.map a ≫ c.hom.app M) ≫ g.hom.app (F.obj M) ≫ R.map (F.map e.hom) =
      R'.map (F'.map e'.hom) ≫
        R'.map (F'.map b ≫ c.hom.app N) ≫ g.hom.app (F.obj N) := by
  rw [← g.hom.naturality]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc, ← R'.map_comp]
  have hc := c.hom.naturality e.hom
  dsimp only [Functor.comp_map] at hc
  rw [Category.assoc, ← hc]
  rw [← Category.assoc, ← F'.map_comp, h, F'.map_comp]
  simp only [R'.map_comp, Category.assoc]

private theorem restrictedComparison
    {C C' D D' A : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category A]
    (S S' : C ⥤ C') (F : C ⥤ D) (F' : C' ⥤ D') (T T' : D ⥤ D')
    (R : D ⥤ A) (R' : D' ⥤ A) (ρ : S ≅ S') (σ : T ≅ T')
    (c : S ⋙ F' ≅ F ⋙ T) (c' : S' ⋙ F' ≅ F ⋙ T')
    (g : T ⋙ R' ≅ R) (g' : T' ⋙ R' ≅ R)
    (hc : ∀ M, F'.map (ρ.hom.app M) ≫ c'.hom.app M =
      c.hom.app M ≫ σ.hom.app (F.obj M))
    (hg : ∀ M, R'.map (σ.hom.app M) ≫ g'.hom.app M = g.hom.app M)
    {M N : C} {M' N' : C'} (a : M' ⟶ S.obj M) (b : N' ⟶ S'.obj N)
    (e : M ≅ N) (e' : M' ≅ N')
    (h : a ≫ ρ.hom.app M ≫ S'.map e.hom = e'.hom ≫ b) :
    R'.map (F'.map a ≫ c.hom.app M) ≫ g.hom.app (F.obj M) ≫ R.map (F.map e.hom) =
      R'.map (F'.map e'.hom) ≫
        R'.map (F'.map b ≫ c'.hom.app N) ≫ g'.hom.app (F.obj N) := by
  have ht : R'.map (F'.map a ≫ c.hom.app M) ≫ g.hom.app (F.obj M) =
      R'.map (F'.map (a ≫ ρ.hom.app M) ≫ c'.hom.app M) ≫
        g'.hom.app (F.obj M) := by
    rw [← hg]
    simpa only [R'.map_comp, F'.map_comp, Category.assoc] using
      congrArg (fun t ↦ R'.map (F'.map a) ≫ R'.map t ≫ g'.hom.app (F.obj M))
        (hc M).symm
  rw [← Category.assoc, ht]
  simpa only [Category.assoc] using
    restrictedSquare S' F F' T' R R' c' g' (a ≫ ρ.hom.app M) b e e'
      (by simpa only [Category.assoc] using h)

/-- The constructed level comparisons commute with one adjacent support arrow.
The hypothesis is the ordinary finite open square, before either derivation or direct
image. The conclusion is an equality of specified morphisms, with no inverse-system
existence conclusion and no completeness hypothesis on K.

Source: Stacks Tags 03DI, 0E8I, 06YY, 0D6E and 015F; Bhatt--Scholze, Definition 6.7.6.
(blueprint: lem-sf-support-adjacent-presentation).

Proof: apply exact derived localization to the finite coefficient square hι. Its
localization factors identify it with the square between openRestriction and the
specified sfOpenRestriction. Naturality of the derived comparison ι at reductionMap
then commutes extension with quotient reduction. The adjunct defining reductionMap
is the same as sfCompactSupportReductionTransition: both use the published scalar
adjunction, its lower unit, and the identity-on-sections restriction associator.
The two restriction associators agree after the quotient identification
sfFiniteOpenPresentation_restriction_eq, since their ordinary maps preserve every
section; exact localization preserves this equality. Apply the higher finite
right-derived direct image. Its normalized scalar square d.comparison agrees with
sfDerivedImageRestriction after the same coefficient identification: resolve a
K-injective representative after restriction and use the two normalization equations
on that resolution. This does not require preservation of K-injectives. Naturality
of that square at the localized ι moves the lower comparison past direct image.
Finally apply completed scalar restriction and its natural composition comparison.
Functoriality and associativity give exactly the displayed equality, including the
last restriction-composition map in sfCompactSupportTransition. The same equations
hold for the empty or identity open and for zero complexes. -/
theorem sfSupportTransition_presentation
    (c : Compactification f) (o : IntegralOpenReduction.Operations l E c.i)
    (d : CompactSupportProperImageTower.DirectData l E c.g)
    (e : CompactSupportProperImageTower.OpenData l E c.i o)
    (ι : ∀ n : ℕ, IntegralOpenReduction.finiteExtension l E c.i o n ≅
      sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E (n + 1)))
    (hι : SfFiniteOpenPresentationCompatible l E c.i o e ι)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    CompactSupportProperImageTower.supportTransition l E c.i c.g o (d := d) e K n ≫
        (sfSupportPresentationLevel l E c o d ι K n).hom =
      (sfSupportPresentationLevel l E c o d ι K (n + 1)).hom ≫
        sfCompactSupportTransition l E c K n := by
  let instFiniteAdditive (m : ℕ) : (IntegralOpenReduction.finiteExtension l E c.i o m).Additive :=
    IntegralOpenReduction.finiteExtensionAdditive l E c.i o m
  let instFiniteLimits (m : ℕ) :
      PreservesFiniteLimits (IntegralOpenReduction.finiteExtension l E c.i o m) :=
    compactSupportFiniteExtensionPreservesFiniteLimits l E c.i o m
  let instFiniteColimits (m : ℕ) :
      PreservesFiniteColimits (IntegralOpenReduction.finiteExtension l E c.i o m) :=
    compactSupportFiniteExtensionPreservesFiniteColimits l E c.i o m
  let instIntrinsicAdditive (m : ℕ) : (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (m + 1))).Additive :=
    Functor.additive_of_iso (ι m)
  let instIntrinsicLimits (m : ℕ) : PreservesFiniteLimits (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (m + 1))) :=
    preservesFiniteLimits_of_natIso (ι m)
  let instIntrinsicColimits (m : ℕ) : PreservesFiniteColimits (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (m + 1))) :=
    preservesFiniteColimits_of_natIso (ι m)
  let instRestrictionLimits (T : Scheme.{u}) :
      PreservesFiniteLimits (normalizedDVRModuleRes l E T (Nat.le_succ n)) :=
    normalizedDVRModuleRes_limits l E T (Nat.le_succ n)
  let instRestrictionColimits (T : Scheme.{u}) :
      PreservesFiniteColimits (normalizedDVRModuleRes l E T (Nat.le_succ n)) :=
    normalizedDVRModuleRes_colimits l E T (Nat.le_succ n)
  let ρX := Functor.mapDerivedCategoryNatIso (sfFiniteOpenPresentationRestriction l E X n)
  let ρZ := Functor.mapDerivedCategoryNatIso (sfFiniteOpenPresentationRestriction l E c.Z n)
  let ρY := Functor.mapDerivedCategoryNatIso (sfFiniteOpenPresentationRestriction l E Y n)
  let β (m : ℕ) := (Functor.mapDerivedCategoryNatIso (ι m)).app
    ((coefficientFiniteDerivedExtension l E X m).obj K)
  let a := (compactSupportCanonicalJLevel l E c.i o (n + 1)).map
      (CompactSupportProperImageTower.reductionMap l E X K n) ≫
    (CompactSupportProperImageTower.openRestriction l E c.i o e n).hom.app
      ((coefficientFiniteDerivedExtension l E X n).obj K)
  let b := (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (n + 2))).mapDerivedCategory.map
        (sfCompactSupportReductionTransition l E X K n) ≫
    (Functor.mapDerivedCategorySquareIso
      (sfOpenRestriction c.i (Padic.coefficientExtensionTransition l E (n + 1)))).hom.app
        ((coefficientFiniteDerivedExtension l E X n).obj K)
  have hs := derivedSquare_change
    (sfFiniteOpenPresentationRestriction l E X n) (ι (n + 1)) (ι n)
    (sfFiniteOpenPresentationRestriction l E c.Z n) (e.ordinary n)
    (sfOpenRestriction c.i (Padic.coefficientExtensionTransition l E (n + 1))) (hι n)
  have ho : a ≫ ρZ.hom.app _ ≫
        (sfCompactSupportFiniteRestriction l E c.Z n).mapDerivedCategory.map (β n).hom =
      (β (n + 1)).hom ≫ b := by
    exact openSquare_transport _ _ _ _ _ _ _ _ ρX ρZ
      (Functor.mapDerivedCategoryNatIso (ι n))
      (Functor.mapDerivedCategoryNatIso (ι (n + 1)))
      (CompactSupportProperImageTower.openRestriction l E c.i o e n)
      (Functor.mapDerivedCategorySquareIso
        (sfOpenRestriction c.i (Padic.coefficientExtensionTransition l E (n + 1)))) hs
      _ _ (CompactSupportProperImageTower.reductionMap l E X K n)
      (sfCompactSupportReductionTransition l E X K n) (reductionMap_change l E X K n)
  have hg (M : normalizedDVRDerived l E Y n) :
      (coefficientFiniteDerivedRestriction l E Y (n + 1)).map (ρY.hom.app M) ≫
        (sfCompactSupportDerivedRestrictionComp l E Y n).hom.app M =
      (compactSupportSystemRestrictionComp l E Y (Nat.le_succ n)).hom.app M := by
    simpa only [ρY, coefficientFiniteDerivedRestriction, normalizedDVRRes,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.comp_obj] using
      (congrArg (fun e ↦ e.hom.app M) (restrictionComp l E Y n)).symm
  have ht := restrictedComparison
    (normalizedDVRRes l E c.Z (Nat.le_succ n))
    (sfCompactSupportFiniteRestriction l E c.Z n).mapDerivedCategory
    (compactSupportLevelDirectImage l E c.g n).rightDerivedFunctor
    (compactSupportLevelDirectImage l E c.g (n + 1)).rightDerivedFunctor
    (normalizedDVRRes l E Y (Nat.le_succ n))
    (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory
    (coefficientFiniteDerivedRestriction l E Y n)
    (coefficientFiniteDerivedRestriction l E Y (n + 1)) ρZ ρY (d.comparison n)
    (sfDerivedImageRestriction c.g (Padic.coefficientExtensionTransition l E (n + 1)))
    (compactSupportSystemRestrictionComp l E Y (Nat.le_succ n))
    (sfCompactSupportDerivedRestrictionComp l E Y n)
    (directComparison l E c.g d n) hg a b (β n) (β (n + 1)) ho
  simp only [CompactSupportProperImageTower.supportTransition, sfSupportPresentationLevel,
    Functor.mapIso_hom, sfCompactSupportTransition, sfAmbientCompactSupportCandidate,
    sfCompactSupportRestriction, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc, a, b, β] at ht ⊢
  exact ht

end WeilConjectures
