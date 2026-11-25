/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalFiniteRealization
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalFiniteSupportProperComparison
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.InverseMateEquivalence
/-! # Compact-support realization of the actual finite adjunction
Source: blueprint theorem-f-shriek-finite-coefficients.
(blueprint: def-pur-adic-support-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
attribute [local instance 5000] strictEtaleLevelDerived strictEtaleSystemDerived
private theorem supportTransposeMate
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {F : C ⥤ C'} {G : D ⥤ D'} (a : L ⊣ R) (b : L' ⊣ R')
    (α : F ⋙ L' ⟶ L ⋙ G) (β : R ⋙ F ⟶ G ⋙ R')
    (hu : ∀ M, F.map (a.unit.app M) ≫ β.app (L.obj M) =
      b.unit.app (F.obj M) ≫ R'.map (α.app M))
    (M : C) (N : D) (h : L.obj M ⟶ N) :
    b.homEquiv _ _ (α.app M ≫ G.map h) =
      F.map (a.homEquiv _ _ h) ≫ β.app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn := β.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ R'.map (G.map h)) (hu M).symm

private theorem supportRightMate
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {F : C ⥤ C'} {G : D ⥤ D'} [F.IsEquivalence] [G.IsEquivalence]
    (a : L ⊣ R) (b : L' ⊣ R') (α : F ⋙ L' ≅ L ⋙ G) :
    ∃! e : R ⋙ F ≅ G ⋙ R', ∀ (M : C) (N : D) (h : L.obj M ⟶ N),
      b.homEquiv _ _ (α.hom.app M ≫ G.map h) =
        F.map (a.homEquiv _ _ h) ≫ e.hom.app N := by
  let β := (mateEquiv a b α.hom)
  have : IsIso β := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful a b F G α
  let e := asIso β
  have he : ∀ (M : C) (N : D) (h : L.obj M ⟶ N),
      b.homEquiv _ _ (α.hom.app M ≫ G.map h) =
        F.map (a.homEquiv _ _ h) ≫ e.hom.app N :=
    supportTransposeMate a b α.hom β (unit_mateEquiv a b α.hom)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext N
  have h := (he' (R.obj N) N (a.counit.app N)).symm.trans
    (he (R.obj N) N (a.counit.app N))
  simpa [Adjunction.homEquiv_unit, ← F.map_comp] using h

private theorem supportLeftMate
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {F : C ⥤ C'} {G : D ⥤ D'} [F.IsEquivalence] [G.IsEquivalence]
    (a : L ⊣ R) (b : L' ⊣ R') (β : R ⋙ F ≅ G ⋙ R') :
    ∃! e : L ⋙ G ≅ F ⋙ L', ∀ (M : C) (N : D) (h : L.obj M ⟶ N),
      b.homEquiv _ _ (e.inv.app M ≫ G.map h) =
        F.map (a.homEquiv _ _ h) ≫ β.hom.app N := by
  let α := ((mateEquiv a b).symm β.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences a b β
  let e := (asIso α).symm
  have he : ∀ (M : C) (N : D) (h : L.obj M ⟶ N),
      b.homEquiv _ _ (e.inv.app M ≫ G.map h) =
        F.map (a.homEquiv _ _ h) ≫ β.hom.app N :=
    supportTransposeMate a b α β.hom (unit_mateEquiv_symm a b β.hom)
  refine ⟨e, he, ?_⟩
  intro e' he'
  have hi : e'.inv = e.inv := by
    ext M
    apply (b.homEquiv _ _).injective
    simpa using (he' M (L.obj M) (𝟙 _)).trans (he M (L.obj M) (𝟙 _)).symm
  apply Iso.ext
  simpa using (congrArg (fun t ↦ e'.hom ≫ t ≫ e.hom) hi).symm

private theorem supportLocalizationComparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    {L R : D ⥤ E} {T : C ⥤ E} (a : Q ⋙ R ≅ T) (b : Q ⋙ L ≅ T) :
    ∃! e : L ≅ R, ∀ J, e.hom.app (Q.obj J) ≫ a.hom.app J = b.hom.app J := by
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
  let d := b ≪≫ a.symm
  let e := ff.preimageIso d
  have he (J) : e.hom.app (Q.obj J) ≫ a.hom.app J = b.hom.app J := by
    have hd := congr_app (ff.map_preimage d.hom) J
    change e.hom.app (Q.obj J) = d.hom.app J at hd
    rw [hd]
    simp [d]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext Q W
  intro J
  exact (cancel_mono (a.hom.app J)).mp ((he' J).trans (he J).symm)

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)
section CompactSupport
variable (c : Compactification g)
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)

/-- Open-extension realization is the mate of the unit-normalized inverse-image
comparison. Its Hom-transpose equation determines the map itself.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: extension by zero is left adjoint to the exact open inverse image in both
presentations. Transport these adjunctions along the realization equivalences and
take the mate of integralExceptionalEtaleInverse. The displayed equation is its
adjunction characterization; bijectivity of the Hom transposes gives uniqueness. -/
theorem integralExceptionalEtaleOpen_existsUnique (n : ℕ) :
    ∃! e : S.val.levelOpen n ⋙ integralExceptionalEtaleRealization l E c.Z n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i,
      ∀ (M : strictEtaleLevel X (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (N : strictEtaleLevel c.Z (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (h : (S.val.levelOpen n).obj M ⟶ N),
        (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).homEquiv _ _
          (e.inv.app M ≫ (integralExceptionalEtaleRealization l E c.Z n).map h) =
        (integralExceptionalEtaleRealization l E X n).map
          ((S.val.levelOpenAdjunction n).homEquiv _ _ h) ≫
          (integralExceptionalEtaleInverse l E c.i S.openImage n).hom.app N := by
  exact supportLeftMate (S.val.levelOpenAdjunction n)
    (Etale.openImmersionLowerShriekUpperStarAdjunction _ c.i)
    (integralExceptionalEtaleInverse l E c.i S.openImage n)

/-- The ordinary open-extension mate, fixed by its transpose equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleOpen (n : ℕ) :
    S.val.levelOpen n ⋙ integralExceptionalEtaleRealization l E c.Z n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i :=
  (integralExceptionalEtaleOpen_existsUnique l E g c S n).choose

/-- The full exact-localization square on every cochain representative.
Source: blueprint integral exceptional realization
(blueprint: def-pur-adic-support-realization). -/
def IsIntegralExceptionalEtaleDerivedOpen (n : ℕ)
    (e : S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory) :
      Prop :=
  ∀ J : CochainComplex (strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ,
        e.hom.app (DerivedCategory.Q.obj J) ≫
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              c.i).mapDerivedCategory.map
                ((integralExceptionalEtaleRealization l E X n).mapDerivedCategoryFactors.hom.app
                   J) ≫
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              c.i).mapDerivedCategoryFactors.hom.app
                (((integralExceptionalEtaleRealization l E X n).mapHomologicalComplex
                   (.up ℤ)).obj J) =
        (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory.map
          ((S.val.levelOpenFactors n).hom.app J) ≫
        (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategoryFactors.hom.app
          (((S.val.levelOpen n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalEtaleOpen l E g c S n).hom (.up ℤ)).app J)

/-- The exact derived open comparison is fixed on every cochain representative by
the recorded exact factorization and the ordinary adjunction mate.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: apply the exact localization functor to the ordinary comparison. The defining
localization factorization is precisely the displayed square. Every derived object
has a complex representative and every derived arrow is a roof; hence that square
also determines the natural isomorphism uniquely. -/
theorem integralExceptionalEtaleDerivedOpen_existsUnique (n : ℕ) :
    ∃! e : S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory,
      IsIntegralExceptionalEtaleDerivedOpen l E g c S n e := by
  let γ : (S.val.levelOpen n).mapHomologicalComplex (.up ℤ) ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapHomologicalComplex (.up ℤ) ≅
      (integralExceptionalEtaleRealization l E X n).mapHomologicalComplex (.up ℤ) ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
            c.i).mapHomologicalComplex (.up ℤ) :=
    NatIso.mapHomologicalComplex (integralExceptionalEtaleOpen l E g c S n) (.up ℤ)
  let a : DerivedCategory.Q ⋙
      ((integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory) ≅
      ((integralExceptionalEtaleRealization l E X n).mapHomologicalComplex (.up ℤ) ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
            c.i).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
          c.i).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm
  let b : DerivedCategory.Q ⋙ (S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory) ≅
      ((integralExceptionalEtaleRealization l E X n).mapHomologicalComplex (.up ℤ) ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
            c.i).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (S.val.levelOpenFactors n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight γ _
  obtain ⟨e, he, hu⟩ := supportLocalizationComparison DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) a b
  have hγ : γ.hom = NatTrans.mapHomologicalComplex
      (integralExceptionalEtaleOpen l E g c S n).hom (.up ℤ) := rfl
  have normalize (e : S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory) :
      IsIntegralExceptionalEtaleDerivedOpen l E g c S n e ↔
        ∀ J, e.hom.app (DerivedCategory.Q.obj J) ≫ a.hom.app J = b.hom.app J := by
    dsimp only [IsIntegralExceptionalEtaleDerivedOpen]
    simp only [a, b, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp,
      Category.comp_id, hγ]
  exact ⟨e, (normalize e).mpr he, fun e' he' ↦ hu e' ((normalize e').mp he')⟩

/-- The exact derived open comparison, specified by its representative square.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleDerivedOpen (n : ℕ) :
    S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory :=
  (integralExceptionalEtaleDerivedOpen_existsUnique l E g c S n).choose

/-- The compact-support realization, literally the open comparison followed by the
proper comparison. Each factor retains its universal normalization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleSupportComparison (n : ℕ) :
    S.levelFunctor n ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (WeilConjectures.integralExceptionalEtaleProperDerivedRight_exists
        l E g c S n).choose ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (integralExceptionalEtaleDerivedOpen l E g c S n) _ ≪≫
    Functor.associator _ _ _
/-- The full compact-support adjunction-transpose normalization.
Source: blueprint integral exceptional realization
(blueprint: def-pur-adic-support-realization). -/
def IsIntegralExceptionalEtaleRightAdjoint (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H)
    (e : G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H) : Prop :=
  ∀ (M : DerivedCategory (strictEtaleLevel X (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n))
        (N : DerivedCategory (strictEtaleLevel Y (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n))
        (h : (S.levelFunctor n).obj M ⟶ N),
        adj.homEquiv _ _
          ((integralExceptionalEtaleSupportComparison l E g c S n).inv.app M ≫
            (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory.map h) =
        (integralExceptionalEtaleRealization l E X n).mapDerivedCategory.map
          ((G.levelAdjunction n).homEquiv _ _ h) ≫ e.hom.app N

/-- The finite exceptional realization is the mate of the already specified compact-
support realization. The Hom-transpose equation fixes its map, including the counit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: compose the generic finite adjunction with the realization equivalences. The
compact-support comparison identifies its left adjoint with the fixed finite compact-
support functor. The induced right-adjoint comparison is uniquely determined by the
Hom-transpose equation. Applying the inverse realization gives its inverse. -/
theorem integralExceptionalEtaleRightAdjoint_existsUnique (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H) :
    ∃! e : G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H,
      IsIntegralExceptionalEtaleRightAdjoint l E g c S n G H adj e := by
  exact supportRightMate (G.levelAdjunction n) adj
    (integralExceptionalEtaleSupportComparison l E g c S n).symm

/-- The finite right-adjoint comparison, fixed by the compact-support counit equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
@[no_expose] def integralExceptionalEtaleRightAdjoint (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H) :
    G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H :=
  (integralExceptionalEtaleRightAdjoint_existsUnique l E g c S n G H adj).choose

end CompactSupport

end WeilConjectures
