/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullFiniteSquare
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Unit normalization of the finite scalar open comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

-- The geometric Hom normalization fixes the scalar mate of the pullback square.
private theorem scalarPull_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : B ⥤ A} {T : A ⥤ B} {P' : D ⥤ C} {T' : C ⥤ D}
    {F : A ⥤ C} {U : C ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    (a : P ⊣ T) (b : P' ⊣ T') (c : F ⊣ U) (e : G ⊣ V)
    (d : V ⋙ P ≅ P' ⋙ U) (z : T' ⋙ V ≅ U ⋙ T)
    (hz : ∀ N, a.homEquiv _ _ (d.hom.app N) =
      V.map (b.unit.app N) ≫ z.hom.app (P'.obj N)) (M : B) :
    P.map (e.unit.app M) ≫ d.hom.app (G.obj M) =
      c.unit.app (P.obj M) ≫ U.map
        ((((a.comp c).ofNatIsoRight z.symm).leftAdjointUniq (e.comp b)).hom.app M) := by
  apply (a.homEquiv _ _).injective
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((a.comp c).ofNatIsoRight z.symm) (e.comp b) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have h' : (a.comp c).homEquiv _ _
      ((((a.comp c).ofNatIsoRight z.symm).leftAdjointUniq (e.comp b)).hom.app M) =
      (e.comp b).unit.app M ≫ z.hom.app _ := by
    rw [← h]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hn := a.unit.naturality (e.unit.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hn]
  have hz' := hz (G.obj M)
  rw [Adjunction.homEquiv_unit] at hz'
  simp only [Functor.comp_obj, Functor.id_obj] at hz' ⊢
  rw [Category.assoc, hz']
  simpa only [Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Category.assoc,
    Functor.comp_obj, Functor.id_obj] using h'.symm

-- Interchange scalar and open mates by their three unit equations.
private theorem scalarOpen_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    {F : A ⥤ C} {U : C ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    (a : J ⊣ P) (b : J' ⊣ P') (c : F ⊣ U) (e : G ⊣ V)
    (d : V ⋙ P ≅ P' ⋙ U) (r : U ⋙ J ⟶ J' ⋙ V)
    (q : P ⋙ F ⟶ G ⋙ P')
    (hr : ∀ N, U.map (b.unit.app N) ≫ d.inv.app (J'.obj N) =
      a.unit.app (U.obj N) ≫ P.map (r.app N))
    (hq : ∀ M, P.map (e.unit.app M) ≫ d.hom.app (G.obj M) =
      c.unit.app (P.obj M) ≫ U.map (q.app M)) (K : A) :
    F.map (a.unit.app K) ≫ q.app (J.obj K) ≫ P'.map
      (((mateEquiv c e).symm (TwoSquare.mk _ _ _ _ r)).app K) =
      b.unit.app (F.obj K) := by
  let t := ((mateEquiv c e).symm (TwoSquare.mk _ _ _ _ r))
  have ht := unit_mateEquiv_symm c e (TwoSquare.mk _ _ _ _ r) K
  change J.map (c.unit.app K) ≫ r.app (F.obj K) =
    e.unit.app (J.obj K) ≫ V.map (t.app K) at ht
  apply (c.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := c.unit.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Functor.comp_obj, Functor.id_obj]
  rw [← Category.assoc, ← hn, Category.assoc]
  rw [← reassoc_of% hq (J.obj K)]
  have hd := d.hom.naturality (t.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hd
  rw [← hd]
  simp only [← P.map_comp_assoc]
  rw [← ht, P.map_comp]
  simp only [Category.assoc]
  have hn' := a.unit.naturality (c.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn'
  rw [← reassoc_of% hn', ← reassoc_of% hr (F.obj K)]
  simp only [Iso.inv_hom_id_app]
  erw [Category.comp_id]

-- The actual localized unit, with the standard exact-functor factorizations.
private theorem localized_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {J : A ⥤ B} {P : B ⥤ A} [J.Additive] [P.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (a : J ⊣ P)
    (K : CochainComplex A ℤ) :
    (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        P.mapDerivedCategoryFactors.inv.app _ ≫
        P.mapDerivedCategory.map (J.mapDerivedCategoryFactors.inv.app K) := by
  unfold exactLocalizationDerivedAdjunction
  rw [Adjunction.localization_unit_app]
  rfl

-- Transport an ordinary unit equation to every derived object.
private theorem localized_unit_transport
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {J J' : A ⥤ B} {P P' : B ⥤ A}
    [J.Additive] [J'.Additive] [P.Additive] [P'.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    (a : J ⊣ P) (b : J' ⊣ P') (e : J ≅ J') (q : P ≅ P')
    (h : ∀ K, a.unit.app K ≫ q.hom.app (J.obj K) ≫ P'.map (e.hom.app K) =
      b.unit.app K) (K : DerivedCategory A) :
    (exactLocalizationDerivedAdjunction a).unit.app K ≫
      (Functor.mapDerivedCategoryNatIso q).hom.app (J.mapDerivedCategory.obj K) ≫
      P'.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso e).hom.app K) =
      (exactLocalizationDerivedAdjunction b).unit.app K := by
  suffices he : (exactLocalizationDerivedAdjunction a).unit ≫
      Functor.whiskerLeft J.mapDerivedCategory (Functor.mapDerivedCategoryNatIso q).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom P'.mapDerivedCategory =
      (exactLocalizationDerivedAdjunction b).unit from congr_app he K
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro L
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_mono (P'.mapDerivedCategory.map (J'.mapDerivedCategoryFactors.hom.app L) ≫
    P'.mapDerivedCategoryFactors.hom.app ((J'.mapHomologicalComplex (.up ℤ)).obj L))).1
  have hn := (Functor.mapDerivedCategoryNatIso q).hom.naturality
    (J.mapDerivedCategoryFactors.inv.app L)
  have he := Functor.mapDerivedCategoryNatIso_fac e L
  have hq := Functor.mapDerivedCategoryNatIso_fac q
    ((J.mapHomologicalComplex (.up ℤ)).obj L)
  have hp := P'.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app L)
  dsimp only [Functor.comp_map] at hn hp
  rw [localized_unit, localized_unit]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← P'.mapDerivedCategory.map_comp_assoc,
    ← P'.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← P'.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [P'.mapDerivedCategory.map_id, Category.id_comp]
  rw [hp, reassoc_of% hq, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hc : (a.mapHomologicalComplex (.up ℤ)).unit.app L ≫
      (NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app
        ((J.mapHomologicalComplex (.up ℤ)).obj L) ≫
      (P'.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app L) =
      (b.mapHomologicalComplex (.up ℤ)).unit.app L := by
    ext i
    exact h (L.X i)
  rw [hc]
  rw [← P'.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [P'.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]

-- Cancel the coefficient presentations and transport the open adjunction unit.
private theorem unit_presentation
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' J'' : C ⥤ D} {P' P'' : D ⥤ C}
    {F F' : A ⥤ C} {G G' : B ⥤ D}
    (a : J ⊣ P) (b : J' ⊣ P') (c : J'' ⊣ P'')
    (eX : F ≅ F') (eY : G ≅ G') (eJ : J' ≅ J'') (eP : P' ≅ P'')
    (q : P ⋙ F ⟶ G ⋙ P') (t : J ⋙ G ⟶ F ⋙ J')
    (h : ∀ K, F.map (a.unit.app K) ≫ q.app (J.obj K) ≫ P'.map (t.app K) =
      b.unit.app (F.obj K))
    (hc : ∀ N, b.unit.app N ≫ eP.hom.app (J'.obj N) ≫ P''.map (eJ.hom.app N) =
      c.unit.app N) (K : A) :
    F'.map (a.unit.app K) ≫
      (eX.inv.app (P.obj (J.obj K)) ≫ q.app (J.obj K) ≫
        P'.map (eY.hom.app (J.obj K)) ≫ eP.hom.app (G'.obj (J.obj K))) ≫
      P''.map (eY.inv.app (J.obj K) ≫ t.app K ≫ eJ.hom.app (F.obj K) ≫
        J''.map (eX.hom.app K)) = c.unit.app (F'.obj K) := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := eX.inv.naturality (a.unit.app K)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [← Category.assoc, hn, Category.assoc]
  rw [← eP.hom.naturality_assoc (eY.inv.app (J.obj K))]
  simp only [← P'.map_comp_assoc, Iso.hom_inv_id_app]
  erw [P'.map_id, Category.id_comp]
  have ht := eP.hom.naturality (t.app K)
  dsimp only [Functor.comp_obj] at ht
  rw [← reassoc_of% ht]
  rw [reassoc_of% h K, reassoc_of% hc (F.obj K)]
  have hn' := c.unit.naturality (eX.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn'
  rw [← hn']
  simp only [Iso.inv_hom_id_app_assoc]

-- The unit equation before introducing constant-ring finite presentations.
private theorem coefficientOpen_unit
    {R S : WeilConjectures.PurCompactSupport.Coefficients.{u}}
    (a : WeilConjectures.PurCompactSupport.Change R S)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategory (proEtaleRingModules X (R.ring X))) :
    (pbcDerivedExtend (a.map X)).map
        ((WeilConjectures.PurCompactSupport.openDerivedAdjunction R j).unit.app K) ≫
      (WeilConjectures.PurCompactSupport.scalarPull a j).hom.app
        ((WeilConjectures.PurCompactSupport.openExtension R j).mapDerivedCategory.obj K) ≫
      (WeilConjectures.PurCompactSupport.pull S j).map
        ((WeilConjectures.PurCompactSupport.openComparison a j).app K) =
      (WeilConjectures.PurCompactSupport.openDerivedAdjunction S j).unit.app
        ((pbcDerivedExtend (a.map X)).obj K) := by
  let := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
      (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j)
  have : IsIso ((mateEquiv
      (WeilConjectures.PurCompactSupport.openAdjunction S j)
      (WeilConjectures.PurCompactSupport.openAdjunction R j)).symm
      (TwoSquare.mk _ _ _ _ (asIso (proEtaleRingRestrictionPullbackInv
        j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
          (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j))).symm.hom)) := by
    change IsIso (WeilConjectures.PurCompactSupport.openRestrictionMap a j)
    infer_instance
  have hm := (exact_localization_inverse_mate
    (WeilConjectures.PurCompactSupport.openAdjunction S j)
    (WeilConjectures.PurCompactSupport.openAdjunction R j)
    (asIso (proEtaleRingRestrictionPullbackInv
      j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
        (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j))).symm).2.1
  change ((mateEquiv
    (WeilConjectures.PurCompactSupport.openDerivedAdjunction S j)
    (WeilConjectures.PurCompactSupport.openDerivedAdjunction R j)).symm
    (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedPullback
      j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
        (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j)).hom)) =
    (WeilConjectures.PurCompactSupport.openRestriction a j).hom at hm
  apply scalarOpen_unit
    (WeilConjectures.PurCompactSupport.openDerivedAdjunction R j)
    (WeilConjectures.PurCompactSupport.openDerivedAdjunction S j)
    (pbcDerivedScalarAdjunction (a.map X)) (pbcDerivedScalarAdjunction (a.map Y))
    (proEtaleRingRestrictionDerivedPullback
      j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
        (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j)).symm
    (WeilConjectures.PurCompactSupport.openRestriction a j).hom
    (WeilConjectures.PurCompactSupport.scalarPull a j).hom
  · intro N
    have h := unit_mateEquiv_symm
      (WeilConjectures.PurCompactSupport.openDerivedAdjunction S j)
      (WeilConjectures.PurCompactSupport.openDerivedAdjunction R j)
      (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedPullback
        j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
          (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j)).hom) N
    change _ = _ ≫ (WeilConjectures.PurCompactSupport.pull R j).map
      (((mateEquiv _ _).symm _).app N) at h
    rw [hm] at h
    exact h
  · intro M
    apply scalarPull_unit
      (proEtaleRingDerivedAdjunction j (R.ring Y) (R.ring X) (R.pull j))
      (proEtaleRingDerivedAdjunction j (S.ring Y) (S.ring X) (S.pull j))
      (pbcDerivedScalarAdjunction (a.map X)) (pbcDerivedScalarAdjunction (a.map Y))
      (proEtaleRingRestrictionDerivedPullback
        j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
          (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j)).symm
      (proEtaleRingRestrictionDerivedDirectImage
        j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
          (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j))
    intro N
    have h := (proEtaleRingSheafChangeAdjunction
      j (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
        (a.map Y) (a.map X) (R.pull j) (S.pull j) (a.square j)).2.2 N _ (𝟙 _)
    simp only [Adjunction.homEquiv_unit] at h
    erw [(proEtaleRingRestrictScalars (a.map X)).mapDerivedCategory.map_id,
      Category.comp_id,
      (proEtaleRingDerivedDirectImage j (S.ring Y) (S.ring X) (S.pull j)).map_id,
      Category.comp_id] at h
    simpa only [pbcDerivedRestrict, pbcRestrict, Iso.symm_hom,
      Adjunction.homEquiv_unit] using h

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite scalar open comparison preserves the actual open unit.
This involves only the scalar and geometric adjunctions, with no system model.
Source: Stacks 03DI, 0E8I, 0D6D and 07A7; fix-prop-coherence, preservation of
adjunction units by coefficient comparisons
(blueprint: lem-sf-integral-open-scalar-unit-square).

Proof: first work with the completed and finite ring sheaves before the
constant-ring presentation isomorphisms. The restriction/pullback square is
invertible and its geometric mate is the normalized restriction/direct-image
comparison (proEtaleRingSheafChangeAdjunction). Taking scalar mates therefore
gives the conjugate of the composite adjunctions used in integralFiniteScalarPull.
The ordinary inverse open mate of this same restriction/pullback square defines
openRestrictionMap. Exact localization preserves that mate and its open units.
Taking its scalar mate defines openComparison. Interchanging these two mate
operations and cancelling the scalar triangle identities identifies openComparison
with the inverse open mate of the scalar/pullback comparison. Its unit equation
is the displayed equality. Finally finiteReductionIso, finitePullbackIso and
finiteOpenIso are the unique adjoint identifications preserving their units;
transport the equation through them. This argument allows any integral K,
including zero, and empty and identity opens, without flatness of the quotient. -/
theorem integralOpenScalarUnitSquare {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : Integral l E X) (n : ℕ) :
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).1
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).2.1
    letI := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).2.2
    (scalarReductionDerivedExtension l E X n).map ((ringedOpenAdj l E j).unit.app K) ≫
      (integralFiniteScalarPull l E j n).hom.app ((ringedOpen l E j).obj K) ≫
      (finiteDerivedPullback l E n j).map
        ((PurCompactSupport.finiteReductionIso l E Y n).inv.app ((ringedOpen l E j).obj K) ≫
          (PurCompactSupport.openComparison
            (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) j).app K ≫
          (Functor.mapDerivedCategoryNatIso
            (PurCompactSupport.finiteOpenIso l E n j)).hom.app
              ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
                (Nat.le_add_left 1 n) X)).obj K) ≫
          (sfIntrinsicExtensionByZero j
            (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
              ((PurCompactSupport.finiteReductionIso l E X n).hom.app K)) =
    (finiteOpenAdj l E j n).unit.app ((scalarReductionDerivedExtension l E X n).obj K) := by
  let := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).1
  let := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  let := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) j
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) j
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) j
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
  let S := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
  have hf := localized_unit_transport
    (PurCompactSupport.openAdjunction S j)
    (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)
    (PurCompactSupport.finiteOpenIso l E n j)
    (PurCompactSupport.finitePullbackIso l E n j)
    (fun M ↦ by
      have h := Adjunction.unit_leftAdjointUniq_hom_app
        ((PurCompactSupport.openAdjunction S j).ofNatIsoRight
          (PurCompactSupport.finitePullbackIso l E n j))
        (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j) M
      simpa only [PurCompactSupport.finiteOpenIso, Adjunction.ofNatIsoRight_unit,
        NatTrans.comp_app,
        Functor.whiskerLeft_app, Category.assoc] using h)
  have h := unit_presentation (ringedOpenAdj l E j)
    (PurCompactSupport.openDerivedAdjunction S j) (finiteOpenAdj l E j n)
    (PurCompactSupport.finiteReductionIso l E X n)
    (PurCompactSupport.finiteReductionIso l E Y n)
    (Functor.mapDerivedCategoryNatIso (PurCompactSupport.finiteOpenIso l E n j))
    (Functor.mapDerivedCategoryNatIso (PurCompactSupport.finitePullbackIso l E n j))
    (PurCompactSupport.scalarPull a j).hom (PurCompactSupport.openComparison a j)
    (coefficientOpen_unit a j) hf K
  simpa only [integralFiniteScalarPull, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using h

end WeilConjectures.IntegralSystemRealization
