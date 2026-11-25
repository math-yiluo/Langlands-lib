/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTower
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Quotient transitions on K-flat representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionDerivedExistence normalizedDVRResCompletedComp
  scalarReductionDerivedExtension scalarReductionCounit

section AdjunctionHelpers
universe a b c v w z
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{z} C]
  {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {S : C ⥤ A}
  (H : C ⥤ B) (i : H ⋙ R ≅ S) (adj : F ⊣ R) (adjn : G ⊣ S)

private theorem adjoint_square (M N : A) (a : M ⟶ N)
    (V : B) (W : C) (cm : F.obj N ⟶ V) (cn : G.obj N ⟶ W)
    (f : V ⟶ H.obj W)
    (hf : adj.unit.app N ≫ R.map cm ≫ R.map f ≫ i.hom.app W =
      adjn.unit.app N ≫ S.map cn) :
    R.map ((adj.homEquiv M (H.obj (G.obj M))).symm
        (adjn.unit.app M ≫ i.inv.app (G.obj M))) ≫
        i.hom.app (G.obj M) ≫ S.map (G.map a) ≫ S.map cn =
      R.map (F.map a) ≫ R.map cm ≫ R.map f ≫ i.hom.app W := by
  let t := (adj.homEquiv M (H.obj (G.obj M))).symm
    (adjn.unit.app M ≫ i.inv.app (G.obj M))
  have ht : adj.unit.app M ≫ R.map t =
      adjn.unit.app M ≫ i.inv.app (G.obj M) := by
    exact (adj.homEquiv_unit _ _ t).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
  have he : t ≫ H.map (G.map a) ≫ H.map cn = F.map a ≫ cm ≫ f := by
    apply (adj.homEquiv _ _).injective
    simp only [adj.homEquiv_unit, Functor.map_comp]
    have hinv := i.inv.naturality (G.map a ≫ cn)
    dsimp only [Functor.comp_map] at hinv
    simp only [Functor.map_comp, Category.assoc] at hinv
    have unm := adj.unit.naturality a
    have unn := adjn.unit.naturality a
    dsimp only [Functor.id_map, Functor.comp_map] at unm unn
    calc
      _ = adjn.unit.app M ≫ i.inv.app (G.obj M) ≫
          R.map (H.map (G.map a)) ≫ R.map (H.map cn) := by
        rw [← Category.assoc, ← Category.assoc, ht]
        simp only [Category.assoc]
      _ = adjn.unit.app M ≫ S.map (G.map a) ≫ S.map cn ≫ i.inv.app W := by
        rw [hinv]
      _ = a ≫ adjn.unit.app N ≫ S.map cn ≫ i.inv.app W := by
        rw [← Category.assoc, ← Category.assoc,
          ← unn]
        simp only [Category.assoc]
      _ = a ≫ adj.unit.app N ≫ R.map cm ≫ R.map f := by
        rw [← Category.assoc (adjn.unit.app N), ← hf]
        simp only [Category.assoc, Iso.hom_inv_id_app]
        dsimp only [Functor.comp_obj]
        simp only [Category.comp_id]
      _ = _ := by
        rw [← Category.assoc a, unm]
        simp only [Category.assoc]
  have hi := congrArg R.map he
  simp only [Functor.map_comp] at hi
  have hn := i.hom.naturality (G.map a ≫ cn)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc] at hn
  calc
    _ = R.map t ≫ R.map (H.map (G.map a)) ≫ R.map (H.map cn) ≫ i.hom.app W := by
      rw [hn]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ i.hom.app W) hi

private theorem normalized_adjoint_square (M N : A) (a : M ⟶ N)
    (V : B) (W : C) (V' W' : A) (cm : F.obj N ⟶ V) (cn : G.obj N ⟶ W)
    (jm : R.obj V ⟶ V') (jn : S.obj W ⟶ W') [Mono jn]
    (f : V ⟶ H.obj W) (τ : V' ⟶ W')
    (hf : R.map f ≫ i.hom.app W ≫ jn = jm ≫ τ)
    (um : N ⟶ V') (un : N ⟶ W')
    (hm : adj.unit.app N ≫ R.map cm ≫ jm = um)
    (hn : adjn.unit.app N ≫ S.map cn ≫ jn = un)
    (hu : um ≫ τ = un) :
    R.map ((adj.homEquiv M (H.obj (G.obj M))).symm
        (adjn.unit.app M ≫ i.inv.app (G.obj M))) ≫
        i.hom.app (G.obj M) ≫ S.map (G.map a) ≫ S.map cn ≫ jn =
      R.map (F.map a) ≫ R.map cm ≫ jm ≫ τ := by
  have h : adj.unit.app N ≫ R.map cm ≫ R.map f ≫ i.hom.app W =
      adjn.unit.app N ≫ S.map cn := by
    apply (cancel_mono jn).1
    simp only [Category.assoc, hf]
    calc
      _ = (adj.unit.app N ≫ R.map cm ≫ jm) ≫ τ := by simp only [Category.assoc]
      _ = _ := by rw [hm, hu, hn]
  have he := congrArg (fun k ↦ k ≫ jn)
    (adjoint_square H i adj adjn M N a V W cm cn f h)
  simpa only [Category.assoc, hf] using he

end AdjunctionHelpers

section TensorHelpers
universe a b r
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S T : Sheaf J CommRingCat.{r}}
  (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T) (hq : f ≫ q = g)
open SheafOfModules.UnrestrictedTowerProof

private noncomputable def tensorRestrictionComp : res q ⋙ res f ≅ res g :=
  normalizedDVRRestrictionCompIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map q) ≪≫
  eqToIso (congrArg (fun k ↦ SheafOfModules.restrictScalars.{r} k)
    (by simpa only [Functor.map_comp] using
      congrArg ((sheafCompose J (forget₂ CommRingCat RingCat)).map) hq))

private theorem sheafMap_restrict
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (res f).map (sheafMap f g q hq M) ≫
        (tensorRestrictionComp f g q hq).hom.app (SheafOfModules.changeOfRings g M) =
      restrictedMap f g q hq M := by
  subst g
  rfl

variable
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (G : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
  (hf : ∀ N, F.obj N = SheafOfModules.changeOfRings f N)
  (hg : ∀ N, G.obj N = SheafOfModules.changeOfRings g N)

private noncomputable def finiteMap
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    F.obj M ⟶ (res q).obj (G.obj M) :=
  eqToHom (hf M) ≫ sheafMap f g q hq M ≫ (res q).map (eqToHom (hg M).symm)

private theorem finiteMap_restrict
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (res f).map (finiteMap f g q hq F G hf hg M) ≫
        (tensorRestrictionComp f g q hq).hom.app (G.obj M) =
      identifiedMap f g q hq M F G hf hg := by
  dsimp only [finiteMap, identifiedMap]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (tensorRestrictionComp f g q hq).hom.naturality (eqToHom (hg M).symm)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc ((res f).map (sheafMap f g q hq M)), sheafMap_restrict]

private theorem finiteMap_naturality
    (hmf : ∀ {N N'} (a : N ⟶ N'), F.map a =
      eqToHom (hf N) ≫ SheafOfModules.changeOfRingsHom f N a ≫ eqToHom (hf N').symm)
    (hmg : ∀ {N N'} (a : N ⟶ N'), G.map a =
      eqToHom (hg N) ≫ SheafOfModules.changeOfRingsHom g N a ≫ eqToHom (hg N').symm)
    {M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M ⟶ N) :
    F.map a ≫ finiteMap f g q hq F G hf hg N =
      finiteMap f g q hq F G hf hg M ≫ (res q).map (G.map a) := by
  subst g
  have h := identifiedMap_naturality f (f ≫ q) q rfl M F G hf hg hmf hmg a
  rw [← finiteMap_restrict, ← finiteMap_restrict] at h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k ↦ k.val.app U x) h

attribute [local irreducible] finiteMap tensorRestrictionComp

end TensorHelpers

attribute [local irreducible] SheafOfModules.changeOfRings
  SheafOfModules.changeOfRingsHom

attribute [local irreducible] SheafOfModules.UnrestrictedTowerProof.identifiedMap
  SheafOfModules.UnrestrictedTowerProof.sheafMap
  SheafOfModules.UnrestrictedTowerProof.restrictedMap
  SheafOfModules.UnrestrictedTowerProof.tensorSection

section ExactHelpers
universe a b c v w z
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{z} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (H : A ⥤ B) (R : B ⥤ C) (S : A ⥤ C)
  [H.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  (i : H ⋙ R ≅ S)

private theorem exactComp_fac (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso H R ≪≫
        Functor.mapDerivedCategoryNatIso i).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategoryFactors.hom.app K =
    R.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso i (.up ℤ)).hom.app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryNatIso_fac]
  have h := Functor.mapDerivedCategoryCompIso_fac H R K
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  congr 1
  apply CategoryTheory.Functor.congr_map
  ext j
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

private theorem exactComp_map (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (f : L ⟶ (H.mapHomologicalComplex (.up ℤ)).obj K) :
    R.mapDerivedCategory.map
        (DerivedCategory.Q.map f ≫ H.mapDerivedCategoryFactors.inv.app K) ≫
      (Functor.mapDerivedCategoryCompIso H R ≪≫
        Functor.mapDerivedCategoryNatIso i).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategoryFactors.hom.app K =
    R.mapDerivedCategoryFactors.hom.app L ≫
      DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map f ≫
        (Functor.mapHomologicalComplexCompIso i (.up ℤ)).hom.app K) := by
  rw [exactComp_fac]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [← R.mapDerivedCategory.map_comp_assoc
    (H.mapDerivedCategoryFactors.inv.app K) (H.mapDerivedCategoryFactors.hom.app K),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := R.mapDerivedCategoryFactors.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]

end ExactHelpers

attribute [local irreducible] Functor.mapDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
attribute [local instance] normalizedDVRKFlatTransitionLocal1
attribute [local instance] normalizedDVRKFlatTransitionLocal2

attribute [local irreducible] normalizedDVRKFlatComparison

attribute [local instance] scalarReductionExtensionAdditive
  scalarReductionRestrictionLimits scalarReductionRestrictionColimits

private noncomputable def coefficientStep (n : ℕ) :
    integralCoefficientCommRingSheaf l E X (n + 1) ⟶
      integralCoefficientCommRingSheaf l E X n where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom ((normalizedDVRQuotient l E X n.le_succ).hom.app U).hom
      naturality := fun _U _V i ↦ (forget₂ CommRingCat RingCat).map_injective
        ((normalizedDVRQuotient l E X n.le_succ).hom.naturality i) }

private theorem coefficientStep_eq (n : ℕ) :
    coefficientStep l E X n = unrestrictedCoefficientStep l E X n := by
  ext U x
  change (normalizedDVRQuotient l E X n.le_succ).hom.app U x = _
  exact congrArg (fun k ↦ k.hom.app U x)
    (Functor.ofOpSequence_map_homOfLE_succ (integralCoefficientSheafTransition l E X) n)

private theorem coefficientStep_app (n : ℕ) (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
    (b : (integralCoefficientCommRingSheaf l E X (n + 1)).obj.obj U) :
    (coefficientStep l E X n).hom.app U b =
      (integralCoefficientSheafTransition l E X n).hom.app U b := by
  change (normalizedDVRQuotient l E X n.le_succ).hom.app U b = _
  exact congrArg (fun k ↦ k.hom.app U b)
    (Functor.ofOpSequence_map_homOfLE_succ (integralCoefficientSheafTransition l E X) n)

private theorem coefficientStep_comp (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E X (n + 1) ≫
      coefficientStep l E X n = completedIntegralCommRingProjectionUnrestricted l E X n := by
  rw [coefficientStep_eq]
  exact unrestrictedCoefficientStep_comp l E X n

attribute [local irreducible] normalizedDVRQuotient integralCoefficientSheafTransition

private theorem reduction_obj (n : ℕ) (N : scalarReductionSource l E X) :
    (scalarReductionExtension l E X n).obj N =
      SheafOfModules.changeOfRings
        (completedIntegralCommRingProjectionUnrestricted l E X n) N := by
  unfold scalarReductionExtension
  exact (scalarReductionExistence l E X n).choose_spec.choose N

private theorem tensorSection_eq (n : ℕ) (N : scalarReductionSource l E X)
    (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj U) (x : N.val.obj U) :
    (eqToHom (reduction_obj l E X n N).symm).val.app U
        (SheafOfModules.UnrestrictedTowerProof.tensorSection
          (completedIntegralCommRingProjectionUnrestricted l E X n) N U b x) =
      unrestrictedIntegralTensorSection l E X n N U b x := by
  unfold SheafOfModules.UnrestrictedTowerProof.tensorSection unrestrictedIntegralTensorSection
  rfl

attribute [local irreducible] scalarReductionExistence unrestrictedIntegralReductionExistence
  scalarReductionExtension unrestrictedIntegralReductionFunctor

private noncomputable def finiteModuleStep (n : ℕ) (N : scalarReductionSource l E X) :
    (scalarReductionExtension l E X (n + 1)).obj N ⟶
      (normalizedDVRModuleRes l E X n.le_succ).obj
        ((scalarReductionExtension l E X n).obj N) :=
  finiteMap
    (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (coefficientStep l E X n) (coefficientStep_comp l E X n)
    (scalarReductionExtension l E X (n + 1)) (scalarReductionExtension l E X n)
    (reduction_obj l E X (n + 1)) (reduction_obj l E X n) N

attribute [local irreducible] finiteModuleStep

private noncomputable def moduleRestrictionComp (n : ℕ) :
    normalizedDVRModuleRes l E X n.le_succ ⋙ scalarReductionRestriction l E X (n + 1) ≅
      scalarReductionRestriction l E X n :=
  tensorRestrictionComp
    (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (coefficientStep l E X n) (coefficientStep_comp l E X n)

attribute [local irreducible] moduleRestrictionComp

private theorem reduction_map (n : ℕ) {M N : scalarReductionSource l E X} (a : M ⟶ N) :
    (scalarReductionExtension l E X n).map a =
      eqToHom (reduction_obj l E X n M) ≫
        SheafOfModules.changeOfRingsHom
          (completedIntegralCommRingProjectionUnrestricted l E X n) M a ≫
        eqToHom (reduction_obj l E X n N).symm := by
  unfold scalarReductionExtension
  exact (scalarReductionExistence l E X n).choose_spec.choose_spec.choose a

private theorem finiteModuleStep_naturality (n : ℕ) {M N : scalarReductionSource l E X}
    (a : M ⟶ N) :
    (scalarReductionExtension l E X (n + 1)).map a ≫ finiteModuleStep l E X n N =
      finiteModuleStep l E X n M ≫
        (normalizedDVRModuleRes l E X n.le_succ).map
          ((scalarReductionExtension l E X n).map a) := by
  unfold finiteModuleStep
  exact finiteMap_naturality
    (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (coefficientStep l E X n) (coefficientStep_comp l E X n)
    (scalarReductionExtension l E X (n + 1)) (scalarReductionExtension l E X n)
    (reduction_obj l E X (n + 1)) (reduction_obj l E X n)
    (reduction_map l E X (n + 1)) (reduction_map l E X n) a

private noncomputable def finiteChainStep (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    unrestrictedTowerFiniteComplex l E X (n + 1) P ⟶
      ((normalizedDVRModuleRes l E X n.le_succ).mapHomologicalComplex (.up ℤ)).obj
        (unrestrictedTowerFiniteComplex l E X n P) where
  f i := finiteModuleStep l E X n (P.X i)
  comm' i j _ := (finiteModuleStep_naturality l E X n (P.d i j)).symm

private theorem completedRestriction_eq (n : ℕ) :
    normalizedDVRResCompleted l E X D hl n = scalarReductionDerivedRestriction l E X n := by
  unfold normalizedDVRResCompleted scalarReductionDerivedRestriction
  rfl

private theorem completedComp_eq (n : ℕ) :
    normalizedDVRResCompletedComp l E X D hl n.le_succ =
      Functor.mapDerivedCategoryCompIso (normalizedDVRModuleRes l E X n.le_succ)
        (scalarReductionRestriction l E X (n + 1)) ≪≫
      Functor.mapDerivedCategoryNatIso (moduleRestrictionComp l E X n) := by
  unfold normalizedDVRResCompletedComp moduleRestrictionComp tensorRestrictionComp
  congr 2

section TensorIdentification
attribute [local semireducible] scalarReductionExistence unrestrictedIntegralReductionExistence
  scalarReductionExtension unrestrictedIntegralReductionFunctor

private theorem finiteChainStep_restrict (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    ((scalarReductionRestriction l E X (n + 1)).mapHomologicalComplex (.up ℤ)).map
        (finiteChainStep l E X n P) ≫
      (Functor.mapHomologicalComplexCompIso
        (moduleRestrictionComp l E X n) (.up ℤ)).hom.app
          (unrestrictedTowerFiniteComplex l E X n P) =
      integralTowerTransition l E X D hl P n := by
  rw [integralTowerTransition_eq]
  apply HomologicalComplex.hom_ext
  intro j
  change (scalarReductionRestriction l E X (n + 1)).map
      (finiteModuleStep l E X n (P.X j)) ≫
    (moduleRestrictionComp l E X n).hom.app ((scalarReductionExtension l E X n).obj (P.X j)) =
    ((unrestrictedTowerTransition l E X P n).f j)
  have hs := finiteMap_restrict
    (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (coefficientStep l E X n) (coefficientStep_comp l E X n)
    (scalarReductionExtension l E X (n + 1)) (scalarReductionExtension l E X n)
    (reduction_obj l E X (n + 1)) (reduction_obj l E X n) (P.X j)
  unfold finiteModuleStep moduleRestrictionComp
  rw [hs]
  simp only [unrestrictedTowerTransition]
  have h := (unrestrictedIntegralTransition_existsUnique l E X n).exists.choose_spec
  apply SheafOfModules.UnrestrictedTowerProof.identified_hom_ext
    (completedIntegralCommRingProjectionUnrestricted l E X (n + 1)) (P.X j)
    (scalarReductionExtension l E X (n + 1)) (reduction_obj l E X (n + 1))
  intro U b x
  refine (SheafOfModules.UnrestrictedTowerProof.identifiedMap_tmul
    (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (coefficientStep l E X n) (coefficientStep_comp l E X n) (P.X j)
    (scalarReductionExtension l E X (n + 1)) (scalarReductionExtension l E X n)
    (reduction_obj l E X (n + 1)) (reduction_obj l E X n) U b x).trans
      ?_
  rw [coefficientStep_app]
  exact (tensorSection_eq l E X n (P.X j) U
    ((integralCoefficientSheafTransition l E X n).hom.app U b) x).trans
      ((h P j U b x).symm.trans
        (congrArg
          (fun z ↦ (((unrestrictedIntegralTransition l E X n).app P).f j).val.app U z)
          (tensorSection_eq l E X (n + 1) (P.X j) U b x).symm))

end TensorIdentification

private theorem integralUnit_step
    (P : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ) :
    integralTowerUnit l E X D hl P (n + 1) ≫ integralTowerTransition l E X D hl P n =
      integralTowerUnit l E X D hl P n := by
  have hu : integralTowerUnitCondition l E X D hl P (integralTowerUnit l E X D hl P) :=
    (integralTowerMaps_existUnique l E X D hl P).exists.choose_spec.1
  have ht : integralTowerTransitionCondition l E X D hl P
      (integralTowerTransition l E X D hl P) :=
    (integralTowerMaps_existUnique l E X D hl P).exists.choose_spec.2
  ext j U x
  change ((integralTowerTransition l E X D hl P n).f j).val.app U
    (((integralTowerUnit l E X D hl P (n + 1)).f j).val.app U x) = _
  erw [hu (n + 1) j U x, hu n j U x]
  have ho : (integralCoefficientSheafTransition l E X n).hom.app U
      (1 : (integralCoefficientCommRingSheaf l E X (n + 1)).obj.obj U) = 1 :=
    map_one ((integralCoefficientSheafTransition l E X n).hom.app U).hom
  simpa only [ho] using ht n j U 1 x

private noncomputable def derivedFiniteStep (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E X (n + 1) P) ⟶
      (normalizedDVRRes l E X n.le_succ).obj
        (DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E X n P)) :=
  DerivedCategory.Q.map (finiteChainStep l E X n P) ≫
    (normalizedDVRModuleRes l E X n.le_succ).mapDerivedCategoryFactors.inv.app
      (unrestrictedTowerFiniteComplex l E X n P)

private theorem derivedFiniteStep_restrict (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (scalarReductionDerivedRestriction l E X (n + 1)).map (derivedFiniteStep l E X n P) ≫
      (normalizedDVRResCompletedComp l E X D hl n.le_succ).hom.app
        (DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E X n P)) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
        (unrestrictedTowerFiniteComplex l E X n P) =
    (scalarReductionRestriction l E X (n + 1)).mapDerivedCategoryFactors.hom.app
        (unrestrictedTowerFiniteComplex l E X (n + 1) P) ≫
      DerivedCategory.Q.map (integralTowerTransition l E X D hl P n) := by
  rw [completedComp_eq]
  unfold derivedFiniteStep scalarReductionDerivedRestriction
  rw [exactComp_map, finiteChainStep_restrict]

private theorem comparison_eq (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    normalizedDVRKFlatComparison l E X n P =
      (scalarReductionDerivedRestriction l E X n).map
        ((scalarReductionCounit l E X n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
        (unrestrictedTowerFiniteComplex l E X n P) := by
  unfold normalizedDVRKFlatComparison
  simp only [Functor.mapHomotopyCategoryFactors, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [(scalarReductionDerivedExtension l E X n).map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id]

local instance : Category.{max (t + 2) (u + 1)}
    (DerivedCategory (scalarReductionSource l E X)) := inferInstance

set_option linter.unusedVariables false in
/-- The canonical quotient chain map is the restriction of the adjoint reduction
transition, expressed through the universal K-flat comparison.
Source: Stacks Tags 03EK, 06YY, 06YL; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-coef-normalized-dvr-kflat-transition).

Proof: first take M=Q(P) and e the identity. The ordinary tensor map sends b tensor x
to rho(b) tensor x. It is linear over the larger finite quotient, because the
completed projections compose with rho. Its adjoint sends x to 1 tensor x and hence
is the smaller scalar-extension unit. Apply the homotopy-category adjunction and
localize. The derived adjunction normalization identifies the resulting adjoint
with the displayed derived transition, after the exact restriction composition
comparison. The universal derived counits give exactly the comparison factors on
both sides. On pure tensors the restricted ordinary map has the formula defining
integralTowerTransition; tensor generation and the universal property of
sheafification prove equality, degree by degree. For general e, naturality of the
two adjunction units, of the counits and of the restriction comparison transports
the equality along e.inv. The argument is valid for n=0 and zero complexes. -/
theorem normalizedDVR_kflat_transition
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P)
    (M : completedIntegralDerivedCategory l E X D hl)
    (e : DerivedCategory.Q.obj P ≅ M) (n : ℕ)
    (am : scalarReductionDerivedExtension l E X (n + 1) ⊣
      scalarReductionDerivedRestriction l E X (n + 1))
    (an : scalarReductionDerivedExtension l E X n ⊣ scalarReductionDerivedRestriction l E X n)
    (hm : am.unit.app (DerivedCategory.Q.obj P) ≫
        normalizedDVRKFlatComparison l E X (n + 1) P =
      DerivedCategory.Q.map (integralTowerUnit l E X D hl P (n + 1)))
    (hn : an.unit.app (DerivedCategory.Q.obj P) ≫
        normalizedDVRKFlatComparison l E X n P =
      DerivedCategory.Q.map (integralTowerUnit l E X D hl P n)) :
    (scalarReductionDerivedRestriction l E X (n + 1)).map
        ((am.homEquiv
          M ((normalizedDVRRes l E X n.le_succ).obj
            ((scalarReductionDerivedExtension l E X n).obj M))).symm
          (an.unit.app M ≫
            (normalizedDVRResCompletedComp l E X D hl n.le_succ).inv.app
              ((scalarReductionDerivedExtension l E X n).obj M))) ≫
      (normalizedDVRResCompletedComp l E X D hl n.le_succ).hom.app
        ((scalarReductionDerivedExtension l E X n).obj M) ≫
      (scalarReductionDerivedRestriction l E X n).map
        ((scalarReductionDerivedExtension l E X n).map e.inv) ≫
      normalizedDVRKFlatComparison l E X n P =
    (scalarReductionDerivedRestriction l E X (n + 1)).map
        ((scalarReductionDerivedExtension l E X (n + 1)).map e.inv) ≫
      normalizedDVRKFlatComparison l E X (n + 1) P ≫
      DerivedCategory.Q.map (integralTowerTransition l E X D hl P n) := by
  let N := DerivedCategory.Q.obj P
  let V := DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E X (n + 1) P)
  let W := DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E X n P)
  let cm := (scalarReductionCounit l E X (n + 1)).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let cn := (scalarReductionCounit l E X n).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let jm := (scalarReductionRestriction l E X (n + 1)).mapDerivedCategoryFactors.hom.app
    (unrestrictedTowerFiniteComplex l E X (n + 1) P)
  let jn := (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
    (unrestrictedTowerFiniteComplex l E X n P)
  have hm' := hm
  have hn' := hn
  rw [comparison_eq] at hm' hn'
  have h := normalized_adjoint_square
    (A := DerivedCategory (scalarReductionSource l E X))
    (R := scalarReductionDerivedRestriction l E X (n + 1))
    (S := scalarReductionDerivedRestriction l E X n)
    (normalizedDVRRes l E X n.le_succ)
    (normalizedDVRResCompletedComp l E X D hl n.le_succ) am an M N e.inv V W
    (DerivedCategory.Q.obj (unrestrictedTowerComplex l E X (n + 1) P))
    (DerivedCategory.Q.obj (unrestrictedTowerComplex l E X n P)) cm cn jm jn
    (derivedFiniteStep l E X n P)
    (DerivedCategory.Q.map (integralTowerTransition l E X D hl P n))
    (derivedFiniteStep_restrict l E X D hl n P)
    (DerivedCategory.Q.map (integralTowerUnit l E X D hl P (n + 1)))
    (DerivedCategory.Q.map (integralTowerUnit l E X D hl P n)) hm' hn'
    (by rw [← CategoryTheory.Functor.map_comp, integralUnit_step])
  rw [comparison_eq, comparison_eq]
  simpa only [completedRestriction_eq,
    cm, cn, jm, jn, Category.assoc] using h

end WeilConjectures
