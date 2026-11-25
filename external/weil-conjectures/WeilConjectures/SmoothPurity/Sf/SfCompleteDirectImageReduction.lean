/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage

import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardComparison
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.Data.Nat.Prime.Infinite
import all WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares

/-! # Complete direct images and their canonical finite reductions

Source: Stacks Project, Tags 099N and 0944; Bhatt--Scholze, Lemmas 6.5.9(2)
and 6.5.11(3). (blueprint: lem-sf-complete-direct-image-reduction).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

attribute [-instance] CompletedCoefficientPushforward.modAbelian
attribute [-instance] CompletedCoefficientPushforward.hasDerived

-- Roos triangles and transport of completeness.

private theorem complete_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u})
    {K L : DerivedCategory (scalarReductionSource.{u, u} l E Y)}
    (e : K ≅ L) (hK : IsSfDerivedComplete l E Y K) :
    IsSfDerivedComplete l E Y L := by
  unfold IsSfDerivedComplete at hK ⊢
  apply roos_transport _ _ e
    (fun n ↦ (sfDerivedReductionRestricted l E Y n).mapIso e)
    (fun n ↦ (sfDerivedReductionUnit l E Y n).app K)
    (fun n ↦ (sfDerivedReductionUnit l E Y n).app L) _ _ hK
  · intro n
    exact ((sfDerivedReductionTransition l E Y n).naturality e.hom).symm
  · intro n
    exact ((sfDerivedReductionUnit l E Y n).naturality e.hom).symm

private theorem roos_unique
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : ℕ → C} [HasProduct T] (t : ∀ n, T (n + 1) ⟶ T n)
    {M N : C} (p : M ⟶ ∏ᶜ T) (q : N ⟶ ∏ᶜ T)
    (δ : ∏ᶜ T ⟶ M⟦(1 : ℤ)⟧) (ε : ∏ᶜ T ⟶ N⟦(1 : ℤ)⟧)
    (hp : IsDerivedLimitTriangle t M p δ) (hq : IsDerivedLimitTriangle t N q ε) :
    ∃ e : M ≅ N, e.hom ≫ q = p := by
  let A := Triangle.mk p (towerTransitionEndomorphism t) δ
  let B := Triangle.mk q (towerTransitionEndomorphism t) ε
  let e := Pretriangulated.isoTriangleOfIso₁₂ A.rotate B.rotate
    (Pretriangulated.rot_of_distTriang A hp)
    (Pretriangulated.rot_of_distTriang B hq) (Iso.refl _) (Iso.refl _) (by simp [A, B])
  let d : A ≅ B :=
    (rotCompInvRot.app A) ≪≫ (Pretriangulated.invRotate C).mapIso e ≪≫
      (rotCompInvRot.app B).symm
  refine ⟨Triangle.π₁.mapIso d, ?_⟩
  have hd : d.hom.hom₂ = 𝟙 _ := by
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  simpa only [Functor.mapIso_hom, Triangle.π₁_map, hd, Category.comp_id, A, B,
    Triangle.mk_mor₁] using
    d.hom.comm₁.symm

private theorem map_roos
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    {T : ℕ → C} [HasProduct T] [HasProduct (fun n ↦ F.obj (T n))]
    [PreservesLimit (Discrete.functor T) F]
    (t : ∀ n, T (n + 1) ⟶ T n) (K : C)
    (p : K ⟶ ∏ᶜ T) (δ : ∏ᶜ T ⟶ K⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle t K p δ) :
    ∃ ε, IsDerivedLimitTriangle (fun n ↦ F.map (t n)) (F.obj K)
      (Pi.lift (fun n ↦ F.map (p ≫ Pi.π T n))) ε := by
  let e := PreservesProduct.iso F T
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = F.map (Pi.π T n) := by simp [e]
  have ht : F.map (towerTransitionEndomorphism t) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ F.map (t n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_comp_π, Functor.map_sub]
    rw [← Category.assoc, he, ← Functor.map_comp]
    rw [← Functor.map_comp, Pi.lift_comp_π, Category.id_comp, Functor.map_comp]
  have hp : F.map p ≫ e.hom = Pi.lift (fun n ↦ F.map (p ≫ Pi.π T n)) := by
    apply Pi.hom_ext
    intro n
    simp [Category.assoc, he]
  refine ⟨e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  rw [← hp]
  exact isomorphic_distinguished _ (F.map_distinguished _ h) _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm
      (by change (F.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ F.map p; simp)
      (by
        change towerTransitionEndomorphism (fun n ↦ F.map (t n)) ≫ e.inv =
          e.inv ≫ F.map (towerTransitionEndomorphism t)
        apply (cancel_mono e.hom).1
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using congrArg (fun z ↦ e.inv ≫ z) ht.symm)
      (by
        change (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ≫
          (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
            e.inv ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)
        simp))

-- Use one cochain unit throughout all derived normalization equations.

private noncomputable def canonical_cochain_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj I) :=
  (derivedCochainRightUnit F F.rightDerivedFunctor F.rightDerivedFunctorUnit).app I

private theorem canonical_cochain_unit_eq_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) :
    canonical_cochain_unit F I =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I) :=
  cochainRightUnit_app_eq F F.rightDerivedFunctor F.rightDerivedFunctorUnit I

private theorem canonical_cochain_unit_objQIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) [I.IsKInjective] :
    canonical_cochain_unit F I = (F.rightDerivedFunctorObjQIso I).inv := by
  rw [canonical_cochain_unit_eq_unit]
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv,
    Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, asIso_hom, Iso.app_hom]
  change _ = (𝟙 _ ≫ _) ≫ F.rightDerivedFunctor.map (𝟙 _)
  simp

private theorem canonical_cochain_unit_isIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso (canonical_cochain_unit F I) := by
  rw [canonical_cochain_unit_objQIso]
  infer_instance

private theorem derived_natTrans_ext_on_kinjectives
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A]
    {D : Type*} [Category D] {F G : DerivedCategory A ⥤ D}
    (x y : F ⟶ G)
    (h : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      x.app (DerivedCategory.Q.obj I) = y.app (DerivedCategory.Q.obj I)) : x = y := by
  ext M
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have := hI
  apply (cancel_epi (F.map e.inv)).mp
  rw [x.naturality, y.naturality, h I]

-- Transport the actual adjunction mate, including its units and the right-adjoint cube.

private theorem projection_formula_transport
    {C D A B C' D' A' B' : Type*}
    [Category C] [Category D] [Category A] [Category B]
    [Category C'] [Category D'] [Category A'] [Category B']
    (LX : C ⥤ A) (RX : A ⥤ C) (LY : D ⥤ B) (RY : B ⥤ D)
    (LX' : C' ⥤ A') (RX' : A' ⥤ C') (LY' : D' ⥤ B') (RY' : B' ⥤ D')
    (aX : LX ⊣ RX) (aY : LY ⊣ RY) (aX' : LX' ⊣ RX') (aY' : LY' ⊣ RY')
    (F : C ⥤ D) (H : A ⥤ B) (F' : C' ⥤ D') (H' : A' ⥤ B')
    (U : C ⥤ C') (V : D ⥤ D') (P : A ⥤ A') (Q : B ⥤ B')
    [Q.ReflectsIsomorphisms]
    (rX : RX ⋙ U ≅ P ⋙ RX') (rY : RY ⋙ V ≅ Q ⋙ RY')
    (sX : U ⋙ LX' ≅ LX ⋙ P) (sY : V ⋙ LY' ≅ LY ⋙ Q)
    (e : F ⋙ V ≅ U ⋙ F') (h : H ⋙ Q ≅ P ⋙ H')
    (d : RX ⋙ F ≅ H ⋙ RY) (d' : RX' ⋙ F' ≅ H' ⋙ RY')
    (huX : ∀ K, aX'.unit.app (U.obj K) ≫ RX'.map (sX.hom.app K) =
      U.map (aX.unit.app K) ≫ rX.hom.app (LX.obj K))
    (huY : ∀ K, aY'.unit.app (V.obj K) ≫ RY'.map (sY.hom.app K) =
      V.map (aY.unit.app K) ≫ rY.hom.app (LY.obj K))
    (cube : ∀ N,
      V.map (d.hom.app N) ≫ rY.hom.app (H.obj N) ≫ RY'.map (h.hom.app N) =
        e.hom.app (RX.obj N) ≫ F'.map (rX.hom.app N) ≫ d'.hom.app (P.obj N))
    (K : C)
    (hb : IsIso ((aY'.homEquiv _ _).symm
      (F'.map (aX'.unit.app (U.obj K)) ≫ d'.hom.app (LX'.obj (U.obj K))))) :
    IsIso ((aY.homEquiv _ _).symm
      (F.map (aX.unit.app K) ≫ d.hom.app (LX.obj K))) := by
  let b := (aY.homEquiv _ _).symm
    (F.map (aX.unit.app K) ≫ d.hom.app (LX.obj K))
  let b' := (aY'.homEquiv _ _).symm
    (F'.map (aX'.unit.app (U.obj K)) ≫ d'.hom.app (LX'.obj (U.obj K)))
  have hb' : IsIso b' := hb
  have heq : Q.map b ≫ h.hom.app (LX.obj K) =
      (sY.app (F.obj K)).inv ≫ LY'.map (e.hom.app K) ≫ b' ≫
        H'.map (sX.hom.app K) := by
    apply (cancel_epi (sY.hom.app (F.obj K))).mp
    simp only [Category.assoc, Iso.app_inv, Iso.hom_inv_id_app_assoc]
    apply (aY'.homEquiv _ _).injective
    change aY'.unit.app _ ≫ RY'.map _ = _
    simp only [Functor.map_comp, ← Category.assoc]
    rw [huY]
    simp only [Category.assoc]
    have hr := rY.hom.naturality b
    dsimp only [Functor.comp_map] at hr
    rw [← reassoc_of% hr]
    simp only [Functor.comp_map, ← V.map_comp_assoc]
    change V.map (aY.unit.app _ ≫ RY.map b) ≫ _ = _
    have hbe : aY.unit.app (F.obj K) ≫ RY.map b =
        F.map (aX.unit.app K) ≫ d.hom.app (LX.obj K) :=
      (aY.homEquiv _ _).apply_symm_apply _
    erw [hbe]
    simp only [Functor.map_comp, Category.assoc]
    rw [cube]
    have hen := e.hom.naturality (aX.unit.app K)
    dsimp only [Functor.comp_map] at hen
    rw [reassoc_of% hen]
    rw [aY'.homEquiv_naturality_left, aY'.homEquiv_naturality_right]
    change _ = e.hom.app K ≫
      ((aY'.homEquiv _ _) b') ≫ RY'.map (H'.map (sX.hom.app K))
    dsimp only [b']
    erw [Equiv.apply_symm_apply]
    have hd := d'.hom.naturality (sX.hom.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hd
    simp only [Category.assoc]
    rw [← hd]
    simp only [← F'.map_comp_assoc, ← F'.map_comp]
    rw [huX]
  have : IsIso (Q.map b ≫ h.hom.app (LX.obj K)) := by
    rw [heq]
    infer_instance
  have : IsIso (Q.map b) := IsIso.of_isIso_comp_right _ (h.hom.app (LX.obj K))
  exact isIso_of_reflects_iso b Q

attribute [local irreducible] canonical_cochain_unit

-- Coherence follows from the ordinary cube and the four universal cochain units.

section NormalizedCube
universe v w z
variable
    {A : Type v} [Category.{w} A] [abA : Abelian A] [derA : HasDerivedCategory.{z} A]
    {B : Type v} [Category.{w} B] [abB : Abelian B] [derB : HasDerivedCategory.{z} B]
    {C : Type v} [Category.{w} C] [abC : Abelian C] [derC : HasDerivedCategory.{z} C]
    {D : Type v} [Category.{w} D] [abD : Abelian D] [derD : HasDerivedCategory.{z} D]
    {A' : Type v} [Category.{w} A'] [abAp : Abelian A'] [derAp : HasDerivedCategory.{z} A']
    {B' : Type v} [Category.{w} B'] [abBp : Abelian B'] [derBp : HasDerivedCategory.{z} B']
    {C' : Type v} [Category.{w} C'] [abCp : Abelian C'] [derCp : HasDerivedCategory.{z} C']
    {D' : Type v} [Category.{w} D'] [abDp : Abelian D'] [derDp : HasDerivedCategory.{z} D']
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    [Abelian.HasKInjectiveResolutions A'] [Abelian.HasKInjectiveResolutions C']
    (F : A ⥤ B) [addF : F.Additive]
    (G : C ⥤ D) [addG : G.Additive]
    (F' : A' ⥤ B') [addFp : F'.Additive]
    (G' : C' ⥤ D') [addGp : G'.Additive]
    (R : A ⥤ C) [addR : R.Additive]
    [limR : PreservesFiniteLimits R] [colR : PreservesFiniteColimits R]
    (S : B ⥤ D) [addS : S.Additive]
    [limS : PreservesFiniteLimits S] [colS : PreservesFiniteColimits S]
    (R' : A' ⥤ C') [addRp : R'.Additive]
    [limRp : PreservesFiniteLimits R'] [colRp : PreservesFiniteColimits R']
    (S' : B' ⥤ D') [addSp : S'.Additive]
    [limSp : PreservesFiniteLimits S'] [colSp : PreservesFiniteColimits S']
    (U : A ⥤ A') [addU : U.Additive]
    [limU : PreservesFiniteLimits U] [colU : PreservesFiniteColimits U]
    (V : B ⥤ B') [addV : V.Additive]
    [limV : PreservesFiniteLimits V] [colV : PreservesFiniteColimits V]
    (P : C ⥤ C') [addP : P.Additive]
    [limP : PreservesFiniteLimits P] [colP : PreservesFiniteColimits P]
    (Q : D ⥤ D') [addQ : Q.Additive]
    [limQ : PreservesFiniteLimits Q] [colQ : PreservesFiniteColimits Q]

private def normalized_square
    (a : F ⋙ S ≅ R ⋙ G)
    (d : F.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅
      R.mapDerivedCategory ⋙ G.rightDerivedFunctor) : Prop :=
  ∀ I : CochainComplex A ℤ,
    S.mapDerivedCategory.map (canonical_cochain_unit F I) ≫
      d.hom.app (DerivedCategory.Q.obj I) ≫
      G.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app I) =
    S.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I) ≫
      canonical_cochain_unit G ((R.mapHomologicalComplex (.up ℤ)).obj I)

private theorem normalized_equivalence_square_exists
    [eqR : R.IsEquivalence] [eqS : S.IsEquivalence] (a : F ⋙ S ≅ R ⋙ G) :
    ∃ d : F.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅
      R.mapDerivedCategory ⋙ G.rightDerivedFunctor,
      normalized_square F G R S a d := by
  let ηF := derivedCochainRightUnit F F.rightDerivedFunctor F.rightDerivedFunctorUnit
  let ηG := derivedCochainRightUnit G G.rightDerivedFunctor G.rightDerivedFunctorUnit
  letI : F.rightDerivedFunctor.IsLeftKanExtension ηF :=
    cochainRightUnit_universal F F.rightDerivedFunctor F.rightDerivedFunctorUnit
  letI : G.rightDerivedFunctor.IsLeftKanExtension ηG :=
    cochainRightUnit_universal G G.rightDerivedFunctor G.rightDerivedFunctorUnit
  letI : R.asEquivalence.functor.Additive := by change R.Additive; infer_instance
  letI : S.asEquivalence.functor.Additive := by change S.Additive; infer_instance
  obtain ⟨d, hd⟩ := rightDerivedSquare R.asEquivalence S.asEquivalence F G
    F.rightDerivedFunctor G.rightDerivedFunctor ηF ηG a
  refine ⟨d, fun I ↦ ?_⟩
  have huF : ηF.app I = canonical_cochain_unit F I := by
    rw [cochainRightUnit_app_eq, canonical_cochain_unit_eq_unit]
  have huG : ηG.app ((R.mapHomologicalComplex (.up ℤ)).obj I) =
      canonical_cochain_unit G ((R.mapHomologicalComplex (.up ℤ)).obj I) := by
    rw [cochainRightUnit_app_eq, canonical_cochain_unit_eq_unit]
  have hdI := hd I
  change S.mapDerivedCategory.map (ηF.app I) ≫ d.hom.app _ ≫
      G.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app I) =
    S.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I) ≫
      ηG.app ((R.mapHomologicalComplex (.up ℤ)).obj I) at hdI
  rw [huF, huG] at hdI
  exact hdI

private theorem normalized_cube
    (a : F ⋙ S ≅ R ⋙ G) (b : F' ⋙ S' ≅ R' ⋙ G')
    (e : F ⋙ V ≅ U ⋙ F') (h : G ⋙ Q ≅ P ⋙ G')
    (r : R ⋙ P ≅ U ⋙ R') (s : S ⋙ Q ≅ V ⋙ S')
    (da : F.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅
      R.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (db : F'.rightDerivedFunctor ⋙ S'.mapDerivedCategory ≅
      R'.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (de : F.rightDerivedFunctor ⋙ V.mapDerivedCategory ≅
      U.mapDerivedCategory ⋙ F'.rightDerivedFunctor)
    (dh : G.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (ha : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      S.mapDerivedCategory.map (canonical_cochain_unit F I) ≫
        da.hom.app (DerivedCategory.Q.obj I) ≫
        G.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app I) =
      S.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I) ≫
        canonical_cochain_unit G ((R.mapHomologicalComplex (.up ℤ)).obj I))
    (hb : normalized_square F' G' R' S' b db)
    (he : normalized_square F F' U V e de)
    (hh : normalized_square G G' P Q h dh)
    (hc : ∀ M : A,
      Q.map (a.hom.app M) ≫ h.hom.app (R.obj M) ≫ G'.map (r.hom.app M) =
        s.hom.app (F.obj M) ≫ S'.map (e.hom.app M) ≫ b.hom.app (U.obj M)) :
    let dr := Functor.mapDerivedCategoryCompIso R P ≪≫
      Functor.mapDerivedCategoryNatIso r ≪≫ (Functor.mapDerivedCategoryCompIso U R').symm
    let ds := Functor.mapDerivedCategoryCompIso S Q ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso V S').symm
    ∀ M : DerivedCategory A,
      Q.mapDerivedCategory.map (da.hom.app M) ≫
        dh.hom.app (R.mapDerivedCategory.obj M) ≫
        G'.rightDerivedFunctor.map (dr.hom.app M) =
      ds.hom.app (F.rightDerivedFunctor.obj M) ≫
        S'.mapDerivedCategory.map (de.hom.app M) ≫
        db.hom.app (U.mapDerivedCategory.obj M) := by
  let dr := Functor.mapDerivedCategoryCompIso R P ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫ (Functor.mapDerivedCategoryCompIso U R').symm
  let ds := Functor.mapDerivedCategoryCompIso S Q ≪≫
    Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso V S').symm
  let x : F.rightDerivedFunctor ⋙ S.mapDerivedCategory ⋙ Q.mapDerivedCategory ⟶
      U.mapDerivedCategory ⋙ R'.mapDerivedCategory ⋙ G'.rightDerivedFunctor :=
    Functor.whiskerRight da.hom Q.mapDerivedCategory ≫
      Functor.whiskerLeft R.mapDerivedCategory dh.hom ≫
      Functor.whiskerRight dr.hom G'.rightDerivedFunctor
  let y : F.rightDerivedFunctor ⋙ S.mapDerivedCategory ⋙ Q.mapDerivedCategory ⟶
      U.mapDerivedCategory ⋙ R'.mapDerivedCategory ⋙ G'.rightDerivedFunctor :=
    Functor.whiskerLeft F.rightDerivedFunctor ds.hom ≫
      Functor.whiskerRight de.hom S'.mapDerivedCategory ≫
      Functor.whiskerLeft U.mapDerivedCategory db.hom
  suffices hxy : x = y from fun M ↦ NatTrans.congr_app hxy M
  apply derived_natTrans_ext_on_kinjectives
  intro I hI
  have := canonical_cochain_unit_isIso F I
  apply (cancel_epi (Q.mapDerivedCategory.map
    (S.mapDerivedCategory.map (canonical_cochain_unit F I)))).mp
  dsimp only [x, y, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  have hn := ds.hom.naturality (canonical_cochain_unit F I)
  dsimp only [Functor.comp_map] at hn
  apply (cancel_mono (G'.rightDerivedFunctor.map
      (R'.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app I)) ≫
    G'.rightDerivedFunctor.map (R'.mapDerivedCategoryFactors.hom.app
      ((U.mapHomologicalComplex (.up ℤ)).obj I)))).mp
  try simp only [Category.assoc]
  have nh := dh.hom.naturality (R.mapDerivedCategoryFactors.hom.app I)
  dsimp only [Functor.comp_map] at nh
  -- Move the source restriction factor through the completed direct-image square.
  have fr := Functor.face_fac R P U R' r I
  change dr.hom.app (DerivedCategory.Q.obj I) ≫
    R'.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app I) ≫
      R'.mapDerivedCategoryFactors.hom.app
        ((U.mapHomologicalComplex (.up ℤ)).obj I) = _ at fr
  erw [← G'.rightDerivedFunctor.map_comp, ← G'.rightDerivedFunctor.map_comp,
    fr, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  erw [← reassoc_of% nh]
  have haI := congrArg Q.mapDerivedCategory.map (ha I)
  try simp only [Functor.map_comp, Category.assoc] at haI
  erw [reassoc_of% haI]
  try simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (hh ((R.mapHomologicalComplex (.up ℤ)).obj I))]
  try simp only [Functor.map_comp, Category.assoc]
  have nb := db.hom.naturality (U.mapDerivedCategoryFactors.hom.app I)
  dsimp only [Functor.comp_map] at nb
  erw [← reassoc_of% nb, reassoc_of% hn]
  have heI := congrArg S'.mapDerivedCategory.map (he I)
  simp only [Functor.map_comp, Category.assoc] at heI
  erw [reassoc_of% heI]
  try simp only [Functor.map_comp, Category.assoc]
  erw [← S'.mapDerivedCategory.map_comp_assoc]
  erw [hb ((U.mapHomologicalComplex (.up ℤ)).obj I)]
  try simp only [Functor.map_comp, Category.assoc]
  have fv := Functor.face_fac S Q V S' s
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  change ds.hom.app _ ≫ _ = _ at fv
  let ac := (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I
  let rc := (NatIso.mapHomologicalComplex r (.up ℤ)).hom.app I
  have nf := S'.mapDerivedCategoryFactors.hom.naturality ec
  dsimp only [Functor.comp_map] at nf
  erw [reassoc_of% nf, reassoc_of% fv]
  have np := Q.mapDerivedCategoryFactors.hom.naturality ac
  dsimp only [Functor.comp_map] at np
  erw [reassoc_of% np]
  have nu := (derivedCochainRightUnit G' G'.rightDerivedFunctor
    G'.rightDerivedFunctorUnit).naturality rc
  dsimp only [Functor.comp_map] at nu
  have nu' : DerivedCategory.Q.map ((G'.mapHomologicalComplex (.up ℤ)).map rc) ≫
      canonical_cochain_unit G' _ =
    canonical_cochain_unit G' _ ≫ G'.rightDerivedFunctor.map
      (DerivedCategory.Q.map rc) := by
    unfold canonical_cochain_unit
    exact nu
  erw [← nu']
  have hc' :
      (Q.mapHomologicalComplex (.up ℤ)).map ac ≫
        (NatIso.mapHomologicalComplex h (.up ℤ)).hom.app
          ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (G'.mapHomologicalComplex (.up ℤ)).map rc =
      (NatIso.mapHomologicalComplex s (.up ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (S'.mapHomologicalComplex (.up ℤ)).map ec ≫
        (NatIso.mapHomologicalComplex b (.up ℤ)).hom.app
          ((U.mapHomologicalComplex (.up ℤ)).obj I) := by
    ext k
    exact hc (I.X k)
  have hqc := congrArg DerivedCategory.Q.map hc'
  simp only [Functor.map_comp, Category.assoc] at hqc
  erw [reassoc_of% hqc]
  rfl

end NormalizedCube

-- Compare the detailed sf coefficients with the completed adic presentation.

section Comparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

private noncomputable def finite_coefficient_iso
    (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (pbcAdicRings W (pbcIntegralDatum l E)).obj (Opposite.op n) ≅
      integralCoefficientCommRingSheaf l E W n :=
  (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).symm ≪≫
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).mapIso
      (integralCoefficientULift l E n).toCommRingCatIso

private theorem coefficient_projection
    (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (purCoefficientIso l E W).hom ≫
        completedIntegralCommRingProjectionUnrestricted l E W n =
      pbcAdicProjection W (pbcIntegralDatum l E) n ≫
        (finite_coefficient_iso l E W n).hom := by
  apply (adicLisseForget W).map_injective
  have he := congrArg Iso.hom (purCoefficientIso_existsUnique l E W).exists.choose_spec
  change (adicLisseForget W).map (purCoefficientIso l E W).hom =
    (integralDetailedCoefficientComparison W l E).hom at he
  rw [Functor.map_comp, he]
  change (integralDetailedCoefficientComparison W l E).hom ≫
      limit.π (integralCoefficientSheafSystem l E W) (Opposite.op n) = _
  exact (integralDetailedCoefficientComparison_exists W l E).exists.choose_spec n

private theorem finite_coefficient_square (n : ℕ) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (finite_coefficient_iso l E Y n).hom ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) =
    completedFiniteCoefficientMap f (pbcIntegralDatum l E) n ≫
      (finite_coefficient_iso l E X n).hom := by
  dsimp only [finite_coefficient_iso, completedFiniteCoefficientMap, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun z ↦ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
    (pbcLevelConstantComparison Y (pbcIntegralDatum l E) n).inv ≫ z)
      (proEtaleConstantInverseImageMap_naturality f
        (integralCoefficientULift l E n).toCommRingCatIso.hom)

private noncomputable def coefficient_inverse_image_iso :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E Y) ≅
      completedIntegralCommRingSheafUnrestricted l E X :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
      (purCoefficientIso l E Y).symm ≪≫
    (have := completedCoefficient_isIso f (pbcIntegralDatum l E)
     asIso (AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E))) ≪≫
      purCoefficientIso l E X

private theorem coefficient_inverse_image_projection (n : ℕ) :
    (coefficient_inverse_image_iso l E f).hom ≫
        completedIntegralCommRingProjectionUnrestricted l E X n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
        proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let P := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  dsimp only [coefficient_inverse_image_iso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [Category.assoc]
  rw [coefficient_projection, ← Category.assoc
    (AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E)),
    completedCoefficient_projection]
  simp only [Category.assoc]
  rw [← finite_coefficient_square]
  change P.map (purCoefficientIso l E Y).inv ≫
      P.map (pbcAdicProjection Y (pbcIntegralDatum l E) n) ≫
      P.map (finite_coefficient_iso l E Y n).hom ≫ _ = _
  have hp := coefficient_projection l E Y n
  have hh : (purCoefficientIso l E Y).inv ≫
      pbcAdicProjection Y (pbcIntegralDatum l E) n ≫
        (finite_coefficient_iso l E Y n).hom =
      completedIntegralCommRingProjectionUnrestricted l E Y n := by
    rw [← hp, Iso.inv_hom_id_assoc]
  change P.map (purCoefficientIso l E Y).inv ≫
      P.map (pbcAdicProjection Y (pbcIntegralDatum l E) n) ≫
      P.map (finite_coefficient_iso l E Y n).hom ≫ _ = _
  simp only [← P.map_comp_assoc, ← P.map_comp, hh]
  rfl

private theorem coefficient_direct_image_eq :
    proEtaleRingDirectImageMap f
        (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X)
        (coefficient_inverse_image_iso l E f) = sfCompletedCoefficientMap l E f := by
  apply (sfCompletedCoefficientMap_existsUnique l E f).unique
  · intro n
    let G := proEtaleSheafDirectImage f CommRingCat.{u + 1}
    let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
    change adj.unit.app _ ≫ G.map (coefficient_inverse_image_iso l E f).hom ≫
        G.map (completedIntegralCommRingProjectionUnrestricted l E X n) = _
    rw [← G.map_comp, coefficient_inverse_image_projection, G.map_comp]
    have hn := adj.unit_naturality
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
    rw [reassoc_of% hn]
    congr 1
    change (adj.homEquiv _ _)
      (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} _) = _
    exact (adj.homEquiv _ _).apply_symm_apply _
  · exact (sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec

private theorem completed_direct_image_eq :
    proEtaleRingModuleDirectImage f
        (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X)
        (coefficient_inverse_image_iso l E f) = sfCompletedModuleDirectImage l E f := by
  unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
  rw [coefficient_direct_image_eq]

private theorem completed_derived_products :
    PreservesLimitsOfShape (Discrete ℕ) (sfCompletedDerivedDirectImage l E f) := by
  let adj := proEtaleRingDerivedAdjunction f
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X) (coefficient_inverse_image_iso l E f)
  have h := adj.rightAdjoint_preservesLimits
  let e := Functor.rightDerivedFunctorNatIso
    (eqToIso (completed_direct_image_eq l E f))
  exact preservesLimitsOfShape_of_natIso e

private theorem completed_coefficient_square :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (purCoefficientIso l E Y).hom ≫ (coefficient_inverse_image_iso l E f).hom =
      AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E) ≫
        (purCoefficientIso l E X).hom := by
  dsimp only [coefficient_inverse_image_iso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private noncomputable def finite_inverse_image_iso (n : ℕ) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (integralCoefficientCommRingSheaf l E Y n) ≅
      integralCoefficientCommRingSheaf l E X n :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
      (finite_coefficient_iso l E Y n).symm ≪≫
    asIso (completedFiniteCoefficientMap f (pbcIntegralDatum l E) n) ≪≫
      finite_coefficient_iso l E X n

private theorem finite_inverse_image_eq (n : ℕ) :
    (finite_inverse_image_iso l E f n).hom =
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  apply (cancel_epi ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
    (finite_coefficient_iso l E Y n).hom)).mp
  dsimp only [finite_inverse_image_iso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (finite_coefficient_square l E f n).symm

private noncomputable def completed_ordinary_comparison :
    sfCompletedModuleDirectImage l E f ⋙
        pbcRestrict (purCoefficientIso l E Y).hom ≅
      pbcRestrict (purCoefficientIso l E X).hom ⋙
        completedModuleDirectImage f (pbcIntegralDatum l E) := by
  let c := coefficient_inverse_image_iso l E f
  have := completedCoefficient_isIso f (pbcIntegralDatum l E)
  let d := proEtaleRingRestrictionDirectImage f
    (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (completedIntegralCommRingSheafUnrestricted l E X)
    (purCoefficientIso l E Y).hom (purCoefficientIso l E X).hom
    (asIso (AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E))) c
    (completed_coefficient_square l E f).symm
  exact Functor.isoWhiskerRight
    (eqToIso (completed_direct_image_eq l E f)).symm
      (pbcRestrict (purCoefficientIso l E Y).hom) ≪≫ d

private theorem finite_direct_image_eq (n : ℕ) : proEtaleRingModuleDirectImage f
    (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (finite_inverse_image_iso l E f n) =
    proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) := by
  unfold proEtaleRingModuleDirectImage proEtaleRingDirectImageMap
  rw [finite_inverse_image_eq]
  have h := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv
  change SheafOfModules.pushforward _ = SheafOfModules.pushforward _
  congr 1
  apply Sheaf.hom_ext
  change Functor.whiskerRight _ _ = Functor.whiskerRight _ _
  congr 1
  apply congrArg (fun z : integralCoefficientCommRingSheaf l E Y n ⟶
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      (integralCoefficientCommRingSheaf l E X n) ↦ z.hom)
  change ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
    (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
      (proEtaleCoefficientDirectImageMap f
        (Padic.coefficientExtensionRing l E (n + 1)))) = _
  exact Equiv.apply_symm_apply _ _

private noncomputable def finite_ordinary_comparison (n : ℕ) :
    proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pbcRestrict (finite_coefficient_iso l E Y n).hom ≅
      pbcRestrict (finite_coefficient_iso l E X n).hom ⋙
        completedFiniteModuleDirectImage f (pbcIntegralDatum l E) n := by
  let c := finite_inverse_image_iso l E f n
  let d := proEtaleRingRestrictionDirectImage f
    ((pbcAdicRings Y (pbcIntegralDatum l E)).obj (Opposite.op n))
    (integralCoefficientCommRingSheaf l E Y n)
    ((pbcAdicRings X (pbcIntegralDatum l E)).obj (Opposite.op n))
    (integralCoefficientCommRingSheaf l E X n)
    (finite_coefficient_iso l E Y n).hom (finite_coefficient_iso l E X n).hom
    (asIso (completedFiniteCoefficientMap f (pbcIntegralDatum l E) n)) c
    (by rw [finite_inverse_image_eq]; exact (finite_coefficient_square l E f n).symm)
  have := proEtaleConstantModuleDirectImage_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  exact Functor.isoWhiskerRight (eqToIso (finite_direct_image_eq l E f n)).symm
    (pbcRestrict (finite_coefficient_iso l E Y n).hom) ≪≫ d

private noncomputable def coefficient_restriction_square
    (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    scalarReductionRestriction.{u, u} l E W n ⋙
        pbcRestrict (purCoefficientIso l E W).hom ≅
      pbcRestrict (finite_coefficient_iso l E W n).hom ⋙
        pbcRestrict (pbcAdicProjection W (pbcIntegralDatum l E) n) :=
  IntegralCoefficientPresentation.restrictionSquare
    (purCoefficientIso l E W).hom
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (pbcAdicProjection W (pbcIntegralDatum l E) n)
    (finite_coefficient_iso l E W n).hom (coefficient_projection l E W n)

private theorem eqToIso_app_sections
    {W : AlgebraicGeometry.Scheme.{u}}
    {R : Sheaf (ProEt.topology W) RingCat.{u + 1}}
    {C : Type*} [Category C] {F G : C ⥤ SheafOfModules.{u + 1} R}
    (h : F = G) (M : C) (U : W.ProEtᵒᵖ) (x : (G.obj M).val.obj U) :
    HEq (((eqToIso h).inv.app M).val.app U x) x := by
  subst G
  rfl

private theorem completed_ordinary_sections
    (M : scalarReductionSource.{u, u} l E X) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange f).op.obj U)) :
    (((completed_ordinary_comparison l E f).hom.app M).val.app U) x = x := by
  have := completedCoefficient_isIso f (pbcIntegralDatum l E)
  dsimp only [completed_ordinary_comparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  change _ = x
  have hs := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique f
    (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (completedIntegralCommRingSheafUnrestricted l E X)
    (purCoefficientIso l E Y).hom (purCoefficientIso l E X).hom
    (asIso (AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E)))
    (coefficient_inverse_image_iso l E f)
    (completed_coefficient_square l E f).symm)).1
  change ((proEtaleRingRestrictionDirectImage f
    (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (completedIntegralCommRingSheafUnrestricted l E X)
    (purCoefficientIso l E Y).hom (purCoefficientIso l E X).hom
    (asIso (AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E)))
    (coefficient_inverse_image_iso l E f)
    (completed_coefficient_square l E f).symm).hom.app M).val.app U
      (((eqToIso (completed_direct_image_eq l E f)).symm.hom.app M).val.app U x) = x
  change _ = x
  exact (hs M U _).trans
    (eq_of_heq (eqToIso_app_sections (completed_direct_image_eq l E f) M U x))

private theorem finite_ordinary_sections (n : ℕ)
    (M : scalarReductionTarget.{u, u} l E X n) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange f).op.obj U)) :
    (((finite_ordinary_comparison l E f n).hom.app M).val.app U) x = x := by
  dsimp only [finite_ordinary_comparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  change _ = x
  have hs := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique f
    ((pbcAdicRings Y (pbcIntegralDatum l E)).obj (Opposite.op n))
    (integralCoefficientCommRingSheaf l E Y n)
    ((pbcAdicRings X (pbcIntegralDatum l E)).obj (Opposite.op n))
    (integralCoefficientCommRingSheaf l E X n)
    (finite_coefficient_iso l E Y n).hom (finite_coefficient_iso l E X n).hom
    (asIso (completedFiniteCoefficientMap f (pbcIntegralDatum l E) n))
    (finite_inverse_image_iso l E f n)
    (by rw [finite_inverse_image_eq]; exact (finite_coefficient_square l E f n).symm))).1
  change ((proEtaleRingRestrictionDirectImage f
    ((pbcAdicRings Y (pbcIntegralDatum l E)).obj (Opposite.op n))
    (integralCoefficientCommRingSheaf l E Y n)
    ((pbcAdicRings X (pbcIntegralDatum l E)).obj (Opposite.op n))
    (integralCoefficientCommRingSheaf l E X n)
    (finite_coefficient_iso l E Y n).hom (finite_coefficient_iso l E X n).hom
    (asIso (completedFiniteCoefficientMap f (pbcIntegralDatum l E) n))
    (finite_inverse_image_iso l E f n)
    (by rw [finite_inverse_image_eq]; exact (finite_coefficient_square l E f n).symm)).hom.app
      M).val.app U
      _ = x
  change _ = x
  exact (hs M U _).trans
    (eq_of_heq (eqToIso_app_sections (finite_direct_image_eq l E f n) M U x))

private theorem pbc_ordinary_inverse_sections (n : ℕ)
    (M : pbcModules X ((pbcAdicRings X (pbcIntegralDatum l E)).obj (Opposite.op n)))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj ((proEtaleBaseChange f).op.obj U)) :
    (((completedRestrictionDirectImageIso f (pbcIntegralDatum l E) n).inv.app M).val.app U)
      x = x := by
  let e := completedRestrictionDirectImageIso f (pbcIntegralDatum l E) n
  have hn := (completedRestrictionDirectImageIso_exists f
    (pbcIntegralDatum l E) n).exists.choose_spec M U ((e.inv.app M).val.app U x)
  have hi := congrArg (fun t ↦ t.val.app U x) (e.inv_hom_id_app M)
  change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at hi
  exact hn.symm.trans hi

private theorem ordinary_cube (n : ℕ) (M : scalarReductionTarget.{u, u} l E X n) :
    (pbcRestrict (purCoefficientIso l E Y).hom).map
        ((sfDirectImageRestrictionComparison l E f n).hom.app M) ≫
      (completed_ordinary_comparison l E f).hom.app
        ((scalarReductionRestriction.{u, u} l E X n).obj M) ≫
      (completedModuleDirectImage f (pbcIntegralDatum l E)).map
        ((coefficient_restriction_square l E X n).hom.app M) =
    (coefficient_restriction_square l E Y n).hom.app
        ((proEtaleConstantModuleDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).obj M) ≫
      (pbcRestrict (pbcAdicProjection Y (pbcIntegralDatum l E) n)).map
        ((finite_ordinary_comparison l E f n).hom.app M) ≫
      (completedRestrictionDirectImageIso f (pbcIntegralDatum l E) n).inv.app
        ((pbcRestrict (finite_coefficient_iso l E X n).hom).obj M) := by
  ext U x
  change (((coefficient_restriction_square l E X n).hom.app M).val.app
      ((proEtaleBaseChange f).op.obj U))
      ((((completed_ordinary_comparison l E f).hom.app
        ((scalarReductionRestriction.{u, u} l E X n).obj M)).val.app U)
        ((((sfDirectImageRestrictionComparison l E f n).hom.app M).val.app U) x)) =
    (((completedRestrictionDirectImageIso f (pbcIntegralDatum l E) n).inv.app
        ((pbcRestrict (finite_coefficient_iso l E X n).hom).obj M)).val.app U)
      ((((finite_ordinary_comparison l E f n).hom.app M).val.app U)
        ((((coefficient_restriction_square l E Y n).hom.app
          ((proEtaleConstantModuleDirectImage f
            (Padic.coefficientExtensionRing l E (n + 1))).obj M)).val.app U) x))
  have ha := (sfDirectImageRestrictionComparison_existsUnique l E f n).exists.choose_spec
    M U x
  have hh := completed_ordinary_sections l E f
    ((scalarReductionRestriction.{u, u} l E X n).obj M) U x
  have he := finite_ordinary_sections l E f n M U x
  have hr := IntegralCoefficientPresentation.restrictionSquare_hom
    (purCoefficientIso l E X).hom
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (pbcAdicProjection X (pbcIntegralDatum l E) n)
    (finite_coefficient_iso l E X n).hom (coefficient_projection l E X n)
    M ((proEtaleBaseChange f).op.obj U) x
  have hs := IntegralCoefficientPresentation.restrictionSquare_hom
    (purCoefficientIso l E Y).hom
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
    (pbcAdicProjection Y (pbcIntegralDatum l E) n)
    (finite_coefficient_iso l E Y n).hom (coefficient_projection l E Y n)
    ((proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).obj M) U x
  have hb := pbc_ordinary_inverse_sections l E f n
    ((pbcRestrict (finite_coefficient_iso l E X n).hom).obj M) U x
  change (((sfDirectImageRestrictionComparison l E f n).hom.app M).val.app U) x = x at ha
  change (((coefficient_restriction_square l E X n).hom.app M).val.app
    ((proEtaleBaseChange f).op.obj U)) x = x at hr
  change (((coefficient_restriction_square l E Y n).hom.app
    ((proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).obj M)).val.app U) x = x at hs
  exact ((congrArg
    (fun z ↦ (((coefficient_restriction_square l E X n).hom.app M).val.app
      ((proEtaleBaseChange f).op.obj U)) z)
    ((congrArg
      (fun z ↦ (((completed_ordinary_comparison l E f).hom.app
        ((scalarReductionRestriction.{u, u} l E X n).obj M)).val.app U) z) ha).trans hh)).trans
    hr).trans
      (((congrArg
        (fun z ↦ (((completedRestrictionDirectImageIso f (pbcIntegralDatum l E) n).inv.app
          ((pbcRestrict (finite_coefficient_iso l E X n).hom).obj M)).val.app U) z)
        ((congrArg
          (fun z ↦ (((finite_ordinary_comparison l E f n).hom.app M).val.app U) z)
          hs).trans he)).trans hb).symm)

private theorem pbc_restriction_normalization (n : ℕ) :
    normalized_square
      (completedFiniteModuleDirectImage f (pbcIntegralDatum l E) n)
      (completedModuleDirectImage f (pbcIntegralDatum l E))
      (pbcRestrict (pbcAdicProjection X (pbcIntegralDatum l E) n))
      (pbcRestrict (pbcAdicProjection Y (pbcIntegralDatum l E) n))
      (completedRestrictionDirectImageIso f (pbcIntegralDatum l E) n).symm
      (completedDerivedRestrictionDirectImageIso f (pbcIntegralDatum l E) n).symm := by
  let d := pbcIntegralDatum l E
  let RX := pbcRestrict (pbcAdicProjection X d n)
  let RY := pbcRestrict (pbcAdicProjection Y d n)
  let F := completedModuleDirectImage f d
  let G := completedFiniteModuleDirectImage f d n
  have uF (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
      completedDirectImageComplexUnit f d C = canonical_cochain_unit F C := by
    have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app C = 𝟙 _ := rfl
    dsimp only [completedDirectImageComplexUnit]
    rw [canonical_cochain_unit_eq_unit]
    rw [hid]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    change 𝟙 _ ≫ _ ≫ F.rightDerivedFunctor.map (𝟙 _) = _
    simp
    rfl
  have uG (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (Opposite.op n))) ℤ) :
      completedFiniteDirectImageComplexUnit f d n C = canonical_cochain_unit G C := by
    have hid : (G.mapHomotopyCategoryFactors (.up ℤ)).inv.app C = 𝟙 _ := rfl
    dsimp only [completedFiniteDirectImageComplexUnit]
    rw [canonical_cochain_unit_eq_unit]
    rw [hid]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    change 𝟙 _ ≫ _ ≫ G.rightDerivedFunctor.map (𝟙 _) = _
    simp
    rfl
  intro C
  have hh := (completedDerivedRestrictionDirectImageIso_exists f d n).exists.choose_spec C
  have h := (inverse_square_iff
    ((completedDerivedRestrictionDirectImageIso f d n).symm.app (DerivedCategory.Q.obj C))
    (RY.mapDerivedCategoryFactors.app ((G.mapHomologicalComplex (.up ℤ)).obj C))
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (completedRestrictionDirectImageIso f d n).symm (.up ℤ)).app C))
    (F.rightDerivedFunctor.mapIso (RX.mapDerivedCategoryFactors.app C))
    (RY.mapDerivedCategory.map (completedFiniteDirectImageComplexUnit f d n C))
    (completedDirectImageComplexUnit f d
      ((RX.mapHomologicalComplex (.up ℤ)).obj C))).1 hh
  simpa only [uF, uG, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv] using h

private theorem sf_restriction_normalization (n : ℕ)
    (J : CochainComplex (scalarReductionTarget.{u, u} l E X n) ℤ) [J.IsKInjective] :
    (scalarReductionDerivedRestriction.{u, u} l E Y n).map
        (canonical_cochain_unit (proEtaleConstantModuleDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))) J) ≫
      (sfDerivedRestrictionComparison l E f n).inv.app (DerivedCategory.Q.obj J) ≫
      (sfCompletedDerivedDirectImage l E f).map
        ((scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactors.hom.app J) =
    (scalarReductionRestriction.{u, u} l E Y n).mapDerivedCategoryFactors.hom.app
        (((proEtaleConstantModuleDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
            (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (sfDirectImageRestrictionComparison l E f n) (.up ℤ)).hom.app J) ≫
      canonical_cochain_unit (sfCompletedModuleDirectImage l E f)
        (((scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex
          (.up ℤ)).obj J) := by
  let F := proEtaleConstantModuleDirectImage f
    (Padic.coefficientExtensionRing l E (n + 1))
  let G := sfCompletedModuleDirectImage l E f
  let R := scalarReductionRestriction.{u, u} l E X n
  let S := scalarReductionRestriction.{u, u} l E Y n
  obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    ((R.mapHomologicalComplex (.up ℤ)).obj J)
  have := hI
  have := hj
  let d := sfDerivedRestrictionComparison l E f n
  have hn := (sfDerivedRestrictionComparison_existsUnique l E f n).exists.choose_spec J I j
  have hu : canonical_cochain_unit G ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
      G.rightDerivedFunctor.map (DerivedCategory.Q.map j) ≫
      (G.rightDerivedFunctorObjQIso I).hom =
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j) := by
    have hnat := G.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.quotient _ (.up ℤ)).map j)
    simp only [canonical_cochain_unit_eq_unit]
    change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I) =
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj J)) ≫
        G.rightDerivedFunctor.map (DerivedCategory.Q.map j) at hnat
    erw [← Category.assoc, ← hnat]
    erw [← canonical_cochain_unit_eq_unit, canonical_cochain_unit_objQIso]
    simp
  apply (cancel_mono (G.rightDerivedFunctor.map (DerivedCategory.Q.map j) ≫
    (G.rightDerivedFunctorObjQIso I).hom)).mp
  simp only [Category.assoc]
  erw [hu]
  erw [← hn]
  simp only [canonical_cochain_unit_objQIso, sfDerivedRestrictionComparison,
    Category.assoc, Iso.inv_hom_id_app_assoc,
    ← S.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id, S.mapDerivedCategory.map_id,
    Category.id_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

-- Apply the normalized cube and then transport the finite projection-formula mate.

-- Give the mate a fixed hom type before asking for its invertibility.
private noncomputable def sf_projection_map (n : ℕ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (scalarReductionDerivedExtension.{u, u} l E Y n).obj
        ((sfCompletedDerivedDirectImage l E f).obj K) ⟶
      sfFiniteDerivedDirectImage l E f K n :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose.homEquiv
    ((sfCompletedDerivedDirectImage l E f).obj K)
    (sfFiniteDerivedDirectImage l E f K n)).symm
    ((sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionUnit l E X n).app K) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))

private theorem sf_projection_map_eq (n : ℕ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    sf_projection_map l E f n K =
      ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose.homEquiv
        ((sfCompletedDerivedDirectImage l E f).obj K)
        (sfFiniteDerivedDirectImage l E f K n)).symm
        ((sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionUnit l E X n).app K) ≫
          (sfDerivedRestrictionComparison l E f n).hom.app
            ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) := rfl

attribute [local irreducible] sf_projection_map

section ProjectionTransport
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] proEtaleConstantModuleDirectImage sfCompletedModuleDirectImage
  completedModuleDirectImage sfDerivedRestrictionComparison
  completedDerivedRestrictionDirectImageIso
attribute [local irreducible] finite_ordinary_comparison completed_ordinary_comparison
  coefficient_restriction_square

private theorem sf_projection_formula (n : ℕ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    IsIso (C := DerivedCategory (scalarReductionTarget.{u, u} l E Y n))
      (sf_projection_map l E f n K) := by
  letI : Abelian.HasKInjectiveResolutions (scalarReductionTarget.{u, u} l E X n) :=
    proEtaleRingModules_hasKInjectiveResolutions X (integralCoefficientCommRingSheaf l E X n)
  let d := pbcIntegralDatum l E
  letI : Abelian.HasKInjectiveResolutions
      (pbcModules X ((pbcAdicRings X d).obj (Opposite.op n))) :=
    proEtaleRingModules_hasKInjectiveResolutions X
      ((pbcAdicRings X d).obj (Opposite.op n))
  letI : Abelian.HasKInjectiveResolutions (pbcModules X (pbcAdicCompletion X d)) :=
    proEtaleRingModules_hasKInjectiveResolutions X (pbcAdicCompletion X d)
  let R := scalarReductionRestriction.{u, u} l E X n
  let S := scalarReductionRestriction.{u, u} l E Y n
  let R' := pbcRestrict (pbcAdicProjection X d n)
  let S' := pbcRestrict (pbcAdicProjection Y d n)
  let U : scalarReductionTarget.{u, u} l E X n ⥤
      pbcModules X ((pbcAdicRings X d).obj (Opposite.op n)) :=
    pbcRestrict (finite_coefficient_iso l E X n).hom
  let V : scalarReductionTarget.{u, u} l E Y n ⥤
      pbcModules Y ((pbcAdicRings Y d).obj (Opposite.op n)) :=
    pbcRestrict (finite_coefficient_iso l E Y n).hom
  let P : scalarReductionSource.{u, u} l E X ⥤
      pbcModules X (pbcAdicCompletion X d) := pbcRestrict (purCoefficientIso l E X).hom
  let Q : scalarReductionSource.{u, u} l E Y ⥤
      pbcModules Y (pbcAdicCompletion Y d) := pbcRestrict (purCoefficientIso l E Y).hom
  letI : R.Additive := by
    change (pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E X n)).Additive
    exact pbcRestrict_additive _
  letI : PreservesFiniteLimits R := (scalarReductionRestriction_exact l E X n).1
  letI : PreservesFiniteColimits R := (scalarReductionRestriction_exact l E X n).2
  letI : S.Additive := by
    change (pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E Y n)).Additive
    exact pbcRestrict_additive _
  letI : PreservesFiniteLimits S := (scalarReductionRestriction_exact l E Y n).1
  letI : PreservesFiniteColimits S := (scalarReductionRestriction_exact l E Y n).2
  letI : R'.Additive := by exact pbcRestrict_additive _
  letI : PreservesFiniteLimits R' := pbcRestrict_limits _
  letI : PreservesFiniteColimits R' := pbcRestrict_colimits _
  letI : S'.Additive := by exact pbcRestrict_additive _
  letI : PreservesFiniteLimits S' := pbcRestrict_limits _
  letI : PreservesFiniteColimits S' := pbcRestrict_colimits _
  have hu (W : AlgebraicGeometry.Scheme.{u}) :
      (pbcRestrict (finite_coefficient_iso l E W n).hom).IsEquivalence :=
    restriction_isEquivalence ((adicLisseForget W).mapIso (finite_coefficient_iso l E W n))
  have hp (W : AlgebraicGeometry.Scheme.{u}) :
      (pbcRestrict (purCoefficientIso l E W).hom).IsEquivalence :=
    restriction_isEquivalence ((adicLisseForget W).mapIso (purCoefficientIso l E W))
  letI : U.Additive := pbcRestrict_additive _
  letI : V.Additive := pbcRestrict_additive _
  letI : P.Additive := pbcRestrict_additive _
  letI : Q.Additive := pbcRestrict_additive _
  letI : PreservesFiniteLimits U := pbcRestrict_limits _
  letI : PreservesFiniteLimits V := pbcRestrict_limits _
  letI : PreservesFiniteLimits P := pbcRestrict_limits _
  letI : PreservesFiniteLimits Q := pbcRestrict_limits _
  letI : PreservesFiniteColimits U := pbcRestrict_colimits _
  letI : PreservesFiniteColimits V := pbcRestrict_colimits _
  letI : PreservesFiniteColimits P := pbcRestrict_colimits _
  letI : PreservesFiniteColimits Q := pbcRestrict_colimits _
  letI : U.IsEquivalence := hu X
  letI : V.IsEquivalence := hu Y
  letI : P.IsEquivalence := hp X
  letI : Q.IsEquivalence := hp Y
  letI : (proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
    proEtaleConstantModuleDirectImage_additive f _
  letI : (sfCompletedModuleDirectImage l E f).Additive :=
    sfCompletedModuleDirectImage_additive l E f
  letI : (completedFiniteModuleDirectImage f d n).Additive :=
    proEtaleRingModuleDirectImage_additive f _ _ _
  letI : (completedModuleDirectImage f d).Additive := completedModuleDirectImage_additive f d
  obtain ⟨de, hde⟩ := normalized_equivalence_square_exists.{u + 2, u + 1, u + 2}
    (eqR := by exact hu X) (eqS := by exact hu Y)
    (addR := by exact pbcRestrict_additive _)
    (addS := by exact pbcRestrict_additive _)
    (limR := by exact pbcRestrict_limits _) (colR := by exact pbcRestrict_colimits _)
    (limS := by exact pbcRestrict_limits _) (colS := by exact pbcRestrict_colimits _)
    (proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)))
    (completedFiniteModuleDirectImage f d n) U V (finite_ordinary_comparison l E f n)
  obtain ⟨dh, hdh⟩ := normalized_equivalence_square_exists.{u + 2, u + 1, u + 2}
    (eqR := by exact hp X) (eqS := by exact hp Y)
    (addR := by exact pbcRestrict_additive _)
    (addS := by exact pbcRestrict_additive _)
    (limR := by exact pbcRestrict_limits _) (colR := by exact pbcRestrict_colimits _)
    (limS := by exact pbcRestrict_limits _) (colS := by exact pbcRestrict_colimits _)
    (sfCompletedModuleDirectImage l E f) (completedModuleDirectImage f d)
    P Q (completed_ordinary_comparison l E f)
  let r : R ⋙ P ≅ U ⋙ R' := coefficient_restriction_square l E X n
  let s : S ⋙ Q ≅ V ⋙ S' := coefficient_restriction_square l E Y n
  letI : (R ⋙ P).Additive := by infer_instance
  letI : (U ⋙ R').Additive := by infer_instance
  letI : (S ⋙ Q).Additive := by infer_instance
  letI : (V ⋙ S').Additive := by infer_instance
  let dr := Functor.mapDerivedCategoryCompIso R P ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫ (Functor.mapDerivedCategoryCompIso U R').symm
  let ds := Functor.mapDerivedCategoryCompIso S Q ≪≫
    Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso V S').symm
  have hc := normalized_cube.{u + 2, u + 1, u + 2}
    (addF := inferInstanceAs ((proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).Additive))
    (addG := inferInstanceAs ((sfCompletedModuleDirectImage l E f).Additive))
    (addFp := inferInstanceAs ((completedFiniteModuleDirectImage f d n).Additive))
    (addGp := inferInstanceAs ((completedModuleDirectImage f d).Additive))
    (addR := inferInstanceAs (R.Additive))
    (addS := inferInstanceAs (S.Additive))
    (addRp := inferInstanceAs (R'.Additive))
    (addSp := inferInstanceAs (S'.Additive))
    (addU := inferInstanceAs (U.Additive))
    (addV := inferInstanceAs (V.Additive))
    (addP := inferInstanceAs (P.Additive))
    (addQ := inferInstanceAs (Q.Additive))
    (limR := inferInstanceAs (PreservesFiniteLimits R))
    (colR := inferInstanceAs (PreservesFiniteColimits R))
    (limS := inferInstanceAs (PreservesFiniteLimits S))
    (colS := inferInstanceAs (PreservesFiniteColimits S))
    (limRp := inferInstanceAs (PreservesFiniteLimits R'))
    (colRp := inferInstanceAs (PreservesFiniteColimits R'))
    (limSp := inferInstanceAs (PreservesFiniteLimits S'))
    (colSp := inferInstanceAs (PreservesFiniteColimits S'))
    (limU := inferInstanceAs (PreservesFiniteLimits U))
    (colU := inferInstanceAs (PreservesFiniteColimits U))
    (limV := inferInstanceAs (PreservesFiniteLimits V))
    (colV := inferInstanceAs (PreservesFiniteColimits V))
    (limP := inferInstanceAs (PreservesFiniteLimits P))
    (colP := inferInstanceAs (PreservesFiniteColimits P))
    (limQ := inferInstanceAs (PreservesFiniteLimits Q))
    (colQ := inferInstanceAs (PreservesFiniteColimits Q))
    (proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)))
    (sfCompletedModuleDirectImage l E f)
    (completedFiniteModuleDirectImage f d n) (completedModuleDirectImage f d)
    R S R' S' U V P Q
    (sfDirectImageRestrictionComparison l E f n)
    (completedRestrictionDirectImageIso f d n).symm
    (finite_ordinary_comparison l E f n) (completed_ordinary_comparison l E f) r s
    (set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      (sfDerivedRestrictionComparison l E f n).symm)
    (set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      (completedDerivedRestrictionDirectImageIso f d n).symm) de dh
    (set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      sf_restriction_normalization l E f n)
    (set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      pbc_restriction_normalization l E f n)
    hde hdh (ordinary_cube l E f n)
  have hcube (N : DerivedCategory (scalarReductionTarget.{u, u} l E X n)) :
      Q.mapDerivedCategory.map ((sfDerivedRestrictionComparison l E f n).hom.app N) ≫
        ds.hom.app ((proEtaleConstantModuleDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctor.obj N) ≫
        S'.mapDerivedCategory.map (de.hom.app N) =
      dh.hom.app (R.mapDerivedCategory.obj N) ≫
        (completedModuleDirectImage f d).rightDerivedFunctor.map (dr.hom.app N) ≫
        (completedDerivedRestrictionDirectImageIso f d n).hom.app
          (U.mapDerivedCategory.obj N) := by
    exact
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      by
        let a := Q.mapDerivedCategory.mapIso
          ((sfDerivedRestrictionComparison l E f n).app N)
        let b := (completedDerivedRestrictionDirectImageIso f d n).app
          (U.mapDerivedCategory.obj N)
        let c₁ := ds.hom.app ((proEtaleConstantModuleDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctor.obj N)
        let c₂ := S'.mapDerivedCategory.map (de.hom.app N)
        let g₁ := dh.hom.app (R.mapDerivedCategory.obj N)
        let g₂ := (completedModuleDirectImage f d).rightDerivedFunctor.map (dr.hom.app N)
        let c := c₁ ≫ c₂
        let g := g₁ ≫ g₂
        have h₀ : a.inv ≫ g = c ≫ b.inv :=
          (hc N).trans (Category.assoc c₁ c₂ b.inv).symm
        have h₁ : g = a.hom ≫ (c ≫ b.inv) := (Iso.inv_comp_eq a).mp h₀
        have h₂ : g = (a.hom ≫ c) ≫ b.inv :=
          h₁.trans (Category.assoc a.hom c b.inv).symm
        have h₃ : g ≫ b.hom = a.hom ≫ c := (Iso.eq_comp_inv b).mp h₂
        exact h₃.symm.trans (Category.assoc g₁ g₂ b.hom)
  letI : U.mapDerivedCategory.IsEquivalence := by
    exact Functor.isEquivalence_mapDerivedCategory U
  letI : V.mapDerivedCategory.IsEquivalence := by
    exact Functor.isEquivalence_mapDerivedCategory V
  letI : P.mapDerivedCategory.IsEquivalence := by
    exact Functor.isEquivalence_mapDerivedCategory P
  letI : Q.mapDerivedCategory.IsEquivalence := by
    exact Functor.isEquivalence_mapDerivedCategory Q
  let ax := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
  let ay := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose
  let ax' := pbcDerivedScalarAdjunction (pbcAdicProjection X d n)
  let ay' := pbcDerivedScalarAdjunction (pbcAdicProjection Y d n)
  obtain ⟨sx, hsx⟩ := IntegralCoefficientPresentation.square_iso ax' ax
    P.mapDerivedCategory U.mapDerivedCategory dr.symm
  obtain ⟨sy, hsy⟩ := IntegralCoefficientPresentation.square_iso ay' ay
    Q.mapDerivedCategory V.mapDerivedCategory ds.symm
  erw [sf_projection_map_eq]
  exact
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    by
      refine projection_formula_transport
        (scalarReductionDerivedExtension.{u, u} l E X n) R.mapDerivedCategory
        (scalarReductionDerivedExtension.{u, u} l E Y n) S.mapDerivedCategory
        (pbcDerivedExtend (pbcAdicProjection X d n)) R'.mapDerivedCategory
        (pbcDerivedExtend (pbcAdicProjection Y d n)) S'.mapDerivedCategory
        ax ay ax' ay'
        (sfCompletedDerivedDirectImage l E f)
        (proEtaleConstantModuleDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctor
        (completedDerivedDirectImage f d) (completedFiniteDerivedDirectImage f d n)
        P.mapDerivedCategory Q.mapDerivedCategory U.mapDerivedCategory V.mapDerivedCategory
        dr ds sx sy dh de (sfDerivedRestrictionComparison l E f n)
        (completedDerivedRestrictionDirectImageIso f d n) ?_ ?_ hcube K ?_
      · intro Z
        have hz := congrArg (fun k ↦ k ≫ dr.hom.app
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj Z)) (hsx Z)
        simpa only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_app,
          Category.comp_id, pbcDerivedRestrict, Functor.comp_obj] using hz
      · intro Z
        have hz := congrArg (fun k ↦ k ≫ ds.hom.app
          ((scalarReductionDerivedExtension.{u, u} l E Y n).obj Z)) (hsy Z)
        simpa only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_app,
          Category.comp_id, pbcDerivedRestrict, Functor.comp_obj] using hz
      · change IsIso (completedDirectImageProjectionFormula f d n
          (P.mapDerivedCategory.obj K))
        exact (completedDirectImageProjectionFormula_properties f d).1 n
          (P.mapDerivedCategory.obj K)

end ProjectionTransport

-- Preserve completeness using the existing normalized completed-coefficient comparison.

private theorem comparison_structure
    (D : CompletedCoefficientPushforward.ComparisonData.{u, u} l E f) :
    D.structureMap =
      (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (sfCompletedCoefficientMap l E f) := by
  let H := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let c : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X) := H.preimage D.structureMap
  have hc : c = sfCompletedCoefficientMap l E f := by
    apply (sfCompletedCoefficientMap_existsUnique l E f).unique
    · intro n
      apply H.map_injective
      have hx : H.map ((proEtaleSheafDirectImage f CommRingCat).map
          (completedIntegralCommRingProjectionUnrestricted l E X n)) =
          (CompletedCoefficientPushforward.ringPush.{u, u} f).map
            (CompletedCoefficientPushforward.projection l E X n) := by rfl
      have hy : H.map (completedIntegralCommRingProjectionUnrestricted l E Y n) =
          CompletedCoefficientPushforward.projection l E Y n := by rfl
      have hz : H.map (proEtaleCoefficientDirectImageMap f
          (Padic.coefficientExtensionRing l E (n + 1))) =
          CompletedCoefficientPushforward.finiteStructure.{u, u} l E f n := by rfl
      simpa only [Functor.map_comp, c, H.map_preimage, hx, hy, hz] using
        D.structureProjection n
    · exact (sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec
  calc
    D.structureMap = H.map c :=
      (H.map_preimage (X := completedIntegralCommRingSheafUnrestricted l E Y)
      (Y := (proEtaleSheafDirectImage f CommRingCat).obj
        (completedIntegralCommRingSheafUnrestricted l E X)) D.structureMap).symm
    _ = _ := congrArg H.map hc

private theorem complete_unrestricted
    (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :
    IsSfDerivedComplete l E Y K ↔ IsDerivedCompleteUnrestricted l E Y K := by
  constructor
  · intro hK
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    have : Fact p.Prime := ⟨hprime⟩
    let D : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ D.p := by change l ≠ p; omega
    exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E Y D hl K).mp hK⟩
  · rintro ⟨D, hl, hK⟩
    exact (sfDerivedComplete_iff_legacy l E Y D hl K).mpr hK

private theorem completed_image_complete
    (D : CompletedCoefficientPushforward.ComparisonData.{u, u} l E f)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K) :
    IsSfDerivedComplete l E Y ((sfCompletedDerivedDirectImage l E f).obj K) := by
  let F := CompletedCoefficientPushforward.push.{u, u} f D.structureMap
  letI := D.completedAdditive
  letI : Abelian.HasKInjectiveResolutions
      (CompletedCoefficientPushforward.Mod.{u, u} X
        (CompletedCoefficientPushforward.R l E X)) :=
    sfCompletedHasKInjectiveResolutions l E X
  letI : (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E X)).IsLocalization
      (HomologicalComplex.quasiIso (scalarReductionSource.{u, u} l E X) (.up ℤ)) :=
    inferInstance
  letI := sfCompletedModuleDirectImage_additive l E f
  let η := derivedCochainRightUnit F F.rightDerivedFunctor F.rightDerivedFunctorUnit
  letI : F.rightDerivedFunctor.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (scalarReductionSource.{u, u} l E X) (.up ℤ)) :=
    ⟨cochainRightUnit_universal F F.rightDerivedFunctor F.rightDerivedFunctorUnit⟩
  letI : D.completedImage.functor.IsRightDerivedFunctor D.completedImage.unit
      (HomologicalComplex.quasiIso (scalarReductionSource.{u, u} l E X) (.up ℤ)) :=
    D.completedImage.universal
  have hF : F = sfCompletedModuleDirectImage l E f := by
    dsimp only [F]
    rw [comparison_structure l E f D]
    rfl
  let e : D.completedImage.functor ≅ sfCompletedDerivedDirectImage l E f :=
    Functor.rightDerivedUnique D.completedImage.functor F.rightDerivedFunctor
      D.completedImage.unit η (HomologicalComplex.quasiIso
        (scalarReductionSource.{u, u} l E X) (.up ℤ)) ≪≫
      Functor.rightDerivedFunctorNatIso (eqToIso hF)
  exact complete_iso l E Y (e.app K)
    ((complete_unrestricted l E Y _).mpr
      (D.preservesComplete K ((complete_unrestricted l E X K).mp hK)))

private theorem finish_from_projection_formula
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K)
    (hc : IsSfDerivedComplete l E Y ((sfCompletedDerivedDirectImage l E f).obj K))
    [PreservesLimitsOfShape (Discrete ℕ) (sfCompletedDerivedDirectImage l E f)]
    (hβ : ∀ n : ℕ, IsIso
      (C := DerivedCategory (scalarReductionTarget.{u, u} l E Y n))
      (sf_projection_map l E f n K))
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) :
    IsSfDerivedComplete l E Y L.obj ∧
      ∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f L n) := by
  let F := sfCompletedDerivedDirectImage l E f
  let a (n : ℕ) := (sfDerivedRestrictionComparison l E f n).app
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)
  obtain ⟨hprod, δ, hδ⟩ := hK
  letI := hprod
  letI : HasProduct (fun n ↦ F.obj ((sfDerivedReductionRestricted l E X n).obj K)) :=
    hasProduct_of_equiv_of_iso (sfDirectImageTerm l E f K) _ (Equiv.refl ℕ) a
  obtain ⟨ε, hε⟩ := map_roos F
    (fun n ↦ (sfDerivedReductionTransition l E X n).app K) K
    (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app K)) δ hδ
  let p (n : ℕ) := F.map ((sfDerivedReductionUnit l E X n).app K) ≫ (a n).hom
  have hR : ∃ hp : HasProduct (sfDirectImageTerm l E f K), letI := hp
      ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f K)
        (F.obj K) (Pi.lift p) ε := by
    apply roos_transport
      (X := fun n ↦ F.obj ((sfDerivedReductionRestricted l E X n).obj K))
      (Y := sfDirectImageTerm l E f K)
      (fun n ↦ F.map ((sfDerivedReductionTransition l E X n).app K))
      (sfDirectImageTransition l E f K) (Iso.refl (F.obj K)) a
      (fun n ↦ F.map ((sfDerivedReductionUnit l E X n).app K)) p
    · intro n
      dsimp only [sfDirectImageTransition, a, Iso.app_hom, Iso.app_inv]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rfl
    · intro n
      simp only [p, Iso.refl_hom, Category.id_comp]
    · refine ⟨inferInstance, ε, ?_⟩
      simpa only [Pi.lift_comp_π] using hε
  obtain ⟨hp, ε', hε'⟩ := hR
  have hR' : ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f K)
      (F.obj K) (Pi.lift p) ε := by
    simpa only using (show ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f K)
      (F.obj K) (Pi.lift p) ε from ⟨ε', hε'⟩)
  obtain ⟨ε'', hε''⟩ := hR'
  obtain ⟨e, he⟩ := roos_unique (sfDirectImageTransition l E f K)
    L.projection (Pi.lift p) L.boundary ε'' L.roos hε''
  refine ⟨complete_iso l E Y e.symm hc, ?_⟩
  intro n
  let adj := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose
  let β := sf_projection_map l E f n K
  have : IsIso β := hβ n
  have hbunit : (adj.homEquiv (F.obj K) (sfFiniteDerivedDirectImage l E f K n)) β = p n := by
    dsimp only [β]
    rw [sf_projection_map_eq, Equiv.apply_symm_apply]
    rfl
  have h : sfDirectImageReductionComparison l E f L n =
      (scalarReductionDerivedExtension.{u, u} l E Y n).map e.hom ≫ β := by
    apply (adj.homEquiv _ _).injective
    dsimp only [sfDirectImageReductionComparison]
    rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left]
    erw [hbunit]
    have hn := congrArg (fun z ↦ z ≫ Pi.π (sfDirectImageTerm l E f K) n) he
    simpa only [Category.assoc, Pi.lift_comp_π] using hn.symm
  rw [h]
  infer_instance

end Comparison

/-- Ordinary pushforward of a complete complex is represented by the prescribed finite
image tower, and its canonical projection adjuncts identify all finite reductions.
No constructibility, finite cohomological dimension, or geometric base is needed.

Source: Stacks Project, Tags 099N(3),(4) and 0944; Bhatt--Scholze,
Lemmas 6.5.9(2) and 6.5.11(3).
(blueprint: lem-sf-complete-direct-image-reduction).

Proof: Put A = O_E, I = (uniformizer). The DVR coefficient theorem gives the free
resolution [A --uniformizer^(n+1)--> A] of A/I^(n+1), so every positive quotient is
perfect. The normalized integral coefficient presentation comparison identifies its
finite quotient sheaves, completed ring, quotient maps, scalar adjunction units and
Roos product maps with the detailed coefficient presentation used here.
Apply the completed direct-image/limit comparison to the reduction tower of K.
Restriction of scalars commutes with direct image by ringed-topos composition;
the structural maps agree after every finite projection and hence agree. Its derived
comparison is the specified sfDerivedRestrictionComparison, by its K-injective
normalization. Thus pushing the augmented Roos triangle for K gives a Roos triangle
for sfDirectImageTerm, with projections F(unit_n) followed by that comparison.
The perfect-quotient projection formula makes the adjuncts of these projections
invertible. The tower projection compatibility identifies the completion unit of F(K)
with F of the completion unit of K followed by the direct-image/limit isomorphism.
Consequently F(K) is complete. Rotate its Roos triangle and the prescribed triangle
of L; the identity on the two product terms extends to a triangle morphism.
The triangle five lemma makes the resulting L -> F(K) an isomorphism, commuting
with every projection. Completeness transports across this isomorphism. Naturality
of the scalar adjunction identifies each comparison for L with scalar extension of
this isomorphism followed by the perfect-quotient comparison for F(K). Hence it is
invertible. This proves the claims for every chosen Roos triangle, including zero
complexes and empty schemes, without choosing a functorial cone. -/
theorem sfCompleteDirectImage_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K)
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) :
    IsSfDerivedComplete l E Y L.obj ∧
      ∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f L n) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  letI : Fact p.Prime := ⟨hprime⟩
  have hlp : l ≠ p := by omega
  obtain ⟨D⟩ := CompletedCoefficientPushforward.comparison l E f p hlp
  letI := completed_derived_products l E f
  exact finish_from_projection_formula l E f K hK
    (completed_image_complete l E f D K hK) (fun n ↦ sf_projection_formula l E f n K) L

end WeilConjectures
