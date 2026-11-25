/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import WeilConjectures.CategoryTheory.SmoothPurity.TowerLimitAcyclicOfEquivalences
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitAcyclic
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Acyclicity input for completed tower pushforward

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0D6E.
(blueprint: lem-pur-completed-coefficient-tower-limit-acyclic-aux).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
private instance smallTowerPushZero
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : D ⥤ C} [F.IsContinuous K J]
    {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
    (c : B ⟶ (F.sheafPushforwardContinuous RingCat.{u} K J).obj A) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (SheafOfModules.pushforward.{u} c)).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext n
  rfl

private theorem smallPushforwardLimitAcyclic
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] [RepresentablyFlat F]
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (c : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} K J).obj A)
    (I : CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) ℤ) (hI : I.IsKInjective)
    (T : CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) ℤ) (hT : T.IsKInjective)
    (j : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (SheafOfModules.pushforward.{u} (F := F) (J := K) (K := J)
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
        (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj B)
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map c))).mapHomologicalComplex
        (.up ℤ)).obj I) ⟶ T)
    [QuasiIso j] :
    QuasiIso (((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) ⥤ _).mapHomologicalComplex
        (.up ℤ)).map j) := by
  let : HasSheafify J (Type u) := hasSheafifyEssentiallySmallSite J (Type u)
  let : HasSheafify K (Type u) := hasSheafifyEssentiallySmallSite K (Type u)
  have : PreservesFiniteLimits (F.sheafPullback (Type u) K J) := by
    apply Functor.sheafPullbackConstruction.preservesFiniteLimits
  obtain ⟨f, hf⟩ := continuousRingedToposModuleDirectImage_exists F
    (F.sheafPullback (Type u) K J) (F.sheafAdjunctionContinuous (Type u) K J) A B c
  let e := (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (eqToIso hf)
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  let j₀ := ec.hom.app I ≫ j
  have : QuasiIso j₀ := by
    dsimp only [j₀]
    infer_instance
  have h := ringedTowerPushforwardLimitAcyclic _ _
    (fun U a b ↦ @mul_comm (A.obj.obj U) _ a b)
    (fun U a b ↦ @mul_comm (B.obj.obj U) _ a b) f I hI T hT j₀
  dsimp only [j₀] at h
  rw [Functor.map_comp] at h
  exact (quasiIso_iff_comp_left _ _).mp h

private abbrev smallSiteEquiv (X : Scheme.{t}) :
    X.ProEt ≌ AsSmall.{max u (t + 1)} X.ProEt := AsSmall.equiv

private abbrev smallTopology (X : Scheme.{t}) :=
  (smallSiteEquiv.{t, u} X).inverse.inducedTopology (ProEt.topology X)

private abbrev smallRing (X : Scheme.{t})
    (A : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}) :=
  ((smallSiteEquiv.{t, u} X).sheafCongr (ProEt.topology X)
    (smallTopology.{t, u} X) RingCat.{max u (t + 1)}).functor.obj A

private def smallModulesModel (X : Scheme.{t})
    (A : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}) :
    SheafOfModules.{max u (t + 1)} A ≌ SheafOfModules.{max u (t + 1)} (smallRing X A) := by
  let e := smallSiteEquiv.{t, u} X
  let K := smallTopology.{t, u} X
  let φ : smallRing X A ⟶
      (e.inverse.sheafPushforwardContinuous RingCat.{max u (t + 1)} K
        (ProEt.topology X)).obj A := 𝟙 _
  let ψ : A ⟶ (e.functor.sheafPushforwardContinuous RingCat.{max u (t + 1)}
      (ProEt.topology X) K).obj (smallRing X A) := 𝟙 _
  have : e.symm.functor.IsContinuous K (ProEt.topology X) :=
    inferInstanceAs (e.inverse.IsContinuous K (ProEt.topology X))
  have : e.symm.inverse.IsContinuous (ProEt.topology X) K :=
    inferInstanceAs (e.functor.IsContinuous (ProEt.topology X) K)
  exact SheafOfModules.pushforwardPushforwardEquivalence e.symm φ ψ (by
    ext U x
    change (A.obj.map (𝟙 U)) x = x
    simp) (by
    ext U x
    change (A.obj.map (𝟙 (e.inverse.op.obj U))) x = x
    simp)

private abbrev smallBaseChange {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (smallSiteEquiv.{t, u} Y).inverse ⋙ proEtaleBaseChange f ⋙
    (smallSiteEquiv.{t, u} X).functor

private instance smallBaseChangeContinuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (smallBaseChange.{t, u} f).IsContinuous (smallTopology.{t, u} Y)
      (smallTopology.{t, u} X) := by
  have := Functor.isContinuous_comp (proEtaleBaseChange f)
    (smallSiteEquiv.{t, u} X).functor (ProEt.topology Y) (ProEt.topology X)
      (smallTopology.{t, u} X)
  exact Functor.isContinuous_comp (smallSiteEquiv.{t, u} Y).inverse
    (proEtaleBaseChange f ⋙ (smallSiteEquiv.{t, u} X).functor)
      (smallTopology.{t, u} Y) (ProEt.topology Y) (smallTopology.{t, u} X)

private abbrev smallStructuralMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {B : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (c : B ⟶ (ringPush.{t, u} f).obj A) :
    smallRing Y B ⟶ ((smallBaseChange.{t, u} f).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (smallTopology.{t, u} Y)
        (smallTopology.{t, u} X)).obj (smallRing X A) :=
  ⟨Functor.whiskerLeft (smallSiteEquiv.{t, u} Y).inverse.op c.hom⟩

private def smallModulesPushforwardComparison {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {B : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (c : B ⟶ (ringPush.{t, u} f).obj A) :
    push f c ⋙ (smallModulesModel Y B).functor ≅
      (smallModulesModel X A).functor ⋙ SheafOfModules.pushforward (smallStructuralMap f c) := by
  dsimp only [smallModulesModel, SheafOfModules.pushforwardPushforwardEquivalence]
  exact Iso.refl _

attribute [local irreducible] smallModulesModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance completedPushAdditiveAux {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)) : (push f c).Additive where
  map_add := by intros; rfl

instance completedPushTowerZeroAux {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).PreservesZeroMorphisms := by
  constructor
  intro A B
  ext n
  rfl

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private instance pushAdditiveForTransport {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {B : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (c : B ⟶ (ringPush.{t, u} f).obj A) : (push f c).Additive where
  map_add := by intros; rfl

private instance pushTowerZeroForTransport {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {B : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (c : B ⟶ (ringPush.{t, u} f).obj A) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext n
  rfl

private theorem towerLimit_push_acyclic_comm {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A₀ : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})
    (B₀ : Sheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (c : (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B₀ ⟶
      (ringPush.{t, u} f).obj
        ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A₀))
    (I : CochainComplex (ℕᵒᵖ ⥤ Mod X
      ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A₀)) ℤ)
    (hI : I.IsKInjective)
    (T : CochainComplex (ℕᵒᵖ ⥤ Mod Y
      ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B₀)) ℤ)
    (hT : T.IsKInjective)
    (j : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).mapHomologicalComplex
      (.up ℤ)).obj I) ⟶ T) [QuasiIso j] :
    QuasiIso (((lim :
      (ℕᵒᵖ ⥤ Mod Y ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B₀)) ⥤
          _).mapHomologicalComplex (.up ℤ)).map j) := by
  let eX := smallSiteEquiv.{t, u} X
  let eY := smallSiteEquiv.{t, u} Y
  let J := smallTopology.{t, u} X
  let K := smallTopology.{t, u} Y
  let F := smallBaseChange.{t, u} f
  have : PreservesFiniteLimits F := by
    dsimp only [F, smallBaseChange]
    infer_instance
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let AX := (eX.sheafCongr (ProEt.topology X) J CommRingCat.{max u (t + 1)}).functor.obj
    A₀
  let AY := (eY.sheafCongr (ProEt.topology Y) K CommRingCat.{max u (t + 1)}).functor.obj
    B₀
  let V := sheafCompose K (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let cs : V.obj AY ⟶ (F.sheafPushforwardContinuous RingCat.{max u (t + 1)} K J).obj
      ((sheafCompose J (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj AX) :=
    smallStructuralMap f c
  let cs' : AY ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u (t + 1)} K J).obj AX :=
    V.preimage (X := AY)
      (Y := (F.sheafPushforwardContinuous CommRingCat.{max u (t + 1)} K J).obj AX) cs
  have hcs : V.map cs' = cs := by
    dsimp only [cs']
    exact Functor.map_preimage V (X := AY)
      (Y := (F.sheafPushforwardContinuous CommRingCat.{max u (t + 1)} K J).obj AX) cs
  let EX := smallModulesModel X
    ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A₀)
  let EY := smallModulesModel Y
    ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B₀)
  have : (SheafOfModules.pushforward.{max u (t + 1)} cs).Additive := ⟨by intros; rfl⟩
  have : (lim : (ℕᵒᵖ ⥤ Mod Y
      ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B₀)) ⥤ _).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ SheafOfModules.{max u (t + 1)} (V.obj AY)) ⥤ _).Additive :=
    Functor.additive_of_preserves_binary_products _
  apply towerLimitAcyclicOfEquivalences EX EY (push f c)
    (SheafOfModules.pushforward.{max u (t + 1)} cs) (smallModulesPushforwardComparison f c)
    ?_ I hI T hT j
  intro I₁ hI₁ T₁ hT₁ j₁ hj₁
  have := hj₁
  have h := smallPushforwardLimitAcyclic F AX AY cs'
  -- The map on commutative rings forgets to the original structural map.
  have he : SheafOfModules.pushforward.{max u (t + 1)} (V.map cs') ≅
      SheafOfModules.pushforward.{max u (t + 1)} cs := SheafOfModules.pushforwardCongr hcs
  let et := (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso he
  let etc := NatIso.mapHomologicalComplex et (.up ℤ)
  let j₀ := etc.hom.app I₁ ≫ j₁
  have : QuasiIso j₀ := by dsimp only [j₀]; infer_instance
  have h₀ := h I₁ hI₁ T₁ hT₁ j₀
  dsimp only [j₀] at h₀
  rw [Functor.map_comp] at h₀
  exact (quasiIso_iff_comp_left _ _).mp h₀

/--
The inverse-limit functor sends a quasi-isomorphism between a levelwise pushforward
of a K-injective completed tower and a K-injective target tower to a
quasi-isomorphism.  This is the acyclicity input used in the normalized derived
limit argument; it is proved by the K-flat pullback and tower-localization
argument of Stacks Tags 0A07 and 0D6E.
(blueprint: lem-pur-completed-coefficient-tower-limit-acyclic-aux)
-/
theorem towerLimit_push_acyclic_aux {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (I : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ) (hI : I.IsKInjective)
    (T : CochainComplex (ℕᵒᵖ ⥤ Mod Y (R l E Y)) ℤ) (hT : T.IsKInjective)
    (j : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).mapHomologicalComplex
      (.up ℤ)).obj I) ⟶ T) [QuasiIso j] :
    QuasiIso (((lim : (ℕᵒᵖ ⥤ Mod Y (R l E Y)) ⥤ Mod Y (R l E Y)).mapHomologicalComplex
      (.up ℤ)).map j) := by
  exact towerLimit_push_acyclic_comm f
    (completedIntegralCommRingSheafUnrestricted l E X)
    (completedIntegralCommRingSheafUnrestricted l E Y) c I hI T hT j

end WeilConjectures.CompletedCoefficientPushforward
