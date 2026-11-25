/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemBridgePushComposition

/-! Vertical pasting for the canonical proper/open transport on integral systems.

The intrinsic data and its bridge are packaged before applying categorical cancellation.
This keeps comparisons of the two derived-category presentations out of that calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 64
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
private theorem transport_vertical
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {S₁ R₁ : A ⥤ C} {S₂ R₂ : C ⥤ E} {S R : A ⥤ E}
    {T₁ P₁ : B ⥤ D} {T₂ P₂ : D ⥤ F} {T P : B ⥤ F}
    {Jk Kk : A ⥤ B} {Ji Ki : C ⥤ D} {Jj Kj : E ⥤ F}
    (bs₁ : S₁ ≅ R₁) (bs₂ : S₂ ≅ R₂) (bs : S ≅ R)
    (bt₁ : T₁ ≅ P₁) (bt₂ : T₂ ≅ P₂) (bt : T ≅ P)
    (bk : Jk ≅ Kk) (bi : Ji ≅ Ki) (bj : Jj ≅ Kj)
    (sc : S₁ ⋙ S₂ ≅ S) (tc : T₁ ⋙ T₂ ≅ T)
    (rc : R₁ ⋙ R₂ ≅ R) (pc : P₁ ⋙ P₂ ≅ P)
    (γ : S ⋙ Jj ⟶ Jk ⋙ T) (γ₁ : S₁ ⋙ Ji ⟶ Jk ⋙ T₁)
    (γ₂ : S₂ ⋙ Jj ⟶ Ji ⋙ T₂)
    (Γ : R ⋙ Kj ⟶ Kk ⋙ P) (Γ₁ : R₁ ⋙ Ki ⟶ Kk ⋙ P₁)
    (Γ₂ : R₂ ⋙ Kj ⟶ Ki ⋙ P₂) (M : A)
    (hb₁ : sc.hom.app M ≫ bs.hom.app M =
      bs₂.hom.app (S₁.obj M) ≫ R₂.map (bs₁.hom.app M) ≫ rc.hom.app M)
    (hb₂ : tc.hom.app (Jk.obj M) ≫ bt.hom.app (Jk.obj M) =
      bt₂.hom.app (T₁.obj (Jk.obj M)) ≫ P₂.map (bt₁.hom.app (Jk.obj M)) ≫
        pc.hom.app (Jk.obj M))
    (hg : γ.app M ≫ bt.hom.app (Jk.obj M) ≫ P.map (bk.hom.app M) =
      bj.hom.app (S.obj M) ≫ Kj.map (bs.hom.app M) ≫ Γ.app M)
    (hg₁ : γ₁.app M ≫ bt₁.hom.app (Jk.obj M) ≫ P₁.map (bk.hom.app M) =
      bi.hom.app (S₁.obj M) ≫ Ki.map (bs₁.hom.app M) ≫ Γ₁.app M)
    (hg₂ : γ₂.app (S₁.obj M) ≫ bt₂.hom.app (Ji.obj (S₁.obj M)) ≫
        P₂.map (bi.hom.app (S₁.obj M)) =
      bj.hom.app (S₂.obj (S₁.obj M)) ≫ Kj.map (bs₂.hom.app (S₁.obj M)) ≫
        Γ₂.app (S₁.obj M))
    (hv : Kj.map (rc.hom.app M) ≫ Γ.app M ≫ pc.inv.app (Kk.obj M) =
      Γ₂.app (R₁.obj M) ≫ P₂.map (Γ₁.app M)) :
    Jj.map (sc.hom.app M) ≫ γ.app M ≫ tc.inv.app (Jk.obj M) =
      γ₂.app (S₁.obj M) ≫ T₂.map (γ₁.app M) := by
  have hv' := congrArg (fun t ↦ t ≫ pc.hom.app (Kk.obj M)) hv
  simp only [Category.assoc, Iso.inv_hom_id_app] at hv'
  erw [Category.comp_id] at hv'
  have hb₂' := congrArg (fun t ↦ t ≫ P.map (bk.hom.app M)) hb₂
  simp only [Category.assoc] at hb₂'
  let e := tc.app (Jk.obj M) ≪≫ bt.app (Jk.obj M) ≪≫ P.mapIso (bk.app M)
  apply (cancel_mono e.hom).mp
  dsimp only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hg]
  rw [bj.hom.naturality_assoc (sc.hom.app M)]
  rw [← Functor.map_comp_assoc, hb₁, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hb₂']
  rw [← pc.hom.naturality (bk.hom.app M)]
  simp only [Functor.comp_map, Functor.comp_obj]
  erw [bt₂.hom.naturality_assoc (γ₁.app M)]
  rw [← P₂.map_comp_assoc, ← P₂.map_comp_assoc]
  simp only [Category.assoc]
  rw [hg₁]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hg₂]
  erw [← Γ₂.naturality_assoc (bs₁.hom.app M)]
  simp only [Functor.comp_map, Functor.comp_obj]
  erw [hv']

-- Store the intrinsic diagram before changing its category presentation.
private structure VerticalData
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F] where
  R₁ : A ⥤ C
  R₂ : C ⥤ E
  R : A ⥤ E
  P₁ : B ⥤ D
  P₂ : D ⥤ F
  P : B ⥤ F
  Kk : A ⥤ B
  Ki : C ⥤ D
  Kj : E ⥤ F
  rc : R₁ ⋙ R₂ ≅ R
  pc : P₁ ⋙ P₂ ≅ P
  Γ : R ⋙ Kj ⟶ Kk ⋙ P
  Γ₁ : R₁ ⋙ Ki ⟶ Kk ⋙ P₁
  Γ₂ : R₂ ⋙ Kj ⟶ Ki ⋙ P₂
  vertical (M : A) : Kj.map (rc.hom.app M) ≫ Γ.app M ≫ pc.inv.app (Kk.obj M) =
    Γ₂.app (R₁.obj M) ≫ P₂.map (Γ₁.app M)

private structure VerticalBridge
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (d : VerticalData (A := A) (B := B) (C := C) (D := D) (E := E) (F := F))
    (S₁ : A ⥤ C) (S₂ : C ⥤ E) (S : A ⥤ E)
    (T₁ : B ⥤ D) (T₂ : D ⥤ F) (T : B ⥤ F)
    (Jk : A ⥤ B) (Ji : C ⥤ D) (Jj : E ⥤ F) where
  bs₁ : S₁ ≅ d.R₁
  bs₂ : S₂ ≅ d.R₂
  bs : S ≅ d.R
  bt₁ : T₁ ≅ d.P₁
  bt₂ : T₂ ≅ d.P₂
  bt : T ≅ d.P
  bk : Jk ≅ d.Kk
  bi : Ji ≅ d.Ki
  bj : Jj ≅ d.Kj

private theorem transport_vertical_data
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {S₁ : A ⥤ C} {S₂ : C ⥤ E} {S : A ⥤ E}
    {T₁ : B ⥤ D} {T₂ : D ⥤ F} {T : B ⥤ F}
    {Jk : A ⥤ B} {Ji : C ⥤ D} {Jj : E ⥤ F}
    (d : VerticalData (A := A) (B := B) (C := C) (D := D) (E := E) (F := F))
    (v : VerticalBridge d S₁ S₂ S T₁ T₂ T Jk Ji Jj)
    (sc : S₁ ⋙ S₂ ≅ S) (tc : T₁ ⋙ T₂ ≅ T)
    (γ : S ⋙ Jj ⟶ Jk ⋙ T) (γ₁ : S₁ ⋙ Ji ⟶ Jk ⋙ T₁)
    (γ₂ : S₂ ⋙ Jj ⟶ Ji ⋙ T₂) (M : A)
    (hb₁ : sc.hom.app M ≫ v.bs.hom.app M =
      v.bs₂.hom.app (S₁.obj M) ≫ d.R₂.map (v.bs₁.hom.app M) ≫ d.rc.hom.app M)
    (hb₂ : tc.hom.app (Jk.obj M) ≫ v.bt.hom.app (Jk.obj M) =
      v.bt₂.hom.app (T₁.obj (Jk.obj M)) ≫ d.P₂.map (v.bt₁.hom.app (Jk.obj M)) ≫
        d.pc.hom.app (Jk.obj M))
    (hg : γ.app M ≫ v.bt.hom.app (Jk.obj M) ≫ d.P.map (v.bk.hom.app M) =
      v.bj.hom.app (S.obj M) ≫ d.Kj.map (v.bs.hom.app M) ≫ d.Γ.app M)
    (hg₁ : γ₁.app M ≫ v.bt₁.hom.app (Jk.obj M) ≫ d.P₁.map (v.bk.hom.app M) =
      v.bi.hom.app (S₁.obj M) ≫ d.Ki.map (v.bs₁.hom.app M) ≫ d.Γ₁.app M)
    (hg₂ : γ₂.app (S₁.obj M) ≫ v.bt₂.hom.app (Ji.obj (S₁.obj M)) ≫
        d.P₂.map (v.bi.hom.app (S₁.obj M)) =
      v.bj.hom.app (S₂.obj (S₁.obj M)) ≫ d.Kj.map (v.bs₂.hom.app (S₁.obj M)) ≫
        d.Γ₂.app (S₁.obj M)) :
    Jj.map (sc.hom.app M) ≫ γ.app M ≫ tc.inv.app (Jk.obj M) =
      γ₂.app (S₁.obj M) ≫ T₂.map (γ₁.app M) := by
  exact transport_vertical v.bs₁ v.bs₂ v.bs v.bt₁ v.bt₂ v.bt v.bk v.bi v.bj
    sc tc d.rc d.pc γ γ₁ γ₂ d.Γ d.Γ₁ d.Γ₂ M hb₁ hb₂ hg hg₁ hg₂ (d.vertical M)

-- Elimination of a constructed witness keeps its functors abstract in the final proof.
private structure VerticalWitness
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {S₁ : A ⥤ C} {S₂ : C ⥤ E} {S : A ⥤ E}
    {T₁ : B ⥤ D} {T₂ : D ⥤ F} {T : B ⥤ F}
    {Jk : A ⥤ B} {Ji : C ⥤ D} {Jj : E ⥤ F}
    (sc : S₁ ⋙ S₂ ≅ S) (tc : T₁ ⋙ T₂ ≅ T)
    (γ : S ⋙ Jj ⟶ Jk ⋙ T) (γ₁ : S₁ ⋙ Ji ⟶ Jk ⋙ T₁)
    (γ₂ : S₂ ⋙ Jj ⟶ Ji ⋙ T₂) (M : A) where
  d : VerticalData (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
  v : VerticalBridge d S₁ S₂ S T₁ T₂ T Jk Ji Jj
  hb₁ : sc.hom.app M ≫ v.bs.hom.app M =
    v.bs₂.hom.app (S₁.obj M) ≫ d.R₂.map (v.bs₁.hom.app M) ≫ d.rc.hom.app M
  hb₂ : tc.hom.app (Jk.obj M) ≫ v.bt.hom.app (Jk.obj M) =
    v.bt₂.hom.app (T₁.obj (Jk.obj M)) ≫ d.P₂.map (v.bt₁.hom.app (Jk.obj M)) ≫
      d.pc.hom.app (Jk.obj M)
  hg : γ.app M ≫ v.bt.hom.app (Jk.obj M) ≫ d.P.map (v.bk.hom.app M) =
    v.bj.hom.app (S.obj M) ≫ d.Kj.map (v.bs.hom.app M) ≫ d.Γ.app M
  hg₁ : γ₁.app M ≫ v.bt₁.hom.app (Jk.obj M) ≫ d.P₁.map (v.bk.hom.app M) =
    v.bi.hom.app (S₁.obj M) ≫ d.Ki.map (v.bs₁.hom.app M) ≫ d.Γ₁.app M
  hg₂ : γ₂.app (S₁.obj M) ≫ v.bt₂.hom.app (Ji.obj (S₁.obj M)) ≫
      d.P₂.map (v.bi.hom.app (S₁.obj M)) =
    v.bj.hom.app (S₂.obj (S₁.obj M)) ≫ d.Kj.map (v.bs₂.hom.app (S₁.obj M)) ≫
      d.Γ₂.app (S₁.obj M)

private def nativeVerticalData (C₀ : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, C₀ (n + 1) ⟶ C₀ n) {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    VerticalData
      (A := ProEtale.SemilinearProperOpen.Derived C₀ τ A)
      (B := ProEtale.SemilinearProperOpen.Derived C₀ τ B₀)
      (C := ProEtale.SemilinearProperOpen.Derived C₀ τ C)
      (D := ProEtale.SemilinearProperOpen.Derived C₀ τ D)
      (E := ProEtale.SemilinearProperOpen.Derived C₀ τ E₀)
      (F := ProEtale.SemilinearProperOpen.Derived C₀ τ F) where
  R₁ := ProEtale.SemilinearProperOpen.R C₀ τ r₁
  R₂ := ProEtale.SemilinearProperOpen.R C₀ τ r₂
  R := ProEtale.SemilinearProperOpen.R C₀ τ (r₁ ≫ r₂)
  P₁ := ProEtale.SemilinearProperOpen.R C₀ τ p₁
  P₂ := ProEtale.SemilinearProperOpen.R C₀ τ p₂
  P := ProEtale.SemilinearProperOpen.R C₀ τ (p₁ ≫ p₂)
  Kk := ProEtale.SemilinearProperOpen.J C₀ τ k
  Ki := ProEtale.SemilinearProperOpen.J C₀ τ i
  Kj := ProEtale.SemilinearProperOpen.J C₀ τ j
  rc := ProEtale.SemilinearProperOpen.sComp C₀ τ r₁ r₂
  pc := ProEtale.SemilinearProperOpen.sComp C₀ τ p₁ p₂
  Γ := ProEtale.SemilinearProperOpen.gamma C₀ τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h
  Γ₁ := ProEtale.SemilinearProperOpen.gamma C₀ τ k r₁ p₁ i h₁
  Γ₂ := ProEtale.SemilinearProperOpen.gamma C₀ τ i r₂ p₂ j h₂
  vertical := (ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting C₀ τ).1
    k i j r₁ r₂ p₁ p₂ h₁ h₂ h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] CanonicalBridge.push CanonicalBridge.shriek Compositors.pushComp
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.rightDerivedFunctor constantSheaf
  HasDerivedCategory.standard DerivedCategory.Q Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryFactors
  ProEtale.SemilinearProperOpen.R ProEtale.SemilinearProperOpen.J
  ProEtale.SemilinearProperOpen.sComp ProEtale.SemilinearProperOpen.gamma

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheaf integralCoefficientSheafTransition
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  sheafCompose ProEtale.SemilinearProperOpen.derived RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CommRingCat.hasForgetToRingCat

private def chosenVerticalData {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    VerticalData (A := System l E A) (B := System l E B₀)
      (C := System l E C) (D := System l E D) (E := System l E E₀) (F := System l E F) :=
  nativeVerticalData (scalarRings l E) (scalarTransitions l E) k i j r₁ r₂ p₁ p₂ h₁ h₂ h

private def chosenVerticalBridge (o : Operations l E) (b : CanonicalBridge l E o)
    {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    VerticalBridge (chosenVerticalData l E k i j r₁ r₂ p₁ p₂ h₁ h₂ h)
      (Operations.push l E o r₁) (Operations.push l E o r₂)
      (Operations.push l E o (r₁ ≫ r₂))
      (Operations.push l E o p₁) (Operations.push l E o p₂)
      (Operations.push l E o (p₁ ≫ p₂))
      (Operations.shriek l E o k) (Operations.shriek l E o i)
      (Operations.shriek l E o j) where
  bs₁ := b.push l E r₁
  bs₂ := b.push l E r₂
  bs := b.push l E (r₁ ≫ r₂)
  bt₁ := b.push l E p₁
  bt₂ := b.push l E p₂
  bt := b.push l E (p₁ ≫ p₂)
  bk := b.shriek l E k
  bi := b.shriek l E i
  bj := b.shriek l E j

section
attribute [local irreducible] chosenVerticalBridge chosenVerticalData

private theorem chosen_compositors (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o)
    {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : System l E A) :
    let d := chosenVerticalData l E k i j r₁ r₂ p₁ p₂ h₁ h₂ h
    let v := chosenVerticalBridge l E o b k i j r₁ r₂ p₁ p₂ h₁ h₂ h
    ((c.pushComp l E r₁ r₂).hom.app M ≫ v.bs.hom.app M =
      v.bs₂.hom.app ((Operations.push l E o r₁).obj M) ≫
        d.R₂.map (v.bs₁.hom.app M) ≫ d.rc.hom.app M) ∧
    ((c.pushComp l E p₁ p₂).hom.app ((Operations.shriek l E o k).obj M) ≫
        v.bt.hom.app ((Operations.shriek l E o k).obj M) =
      v.bt₂.hom.app ((Operations.push l E o p₁).obj
        ((Operations.shriek l E o k).obj M)) ≫
        d.P₂.map (v.bt₁.hom.app ((Operations.shriek l E o k).obj M)) ≫
        d.pc.hom.app ((Operations.shriek l E o k).obj M)) := by
  dsimp only
  delta chosenVerticalBridge chosenVerticalData nativeVerticalData
  exact ⟨integralSystemBridgePushComposition l E o c b r₁ r₂ M,
    integralSystemBridgePushComposition l E o c b p₁ p₂
      ((Operations.shriek l E o k).obj M)⟩

private theorem chosen_canonical (o : Operations l E)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (canonical : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M)
    {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : System l E A) :
    let d := chosenVerticalData l E k i j r₁ r₂ p₁ p₂ h₁ h₂ h
    let v := chosenVerticalBridge l E o b k i j r₁ r₂ p₁ p₂ h₁ h₂ h
    ((gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        v.bt.hom.app ((Operations.shriek l E o k).obj M) ≫
        d.P.map (v.bk.hom.app M) =
      v.bj.hom.app ((Operations.push l E o (r₁ ≫ r₂)).obj M) ≫
        d.Kj.map (v.bs.hom.app M) ≫ d.Γ.app M) ∧
    ((gamma k r₁ p₁ i h₁).app M ≫
        v.bt₁.hom.app ((Operations.shriek l E o k).obj M) ≫
        d.P₁.map (v.bk.hom.app M) =
      v.bi.hom.app ((Operations.push l E o r₁).obj M) ≫
        d.Ki.map (v.bs₁.hom.app M) ≫ d.Γ₁.app M) ∧
    ((gamma i r₂ p₂ j h₂).app ((Operations.push l E o r₁).obj M) ≫
        v.bt₂.hom.app ((Operations.shriek l E o i).obj
          ((Operations.push l E o r₁).obj M)) ≫
        d.P₂.map (v.bi.hom.app ((Operations.push l E o r₁).obj M)) =
      v.bj.hom.app ((Operations.push l E o r₂).obj
        ((Operations.push l E o r₁).obj M)) ≫
        d.Kj.map (v.bs₂.hom.app ((Operations.push l E o r₁).obj M)) ≫
        d.Γ₂.app ((Operations.push l E o r₁).obj M)) := by
  dsimp only
  delta chosenVerticalBridge chosenVerticalData nativeVerticalData
  exact ⟨canonical k (r₁ ≫ r₂) (p₁ ≫ p₂) j h M,
    canonical k r₁ p₁ i h₁ M,
    canonical i r₂ p₂ j h₂ ((Operations.push l E o r₁).obj M)⟩

/-- Vertical proper/open transport pasting for the canonically normalized gamma.
The bridge equation identifies each supplied component with the intrinsic mate.
Source: Stacks 0F7C, 0F7D and 0F7F; Zheng Lemma 4.10.
(blueprint: lem-sf-integral-system-proper-open-transport-pasting-vertical).
Proof: the section-normalized bridge intertwines both direct-image compositors.
Apply the three canonical component equations. Naturality moves the bridge maps
through the functors, and cancellation of the endpoint isomorphism reduces the claim
to intrinsic vertical mate pasting. -/
theorem integralSystemProperOpenTransportPastingVertical
    (o : Operations l E) (c : Compositors l E o)
    (_a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (canonical : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M) :
  ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : System l E A),
      (Operations.shriek l E o j).map ((c.pushComp l E r₁ r₂).hom.app M) ≫
          (gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (c.pushComp l E p₁ p₂).inv.app ((Operations.shriek l E o k).obj M) =
        (gamma i r₂ p₂ j h₂).app ((Operations.push l E o r₁).obj M) ≫
          (Operations.push l E o p₂).map ((gamma k r₁ p₁ i h₁).app M) := by
  intro A C E₀ B₀ D F k i j r₁ r₂ p₁ p₂ hk hi hj qk qi qj hr₁ hr₂ hp₁ hp₂ h₁ h₂ h M
  let d := chosenVerticalData l E k i j r₁ r₂ p₁ p₂ h₁ h₂ h
  let v := chosenVerticalBridge l E o b k i j r₁ r₂ p₁ p₂ h₁ h₂ h
  have hc := chosen_compositors l E o c b k i j r₁ r₂ p₁ p₂ h₁ h₂ h M
  have hg := chosen_canonical l E o gamma b canonical k i j r₁ r₂ p₁ p₂ h₁ h₂ h M
  have hw : Nonempty (VerticalWitness
      (c.pushComp l E r₁ r₂) (c.pushComp l E p₁ p₂)
      (gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h) (gamma k r₁ p₁ i h₁) (gamma i r₂ p₂ j h₂) M) :=
    ⟨{ d := d, v := v, hb₁ := hc.1, hb₂ := hc.2,
       hg := hg.1, hg₁ := hg.2.1, hg₂ := hg.2.2 }⟩
  obtain ⟨w⟩ := hw
  exact transport_vertical_data w.d w.v
    (c.pushComp l E r₁ r₂) (c.pushComp l E p₁ p₂)
    (gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h) (gamma k r₁ p₁ i h₁) (gamma i r₂ p₂ j h₂)
    M w.hb₁ w.hb₂ w.hg w.hg₁ w.hg₂

end
end WeilConjectures.IntegralSystemRealization
