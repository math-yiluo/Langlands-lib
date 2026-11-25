/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteRealizationEtaleOrigin
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteSupportCandidateComposition

/-! # Binary normalization in the canonical origin category -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 2048
set_option cleanup.letToHave false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The existing coefficient realization restricted to bounded constructible objects.
Source: finite-ring constructible derived origin, applied to the fixed realization
(blueprint: lem-sf-finite-support-origin-binary-normalization). -/
def originInclusion (X : SixFunctorSpace D) :
    sixFunctorFiniteCategory D C E n hn X ⥤
      (DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        X.obj.left).FullSubcategory :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (DerivedCategory.plusEtaleOrigin
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    X.obj.left).lift
      ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse)
      (fun K ↦ finiteRealization_etaleOrigin X K)

/-- Conjugate a functor comparison through the inverse coefficient equivalences.
Source: equivalence unit and counit cancellation
(blueprint: lem-sf-finite-support-origin-binary-normalization). -/
def inverseConjugation {A B C₀ D₀ : Type*}
    [Category A] [Category B] [Category C₀] [Category D₀]
    (R : A ≌ B) (R' : C₀ ≌ D₀) (F : B ⥤ D₀) (G : A ⥤ C₀)
    (e : R.functor ⋙ F ≅ G ⋙ R'.functor) : F ⋙ R'.inverse ≅ R.inverse ⋙ G :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight R.counitIso.symm F) R'.inverse ≪≫
    Functor.isoWhiskerLeft R.inverse (Functor.isoWhiskerRight e R'.inverse) ≪≫
    Functor.isoWhiskerLeft (R.inverse ⋙ G) R'.unitIso.symm ≪≫
    Functor.rightUnitor _

private theorem inverseConjugation_app
    {A B C₀ D₀ : Type*} [Category A] [Category B] [Category C₀] [Category D₀]
    (R : A ≌ B) (R' : C₀ ≌ D₀) (F : B ⥤ D₀) (G : A ⥤ C₀)
    (e : R.functor ⋙ F ≅ G ⋙ R'.functor) (M : A) (K : B)
    (w : R.functor.obj M ≅ K) :
    (inverseConjugation R R' F G e).hom.app K =
      R'.inverse.map (F.map w.inv ≫ e.hom.app M) ≫
        R'.unitIso.inv.app (G.obj M) ≫
          G.map (R.unitIso.hom.app M ≫ R.inverse.map w.hom) := by
  let t := R.unitIso.hom.app M ≫ R.inverse.map w.hom
  have he := e.hom.naturality t
  dsimp only [Functor.comp_map] at he
  have hn := R'.unitIso.inv.naturality (G.map t)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have ht : w.inv ≫ R.functor.map t = R.counitIso.inv.app K := by
    dsimp [t]
    simp only [Functor.map_comp, ← R.counitInv_app_functor]
    have hw := R.counitIso.inv.naturality w.hom
    dsimp only [Functor.id_map, Functor.comp_map] at hw
    change w.inv ≫ R.counitIso.inv.app _ ≫ _ = _
    rw [← hw]
    simp
  simp only [inverseConjugation, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
    Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at he hn ⊢
  simp only [Category.comp_id]
  change _ = R'.inverse.map (F.map w.inv ≫ e.hom.app M) ≫
    R'.unitIso.inv.app (G.obj M) ≫ G.map t
  have hinner : F.map (R.counitIso.inv.app K) ≫ e.hom.app (R.inverse.obj K) =
      (F.map w.inv ≫ e.hom.app M) ≫ R'.functor.map (G.map t) := by
    rw [Category.assoc, ← he, ← Category.assoc, ← F.map_comp, ht]
  rw [← hn]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ R'.inverse.map z ≫ R'.unitIso.inv.app (G.obj (R.inverse.obj K)))
      hinner

private theorem transport_normalization
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (R₀ : A₀ ≌ B₀) (R₁ : A₁ ≌ B₁) (R₂ : A₂ ≌ B₂)
    (P : B₀ ⥤ B₁) (P' : B₁ ⥤ B₂) (P'' : B₀ ⥤ B₂)
    (Q : A₀ ⥤ A₁) (Q' : A₁ ⥤ A₂) (Q'' : A₀ ⥤ A₂)
    (e : R₀.functor ⋙ P ≅ Q ⋙ R₁.functor)
    (e' : R₁.functor ⋙ P' ≅ Q' ⋙ R₂.functor)
    (e'' : R₀.functor ⋙ P'' ≅ Q'' ⋙ R₂.functor)
    (k₀ : B₀) (k₁ : B₁) (k₂ kh : B₂)
    (ρ : k₁ ≅ P.obj k₀) (σ : k₂ ≅ P'.obj k₁) (τ : kh ≅ P''.obj k₀)
    (M : A₀) (w : R₀.functor.obj M ≅ k₀) (α : k₂ ⟶ kh)
    (a : Q'.obj (Q.obj M) ⟶ Q''.obj M)
    (b : Q'.obj (Q.obj (R₀.inverse.obj k₀)) ⟶ Q''.obj (R₀.inverse.obj k₀))
    (hnat : Q'.map (Q.map (R₀.unitIso.hom.app M ≫ R₀.inverse.map w.hom)) ≫ b =
      a ≫ Q''.map (R₀.unitIso.hom.app M ≫ R₀.inverse.map w.hom))
    (hnorm : α ≫ (τ ≪≫ P''.mapIso w.symm ≪≫ e''.app M).hom =
      (σ ≪≫ P'.mapIso (ρ ≪≫ P.mapIso w.symm ≪≫ e.app M) ≪≫
        e'.app (Q.obj M)).hom ≫ R₂.functor.map a) :
    R₂.inverse.map α ≫ R₂.inverse.map τ.hom ≫
        (inverseConjugation R₀ R₂ P'' Q'' e'').hom.app k₀ =
      (R₂.inverse.map σ.hom ≫ (inverseConjugation R₁ R₂ P' Q' e').hom.app k₁) ≫
        Q'.map (R₁.inverse.map ρ.hom ≫
          (inverseConjugation R₀ R₁ P Q e).hom.app k₀) ≫ b := by
  let t : M ≅ R₀.inverse.obj k₀ := R₀.unitIso.app M ≪≫ R₀.inverse.mapIso w
  let wf : k₁ ≅ R₁.functor.obj (Q.obj M) := ρ ≪≫ P.mapIso w.symm ≪≫ e.app M
  let wh : kh ≅ R₂.functor.obj (Q''.obj M) := τ ≪≫ P''.mapIso w.symm ≪≫ e''.app M
  let wgf : k₂ ≅ R₂.functor.obj (Q'.obj (Q.obj M)) := σ ≪≫ P'.mapIso wf ≪≫ e'.app (Q.obj M)
  let v : R₁.inverse.obj k₁ ≅ Q.obj M := R₁.inverse.mapIso wf ≪≫ (R₁.unitIso.app (Q.obj M)).symm
  have hf : R₁.inverse.map ρ.hom ≫
      (inverseConjugation R₀ R₁ P Q e).hom.app k₀ = v.hom ≫ Q.map t.hom := by
    rw [inverseConjugation_app R₀ R₁ P Q e M k₀ w]
    simp only [v, wf, t, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  have hh : R₂.inverse.map τ.hom ≫
      (inverseConjugation R₀ R₂ P'' Q'' e'').hom.app k₀ =
        R₂.inverse.map wh.hom ≫ R₂.unitIso.inv.app (Q''.obj M) ≫ Q''.map t.hom := by
    rw [inverseConjugation_app R₀ R₂ P'' Q'' e'' M k₀ w]
    simp only [wh, t, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hg : R₂.inverse.map σ.hom ≫
      (inverseConjugation R₁ R₂ P' Q' e').hom.app k₁ =
        R₂.inverse.map wgf.hom ≫ R₂.unitIso.inv.app (Q'.obj (Q.obj M)) ≫
          Q'.map v.inv := by
    rw [inverseConjugation_app R₁ R₂ P' Q' e' (Q.obj M) k₁ wf.symm]
    simp only [wgf, v, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc]
  rw [hh, hg, hf]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Q'.map_comp_assoc, v.inv_hom_id, Q'.map_id, Category.id_comp]
  rw [← R₂.inverse.map_comp_assoc, hnorm, R₂.inverse.map_comp]
  have hu := R₂.unitIso.inv.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  simp only [Category.assoc]
  rw [reassoc_of% hu]
  change _ = R₂.inverse.map wgf.hom ≫ _
  change Q'.map (Q.map t.hom) ≫ b = a ≫ Q''.map t.hom at hnat
  change R₂.inverse.map wgf.hom ≫ R₂.unitIso.inv.app (Q'.obj (Q.obj M)) ≫
    a ≫ Q''.map t.hom = _
  exact congrArg (fun z ↦ R₂.inverse.map wgf.hom ≫
    R₂.unitIso.inv.app (Q'.obj (Q.obj M)) ≫ z) hnat.symm

/-- Comparison with the canonical origin support, built from the given realization
and the canonical change of compactification. No new comparison is chosen.
Source: the prescribed finite support realization and canonical candidate comparison
(blueprint: lem-sf-finite-support-origin-binary-normalization). -/
def originSupportComparison (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [QuasiCompact f.hom.left] (c : Compactification f.hom.left) :
    letI := c.hasCompactification
    S.finite.support f c ⋙ originInclusion (C := C) (E := E) (n := n) (hn := hn) Y ≅
      originInclusion (C := C) (E := E) (n := n) (hn := hn) X ⋙
        originCompactSupport
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) f.hom.left := by
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  letI := c.hasCompactification
  let A := Padic.coefficientExtensionRing C.l E n
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A))
    Y.obj.left).fullyFaithfulι
  apply (H.whiskeringRight _).preimageIso
  exact Functor.isoWhiskerRight (S.finiteSupport f c) RY.inverse ≪≫
    Functor.isoWhiskerLeft
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
      (inverseConjugation RX RY (sixFunctorFiniteSupport D C E n hn f c)
        (sfFixedCompactSupport A c) (sfIntrinsicCompactSupportComparison A c)) ≪≫
    Functor.isoWhiskerLeft (originInclusion (C := C) (E := E) (n := n) (hn := hn) X)
      (towerCandidateComparison (ULift.{u + 1} A) c
        (HasCompactification.compactification f.hom.left))

attribute [local implicit_reducible] realization sixFunctorFiniteRealization sixFunctorFiniteSupport
  sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate originInclusion
  rightDerivedLowerShriek originCompactSupport comparisonUpperStarPlusEtaleOrigin
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  sfIntrinsicDerivedEquivalence
  sfIntrinsicCompactSupportComparison inverseConjugation towerCandidateComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private abbrev candidateSupport (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1} A)) c

private def fixedSupportComparison (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    S.finite.support f c ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ⋙
      (realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse ≅
    (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
      (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse ⋙
      candidateSupport (Padic.coefficientExtensionRing C.l E n) c :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  Functor.isoWhiskerRight (S.finiteSupport f c)
      (realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse ≪≫
    Functor.isoWhiskerLeft
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
      (inverseConjugation (realization (C := C) (E := E) (n := n) (hn := hn) X)
        (realization (C := C) (E := E) (n := n) (hn := hn) Y)
        (sixFunctorFiniteSupport D C E n hn f c)
        (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c)
        (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) c))

private theorem cancel_candidate_factors
    {C₀ B : Type*} [Category C₀] [Category B] {F G : C₀ ⥤ B}
    (e : F ≅ G) (K : C₀) {x y z : B}
    (a : x ⟶ y) (b : y ⟶ z) (c : z ⟶ G.obj K) :
    (a ≫ b ≫ c ≫ e.inv.app K) ≫ e.hom.app K = a ≫ b ≫ c := by
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

attribute [local irreducible] originComposition originCompositionAmbient originCompositionModel

private theorem candidateComposition_cancel (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (O : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    (finiteSupportCandidateComposition A f g cf cg cfg).hom.app O ≫
      (towerCandidateComparison A cfg (HasCompactification.compactification (f ≫ g))).hom.app O =
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
      ((towerCandidateComparison A cf (HasCompactification.compactification f)).hom.app O) ≫
      (towerCandidateComparison A cg (HasCompactification.compactification g)).hom.app
        ((originCompactSupport A f).obj O) ≫
      (originCompositionAmbient A f g).hom.app O := by
  rw [finiteSupportCandidateComposition_app]
  exact cancel_candidate_factors
    (towerCandidateComparison A cfg (HasCompactification.compactification (f ≫ g))) O _ _ _

attribute [local irreducible] originSupportComparison

private theorem spaceNoetherian (X : SixFunctorSpace D) : IsNoetherian X.obj.left := by
  let := X.property.1
  let := X.property.2
  let := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  let := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  exact {}

private def originOfRefinement (X : SixFunctorSpace D)
    (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left) :
    let := Padic.finite_coefficientExtensionRing C.l E n hn
    (DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      X.obj.left).FullSubcategory := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let Λ := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let : TopologicalSpace Λ := ⊥
  let := discreteTopology_bot Λ
  exact ⟨refinementFiniteLevelFixedObject C.l E n hn X.obj.left O,
    ⟨O.2.L.obj, O.2.L.property, ⟨refinementFixedWitnessIso X.obj.left Λ O⟩⟩⟩

private theorem candidate_at_refinement_witness
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left) :
    let := cf.hasCompactification
    let := cg.hasCompactification
    let := cfg.hasCompactification
    let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
    let := Padic.finite_coefficientExtensionRing C.l E n hn
    (finiteSupportCandidateComposition
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
      f.hom.left g.hom.left cf cg cfg).hom.app (originOfRefinement X O) =
      sixFunctorFiniteCompositionComparison C E n hn f g cf cg cfg O := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let Λ := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let : TopologicalSpace Λ := ⊥
  let := discreteTopology_bot Λ
  let := spaceNoetherian X
  let := spaceNoetherian Y
  let := spaceNoetherian Z
  let a := refinementFixedWitnessIso X.obj.left Λ O
  let OM := originOfRefinement (C := C) (E := E) (n := n) (hn := hn) X O
  let c := finiteSupportCandidateComposition Λ f.hom.left g.hom.left cf cg cfg
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X.obj.left
  have hq := finiteSupportCandidateTransport₂
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X.obj.left)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg)
    c.hom (Φ.obj O.2.L) OM a
  have he := finiteSupportCandidateComposition_etale
    Λ f.hom.left g.hom.left cf cg cfg O.2.L
  exact hq.trans (congrArg (fun z ↦
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).map
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf).map a.inv) ≫ z ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg).map a.hom) he)

private theorem fixedSupportComparison_of_normalization
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    let := cf.hasCompactification
    let := cg.hasCompactification
    let := cfg.hasCompactification
    let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
    let : QuasiCompact (f ≫ g).hom.left :=
      inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
    let := Padic.finite_coefficientExtensionRing C.l E n hn
    ∀ (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left)
      (w : (realization (C := C) (E := E) (n := n) (hn := hn) X).functor.obj
        (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) ≅ K.obj)
      (b : (candidateSupport (Padic.coefficientExtensionRing C.l E n) cg).obj
          ((candidateSupport (Padic.coefficientExtensionRing C.l E n) cf).obj
        ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)) ⟶
        (candidateSupport (Padic.coefficientExtensionRing C.l E n) cfg).obj
        ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)),
      (candidateSupport (Padic.coefficientExtensionRing C.l E n) cg).map
        ((candidateSupport (Padic.coefficientExtensionRing C.l E n) cf).map
        ((realization (C := C) (E := E) (n := n) (hn := hn) X).unitIso.hom.app
        (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O)
        ≫ (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.map w.hom)) ≫ b =
      sixFunctorFiniteCompositionComparison C E n hn f g cf cg cfg O ≫
        (candidateSupport (Padic.coefficientExtensionRing C.l E n) cfg).map
        ((realization (C := C) (E := E) (n := n) (hn := hn) X).unitIso.hom.app
        (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O)
        ≫ (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.map w.hom) →
    (realization (C := C) (E := E) (n := n) (hn := hn) Z).inverse.map
        ((S.finite.composition f g cf cg cfg).inv.app K).hom ≫
      (fixedSupportComparison S (f ≫ g) cfg).hom.app K =
    (fixedSupportComparison S g cg).hom.app ((S.finite.support f cf).obj K) ≫
      (candidateSupport (Padic.coefficientExtensionRing C.l E n) cg).map
        ((fixedSupportComparison S f cf).hom.app K) ≫
      b := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  intro _ _ _ _ _ _ O w b hnat
  let A := Padic.coefficientExtensionRing C.l E n
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let M := refinementFiniteLevelFixedObject C.l E n hn X.obj.left O
  have hnorm := S.finiteCompositionNormalization f g cf cg cfg K O w
  exact transport_normalization RX RY RZ
    (sixFunctorFiniteSupport D C E n hn f cf)
    (sixFunctorFiniteSupport D C E n hn g cg)
    (sixFunctorFiniteSupport D C E n hn (f ≫ g) cfg)
    (candidateSupport A cf) (candidateSupport A cg) (candidateSupport A cfg)
    (sfIntrinsicCompactSupportComparison A cf) (sfIntrinsicCompactSupportComparison A cg)
    (sfIntrinsicCompactSupportComparison A cfg)
    K.obj ((S.finite.support f cf).obj K).obj
    ((S.finite.support g cg).obj ((S.finite.support f cf).obj K)).obj
    ((S.finite.support (f ≫ g) cfg).obj K).obj
    ((S.finiteSupport f cf).app K)
    ((S.finiteSupport g cg).app ((S.finite.support f cf).obj K))
    ((S.finiteSupport (f ≫ g) cfg).app K) M w
    ((S.finite.composition f g cf cg cfg).inv.app K).hom
    (sixFunctorFiniteCompositionComparison C E n hn f g cf cg cfg O) b hnat hnorm

private theorem fixedSupportComparison_composition_app
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    let := cf.hasCompactification
    let := cg.hasCompactification
    let := cfg.hasCompactification
    let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
    let : QuasiCompact (f ≫ g).hom.left :=
      inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
    let := Padic.finite_coefficientExtensionRing C.l E n hn
    (realization (C := C) (E := E) (n := n) (hn := hn) Z).inverse.map
        ((S.finite.composition f g cf cg cfg).inv.app K).hom ≫
      (fixedSupportComparison S (f ≫ g) cfg).hom.app K =
    (fixedSupportComparison S g cg).hom.app ((S.finite.support f cf).obj K) ≫
      (candidateSupport (Padic.coefficientExtensionRing C.l E n) cg).map
        ((fixedSupportComparison S f cf).hom.app K) ≫
      (finiteSupportCandidateComposition
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
        f.hom.left g.hom.left cf cg cfg).hom.app
          ((originInclusion (C := C) (E := E) (n := n) (hn := hn) X).obj K) := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let Λ := ULift.{u + 1} A
  let : TopologicalSpace Λ := ⊥
  let := discreteTopology_bot Λ
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  obtain ⟨L, hL, ⟨e⟩⟩ := finiteRealization_etaleOrigin X K
  let L₀ : DerivedCategory.Plus (Sheaf X.obj.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) := ⟨L, hL⟩
  let O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left :=
    ⟨(finiteCoefficientComparison X.obj.left Λ).mapDerivedCategoryPlus.obj L₀,
      ⟨L₀, Iso.refl _⟩⟩
  let M := refinementFiniteLevelFixedObject C.l E n hn X.obj.left O
  let a := refinementFixedWitnessIso X.obj.left Λ O
  let OM := originOfRefinement (C := C) (E := E) (n := n) (hn := hn) X O
  let w : RX.functor.obj M ≅ K.obj :=
    RX.functor.mapIso (a.symm ≪≫ e) ≪≫ RX.counitIso.app K.obj
  let c := finiteSupportCandidateComposition Λ f.hom.left g.hom.left cf cg cfg
  have hnat := finiteSupportCandidateNaturality₂
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X.obj.left)
    (candidateSupport A cf) (candidateSupport A cg)
    (candidateSupport A cfg) c.hom OM ((originInclusion X).obj K)
    (RX.unitIso.hom.app M ≫ RX.inverse.map w.hom)
  have hcomp := candidate_at_refinement_witness f g cf cg cfg O
  rw [hcomp] at hnat
  exact fixedSupportComparison_of_normalization S f g cf cg cfg K O w
    (c.hom.app ((originInclusion X).obj K)) hnat

private theorem whiskerRight_twice_strict
    {B C₀ D₀ T : Type*} [Category B] [Category C₀] [Category D₀] [Category T]
    {F G : B ⥤ C₀} (P : C₀ ⥤ D₀) (Q : D₀ ⥤ T) (α : F ⟶ G) :
    Functor.whiskerRight (Functor.whiskerRight α P) Q =
      Functor.whiskerRight α (P ⋙ Q) := rfl

private theorem whiskerLeft_twice_strict
    {B C₀ D₀ T : Type*} [Category B] [Category C₀] [Category D₀] [Category T]
    (F : B ⥤ C₀) (G : C₀ ⥤ D₀) {P Q : D₀ ⥤ T} (α : P ⟶ Q) :
    Functor.whiskerLeft F (Functor.whiskerLeft G α) =
      Functor.whiskerLeft (F ⋙ G) α := rfl

private theorem whiskerRight_left_strict
    {B C₀ D₀ T : Type*} [Category B] [Category C₀] [Category D₀] [Category T]
    (F : B ⥤ C₀) {G H : C₀ ⥤ D₀} (α : G ⟶ H) (P : D₀ ⥤ T) :
    Functor.whiskerRight (Functor.whiskerLeft F α) P =
      Functor.whiskerLeft F (Functor.whiskerRight α P) := rfl

private theorem originSupportComparison_hom (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) :
    let := c.hasCompactification
    let := Padic.finite_coefficientExtensionRing C.l E n hn
    Functor.whiskerRight (originSupportComparison S f c).hom
      (DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        Y.obj.left).ι =
    (fixedSupportComparison S f c).hom ≫
      Functor.whiskerLeft (originInclusion (C := C) (E := E) (n := n) (hn := hn) X)
        (towerCandidateComparison (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
          c (HasCompactification.compactification f.hom.left)).hom := by
  let := c.hasCompactification
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let α := Functor.whiskerRight (S.finiteSupport f c).hom RY.inverse
  let β := Functor.whiskerLeft
    (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    (inverseConjugation RX RY (sixFunctorFiniteSupport D C E n hn f c)
      (sfFixedCompactSupport A c) (sfIntrinsicCompactSupportComparison A c)).hom
  let γ := Functor.whiskerLeft
    (originInclusion (C := C) (E := E) (n := n) (hn := hn) X)
    (towerCandidateComparison (ULift.{u + 1} A) c
      (HasCompactification.compactification f.hom.left)).hom
  unfold originSupportComparison
  change α ≫ β ≫ γ = (α ≫ β) ≫ γ
  exact (Category.assoc α β γ).symm

private theorem originComposition_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Functor.whiskerRight (originComposition A f g).hom
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι =
      (originCompositionAmbient A f g).hom := by
  unfold originComposition
  rfl

private theorem candidateComposition_cancel_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) :
    (finiteSupportCandidateComposition A f g cf cg cfg).hom ≫
      (towerCandidateComparison A cfg (HasCompactification.compactification (f ≫ g))).hom =
    Functor.whiskerRight
      (towerCandidateComparison A cf (HasCompactification.compactification f)).hom
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg) ≫
    Functor.whiskerLeft (originCompactSupport A f)
      (towerCandidateComparison A cg (HasCompactification.compactification g)).hom ≫
      (originCompositionAmbient A f g).hom := by
  apply NatTrans.ext
  funext O
  exact candidateComposition_cancel A f g cf cg cfg O

private theorem fixedSupportComparison_composition_nat
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    letI : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
    letI : QuasiCompact (f ≫ g).hom.left :=
      inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    Functor.whiskerRight (S.finite.composition f g cf cg cfg).inv
      ((intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι ⋙
        (realization (C := C) (E := E) (n := n) (hn := hn) Z).inverse) ≫
      (fixedSupportComparison S (f ≫ g) cfg).hom =
    Functor.whiskerLeft (S.finite.support f cf) (fixedSupportComparison S g cg).hom ≫
      Functor.whiskerRight (fixedSupportComparison S f cf).hom
        (candidateSupport (Padic.coefficientExtensionRing C.l E n) cg) ≫
      Functor.whiskerLeft (originInclusion (C := C) (E := E) (n := n) (hn := hn) X)
        (finiteSupportCandidateComposition
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
          f.hom.left g.hom.left cf cg cfg).hom := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  apply NatTrans.ext
  funext K
  exact fixedSupportComparison_composition_app S f g cf cg cfg K

attribute [local irreducible] fixedSupportComparison

private theorem supportComparison_candidate_path (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    letI : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
    letI : QuasiCompact (f ≫ g).hom.left :=
      inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := Padic.coefficientExtensionRing C.l E n
    let Λ := ULift.{u + 1} A
    let IX := originInclusion (C := C) (E := E) (n := n) (hn := hn) X
    let JZ := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z.obj.left).ι
    Functor.whiskerLeft (S.finite.support f cf)
        (Functor.whiskerRight (originSupportComparison S g cg).hom JZ) ≫
      Functor.whiskerRight (originSupportComparison S f cf).hom
        (originCompactSupport Λ g.hom.left ⋙ JZ) ≫
      Functor.whiskerLeft IX (originCompositionAmbient Λ f.hom.left g.hom.left).hom =
    (Functor.whiskerLeft (S.finite.support f cf) (fixedSupportComparison S g cg).hom ≫
      Functor.whiskerRight (fixedSupportComparison S f cf).hom (candidateSupport A cg) ≫
      Functor.whiskerLeft IX
        (finiteSupportCandidateComposition Λ f.hom.left g.hom.left cf cg cfg).hom) ≫
      Functor.whiskerLeft IX
        (towerCandidateComparison Λ cfg
          (HasCompactification.compactification (f.hom.left ≫ g.hom.left))).hom := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
  let : QuasiCompact (f ≫ g).hom.left :=
    inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  intro A Λ IX JZ
  let IY := originInclusion (C := C) (E := E) (n := n) (hn := hn) Y
  let JY := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Y.obj.left).ι
  let γf := originSupportComparison S f cf
  let Ug := originCompactSupport Λ g.hom.left
  let θg := towerCandidateComparison Λ cg (HasCompactification.compactification g.hom.left)
  rw [originSupportComparison_hom S g cg]
  simp only [Functor.whiskerLeft_comp, whiskerLeft_twice_strict, Category.assoc]
  have hex := Functor.whiskerLeft_comp_whiskerRight γf.hom θg.hom
  change Functor.whiskerLeft (S.finite.support f cf ⋙ IY) θg.hom ≫
      Functor.whiskerRight γf.hom (Ug ⋙ JZ) =
    Functor.whiskerRight γf.hom (JY ⋙ candidateSupport A cg) ≫
      Functor.whiskerLeft (IX ⋙ originCompactSupport Λ f.hom.left) θg.hom at hex
  rw [reassoc_of% hex]
  have hf := congrArg (fun η ↦ Functor.whiskerRight η (candidateSupport A cg))
    (originSupportComparison_hom S f cf)
  simp only [whiskerRight_twice_strict, Functor.whiskerRight_comp,
    whiskerRight_left_strict] at hf
  conv_lhs =>
    arg 2
    arg 1
    rw [hf]
  simp only [Category.assoc]
  conv_lhs =>
    arg 2
    arg 2
    arg 2
    arg 1
    rw [← whiskerLeft_twice_strict IX (originCompactSupport Λ f.hom.left) θg.hom]
  have hc := congrArg (Functor.whiskerLeft IX)
    (candidateComposition_cancel_nat Λ f.hom.left g.hom.left cf cg cfg)
  simp only [Functor.whiskerLeft_comp] at hc
  conv_lhs =>
    arg 2
    arg 2
    rw [← hc]

private theorem postcompose_normalization {T : Type*} [Category T]
    {a b c d : T} (α : a ⟶ b) (β : b ⟶ c) (γ : a ⟶ c)
    (h : α ≫ β = γ) (δ : c ⟶ d) : α ≫ β ≫ δ = γ ≫ δ := by
  rw [← Category.assoc, h]

private theorem faithful_composition_path
    {B₀ B₁ B₂ O₀ O₁ O₂ T : Type*}
    [Category B₀] [Category B₁] [Category B₂]
    [Category O₀] [Category O₁] [Category O₂] [Category T]
    (I₀ : B₀ ⥤ O₀) (I₁ : B₁ ⥤ O₁) (I₂ : B₂ ⥤ O₂)
    (F : B₀ ⥤ B₁) (G : B₁ ⥤ B₂) (FG : B₀ ⥤ B₂)
    (U : O₀ ⥤ O₁) (V : O₁ ⥤ O₂) (UV : O₀ ⥤ O₂)
    (J : O₂ ⥤ T) (H : J.FullyFaithful)
    (σ : FG ≅ F ⋙ G) (α : F ⋙ I₁ ≅ I₀ ⋙ U)
    (β : G ⋙ I₂ ≅ I₁ ⋙ V) (γ : FG ⋙ I₂ ≅ I₀ ⋙ UV)
    (ω : U ⋙ V ≅ UV)
    (h : Functor.whiskerRight σ.inv (I₂ ⋙ J) ≫ Functor.whiskerRight γ.hom J =
      Functor.whiskerLeft F (Functor.whiskerRight β.hom J) ≫
        Functor.whiskerRight α.hom (V ⋙ J) ≫
        Functor.whiskerLeft I₀ (Functor.whiskerRight ω.hom J)) :
    Functor.whiskerRight σ.inv I₂ ≫ γ.hom =
      Functor.whiskerLeft F β.hom ≫ Functor.whiskerRight α.hom V ≫
        Functor.whiskerLeft I₀ ω.hom := by
  apply (H.whiskeringRight B₀).map_injective
  change Functor.whiskerRight (Functor.whiskerRight σ.inv I₂ ≫ γ.hom) J =
    Functor.whiskerRight
      (Functor.whiskerLeft F β.hom ≫ Functor.whiskerRight α.hom V ≫
        Functor.whiskerLeft I₀ ω.hom) J
  simpa only [Functor.whiskerRight_comp, whiskerRight_twice_strict,
    whiskerRight_left_strict] using h

/-- The binary operation compositor agrees with the canonical origin compositor.
Source: finiteCompositionNormalization in def-sf-operation-stages and the witnessed
composition construction in proposition-composition-base-change-rf-shriek--1
(blueprint: lem-sf-finite-support-origin-binary-normalization).

Proof: fix a bounded constructible input and obtain its bounded etale origin by
finiteRing_constructibleDerived_origin. Retain this witness in
finiteCompositionNormalization. Expand the witness-support comparisons and cancel
its input identification. Naturality of the fixed-scalar support comparison cancels
the intermediate coefficient counit. The witnessed compositor is the canonical
origin compositor with the three candidate comparisons, by compact-support site
coherence and the definition of towerCandidateComparison. The candidate comparisons
cancel with those in originSupportComparison. The result is the displayed equality
at every object; natural-transformation extensionality proves the equation. This
involves two support operations, no tensor, no projection, and no triple coherence.
Zero objects and identity morphisms use the same cancellations. -/
theorem originSupportComparison_composition (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    letI : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
    letI : QuasiCompact (f ≫ g).hom.left :=
      inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    Functor.whiskerRight (S.finite.composition f g cf cg cfg).inv
        (originInclusion (C := C) (E := E) (n := n) (hn := hn) Z) ≫
      (originSupportComparison S (f ≫ g) cfg).hom =
    Functor.whiskerLeft (S.finite.support f cf) (originSupportComparison S g cg).hom ≫
      Functor.whiskerRight (originSupportComparison S f cf).hom
        (originCompactSupport
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) g.hom.left) ≫
      Functor.whiskerLeft (originInclusion (C := C) (E := E) (n := n) (hn := hn) X)
        (originComposition
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
          f.hom.left g.hom.left).hom := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
  let : QuasiCompact (f ≫ g).hom.left :=
    inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let Λ := ULift.{u + 1} A
  let IX := originInclusion (C := C) (E := E) (n := n) (hn := hn) X
  let IY := originInclusion (C := C) (E := E) (n := n) (hn := hn) Y
  let IZ := originInclusion (C := C) (E := E) (n := n) (hn := hn) Z
  let JZ := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z.obj.left).ι
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z.obj.left).fullyFaithfulι
  let σ := S.finite.composition f g cf cg cfg
  let γf := originSupportComparison S f cf
  let γg := originSupportComparison S g cg
  let γfg := originSupportComparison S (f ≫ g) cfg
  let Ug := originCompactSupport Λ g.hom.left
  let ω := originComposition Λ f.hom.left g.hom.left
  let θfg := towerCandidateComparison Λ cfg
    (HasCompactification.compactification (f.hom.left ≫ g.hom.left))
  apply faithful_composition_path IX IY IZ (S.finite.support f cf)
    (S.finite.support g cg) (S.finite.support (f ≫ g) cfg)
    (originCompactSupport Λ f.hom.left) Ug (originCompactSupport Λ (f ≫ g).hom.left)
    JZ H σ γf γg γfg ω
  change Functor.whiskerRight σ.inv
      ((intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι ⋙
        (realization (C := C) (E := E) (n := n) (hn := hn) Z).inverse) ≫
      Functor.whiskerRight γfg.hom JZ = _
  rw [originSupportComparison_hom S (f ≫ g) cfg, originComposition_hom]
  rw [supportComparison_candidate_path S f g cf cg cfg]
  change Functor.whiskerRight σ.inv
      ((intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι ⋙
        (realization (C := C) (E := E) (n := n) (hn := hn) Z).inverse) ≫
      (fixedSupportComparison S (f ≫ g) cfg).hom ≫
      Functor.whiskerLeft IX θfg.hom =
    (Functor.whiskerLeft (S.finite.support f cf) (fixedSupportComparison S g cg).hom ≫
      Functor.whiskerRight (fixedSupportComparison S f cf).hom (candidateSupport A cg) ≫
      Functor.whiskerLeft IX
        (finiteSupportCandidateComposition Λ f.hom.left g.hom.left cf cg cfg).hom) ≫
      Functor.whiskerLeft IX θfg.hom
  exact postcompose_normalization _ _ _
    (fixedSupportComparison_composition_nat S f g cf cg cfg)
    (Functor.whiskerLeft IX θfg.hom)

end WeilConjectures.CompactSupportFiniteProjection
