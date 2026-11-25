/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition

/-! # Candidate comparisons and the fixed-scalar support compositor -/

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

attribute [local implicit_reducible] rightDerivedLowerShriek originCompactSupport
  comparisonUpperStarPlusEtaleOrigin coherenceProEtaleFunctor
  coherenceBoundedSiteFunctor coherenceSiteFunctor coherenceEtaleFunctor

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  originCompositionModel towerCandidateComparison

/-- Naturality of the four-factor comparison.
Source: naturality of the four factors and functoriality
(blueprint: lem-sf-finite-support-candidate-composition).

Proof: move the input map through the four factors, in order, using the naturality
of α, β, ω and δ⁻¹. Functoriality of Q moves it through the first factor. -/
theorem finiteSupportCandidateCompositionCore_naturality
    {C₀ C₁ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category D₂]
    (I : C₀ ⥤ D₀) (J : C₁ ⥤ D₁) (F : C₀ ⥤ C₁)
    (P : D₀ ⥤ D₁) (Q Q₀ : D₁ ⥤ D₂) (R R₀ : D₀ ⥤ D₂)
    (α : I ⋙ P ≅ F ⋙ J) (β : J ⋙ Q ≅ J ⋙ Q₀)
    (ω : F ⋙ J ⋙ Q₀ ≅ I ⋙ R₀) (δ : I ⋙ R ≅ I ⋙ R₀) (K L : C₀) (h : K ⟶ L) :
    Q.map (P.map (I.map h)) ≫
        (Q.map (α.hom.app L) ≫ β.hom.app (F.obj L) ≫ ω.hom.app L ≫ δ.inv.app L) =
      (Q.map (α.hom.app K) ≫ β.hom.app (F.obj K) ≫ ω.hom.app K ≫ δ.inv.app K) ≫
        R.map (I.map h) := by
  have hf := α.hom.naturality h
  have hg := β.hom.naturality (F.map h)
  have hc := ω.hom.naturality h
  have hh := δ.inv.naturality h
  dsimp only [Functor.comp_map] at hf hg hc hh
  change Q.map (P.map (I.map h)) ≫
      (Q.map (α.hom.app L) ≫ β.hom.app (F.obj L) ≫ ω.hom.app L ≫ δ.inv.app L) =
    (Q.map (α.hom.app K) ≫ β.hom.app (F.obj K) ≫ ω.hom.app K ≫ δ.inv.app K) ≫
      R.map (I.map h)
  rw [← Q.map_comp_assoc, hf, Q.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hg, reassoc_of% hc, hh]

/-- Compose four comparison factors, keeping the naturality calculation abstract.
Source: functoriality and naturality
(blueprint: lem-sf-finite-support-candidate-composition). -/
@[irreducible] def finiteSupportCandidateCompositionCore
    {C₀ C₁ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category D₂]
    (I : C₀ ⥤ D₀) (J : C₁ ⥤ D₁) (F : C₀ ⥤ C₁)
    (P : D₀ ⥤ D₁) (Q Q₀ : D₁ ⥤ D₂) (R R₀ : D₀ ⥤ D₂)
    (α : I ⋙ P ≅ F ⋙ J) (β : J ⋙ Q ≅ J ⋙ Q₀)
    (ω : F ⋙ J ⋙ Q₀ ≅ I ⋙ R₀) (δ : I ⋙ R ≅ I ⋙ R₀) :
    I ⋙ P ⋙ Q ≅ I ⋙ R := by
  refine NatIso.ofComponents (fun K ↦ Q.mapIso (α.app K) ≪≫ β.app (F.obj K) ≪≫
    ω.app K ≪≫ (δ.app K).symm) ?_
  intro K L h
  exact finiteSupportCandidateCompositionCore_naturality
    I J F P Q Q₀ R R₀ α β ω δ K L h

/-- Component formula for the abstract four-factor construction.
Source: its definition
(blueprint: lem-sf-finite-support-candidate-composition). -/
theorem finiteSupportCandidateCompositionCore_app
    {C₀ C₁ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category D₂]
    (I : C₀ ⥤ D₀) (J : C₁ ⥤ D₁) (F : C₀ ⥤ C₁)
    (P : D₀ ⥤ D₁) (Q Q₀ : D₁ ⥤ D₂) (R R₀ : D₀ ⥤ D₂)
    (α : I ⋙ P ≅ F ⋙ J) (β : J ⋙ Q ≅ J ⋙ Q₀)
    (ω : F ⋙ J ⋙ Q₀ ≅ I ⋙ R₀) (δ : I ⋙ R ≅ I ⋙ R₀) (K : C₀) :
    (finiteSupportCandidateCompositionCore I J F P Q Q₀ R R₀ α β ω δ).hom.app K =
      Q.map (α.hom.app K) ≫ β.hom.app (F.obj K) ≫ ω.hom.app K ≫ δ.inv.app K := by
  unfold finiteSupportCandidateCompositionCore
  rfl

/-- Conjugate the canonical origin compositor to the three specified candidates.
Source: proposition-composition-base-change-rf-shriek--1, compactification independence
(blueprint: lem-sf-finite-support-candidate-composition). -/
@[irreducible] def finiteSupportCandidateComposition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg :=
  finiteSupportCandidateCompositionCore
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).ι
    (originCompactSupport A f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (towerCandidateComparison A cf (HasCompactification.compactification f))
    (towerCandidateComparison A cg (HasCompactification.compactification g))
    (originCompositionAmbient A f g)
    (towerCandidateComparison A cfg (HasCompactification.compactification (f ≫ g)))

private theorem ambient_composition_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (originCompositionAmbient A f g).hom.app
      ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
      (originCompositionModel A f g).hom.app L := by
  have h := congr_app (originComposition_model A f g) L
  change (originCompositionAmbient A f g).hom.app
    ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) = _ at h
  exact h

/-- The four specified component maps of the candidate compositor.
Source: its componentwise construction
(blueprint: lem-sf-finite-support-candidate-composition). -/
theorem finiteSupportCandidateComposition_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    (finiteSupportCandidateComposition A f g cf cg cfg).hom.app K =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((towerCandidateComparison A cf (HasCompactification.compactification f)).hom.app K) ≫
      (towerCandidateComparison A cg (HasCompactification.compactification g)).hom.app
        ((originCompactSupport A f).obj K) ≫
      (originCompositionAmbient A f g).hom.app K ≫
      (towerCandidateComparison A cfg
        (HasCompactification.compactification (f ≫ g))).inv.app K := by
  unfold finiteSupportCandidateComposition
  exact finiteSupportCandidateCompositionCore_app _ _ _ _ _ _ _ _ _ _ _ _ K

private theorem square_conjugate {B : Type*} [Category B]
    {x x' y y' : B} (i : x ≅ x') (j : y ≅ y')
    (m : x ⟶ y) (r : x' ⟶ y') (h : m ≫ j.hom = i.hom ≫ r) :
    i.inv ≫ m ≫ j.hom = r := by
  rw [h]
  simp

private theorem naturality_conjugate {B T : Type*} [Category B] [Category T]
    {F G : B ⥤ T} (η : F ⟶ G) {X Y : B} (e : X ≅ Y) :
    η.app X = F.map e.hom ≫ η.app Y ≫ G.map e.inv := by
  rw [η.naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]

/-- Transport a comparison on a full subcategory across an ambient isomorphism.
Source: naturality and inverse cancellation
(blueprint: lem-sf-finite-support-candidate-composition). -/
theorem finiteSupportCandidateTransport
    {A B : Type*} [Category A] [Category B] (S : ObjectProperty A)
    (P Q : A ⥤ B) (η : S.ι ⋙ P ⟶ S.ι ⋙ Q)
    (K L : S.FullSubcategory) (a : K.obj ≅ L.obj) :
    η.app L = P.map a.inv ≫ η.app K ≫ Q.map a.hom := by
  let e : K ≅ L := ObjectProperty.isoMk _ a
  exact naturality_conjugate η e.symm

/-- The same transport, with the two source operations evaluated explicitly.
Source: functor composition (blueprint: lem-sf-finite-support-candidate-composition). -/
theorem finiteSupportCandidateTransport₂
    {A B T : Type*} [Category A] [Category B] [Category T] (S : ObjectProperty A)
    (P : A ⥤ B) (Q : B ⥤ T) (R : A ⥤ T)
    (η : S.ι ⋙ P ⋙ Q ⟶ S.ι ⋙ R)
    (K L : S.FullSubcategory) (a : K.obj ≅ L.obj) :
    η.app L = Q.map (P.map a.inv) ≫ η.app K ≫ R.map a.hom :=
  finiteSupportCandidateTransport S (P ⋙ Q) R η K L a

/-- Naturality on a full subcategory, evaluated on an ambient morphism.
Source: naturality (blueprint: lem-sf-finite-support-candidate-composition). -/
theorem finiteSupportCandidateNaturality₂
    {A B T : Type*} [Category A] [Category B] [Category T] (S : ObjectProperty A)
    (P : A ⥤ B) (Q : B ⥤ T) (R : A ⥤ T)
    (η : S.ι ⋙ P ⋙ Q ⟶ S.ι ⋙ R)
    (K L : S.FullSubcategory) (m : K.obj ⟶ L.obj) :
    Q.map (P.map m) ≫ η.app L = η.app K ≫ R.map m :=
  η.naturality (ObjectProperty.homMk m)

private theorem candidate_at_etale (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (towerCandidateComparison A c d).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
      (coherenceCompactificationChange A c d L).hom := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  let model := compactSupportSiteComparison A c ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c d)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≪≫
    (compactSupportSiteComparison A d).symm
  have ht := (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).map_preimage
    (X := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (Y := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) model.hom
  have hh : (towerCandidateComparison A c d).hom.app (Φ.obj L) = model.hom.app L := by
    unfold towerCandidateComparison
    exact congr_app ht L
  have hb : model.hom.app L =
      (coherenceBoundaryComponent A c L).inv ≫
        (coherenceBoundedSiteFunctor A Y).map
          ((coherenceEtaleChangeIso A c d).hom.app L) ≫
        (coherenceBoundaryComponent A d L).hom := by
    simp only [model, coherenceBoundaryComponent, coherenceEvaluateSquare,
      coherenceBoundaryIso, compactExchangeTransportComparison,
      coherenceBoundedSiteFunctor, coherenceSiteFunctor, coherenceEtaleChangeIso,
      Etale.rightDerivedLowerShriekOfCompactificationPlusιIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_map, Functor.map_comp, Functor.comp_obj,
      Category.assoc, Category.id_comp, Category.comp_id]
    erw [Category.id_comp]
  exact hh.trans (hb.trans (square_conjugate (coherenceBoundaryComponent A c L)
    (coherenceBoundaryComponent A d L) _ _
    (compactification_change_square_component A c d L)))

private theorem inverse_app_of_hom {B T : Type*} [Category B] [Category T]
    {F G : B ⥤ T} (e : F ≅ G) (K : B) (i : F.obj K ≅ G.obj K)
    (h : e.hom.app K = i.hom) : e.inv.app K = i.inv := by
  have hi : e.app K = i := Iso.ext ((Iso.app_hom e K).trans h)
  exact (Iso.app_inv e K).symm.trans (congrArg Iso.inv hi)

private theorem inverse_square {B T : Type*} [Category B] [Category T]
    (N : B ⥤ T) {X Y : B} {x y : T} (i : N.obj X ≅ x) (j : N.obj Y ≅ y)
    (e : X ≅ Y) (m : x ≅ y) (r : y ≅ x)
    (h : N.map e.hom ≫ j.hom = i.hom ≫ m.hom)
    (h' : N.map e.inv ≫ i.hom = j.hom ≫ r.hom) : m.inv = r.hom := by
  have hm : m = i.symm ≪≫ N.mapIso e ≪≫ j := by
    apply Iso.ext
    exact (square_conjugate i j _ _ h).symm
  rw [hm]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc] using
    square_conjugate j i _ _ h'

private theorem coherence_change_inverse (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceCompactificationChange A c d L).inv =
      (coherenceCompactificationChange A d c L).hom := by
  have h := compactification_change_square_component A c d L
  have h' := compactification_change_square_component A d c L
  have hs := congr_app (congrArg Iso.hom
    (Etale.rightDerivedLowerShriekOfCompactificationPlusIso_symm A c d)) L
  change (coherenceEtaleChangeIso A c d).inv.app L =
    (coherenceEtaleChangeIso A d c).hom.app L at hs
  rw [← hs] at h'
  exact inverse_square (coherenceBoundedSiteFunctor A Y)
    (coherenceBoundaryComponent A c L) (coherenceBoundaryComponent A d L)
    ((coherenceEtaleChangeIso A c d).app L)
    (coherenceCompactificationChange A c d L)
    (coherenceCompactificationChange A d c L) h h'

private theorem substitute_four_factors {B : Type*} [Category B]
    {x₀ x₁ x₂ x₃ x₄ y₁ y₂ : B}
    {a a' : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c c' : x₂ ⟶ x₃} {d d' : x₃ ⟶ x₄}
    {b₁ : x₁ ⟶ y₁} {b₂ : y₁ ⟶ y₂} {b₃ : y₂ ⟶ x₂}
    (ha : a = a') (hb : b = b₁ ≫ b₂ ≫ b₃) (hc : c = c') (hd : d = d') :
    a ≫ b ≫ c ≫ d = a' ≫ b₁ ≫ b₂ ≫ b₃ ≫ c' ≫ d' := by
  rw [ha, hb, hc, hd]
  simp only [Category.assoc]

private theorem proMap_from_four
    {C D : Type*} [Category C] [Category D] {N : C ⥤ D}
    {a₀ a₁ a₂ a₃ a₄ : C} {b₀ b₁ b₂ v₀ v₁ v₂ p q : D}
    {bin : N.obj a₀ ⟶ v₀} {bout : N.obj a₄ ⟶ q}
    (t : CoherencePastingData N a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ v₀ v₁ v₂ p q bin bout)
    {a : v₀ ⟶ v₁} {b : v₁ ⟶ v₂} {c : v₂ ⟶ p} {d : p ⟶ q}
    (ha : a = t.r₁) (hb : b = t.r₂ ≫ t.rd ≫ t.rb) (hc : c = t.o) (hd : d = t.re) :
    a ≫ b ≫ c ≫ d = t.proMap :=
  substitute_four_factors ha hb hc hd

private theorem proMap_grouped
    {C D : Type*} [Category C] [Category D] {N : C ⥤ D}
    {a₀ a₁ a₂ a₃ a₄ : C} {b₀ b₁ b₂ v₀ v₁ v₂ p q : D}
    {bin : N.obj a₀ ⟶ v₀} {bout : N.obj a₄ ⟶ q}
    (t : CoherencePastingData N a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ v₀ v₁ v₂ p q bin bout) :
    t.r₁ ≫ (t.r₂ ≫ t.rd ≫ t.rb) ≫ t.o ≫ t.re = t.proMap :=
  proMap_from_four t rfl rfl rfl rfl

private theorem coherence_data_r1 (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (coherenceCompositionData A cf cg cfg L).r₁ =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        (coherenceCompactificationChange A cf (HasCompactification.compactification f) L).hom := by
  rfl

private theorem coherence_data_r2 (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (coherenceCompositionData A cf cg cfg L).r₂ =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        (coherenceBoundaryComponent A (HasCompactification.compactification f) L).inv := by
  rfl

private theorem coherence_data_rd (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (coherenceCompositionData A cf cg cfg L).rd =
      (coherenceCompactificationChange A cg (HasCompactification.compactification g)
        ((coherenceEtaleFunctor A (HasCompactification.compactification f)).obj L)).hom := by
  rfl

private theorem coherence_data_rb (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (coherenceCompositionData A cf cg cfg L).rb =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification g)).map
        (coherenceBoundaryComponent A (HasCompactification.compactification f) L).hom := by
  rfl

private def coherence_data_with_o (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (o : (coherenceProEtaleFunctor A (HasCompactification.compactification g)).obj
        ((coherenceProEtaleFunctor A (HasCompactification.compactification f)).obj
          ((coherenceBoundedSiteFunctor A X).obj L)) ⟶
      (coherenceProEtaleFunctor A (HasCompactification.compactification (f ≫ g))).obj
        ((coherenceBoundedSiteFunctor A X).obj L)) :
  let cf₀ := HasCompactification.compactification f
  let cg₀ := HasCompactification.compactification g
  let cfg₀ := HasCompactification.compactification (f ≫ g)
  let NX := coherenceBoundedSiteFunctor A X
  let NY := coherenceBoundedSiteFunctor A Y
  let NZ := coherenceBoundedSiteFunctor A Z
  let Ec := coherenceEtaleFunctor A cf
  let Ea := coherenceEtaleFunctor A cf₀
  let Ed := coherenceEtaleFunctor A cg
  let Eb := coherenceEtaleFunctor A cg₀
  let Efg := coherenceEtaleFunctor A cfg₀
  let Ee := coherenceEtaleFunctor A cfg
  let Fc := coherenceProEtaleFunctor A cf
  let Fa := coherenceProEtaleFunctor A cf₀
  let Fd := coherenceProEtaleFunctor A cg
  let Fb := coherenceProEtaleFunctor A cg₀
  let Ffg := coherenceProEtaleFunctor A cfg₀
  let Fe := coherenceProEtaleFunctor A cfg
  let M := Ea.obj L
  CoherencePastingData NZ (Ed.obj (Ec.obj L)) (Ed.obj M) (Eb.obj M) (Efg.obj L)
    (Ee.obj L) (Fd.obj (NY.obj (Ec.obj L))) (Fd.obj (NY.obj M)) (Fb.obj (NY.obj M))
    (Fd.obj (Fc.obj (NX.obj L))) (Fd.obj (Fa.obj (NX.obj L)))
    (Fb.obj (Fa.obj (NX.obj L))) (Ffg.obj (NX.obj L)) (Fe.obj (NX.obj L))
    (coherenceCompositionSource A cf cg L).hom (coherenceBoundaryComponent A cfg L).hom :=
  let c := HasCompactification.compactification f
  let d := HasCompactification.compactification g
  let e := HasCompactification.compactification (f ≫ g)
  let M := (coherenceEtaleFunctor A c).obj L
  { coherenceCompositionData A cf cg cfg L with
    e₀ := (coherenceEtaleFunctor A cg).mapIso ((coherenceEtaleChangeIso A cf c).app L)
    e₁ := (coherenceEtaleChangeIso A cg d).app M
    e₂ := coherenceChosenEtaleCompositorComponent A f g L
    e₃ := (coherenceEtaleChangeIso A e cfg).app L
    s₀ := (coherenceBoundaryComponent A cg ((coherenceEtaleFunctor A cf).obj L)).hom
    s₁ := (coherenceBoundaryComponent A cg M).hom
    s₂ := (coherenceBoundaryComponent A d M).hom
    s₃ := (coherenceBoundaryComponent A e L).hom
    r₀ := (coherenceProEtaleFunctor A cg).map (coherenceBoundaryComponent A cf L).hom
    r₁ := (coherenceProEtaleFunctor A cg).map
      (coherenceCompactificationChange A cf c L).hom
    r₂ := (coherenceProEtaleFunctor A cg).map (coherenceBoundaryComponent A c L).inv
    rd := (coherenceCompactificationChange A cg d M).hom
    rb := (coherenceProEtaleFunctor A d).map (coherenceBoundaryComponent A c L).hom
    o := o
    re := (coherenceCompactificationChange A e cfg L).hom
    n := (coherenceProEtaleFunctor A cg).map
      ((coherenceBoundedSiteFunctor A Y).map ((coherenceEtaleChangeIso A cf c).hom.app L)) }

private theorem coherence_data_with_o_projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (o : (coherenceProEtaleFunctor A (HasCompactification.compactification g)).obj
        ((coherenceProEtaleFunctor A (HasCompactification.compactification f)).obj
          ((coherenceBoundedSiteFunctor A X).obj L)) ⟶
      (coherenceProEtaleFunctor A (HasCompactification.compactification (f ≫ g))).obj
        ((coherenceBoundedSiteFunctor A X).obj L)) :
    (coherence_data_with_o A f g cf cg cfg L o).o = o := by
  rfl

private theorem coherence_data_eq_with_o (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    coherenceCompositionData A cf cg cfg L =
      coherence_data_with_o A f g cf cg cfg L
        (coherenceChosenProEtaleCompositorComponent A f g L).hom := by
  rfl

private theorem coherence_data_o (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (coherenceCompositionData A cf cg cfg L).o =
      (coherenceChosenProEtaleCompositorComponent A f g L).hom := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  exact (congrArg CoherencePastingData.o
    (coherence_data_eq_with_o A f g cf cg cfg L)).trans
      (coherence_data_with_o_projection A f g cf cg cfg L _)

private theorem coherence_data_re (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (coherenceCompositionData A cf cg cfg L).re =
      (coherenceCompactificationChange A
        (HasCompactification.compactification (f ≫ g)) cfg L).hom := by
  rfl

private theorem chosen_compositor_iso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    coherenceChosenProEtaleCompositorComponent A f g L =
      (originCompositionModel A f g).app L := by
  rfl

private theorem coherence_pro_definition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    coherenceProEtaleCompositor A cf cg cfg L =
      (coherenceCompositionData A cf cg cfg L).proMap := by
  rfl

private theorem candidate_factor_one (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((towerCandidateComparison A cf
          (HasCompactification.compactification f)).hom.app
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L)) =
      (coherenceCompositionData A cf cg cfg L).r₁ := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  let Ψ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y
  let c := HasCompactification.compactification f
  let d := HasCompactification.compactification g
  let e := HasCompactification.compactification (f ≫ g)
  let M := (coherenceEtaleFunctor A c).obj L
  let t := coherenceCompositionData A cf cg cfg L
  exact ((rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} A) cg).congr_map (candidate_at_etale A cf c L)).trans
      (coherence_data_r1 A f g cf cg cfg L).symm

private theorem candidate_factor_two (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (towerCandidateComparison A cg (HasCompactification.compactification g)).hom.app
        ((originCompactSupport A f).obj
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L)) =
      (coherenceCompositionData A cf cg cfg L).r₂ ≫
        (coherenceCompositionData A cf cg cfg L).rd ≫
        (coherenceCompositionData A cf cg cfg L).rb := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  let Ψ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y
  let c := HasCompactification.compactification f
  let d := HasCompactification.compactification g
  let e := HasCompactification.compactification (f ≫ g)
  let M := (coherenceEtaleFunctor A c).obj L
  have hq := finiteSupportCandidateTransport
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (towerCandidateComparison A cg d).hom
    (Ψ.obj M) ((originCompactSupport A f).obj (Φ.obj L))
    (coherenceBoundaryComponent A c L)
  have hb := hq.trans (congrArg (fun z ↦
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        (coherenceBoundaryComponent A c L).inv ≫ z ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        (coherenceBoundaryComponent A c L).hom) (candidate_at_etale A cg d M))
  rw [coherence_data_r2, coherence_data_rd, coherence_data_rb]
  exact hb

private theorem candidate_factor_three (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (originCompositionAmbient A f g).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
      (coherenceCompositionData A cf cg cfg L).o := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  let Ψ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y
  let c := HasCompactification.compactification f
  let d := HasCompactification.compactification g
  let e := HasCompactification.compactification (f ≫ g)
  let M := (coherenceEtaleFunctor A c).obj L
  have hi := (congrArg Iso.hom (chosen_compositor_iso A f g L)).trans
    (Iso.app_hom (originCompositionModel A f g) L)
  exact ((ambient_composition_app A f g L).trans hi.symm).trans
    (coherence_data_o A f g cf cg cfg L).symm

private theorem candidate_factor_four (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (towerCandidateComparison A cfg
        (HasCompactification.compactification (f ≫ g))).inv.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
      (coherenceCompositionData A cf cg cfg L).re := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  let Ψ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y
  let c := HasCompactification.compactification f
  let d := HasCompactification.compactification g
  let e := HasCompactification.compactification (f ≫ g)
  let M := (coherenceEtaleFunctor A c).obj L
  have he' := (inverse_app_of_hom (towerCandidateComparison A cfg e) (Φ.obj L)
    (coherenceCompactificationChange A cfg e L) (candidate_at_etale A cfg e L)).trans
      (coherence_change_inverse A cfg e L)
  exact he'.trans (coherence_data_re A f g cf cg cfg L).symm

private theorem coherence_pro_grouped (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    coherenceProEtaleCompositor A cf cg cfg L =
      (coherenceCompositionData A cf cg cfg L).r₁ ≫
        ((coherenceCompositionData A cf cg cfg L).r₂ ≫ (coherenceCompositionData A cf cg cfg L).rd ≫
          (coherenceCompositionData A cf cg cfg L).rb) ≫
        (coherenceCompositionData A cf cg cfg L).o ≫
          (coherenceCompositionData A cf cg cfg L).re := by
  exact (coherence_pro_definition A f g cf cg cfg L).trans
    (proMap_grouped (coherenceCompositionData A cf cg cfg L)).symm

/-- The candidate compositor evaluates to the recorded pro-etale compositor on an
etale input. Source: compactSupportSiteCoherence, comparison/composition calculation,
and proposition-composition-base-change-rf-shriek--1
(blueprint: lem-sf-finite-support-candidate-composition).

Proof: precompose each towerCandidateComparison with the etale-origin equivalence.
Its defining fully faithful preimage is the site comparison, the etale change of
compactification, and the inverse site comparison. The refinement square for each
leg of the common refinement identifies this with coherenceCompactificationChange.
The inverse comparison is the reverse comparison by the etale cocycle law.
Use the site comparison for the first chosen compactification to identify its
support value with the etale support of the input. Naturality of the second
candidate comparison inserts this identification and its inverse. The chosen
origin compositor evaluates to originCompositionModel by its fully faithful
preimage construction. The resulting six factors are exactly those of
coherenceCompositionData.proMap, hence coherenceProEtaleCompositor. This calculation
also applies to zero complexes and identity scheme morphisms. -/
theorem finiteSupportCandidateComposition_etale (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    (finiteSupportCandidateComposition A f g cf cg cfg).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
      coherenceProEtaleCompositor A cf cg cfg L := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  rw [finiteSupportCandidateComposition_app, candidate_factor_one,
    candidate_factor_two, candidate_factor_three, candidate_factor_four,
    coherence_pro_grouped]

end WeilConjectures.CompactSupportFiniteProjection
