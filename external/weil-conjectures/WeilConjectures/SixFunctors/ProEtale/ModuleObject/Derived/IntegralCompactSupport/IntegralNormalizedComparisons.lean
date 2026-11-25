/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBoundaryRefinementNormalization

/-! # Coherence portions for integral compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
attribute [local irreducible]
  AlgebraicGeometry.Compactification.inf AlgebraicGeometry.Compactification.graph
  AlgebraicGeometry.Compactification.infFst AlgebraicGeometry.Compactification.infSnd
set_option synthInstance.maxSize 2048
set_option Elab.async false

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
section Coefficients

attribute [local instance 2000] CategoryTheory.scalarTensor4 CategoryTheory.scalarTensor12
  CategoryTheory.scalarTensor23 CategoryTheory.scalarTensorColimits
  CategoryTheory.scalarFlipTensorColimits CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
attribute [local irreducible] HasDerivedCategory.standard

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar openImmersionLowerShriek
  derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  localizing localizingClosureProEtale CategoryTheory.localizingClosure
  compactificationRefinementComponent localizingRefinementMap
  pushComp refinementDerivedLowerStarComp
  Adjunction.ofNatIsoRight upperStarComp

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Restrict a comparison along an inclusion of full subcategories. -/
private def restrict_comparison {C D : Type*} [Category C] [Category D]
    {P Q : ObjectProperty C} (h : P ≤ Q) {F G : C ⥤ D}
    (e : Q.ι ⋙ F ≅ Q.ι ⋙ G) : P.ι ⋙ F ≅ P.ι ⋙ G :=
  NatIso.ofComponents (fun K ↦ e.app ((ObjectProperty.ιOfLE h).obj K)) (by
    intro K L a
    exact e.hom.naturality ((ObjectProperty.ιOfLE h).map a))

private theorem iso_eq_of_hom_inv {C : Type*} [Category C] {X Y : C}
    (a b : X ≅ Y) (h : a.hom ≫ b.inv = 𝟙 X) : a = b := by
  apply Iso.ext
  apply (cancel_mono b.inv).1
  exact h.trans b.hom_inv_id.symm

private theorem cancel_refinement {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ A) (h : A ⟶ D) (q : B ⟶ D) (hh : IsIso h)
    (hf : f ≫ q = h) (hq : q = g ≫ h) : f ≫ g = 𝟙 A := by
  let _ : IsIso h := hh
  apply (cancel_mono h).1
  simpa only [hq, Category.assoc, Category.id_comp] using hf

private theorem iso_eq_of_inv {C : Type*} [Category C] {A B : C}
    (a b : A ≅ B) (g : B ⟶ A) (h : a.hom ≫ g = 𝟙 A) (hb : HEq b.inv g) : a = b :=
  iso_eq_of_hom_inv a b ((congrArg (fun z ↦ a.hom ≫ z) (eq_of_heq hb)).trans h)

private theorem exists_iso_eq_of_inv {C : Type*} [Category C] {A B : C}
    {E : Sort*} {P : E → Prop} {F : E → (A ≅ B)}
    (a : A ≅ B) (g : B ⟶ A) (h : a.hom ≫ g = 𝟙 A)
    (he : ∃ e, P e ∧ HEq (F e).inv g) : ∃ e, P e ∧ a = F e := by
  obtain ⟨e, he, hinv⟩ := he
  exact ⟨e, he, iso_eq_of_inv a (F e) g h hinv⟩

/-- A common dense refinement of a compactification with itself supplies a dense source. -/
private theorem dense_refinement {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f) :
    ∃ w : Compactification.BoundaryCompactification f,
      IsSchemeTheoreticallyDominant w.obj.obj.i ∧ Nonempty (w ⟶ c) := by
  have h := Compactification.exists_common_dense_refinement.{u, u} f c.obj.obj c.obj.obj
  let w : Compactification.BoundaryCompactification f :=
    ⟨⟨Compactification.inf c.obj.obj c.obj.obj, h.2.2.1⟩⟩
  refine ⟨w, h.2.2.2.1, ⟨?_⟩⟩
  exact ⟨ObjectProperty.homMk (Compactification.infFst c.obj.obj c.obj.obj),
    h.2.2.2.2.2.2.2.2.2.2.2.1⟩

variable (k : Type u) [Field k]
-- The explicit comparison family has several large derived-category instance arguments.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparisonsForCoefficient
    (ℓ : ℕ) [Fact ℓ.Prime] (hadm : IsLocalizingAdmissibleCoefficient ℓ Λ)
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hclosure : ∀ X : Spaces k,
      localizingClosureProEtale Λ X.obj.left = localizing Λ X.obj.left) :
    ∃ φ : Comparisons Λ k,
      (∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactifications k f),
    φ f c c = Iso.refl _) ∧
      (∀ {X Y : Spaces k} (f : X ⟶ Y) (c d e : Compactifications k f),
    φ f c d ≪≫ φ f d e = φ f c e) ∧
      (∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing Λ X.obj.left).FullSubcategory),
      ∃ e : (extend Λ d.obj.i).obj K.obj ≅
          (push Λ r.hom).obj ((extend
            Λ c.obj.i).obj K.obj),
        (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction Λ r K.obj =
              (openAdjunction Λ c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso Λ r K.obj e) := by
  classical
  have per_morphism {X Y : Spaces k} (f : X ⟶ Y) :
      ∃ φ : ∀ c d : Compactifications k f,
          candidate Λ k (X := X) (Y := Y) (f := f) c ≅
            candidate Λ k (X := X) (Y := Y) (f := f) d,
        (∀ c, φ c c = Iso.refl _) ∧
        (∀ c d e, φ c d ≪≫ φ d e = φ c e) ∧
        (∀ (c d : Compactifications k f) (r : c.obj.Refinement d.obj)
          (hb : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
          (K : (localizing Λ X.obj.left).FullSubcategory),
          ∃ e : (extend Λ d.obj.i).obj K.obj ≅
              (push Λ r.hom).obj ((extend Λ c.obj.i).obj K.obj),
            (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
                refinementRestriction Λ r K.obj = (openAdjunction Λ c.obj.i).unit.app K.obj ∧
              (φ c d).app K = refinementIso Λ r K.obj e) := by
    classical
    have : IsSeparated X.obj.hom := X.property.1
    have : LocallyOfFiniteType X.obj.hom := X.property.2.1
    have : QuasiCompact X.obj.hom := X.property.2.2
    have : IsSeparated Y.obj.hom := Y.property.1
    have : LocallyOfFiniteType Y.obj.hom := Y.property.2.1
    have : QuasiCompact Y.obj.hom := Y.property.2.2
    have : IsSeparated (X.obj.left ↘ Spec (.of k)) := X.property.1
    have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of k)) := X.property.2.1
    have : QuasiCompact (X.obj.left ↘ Spec (.of k)) := X.property.2.2
    have : IsSeparated (Y.obj.left ↘ Spec (.of k)) := Y.property.1
    have : LocallyOfFiniteType (Y.obj.left ↘ Spec (.of k)) := Y.property.2.1
    have : QuasiCompact (Y.obj.left ↘ Spec (.of k)) := Y.property.2.2
    have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
    have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
    have : QuasiSeparatedSpace X.obj.left := quasiSeparatedSpace_of_quasiSeparated X.obj.hom
    have : QuasiSeparatedSpace Y.obj.left := quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
    have hft : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
      rw [Over.w f.hom]
      infer_instance
    have hsep : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
      rw [Over.w f.hom]
      infer_instance
    have : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp _ Y.obj.hom
    have : IsSeparated f.hom.left := IsSeparated.of_comp _ Y.obj.hom
    have : QuasiCompact f.hom.left :=
      QuasiCompact.of_comp (f := f.hom.left) (g := Y.obj.hom)
    have he := hclosure X
    let J := ObjectProperty.ιOfLE (le_of_eq he.symm)
    obtain ⟨ψ, hiso, hn, hi, hc⟩ :=
      compactification_coherence_cocycle Λ ℓ hadm k f.hom.left
    let φ (c d : Compactifications k f) :
        candidate Λ k (X := X) (Y := Y) (f := f) c ≅
          candidate Λ k (X := X) (Y := Y) (f := f) d :=
      restrict_comparison (le_of_eq he.symm) (ψ ⟨c⟩ ⟨d⟩)
    refine ⟨φ, ?_, ?_, ?_⟩
    · intro c
      apply Iso.ext
      apply NatTrans.ext
      funext K
      exact congrArg (fun e ↦ e.hom.app (J.obj K)) (hi ⟨c⟩)
    · intro c d e
      apply Iso.ext
      apply NatTrans.ext
      funext K
      exact congrArg (fun e ↦ e.hom.app (J.obj K)) (hc ⟨c⟩ ⟨d⟩ ⟨e⟩)
    · intro c d r hb K
      let r' : (⟨c⟩ : Compactification.BoundaryCompactification f.hom.left) ⟶ ⟨d⟩ :=
        ⟨ObjectProperty.homMk r, hb⟩
      let L := J.obj K
      refine exists_iso_eq_of_inv ((φ c d).app K)
        (compactificationRefinementComponent Λ r' K.obj) ?_ ?_
      · obtain ⟨w, hd, ⟨a⟩⟩ := dense_refinement (X := X.obj.left) (Y := Y.obj.left)
          f.hom.left (show Compactification.BoundaryCompactification f.hom.left from ⟨c⟩)
        have hnorm := hn ⟨c⟩ ⟨d⟩ ⟨w, hd⟩ a (a ≫ r') L
        exact cancel_refinement _ _ _ _ (hiso ⟨c⟩ ⟨w, hd⟩ a L) hnorm
          (refinementComponent_comp Λ ℓ hadm r' a L.obj)
      · exact integral_boundaryRefinement_normalization Λ k ℓ hadm f c d r hb K L.property
  -- Assemble the independently normalized families for all morphisms.
  choose φ hi hc hn using @per_morphism
  exact ⟨φ, hi, hc, hn⟩

/-- Normalized comparison maps and their groupoid equations.

Source: blueprint proposition-construction-independence-rf-shriek, common dense refinement
construction, and proposition-construction-independence-rf-shriek, comparison paragraph.
(blueprint: lem-sfb-total-derived-normalized-comparisons).

Proof: specialize localizingClosure_ctf_equals_bc to O_E using the identity
coefficient isomorphism. Write he for the equality Loc(Dctf) = Loc(Dbc). Take the
canonical comparison family from compactification_coherence_cocycle
and restrict its source using he. Identity and cocycle follow componentwise. For a
boundary refinement, choose a dense refinement of its source.
The composite-law for normalized refinement components and cancellation of the dense
component identify the canonical comparison with the inverse refinement component.
The boundary-vanishing theorem makes the localizing refinement map invertible.
Transport its normalization along the canonical comparison between termwise and total
pullback. The open unit and proper counit are transported by the same adjunction
isomorphism; its naturality cancels the transport factors. The derived pushforward
compositor is the conjugate of the total pullback compositor by uniqueness of right
adjoints, so its inverse is precisely pushComp. This gives refinementIso as stated.
The argument allows empty distinguished opens and zero complexes. -/
theorem normalizedComparisons
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    : ∃ φ : Comparisons (Profinite.padicIntegersRingObj ℓ E.val) k,
      (∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactifications k f),
    φ f c c = Iso.refl _) ∧
      (∀ {X Y : Spaces k} (f : X ⟶ Y) (c d e : Compactifications k f),
    φ f c d ≪≫ φ f d e = φ f c e) ∧
      (∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left).FullSubcategory),
      ∃ e : (extend (Profinite.padicIntegersRingObj ℓ E.val) d.obj.i).obj K.obj ≅
          (push (Profinite.padicIntegersRingObj ℓ E.val) r.hom).obj ((extend
            (Profinite.padicIntegersRingObj ℓ E.val) c.obj.i).obj K.obj),
        (openAdjunction (Profinite.padicIntegersRingObj ℓ E.val) d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction (Profinite.padicIntegersRingObj ℓ E.val) r K.obj =
              (openAdjunction (Profinite.padicIntegersRingObj ℓ E.val) c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso (Profinite.padicIntegersRingObj ℓ E.val) r K.obj e) := by
  classical
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  have hclosure (X : Spaces k) :
      localizingClosureProEtale Λ X.obj.left = localizing Λ X.obj.left := by
    have : IsSeparated X.obj.hom := X.property.1
    have : QuasiCompact X.obj.hom := X.property.2.2
    have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
    have : QuasiSeparatedSpace X.obj.left := quasiSeparatedSpace_of_quasiSeparated X.obj.hom
    simpa only [localizingClosureProEtale, localizing, generators] using
      (localizingClosure_ctf_equals_bc ℓ X.obj.left Λ
        (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.2.1
  exact comparisonsForCoefficient Λ k ℓ hadm hclosure

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
