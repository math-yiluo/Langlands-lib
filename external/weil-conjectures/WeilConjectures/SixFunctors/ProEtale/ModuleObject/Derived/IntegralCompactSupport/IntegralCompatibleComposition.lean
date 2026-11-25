/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.NonrationalCompositionSeed
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc

/-! # Coherence portions for integral compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
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
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (k : Type u) [Field k]

private theorem transportComposition
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {I J L : Type*} (F : I → C ⥤ D) (G : J → D ⥤ E) (H : L → C ⥤ E)
    (pf : ∀ c d, F c ≅ F d) (pg : ∀ c d, G c ≅ G d) (ph : ∀ c d, H c ≅ H d)
    (cpf : ∀ c d e X, (pf c d).hom.app X ≫ (pf d e).hom.app X = (pf c e).hom.app X)
    (cpg : ∀ c d e X, (pg c d).hom.app X ≫ (pg d e).hom.app X = (pg c e).hom.app X)
    (cph : ∀ c d e X, (ph c d).hom.app X ≫ (ph d e).hom.app X = (ph c e).hom.app X)
    (i₀ : I) (j₀ : J) (l₀ : L) (β : F i₀ ⋙ G j₀ ≅ H l₀) :
    ∃ α : ∀ i j l, F i ⋙ G j ≅ H l,
      ∀ i j l i' j' l' X,
        (G j).map ((pf i i').hom.app X) ≫
            (pg j j').hom.app ((F i').obj X) ≫ (α i' j' l').hom.app X =
          (α i j l).hom.app X ≫ (ph l l').hom.app X := by
  let α := fun i j l ↦
    Functor.isoWhiskerRight (pf i i₀) (G j) ≪≫
      Functor.isoWhiskerLeft (F i₀) (pg j j₀) ≪≫ β ≪≫ ph l₀ l
  refine ⟨α, ?_⟩
  intro i j l i' j' l' X
  dsimp only [α, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight, Functor.whiskerLeft]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, ← Functor.map_comp_assoc, cpf]
  rw [← Category.assoc ((pg j j').hom.app _), cpg]
  rw [cph]

-- The concrete derived-module functors require more than the default elaboration budget.
/-- Composition for the specified normalized comparison family.

Source: blueprint proposition-composition-base-change-rf-shriek--1, clause (1), the
composition-isomorphism and canonicity paragraphs, specialized in
proposition-construction-independence-rf-shriek step 6. (blueprint:
lem-sfb-total-derived-compatible-composition).

Proof: specialize localizingClosure_ctf_equals_bc to O_E using the identity
coefficient isomorphism. Write he for the equality Loc(Dctf) = Loc(Dbc). Use the
nonrational localizing composition theorem for the integral coefficient O_E,
transported along he. Its refinement compatibility is for the same canonical open
unit and proper counit as hn. Pass through common dense refinements to identify its
comparison family with φ; injectivity of the open adjunction and hn give equality of
both normalized refinement maps. Equivalently take one composition seed and transport
it along φ in all three variables. Naturality of φ moves the f-comparison across the
g-comparison, and the three cocycle equations hc combine the factors. This yields the
simultaneous comparison equation displayed below. Preservation h supplies membership
of the middle object, and fullness keeps all morphisms in the original ambient category.
The construction includes identity maps and empty schemes. -/
theorem compatibleComposition
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (h : Preservation (Profinite.padicIntegersRingObj ℓ E.val) k) (φ : Comparisons
      (Profinite.padicIntegersRingObj ℓ E.val) k)
    (hi : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactifications k f),
    φ f c c = Iso.refl _)
    (hc : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d e : Compactifications k f),
    φ f c d ≪≫ φ f d e = φ f c e)
    (hn : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left).FullSubcategory),
      ∃ e : (extend (Profinite.padicIntegersRingObj ℓ E.val) d.obj.i).obj K.obj ≅
          (push (Profinite.padicIntegersRingObj ℓ E.val) r.hom).obj ((extend
            (Profinite.padicIntegersRingObj ℓ E.val) c.obj.i).obj K.obj),
        (openAdjunction (Profinite.padicIntegersRingObj ℓ E.val) d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction (Profinite.padicIntegersRingObj ℓ E.val) r K.obj =
              (openAdjunction (Profinite.padicIntegersRingObj ℓ E.val) c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso (Profinite.padicIntegersRingObj ℓ E.val) r K.obj e)
    : ∃ μ : Compositions (Profinite.padicIntegersRingObj ℓ E.val) k,
      (∀ {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c c' : Compactifications k f) (d d' : Compactifications k g)
    (e e' : Compactifications k (f ≫ g))
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left).FullSubcategory),
      (image (Profinite.padicIntegersRingObj ℓ E.val) d.obj).map ((φ f c c').hom.app K) ≫
          (φ g d d').hom.app
            ⟨(image (Profinite.padicIntegersRingObj ℓ E.val) c'.obj).obj K.obj, h.maps_localizing
              c' K.obj K.property⟩ ≫
          (μ f g c' d' e').hom.app K =
        (μ f g c d e).hom.app K ≫ (φ (f ≫ g) e e').hom.app K) := by
  classical
  have _identity := @hi
  have _normalization := @hn
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  have closure_eq (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
      localizingClosureProEtale Λ T = localizing Λ T :=
    (localizingClosure_ctf_equals_bc ℓ T Λ
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.2.1
  have perTriple : ∀ {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z),
      ∃ μ : ∀ (c : Compactifications k f) (d : Compactifications k g)
          (e : Compactifications k (f ≫ g)),
          candidate Λ k c ⋙ image Λ d.obj ≅ candidate Λ k e,
        ∀ (c c' : Compactifications k f) (d d' : Compactifications k g)
          (e e' : Compactifications k (f ≫ g))
          (K : (localizing Λ X.obj.left).FullSubcategory),
          (image Λ d.obj).map ((φ f c c').hom.app K) ≫
              (φ g d d').hom.app
                ⟨(image Λ c'.obj).obj K.obj, h.maps_localizing c' K.obj K.property⟩ ≫
              (μ c' d' e').hom.app K =
            (μ c d e).hom.app K ≫ (φ (f ≫ g) e e').hom.app K := by
    intro X Y Z f g
    let : X.obj.left.Over (Spec (.of k)) := ⟨X.obj.hom⟩
    let : Y.obj.left.Over (Spec (.of k)) := ⟨Y.obj.hom⟩
    let : Z.obj.left.Over (Spec (.of k)) := ⟨Z.obj.hom⟩
    have : IsSeparated (X.obj.left ↘ Spec (.of k)) := X.property.1
    have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of k)) := X.property.2.1
    have : QuasiCompact (X.obj.left ↘ Spec (.of k)) := X.property.2.2
    have : IsSeparated (Y.obj.left ↘ Spec (.of k)) := Y.property.1
    have : LocallyOfFiniteType (Y.obj.left ↘ Spec (.of k)) := Y.property.2.1
    have : QuasiCompact (Y.obj.left ↘ Spec (.of k)) := Y.property.2.2
    have : IsSeparated (Z.obj.left ↘ Spec (.of k)) := Z.property.1
    have : LocallyOfFiniteType (Z.obj.left ↘ Spec (.of k)) := Z.property.2.1
    have : QuasiCompact (Z.obj.left ↘ Spec (.of k)) := Z.property.2.2
    have : f.hom.left.IsOver (Spec (.of k)) := ⟨Over.w f.hom⟩
    have : g.hom.left.IsOver (Spec (.of k)) := ⟨Over.w g.hom⟩
    have : CompactSpace X.obj.left :=
      QuasiCompact.compactSpace_of_compactSpace (X.obj.left ↘ Spec (.of k))
    have : CompactSpace Y.obj.left :=
      QuasiCompact.compactSpace_of_compactSpace (Y.obj.left ↘ Spec (.of k))
    have : CompactSpace Z.obj.left :=
      QuasiCompact.compactSpace_of_compactSpace (Z.obj.left ↘ Spec (.of k))
    have : QuasiSeparatedSpace X.obj.left :=
      quasiSeparatedSpace_of_quasiSeparated (X.obj.left ↘ Spec (.of k))
    have : QuasiSeparatedSpace Y.obj.left :=
      quasiSeparatedSpace_of_quasiSeparated (Y.obj.left ↘ Spec (.of k))
    have : QuasiSeparatedSpace Z.obj.left :=
      quasiSeparatedSpace_of_quasiSeparated (Z.obj.left ↘ Spec (.of k))
    have : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
      rw [Over.w]; exact X.property.1
    have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
      rw [Over.w]; exact X.property.2.1
    have : IsSeparated f.hom.left := IsSeparated.of_comp _ Y.obj.hom
    have : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp _ Y.obj.hom
    have : QuasiCompact f.hom.left := quasiCompact_of_compactSpace _
    have : IsSeparated (g.hom.left ≫ Z.obj.hom) := by
      rw [Over.w]; exact Y.property.1
    have : LocallyOfFiniteType (g.hom.left ≫ Z.obj.hom) := by
      rw [Over.w]; exact Y.property.2.1
    have : IsSeparated g.hom.left := IsSeparated.of_comp _ Z.obj.hom
    have : LocallyOfFiniteType g.hom.left := locallyOfFiniteType_of_comp _ Z.obj.hom
    have : QuasiCompact g.hom.left := quasiCompact_of_compactSpace _
    have eX := closure_eq X.obj.left
    have eY := closure_eq Y.obj.left
    have eZ := closure_eq Z.obj.left
    have hf (c : Compactification.BoundaryCompactification f.hom.left)
        (K : Ambient Λ X.obj.left) (hK : localizingClosureProEtale Λ X.obj.left K) :
        localizingClosureProEtale Λ Y.obj.left ((image Λ c.obj.obj).obj K) := by
      rw [eY]
      exact h.maps_localizing (f := f) c.obj K (eX ▸ hK)
    have hg (c : Compactification.BoundaryCompactification g.hom.left)
        (K : Ambient Λ Y.obj.left) (hK : localizingClosureProEtale Λ Y.obj.left K) :
        localizingClosureProEtale Λ Z.obj.left ((image Λ c.obj.obj).obj K) := by
      rw [eZ]
      exact h.maps_localizing (f := g) c.obj K (eY ▸ hK)
    have hgf (c : Compactification.BoundaryCompactification (f.hom.left ≫ g.hom.left))
        (K : Ambient Λ X.obj.left) (hK : localizingClosureProEtale Λ X.obj.left K) :
        localizingClosureProEtale Λ Z.obj.left ((image Λ c.obj.obj).obj K) := by
      rw [eZ]
      exact h.maps_localizing (f := f ≫ g) c.obj K (eX ▸ hK)
    obtain ⟨c₀, d₀, e₀, ⟨β⟩⟩ :=
      exists_nonrationalLocalizingLowerShriekCompositionSeed Λ ℓ
        (Or.inr (Or.inr ⟨E, ⟨Iso.refl _⟩⟩)) k f.hom.left g.hom.left hf hg hgf
    let F := fun c : Compactifications k f ↦
      (localizing Λ Y.obj.left).lift (candidate Λ k c)
        (fun K ↦ h.maps_localizing c K.obj K.property)
    let G := fun d : Compactifications k g ↦ candidate Λ k d
    let H := fun e : Compactifications k (f ≫ g) ↦ candidate Λ k e
    let pf : ∀ c d, F c ≅ F d := fun c d ↦
      NatIso.ofComponents
        (fun K ↦ (localizing Λ Y.obj.left).isoMk ((φ f c d).app K))
        (fun m ↦ (localizing Λ Y.obj.left).ι.map_injective ((φ f c d).hom.naturality m))
    let β' : F c₀.obj ⋙ G d₀.obj ≅ H e₀.obj :=
      NatIso.ofComponents
        (fun K ↦ (localizingClosureProEtale Λ Z.obj.left).ι.mapIso
          (β.app ⟨K.obj, eX.symm ▸ K.property⟩)) (by
          intro K L m
          exact congrArg (fun q ↦ q.hom)
            (β.hom.naturality
              (ObjectProperty.homMk (P := localizingClosureProEtale Λ X.obj.left)
                (X := ⟨K.obj, eX.symm ▸ K.property⟩)
                (Y := ⟨L.obj, eX.symm ▸ L.property⟩) m.hom)))
    have cpf c d e K :
        (pf c d).hom.app K ≫ (pf d e).hom.app K = (pf c e).hom.app K := by
      apply (localizing Λ Y.obj.left).ι.map_injective
      exact congrArg (fun q ↦ q.hom.app K) (hc f c d e)
    have cpg c d e K :
        (φ g c d).hom.app K ≫ (φ g d e).hom.app K = (φ g c e).hom.app K :=
      congrArg (fun q ↦ q.hom.app K) (hc g c d e)
    have cph c d e K :
        (φ (f ≫ g) c d).hom.app K ≫ (φ (f ≫ g) d e).hom.app K =
          (φ (f ≫ g) c e).hom.app K :=
      congrArg (fun q ↦ q.hom.app K) (hc (f ≫ g) c d e)
    obtain ⟨α, hα⟩ := transportComposition F G H pf (φ g) (φ (f ≫ g)) cpf cpg cph
      c₀.obj d₀.obj e₀.obj β'
    refine ⟨α, ?_⟩
    intro c c' d d' e e' K
    exact hα c d e c' d' e' K
  choose μ hμ using @perTriple
  refine ⟨fun {X Y Z} f g ↦ @μ X Y Z f g, ?_⟩
  intro X Y Z f g c c' d d' e e' K
  exact @hμ X Y Z f g c c' d d' e e' K

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
