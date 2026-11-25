/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.BrownExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenPullbackGenerators
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.Compactification.BoundaryRefinement
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenCompactSupportExchange
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing

/-!
# Open restriction of the Brown exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-sf-mate,
proposition-composition-open-restriction-compactifications-f, clauses (1)--(3) and proof
(blueprint: proposition-composition-open-restriction-compactifications-f).

The exceptional functors are arbitrary right adjoints of the recorded compactification
lower shrieks, hence include the compactification-independent Brown adjoints. All comparison
isomorphisms below are characterized by explicit adjunction equations. The target equation
uses the ordinary open base-change mate, defined before any invertibility assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem conjugate_hom
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁)
    (T : C) (B : D) (f : T ⟶ R₁.obj B) :
    f ≫ ((conjugateIsoEquiv a₁ a₂ e).hom.app B) =
      a₂.homEquiv T B (e.hom.app T ≫ (a₁.homEquiv T B).symm f) := by
  apply (a₂.homEquiv T B).symm.injective
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc]
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
  rw [← e.hom.naturality_assoc]

private theorem normalized_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E : A ⥤ B} {R : B ⥤ A} {F : B ⥤ D} {G : D ⥤ B}
    {Q : A ⥤ C} {J : C ⥤ A} {V : C ⥤ D} {W : D ⥤ C}
    (ae : E ⊣ R) (af : F ⊣ G) (aq : Q ⊣ J) (av : V ⊣ W)
    (β : Q ⋙ V ≅ E ⋙ F)
    (T : ∀ M, W.obj (F.obj (E.obj M)) ⟶ Q.obj M)
    (hβ : ∀ M, T M ≫ av.unit.app (Q.obj M) ≫ W.map (β.hom.app M) = 𝟙 _)
    (M : A) (N : D) (b : M ⟶ R.obj (G.obj N)) :
    T M ≫ (aq.homEquiv M (W.obj N)).symm
        (b ≫ (conjugateIsoEquiv (ae.comp af) (aq.comp av) β).hom.app N) =
      W.map ((af.homEquiv (E.obj M) N).symm ((ae.homEquiv M (G.obj N)).symm b)) := by
  rw [conjugate_hom (ae.comp af) (aq.comp av)]
  simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  change T M ≫ (aq.homEquiv M (W.obj N)).symm
    ((aq.homEquiv M (W.obj N)) ((av.homEquiv (Q.obj M) N)
      (β.hom.app M ≫ (af.homEquiv (E.obj M) N).symm
        ((ae.homEquiv M (G.obj N)).symm b)))) = _
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_unit, W.map_comp]
  have hb := hβ M
  rw [← Category.assoc] at hb
  rw [← Category.assoc, ← Category.assoc, hb, Category.id_comp]

/-- Open extension is left adjoint to exact restriction on precisely Loc(Dctf). The Hom
bijection is the restriction of the existing termwise open adjunction. Every Brown right
adjoint is identified with restriction by the unique counit-compatible isomorphism.
Source: blueprint proposition-composition-open-restriction-compactifications-f (1)
(blueprint: proposition-composition-open-restriction-compactifications-f).

Proof: The existing exact derived open adjunction already supplies the ambient Hom
bijections. Obtain open-extension preservation from openImmersionLowerShriek_localizing.
For pullback, use openPullback_generators and the defining intersection of the localizing
closure: inverse images of the replete triangulated sum-closed candidates are again such
candidates, since exact termwise pullback is also a left adjoint. Restrict the ambient
adjunction using restrictFullyFaithful, retaining its Hom formula. Transport extension
preservation and the adjunction along mateOpenTrivialLowerShriek for (j,id). The canonical
rightAdjointUniq has precisely the displayed counit equation; injectivity of the inverse
Hom equivalence proves that it is the only such isomorphism. -/
theorem mateOpenImmersion
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    ∃ (he : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
          localizingClosureProEtale Λ X
            ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj))
      (hs : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj))
      (ht : ∀ K, localizingClosureProEtale Λ U K → localizingClosureProEtale Λ X
        ((rightDerivedLowerShriekOfCompactification Λ
          (Compactification.ofIsOpenImmersion j)).obj K))
      (adj : mateOpenExtension Λ j he ⊣ mateOpenPullback Λ j hs),
      (∀ (M : (localizingClosureProEtale Λ U).FullSubcategory)
        (N : (localizingClosureProEtale Λ X).FullSubcategory)
        (b : (mateOpenExtension Λ j he).obj M ⟶ N),
        (adj.homEquiv M N b).hom =
          (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv M.obj N.obj b.hom) ∧
      ∀ (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory)
        (adjG : localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j) ht ⊣ G),
        ∃! e : G ≅ mateOpenPullback Λ j hs,
          ∀ N,
            ((localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j) ht).map
                (e.hom.app N)).hom ≫
              (mateOpenTrivialLowerShriek Λ j).hom.app
                ((mateOpenPullback Λ j hs).obj N).obj ≫
              (adj.counit.app N).hom = (adjG.counit.app N).hom := by
  let : U.Over (Spec (.of k)) := ⟨j ≫ (X ↘ Spec (.of k))⟩
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ (X ↘ Spec (.of k))))
  have : QuasiCompact (U ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (j ≫ (X ↘ Spec (.of k))))
  have : IsSeparated (U ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (j ≫ (X ↘ Spec (.of k))))
  obtain ⟨_, _, he, _⟩ :=
    (openImmersionLowerShriek_localizing ℓ k p _hp _hpℓ Λ _hΛ j).2.2
  have hs : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj) := by
    let F := (upperStar Λ j).mapDerivedCategory
    let adjF := (derivedUpperStarLowerStarAdjunction Λ j).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ j)
    have : F.IsLeftAdjoint := adjF.isLeftAdjoint
    intro K P hP hS
    let := hP.1
    let := hP.2.1
    have hR : IsLocalizingSubcategory (P.inverseImage F) := by
      refine ⟨inferInstance, inferInstance, ?_⟩
      intro I D hD hobj
      let := hD
      have : PreservesColimit D F :=
        adjF.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
      have : HasColimit (D ⋙ F) := inferInstance
      exact P.prop_of_iso (preservesColimitIso F D).symm
        (hP.prop_colimit (D ⋙ F) inferInstance hobj)
    exact K.property (P.inverseImage F) hR (fun L hL ↦
      hS _ (openPullback_generators Λ ℓ k p _hp _hpℓ _hΛ j ⟨L, hL⟩))
  have ht : ∀ K, localizingClosureProEtale Λ U K → localizingClosureProEtale Λ X
      ((rightDerivedLowerShriekOfCompactification Λ
        (Compactification.ofIsOpenImmersion j)).obj K) := by
    intro K hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso ((mateOpenTrivialLowerShriek Λ j).app K).symm
      (he ⟨K, hK⟩ P hP hS)
  let adj : mateOpenExtension Λ j he ⊣ mateOpenPullback Λ j hs :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).restrictFullyFaithful
      (localizingClosureProEtale Λ U).fullyFaithfulι
      (localizingClosureProEtale Λ X).fullyFaithfulι (Iso.refl _) (Iso.refl _)
  have hadj : ∀ (M : (localizingClosureProEtale Λ U).FullSubcategory)
      (N : (localizingClosureProEtale Λ X).FullSubcategory)
      (b : (mateOpenExtension Λ j he).obj M ⟶ N),
      (adj.homEquiv M N b).hom =
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv M.obj N.obj
          b.hom := by
    intro M N b
    dsimp only [adj]
    rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
    simp [Adjunction.homEquiv_apply]
  let t : localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j) ht ≅
      mateOpenExtension Λ j he := NatIso.ofComponents
    (fun M ↦ (localizingClosureProEtale Λ X).isoMk
      ((mateOpenTrivialLowerShriek Λ j).app M.obj))
    (by intro M N b; ext; exact (mateOpenTrivialLowerShriek Λ j).hom.naturality b.hom)
  let adjT := adj.ofNatIsoLeft t.symm
  refine ⟨he, hs, ht, adj, hadj, ?_⟩
  intro G adjG
  refine ⟨adjG.rightAdjointUniq adjT, ?_, ?_⟩
  · intro N
    exact congrArg (fun b ↦ b.hom) (adjG.rightAdjointUniq_hom_app_counit adjT N)
  · intro e heq
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (adjT.homEquiv _ N).symm.injective
    exact (show _ = (adjG.counit.app N) by
      ext
      exact heq N).trans
        (adjG.homEquiv_symm_rightAdjointUniq_hom_app adjT N).symm

end AlgebraicGeometry.ProEtale.CondensedRing
