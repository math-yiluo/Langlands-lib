/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Coefficient restriction without an invertibility hypothesis

Source: Stacks Project, Tags 00Y0 and 03CO.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProEt
namespace WeilConjectures

private def constantComparison {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{max u (t + 1)}) :
    (clopenRingRestriction j).obj
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (topology X) CommRingCat.{max u (t + 1)}).obj A)) ≅
      (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (topology Y) CommRingCat.{max u (t + 1)}).obj A) := by
  let F : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact (sheafCompose (topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso
    ((F.pushforwardContinuousSheafificationCompatibility CommRingCat.{max u (t + 1)} (topology Y)
        (topology X)).app ((Functor.const X.ProEtᵒᵖ).obj A)).symm

private theorem constantComparison_sections {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{max u (t + 1)}) (W : Y.ProEt) :
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
        ((toSheafify (topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
        (constantComparison.{t, u} j A).hom.hom.app (op W) =
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
        ((toSheafify (topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app (op W)) := by
  let F : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  have h := congrArg (fun f ↦ f.app (op W))
    (F.toSheafify_pullbackSheafificationCompatibility CommRingCat.{max u (t + 1)} (topology Y)
      (topology X) ((Functor.const X.ProEtᵒᵖ).obj A))
  let c := (F.pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (topology Y) (topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj A)
  change (forget₂ CommRingCat RingCat).map
      ((toSheafify (topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (F.op.obj (op W)) ≫
        c.inv.hom.app (op W)) = _
  apply (forget₂ CommRingCat RingCat).congr_map
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  apply (cancel_mono (c.hom.hom.app (op W))).mp
  have hc : c.inv.hom.app (op W) ≫ c.hom.hom.app (op W) = 𝟙 _ :=
    congrArg (fun f ↦ f.hom.app (op W)) c.inv_hom_id
  rw [Category.assoc, hc]
  erw [Category.comp_id]
  exact h.symm

private theorem constantComparison_naturality {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) :
    (clopenRingRestriction j).map
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (topology X) CommRingCat.{max u (t + 1)}).map f)) ≫
        (constantComparison.{t, u} j B).hom =
      (constantComparison.{t, u} j A).hom ≫
        (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (topology Y) CommRingCat.{max u (t + 1)}).map f) := by
  let F : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact (sheafCompose (topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).congr_map
    ((F.pushforwardContinuousSheafificationCompatibility CommRingCat.{max u (t + 1)} (topology Y)
      (topology X)).inv.naturality ((Functor.const X.ProEtᵒᵖ).map f))

private theorem ringRestriction_preservesLimits {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    PreservesLimitsOfShape ℕᵒᵖ (clopenRingRestriction.{t, max u (t + 1)} j) := by
  let F : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : PreservesLimitsOfShape ℕᵒᵖ
      (clopenRingRestriction.{t, max u (t + 1)} j ⋙
        sheafToPresheaf (topology Y) RingCat.{max u (t + 1)}) := by
    change PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (topology X) RingCat.{max u (t + 1)} ⋙
        (Functor.whiskeringLeft Y.ProEtᵒᵖ X.ProEtᵒᵖ RingCat.{max u (t + 1)}).obj F.op)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (topology Y) RingCat.{max u (t + 1)})

private theorem restriction_exact {T : Scheme.{t}} (U : T.Opens)
    (R : Sheaf (ProEt.topology T) RingCat.{max u (t + 1)})
    (S : Sheaf (ProEt.topology U.toScheme) RingCat.{max u (t + 1)})
    (c : S ≅ sfClopenRingRestriction U R) :
    (sfClopenModuleRestriction U R S c).Additive ∧
      PreservesFiniteLimits (sfClopenModuleRestriction U R S c) ∧
      PreservesFiniteColimits (sfClopenModuleRestriction U R S c) := by
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralCoefficientAbSheafify.{t, u} U.toScheme
  let := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  have : (sfClopenSiteInclusion U).IsCocontinuous (topology U.toScheme)
      (topology T) := isCocontinuous_overMap (inferInstance : WeaklyEtale U.ι)
  let F := sfClopenModuleRestriction U R S c
  let G := SheafOfModules.toSheaf S
  let H := (sfClopenSiteInclusion U).sheafPushforwardContinuous
    AddCommGrpCat.{max u (t + 1)} (ProEt.topology U.toScheme) (ProEt.topology T)
  have : F.Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  let e : F ⋙ G ≅ SheafOfModules.toSheaf R ⋙ H := Iso.refl _
  have : PreservesFiniteLimits H := by
    have : PreservesFiniteLimits (H ⋙ sheafToPresheaf _ _) := by
      change PreservesFiniteLimits
        (sheafToPresheaf _ _ ⋙
          (Functor.whiskeringLeft U.toScheme.ProEtᵒᵖ T.ProEtᵒᵖ
            AddCommGrpCat.{max u (t + 1)}).obj (sfClopenSiteInclusion U).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have : PreservesFiniteLimits (F ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F G
  have : H.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat f).mpr hf
    have : Sheaf.IsLocallySurjective (H.map f) :=
      Presheaf.isLocallySurjective_whisker (topology U.toScheme) (topology T)
        (sfClopenSiteInclusion U) f.hom
    exact Sheaf.epi_of_isLocallySurjective (H.map f)
  have : F.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    apply G.epi_of_epi_map
    exact inferInstanceAs (Epi (H.map ((SheafOfModules.toSheaf R).map f)))
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  exact ⟨inferInstance, inferInstance, Functor.preservesFiniteColimits_of_preservesHomology F⟩

/-- Canonical finite and completed coefficient comparisons, with exact module
restriction, require no invertibility of the coefficient prime on the scheme.

Source: Stacks Project, Tags 00Y0, 03CO and 03DH
(blueprint: lem-sf-clopen-coefficient-comparison).
Proof: composition into an open subscheme is continuous and cocontinuous, so its
precomposition commutes with sheafification. Apply that comparison to each constant
finite quotient ring; the sheafification units give the constant-section normalization.
Naturality in the quotient homomorphisms gives all transition squares. Precomposition
preserves sectionwise limits, so the inverse limit of the finite comparisons gives the
completion comparison and its projection squares. The underlying abelian-sheaf functor
of module restriction is the same precomposition, even after scalar transport. It
preserves kernels and locally surjective maps, hence is additive and exact. This applies
to the completed ring and every finite quotient, including empty opens. -/
theorem sf_clopen_coefficient_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens) :
    Nonempty (SfClopenCoefficientRestriction l E T U) := by
  let finite (n : ℕ) := (constantComparison.{t, u} U.ι
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).symm
  have ht (n : ℕ) :
      (finite (n + 1)).hom ≫ ((sfClopenSiteInclusion U).sheafPushforwardContinuous _ _ _).map
          (integralCoefficientSheafTransition l E T n) =
        integralCoefficientSheafTransition l E U.toScheme n ≫ (finite n).hom := by
    have h := constantComparison_naturality U.ι
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))
    change _ ≫ (finite n).inv = (finite (n + 1)).inv ≫ _ at h
    have hpre := congrArg (fun f ↦ (finite (n + 1)).hom ≫ f) h
    have hcancel : (finite (n + 1)).hom ≫
        ((sfClopenSiteInclusion U).sheafPushforwardContinuous _ _ _).map
          (integralCoefficientSheafTransition l E T n) ≫ (finite n).inv =
        integralCoefficientSheafTransition l E U.toScheme n := by
      simpa only [Category.assoc, Iso.hom_inv_id_assoc,
        integralCoefficientSheafTransition, sfClopenSiteInclusion, clopenRingRestriction] using hpre
    have hpost := congrArg (fun f ↦ f ≫ (finite n).hom) hcancel
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hpost
  let fn : integralCoefficientSheafSystem l E U.toScheme ⟶
      integralCoefficientSheafSystem l E T ⋙ clopenRingRestriction U.ι :=
    NatTrans.ofOpSequence (fun n ↦ (finite n).hom) (by
      intro n
      simpa only [Functor.comp_map, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using (ht n).symm)
  have (n : ℕᵒᵖ) : IsIso (fn.app n) := by
    change IsIso (finite n.unop).hom
    infer_instance
  have : IsIso fn := NatIso.isIso_of_isIso_app _
  let f := asIso fn
  have : PreservesLimitsOfShape ℕᵒᵖ (clopenRingRestriction.{t, max u (t + 1)} U.ι) :=
    ringRestriction_preservesLimits U.ι
  let completed := HasLimit.isoOfNatIso f ≪≫
    (preservesLimitIso (clopenRingRestriction U.ι)
      (integralCoefficientSheafSystem l E T)).symm
  refine ⟨{
    finite := finite
    finite_constant := ?_
    completion := completed
    projection := ?_
    transition := ht
    additive := (restriction_exact U _ _ completed).1
    limits := (restriction_exact U _ _ completed).2.1
    colimits := (restriction_exact U _ _ completed).2.2
    finite_additive := fun n ↦ (restriction_exact U _ _ (finite n)).1
    finite_limits := fun n ↦ (restriction_exact U _ _ (finite n)).2.1
    finite_colimits := fun n ↦ (restriction_exact U _ _ (finite n)).2.2 }⟩
  · intro n V x
    have h := constantComparison_sections U.ι
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) V
    let c := constantComparison.{t, u} U.ι
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    have h' := congrArg (fun g ↦ g x) h
    have hc := congrArg (fun g ↦ g.hom.app (op V)) c.inv_hom_id
    have hcx := congrArg (fun g ↦ g
      ((toSheafify (topology U.toScheme) ((Functor.const U.toScheme.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op V) x)) hc
    apply (ConcreteCategory.bijective_of_isIso (c.hom.hom.app (op V))).1
    exact hcx.trans h'.symm
  · intro n
    simp [completed, Category.assoc, HasLimit.isoOfNatIso_hom_π, f, fn]

end WeilConjectures
