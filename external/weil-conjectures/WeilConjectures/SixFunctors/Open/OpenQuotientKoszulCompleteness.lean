/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.CategoryTheory.Limits.HasLimits

import WeilConjectures.SixFunctors.Open.OpenDvrAugmentedTowerComparison
import WeilConjectures.SixFunctors.Open.OpenDvrIntrinsicCriterion
import WeilConjectures.SixFunctors.Open.OpenDvrIntrinsicOpenTransport

/-! # DVR quotient, Koszul and open completeness assembly -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section FiniteCoefficients

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

private def dvrFiniteComparison :
    adicLisseRing T Λ ≅ AdicCoefficients.finiteRingPresentation T Λ :=
  let := CompletedConstantReduction.constantComparison_isIso T Λ
  (adicLisseForget T).mapIso (asIso (AdicCoefficients.constantComparison T Λ)) ≪≫
    AdicCoefficients.finiteRingComparison T Λ

private theorem dvrFiniteComparison_constants :
    letI : TopologicalSpace Λ := ⊥
    letI : DiscreteTopology Λ := ⟨rfl⟩
    adicLisseConstantUnit T Λ ≫ (dvrFiniteComparison T Λ).hom.hom =
      ProEtale.finiteCoefficientScalarMap T Λ := by
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  dsimp only [dvrFiniteComparison, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  change Functor.whiskerRight
    (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)))
      (forget₂ CommRingCat RingCat) ≫
    (Functor.whiskerRight (AdicCoefficients.constantComparison T Λ).hom
      (forget₂ CommRingCat RingCat) ≫ _) = _
  rw [← Category.assoc, ← Functor.whiskerRight_comp]
  change Functor.whiskerRight
    (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)) ≫
      sheafifyMap (ProEt.topology T) (AdicCoefficients.constants T Λ))
    (forget₂ CommRingCat RingCat) ≫ _ = _
  rw [← toSheafify_naturality, Functor.whiskerRight_comp, Category.assoc]
  change _ ≫ (Functor.whiskerRight
    (toSheafify (ProEt.topology T) (AdicCoefficients.functionPresheaf T Λ))
    (forget₂ CommRingCat RingCat) ≫
    ((AdicCoefficients.finiteRingComparison_exists T Λ).choose).hom) = _
  rw [(AdicCoefficients.finiteRingComparison_exists T Λ).choose_spec.1.2]
  rfl

end FiniteCoefficients

attribute [local irreducible] dvrFiniteComparison

private theorem dvrConstants_hom_ext (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    {S : Sheaf (ProEt.topology T) RingCat.{u + 1}}
    (f g : adicLisseRing T Λ ⟶ S)
    (h : adicLisseConstantUnit T Λ ≫ f.hom = adicLisseConstantUnit T Λ ≫ g.hom) :
    f = g := by
  ext U x
  have hs := (isSheaf_iff_isSheaf_of_type (ProEt.topology T)
    (S.obj ⋙ CategoryTheory.forget RingCat.{u + 1})).1
      ((sheafCompose (ProEt.topology T) (CategoryTheory.forget RingCat.{u + 1})).obj S).property
  apply (hs.isSeparated _
    (Presheaf.imageSieve_mem (ProEt.topology T) (adicLisseConstantUnit T Λ) x)).ext
  rintro V k ⟨a, ha⟩
  change S.obj.map k.op (f.hom.app U x) = S.obj.map k.op (g.hom.app U x)
  have hfn := ConcreteCategory.congr_hom (f.hom.naturality k.op) x
  have hgn := ConcreteCategory.congr_hom (g.hom.naturality k.op) x
  change f.hom.app (op V) ((adicLisseRing T Λ).obj.map k.op x) =
    S.obj.map k.op (f.hom.app U x) at hfn
  change g.hom.app (op V) ((adicLisseRing T Λ).obj.map k.op x) =
    S.obj.map k.op (g.hom.app U x) at hgn
  rw [← hfn, ← hgn, ← ha]
  exact ConcreteCategory.congr_hom (congr_app h (op V)) a

private theorem dvrFiniteComparison_naturality (T : Scheme.{u})
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ']
    (φ : Λ →+* Λ')
    (f : AdicCoefficients.finiteRingPresentation T Λ ⟶
      AdicCoefficients.finiteRingPresentation T Λ')
    (hf : Functor.whiskerRight ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
        (adicLisseConstantUnit T Λ' ≫ (dvrFiniteComparison T Λ').hom.hom) =
      (adicLisseConstantUnit T Λ ≫ (dvrFiniteComparison T Λ).hom.hom) ≫ f.hom) :
    (adicLisseForget T).map ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ)) ≫ (dvrFiniteComparison T Λ').hom =
      (dvrFiniteComparison T Λ).hom ≫ f := by
  apply dvrConstants_hom_ext T Λ
  have hη := congrArg
    (fun f ↦ Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (toSheafify_naturality (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ)))
  rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp] at hη
  change (Functor.whiskerRight
      (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
      Functor.whiskerRight
        (sheafifyMap (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) ≫ _ = _
  rw [← hη, Category.assoc]
  exact hf

private def dvrRestrictCancel {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) RingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : T.ProEtᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private def dvrRestrictEquivalence {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) RingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
  CategoryTheory.Equivalence.mk
    (SheafOfModules.restrictScalars e.hom) (SheafOfModules.restrictScalars e.inv)
    (dvrRestrictCancel e.inv e.hom e.inv_hom_id).symm
    (dvrRestrictCancel e.hom e.inv e.hom_inv_id)

private theorem dvrCoefficientModel_exists
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (T : Scheme.{u}) : Nonempty (OpenDvrCoefficientModel l E d T) := by
  rcases d with ⟨⟨I, hn, hg, ht, hp⟩, hf⟩
  dsimp only at hd
  subst I
  let d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E) :=
    { ideal := Ideal.span {Padic.coefficientExtensionUniformizer l E}
      noetherian := hn
      finitelyGenerated := hg
      quotientTorsion := ht
      quotientPerfect := hp
      quotientFinite := hf }
  let (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) := hf n
  let c (n : ℕ) : integralCoefficientSheaf.{u, u} l E T n ≅
      completedAdicFiniteRing T d n :=
    dvrFiniteComparison T (completedAdicQuotient d n)
  have hc (n : ℕ) : integralCoefficientSheafTransition.{u, u} l E T n ≫ (c n).hom =
      (c (n + 1)).hom ≫ completedAdicFiniteStep T d n := by
    let : TopologicalSpace (completedAdicQuotient d n) := ⊥
    let : DiscreteTopology (completedAdicQuotient d n) := ⟨rfl⟩
    let : TopologicalSpace (completedAdicQuotient d (n + 1)) := ⊥
    let : DiscreteTopology (completedAdicQuotient d (n + 1)) := ⟨rfl⟩
    apply dvrFiniteComparison_naturality T
      (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1)) :
        completedAdicQuotient d (n + 1) →+* completedAdicQuotient d n)
    rw [dvrFiniteComparison_constants, dvrFiniteComparison_constants]
    change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
    unfold completedAdicFiniteStep
    rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc]
    have hconst : Functor.whiskerRight
        ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom
          (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1)) :
            completedAdicQuotient d (n + 1) →+* completedAdicQuotient d n)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
          ProEtale.finiteCoefficientConstants T (completedAdicQuotient d n) =
        ProEtale.finiteCoefficientConstants T (completedAdicQuotient d (n + 1)) ≫
          completedAdicFinitePresheafStep T d n := by
      ext U a
      rfl
    rw [hconst, Category.assoc]
  let ec : integralCoefficientSheafSystem.{u, u} l E T ⟶ completedAdicRingSystem T d :=
    NatTrans.ofOpSequence (fun n ↦ (c n).hom) (by
      intro n
      simpa only [integralCoefficientSheafSystem, completedAdicRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using hc n)
  let e : integralCoefficientSheafSystem.{u, u} l E T ≅ completedAdicRingSystem T d :=
    NatIso.ofComponents (fun n ↦ c n.unop) (fun f ↦ ec.naturality f)
  let er : completedAdicRing T d ≅ completedIntegralCoefficientSheafUnrestricted.{u, u} l E T :=
    (lim.mapIso e).symm
  let F := sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let eC : completedAdicCommRing T d ≅
      completedIntegralCommRingSheafUnrestricted.{u, u} l E T :=
    F.preimageIso er
  let m := dvrRestrictEquivalence er
  refine ⟨{ finite := c
            finite_constants := ?_
            finite_transition := hc
            completed := eC
            completed_projection := ?_
            modules := m
            modules_functor := ?_
            additive := by
              change (SheafOfModules.restrictScalars er.hom).Additive
              infer_instance
            inverse_additive := by
              change (SheafOfModules.restrictScalars er.inv).Additive
              infer_instance }⟩
  · intro n V a
    exact ConcreteCategory.congr_hom
      (congr_app (dvrFiniteComparison_constants T (completedAdicQuotient d n)) V)
        (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a))
  · intro n
    change F.map eC.hom ≫ limit.π _ (op n) ≫ (c n).hom = limit.π _ (op n)
    change F.map (F.preimage (X := completedAdicCommRing T d)
        (Y := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) er.hom) ≫ _ = _
    rw [Functor.map_preimage]
    change (lim.mapIso e).inv ≫ limit.π _ (op n) ≫ e.hom.app (op n) = _
    rw [← limMap_π]
    exact Iso.inv_hom_id_assoc (lim.mapIso e) _
  · change SheafOfModules.restrictScalars er.hom =
      SheafOfModules.restrictScalars (F.map (F.preimage (X := completedAdicCommRing T d)
        (Y := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) er.hom))
    rw [Functor.map_preimage]

private def dvrConstantOpenIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] :
    SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of Λ)) ≅
      (constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).obj (CommRingCat.of Λ) := by
  let G : U.ProEt ⥤ X.ProEt := proEtaleOpenComposition j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    SheafOfModules.OpenTensorNormalization.openInclusion_continuous .ordinary j
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact ((G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))).symm

private theorem dvrConstantOpenIso_constants {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type (u + 1)) [CommRing Λ]
    (V : U.ProEtᵒᵖ) (a : Λ) :
    (dvrConstantOpenIso j Λ).hom.hom.app V
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))).app
          ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj V) a) =
      (toSheafify (ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of Λ))).app V a := by
  let G : U.ProEt ⥤ X.ProEt := proEtaleOpenComposition j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    SheafOfModules.OpenTensorNormalization.openInclusion_continuous .ordinary j
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  have h := G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))
  have h' := ConcreteCategory.congr_hom (congr_app h V) a
  apply (ConcreteCategory.bijective_of_isIso
    ((dvrConstantOpenIso j Λ).inv.hom.app V)).1
  change ((dvrConstantOpenIso j Λ).hom.hom.app V ≫
    (dvrConstantOpenIso j Λ).inv.hom.app V) _ = _
  rw [show (dvrConstantOpenIso j Λ).hom.hom.app V ≫
      (dvrConstantOpenIso j Λ).inv.hom.app V = 𝟙 _ from
    congr_app (congrArg (fun f ↦ f.hom) (dvrConstantOpenIso j Λ).hom_inv_id) V]
  change _ = ((G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology X)).hom.app
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))).hom.app V _
  exact h'.symm

private theorem dvrConstantOpenIso_naturality {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ']
    (φ : Λ →+* Λ') :
    letI : (SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).IsContinuous
        (ProEt.topology U) (ProEt.topology X) :=
      SheafOfModules.OpenTensorNormalization.openInclusion_continuous .ordinary j
    ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j
      ).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom φ)) ≫ (dvrConstantOpenIso j Λ').hom =
      (dvrConstantOpenIso j Λ).hom ≫
        (constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ) := by
  let G : U.ProEt ⥤ X.ProEt := proEtaleOpenComposition j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    SheafOfModules.OpenTensorNormalization.openInclusion_continuous .ordinary j
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact (G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology X)).inv.naturality
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom φ))

private theorem dvrOpenModel_exists {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : Nonempty (OpenDvrOpenModel l E j) := by
  let G : U.ProEt ⥤ X.ProEt := proEtaleOpenComposition j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    SheafOfModules.OpenTensorNormalization.openInclusion_continuous .ordinary j
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let P := G.sheafPushforwardContinuous RingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology X)
  let F := sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let c (n : ℕ) := dvrConstantOpenIso j
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let cr (n : ℕ) : P.obj (integralCoefficientSheaf.{u, u} l E X n) ≅
      integralCoefficientSheaf.{u, u} l E U n := F.mapIso (c n)
  have hcr (n : ℕ) : P.map (integralCoefficientSheafTransition.{u, u} l E X n) ≫
      (cr n).hom = (cr (n + 1)).hom ≫ integralCoefficientSheafTransition.{u, u} l E U n := by
    exact congrArg F.map (dvrConstantOpenIso_naturality j
      (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1)) :
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2)) →+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let ec : integralCoefficientSheafSystem.{u, u} l E X ⋙ P ⟶
      integralCoefficientSheafSystem.{u, u} l E U :=
    NatTrans.ofOpSequence (fun n ↦ (cr n).hom) (by
      intro n
      simpa only [integralCoefficientSheafSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ] using hcr n)
  let e : integralCoefficientSheafSystem.{u, u} l E X ⋙ P ≅
      integralCoefficientSheafSystem.{u, u} l E U :=
    NatIso.ofComponents (fun n ↦ cr n.unop) (fun f ↦ ec.naturality f)
  let er := preservesLimitIso P (integralCoefficientSheafSystem.{u, u} l E X) ≪≫
    lim.mapIso e
  let eC : SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) ≅
      completedIntegralCommRingSheafUnrestricted.{u, u} l E U := F.preimageIso er
  let m := dvrRestrictEquivalence (F.mapIso eC)
  obtain ⟨ext⟩ := SheafOfModules.OpenTensorNormalization.ordinaryOpenExtension_exists j
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
  refine ⟨{ finite := fun n ↦ (sheafToPresheaf _ CommRingCat.{u + 1}).mapIso (c n)
            finite_constants := ?_
            ring := eC
            ring_projection := ?_
            modules := m
            modules_functor := rfl
            additive := ?_
            inverse_additive := ?_
            extension := ext }⟩
  · intro n V a
    exact dvrConstantOpenIso_constants j _ V a
  · intro n
    apply ((Functor.whiskeringRight _ _ _).obj
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
    change (sheafToPresheaf _ RingCat.{u + 1}).map
        (P.map (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)) ≫
          (cr n).hom) = _
    have her : F.map eC.hom = er.hom := by
      exact Functor.map_preimage _ _
    change _ = (sheafToPresheaf _ RingCat.{u + 1}).map
      (F.map eC.hom ≫ limit.π (integralCoefficientSheafSystem.{u, u} l E U) (op n))
    rw [her]
    congr 1
    change _ = (preservesLimitIso P _).hom ≫
      limMap e.hom ≫ limit.π _ (op n)
    rw [limMap_π, ← Category.assoc, preservesLimitIso_hom_π]
    rfl
  · change (SheafOfModules.restrictScalars (F.map eC.hom)).Additive
    infer_instance
  · change (SheafOfModules.restrictScalars (F.map eC.inv)).Additive
    infer_instance

private theorem openDvrUniformizer_ne_zero :
    Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro hz
  apply hm
  rw [← hgen, hz, Ideal.span_singleton_eq_bot]

private theorem openDvrResolution_properties (n : ℕ) :
    ∃ f : openDvrResolution l E n ⟶
        (CochainComplex.singleFunctor (ModuleCat (Padic.coefficientExtensionIntegers l E))
          0).obj (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionRing l E (n + 1))),
      QuasiIso f ∧
      (openDvrResolution l E n).IsStrictlyGE (-1) ∧
      (openDvrResolution l E n).IsStrictlyLE 0 ∧
      (∀ i : ℤ, Module.Free (Padic.coefficientExtensionIntegers l E)
          ((openDvrResolution l E n).X i) ∧
        Module.Projective (Padic.coefficientExtensionIntegers l E)
          ((openDvrResolution l E n).X i) ∧
        Module.Finite (Padic.coefficientExtensionIntegers l E)
          ((openDvrResolution l E n).X i)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let a : R := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
  let I := Padic.coefficientExtensionIdeal l E (n + 1)
  let f : ModuleCat.of R R ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom ((LinearMap.lsmul R R) a)
  let q : ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ I) := ModuleCat.ofHom I.mkQ
  have hw : f ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Ideal.Quotient.mk I (a * x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hI : I = Ideal.span ({a} : Set R) := Ideal.span_singleton_pow _ _
    rw [hI]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a))
  let S := ShortComplex.mk f q hw
  have hS : S.ShortExact := by
    have : Mono f := (ModuleCat.mono_iff_injective f).2
      (mul_right_injective₀ (pow_ne_zero _ (openDvrUniformizer_ne_zero l E)))
    have : Epi q := (ModuleCat.epi_iff_surjective q).2 I.mkQ_surjective
    refine { exact := ?_ }
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change Ideal.Quotient.mk I x = 0 at hx
    have hx' := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [show I = Ideal.span ({a} : Set R) from Ideal.span_singleton_pow _ _] at hx'
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx'
    exact ⟨y, hy.symm⟩
  let F := CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)
  have : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single (ModuleCat R) (.up ℤ) 0))
  have : PreservesFiniteColimits F :=
    inferInstanceAs
      (PreservesFiniteColimits (HomologicalComplex.single (ModuleCat R) (.up ℤ) 0))
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  refine ⟨CochainComplex.mappingCone.descShortComplex (S.map F),
    CochainComplex.mappingCone.quasiIso_descShortComplex hSF, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    apply (CochainComplex.mappingCone.isZero_X_iff _ _).2
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    apply (CochainComplex.mappingCone.isZero_X_iff _ _).2
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  · intro i
    have hsingle (j : ℤ) : Module.Free R ((F.obj (ModuleCat.of R R)).X j) ∧
        Module.Finite R ((F.obj (ModuleCat.of R R)).X j) := by
      by_cases hj : j = 0
      · subst j
        let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)
        exact ⟨Module.Free.of_equiv e.toLinearEquiv.symm,
          Module.Finite.equiv e.toLinearEquiv.symm⟩
      · have : Subsingleton ((F.obj (ModuleCat.of R R)).X j) :=
          ModuleCat.subsingleton_of_isZero
            (HomologicalComplex.isZero_single_obj_X _ _ _ _ hj)
        exact ⟨inferInstance, inferInstance⟩
    have := (hsingle (i + 1)).1
    have := (hsingle (i + 1)).2
    have := (hsingle i).1
    have := (hsingle i).2
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod (F.map f) i (i + 1) rfl ≪≫
      ModuleCat.biprodIsoProd _ _
    have hfree : Module.Free R ((openDvrResolution l E n).X i) :=
      Module.Free.of_equiv e.toLinearEquiv.symm
    have hfinite : Module.Finite R ((openDvrResolution l E n).X i) :=
      Module.Finite.equiv e.toLinearEquiv.symm
    exact ⟨hfree, inferInstance, hfinite⟩

private theorem dvrCompletionModel_exists
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal)
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E T) :
    Nonempty (OpenDvrCompletionModel l E C S hd) := by
  obtain ⟨A⟩ := openDvrAugmentedTowerComparison l E d T C S
  refine ⟨{ tower := A.tower
            rlim := A.rlim
            limit_model := A.limit_model
            representative := A.representative
            unit := A.unit
            koszul_unit := ?_
            intrinsic_unit := ?_
            complete_iff := openDvrIntrinsicCriterion l E d hd T C }⟩
  · intro P
    rw [← Category.assoc, ← Category.assoc,
      (koszulReconstruction T d 1 (fun _ ↦ Padic.coefficientExtensionUniformizer l E)
        hd).choose_spec.1]
    simpa only [Category.assoc] using A.unit P
  · intro P
    have h := (reconstructionKoszulIntrinsicComparison T d 1
      (fun _ ↦ Padic.coefficientExtensionUniformizer l E)
        (C.derived.functor.obj P)).choose_spec
    have hi := (Iso.comp_inv_eq
      (reconstructionKoszulIntrinsicComparison T d 1
        (fun _ ↦ Padic.coefficientExtensionUniformizer l E)
        (C.derived.functor.obj P)).choose).2 h.symm
    calc
      _ = (reconstructionKoszulDerivedUnit T d 1
          (fun _ ↦ Padic.coefficientExtensionUniformizer l E)).app
            (C.derived.functor.obj P) ≫
          (koszulReconstruction T d 1
            (fun _ ↦ Padic.coefficientExtensionUniformizer l E) hd).choose.hom.app
              (C.derived.functor.obj P) ≫
          (reconstructionRlim T d).map (A.tower.hom.app P) ≫
          A.rlim.hom.app ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
            (S.reduction.obj P)) := by rw [← Category.assoc, hi]
      _ = _ := by
        rw [← Category.assoc, ← Category.assoc,
          (koszulReconstruction T d 1
            (fun _ ↦ Padic.coefficientExtensionUniformizer l E) hd).choose_spec.1]
        simpa only [Category.assoc] using A.unit P

private theorem dvrActualUnit_isIso
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal)
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (M : OpenDvrCompletionModel l E C (openDvrSystem l E T) hd)
    (P : DerivedCategory (scalarReductionSource.{u, u} l E T))
    (hP : IsDerivedCompleteUnrestricted.{u, u} l E T P) :
    IsIso ((openDvrSystem l E T).adjunction.unit.app P) := by
  have := (M.complete_iff P).1 hP
  have he : IsIso (C.derived.functor.map ((openDvrSystem l E T).adjunction.unit.app P)) := by
    rw [← M.intrinsic_unit P]
    infer_instance
  exact isIso_of_reflects_iso _ C.derived.functor

/-- DVR quotient augmentation, Koszul completion, and quasi-compact open completeness.
Source: Stacks Tags 093M, 0A0E, 099B and 09BP; blueprint fix-prop-coherence
(blueprint: lem-sf-open-quotient-koszul-completeness).

Proof: (1) The extension-integers DVR theorem makes R a domain and a principal ideal
ring with finite residue field. Thus R is Noetherian, its residue group is torsion,
and the finite quotients have the displayed two-term free resolutions.
(2) Completed constant-sheaf reduction identifies finite constant coefficients with
continuous component functions, compatibly with the strict quotient maps and their limit.
(3) Choose one flat-term K-flat resolution. Both strict towers and their augmentations
are the same quotient tensor complex; scalar restriction only forgets actions.
(4) The sequence projection derived adjunction sends identity to x ↦ x tensor 1.
The pushforward/limit comparison and completed quotient-unit normalization identify
this whole strict augmentation, before evaluation, with the actual derived unit.
(5) The specified Koszul reconstruction comparison carries its unit to that unit.
(6) Regular-generator Koszul reconstruction and the completion reflector turn quotient
Roos completeness into invertibility of the actual Koszul unit, using isomorphism
invariance of completeness, not an identification of an arbitrary Roos isomorphism.
(7) Conversely its invertibility transports the actual strict-tower Roos triangle.
(8) Apply completed open-exchange transport to the identity cartesian square for the
quasi-compact open. It preserves intrinsic completeness; (6)--(7) give quotient
completeness and actual-unit invertibility. The calculus unit/projection identity
gives precisely the finite reduction maps. No boundedness hypothesis is used. -/
theorem openQuotientKoszulCompleteness :
    ∃ (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
      (hd : Ideal.span (Set.range (fun _ : Fin 1 ↦
        Padic.coefficientExtensionUniformizer l E)) = d.ideal),
      (∀ n : ℕ,
        ∃ f : openDvrResolution l E n ⟶
            (CochainComplex.singleFunctor (ModuleCat (Padic.coefficientExtensionIntegers l E))
              0).obj (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
                (Padic.coefficientExtensionRing l E (n + 1))),
          QuasiIso f ∧
          (openDvrResolution l E n).IsStrictlyGE (-1) ∧
          (openDvrResolution l E n).IsStrictlyLE 0 ∧
          (∀ i : ℤ, Module.Free (Padic.coefficientExtensionIntegers l E)
              ((openDvrResolution l E n).X i) ∧
            Module.Projective (Padic.coefficientExtensionIntegers l E)
              ((openDvrResolution l E n).X i) ∧
            Module.Finite (Padic.coefficientExtensionIntegers l E)
              ((openDvrResolution l E n).X i))) ∧
      (∀ T : Scheme.{u}, IsUnit (l : Γ(T, ⊤)) →
        ∃ C : OpenDvrCoefficientModel l E d T,
          Nonempty (OpenDvrCompletionModel l E C (openDvrSystem l E T) hd)) ∧
      (∀ (U X : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j],
        IsUnit (l : Γ(U, ⊤)) → IsUnit (l : Γ(X, ⊤)) →
        ∃ O : OpenDvrOpenModel l E j,
          ∀ K : DerivedCategory (scalarReductionSource.{u, u} l E U),
            IsDerivedCompleteUnrestricted.{u, u} l E U K →
            IsDerivedCompleteUnrestricted.{u, u} l E X (O.jShriek.obj K) ∧
            IsIso ((openDvrSystem l E X).adjunction.unit.app (O.jShriek.obj K)) ∧
            (∀ n : ℕ,
              (openDvrSystem l E X).adjunction.unit.app (O.jShriek.obj K) ≫
                (coefficientSequenceProjection.{u, u} l E X n).app
                  ((openDvrSystem l E X).reduction.obj (O.jShriek.obj K)) =
                (coefficientFiniteAdjunction.{u, u} l E X n).unit.app (O.jShriek.obj K) ≫
                  (coefficientFiniteDerivedRestriction.{u, u} l E X n).map
                    (((openDvrSystem l E X).reductionEvaluation n).inv.app
                      (O.jShriek.obj K)))) := by
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  have hgen : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal := by
    rw [hd]
    congr 1
    exact Set.range_const
  refine ⟨d, hgen, openDvrResolution_properties l E, ?_, ?_⟩
  · intro T hl
    obtain ⟨C⟩ := dvrCoefficientModel_exists l E d hd T
    exact ⟨C, dvrCompletionModel_exists l E d hgen T C (openDvrSystem l E T)⟩
  · intro U X j _ _ hU hX
    obtain ⟨C_U⟩ := dvrCoefficientModel_exists l E d hd U
    obtain ⟨C_X⟩ := dvrCoefficientModel_exists l E d hd X
    obtain ⟨O⟩ := dvrOpenModel_exists l E j
    obtain ⟨M_X⟩ := dvrCompletionModel_exists l E d hgen X C_X (openDvrSystem l E X)
    refine ⟨O, ?_⟩
    intro K hK
    have hI := openDvrIntrinsicOpenTransport l E d hgen j C_U C_X O K
      ((openDvrIntrinsicCriterion l E d hgen U C_U K).1 hK)
    have hcomplete := (openDvrIntrinsicCriterion l E d hgen X C_X (O.jShriek.obj K)).2 hI
    exact ⟨hcomplete, dvrActualUnit_isIso l E d hgen X C_X M_X _ hcomplete,
      fun n ↦ (openDvrSystem l E X).unit_projection _ n⟩

end WeilConjectures
