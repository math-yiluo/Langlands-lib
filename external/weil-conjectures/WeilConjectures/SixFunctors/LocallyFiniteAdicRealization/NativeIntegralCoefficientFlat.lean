/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralRationalizationExact
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Locally.LocallyFiniteCoefficientRingRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Flatness of the normalized integral-to-native coefficient map

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-flat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

private def extensionComp {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c) :
    pbcExtend a ⋙ pbcExtend b ≅ pbcExtend c :=
  (((pbcScalarAdjunction a).comp (pbcScalarAdjunction b)).ofNatIsoRight
    (pbcRestrictComp a b c h)).leftAdjointUniq (pbcScalarAdjunction c)

private theorem extension_iso_exact {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (e : R ≅ S) :
    PreservesFiniteLimits (pbcExtend e.hom) := by
  have : (pbcRestrict e.hom).IsEquivalence :=
    inferInstanceAs
      (ProEtale.CondensedRing.ringModuleEquivalenceOfIso X
        ((adicLisseForget X).mapIso e)).functor.IsEquivalence
  have := (pbcScalarAdjunction e.hom).isEquivalence_left_of_isEquivalence_right
  infer_instance

private theorem extension_comp_exact {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    [PreservesFiniteLimits (pbcExtend a)] [PreservesFiniteLimits (pbcExtend b)] :
    PreservesFiniteLimits (pbcExtend c) :=
  preservesFiniteLimits_of_natIso (extensionComp a b c h)

private theorem internal_exact (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] [PreservesFiniteLimits (Mod.extendScalars a)] :
    PreservesFiniteLimits (pbcExtend (ProEtale.CondensedRing.sectionRingMap X a)) := by
  let ER := InternalAbelianSheafModule.sectionModuleEquivalence
    (ProEt.topology X) R
  let ES := InternalAbelianSheafModule.sectionModuleEquivalence
    (ProEt.topology X) S
  let adj := ER.symm.toAdjunction.comp
    ((Mod.extendRestrictAdjunction a).comp ES.toAdjunction)
  let d := ProEtale.CondensedRing.sectionModuleComapIso X a
  let q : (ES.inverse ⋙ Mod.comap a) ⋙ ER.functor ≅
      pbcRestrict (ProEtale.CondensedRing.sectionRingMap X a) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft ES.inverse d ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ES.counitIso _ ≪≫ Functor.leftUnitor _
  exact preservesFiniteLimits_of_natIso
    ((adj.ofNatIsoRight q).leftAdjointUniq (pbcScalarAdjunction _))

private def liftContinuousEquiv (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (V : Type u) [TopologicalSpace V] :
    C(V, T) ≃+* C(V, ULift.{u + 1} T) where
  toFun f := ⟨fun x ↦ ULift.up (f x), continuous_uliftUp.comp f.continuous⟩
  invFun f := ⟨fun x ↦ (f x).down, continuous_uliftDown.comp f.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem integral_exact (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (C : CoefficientPresentation l X E i) :
    PreservesFiniteLimits (pbcExtend C.integralInclusion) := by
  let := coefficientExtensionNormedField l E
  let A := Padic.coefficientExtensionIntegers l E
  have hA : ∀ x : E, x ∈ A ↔ ‖x‖ ≤ 1 :=
    (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.1
  have : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := ℚ_[l]) (L := E))
  have hf (U : X.ProEtᵒᵖ) : (C.integralInclusion.hom.app U).hom.Flat := by
    let eA := liftContinuousEquiv A U.unop.left
    let eE := liftContinuousEquiv E U.unop.left
    let f := A.subtype.compLeftContinuous U.unop.left continuous_subtype_val
    have h : (C.integralInclusion.hom.app U).hom =
        eE.toRingHom.comp (f.comp eA.symm.toRingHom) := by
      apply RingHom.ext
      intro s
      apply ContinuousMap.ext
      intro x
      apply ULift.ext
      exact C.integralInclusion_normalized U.unop s x
    rw [h]
    exact ((RingHom.Flat.of_bijective eA.symm.bijective).comp
      (AlgebraicGeometry.Scheme.continuous_flat A hA (X := U.unop.left))).comp
        (RingHom.Flat.of_bijective eE.bijective)
  have : PreservesFiniteLimits
      (SfScalarExtension.F.{u + 1, u, u + 1} C.integralInclusion) :=
    SfScalarExtension.preserves.{u + 1, u, u + 1} C.integralInclusion hf
  have : (SfScalarExtension.F.{u + 1, u, u + 1} C.integralInclusion).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨_, _, hadj⟩ :=
    SheafOfModules.sheafRingCoefficientOrdinaryAdjunction C.integralInclusion
  have hobj (M : pbcModules X (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X E)) :
      (SfScalarExtension.F.{u + 1, u, u + 1} C.integralInclusion).obj M =
        SheafOfModules.changeOfRings C.integralInclusion M := by
    unfold SfScalarExtension.F
    rfl
  have hmap {M N : pbcModules X (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X E)}
      (f : M ⟶ N) :
      (SfScalarExtension.F.{u + 1, u, u + 1} C.integralInclusion).map f =
        eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom C.integralInclusion M f ≫
          eqToHom (hobj N).symm := by
    unfold SfScalarExtension.F at hobj ⊢
    rfl
  obtain ⟨adj, _⟩ := hadj (SfScalarExtension.F.{u + 1, u, u + 1} C.integralInclusion)
    hobj hmap
  exact preservesFiniteLimits_of_natIso
    (adj.leftAdjointUniq (pbcScalarAdjunction _))

private def rationalRangeIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (X : Scheme.{u}) :
    (adicLisseForget X).obj (rationalCoefficientSheaf l X E) ≅
      ProEtale.continuousMapRingSheaf X i.fieldRange := by
  let := coefficientExtensionNormedField l E
  let e := i.equivFieldRange
  let f : AbsoluteValue E ℝ :=
    (NormedField.toAbsoluteValue (PadicAlgCl l)).comp i.toRingHom.injective
  have hf (a : ℚ_[l]) : f (algebraMap ℚ_[l] E a) = ‖a‖ := by
    change ‖i (algebraMap ℚ_[l] E a)‖ = ‖a‖
    rw [i.commutes]
    exact PadicAlgCl.norm_extends l a
  have he : Isometry e := AddMonoidHomClass.isometry_of_norm e
    (spectralNorm_unique_field_norm_ext hf)
  let h : E ≃ₜ i.fieldRange :=
    (show E ≃ᵢ i.fieldRange from { e.toEquiv with isometry_toFun := he }).toHomeomorph
  let q (U : X.ProEtᵒᵖ) : C(U.unop.left, ULift.{u + 1} E) ≃+*
      ULift.{u + 1} C(U.unop.left, i.fieldRange) :=
    { toFun := fun s ↦ ULift.up
        ⟨fun x ↦ e (s x).down,
          h.continuous.comp (continuous_uliftDown.comp s.continuous)⟩
      invFun := fun s ↦
        ⟨fun x ↦ ULift.up (e.symm (s.down x)),
          continuous_uliftUp.comp (h.symm.continuous.comp s.down.continuous)⟩
      left_inv := fun s ↦ by
        apply ContinuousMap.ext
        intro x
        apply ULift.ext
        exact e.symm_apply_apply _
      right_inv := fun s ↦ by
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _
      map_mul' := fun s t ↦ by
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.map_mul _ _
      map_add' := fun s t ↦ by
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.map_add _ _ }
  exact ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ (q U).toRingCatIso) (fun _ ↦ rfl))

private theorem rational_exact (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsNoetherian X] [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (C : CoefficientPresentation l X E i) :
    PreservesFiniteLimits (pbcExtend C.rationalInclusion) := by
  obtain ⟨θ, hθ, hval, _⟩ := ProEtale.locallyFiniteCoefficientRing_realization.{u} l
  let K : PadicAlgCl.FiniteIntermediateField l :=
    ⟨i.fieldRange, Module.Finite.equiv i.equivFieldRange.toLinearEquiv⟩
  let R := ProEtale.continuousMapRingSheaf X K
  let A := (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj (ProEt.topology X) R
    (fun U s t ↦ @mul_comm (ULift.{u + 1} C(U.unop.left, K)) inferInstance s t)
  let g := asIso (ProEtale.chartComparison X K)
  let b := ProEtale.padicSubfieldRingObjToPadicAlgCl X l K
  have : IsMonHom (θ X).hom := hθ X
  let a := g.inv ≫ b ≫ (θ X).hom
  have : IsMonHom a := by dsimp only [a]; infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars g.inv) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv g.inv).symm
  have : PreservesFiniteLimits (Mod.extendScalars b) :=
    ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
      l X K
  have : PreservesFiniteLimits (Mod.extendScalars (θ X).hom) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv (θ X).hom).symm
  have : PreservesFiniteLimits (Mod.extendScalars (b ≫ (θ X).hom)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsComp b (θ X).hom).symm
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsComp g.inv (b ≫ (θ X).hom)).symm
  let e : rationalCoefficientSheaf l X E ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) A :=
    (fullyFaithfulSheafCompose (ProEt.topology X)
      CommRingCat.fullyFaithfulForget₂ToRingCat.{u + 1}).preimageIso
        (rationalRangeIso l E i X ≪≫
          (ProEtale.CondensedRing.reconstructedRingIso.{u} X R).symm)
  have h : e.hom ≫ ProEtale.CondensedRing.sectionRingMap X a =
      C.rationalInclusion := by
    apply Sheaf.hom_ext
    ext U s
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    have hv := hval X K U (g.inv.hom.app U
      ((rationalRangeIso l E i X).hom.hom.app U s)) x
    have hg := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app U) g.inv_hom_id)
      ((rationalRangeIso l E i X).hom.hom.app U s)
    change (g.hom.hom.app U (g.inv.hom.app U _)) = _ at hg
    have hv' := hv.trans (congrArg (fun z ↦ (z.down x : PadicAlgCl l)) hg)
    exact hv'.trans (C.rationalInclusion_normalized U s x).symm
  exact @extension_comp_exact X _ _ _ e.hom
    (ProEtale.CondensedRing.sectionRingMap X a) C.rationalInclusion h
    (extension_iso_exact e) (internal_exact X A (abRing l X) a)

/-- Ordinary extension along the normalized integral coefficient map preserves finite limits.

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-flat).

Proof in words: extension along C.integral.inv is an equivalence. The normalization
of C.integralInclusion identifies its section maps with the continuous integral-to-field
inclusions. The clopen partition according as the norm is at most one or greater than
one supplies an integral nowhere-zero denominator for every continuous field-valued
function. Thus these section maps are localizations and flat. Continuous ULift ring
isomorphisms retain flatness. Sectionwise extension followed by sheafification preserves
finite limits; its scalar adjunction identifies it with pbcExtend C.integralInclusion.
For the rational inclusion, take the finite intermediate field which is the range of i.
The unique extended p-adic norm makes i.equivFieldRange an isometry. Postcomposition
therefore identifies the rational coefficient sheaf with continuous functions into this
field. The continuous chart and the normalized locally finite coefficient realization
transport the proved flat finite-subfield inclusion to the native coefficient ring.
The section-action equivalences identify restriction along the reconstructed section
map, so uniqueness of scalar left adjoints transports this exact extension to ordinary
module sheaves. The pointwise normalization of C.rationalInclusion identifies the map.
Finally pbcRestrictComp and uniqueness of left adjoints identify the composite of the
three exact extensions with extension along C.integralMap. Empty schemes and zero
modules satisfy the same function and adjunction identities.
-/
theorem nativeIntegralCoefficient_flat
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (C : CoefficientPresentation l X E i) :
    PreservesFiniteLimits (pbcExtend (C.integralMap l X)) := by
  have : PreservesFiniteLimits (pbcExtend C.integral.inv) :=
    extension_iso_exact C.integral.symm
  have := integral_exact l X E i C
  have := rational_exact l X E i C
  have : PreservesFiniteLimits (pbcExtend (C.integralInclusion ≫ C.rationalInclusion)) :=
    extension_comp_exact _ _ _ rfl
  exact extension_comp_exact _ _ _ rfl

end WeilConjectures.LocallyFiniteAdicRealization
