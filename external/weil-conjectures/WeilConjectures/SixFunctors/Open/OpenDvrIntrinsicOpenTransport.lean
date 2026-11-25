/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import WeilConjectures.SixFunctors.Open.OpenDvrIntrinsicCriterion
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedDirectImagePreservesCompleteness
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Data.Nat.Prime.Infinite

/-! # Quasi-compact open extension preserves intrinsic DVR completeness

Source: Stacks Tags 0941, 099B and 0A0E; canonical coefficient transport.
(blueprint: lem-sf-open-dvr-intrinsic-open-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
local instance dvrOpen_commRingSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  (integralCoefficientRingSheafify.{u, u} T).isRightAdjoint

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem dvrOpen_products
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (O : OpenDvrOpenModel l E j) :
    PreservesLimitsOfShape (Discrete ℕ) O.extension.ordinary := by
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  let W : X.ProEt := ProEt.mk j
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let e := ProEt.sliceEquiv X W
  have : e.inverse.IsDenseSubsite (ProEt.topology U) ((ProEt.topology X).over W) :=
    ProEt.sliceDense X W
  let B := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j R)
  let c : B ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U) ((ProEt.topology X).over W)).obj (A.over W) := Iso.refl _
  obtain ⟨q, hq⟩ := ProEt.module_transport.{u} ((ProEt.topology X).over W)
    (ProEt.topology U) e (A.over W) B c
  let F : SheafOfModules.{u + 1} (A.over W) ⥤ SheafOfModules.{u + 1} A :=
    SheafOfModules.extensionByZeroPresheaf.{u + 1, u, u + 1, u + 1} A W ⋙
      PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} (𝟙 A.obj)
  let a₀ : F ⊣ SheafOfModules.overFunctor.{u + 1, u, u + 1, u + 1} A W :=
    SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1} R W
  let L := q.inverse ⋙ F
  let a : L ⊣ SheafOfModules.OpenTensorNormalization.restrict .ordinary j R :=
    (q.symm.toAdjunction.comp a₀).ofNatIsoRight (by
      apply Functor.fullyFaithfulCancelRight (SheafOfModules.forget B)
      change SheafOfModules.overFunctor.{u + 1, u, u + 1, u + 1} A W ⋙ q.functor ⋙
        SheafOfModules.forget B ≅
          SheafOfModules.OpenTensorNormalization.restrict .ordinary j R ⋙
            SheafOfModules.forget B
      rw [hq]
      refine NatIso.ofComponents (fun M ↦ ?_) ?_
      · exact PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl)
      · intro M N f
        ext V x
        rfl)
  have : IsOpenImmersion W.hom := by change IsOpenImmersion j; infer_instance
  have : QuasiCompact W.hom := by change QuasiCompact j; infer_instance
  have : ∀ M : ULift.{u + 1} ℕ → SheafOfModules.{u + 1} (A.over W),
      PreservesLimit (Discrete.functor M) F := by
    intro M
    have : IsIso (piComparison F M) :=
      (proEtaleRingedExtensionByZero_products W R (ULift.{u + 1} ℕ) M).1
    exact PreservesProduct.of_iso_comparison F M
  have : PreservesLimitsOfShape (Discrete (ULift.{u + 1} ℕ)) F :=
    preservesLimitsOfShape_of_discrete F
  have : PreservesLimitsOfShape (Discrete ℕ) F :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) F
  have : PreservesLimitsOfShape (Discrete ℕ) L := inferInstance
  exact preservesLimitsOfShape_of_natIso (Adjunction.leftAdjointUniq a O.extension.adjunction)

private theorem dvrOpen_scalar_projection (T : Scheme.{u}) (n : ℕ) (V : T.ProEtᵒᵖ) :
    (completedIntegralCommRingProjectionUnrestricted.{u, u} l E T n).hom.app V
      (integralCompletionScalarValue.{u, u} l E T V) =
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app V
      (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (Padic.coefficientExtensionUniformizer l E))) := by
  let B := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  let C := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let q : B ⟶ C := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))
  have hq : integralConstantToCompletionOfUniverses.{u, u} l E T ≫
      limit.π (integralCoefficientSheafSystem.{u, u} l E T) (op n) =
        integralConstantQuotientOfUniverses.{u, u} l E T n := limit.lift_π _ _
  have hh := congrArg (fun f ↦ f.hom.app V
    ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj B)).app V
      (ULift.up (Padic.coefficientExtensionUniformizer l E)))) hq
  change _ = (integralConstantQuotientOfUniverses.{u, u} l E T n).hom.app V _ at hh
  change (completedIntegralCommRingProjectionUnrestricted.{u, u} l E T n).hom.app V
      (integralCompletionScalarValue.{u, u} l E T V) = _ at hh
  rw [hh]
  exact congrArg (fun f ↦ f.app V
    (ULift.up (Padic.coefficientExtensionUniformizer l E)))
      (toSheafify_naturality (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).map q)).symm

private theorem dvrOpen_scalar_restrict
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (O : OpenDvrOpenModel l E j) (V : U.ProEtᵒᵖ) :
    O.ring.hom.hom.app V (integralCompletionScalarValue.{u, u} l E X
      ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj V)) =
        integralCompletionScalarValue.{u, u} l E U V := by
  let ev := sheafToPresheaf (ProEt.topology U) RingCat.{u + 1} ⋙
    (CategoryTheory.evaluation U.ProEtᵒᵖ RingCat.{u + 1}).obj V
  apply Concrete.isLimit_ext _ (isLimitOfPreserves ev
    (limit.isLimit (integralCoefficientSheafSystem l E U)))
  intro n
  have hp := congrArg (fun f ↦ f.app V (integralCompletionScalarValue.{u, u} l E X
    ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj V)))
      (O.ring_projection n.unop)
  change (completedIntegralCommRingProjectionUnrestricted l E U n.unop).hom.app V
      (O.ring.hom.hom.app V _) =
    (completedIntegralCommRingProjectionUnrestricted l E U n.unop).hom.app V _
  change (O.finite n.unop).hom.app V
      ((completedIntegralCommRingProjectionUnrestricted l E X n.unop).hom.app
        ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj V) _) =
    (completedIntegralCommRingProjectionUnrestricted l E U n.unop).hom.app V
      (O.ring.hom.hom.app V _) at hp
  rw [← hp, dvrOpen_scalar_projection, dvrOpen_scalar_projection]
  exact O.finite_constants n.unop V
    (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))
      (Padic.coefficientExtensionUniformizer l E)))

private theorem dvrOpen_scalar_extension
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (O : OpenDvrOpenModel l E j)
    (P : CochainComplex (scalarReductionSource.{u, u} l E U) ℤ) :
    End.of (((O.modules.functor ⋙ O.extension.ordinary).mapHomologicalComplex (.up ℤ)).map
      (integralKoszulScalar.{u, u} l E U P).asHom) =
    integralKoszulScalar.{u, u} l E X
      (((O.modules.functor ⋙ O.extension.ordinary).mapHomologicalComplex (.up ℤ)).obj P) := by
  let GP := ((O.modules.functor ⋙ O.extension.ordinary).mapHomologicalComplex (.up ℤ)).obj P
  apply End.ext
  apply HomologicalComplex.hom_ext
  intro i
  let M := O.modules.functor.obj (P.X i)
  let adj := O.extension.adjunction
  have hF' (F : scalarReductionSource.{u, u} l E U ⥤
      AlgebraicGeometry.Scheme.ProjectionRestriction.Mod
        (SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j
          (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)))
      (hF : F = SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology U)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map O.ring.hom)) :
      ∀ (V : U.ProEtᵒᵖ) (x : (F.obj (P.X i)).val.obj V),
        (F.map ((integralKoszulScalar.{u, u} l E U P).asHom.f i)).val.app V x =
          integralCompletionScalarValue.{u, u} l E X
            ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj V) • x := by
    subst F
    intro V x
    let x₀ : (P.X i).val.obj V := x
    change ((integralKoszulScalar.{u, u} l E U P).asHom.f i).val.app V x₀ =
      O.ring.hom.hom.app V (integralCompletionScalarValue.{u, u} l E X _) • x₀
    have hs := (integralKoszulScalar_existsUnique.{u, u} l E U P).exists.choose_spec i V x₀
    change ((integralKoszulScalar.{u, u} l E U P).asHom.f i).val.app V x₀ = _ at hs
    exact hs.trans (congrArg (fun z ↦ z • x₀) (dvrOpen_scalar_restrict l E j O V)).symm
  have hF := hF' O.modules.functor O.modules_functor
  change O.extension.ordinary.map (O.modules.functor.map
    ((integralKoszulScalar.{u, u} l E U P).asHom.f i)) = _
  apply (adj.homEquiv M (O.extension.ordinary.obj M)).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  change adj.unit.app M ≫
    (O.extension.ordinary ⋙
      SheafOfModules.OpenTensorNormalization.restrict .ordinary j
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).map _ = _
  rw [← adj.unit.naturality (O.modules.functor.map
    ((integralKoszulScalar.{u, u} l E U P).asHom.f i))]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change (adj.unit.app M).val.app V
      ((O.modules.functor.map ((integralKoszulScalar.{u, u} l E U P).asHom.f i)).val.app V x) =
    ((integralKoszulScalar.{u, u} l E X GP).asHom.f i).val.app
      ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj V)
          ((adj.unit.app M).val.app V x)
  rw [hF]
  have hs := (integralKoszulScalar_existsUnique.{u, u} l E X GP).exists.choose_spec i
    ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj V)
      ((adj.unit.app M).val.app V x)
  change _ = integralCompletionScalarValue.{u, u} l E X _ • _ at hs
  exact (((adj.unit.app M).val.app V).hom.map_smul _ _).trans hs.symm

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
private theorem dvrOpen_complete
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (O : OpenDvrOpenModel l E j)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E U))
    (hK : IsDerivedCompleteUnrestricted.{u, u} l E U K) :
    IsDerivedCompleteUnrestricted.{u, u} l E X (O.jShriek.obj K) := by
  classical
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  have hne : p ≠ l := by omega
  let H : scalarReductionSource.{u, u} l E U ⥤ scalarReductionSource.{u, u} l E X :=
    O.modules.functor ⋙ O.extension.ordinary
  have : PreservesFiniteLimits H :=
    comp_preservesFiniteLimits O.modules.functor O.extension.ordinary
  have : PreservesFiniteColimits H :=
    comp_preservesFiniteColimits O.modules.functor O.extension.ordinary
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  let G := H.mapHomologicalComplex (.up ℤ)
  have : PreservesLimitsOfShape (Discrete ℕ) O.extension.ordinary :=
    dvrOpen_products l E j O
  have : PreservesLimitsOfShape (Discrete ℕ) H := inferInstance
  let P : CochainComplex (scalarReductionSource.{u, u} l E U) ℤ :=
    DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hP : IsDerivedCompleteUnrestricted.{u, u} l E U (DerivedCategory.Q.obj P) :=
    (complete_iff_local.{u, u} p l hne E U _).mpr
      (integralLocallyComplete_iso.{u, u} l E U _ e.symm
        ((complete_iff_local.{u, u} p l hne E U K).mp hK))
  let μ := integralKoszulScalar.{u, u} l E U P
  have hμ : QuasiIso (CochainComplex.PrincipalCone.unit μ) :=
    (complete_iff_principalUnit.{u, u} p l hne E U P).mp hP
  have : QuasiIso (G.map (CochainComplex.PrincipalCone.unit μ)) := inferInstance
  have hscalar : End.of (G.map μ.asHom) = integralKoszulScalar.{u, u} l E X (G.obj P) := by
    simpa only [G, H, μ] using dvrOpen_scalar_extension l E j O P
  let a : DerivedCategory.Q.obj (G.obj P) ≅ DerivedCategory.Q.obj
      (CochainComplex.PrincipalCone.completion (integralKoszulScalar.{u, u} l E X (G.obj P))) :=
    asIso (DerivedCategory.Q.map (G.map (CochainComplex.PrincipalCone.unit μ))) ≪≫
      DerivedCategory.Q.mapIso (principalMapIso H μ) ≪≫
        DerivedCategory.Q.mapIso (eqToIso (congrArg
          (fun z : End (G.obj P) ↦ CochainComplex.PrincipalCone.completion z) hscalar))
  have hcomplete := (IntegralPrincipalCone.localCriterion.{u, u} l E X
    (integralCompletionScalarValue.{u, u} l E X) (integralScalar_natural.{u, u} l E X)
    (G.obj P) (integralKoszulScalar.{u, u} l E X (G.obj P))
    (integralKoszulScalar_existsUnique.{u, u} l E X (G.obj P)).exists.choose_spec
    (DerivedCategory.Q.obj (G.obj P)) (Iso.refl _)).1
  have hlocal := integralLocallyComplete_iso.{u, u} l E X _ a.symm hcomplete
  let b : DerivedCategory.Q.obj (G.obj P) ≅ O.jShriek.obj K :=
    (H.mapDerivedCategoryFactors.app P).symm ≪≫ H.mapDerivedCategory.mapIso e ≪≫
      ((Functor.mapDerivedCategoryCompIso O.modules.functor O.extension.ordinary).app K).symm
  exact (complete_iff_local.{u, u} p l hne E X _).mpr
    (integralLocallyComplete_iso.{u, u} l E X _ b hlocal)

/-- Transport the completed open-preservation theorem across canonical coefficients.
Source: Stacks Tags 03DI, 09BP and 099B
(blueprint: lem-sf-open-dvr-intrinsic-open-transport).

Proof: lift the DVR datum into the coefficient universe and compare its quotient
rings with the lifted quotients, sending the class of a to the lifted class of a.
The tensor universal property and uniqueness of limits transport the explicit Koszul
fiber and its degree-zero unit to the completedAdicIntrinsicUnit construction used
here. Apply completedOpenExchangeComparison to the identity cartesian square with
horizontal map j. Its first preservation clause gives intrinsic completeness of the
completed-coefficient extension. Under C_U and C_X, the finite-constant and limit
projection equations identify its restriction right adjoint with the actual open
restriction in O. Uniqueness of left adjoints gives an isomorphism from O.jShriek,
compatible with scalar equivalence. Exact equivalences and this isomorphism transport
the intrinsic fiber unit, so invertibility of the source unit implies invertibility
of the displayed target unit. Quasi-compactness is exactly the hypothesis needed for
completed open preservation; no commutation with arbitrary inverse limits is used. -/
theorem openDvrIntrinsicOpenTransport
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (C_U : OpenDvrCoefficientModel l E d U) (C_X : OpenDvrCoefficientModel l E d X)
    (O : OpenDvrOpenModel l E j)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E U))
    (hK : IsIso (completedAdicIntrinsicUnit U d 1
      (fun _ ↦ Padic.coefficientExtensionUniformizer l E) (C_U.derived.functor.obj K))) :
    IsIso (completedAdicIntrinsicUnit X d 1
      (fun _ ↦ Padic.coefficientExtensionUniformizer l E)
      (C_X.derived.functor.obj (O.jShriek.obj K))) := by
  apply (openDvrIntrinsicCriterion l E d hd X C_X (O.jShriek.obj K)).mp
  exact dvrOpen_complete l E j O K ((openDvrIntrinsicCriterion l E d hd U C_U K).mpr hK)

end WeilConjectures
