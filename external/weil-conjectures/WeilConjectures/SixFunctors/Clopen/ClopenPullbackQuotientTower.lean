/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.OpenCompletedRestriction.OpenCompletedRestrictionIdentification
import all WeilConjectures.SmoothPurity.OpenCompletedRestriction.OpenCompletedRestrictionIdentification
import WeilConjectures.SmoothPurity.IntegralAmbient.NormalizedIntegralPullbackTower
import WeilConjectures.SixFunctors.Sf.SfClopenCoefficientComparison
import WeilConjectures.SixFunctors.Clopen.ClopenScalarQuotientTower
import WeilConjectures.SixFunctors.Clopen.ClopenOrdinaryPullbackComparison
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # Exact open restriction of the strict finite pullback tower

Source: Stacks Project, sites-modules.tex, Tags 03D2 and 03D8.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
-- This instance has a free universe and leaves universe constraints stuck here.
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] OpenCompletedRestriction.coefficients

set_option backward.defeqAttrib.useBackward true
set_option allowUnsafeReducibility true
attribute [local reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.finite
  IntegralOnSlice.projection
  integralCoefficientCommRingSheaf integralCoefficientSheaf CategoryTheory.constantSheaf
  CategoryTheory.Functor.sheafPushforwardContinuous

private noncomputable def ordinarySfIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Scheme.{u}) (U : V.Opens) (d : SfClopenCoefficientRestriction l E V U) :
    OpenCompletedRestriction.ordinary l E U.ι ≅
      sfClopenModuleRestriction U _ _ d.completion := by
  let H := sheafCompose (ProEt.topology U.toScheme)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let ff := fullyFaithfulSheafCompose (ProEt.topology U.toScheme)
    CommRingCat.fullyFaithfulForget₂ToRingCat.{u + 1}
  let finite (n : ℕ) : integralCoefficientCommRingSheaf l E U.toScheme n ≅
      (OpenCompletedRestriction.ringRestriction.{u, u} U.ι).obj
        (integralCoefficientCommRingSheaf l E V n) := ff.preimageIso (d.finite n)
  let completed : completedIntegralCommRingSheafUnrestricted.{u, u} l E U.toScheme ≅
      (OpenCompletedRestriction.ringRestriction.{u, u} U.ι).obj
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E V) :=
    ff.preimageIso d.completion
  have hf (n : ℕ) : H.map (finite n).hom = (d.finite n).hom := ff.map_preimage _
  have hc : H.map completed.hom = d.completion.hom := ff.map_preimage _
  let c : OpenCompletedRestriction.Coefficients.{u, u} l E U.ι :=
    { finite := finite
      constants := by
        intro n V
        apply (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_injective
        rw [Functor.map_comp]
        change _ ≫ (H.map (finite n).hom).hom.app (op V) = _
        rw [hf]
        exact RingCat.hom_ext (RingHom.ext (d.finite_constant n V))
      completed := completed
      projections := by
        intro n
        apply H.map_injective
        rw [Functor.map_comp, Functor.map_comp, hc, hf]
        exact d.projection n }
  have he : c = OpenCompletedRestriction.coefficients.{u, u} l E U.ι :=
    OpenCompletedRestriction.coefficients_subsingleton l E U.ι c _
  have hnormalized : H.map
      (OpenCompletedRestriction.coefficients.{u, u} l E U.ι).completed.hom =
      d.completion.hom := by
    rw [← he]
    exact hc
  let F : scalarReductionSource.{u, u} l E V ⥤
      scalarReductionSource.{u, u} l E U.toScheme :=
    sfClopenModuleRestriction U _ _ d.completion
  let : F.Additive := d.additive
  let : PreservesFiniteLimits F := d.limits
  let : PreservesFiniteColimits F := d.colimits
  let e : OpenCompletedRestriction.ordinary.{u, u} l E U.ι ≅ F :=
    SheafOfModules.pushforwardCongr (F := sfClopenSiteInclusion U)
      (J := ProEt.topology U.toScheme) (K := ProEt.topology V) hnormalized ≪≫ Iso.refl _
  exact e

attribute [local irreducible] ordinarySfIso

/-- The strict finite pullback tower is restriction of the strict quotient tower.

Source: Stacks Project, sites-modules.tex, Tags 03D2 and 03D8; step 1 of
lem-fix-clopen-integral-completion-restriction.
(blueprint: lem-sf-clopen-pullback-quotient-tower).

Proof: composition with the open immersion is left adjoint to base change on the
pro-etale sites. Transpose the inverse normalized coefficient isomorphism under
this adjunction. The finite transpose fixes constant sections, so it is the
specified direct-image coefficient map. The completed transpose commutes with
every finite projection, so uniqueness identifies it with the specified ambient
completed coefficient map. The ringed-site adjunction and uniqueness of module
left adjoints therefore identify ordinary restriction with ambient pullback.

Use the existing clopen scalar quotient comparison to commute restriction with
each actual quotient complex. Its tensor normalization proves naturality in the
input complex and compatibility with quotient transitions: after the inverse
comparison, local pure tensors generate the source, and both composites have the
same formula. Assemble these comparisons by NatTrans.ofOpSequence. Identify the
global slice towers with the unrestricted quotient towers. Finally compose with
the normalized ambient pullback tower isomorphism. No invertibility of the prime,
completeness or boundedness is used. Empty clopens give the unique comparison in
the zero module category. -/
theorem clopenPullbackQuotientTower
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Scheme.{u}) (U : V.Opens) (hU : IsClosed (U : Set V)) :
    Nonempty (IntegralOnSlice.tower l E V none ⋙
      (Functor.whiskeringRight ℕᵒᵖ (IntegralOnSlice.Cx l E V none)
        (IntegralOnSlice.Cx l E U.toScheme none)).obj
          (OpenCompletedRestriction.complexRestriction l E U.ι) ≅
      integralOperationsPullbackTowerFunctor l E U.ι) := by
  obtain ⟨d⟩ := sf_clopen_coefficient_comparison l E V U
  obtain ⟨t⟩ := clopenScalarQuotientTower l E V U hU d
  let SF : IntegralOnSlice.Mod l E V none ⥤ IntegralOnSlice.Mod l E U.toScheme none :=
    sfClopenModuleRestriction U _ _ d.completion
  let : SF.Additive := d.additive
  let : SF.PreservesZeroMorphisms := @Functor.preservesZeroMorphisms_of_additive
    _ _ _ _ _ _ SF d.additive
  let : (IntegralAmbient.pull l E U.ι).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (IntegralAmbient.pull l E U.ι) (IntegralAmbient.pull_additive l E U.ι)
  let e := NatIso.mapHomologicalComplex (ordinarySfIso l E V U d) (.up ℤ)
  let P := Functor.whiskeringRight ℕᵒᵖ (IntegralOnSlice.Cx l E V none)
    (IntegralOnSlice.Cx l E U.toScheme none)
  let q : IntegralOnSlice.tower l E V none ⋙
      P.obj (OpenCompletedRestriction.complexRestriction l E U.ι) ≅
      OpenCompletedRestriction.complexRestriction l E U.ι ⋙
        IntegralOnSlice.tower l E U.toScheme none :=
    Functor.isoWhiskerRight (eqToIso (IntegralOnSlice.globalTower_eq l E V)) _ ≪≫
    Functor.isoWhiskerLeft _ (P.mapIso e) ≪≫ t ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (IntegralOnSlice.globalTower_eq l E U.toScheme)).symm ≪≫
    Functor.isoWhiskerRight e.symm _
  obtain ⟨b₀⟩ := clopenOrdinaryPullbackComparison l E V U
  let b := NatIso.mapHomologicalComplex b₀ (.up ℤ)
  exact ⟨q ≪≫ Functor.isoWhiskerRight b _ ≪≫
    (IntegralAmbient.pullTowerModel l E U.ι).exists.choose⟩

end WeilConjectures
