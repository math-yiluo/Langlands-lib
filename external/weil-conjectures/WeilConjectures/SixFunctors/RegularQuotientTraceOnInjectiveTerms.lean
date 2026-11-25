/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
import WeilConjectures.SixFunctors.Regular.RegularQuotientInjectiveKernel
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAdjoint
import WeilConjectures.Algebra.Homology.RegularQuotientCone.Augmentation.RegularQuotientConeTraceShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all Mathlib.Algebra.Homology.Localization

/-! Termwise-injective computation of the regular quotient trace.

Source: Stacks Tags 06YY, 07A6, 0A70, 0BZE, 0BZH and 08FZ;
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry

section DerivedCounit

open CategoryTheory.Limits

variable {B D : Type*} [Category B] [Category D] [Abelian B] [Abelian D]
  [HasDerivedCategory B] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : B ⥤ D} {R : D ⥤ B} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

set_option backward.isDefEq.respectTransparency false in
/-- On a K-injective complex, the counit of the derived adjunction `L ⊣ R(R)` is the localized
termwise counit, once `R(R)` is computed termwise.
Source: Stacks Tags 05TG and 0A70; the derived counit is the localization of the ordinary counit
on K-injective representatives (auxiliary; not a blueprint node). -/
theorem CategoryTheory.Adjunction.mapDerivedCategory_map_rightDerivedFunctorObjQIso_inv_counit
    (adj : L ⊣ R) (J : CochainComplex D ℤ) [J.IsKInjective] :
    L.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso J).inv ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj J) =
    L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app J) := by
  have hq₁ (K : CochainComplex B ℤ) : (DerivedCategory.quotientCompQhIso B).hom.app K = 𝟙 _ :=
    rfl
  have hq₂ (K : CochainComplex B ℤ) : (DerivedCategory.quotientCompQhIso B).inv.app K = 𝟙 _ :=
    rfl
  have hq₃ (K : CochainComplex D ℤ) : (DerivedCategory.quotientCompQhIso D).hom.app K = 𝟙 _ :=
    rfl
  have hh (K : CochainComplex B ℤ) : (L.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ :=
    rfl
  have hinv : (R.rightDerivedFunctorObjQIso J).inv =
      R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J) := by
    simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
      Functor.mapIso_inv, Iso.app_inv, asIso_hom, Iso.app_hom, hq₂, hq₃,
      CategoryTheory.Functor.map_id, Category.id_comp]
    erw [Category.comp_id]
  have hf : L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj ((R.mapHomologicalComplex (.up ℤ)).obj J)) =
      L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) := by
    simp only [Functor.mapDerivedCategoryFactorsh_hom_app, hq₁, hh,
      CategoryTheory.Functor.map_id, Category.id_comp]
    erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id]
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj J)
  erw [hf] at h
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  rw [hinv]
  exact h

end DerivedCounit

namespace WeilConjectures

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

private local instance (T : Scheme.{u}) : EssentiallySmall.{u+1} T.ProEt :=
  essentiallySmallSelf.{0,u,u+1} _
private local instance (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u,u} T
private local instance (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u,u} T
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

open SheafOfModules SheafOfModules.RegularQuotientCone in
/-- The normalized regular quotient trace is invertible on a K-injective complex with injective
terms.
Source: Stacks Tags 06YY, 07A6, 0A70 and 08FZ; the principal short exact sequence of complexes
and its cone-boundary/coinduction comparison
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms).

Proof: derived coinduction at `Q X` is ordinary coinduction applied termwise, with counit the
localized termwise counit. On injective terms the coinduction counit and the positive
uniformizer scalar form a short exact sequence; apply it to `X⟦-1⟧` and conclude by the
normalized cone comparison for short exact sequences of the regular scalar. -/
theorem reductionCoinductionTrace_isIso_of_isKInjective_of_injective
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (X : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    [X.IsKInjective] [∀ i : ℤ, Injective (X.X i)] :
    IsIso ((reductionCoinductionTrace.{u} l E T n).app (DerivedCategory.Q.obj X)) := by
  let : Abelian.HasKInjectiveResolutions (scalarReductionSource.{u, u} l E T) :=
    Scheme.proEtaleRingModules_hasKInjectiveResolutions T
      (completedIntegralCommRingSheafUnrestricted l E T)
  let b := reductionAugmentation l E T n
  let adjm := scalarReductionCoinductionAdjunction.{u} l E T n
  let Vc := (scalarReductionRestriction.{u, u} l E T n).mapHomologicalComplex (.up ℤ)
  let Cc := (scalarReductionCoinduction.{u} l E T n).mapHomologicalComplex (.up ℤ)
  let εX : Vc.obj (Cc.obj X) ⟶ X := (adjm.mapHomologicalComplex (.up ℤ)).counit.app X
  let tC := complexScalar (completedIntegralCommRingSheafUnrestricted l E T)
    (reductionScalarSection l E T n)
  have hε : εX⟦(-1 : ℤ)⟧' ≫ tC.app (X⟦(-1 : ℤ)⟧) = 0 := by
    ext i : 1
    exact counit_scalar_zero _ _ (reductionScalar_zero l E T n) adjm (X.X (i + -1))
  have hS : (ShortComplex.mk (εX⟦(-1 : ℤ)⟧') (tC.app (X⟦(-1 : ℤ)⟧)) hε).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact scalarReductionCoinduction_counit_shortExact l E T n (X.X (i + -1))
  let e := (shiftFunctorCompIsoId (CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    (-1 : ℤ) 1 (by omega)).app (Vc.obj (Cc.obj X))
  let w := (shiftFunctorCompIsoId (CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    (-1 : ℤ) 1 (by omega)).app X
  have he : e.hom ≫ εX = (εX⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫ w.hom :=
    ((shiftFunctorCompIsoId (CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      (-1 : ℤ) 1 (by omega)).hom.naturality εX).symm
  let γ : (scalarReductionDerivedCoinduction l E T n).obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj (Cc.obj X) :=
    (scalarReductionCoinduction.{u} l E T n).rightDerivedFunctorObjQIso X
  have hγ : b.V.map γ.inv ≫
      (reductionAugmentationCoinductionAdjunction l E T n).counit.app (DerivedCategory.Q.obj X) =
      b.restriction_factor.hom.app (Cc.obj X) ≫ DerivedCategory.Q.map εX := by
    have h1 :=
      CategoryTheory.Adjunction.mapDerivedCategory_map_rightDerivedFunctorObjQIso_inv_counit
        adjm X
    have h2 : (reductionAugmentationRestrictionIso l E T n).hom.app
        (DerivedCategory.Q.obj (Cc.obj X)) =
        b.restriction_factor.hom.app (Cc.obj X) ≫
          (scalarReductionRestriction.{u, u} l E T n).mapDerivedCategoryFactors.inv.app
            (Cc.obj X) := by
      simp [reductionAugmentationRestrictionIso, b, Localization.liftNatIso,
        Localization.liftNatTrans_app]
    have h3 := (reductionAugmentationRestrictionIso l E T n).hom.naturality γ.inv
    change b.V.map γ.inv ≫ ((reductionAugmentationRestrictionIso l E T n).hom.app _ ≫
      (scalarReductionDerivedCoinductionAdjunction l E T n).counit.app _) = _
    rw [← Category.assoc, h3, h2, Category.assoc, Category.assoc]
    erw [h1, Iso.inv_hom_id_app_assoc]
  exact b.isIso_coinductionTrace_app_of_shortExact (reductionScalar_zero l E T n)
    (reductionAugmentationCoinductionAdjunction l E T n) _ hε hS e w εX he γ hγ

/-- The normalized regular quotient trace is invertible on a complex with injective terms.
Source: Stacks Tags 06YY, 07A6, 0A70, 0BZE, 0BZH and 08FZ; the principal short exact
sequence of complexes and its cone-boundary/coinduction comparison.
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms).

Proof: a termwise-injective unbounded complex need not be K-injective, so first replace `I`
by its functorial K-injective resolution `I ⟶ R(I)` with injective terms (Stacks 079P); its
localization is an isomorphism and naturality of the trace reduces to `R(I)`. There derived
coinduction at `Q R(I)` is ordinary coinduction applied termwise. Apply the degreewise
injective short exact sequence to obtain a short exact sequence of complexes. Identify its
mapping-cone projection with the normalized cone boundary using the augmentation adjoint
formula, then transpose along the derived coinduction adjunction. The resulting component
is invertible after localization.
-/
theorem reductionCoinductionTrace_isIso_onInjectiveTerms
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (I : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    [∀ i : ℤ, Injective (I.X i)] :
    IsIso ((reductionCoinductionTrace.{u} l E T n).app (DerivedCategory.Q.obj I)) := by
  obtain ⟨_, _, Rf, η, h⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
      u + 1, u, u + 1} (Scheme.ProEt.topology T) (completedIntegralCommRingSheafUnrestricted l E T)
  obtain ⟨hq, hK, hinj⟩ := h I
  have : (Rf.obj I).IsKInjective := hK
  have : ∀ i : ℤ, Injective ((Rf.obj I).X i) := hinj
  exact (NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Q.map (η.app I)))).mpr
    (reductionCoinductionTrace_isIso_of_isKInjective_of_injective l E T n (Rf.obj I))

end WeilConjectures
