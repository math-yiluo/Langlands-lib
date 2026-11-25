/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.OrdinaryCompactSupportCoefficientTransport
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitRestrictionAcyclicity
import WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Limit acyclicity of resolved coefficient systems

Source: Stacks Project, Tags 0940 and 0941; blueprint compact-support realization,
Step 11 (acyclicity part).
(blueprint: lem-pur-coefficient-restriction-limit-acyclicity). -/

@[expose] public noncomputable section
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CompactSupportCondensedRealization

open SheafOfModules.RestrictedTowerResolution

private theorem unit_isIso_of_acyclic
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ B) [G.Additive] (X : CochainComplex A ℤ)
    (hX : ∀ (J : CochainComplex A ℤ) [J.IsKInjective] (j : X ⟶ J) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    IsIso ((rightUnit G).app X) := by
  obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
  have := hj
  have := hX J j
  have hu : IsIso ((rightUnit G).app J) := by
    change IsIso (G.rightDerivedFunctorUnitQ J)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hi : IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have hh : DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j) ≫
      (rightUnit G).app J =
      (rightUnit G).app X ≫ G.rightDerivedFunctor.map (DerivedCategory.Q.map j) :=
    rightUnitApp_naturality G j
  have : IsIso ((rightUnit G).app X ≫ G.rightDerivedFunctor.map (DerivedCategory.Q.map j)) := by
    rw [← hh]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.rightDerivedFunctor.map (DerivedCategory.Q.map j))

/-- The underlying completed-coefficient towers of a K-injective system, including
its coefficient restriction, are acyclic for inverse limit.
Source: Stacks Project, Tags 0940, 0941 and 0D6E
(blueprint: lem-pur-coefficient-restriction-limit-acyclicity).
Proof: identify coefficient systems with strict systems using the exact vertical-slice
 equivalence. For the source field apply restricted-tower resolution acyclicity.
For the source completed ring acting on the target-field quotient system, compose
its completed coefficient map with the target projection cone. The generic restricted
system functor for this cone is termwise completed restriction of the target tower:
both the scalar actions and all transition maps agree. The supplied strict tower
comparison identifies this tower with restriction of the coefficient system followed
by source-field tower restriction. Apply the same generic acyclicity theorem over
this source completed ring. Naturality of the actual universal limit unit along a
K-injective tower resolution identifies it with an isomorphism, because inverse
limit sends that resolution map to a quasi-isomorphism. No preservation of
K-injective complexes by scalar restriction is asserted. -/
theorem coefficientRestrictionLimitAcyclicity
    (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    (e : systemRestriction l E F i W ⋙ coefficientSequenceRestriction.{u, u} l E W ≅
      coefficientSequenceRestriction.{u, u} l F W ⋙
        (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource.{u, u} l F W)
          (scalarReductionSource.{u, u} l E W)).obj
          (pbcRestrict (completedCoefficientMap.{u, u} l E F i W)))
    (I : CochainComplex (coefficientSequenceModules.{u, u} l F W) ℤ) [I.IsKInjective] :
    IsIso ((rightUnit (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l F W) ⥤
        scalarReductionSource.{u, u} l F W)).app
      (((coefficientSequenceRestriction.{u, u} l F W).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    IsIso ((rightUnit (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ⥤
        scalarReductionSource.{u, u} l E W)).app
      (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj
        (((systemRestriction l E F i W).mapHomologicalComplex (.up ℤ)).obj I))) := by
  constructor
  · apply unit_isIso_of_acyclic
    intro J hJ j hj
    exact CompletionUnit.restricted_limit_acyclic.{u, u} l F W I J j
  let A := completedIntegralCommRingSheafUnrestricted.{u, u} l F W
  let A' := completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  let B := coefficientSequenceCommRingSystem.{u, u} l F W
  let c := completedCoefficientMap.{u, u} l E F i W
  let α := CompletionUnit.coefficientCone.{u, u} l F W
  let α' : (Functor.const ℕᵒᵖ).obj A' ⟶ B := (Functor.const ℕᵒᵖ).map c ≫ α
  let eqv := CompletionUnit.strictEquivalence.{u, u} l F W
  let U := SheafOfModules.RestrictedTowerResolution.restrictionFunctor A B α
  let U' := SheafOfModules.RestrictedTowerResolution.restrictionFunctor A' B α'
  let R := (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource.{u, u} l F W)
    (scalarReductionSource.{u, u} l E W)).obj (pbcRestrict c)
  let h : U' ≅ U ⋙ R := NatIso.ofComponents (fun M ↦
    NatIso.ofComponents (fun n ↦
      (SheafOfModules.systemScalarRestrictionComposition c (α.app n)
        (α'.app n) rfl).symm.app (M.level n.unop))
      (by intro n m f; ext V x; rfl))
      (by intro M N f; ext n V x; rfl)
  have heq : eqv.functor ⋙ U = coefficientSequenceRestriction.{u, u} l F W :=
    CompletionUnit.restriction_as_strict.{u, u} l F W
  let h' : eqv.functor ⋙ U' ≅
      systemRestriction l E F i W ⋙ coefficientSequenceRestriction.{u, u} l E W :=
    Functor.isoWhiskerLeft eqv.functor h ≪≫
      Functor.isoWhiskerRight (eqToIso heq) R ≪≫ e.symm
  let I' := (eqv.functor.mapHomologicalComplex (.up ℤ)).obj I
  have hI' : CochainComplex.IsKInjective I' := inferInstance
  let : (coefficientSequenceRestriction.{u, u} l E W).Additive :=
    coefficientSequenceRestriction_additive l E W
  let : (systemRestriction l E F i W).Additive := by
    change (SemilinearSections.res _).Additive
    infer_instance
  let : (systemRestriction l E F i W ⋙
      coefficientSequenceRestriction.{u, u} l E W).Additive := inferInstance
  let hI := (NatIso.mapHomologicalComplex h' (.up ℤ)).app I
  apply unit_isIso_of_acyclic
  intro J hJ j hj
  let hsite : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} W.ProEt
  let hSh : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    @SheafOfModules.hasSheafify_coefficientUniverse W.ProEt _ hsite (ProEt.topology W)
  let hL : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    @SheafOfModules.wEqualsLocallyBijective_coefficientUniverse W.ProEt _ hsite
      (ProEt.topology W)
  let hcomp : (ProEt.topology W).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let hD := scalarReductionSourceDerived.{u, u} l E W
  have hh := (@acyclicity.{u + 1, u, u + 1, u + 2} W.ProEt inferInstance (ProEt.topology W)
    hsite hcomp hL hSh A' B α' hD I' I' (𝟙 I') inferInstance hI' J
    (hI.hom ≫ j) inferInstance hJ).1
  have hc : QuasiIso (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ⥤ _).mapHomologicalComplex
      (.up ℤ)).map hI.hom ≫
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ⥤ _).mapHomologicalComplex
      (.up ℤ)).map j) := by
    simpa only [Functor.map_comp] using hh
  exact (quasiIso_iff_comp_left _ _).1 hc

end WeilConjectures.CompactSupportCondensedRealization
