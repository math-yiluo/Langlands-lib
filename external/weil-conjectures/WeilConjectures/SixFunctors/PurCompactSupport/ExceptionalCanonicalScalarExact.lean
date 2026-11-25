/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles

/-! # Exactness with the counit-normalized scalar shift -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
universe u
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] HasDerivedCategory.standard reductionDerivedChange

/-- Derived scalar extension is exact for the shift normalized by its universal counit.
Source: Stacks Tags 06XN and 05SE.
(blueprint: lem-sf-canonical-scalar-exact).

Proof: take the resolving class of homotopy objects where the scalar counit is
invertible. K-flat resolutions show that this class resolves every object. Naturality
of the counit shows that scalar extension inverts quasi-isomorphisms between objects
of this class. Its denominator diagrams are therefore essentially constant. The
shift-compatible Kan comparison maps every distinguished source triangle to a
distinguished triangle. Every distinguished triangle in the derived category is
isomorphic to such a source triangle, so exactness follows by transport. -/
theorem canonicalScalarExact {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedExtend φ).IsTriangulated := by
  classical
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let A := pbcModules T R
  let B := pbcModules T S
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let LF := pbcDerivedExtend φ
  let F := (pbcExtend φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let ε : Q ⋙ LF ⟶ F := pbcExtensionCounit φ
  have hLF : LF.IsRightKanExtension ε :=
    (pbcDerivedExtension_universal φ).isRightKanExtension
  have hε : ε.CommShift ℤ := (scalarCommShift_existsUnique φ).exists.choose_spec
  obtain ⟨hleft, hright, htri, hsat, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  have : W.HasRightCalculusOfFractions := hright
  have : W.HasLeftCalculusOfFractions := hleft
  have : W.HasTwoOutOfThreeProperty := htwo
  have hW : W.IsSaturatedTriangulatedMultiplicativeSystem :=
    ⟨⟨⟨hleft, hright⟩, fun _ _ _ _ h g f ↦ hsat _ _ _ _ g h f⟩, htri⟩
  let P : Set (HomotopyCategory A (.up ℤ)) := {K | IsIso (ε.app K)}
  have hres : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (K' : HomotopyCategory A (.up ℤ)) (s : K' ⟶ K), K' ∈ P ∧ W s := by
    intro K
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨K', s, hK', hs⟩ :=
      ScalarReductionDerivedProof.kFlatResolutions.{u + 1, u, u + 1}
        (J := ProEt.topology T) (O := R) G
    exact ⟨_, (HomotopyCategory.quotient _ _).map s,
      pbcExtensionCounit_isIso φ K' hK',
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ K K' (s : K ⟶ K'), K ∈ P → K' ∈ P → W s → IsIso (F.map s) := by
    intro K K' s hK hK' hs
    have : IsIso (ε.app K) := hK
    have : IsIso (ε.app K') := hK'
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    have : IsIso ((Q ⋙ LF).map s) := by dsimp only [Functor.comp_map]; infer_instance
    exact IsIso.of_isIso_fac_left (ε.naturality s).symm
  have hdefined : ∀ K, F.IsTriangulatedLeftDerivedDefinedAt W hW K := by
    intro K
    obtain ⟨Y, _, hc, _, _⟩ :=
      Functor.resolvingClass_essentialConstancy W F P hres hinv K
    exact ⟨Y, hc⟩
  have : (Q ⋙ LF).IsTriangulated := by
    constructor
    intro V hV
    exact Functor.leftDerived_kan_map_source_distinguished _ _ _ F W hW Q LF ε hLF
      hdefined hε V hV
  have := Localization.essSurj_mapArrow Q W
  constructor
  intro V hV
  obtain ⟨V₀, e, hV₀⟩ := (Q.distTriang_iff V).1 hV
  exact Pretriangulated.isomorphic_distinguished _
    ((Q ⋙ LF).map_distinguished V₀ hV₀) _
    (LF.mapTriangle.mapIso e ≪≫ (Functor.mapTriangleCompIso Q LF).symm.app V₀)

end WeilConjectures.PurCompactSupport
