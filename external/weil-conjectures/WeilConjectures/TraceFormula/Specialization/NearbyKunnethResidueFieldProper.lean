/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeResidueIff
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedPointsDetection
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobalTorsion
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlicePoints
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ResidueFieldEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseHypotheses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!

# The Künneth map of proper models modulo `ϖ`

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type along proper structure morphisms, `E ⊆ ℚ̄_ℓ` finite with residue field `𝔽_E`, and
`A₀`, `B₀` bounded constructible `𝒪_E`-complexes. If the generic-slicing step holds with
`𝒪_E`-coefficients in chart dimension `m + m' - 1`, the Künneth map with `𝔽_E`-coefficients of
the reductions `𝔽_E ⊗ᴸ A₀`, `𝔽_E ⊗ᴸ B₀` is an isomorphism
(`NearbyCyclesModel.isIso_kunnethMap_residueField_of_isProper`). This is the closed-point
criterion (`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`) on the
special fibre `X_s × Y_s`, a scheme of finite type over the separably closed field `k'`:
* the source and the target of the Künneth map are bounded below of étale origin
  (`NearbyCyclesModel.plusEtaleOrigin_kunnethMap_source`,
  `NearbyCyclesModel.plusEtaleOrigin_kunnethMap_target`);
* every non-closed point is reached by a generic slice along which the pullback of the `𝒪_E`
  Künneth map, hence of its reduction, is invertible
  (`NearbyCyclesModel.exists_isIso_map_kunnethMap_of_not_isClosed`,
  `NearbyCyclesModel.isIso_map_map_kunnethMap_iff_residueField`);
* its global sections are invertible (`NearbyCyclesModel.isIso_lowerStar_kunnethMap_residueField`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k' : Type u}
  [Field k'] [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `𝔽̲_E`. -/
local notation "𝔽" => Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E.1)

set_option hygiene false in
/-- The condensed ring `𝒪̲_E`. -/
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

-- the Künneth maps of the product are large terms
/-- **Gabber's Künneth formula for proper models, modulo `ϖ`** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`; Illusie, *Autour du théorème de monodromie
locale*, proof of Thm. 4.7): for the product `P` over the strictly henselian trait of models `M`,
`N` of finite type along proper structure morphisms, whose total spaces locally embed into `𝔸ᵐ_S`,
`𝔸^{m'}_S`, if the generic-slicing step holds with `𝒪_E`-coefficients in chart dimension
`m + m' - 1`, then for bounded constructible `𝒪_E`-complexes `A₀`, `B₀` on noetherian `X`, `Y` the
Künneth map of the reductions `𝔽_E ⊗ᴸ A₀`, `𝔽_E ⊗ᴸ B₀` is an isomorphism. -/
theorem isIso_kunnethMap_residueField_of_isProper [IsNoetherian X] [IsNoetherian Y]
    [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {m m' : ℕ} (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula 𝒪 k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj 𝒪 X))} (hA₀ : boundedConstructible (condensedRingObj 𝒪 X) A₀)
    {B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj 𝒪 Y))} (hB₀ : boundedConstructible (condensedRingObj 𝒪 Y) B₀) :
    IsIso (kunnethMap 𝔽 φ₁ φ₂
      ((Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj A₀)
      ((Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) Y)).leftDerivedFunctor.obj B₀)) := by
  have : TopologicalSpace.NoetherianSpace X := inferInstance
  have : TopologicalSpace.NoetherianSpace Y := inferInstance
  have ha : A₀.IsGE hA₀.1.1.choose := hA₀.1.1.choose_spec
  have ha' : B₀.IsGE hB₀.1.1.choose := hB₀.1.1.choose_spec
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : QuasiCompact M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip inferInstance
  have : QuasiSeparated M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip inferInstance
  have : QuasiCompact N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip inferInstance
  have : QuasiSeparated N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip inferInstance
  have : QuasiCompact P.j := MorphismProperty.of_isPullback hP.isPullback_j.flip inferInstance
  have : QuasiSeparated P.j := MorphismProperty.of_isPullback hP.isPullback_j.flip inferInstance
  have hT : IsField (PadicAlgCl.integersResidueField ℓ E.1) := Field.toIsField _
  have hAe := plusEtaleOrigin_extendScalars_residueField_of_boundedConstructible E hA₀
  have hBe := plusEtaleOrigin_extendScalars_residueField_of_boundedConstructible E hB₀
  -- bounds below of `A₀`, `B₀` and of their external product
  have : A₀.IsGE (min hA₀.1.1.choose hB₀.1.1.choose) :=
    DerivedCategory.TStructure.t.isGE_of_ge A₀ _ _ (min_le_left _ _)
  have : B₀.IsGE (min hA₀.1.1.choose hB₀.1.1.choose) :=
    DerivedCategory.TStructure.t.isGE_of_ge B₀ _ _ (min_le_right _ _)
  -- Infer the external product from the preservation lemmas to reuse its derived tensor structure.
  have hAB := boundedConstructible_tensorObj
    (PadicIntegersRingObj.lisseHypotheses ℓ E.1).toLisseTensorHypotheses
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₁ A₀ hA₀)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₂ B₀ hB₀)
  refine hAB.1.1.elim fun c hc ↦ ?_
  -- its global sections are invertible
  have hΓ := isIso_lowerStar_kunnethMap_residueField ℓ E hM hN hpb hP hgen
    (boundedConstructible_derivedExtendScalars_residueField X ℓ E.1 A₀ hA₀)
    (boundedConstructible_derivedExtendScalars_residueField Y ℓ E.1 B₀ hB₀)
  have hs := plusEtaleOrigin_kunnethMap_source _ (M := M) (N := N) (f₁' := f₁') (f₂' := f₂')
    hT hAe hBe
  have ht := plusEtaleOrigin_kunnethMap_target _ (P := P) (f₁ := f₁) (f₂ := f₂) hT hAe hBe
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed _ Z'.hom _ hs ht ?_ hΓ
  -- the pullback of the Künneth map to a non-closed point is invertible by generic slicing
  intro z hz
  have key := exists_isIso_map_kunnethMap_of_not_isClosed 𝒪 (M := M) (N := N) (P := P)
    (φ₁ := φ₁) (φ₂ := φ₂) (A := A₀) (B := B₀) hM hN hpb hP hgen hm hm' hslice heM heN hA₀ hB₀ z hz
  refine key.imp fun W ↦ Exists.imp fun h ↦ Exists.imp fun w hw ↦ ⟨hw.1, ?_⟩
  have := hw.2
  exact (isIso_map_map_kunnethMap_iff_residueField ℓ E φ₁ φ₂ h A₀ B₀
    (min hA₀.1.1.choose hB₀.1.1.choose) c).1 (Functor.map_isIso _ _)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
