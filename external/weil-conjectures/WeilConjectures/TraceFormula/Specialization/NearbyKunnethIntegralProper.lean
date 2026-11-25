/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangePadicAlgClIff
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionRationalIsIso
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethRational
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethResidueFieldProper

/-!

# Gabber's Künneth formula for proper models with `𝒪_E`-coefficients

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type along proper structure morphisms, whose total spaces locally embed into `𝔸ᵐ_S`,
`𝔸^{m'}_S`, and `E ⊆ ℚ̄_ℓ` finite with ring of integers `𝒪_E` and residue field `𝔽_E`. If the
generic-slicing step holds in chart dimension `m + m' - 1` with `𝒪_E`-coefficients for every `E`
and with `ℚ̄_ℓ`-coefficients, the Künneth map `Π_{A,B}` with `𝒪_E`-coefficients is an isomorphism
for bounded constructible `A`, `B`
(`NearbyCyclesModel.isIso_kunnethMap_padicIntegers_of_isProper`). By the conservativity of the
reduction and the rationalization
(`ProEtale.CondensedRing.isIso_of_isIso_extendScalars_residueField_padicAlgCl`), it suffices that
* its reduction `𝔽_E ⊗ᴸ Π_{A,B}` is invertible: it is the Künneth map of the reductions
  (`NearbyCyclesModel.isIso_map_kunnethMap_iff_residueField`), invertible by
  `NearbyCyclesModel.isIso_kunnethMap_residueField_of_isProper`;
* its rationalization `ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Π_{A,B}` is invertible: it is the Künneth map of the
  rationalizations (`NearbyCyclesModel.isIso_map_map_kunnethMap_iff_padicAlgCl`), which are
  bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_extendScalars_padicAlgCl_obj`),
  invertible by `NearbyCyclesModel.isIso_kunnethMap_padicAlgCl_of_isProper`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **Gabber's Künneth formula for proper models with `𝒪_E`-coefficients** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`; Illusie, *Autour du théorème de monodromie
locale*, proof of Thm. 4.7): for the product `P` over the strictly henselian trait of models `M`,
`N` of finite type along proper structure morphisms, whose total spaces locally embed into `𝔸ᵐ_S`,
`𝔸^{m'}_S`, if the generic-slicing step holds in chart dimension `m + m' - 1` with
`𝒪_E`-coefficients for every `E` and with `ℚ̄_ℓ`-coefficients, the Künneth map `Π_{A,B}` of bounded
constructible `𝒪_E`-complexes `A`, `B` on noetherian `X`, `Y` is an isomorphism.

This is the cone argument: the cone of `Π_{A,B}` has vanishing reduction and rationalization
(`ProEtale.CondensedRing.isIso_of_isIso_extendScalars_residueField_padicAlgCl`), since the
reduction `𝔽_E ⊗ᴸ Π_{A,B}` and the rationalization `ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Π_{A,B}` are the
Künneth maps of the reductions and of the rationalizations of `A`, `B`, invertible by
`NearbyCyclesModel.isIso_kunnethMap_residueField_of_isProper` and
`NearbyCyclesModel.isIso_kunnethMap_padicAlgCl_of_isProper`. -/
theorem isIso_kunnethMap_padicIntegers_of_isProper [IsNoetherian X] [IsNoetherian Y]
    [TopologicalSpace.NoetherianSpace Z] (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {m m' : ℕ} (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' (m + m' - 1))
    (hsliceQ : 0 < m + m' → SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y) B) :
    IsIso (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A B) := by
  have : TopologicalSpace.NoetherianSpace X := inferInstance
  have : TopologicalSpace.NoetherianSpace Y := inferInstance
  have hqc : QuasiCompact (traitGenericPoint k') := inferInstance
  have hqs : QuasiSeparated (traitGenericPoint k') := inferInstance
  have : QuasiCompact M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip hqc
  have : QuasiSeparated M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip hqs
  have : QuasiCompact N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip hqc
  have : QuasiSeparated N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip hqs
  have : QuasiCompact P.j := MorphismProperty.of_isPullback hP.isPullback_j.flip hqc
  have : QuasiSeparated P.j := MorphismProperty.of_isPullback hP.isPullback_j.flip hqs
  -- bounds below of `A`, `B` and of their external product
  have ha : A.IsGE hA.1.1.choose := hA.1.1.choose_spec
  have ha' : B.IsGE hB.1.1.choose := hB.1.1.choose_spec
  have : A.IsGE (min hA.1.1.choose hB.1.1.choose) :=
    DerivedCategory.TStructure.t.isGE_of_ge A _ _ (min_le_left _ _)
  have : B.IsGE (min hA.1.1.choose hB.1.1.choose) :=
    DerivedCategory.TStructure.t.isGE_of_ge B _ _ (min_le_right _ _)
  have hAB : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)
      (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A ⊗
        L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B) :=
    boundedConstructible_tensorObj
      (PadicIntegersRingObj.lisseHypotheses ℓ E.1).toLisseTensorHypotheses
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₁ A hA)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₂ B hB)
  have hc : (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B).IsGE hAB.1.1.choose :=
    hAB.1.1.choose_spec
  refine isIso_of_isIso_extendScalars_residueField_padicAlgCl ℓ E (X := Z'.left) _ ?_ ?_
  · exact (isIso_map_kunnethMap_iff_residueField ℓ E φ₁ φ₂ A B
      (min hA.1.1.choose hB.1.1.choose) hAB.1.1.choose).2
      (isIso_kunnethMap_residueField_of_isProper E hM hN hpb hP hgen hm hm'
        (fun h ↦ hslice h E) heM heN hA hB)
  · exact (isIso_map_map_kunnethMap_iff_padicAlgCl ℓ E φ₁ φ₂ A B
      (min hA.1.1.choose hB.1.1.choose) hAB.1.1.choose).2
      (isIso_kunnethMap_padicAlgCl_of_isProper hM hN hpb hP hgen hm hm' hsliceQ heM heN
        (boundedConstructible_extendScalars_padicAlgCl_obj ℓ E hA)
        (boundedConstructible_extendScalars_padicAlgCl_obj ℓ E hB))

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
