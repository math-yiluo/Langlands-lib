/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethProper
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal

/-!

# Gabber's Künneth formula for proper models with `ℚ̄_ℓ`-coefficients, given the slices

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type along proper structure morphisms. If the generic-slicing step holds in chart dimension
`m + m' - 1` with `ℚ̄_ℓ`-coefficients (`NearbyCyclesModel.SliceKunnethFormula`), the Künneth map
`Π_{A,B}` is an isomorphism for bounded constructible `A`, `B`
(`NearbyCyclesModel.isIso_kunnethMap_padicAlgCl_of_isProper`): this is
`NearbyCyclesModel.isIso_kunnethMap_of_isProper`, whose remaining inputs are supplied here,
namely Deligne's finiteness theorem for the nearby cycles
(`NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`,
`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`), the monoidality of the nearby
cycles of the trait on the cohomology of the geometric generic fibres
(`NearbyCyclesModel.isIso_kunnethMap_traitGenericModel_of_shiftDecomposition`) and the detection
of complexes supported on finitely many closed points by their global sections
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`).

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

/-- **Gabber's Künneth formula for proper models, `ℚ̄_ℓ`-coefficients, given the slices**
(Illusie, *Autour du théorème de monodromie locale*, Thm. 4.7; blueprint
`proposition-external-kunneth-formula-nearby-cycles`): for the product `P` over the strictly
henselian trait of models `M`, `N` of finite type along proper structure morphisms whose total
spaces locally embed into `𝔸ᵐ_S`, `𝔸^{m'}_S`, if the generic-slicing step holds in chart dimension
`m + m' - 1`, the Künneth map `Π_{A,B}` is an isomorphism for bounded constructible `A`, `B`. -/
theorem isIso_kunnethMap_padicAlgCl_of_isProper [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {m m' : ℕ} (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B) := by
  have : LocallyOfFiniteType (Over.mk gM).hom := MorphismProperty.of_isPullback
    hM.isPullback_j hM.locallyOfFiniteType
  have : QuasiCompact (Over.mk gM).hom := MorphismProperty.of_isPullback hM.isPullback_j
    hM.quasiCompact
  have : IsSeparated (Over.mk gM).hom := MorphismProperty.of_isPullback hM.isPullback_j
    hM.isSeparated
  have : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of (traitGenericField k'))))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  have : QuasiCompact (Over.mk (𝟙 (Spec (.of (traitGenericField k'))))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 _))
  have : IsSeparated (Over.mk (𝟙 (Spec (.of (traitGenericField k'))))).hom :=
    inferInstanceAs (IsSeparated (𝟙 _))
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  have : IsSeparated Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.isSeparated
  have hΨA := preservesBoundedConstructible_of_isTraitModel M hM.isTraitModel ⟨eM, heM⟩ A hA
  have := hP.locallyOfFiniteType
  have := hP.quasiCompact
  have hΨB := preservesBoundedConstructible_of_isTraitModel N hN.isTraitModel ⟨eN, heN⟩ B hB
  have hpush := boundedConstructible_rightDerivedLowerStar_obj ℓ
    (Over.homMk (U := Over.mk gM) (V := Over.mk (𝟙 (Spec (.of (traitGenericField k'))))) gM
      (Category.comp_id _)) ⟨_, boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A hA⟩
  exact isIso_kunnethMap_of_isProper hM hN hpb hP hgen hm hm' hslice heM heN hA hB hΨA hΨB
    (boundedConstructible_kunnethMap_source hΨA hΨB)
    (boundedConstructible_kunnethMap_target (φ₁ := φ₁) (φ₂ := φ₂) (φ₁.total ≫ qM)
      (fun C₀ hC₀ ↦ boundedConstructible_geometricNearbyCycles_obj P hP.isTraitModel hC₀)
      heM heN hA hB)
    (isIso_kunnethMap_traitGenericModel_of_shiftDecomposition _ k' _ _
      (nonempty_shiftDecomposition_of_boundedConstructible ℓ _ hpush))
    (fun S hS C hC hU hΓ ↦ isZero_of_isZero_upperStar_finsetComplOpens ℓ S hS C hC hU hΓ)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
