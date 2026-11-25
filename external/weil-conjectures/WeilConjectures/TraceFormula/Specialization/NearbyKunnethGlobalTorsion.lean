/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchangeFinite
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.OrdinaryKunnethResidueField
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidalTorsion
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorFiniteTransfer
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.Tactic.TransportExact

/-!

# Gabber's Künneth formula for nearby cycles: global sections with finite coefficients

Let `T` be a finite discrete commutative ring (for instance the residue field `𝔽_E`) and
`T̲ = C(-, T)` its condensed ring. This file proves the finite-coefficient form of the
global-sections step of Illusie's proof of Gabber's Künneth formula
(`NearbyCyclesModel.isIso_lowerStar_kunnethMap_of_isIso`): for the product `P` over the trait
`Spec k'⟦t⟧` of models `M`, `N` of finite type along proper structure morphisms, the direct image
`R(a_{P_s})_* Π_{A,B}` of the Künneth map of nearby cycles to the point `Spec k'` is an
isomorphism, given the ordinary Künneth formulas on the special and geometric generic fibres and
the Künneth map of the trait
(`NearbyCyclesModel.isIso_lowerStar_kunnethMap_finiteCoefficient`).

The three proper exchanges `χ` of the structure morphisms to the trait are invertible on
complexes bounded below of étale origin
(`IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app_finiteCoefficient`):
this is proper base change with finite coefficients
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`), which needs
no hypothesis on the characteristic.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-! ### The proper exchange with finite coefficients -/

section Exchange

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The proper exchange for the structure morphism, with finite coefficients** (blueprint
`prose-E-03` (2); SGA 7 XIII (2.1.7.1)): for a model `M` of finite type over
the trait `Spec k'⟦t⟧` along a proper `q`, the pushforward exchange
`χ : Ψ_S Rg_* K ⟶ R(q_s)_* Ψ_M K` of the structure morphism `(q, g) : M ⟶ S` is an isomorphism at
every complex `K` on the geometric generic fibre bounded below of étale origin. -/
theorem IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app_finiteCoefficient
    (h : M.IsTraitModelOver q g) [IsProper q]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) M.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) M.generic
      ((finiteCoefficientDerivedEquivalence M.generic T).functor.obj K)) :
    IsIso ((h.toTraitGeneric.pushforwardExchange (Profinite.continuousMapRingObj T)).app K) := by
  have : IsProper h.toTraitGeneric.total := ‹IsProper q›
  have : IsProper g := MorphismProperty.of_isPullback h.isPullback_j ‹IsProper q›
  have : QuasiCompact M.toGeneric.j :=
    MorphismProperty.of_isPullback h.isPullback_j.flip inferInstance
  have : QuasiSeparated M.toGeneric.j :=
    MorphismProperty.of_isPullback h.isPullback_j.flip inferInstance
  have : IsIso (traitGenericModel k').ε :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of (traitGenericField k')))))
  exact h.toTraitGeneric.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient T
    h.isPullback_i (IsPullback.of_horiz_isIso ⟨rfl⟩) K hK

end Exchange

/-! ### The global-sections step with finite coefficients -/

section Global

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed ring `T̲ = C(-, T)`. -/
local notation "𝐓" => Profinite.continuousMapRingObj T

-- the composite square identifying the direct image of the Künneth map has large terms
/-- **The global-sections step of Gabber's Künneth formula, with finite coefficients**: let `P`
be the product over the henselian trait `Spec k'⟦t⟧` of models `M`, `N` of finite type along
proper structure morphisms, with projections compatible with the structure morphisms to
`Spec Ω`. For complexes `A`, `B` whose restrictions `Lε^* A`, `Lε^* B` to the geometric generic
fibres, and the external product of these, are bounded below of étale origin, the direct image
`R(a_{P_s})_* Π_{A,B}` of the Künneth map of nearby cycles to the point `Spec k'` is an
isomorphism, given the ordinary Künneth formulas on the special and geometric generic fibres and
the Künneth map of the trait at `(RΓ(X_η̄, A), RΓ(Y_η̄, B))`. The proper exchanges are
`IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app_finiteCoefficient`. -/
theorem isIso_lowerStar_kunnethMap_finiteCoefficient (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj 𝐓 X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj 𝐓 Y)))
    (hA : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) M.generic
      ((finiteCoefficientDerivedEquivalence M.generic T).functor.obj (L((M.ε)^*⟦𝐓⟧).obj A)))
    (hB : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj (L((N.ε)^*⟦𝐓⟧).obj B)))
    (hAB : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) P.generic
      ((finiteCoefficientDerivedEquivalence P.generic T).functor.obj
        (L((φ₁.generic)^*⟦𝐓⟧).obj (L((M.ε)^*⟦𝐓⟧).obj A) ⊗
          L((φ₂.generic)^*⟦𝐓⟧).obj (L((N.ε)^*⟦𝐓⟧).obj B))))
    (hκs : IsIso (lowerStarKunnethMap' 𝐓
      (⟨(special_comp_hom_fst hM hP).trans (Category.comp_id _).symm⟩ :
        CommSq f₁' Z'.hom X'.hom (𝟙 _))
      (⟨(special_comp_hom_snd hN hpb hP).trans (Category.comp_id _).symm⟩ :
        CommSq f₂' Z'.hom Y'.hom (𝟙 _))
      ((M.toGeneric.nearbyCycles 𝐓).obj (L((M.ε)^*⟦𝐓⟧).obj A))
      ((N.toGeneric.nearbyCycles 𝐓).obj (L((N.ε)^*⟦𝐓⟧).obj B))))
    (hκΩ : IsIso (lowerStarKunnethMap' 𝐓
      (⟨(Category.comp_id _).symm⟩ : CommSq φ₁.generic (φ₁.generic ≫ gM) gM (𝟙 _))
      (⟨hgen.trans (Category.comp_id _).symm⟩ : CommSq φ₂.generic (φ₁.generic ≫ gM) gN (𝟙 _))
      (L((M.ε)^*⟦𝐓⟧).obj A) (L((N.ε)^*⟦𝐓⟧).obj B)))
    (hT : IsIso (kunnethMap 𝐓 (Hom.id (traitGenericModel k')) (Hom.id (traitGenericModel k'))
      (R((gM)_*⟦𝐓⟧).obj (L((M.ε)^*⟦𝐓⟧).obj A)) (R((gN)_*⟦𝐓⟧).obj (L((N.ε)^*⟦𝐓⟧).obj B)))) :
    IsIso (R((Z'.hom)_*⟦𝐓⟧).map (kunnethMap 𝐓 φ₁ φ₂ A B)) := by
  have : IsProper φ₁.total := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hχM := hM.isIso_pushforwardExchange_toTraitGeneric_app_finiteCoefficient T _ hA
  have hχN := hN.isIso_pushforwardExchange_toTraitGeneric_app_finiteCoefficient T _ hB
  have hχP := hP.isIso_pushforwardExchange_toTraitGeneric_app_finiteCoefficient T _ hAB
  refine isIso_lowerStar_kunnethMap_of_isIso 𝐓 hM hN hpb hP hgen A B ?_ ?_ ?_ hκs hκΩ hT
  · cast_proofs hχM
  · cast_proofs hχN
  · cast_proofs hχP

end Global

/-! ### Source and target of the Künneth map are of étale origin -/

section EtaleOrigin

variable {X Y Z X' Y' Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}
  {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj T) X))}
  {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj T) Y))}

/-- Over a finite field `T`, the source `Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B` of the Künneth map is
bounded below of étale origin if `A` and `B` are: nearby cycles and the external product
preserve complexes of étale origin. -/
theorem plusEtaleOrigin_kunnethMap_source (hT : IsField T) [QuasiCompact M.j]
    [QuasiSeparated M.j] [QuasiCompact N.j] [QuasiSeparated N.j]
    (hA : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj A))
    (hB : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y
      ((finiteCoefficientDerivedEquivalence Y T).functor.obj B)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Z'
      ((finiteCoefficientDerivedEquivalence Z' T).functor.obj
        (L((f₁')^*⟦Profinite.continuousMapRingObj T⟧).obj
            ((M.nearbyCycles (Profinite.continuousMapRingObj T)).obj A) ⊗
          L((f₂')^*⟦Profinite.continuousMapRingObj T⟧).obj
            ((N.nearbyCycles (Profinite.continuousMapRingObj T)).obj B))) :=
  ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj_leftDerivedUpperStar T
    hT f₁' f₂' (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_nearbyCycles_obj T M hA)
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_nearbyCycles_obj T N hB)

/-- Over a finite field `T`, the target `Ψ_P (Lf₁^* A ⊗ Lf₂^* B)` of the Künneth map is bounded
below of étale origin if `A` and `B` are. -/
theorem plusEtaleOrigin_kunnethMap_target (hT : IsField T) [QuasiCompact P.j]
    [QuasiSeparated P.j]
    (hA : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj A))
    (hB : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y
      ((finiteCoefficientDerivedEquivalence Y T).functor.obj B)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Z'
      ((finiteCoefficientDerivedEquivalence Z' T).functor.obj
        ((P.nearbyCycles (Profinite.continuousMapRingObj T)).obj
          (L((f₁)^*⟦Profinite.continuousMapRingObj T⟧).obj A ⊗
            L((f₂)^*⟦Profinite.continuousMapRingObj T⟧).obj B))) :=
  plusEtaleOrigin_finiteCoefficientDerivedEquivalence_nearbyCycles_obj T P
    (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj_leftDerivedUpperStar T
      hT f₁ f₂ hA hB)

end EtaleOrigin

/-! ### The global-sections step with coefficients `𝔽_E` -/

section ResidueField

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k' : Type u} [Field k']
  [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `𝔽̲_E`. -/
local notation "𝔽" => Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E.1)

-- the composite square identifying the direct image of the Künneth map has large terms
/-- **The global-sections step of Gabber's Künneth formula with coefficients `𝔽_E`** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, equation (4)): let `P` be the product over the
henselian trait `Spec k'⟦t⟧`, `k'` separably closed with `ℓ ≠ char k'`, of models `M`, `N` of finite
type along proper structure morphisms, with projections compatible with the structure morphisms to
`Spec Ω`. For bounded constructible complexes `A`, `B` of module objects over `𝔽̲_E`, the direct
image `R(a_{P_s})_* Π_{A,B}` of the Künneth map of nearby cycles to the point `Spec k'` is an
isomorphism. The inputs of `isIso_lowerStar_kunnethMap_finiteCoefficient` are the ordinary
Künneth formula with coefficients `𝔽_E` (`isIso_lowerStarKunnethMap'_of_isPullback_residueField`)
on the special and geometric generic fibres, at complexes of étale origin, and the Künneth
formula of the trait (`isIso_kunnethMap_traitGenericModel_residueField_lowerStar`). -/
theorem isIso_lowerStar_kunnethMap_residueField (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj 𝔽 X))} (hA : boundedConstructible (condensedRingObj 𝔽 X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj 𝔽 Y))} (hB : boundedConstructible (condensedRingObj 𝔽 Y) B) :
    IsIso (R((Z'.hom)_*⟦𝔽⟧).map (kunnethMap 𝔽 φ₁ φ₂ A B)) := by
  have hs₁ := special_comp_hom_fst hM hP
  have hs₂ := special_comp_hom_snd hN hpb hP
  have : LocallyOfFiniteType X'.hom := MorphismProperty.of_isPullback hM.isPullback_i
    hM.locallyOfFiniteType
  have : QuasiCompact X'.hom := MorphismProperty.of_isPullback hM.isPullback_i hM.quasiCompact
  have : LocallyOfFiniteType Y'.hom := MorphismProperty.of_isPullback hN.isPullback_i
    hN.locallyOfFiniteType
  have : QuasiCompact Y'.hom := MorphismProperty.of_isPullback hN.isPullback_i hN.quasiCompact
  have : LocallyOfFiniteType (Over.mk gM).hom := MorphismProperty.of_isPullback
    hM.isPullback_j hM.locallyOfFiniteType
  have : QuasiCompact (Over.mk gM).hom := MorphismProperty.of_isPullback hM.isPullback_j
    hM.quasiCompact
  have : LocallyOfFiniteType (Over.mk gN).hom := MorphismProperty.of_isPullback
    hN.isPullback_j hN.locallyOfFiniteType
  have : QuasiCompact (Over.mk gN).hom := MorphismProperty.of_isPullback hN.isPullback_j
    hN.quasiCompact
  have : IsSeparated gM := MorphismProperty.of_isPullback hM.isPullback_j hM.isSeparated
  have : IsSeparated gN := MorphismProperty.of_isPullback hN.isPullback_j hN.isSeparated
  have : LocallyOfFiniteType gM := ‹LocallyOfFiniteType (Over.mk gM).hom›
  have : QuasiCompact gM := ‹QuasiCompact (Over.mk gM).hom›
  have : LocallyOfFiniteType gN := ‹LocallyOfFiniteType (Over.mk gN).hom›
  have : QuasiCompact gN := ‹QuasiCompact (Over.mk gN).hom›
  have : QuasiCompact M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip inferInstance
  have : QuasiSeparated M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip inferInstance
  have : QuasiCompact N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip inferInstance
  have : QuasiSeparated N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip inferInstance
  have hfield : IsField (PadicAlgCl.integersResidueField ℓ E.1) := Field.toIsField _
  -- the complexes on the geometric generic fibres, and their nearby cycles, are of étale origin
  have hA' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A hA
  have hB' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ N.ε B hB
  have hAo := plusEtaleOrigin_of_boundedConstructible_residueField E hA'
  have hBo := plusEtaleOrigin_of_boundedConstructible_residueField E hB'
  have hABo :=
    ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj_leftDerivedUpperStar
    _ hfield φ₁.generic φ₂.generic hAo hBo
  have hΨA := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_nearbyCycles_obj _ M.toGeneric hAo
  have hΨB := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_nearbyCycles_obj _ N.toGeneric hBo
  -- the ordinary Künneth formulas and the Künneth formula of the trait
  have hκs := isIso_lowerStarKunnethMap'_of_isPullback_residueField ℓ E (X := X') (Y := Y')
    (P := Z') f₁' f₂' (hs₁.trans (Category.comp_id _).symm) (hs₂.trans (Category.comp_id _).symm)
    (isPullback_special hM hN hpb hP) _ hΨA _ hΨB
  have hκΩ := isIso_lowerStarKunnethMap'_of_isPullback_residueField ℓ E (X := Over.mk gM)
    (Y := Over.mk gN) (P := Over.mk (φ₁.generic ≫ gM)) φ₁.generic φ₂.generic
    (Category.comp_id _).symm (hgen.trans (Category.comp_id _).symm)
    (isPullback_generic hM hN hpb hP hgen) _ hAo _ hBo
  have hT := isIso_kunnethMap_traitGenericModel_residueField_lowerStar ℓ E.1 k' gM hA'
    (R((gN)_*⟦𝔽⟧).obj (L((N.ε)^*⟦𝔽⟧).obj B))
  refine isIso_lowerStar_kunnethMap_finiteCoefficient _ hM hN hpb hP hgen A B hAo hBo hABo ?_ ?_ ?_
  · transport_exact hκs
  · transport_exact hκΩ
  · transport_exact hT

end ResidueField

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
