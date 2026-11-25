/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralFlat

/-!
# Flatness of `ℚ̄_ℓ,X` over `ℤ`

Let `ℓ` be a prime and `X` a scheme. The coefficient ring object `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ` on
`X_proét` is a flat abelian sheaf: tensoring with it is exact
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_tensorLeft_padicAlgClRingObj`).

Indeed `ℚ̄_ℓ,X = colim_E E_X` is a filtered colimit over the finite subextensions `E`
(`AlgebraicGeometry.ProEtale.isColimitPadicAlgClRingObjCocone`), each `E_X` is flat over `ℤ`
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_tensorLeft_continuousMapRingObj`), the tensor
product commutes with colimits, and filtered colimits of abelian sheaves are exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Tensoring with `ℚ̄_ℓ,X` preserves monomorphisms: `ℚ̄_ℓ,X ⊗ g` is the filtered colimit of the
monomorphisms `E_X ⊗ g`. -/
instance preservesMonomorphisms_tensorLeft_padicAlgClRingObj :
    (tensorLeft (padicAlgClRingObj X ℓ)).PreservesMonomorphisms where
  preserves {A B} g _ := by
    have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
    have (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
        PreservesColimitsOfSize.{0, 0} (tensorRight Z) :=
      preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Z)
    let hA := isColimitOfPreserves (tensorRight A) (isColimitPadicAlgClRingObjCocone X ℓ)
    let hB := isColimitOfPreserves (tensorRight B) (isColimitPadicAlgClRingObjCocone X ℓ)
    let α : Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X ⋙ tensorRight A ⟶
        Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X ⋙ tensorRight B :=
      Functor.whiskerLeft (Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X)
        ((tensoringRight _).map g)
    have (E : PadicAlgCl.FiniteIntermediateField ℓ) : Mono (α.app E) :=
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj E.1) X)).map_mono g
    have : Mono α := NatTrans.mono_of_mono_app α
    have heq : padicAlgClRingObj X ℓ ◁ g =
        (hA.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫ colimMap α ≫
          (hB.coconePointUniqueUpToIso (colimit.isColimit _)).inv := hA.hom_ext fun E ↦ by
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc, colimit.cocone_ι, ι_colimMap_assoc,
        ← colimit.cocone_ι, IsColimit.comp_coconePointUniqueUpToIso_inv]
      exact (whisker_exchange ((padicAlgClRingObjCocone X ℓ).ι.app E) g).symm
    have : Mono (colimMap α) := colim.map_mono _
    change Mono (padicAlgClRingObj X ℓ ◁ g)
    rw [heq]
    infer_instance

/-- **`ℚ̄_ℓ,X` is flat over `ℤ`**: tensoring with `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ` is exact. -/
instance preservesFiniteLimits_tensorLeft_padicAlgClRingObj :
    PreservesFiniteLimits (tensorLeft (padicAlgClRingObj X ℓ)) :=
  preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

end AlgebraicGeometry.ProEtale
