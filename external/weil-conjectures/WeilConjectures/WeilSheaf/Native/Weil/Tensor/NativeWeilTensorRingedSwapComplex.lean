/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedComplexes

/-! # The native chain swap obtained from the ringed signed swap

Source: Stacks 06YU and 0FPT, signed total tensor symmetry.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
-- Keep the large sheaf monoidal constructions behind their public APIs.
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)

/-- Transport the signed ringed chain swap through the explicit total comparisons.
Source: Stacks 06YU and 0FPT.
(blueprint: new-sf-native-weil-ringed-swap-complex).

The additive equivalence is fully faithful on complexes. Its preimage of this
specified composite is therefore a real construction, with no existence choice. -/
def nativeRingedSwapComplex
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    CochainComplex.mapBifunctor Q P T ≅ CochainComplex.mapBifunctor P Q T := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  letI := SheafOfModules.symmetricCategory b.R
  let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
  exact Ec.preimageIso (A.chain Q P ≪≫
    (CochainComplex.Monoidal.braiding (Ec.obj P) (Ec.obj Q)) ≪≫ (A.chain P Q).symm)

/-- The native chain swap satisfies its defining ringed comparison square.
Source: full faithfulness and cancellation, applied to the signed swap of Stacks 0FPT.
(blueprint: new-sf-native-weil-ringed-swap-complex).

Proof: map the full-faithful preimage, expand the composite isomorphism, and cancel
its last inverse against the comparison on the left-hand side. -/
theorem nativeRingedSwapComplex_square
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SheafOfModules.symmetricCategory b.R
    let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
    Ec.map (nativeRingedSwapComplex b T adj A P Q).hom ≫ (A.chain P Q).hom =
      (A.chain Q P).hom ≫ (CochainComplex.Monoidal.braiding (Ec.obj P) (Ec.obj Q)).hom := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  letI := SheafOfModules.symmetricCategory b.R
  simp only [nativeRingedSwapComplex, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.ProEtaleWeilSheaf
