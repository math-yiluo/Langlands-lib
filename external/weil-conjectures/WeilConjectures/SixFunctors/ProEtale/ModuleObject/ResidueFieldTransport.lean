/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# Residue field module sheaves and the finite-coefficient comparison

Let `X` be a scheme and `𝔽_E` the residue field of the ring of integers of a finite subextension
`E ⊆ ℚ̄_ℓ`. The residue field `𝔽_E` is finite (`PadicAlgCl.finite_integersResidueField`), so
module objects over `𝔽_{E,X} = p_X^* 𝔽̲_E` are the pro-étale sheaves of `𝔽_E`-modules through the
equivalence `ProEtale.finiteCoefficientModEquivalence`, which keeps the underlying abelian
sheaves.

We show that `ProEtale.residueFieldModuleSheaf X ℓ E` is isomorphic to the functor of this
equivalence, hence is itself an equivalence, as soon as the constant global sections of
`𝔽_{E,X}` used to define it (`ProEtale.residueFieldSectionRingHom`) are the images under `p_X^*`
of the constant global sections of `𝔽̲_E` (`ProEtale.ResidueFieldSectionFac`):
`ProEtale.residueFieldModuleSheafIsoOfSection` and
`ProEtale.isEquivalence_residueFieldModuleSheaf_of_section`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- For `E` finite over `ℚ_ℓ`, the residue field `𝔽_E` is finite: it is the image of the compact
space `𝒪_E` under the continuous residue map to a discrete space. -/
instance finite_integersResidueField [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] : Finite (integersResidueField ℓ E) := by
  let := normedFieldOfAlgebra ℓ E
  have := compactSpace_integers ℓ E
  rw [← Set.finite_univ_iff, ← (integersResidue_surjective ℓ E).range_eq]
  exact (isCompact_range (continuous_integersResidue ℓ E)).finite_of_discrete

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The constant global section `c` of `𝔽_{E,X}` defining `ProEtale.residueFieldModuleSheaf` is
the image under `p_X^*` of the constant global section `c` of the condensed ring `𝔽̲_E`. -/
def ResidueFieldSectionFac : Prop :=
  ∀ c : ResidueFieldCoeff.{u} ℓ E, (residueFieldSectionRingHom X ℓ E c).hom =
    ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map
      (Profinite.continuousMapConstRingHom.{u} (integersResidueField ℓ E) (ULift.down c)).hom

variable {X ℓ E} in
/-- Under `ProEtale.ResidueFieldSectionFac`, the action of `c` on `residueFieldModuleSheaf X ℓ E`
is that on the sheaf of `𝔽_E`-modules given by `finiteCoefficientModEquivalence`. -/
lemma sectionActRingHom_residueFieldSectionRingHom_of_fac (h : ResidueFieldSectionFac X ℓ E)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E))
    (c : ResidueFieldCoeff.{u} ℓ E) :
    (Mod.sectionActRingHom M (residueFieldSectionRingHom X ℓ E c)).asHom =
      (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        (Sheaf.smulEnd
          ((finiteCoefficientModEquivalence X (integersResidueField ℓ E)).functor.obj M) c) := by
  change (_ : M.X ⟶ M.X) = _
  ext U y
  refine Eq.trans ?_
    (finiteCoefficientModEquivalence_smul X (integersResidueField ℓ E) M U (ULift.down c) y).symm
  rw [Mod.sectionActRingHom_apply, h c]
  rfl

/-- Under `ProEtale.ResidueFieldSectionFac`, `residueFieldModuleSheaf X ℓ E` is the functor of the
equivalence `finiteCoefficientModEquivalence` between module objects over `𝔽_{E,X}` and sheaves
of `𝔽_E`-modules. -/
noncomputable def residueFieldModuleSheafIsoOfSection (h : ResidueFieldSectionFac X ℓ E) :
    residueFieldModuleSheaf X ℓ E ≅
      (finiteCoefficientModEquivalence X (integersResidueField ℓ E)).functor :=
  Sheaf.isoOfSheafComposeForget₂ (Λ := ResidueFieldCoeff.{u} ℓ E)
    (P := residueFieldModuleSheaf X ℓ E)
    (Q := (finiteCoefficientModEquivalence X (integersResidueField ℓ E)).functor)
    (residueFieldModuleSheafCompForgetIso X) fun M c ↦ by
    rw [sheafCompose_map_smulEnd_comp_residueFieldModuleSheafCompForgetIso_hom_app,
      sectionActRingHom_residueFieldSectionRingHom_of_fac h]

/-- Under `ProEtale.ResidueFieldSectionFac`, `residueFieldModuleSheaf X ℓ E` is an equivalence of
categories. -/
lemma isEquivalence_residueFieldModuleSheaf_of_section (h : ResidueFieldSectionFac X ℓ E) :
    (residueFieldModuleSheaf X ℓ E).IsEquivalence :=
  Functor.isEquivalence_of_iso (residueFieldModuleSheafIsoOfSection X ℓ E h).symm

end AlgebraicGeometry.ProEtale
