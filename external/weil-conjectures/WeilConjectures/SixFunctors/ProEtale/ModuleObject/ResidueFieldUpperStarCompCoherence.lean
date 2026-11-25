/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldUpperStarCompForget

/-!
# Residue field module sheaves and the composition of pullbacks

The isomorphisms `ProEtale.residueFieldModuleSheafUpperStarIso` are compatible with the
composition isomorphisms of the pullbacks of module objects over `𝔽_E` and of pro-étale sheaves of
`𝔽_E`-modules (`ProEtale.residueFieldModuleSheafUpperStarIso_compCoherence`). This is checked on
underlying abelian sheaves, where it follows from the corresponding compatibilities of
`ProEtale.CondensedRing.upperStarForgetIso` and `ProEtale.sheafComposeForget₂CompUpperStarIso`.

## Implementation notes

As in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafComparison`, the
statement is first proved for the commutative-ring form of `C(-, 𝔽_E)`, and then transported
to the usual form as a whole, through the predicate `CategoryTheory.CompCoherence`: kernel checks
comparing objects `(a)^*⟦Λ⟧.obj M` for the two forms time out, while comparing the functors and
isomorphisms themselves is cheap.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

section Aux

attribute [local instance high] isTopologicalRing_residueField

set_option hygiene false in
local notation "residueFieldCommRingObj" =>
  @Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E) _ CommRing.toRing _

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- On underlying abelian sheaves, `residueFieldModuleSheafUpperStarIsoAux` is the composite of
the identifications of the underlying sheaves of residue field module sheaves, of pullbacks of
module objects and of pullbacks of sheaves of modules. -/
lemma sheafCompose_map_residueFieldModuleSheafUpperStarIsoAux_hom_app' {A B : Scheme.{u}}
    (a : A ⟶ B)
    (M : Mod (Sheaf (ProEt.topology B) Ab.{u + 1})
      (condensedRingObj (residueFieldCommRingObj) B)) :
    (sheafCompose (ProEt.topology A)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        ((residueFieldModuleSheafUpperStarIsoAux ℓ E a).hom.app M) =
      (residueFieldModuleSheafCompForgetIso A).hom.app
          ((a)^*⟦residueFieldCommRingObj⟧.obj M) ≫
        (upperStarForgetIso (residueFieldCommRingObj) a).inv.app M ≫
        (a)^*[Ab.{u + 1}].map ((residueFieldModuleSheafCompForgetIso B).inv.app M) ≫
        (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a).hom.app
          ((residueFieldModuleSheaf B ℓ E).obj M) := by
  refine (sheafCompose_map_residueFieldModuleSheafUpperStarIsoAux_hom_app ℓ E a M).trans ?_
  simp [residueFieldModuleSheafUpperStarForgetIso]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- `residueFieldModuleSheafUpperStarIsoAux` is compatible with the composition isomorphisms. -/
theorem residueFieldModuleSheafUpperStarIsoAux_compCoherence {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    CompCoherence (CondensedRing.upperStarComp (residueFieldCommRingObj) f g)
      (ProEtale.upperStarComp (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f g)
      (residueFieldModuleSheafUpperStarIsoAux ℓ E g) (residueFieldModuleSheafUpperStarIsoAux ℓ E f)
      (residueFieldModuleSheafUpperStarIsoAux ℓ E (f ≫ g)) :=
  compCoherence_of_faithful (residueFieldModuleSheafCompForgetIso Z)
    (residueFieldModuleSheafCompForgetIso Y) (residueFieldModuleSheafCompForgetIso X)
    (upperStarForgetIso (residueFieldCommRingObj) g)
    (upperStarForgetIso (residueFieldCommRingObj) f)
    (upperStarForgetIso (residueFieldCommRingObj) (f ≫ g))
    (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) g)
    (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) f)
    (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) (f ≫ g))
    _ _ (ProEtale.upperStarComp Ab.{u + 1} f g)
    (upperStarComp_hom_app_upperStarForgetIso (residueFieldCommRingObj) f g)
    (sheafComposeForget₂CompUpperStarIso_hom_app_comp (ResidueFieldCoeff.{u} ℓ E) f g)
    _ _ _
    (sheafCompose_map_residueFieldModuleSheafUpperStarIsoAux_hom_app' ℓ E g)
    (sheafCompose_map_residueFieldModuleSheafUpperStarIsoAux_hom_app' ℓ E f)
    (sheafCompose_map_residueFieldModuleSheafUpperStarIsoAux_hom_app' ℓ E (f ≫ g))

end Aux

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **The isomorphisms `residueFieldModuleSheafUpperStarIso` are compatible with the composition
isomorphisms** of the pullbacks of module objects over `𝔽_E` and of pro-étale sheaves of
`𝔽_E`-modules. -/
theorem residueFieldModuleSheafUpperStarIso_compCoherence {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    CompCoherence
      (CondensedRing.upperStarComp
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f g)
      (ProEtale.upperStarComp (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f g)
      (residueFieldModuleSheafUpperStarIso ℓ E g) (residueFieldModuleSheafUpperStarIso ℓ E f)
      (residueFieldModuleSheafUpperStarIso ℓ E (f ≫ g)) :=
  residueFieldModuleSheafUpperStarIsoAux_compCoherence ℓ E f g

end AlgebraicGeometry.ProEtale
