/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitBallRingObj.BoundedConstructibleTensorSingle
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-! # BoundedConstructibleTensorPreservation

The tensor unit and the two finite truncation inductions for tensor closure.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The coefficient object is bounded constructible and is the tensor unit. This is the unit
clause needed to form the monoidal bounded-constructible subcategory.
Source: the unit clause of `proposition-six-operations-dctf--14` in the blueprint.
(blueprint: lem-sfb-dc-tensor-unit) -/
theorem boundedConstructible_tensor_unit :
    boundedConstructible (condensedRingObj Λ X.left)
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left)))) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)
  let U := (𝟙_ (DerivedCategory C))
  let eUnit : (DerivedCategory.singleFunctor C 0).obj (𝟙_ C) ≅ U :=
    DerivedCategory.singleFunctorObjUnitIso C
  have eb : DerivedCategory.TStructure.t.bounded U := by
    refine ⟨⟨0, DerivedCategory.TStructure.t.isGE_of_iso eUnit 0⟩, ?_⟩
    exact ⟨0, DerivedCategory.TStructure.t.isLE_of_iso eUnit 0⟩
  letI : U.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eUnit 0
  letI : U.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eUnit 0
  refine ⟨eb, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app (𝟙_ C)
    have hr : IsConstructibleModuleObject (condensedRingObj Λ X.left)
        (Mod.regular (condensedRingObj Λ X.left)) := by
      exact ⟨Scheme.Stratification.trivial X.left, fun i ↦ by
        refine ⟨.singleton (𝟙 X.left) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
        let G := AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1}
          ((Scheme.Stratification.trivial X.left).immersion i)
        let F := G.obj (condensedRingObj Λ X.left)
        let H := AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1}
          (𝟙 ((Scheme.Stratification.trivial X.left).domain i))
        let e' : (H.mapMod F).obj ((G.mapMod (condensedRingObj Λ X.left)).obj
            (Mod.regular (condensedRingObj Λ X.left))) ≅ Mod.regular (H.obj F) :=
          Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
            MonoidalCategory.whiskerLeft_id, Category.id_comp])
        let e1 : Mod.regular (H.obj F) ≅ Mod.finiteFree (H.obj F) 1 :=
          (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular (H.obj F))).symm
        refine ⟨1, 0, 0, ⟨e'.symm ≪≫ e1 ≪≫ ?_⟩⟩
        exact (cokernelZeroIsoTarget (X := Mod.finiteFree (H.obj F) 0)
          (Y := Mod.finiteFree (H.obj F) 1)).symm⟩
    exact constructible_of_iso (e.symm ≪≫ (DerivedCategory.homologyFunctor C 0).mapIso eUnit) hr
  · by_cases hneg : n < 0
    · have hz := DerivedCategory.isZero_of_isGE U 0 n hneg
      exact constructible_of_isZero (condensedRingObj Λ X.left) hz
    · have hpos : 0 < n := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hn)
      have hz := DerivedCategory.isZero_of_isLE U 0 n hpos
      exact constructible_of_isZero (condensedRingObj Λ X.left) hz

/-- The derived tensor of two bounded constructible module-object complexes is bounded
constructible, for any coefficient ring whose bounded constructible category is triangulated
and satisfies the degree-zero tensor calculation `hsingle` (`boundedConstructible_tensor_single`).
Source: `proposition-six-operations-dctf--14` in the blueprint.
(blueprint: proposition-six-operations-dctf--14) -/
private theorem boundedConstructible_tensor_closure_of
    (htri : (boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated)
    (hsingle : ∀ F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left),
      IsConstructibleModuleObject (condensedRingObj Λ X.left) F →
      IsConstructibleModuleObject (condensedRingObj Λ X.left) G →
      boundedConstructible (condensedRingObj Λ X.left)
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
          (DerivedCategory.singleFunctor _ 0).obj G))
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K)
    (hL : boundedConstructible (condensedRingObj Λ X.left) L) :
    boundedConstructible (condensedRingObj Λ X.left)
      (((-⊗ᴸ-(X.left)⟦Λ⟧).obj K).obj L) := by
  let P := boundedConstructible (condensedRingObj Λ X.left)
  have : P.IsTriangulated := htri
  change P (K ⊗ L)
  apply prop_of_boundedConstructibleModule (P.inverseImage (tensorLeft K)) ?_ hL
  intro G hG
  exact prop_of_boundedConstructibleModule
    (P.inverseImage (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)))
    (fun F hF ↦ hsingle F G hF hG) hK

variable {X}

private theorem isNoetherian_left : IsNoetherian X.left :=
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  ⟨⟩

/-- The derived tensor of two bounded constructible complexes is bounded constructible,
`ℚ̄_ℓ` coefficients. This is the tensor-closure clause of the ell-adic finiteness theorem.
Source: `proposition-six-operations-dctf--14` in the blueprint.
(blueprint: proposition-six-operations-dctf--14) -/
theorem boundedConstructible_tensor_closure
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      (((-⊗ᴸ-(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj K).obj L) :=
  have := isNoetherian_left (X := X)
  boundedConstructible_tensor_closure_of _ X
    (isTriangulated_boundedConstructible_ellAdic_padicAlgCl X.left ℓ)
    (fun F G hF hG ↦ boundedConstructible_tensor_single ℓ X F G hF hG) K L hK hL

namespace ContinuousMapRingObj

/-- The derived tensor of two bounded constructible complexes is bounded constructible,
`E̲` coefficients for `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`.
(blueprint: proposition-six-operations-dctf--14) -/
theorem boundedConstructible_tensor_closure
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left)
      (((-⊗ᴸ-(X.left)⟦Profinite.continuousMapRingObj E⟧).obj K).obj L) :=
  have := isNoetherian_left (X := X)
  boundedConstructible_tensor_closure_of _ X
    (isTriangulated_boundedConstructible_ellAdic_continuous X.left ℓ E)
    (fun F G hF hG ↦
      ContinuousMapRingObj.boundedConstructible_tensor_single ℓ E X F G hF hG)
    K L hK hL

end ContinuousMapRingObj

namespace PadicIntegersRingObj

/-- The derived tensor of two bounded constructible complexes is bounded constructible,
`𝒪̲_E` coefficients for `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`.
(blueprint: proposition-six-operations-dctf--14) -/
theorem boundedConstructible_tensor_closure
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)
      (((-⊗ᴸ-(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K).obj L) :=
  have := isNoetherian_left (X := X)
  boundedConstructible_tensor_closure_of _ X
    (isTriangulated_boundedConstructible_ellAdic_padicIntegers X.left ℓ E)
    (fun F G hF hG ↦
      PadicIntegersRingObj.boundedConstructible_tensor_single ℓ E X F G hF hG)
    K L hK hL

end PadicIntegersRingObj

namespace UnitBallRingObj

/-- The derived tensor of two bounded constructible complexes is bounded constructible,
`O̲` coefficients for `O` the closed unit ball of a finite normed extension `E` of `ℚ_ℓ`.
(blueprint: proposition-six-operations-dctf--14) -/
theorem boundedConstructible_tensor_closure
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] {E : Type} [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj O) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj O) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj O) X.left)
      (((-⊗ᴸ-(X.left)⟦Profinite.continuousMapRingObj O⟧).obj K).obj L) :=
  have := isNoetherian_left (X := X)
  boundedConstructible_tensor_closure_of _ X
    (isTriangulated_boundedConstructible_ellAdic_unitBall X.left ℓ O hO.out)
    (fun F G hF hG ↦ UnitBallRingObj.boundedConstructible_tensor_single ℓ O F G hF hG)
    K L hK hL

end UnitBallRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
