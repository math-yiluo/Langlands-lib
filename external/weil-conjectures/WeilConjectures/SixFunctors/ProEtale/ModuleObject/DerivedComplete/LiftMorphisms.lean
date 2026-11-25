/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransitionComplex
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterTower
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionTower

/-!
# Lifting morphisms into derived complete `𝒪_E`-complexes

Let `K` and `L` be complexes of `𝒪_{E,X}`-module objects on `X_proét`, with `L` derived complete
(`ProEtale.derivedCompleteIntegers`). Write `red_n` for the derived reduction modulo `ℓⁿ` and
`Res_n` for the restriction of scalars along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X`.

## Canonical transitions

The reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` induces the morphism of coefficient ring objects
`ProEtale.integersModPowTransition` and the canonical transition maps
`ProEtale.reductionTransition : Res_{n+1} (red_{n+1} K) ⟶ Res_n (red_n K)`, natural in `K`
(`ProEtale.reductionTransitionNatTrans`), compatible with the units `K ⟶ Res_n (red_n K)`
(`ProEtale.unit_comp_reductionTransition`) and with the connecting morphisms of the natural
reduction triangles (`ProEtale.reductionδ_comp_shift_map_zsmul`). The latter is the
naturality of the connecting morphisms of short exact sequences
(`Mod.derivedReductionTransition_app_comp_derivedExtendScalarsTriangleδ`). Hence the tower
`⋯ ⟶ Res_2 (red_2 K) ⟶ Res_1 (red_1 K)` with the canonical transitions
(`ProEtale.canonicalReductionTower`) has `K` as homotopy limit when `K` is derived complete
(`ProEtale.isHomotopyLimit_canonicalReductionTowerCone`).

## Lifting

* `ProEtale.exists_comp_unit_eq`: a family of maps `φ_n : K ⟶ Res_n (red_n L)` compatible
  with the canonical transitions lifts to a morphism `φ : K ⟶ L`.
* `ProEtale.exists_derivedReduction_map_eq`: a family of maps `φ_n : red_n K ⟶ red_n L`
  compatible with the canonical transitions is of the form `red_n φ` for a morphism `φ : K ⟶ L`.
* `ProEtale.eq_of_comp_unit_eq`, `ProEtale.existsUnique_derivedReduction_map_eq`: the lift is
  unique when the groups `Hom(K⟦1⟧, Res_n (red_n L))` are finite (`lim¹` vanishes).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- The transition `(𝒪_E ⧸ ℓⁿ⁺¹)̲ ⟶ (𝒪_E ⧸ ℓⁿ)̲` of ring objects of condensed abelian groups,
induced by the reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`. -/
noncomputable def integersModPowRingObjTransition :
    integersModPowRingObj.{u} ℓ E (n + 1) ⟶ integersModPowRingObj ℓ E n :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap (PadicAlgCl.integersModPowTransition ℓ E n)
      continuous_of_discreteTopology)

instance : IsMonHom (integersModPowRingObjTransition.{u} ℓ E n) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap (PadicAlgCl.integersModPowTransition ℓ E n)
        continuous_of_discreteTopology)))

/-- The reductions `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` are compatible with the transitions. -/
@[reassoc (attr := simp)]
lemma padicIntegersRingObjToIntegersModPow_comp_integersModPowRingObjTransition :
    padicIntegersRingObjToIntegersModPow.{u} ℓ E (n + 1) ≫
        integersModPowRingObjTransition ℓ E n =
      padicIntegersRingObjToIntegersModPow ℓ E n := by
  rw [padicIntegersRingObjToIntegersModPow, integersModPowRingObjTransition,
    ← Functor.map_comp]
  rfl

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

open scoped CategoryTheory.Obj

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  (n : ℕ)

/-- The transition `(𝒪_E ⧸ ℓⁿ⁺¹)_X ⟶ (𝒪_E ⧸ ℓⁿ)_X` of coefficient ring objects on `X_proét`. -/
noncomputable abbrev integersModPowTransition :
    condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) X ⟶
      condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X :=
  coefficientMap (Profinite.integersModPowRingObjTransition ℓ E n) X

/-- The reductions `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` are compatible with the transitions. -/
@[reassoc (attr := simp)]
lemma integersModPowReduction_comp_integersModPowTransition :
    integersModPowReduction X ℓ E (n + 1) ≫ integersModPowTransition X ℓ E n =
      integersModPowReduction X ℓ E n := by
  rw [integersModPowReduction, integersModPowTransition, ← coefficientMap_comp,
    Profinite.padicIntegersRingObjToIntegersModPow_comp_integersModPowRingObjTransition]

variable {X ℓ}

/-- The canonical transition `Res_{n+1} (red_{n+1} K) ⟶ Res_n (red_n K)` between the
reductions modulo `ℓⁿ⁺¹` and `ℓⁿ`, as a natural transformation. -/
noncomputable def reductionTransitionNatTrans :
    (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor ⋙
        (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor ⋙
        (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory :=
  Mod.derivedReductionTransition _ (integersModPowTransition X ℓ E n) _
    (integersModPowReduction_comp_integersModPowTransition X ℓ E n)

/-- The canonical transition `Res_{n+1} (red_{n+1} K) ⟶ Res_n (red_n K)` between the
reductions modulo `ℓⁿ⁺¹` and `ℓⁿ` of a complex `K` of `𝒪_{E,X}`-module objects, induced by the
reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`. -/
noncomputable abbrev reductionTransition
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K) ⟶
      (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj K) :=
  (reductionTransitionNatTrans E n).app K

/-- The canonical transitions are natural. -/
@[reassoc]
lemma reductionTransition_naturality
    {K K' : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (f : K ⟶ K') :
    (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.map
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map f) ≫
      reductionTransition E n K' =
    reductionTransition E n K ≫
      (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory.map
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.map f) :=
  (reductionTransitionNatTrans E n).naturality f

/-- The canonical transitions are compatible with the units `K ⟶ Res_n (red_n K)`. -/
@[reassoc (attr := simp)]
lemma unit_comp_reductionTransition
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1))).unit.app K ≫ reductionTransition E n K =
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E n)).unit.app K :=
  Mod.unit_app_comp_derivedReductionTransition_app _ _ _ _ K

/-- The canonical transitions are compatible with the connecting morphisms of the natural
reduction triangles `K --ℓⁿ--> K ⟶ Res_n (red_n K) ⟶ K⟦1⟧` and the multiplication by `ℓ`:
`(ℓ, 𝟙, transition)` is a morphism from the reduction triangle modulo `ℓⁿ⁺¹` to the one
modulo `ℓⁿ`. -/
@[reassoc]
lemma reductionδ_comp_shift_map_zsmul
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    (integersModPowReductionδ ℓ E (n + 1) X).app K ≫
        (shiftFunctor _ (1 : ℤ)).map ((ℓ : ℤ) • 𝟙 K) =
      reductionTransition E n K ≫ (integersModPowReductionδ ℓ E n X).app K :=
  (Mod.derivedReductionTransition_app_comp_derivedExtendScalarsTriangleδ _
    (integersModPowReduction_comp_integersModPowTransition X ℓ E n) _ _ (ℓ : ℤ) (pow_succ' _ _)
    _ _ _ _ K).symm

/-- The tower `⋯ ⟶ Res_3 (red_3 K) ⟶ Res_2 (red_2 K) ⟶ Res_1 (red_1 K)` of reductions modulo
`ℓⁿ` of a complex `K` of `𝒪_{E,X}`-module objects, with the canonical transitions; its `n`-th
term is `Res_{n+1} (red_{n+1} K)`. -/
noncomputable def canonicalReductionTower
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :=
  Functor.ofOpSequence (X := fun n ↦
    (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K))
    (fun n ↦ reductionTransition E (n + 1) K)

@[simp]
lemma canonicalReductionTower_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (canonicalReductionTower E K).obj (op n) =
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj
          K) :=
  rfl

@[simp]
lemma canonicalReductionTower_map_succ
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (canonicalReductionTower E K).map (homOfLE (Nat.le_add_right n 1)).op =
      reductionTransition E (n + 1) K :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The cone over the tower of reductions of `K` with the canonical transitions, with point `K`,
whose legs are the units `K ⟶ Res_{n+1} (red_{n+1} K)` of the adjunctions
`red_{n+1} ⊣ Res_{n+1}`. -/
noncomputable def canonicalReductionTowerCone
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    Cone (canonicalReductionTower E K) :=
  Limits.Cone.ofOpSequence (X := fun n ↦
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K))
    (fun n ↦ reductionTransition E (n + 1) K) K (fun n ↦
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1))).unit.app K)
    (fun n ↦ unit_comp_reductionTransition E (n + 1) K)

@[simp]
lemma canonicalReductionTowerCone_pt
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    (canonicalReductionTowerCone E K).pt = K :=
  rfl

@[simp]
lemma canonicalReductionTowerCone_π_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (canonicalReductionTowerCone E K).π.app (op n) =
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1))).unit.app K :=
  rfl

variable {E}

/-- **A derived complete `𝒪_E`-complex is the homotopy limit of its reductions modulo `ℓⁿ`,
with the canonical transitions**: the cone `K ⟶ Res_{n+1} (red_{n+1} K)` of units over
`ProEtale.canonicalReductionTower` is a homotopy limit cone. -/
theorem isHomotopyLimit_canonicalReductionTowerCone
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) :
    IsHomotopyLimit (canonicalReductionTowerCone E K) := by
  have hP : derivedCompleteIntegers ℓ E X (∏ᶜ fun _ : ℕ ↦ K) :=
    derivedCompleteIntegers_piObj _ fun _ ↦ hK
  refine isHomotopyLimit_of_triangles _ (ℓ : ℤ)
    (fun n ↦ (integersModPowReductionδ ℓ E (n + 1) X).app K)
    (fun n ↦ integersModPowReduction_distinguished ℓ E (n + 1) K) (fun n ↦ ?_)
    (isIso_id_add_zsmul_of_derivedCompleteIntegers hP)
    (isIso_id_add_zsmul_of_derivedCompleteIntegers (derivedCompleteIntegers_shift hP 1))
  rw [canonicalReductionTower_map_succ]
  exact reductionδ_comp_shift_map_zsmul E (n + 1) K

/-- **Lifting morphisms into a derived complete complex**: if `L` is derived complete, every
family of maps `φ_n : K ⟶ Res_{n+1} (red_{n+1} L)` compatible with the canonical transitions
is induced by a morphism `φ : K ⟶ L`, i.e. `φ_n = φ ≫ η_n` for the units
`η_n : L ⟶ Res_{n+1} (red_{n+1} L)`. -/
theorem exists_comp_unit_eq
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    (φ : ∀ n : ℕ, K ⟶ (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))
    (hφ : ∀ n : ℕ, φ (n + 1) ≫ reductionTransition E (n + 1) L = φ n) :
    ∃ f : K ⟶ L, ∀ n : ℕ, f ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X ℓ E (n + 1))).unit.app L = φ n :=
  (isHomotopyLimit_canonicalReductionTowerCone hL).exists_lift
    (Limits.Cone.ofOpSequence _ K φ hφ)

/-- **Uniqueness of the lift** into a derived complete complex: if `L` is derived complete and
the groups `Hom(K⟦1⟧, Res_{n+1} (red_{n+1} L))` are finite, a morphism `K ⟶ L` is determined by
its composites with the units `L ⟶ Res_{n+1} (red_{n+1} L)` (the `lim¹` term of the Milnor
sequence vanishes). -/
theorem eq_of_comp_unit_eq
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    [∀ n : ℕ, Finite (K⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))]
    {f g : K ⟶ L}
    (h : ∀ n : ℕ, f ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1))).unit.app L =
      g ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1))).unit.app L) : f = g :=
  have : ∀ n : ℕ, Finite (K⟦(1 : ℤ)⟧ ⟶ (canonicalReductionTower E L).obj (op n)) := fun n ↦
    inferInstanceAs (Finite (K⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)))
  ((isHomotopyLimit_canonicalReductionTowerCone hL).bijective_milnorMap K).1
    (Subtype.ext (funext h))

/-- A morphism `f : K ⟶ L` satisfies `red_{n+1} f = φ_n` if and only if
`f ≫ η^L_n = η^K_n ≫ Res_{n+1} φ_n`, for the units `η_n` of `red_{n+1} ⊣ Res_{n+1}`. -/
lemma derivedReduction_map_eq_iff
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (f : K ⟶ L)
    (φ : (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj L) :
    (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.map f = φ ↔
      f ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowReduction X ℓ E n)).unit.app L =
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowReduction X ℓ E n)).unit.app K ≫
          (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory.map φ := by
  constructor
  · rintro rfl
    exact ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X ℓ E n)).unit_naturality f).symm
  · intro h
    apply ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X ℓ E n)).homEquiv K _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X ℓ E n)).unit_naturality f).trans h

/-- If maps `φ : red_{n+1} K ⟶ red_{n+1} L` and `φ' : red_n K ⟶ red_n L` are compatible with
the canonical transitions, then so are their adjoints `K ⟶ Res_{n+1} (red_{n+1} L)` and
`K ⟶ Res_n (red_n L)`. -/
lemma homEquiv_comp_reductionTransition
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (φ : (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)
    (φ' : (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj L)
    (h : (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.map φ ≫
        reductionTransition E n L =
      reductionTransition E n K ≫
        (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory.map φ') :
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1))).homEquiv K _) φ ≫ reductionTransition E n L =
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E n)).homEquiv K _) φ' :=
  (congrArg (· ≫ reductionTransition E n L) (Adjunction.homEquiv_unit _ _ _ φ)).trans
    ((assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans
      ((unit_comp_reductionTransition_assoc E n K _).trans
        (Adjunction.homEquiv_unit _ _ _ φ').symm)))

/-- **Lifting morphisms of reductions into a derived complete complex**: if `L` is derived
complete, every family of maps `φ_n : red_{n+1} K ⟶ red_{n+1} L` compatible with the canonical
transitions is of the form `φ_n = red_{n+1} f` for a morphism `f : K ⟶ L`. -/
theorem exists_derivedReduction_map_eq
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    (φ : ∀ n : ℕ,
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)
    (hφ : ∀ n : ℕ,
      (Mod.comap (integersModPowReduction X ℓ E (n + 1 + 1))).mapDerivedCategory.map (φ (n + 1)) ≫
          reductionTransition E (n + 1) L =
        reductionTransition E (n + 1) K ≫
          (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.map (φ n)) :
    ∃ f : K ⟶ L, ∀ n : ℕ,
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map f =
        φ n := by
  obtain ⟨f, hf⟩ := exists_comp_unit_eq hL (fun n ↦ ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X ℓ E (n + 1))).homEquiv K _) (φ n))
    (fun n ↦ homEquiv_comp_reductionTransition (n + 1) (φ (n + 1)) (φ n) (hφ n))
  exact ⟨f, fun n ↦ (derivedReduction_map_eq_iff (n + 1) f (φ n)).2
    ((hf n).trans (Adjunction.homEquiv_unit _ _ _ _))⟩

/-- **Unique lifting of morphisms of reductions** into a derived complete complex `L`, when the
groups `Hom(K⟦1⟧, Res_{n+1} (red_{n+1} L))` are finite. -/
theorem existsUnique_derivedReduction_map_eq
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    [∀ n : ℕ, Finite (K⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))]
    (φ : ∀ n : ℕ,
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)
    (hφ : ∀ n : ℕ,
      (Mod.comap (integersModPowReduction X ℓ E (n + 1 + 1))).mapDerivedCategory.map (φ (n + 1)) ≫
          reductionTransition E (n + 1) L =
        reductionTransition E (n + 1) K ≫
          (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.map (φ n)) :
    ∃! f : K ⟶ L, ∀ n : ℕ,
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map f =
        φ n := by
  obtain ⟨f, hf⟩ := exists_derivedReduction_map_eq hL φ hφ
  refine ⟨f, hf, fun g hg ↦ eq_of_comp_unit_eq hL fun n ↦ ?_⟩
  rw [(derivedReduction_map_eq_iff (n + 1) g (φ n)).1 (hg n),
    (derivedReduction_map_eq_iff (n + 1) f (φ n)).1 (hf n)]

end AlgebraicGeometry.ProEtale
