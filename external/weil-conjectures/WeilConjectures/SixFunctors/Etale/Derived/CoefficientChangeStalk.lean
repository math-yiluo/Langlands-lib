/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.UniversalArrowMate
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.SixFunctors.Etale.LowerStarGeometricPoint

/-!
# Geometric stalks commute with finite-level coefficient reduction

Let `ρ : Λ →+* Λ'` be a surjection of finite coefficient rings whose exponent is invertible on a
separably closed field `k`, and `x̄ : Spec k ⟶ X` a geometric point. The canonical coefficient
comparison `K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄`
(`AlgebraicGeometry.Etale.geometricStalkRestrictScalarsIso`) is an isomorphism for every
`K ∈ Dᵇctf(X, Λ)` (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).

Both squares of the pasting carry derived base changes to derived base changes, as their
horizontal functors are computed by exact left adjoints whose right adjoints commute with
restriction of scalars (`CategoryTheory.Adjunction.bijective_comp_map_of_unit_comp_map`): the
pullback `x̄^*`, whose right adjoint `x̄_*` is exact as `k` is separably closed
(`AlgebraicGeometry.Etale.isDerivedBaseChange_leftDerivedUpperStar_map_comp`), and the global
sections on `Spec k`, an equivalence of categories
(`AlgebraicGeometry.Etale.isDerivedBaseChange_rightDerivedGlobalSections_map_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')
  {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (x : Spec (.of k) ⟶ X)


/-- The derived pullback along a geometric point carries derived base changes to derived base
changes: if `η : K ⟶ Res K'` exhibits `K'` as `K ⊗ᴸ_Λ Λ'`, then `Lx̄^* η` followed by the
comparison `Lx̄^* Res ≅ Res Lx̄^*` exhibits `Lx̄^* K'` as `Lx̄^* K ⊗ᴸ_Λ Λ'`. The derived pullback
is induced by the exact `x̄^*`, whose right adjoint `x̄_*` is exact and commutes with restriction
of scalars. -/
lemma isDerivedBaseChange_leftDerivedUpperStar_map_comp
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Sheaf.IsDerivedBaseChange (((x)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map η ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ x).hom.app K') := by
  let adj (Γ : Type (u + 1)) [CommRing Γ] :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Γ) x).mapDerivedCategoryAdjunction
  have hβ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) x).unit.app
          ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj G) ≫
        (x)_*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIso ρ x).hom.app G) =
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') x).unit.app G) ≫
        (lowerStarCompRestrictScalarsIso ρ x).hom.app ((x)^*[ModuleCat.{u + 1} Λ'].obj G) := by
    rw [restrictScalars_map_unit_app]
    exact (Category.comp_id _).symm
  have hθ : Sheaf.IsDerivedBaseChange
      (((x)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map η ≫
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ x)).hom.app K') :=
    fun N ↦ Adjunction.bijective_comp_map_of_unit_comp_map (adj Λ') (adj Λ) _
      (Functor.mapDerivedCategorySquareIso (lowerStarCompRestrictScalarsIso ρ x)).hom
      (Adjunction.mapDerivedCategoryAdjunction_mate
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') x)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) x) (lowerStarCompRestrictScalarsIso ρ x)
        (upperStarRestrictScalarsIso ρ x) hβ) η hη N
  have h := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) x).hom.naturality η
  rw [leftDerivedUpperStarRestrictScalarsIso_hom_app, reassoc_of% h,
    ← Category.assoc (((x)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map η), ← Category.assoc]
  exact (Sheaf.IsDerivedBaseChange.of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) x).app K) hθ).comp_map_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ') x).app K').symm

/-- The global sections on `Spec k`, for `k` separably closed, are left adjoint to the constant
sheaf functor: they are the inverse of the equivalence between `Λ`-modules and étale sheaves of
`Λ`-modules on `Spec k`. -/
noncomputable abbrev globalSectionsConstantSheafAdjunction (Γ : Type (u + 1)) [CommRing Γ] :
    (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Γ)).obj
        (op (etalePoint k)) ⊣
      constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Γ) :=
  (constantSheafEquivalenceOfIsSepClosed Γ (k := k)).symm.toAdjunction

/-- The identification `Γ(Spec k, Res -) = Res Γ(Spec k, -)` of the global sections with
restriction of scalars, as a square. -/
noncomputable abbrev globalSectionsRestrictScalarsSquare :
    TwoSquare (Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ)
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
        (op (etalePoint k)))
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k)))
      (ModuleCat.restrictScalars.{u + 1} ρ) :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

/-- The comparison `Λ'_{Spec k} ∘ Res ⟶ Res ∘ Λ'_{Spec k}` of constant sheaf functors with
restriction of scalars: the mate of `AlgebraicGeometry.Etale.globalSectionsRestrictScalarsSquare`
along `AlgebraicGeometry.Etale.globalSectionsConstantSheafAdjunction`. -/
noncomputable abbrev constantSheafRestrictScalarsMate :
    TwoSquare (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ'))
      (ModuleCat.restrictScalars.{u + 1} ρ)
      (Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ)
      (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  mateEquiv (globalSectionsConstantSheafAdjunction Λ') (globalSectionsConstantSheafAdjunction Λ)
    (globalSectionsRestrictScalarsSquare ρ)

/-- The comparison of constant sheaf functors with restriction of scalars is an isomorphism, as
the mate of an isomorphism along equivalences. -/
instance isIso_constantSheafRestrictScalarsMate :
    IsIso (constantSheafRestrictScalarsMate ρ (k := k)) := by
  have (M : ModuleCat.{u + 1} Λ') :
      IsIso ((constantSheafRestrictScalarsMate ρ (k := k)).app M) := by
    have h := mateEquiv_counit (globalSectionsConstantSheafAdjunction Λ' (k := k))
      (globalSectionsConstantSheafAdjunction Λ) (globalSectionsRestrictScalarsSquare ρ) M
    simp only [Equivalence.toAdjunction_counit] at h
    have : IsIso (((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k))).map ((constantSheafRestrictScalarsMate ρ).app M)) := by
      rw [(IsIso.eq_comp_inv _).2 h]
      infer_instance
    exact isIso_of_reflects_iso _
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k)))
  exact NatIso.isIso_of_isIso_app _

/-- The derived global sections on `Spec k`, for `k` separably closed, carry derived base
changes to derived base changes: if `θ : M ⟶ Res M'` exhibits `M'` as `M ⊗ᴸ_Λ Λ'`, then
`RΓ(Spec k, θ)` followed by the comparison `RΓ(Spec k, Res -) ≅ Res RΓ(Spec k, -)` exhibits
`RΓ(Spec k, M')` as `RΓ(Spec k, M) ⊗ᴸ_Λ Λ'`. The global sections are an equivalence. -/
lemma isDerivedBaseChange_rightDerivedGlobalSections_map_comp
    {M : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M' : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {θ : M ⟶ (Sheaf.derivedRestrictScalars (Spec (.of k)).smallEtaleTopology ρ).obj M'}
    (hθ : Sheaf.IsDerivedBaseChange θ) :
    ModuleCat.IsDerivedBaseChange
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map θ ≫
        (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ).hom.app M') := by
  let adj (Γ : Type (u + 1)) [CommRing Γ] :=
    (globalSectionsConstantSheafAdjunction Γ (k := k)).mapDerivedCategoryAdjunction
  have hβ (G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')) :=
    (unit_mateEquiv (globalSectionsConstantSheafAdjunction Λ' (k := k))
      (globalSectionsConstantSheafAdjunction Λ) (globalSectionsRestrictScalarsSquare ρ) G).symm
  have hθ' : ModuleCat.IsDerivedBaseChange
      (((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (etalePoint k))).mapDerivedCategory.map θ ≫
        (Functor.mapDerivedCategorySquareIso
          (F₁ := Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ)
          (F₂ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (op (etalePoint k)))
          (G₁ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
            (op (etalePoint k)))
          (G₂ := ModuleCat.restrictScalars.{u + 1} ρ) (Iso.refl _)).hom.app M') :=
    fun N ↦ Adjunction.bijective_comp_map_of_unit_comp_map (adj Λ') (adj Λ) _
      (Functor.mapDerivedCategorySquareIso
        (asIso (constantSheafRestrictScalarsMate ρ (k := k)))).hom
      (Adjunction.mapDerivedCategoryAdjunction_mate (globalSectionsConstantSheafAdjunction Λ')
        (globalSectionsConstantSheafAdjunction Λ)
        (asIso (constantSheafRestrictScalarsMate ρ (k := k))) (Iso.refl _) hβ) θ hθ N
  have h := (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ (k := k)).hom.naturality θ
  rw [derivedRestrictScalarsCompRightDerivedGlobalSectionsIso, Iso.trans_hom, Iso.trans_hom,
    NatTrans.comp_app, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    reassoc_of% h, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    ← Category.assoc (((sheafSections (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (op (etalePoint k))).mapDerivedCategory.map θ),
    ← Category.assoc]
  exact (ModuleCat.IsDerivedBaseChange.of_iso
    ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ (k := k)).app M) hθ').comp_map_iso
    ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ' (k := k)).app M').symm

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--7` (subsection
`theorem-grothendieck-lefschetz-trace-formula--7`), the pullback isomorphism at a geometric point:
for a morphism `ρ : Λ →+* Λ'` of finite rings whose exponent is invertible on `k`, the canonical
coefficient comparison `K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄` of geometric stalks
(`AlgebraicGeometry.Etale.geometricStalkRestrictScalarsIso`) is an isomorphism for every
`K ∈ Dᵇctf(X, Λ)`. -/
theorem isCoefficientChange_geometricStalkRestrictScalarsIso [Finite Λ] [Finite Λ']
    [HasInvertibleExponent Λ (Spec (.of k))] :
    IsCoefficientChange ρ (geometricStalk Λ x) (geometricStalk Λ' x)
      (geometricStalkRestrictScalarsIso ρ x) := by
  intro K K' η _ hη
  rw [geometricStalkRestrictScalarsIso, pasteTwoSquaresIso_hom_app, Functor.comp_map,
    ← Functor.map_comp_assoc]
  exact isDerivedBaseChange_rightDerivedGlobalSections_map_comp ρ
    (isDerivedBaseChange_leftDerivedUpperStar_map_comp ρ x hη)

end AlgebraicGeometry.Etale
