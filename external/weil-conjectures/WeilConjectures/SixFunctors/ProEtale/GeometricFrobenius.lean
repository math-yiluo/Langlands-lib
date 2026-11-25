/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Pro-étale functors along a base change to `k̄` commute with the Frobenius pullbacks

Let `k` be a finite field, `φ : X₀ ⟶ Y₀` a morphism of `k`-schemes and `φ̄ = φ × 𝟙 : X ⟶ Y` its
base change to the geometric fibers, so that `φ̄ ≫ Fr_Y = Fr_X ≫ φ̄` for the geometric Galois
Frobenii (`AlgebraicGeometry.Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius`).

On pro-étale sheaves the pullback along the automorphism `Fr` is the pushforward along its
inverse (`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`), and we write
`Fr^* = (Fr⁻¹)_*` throughout. This file constructs the exchange isomorphisms which transport
Frobenius structures along `φ̄_*`, `φ̄^*` and, for an open immersion `φ`, the extension by zero
`φ̄_!`. They are the pro-étale counterparts of
`WeilConjectures.SixFunctors.Etale.GeometricFrobenius` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.GeometricFrobenius`.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso`:
  `φ̄_* ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_*`.
- `AlgebraicGeometry.ProEtale.upperStarGeometricFiberMapCompFrobeniusIso`:
  `φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*`.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`:
  `φ̄_! ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_!` for an open immersion `φ`.

## Main results

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso`
  : the comparison `φ̄_! ⟶ φ̄_*` commutes with these exchange isomorphisms. The exchange
  isomorphism for `φ̄_*` is conjugate to the one for the restriction `φ̄^*`
  (`AlgebraicGeometry.ProEtale.conjugateEquiv_openImmersionRestrictionFrobeniusIso_inv`),
  so this is an instance of the general compatibility of the comparison of an adjoint triple
  with conjugate exchange isomorphisms
  (`CategoryTheory.Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open ProEtale

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The base change `φ̄` commutes with the inverses of the geometric Galois Frobenii. -/
@[reassoc]
lemma Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv :
    Scheme.Hom.geometricFiberMap φ h ≫ g.geometricGaloisFrobenius.asIso.inv =
      f.geometricGaloisFrobenius.asIso.inv ≫ Scheme.Hom.geometricFiberMap φ h := by
  rw [Iso.comp_inv_eq, Category.assoc,
    Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius, Iso.inv_hom_id_assoc]

/-- The pushforward along the base change `φ̄` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*`: both composites are the pushforward along
`φ̄ ≫ Fr_Y⁻¹ = Fr_X⁻¹ ≫ φ̄`. -/
noncomputable def ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_*[A] ⋙ (g.geometricGaloisFrobenius.asIso.inv)_*[A] ≅
      (f.geometricGaloisFrobenius.asIso.inv)_*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)_*[A] :=
  lowerStarComp A _ _ ≪≫
    lowerStarCongr A (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    (lowerStarComp A _ _).symm

/-- The pullback along the base change `φ̄` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*`: identifying `(Fr⁻¹)_*` with `Fr^*`, both composites are the pullback along
`Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`. -/
noncomputable def ProEtale.upperStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)^*[A] ⋙ (f.geometricGaloisFrobenius.asIso.inv)_*[A] ≅
      (g.geometricGaloisFrobenius.asIso.inv)_*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)^*[A] :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv A f.geometricGaloisFrobenius.asIso).symm ≪≫
    (upperStarComp A _ _).symm ≪≫
    upperStarCongr A (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm ≪≫
    upperStarComp A _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv A g.geometricGaloisFrobenius.asIso) _

section OpenImmersion

variable [IsOpenImmersion φ]

/-- The restriction along the base change `φ̄` of an open immersion commutes with the
pushforwards along the Frobenii: `(Fr_Y)_* ⋙ φ̄^* ≅ φ̄^* ⋙ (Fr_X)_*`, the right adjoints of the
two sides of `ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def ProEtale.openImmersionRestrictionGeometricFiberMapCompFrobeniusIso :
    (g.geometricGaloisFrobenius.asIso.hom)_*[A] ⋙
        ProEtale.openImmersionRestriction A (Scheme.Hom.geometricFiberMap φ h) ≅
      ProEtale.openImmersionRestriction A (Scheme.Hom.geometricFiberMap φ h) ⋙
        (f.geometricGaloisFrobenius.asIso.hom)_*[A] :=
  Functor.isoWhiskerRight
      (upperStarIsoLowerStarInv A g.geometricGaloisFrobenius.asIso.symm).symm _ ≪≫
    Functor.isoWhiskerLeft _ (upperStarIsoOpenImmersionRestriction A _).symm ≪≫
    (upperStarComp A _ _).symm ≪≫
    upperStarCongr A
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    upperStarComp A _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction A _) _ ≪≫
    Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv A f.geometricGaloisFrobenius.asIso.symm)

/-- The extension by zero along the base change `φ̄` of an open immersion `φ` of `k`-schemes
commutes with the Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`: the two composites
`φ̄_! ⋙ (Fr_Y⁻¹)_*` and `(Fr_X⁻¹)_* ⋙ φ̄_!` are left adjoint to the two sides of
`ProEtale.openImmersionRestrictionGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_!open[A] ⋙ (g.geometricGaloisFrobenius.asIso.inv)_*[A] ≅
      (f.geometricGaloisFrobenius.asIso.inv)_*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)_!open[A] :=
  (conjugateIsoEquiv
      ((lowerStarEquivalence A f.geometricGaloisFrobenius.asIso).symm.toAdjunction.comp
        (openImmersionLowerShriekAdjunction A _))
      ((openImmersionLowerShriekAdjunction A _).comp
        (lowerStarEquivalence A g.geometricGaloisFrobenius.asIso).symm.toAdjunction)).symm
    (openImmersionRestrictionGeometricFiberMapCompFrobeniusIso A φ h).symm

/-- The exchange isomorphism `ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso` for the
pushforwards is conjugate, under the adjunctions `φ̄^* ⊣ φ̄_*` composed with the Frobenius
equivalences, to `ProEtale.openImmersionRestrictionGeometricFiberMapCompFrobeniusIso` for the
restrictions. Each of the seven constituents of the latter is conjugate to the identity, to a
composition isomorphism or to a congruence isomorphism of pushforwards. -/
lemma ProEtale.conjugateEquiv_openImmersionRestrictionFrobeniusIso_inv :
    conjugateEquiv ((lowerStarEquivalence A g.geometricGaloisFrobenius.asIso).toAdjunction.comp
        (openImmersionRestrictionLowerStarAdjunction A (Scheme.Hom.geometricFiberMap φ h)))
      ((openImmersionRestrictionLowerStarAdjunction A (Scheme.Hom.geometricFiberMap φ h)).comp
        (lowerStarEquivalence A f.geometricGaloisFrobenius.asIso).toAdjunction)
      (openImmersionRestrictionGeometricFiberMapCompFrobeniusIso A φ h).inv =
    (lowerStarGeometricFiberMapCompFrobeniusIso A φ h).hom := by
  set j := Scheme.Hom.geometricFiberMap φ h
  set a := f.geometricGaloisFrobenius.asIso
  set b := g.geometricGaloisFrobenius.asIso
  set adj := openImmersionRestrictionLowerStarAdjunction A j
  have h₁ := conjugateEquiv_whiskerRight (lowerStarEquivalence A b).toAdjunction
    (upperStarLowerStarAdjunction A (Iso.symm b).hom) adj (upperStarIsoLowerStarInv A b.symm).hom
  have h₂ := conjugateEquiv_whiskerLeft adj (upperStarLowerStarAdjunction A j)
    (upperStarLowerStarAdjunction A (Iso.symm b).hom)
    (upperStarIsoOpenImmersionRestriction A j).hom
  have h₃ : conjugateEquiv ((upperStarLowerStarAdjunction A (Iso.symm b).hom).comp
      (upperStarLowerStarAdjunction A j)) (upperStarLowerStarAdjunction A (j ≫ b.inv))
      (upperStarComp A j (Iso.symm b).hom).hom = (lowerStarComp A j (Iso.symm b).hom).hom :=
    conjugateEquiv_upperStarComp_hom A j _
  have h₅ := conjugateEquiv_upperStarComp_inv A a.inv j
  have h₄ := conjugateEquiv_upperStarCongr_inv A
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)
  have h₆ : conjugateEquiv ((upperStarLowerStarAdjunction A j).comp
      (upperStarLowerStarAdjunction A a.inv)) (adj.comp (upperStarLowerStarAdjunction A
        (Iso.symm a).hom)) (Functor.whiskerRight (upperStarIsoOpenImmersionRestriction A j).inv
          (a.inv)^*[A]) = _ :=
    conjugateEquiv_whiskerRight (upperStarLowerStarAdjunction A j) adj
      (upperStarLowerStarAdjunction A a.inv) (upperStarIsoOpenImmersionRestriction A j).inv
  have h₇ := conjugateEquiv_whiskerLeft (upperStarLowerStarAdjunction A (Iso.symm a).hom)
    (lowerStarEquivalence A a).toAdjunction adj (upperStarIsoLowerStarInv A a.symm).inv
  have hb : conjugateEquiv (lowerStarEquivalence A b).toAdjunction
      (upperStarLowerStarAdjunction A (Iso.symm b).hom)
      (upperStarIsoLowerStarInv A b.symm).hom = 𝟙 _ := by
    rw [← lowerStarEquivalence_symm_symm_toAdjunction]
    exact conjugateEquiv_leftAdjointUniq_hom _ _
  have ha : conjugateEquiv (upperStarLowerStarAdjunction A (Iso.symm a).hom)
      (lowerStarEquivalence A a).toAdjunction
      (upperStarIsoLowerStarInv A a.symm).inv = 𝟙 _ := by
    rw [← lowerStarEquivalence_symm_symm_toAdjunction]
    exact conjugateEquiv_leftAdjointUniq_inv _ _
  have hj : conjugateEquiv adj (upperStarLowerStarAdjunction A j)
      (upperStarIsoOpenImmersionRestriction A j).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  have hj' : conjugateEquiv (upperStarLowerStarAdjunction A j) adj
      (upperStarIsoOpenImmersionRestriction A j).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  rw [hb] at h₁
  rw [ha] at h₇
  rw [hj] at h₂
  rw [hj'] at h₆
  simp only [openImmersionRestrictionGeometricFiberMapCompFrobeniusIso, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ (adj.comp (upperStarLowerStarAdjunction A (Iso.symm a).hom)) _,
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A j).comp
      (upperStarLowerStarAdjunction A a.inv)) _,
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (a.inv ≫ j)) _,
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (j ≫ b.inv)) _,
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A (Iso.symm b).hom).comp
      (upperStarLowerStarAdjunction A j)) _,
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A (Iso.symm b).hom).comp adj) _]
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.comp_id]
  exact (congrArg (· ≫ _) (congrArg (· ≫ _) (Category.id_comp _))).trans
    (Category.assoc _ _ _)

/-- The comparison `φ̄_! ⟶ φ̄_*` commutes with the Frobenius exchange isomorphisms
`ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso` (`e_!`) and
`ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso` (`e_*`): the square

```
                  Fr_Y^* (can)
  Fr_Y^* ∘ φ̄_! ────────────────▶ Fr_Y^* ∘ φ̄_*
       │                              │
   e_! │                              │ e_*
       ▼                              ▼
  φ̄_! ∘ Fr_X^* ────────────────▶ φ̄_* ∘ Fr_X^*
                  can Fr_X^*
```

commutes, where `can` is `AlgebraicGeometry.ProEtale.openImmersionLowerShriekToLowerStar`. Both
composites are adjoint, under `φ̄_! ⊣ φ̄^*`, to the inverse of the counit of `φ̄^* ⊣ φ̄_*`
transported along the Frobenii. -/
lemma ProEtale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso :
    Functor.whiskerRight
        (ProEtale.openImmersionLowerShriekToLowerStar A (Scheme.Hom.geometricFiberMap φ h))
        (g.geometricGaloisFrobenius.asIso.inv)_*[A] ≫
      (ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso A φ h).hom =
    (ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso A φ h).hom ≫
      Functor.whiskerLeft (f.geometricGaloisFrobenius.asIso.inv)_*[A]
        (ProEtale.openImmersionLowerShriekToLowerStar A (Scheme.Hom.geometricFiberMap φ h)) := by
  have hcan (F : Sheaf (Scheme.ProEt.topology (Scheme.Hom.geometricFiber f)) A) :
      (openImmersionLowerShriekAdjunction A (Scheme.Hom.geometricFiberMap φ h)).unit.app F ≫
        (openImmersionRestriction A (Scheme.Hom.geometricFiberMap φ h)).map
          ((openImmersionLowerShriekToLowerStar A (Scheme.Hom.geometricFiberMap φ h)).app F) =
      inv ((openImmersionRestrictionLowerStarAdjunction A
        (Scheme.Hom.geometricFiberMap φ h)).counit.app F) := by
    rw [openImmersionLowerShriekToLowerStar_app, Functor.map_comp]
    erw [(openImmersionLowerShriekAdjunction A _).unit_naturality_assoc,
      Adjunction.right_triangle_components, Category.comp_id]
    simp
  have := Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom
    (openImmersionLowerShriekAdjunction A (Scheme.Hom.geometricFiberMap φ h))
    (openImmersionRestrictionLowerStarAdjunction A (Scheme.Hom.geometricFiberMap φ h))
    (lowerStarEquivalence A (f.geometricGaloisFrobenius).asIso)
    (lowerStarEquivalence A g.geometricGaloisFrobenius.asIso)
    (openImmersionRestrictionGeometricFiberMapCompFrobeniusIso A φ h) _ hcan
  rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateEquiv_openImmersionRestrictionFrobeniusIso_inv] at this
  exact this

end OpenImmersion

end AlgebraicGeometry
