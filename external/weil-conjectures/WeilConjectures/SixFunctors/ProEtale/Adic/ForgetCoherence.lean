/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius

/-!
# The structure isomorphisms of `ℓ`-adic pullbacks on the underlying sheaves

The pullback `g^*` of sheaves of modules over the constant `ℓ`-adic sheaves is the pullback of
the underlying sheaves of `ℚ̄_ℓ`-modules (`AlgebraicGeometry.ProEtale.adicUpperStar_obj_X`), but
its composition isomorphisms, its congruence isomorphisms and the identification
`e^* ≅ (e⁻¹)_*` for an isomorphism `e` are constructed separately, by uniqueness of adjoints.
This file shows that they are those of the underlying sheaves.

## Main statements

- `AlgebraicGeometry.ProEtale.adicUpperStarComp_hom_app_hom`: the composition isomorphism
  `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*`.
- `AlgebraicGeometry.ProEtale.adicUpperStarCongr_hom_app_hom`: the congruence isomorphism.
- `AlgebraicGeometry.ProEtale.adicUpperStarIsoLowerStarInv_hom_app_hom`: the identification
  `e^* ≅ (e⁻¹)_*`.
- `AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso_hom_app_hom`: the
  exchange isomorphism of the pullback along a base change to `k̄` with the Frobenius pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The composition isomorphism of `ℓ`-adic pullbacks is that of the underlying sheaves. -/
lemma adicUpperStarComp_hom_app_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : AdicSheaf l R) :
    ((adicUpperStarComp l h₁ h₂).hom.app M).hom =
      (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.app M.X := by
  have e := conjugateEquiv_upperStarComp_hom (WeilCoefficients.{u} l) h₁ h₂
  rw [← Equiv.eq_symm_apply] at e
  rw [e]
  change (((conjugateEquiv _ _).symm (adicLowerStarComp l h₁ h₂).hom).app M).hom = _
  rw [conjugateEquiv_symm_apply_app, conjugateEquiv_symm_apply_app]
  simp only [Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarLowerStarAdjunction, Adjunction.comp_unit_app,
    Adjunction.modAdjunction_unit_app_hom, Adjunction.modAdjunction_counit_app_hom,
    adicLowerStarComp_hom_app_hom, adicLowerStar_map_hom, Functor.map_comp, Category.assoc]
  rfl

/-- The inverse of the composition isomorphism of `ℓ`-adic pullbacks is that of the underlying
sheaves. -/
lemma adicUpperStarComp_inv_app_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : AdicSheaf l R) :
    ((adicUpperStarComp l h₁ h₂).inv.app M).hom =
      (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).inv.app M.X := by
  rw [← cancel_epi ((upperStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.app M.X),
    Iso.hom_inv_id_app, ← adicUpperStarComp_hom_app_hom, ← Mod.comp_hom', Iso.hom_inv_id_app]
  rfl

/-- The congruence isomorphism of `ℓ`-adic pullbacks is that of the underlying sheaves. -/
lemma adicUpperStarCongr_hom_app_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (M : AdicSheaf l Y) :
    ((adicUpperStarCongr l h).hom.app M).hom =
      (upperStarCongr (WeilCoefficients.{u} l) h).hom.app M.X := by
  subst h
  rfl

lemma adicLowerStarId_inv_app_hom (X : Scheme.{u}) (M : AdicSheaf l X) :
    ((adicLowerStarId l X).inv.app M).hom =
      (lowerStarId (WeilCoefficients.{u} l) X).inv.app M.X :=
  Category.id_comp _

lemma adicLowerStarId_hom_app_hom (X : Scheme.{u}) (M : AdicSheaf l X) :
    ((adicLowerStarId l X).hom.app M).hom =
      (lowerStarId (WeilCoefficients.{u} l) X).hom.app M.X :=
  Category.comp_id _

lemma adicLowerStarCongr_inv_app_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (M : AdicSheaf l Z) :
    ((adicLowerStarCongr l h).inv.app M).hom =
      (lowerStarCongr (WeilCoefficients.{u} l) h).inv.app M.X :=
  rfl

-- Stated for arbitrary `a`, `b` and `h`: for `a = e.inv`, `b = e.hom` and `h = e.inv_hom_id`
-- the kernel times out on the same proof.
private lemma adicLowerStarComp_trans_inv_app_hom {X Y : Scheme.{u}} (a : Y ⟶ X) (b : X ⟶ Y)
    (h : a ≫ b = 𝟙 Y) (M : AdicSheaf l Y) :
    ((adicLowerStarComp l a b ≪≫ adicLowerStarCongr l h ≪≫ adicLowerStarId l Y).inv.app M).hom =
      (lowerStarComp _ a b ≪≫ lowerStarCongr _ h ≪≫ lowerStarId _ Y).inv.app M.X := by
  rw [Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comp_hom', adicLowerStarCongr_inv_app_hom, adicLowerStarComp_inv_app_hom,
    adicLowerStarId_inv_app_hom]
  rfl

private lemma adicLowerStarEquivalence_counitIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (adicLowerStarEquivalence l e).counitIso =
      adicLowerStarComp l e.inv e.hom ≪≫ adicLowerStarCongr l e.inv_hom_id ≪≫
        adicLowerStarId l Y :=
  rfl

private lemma lowerStarEquivalence_counitIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (lowerStarEquivalence (WeilCoefficients.{u} l) e).counitIso =
      lowerStarComp _ e.inv e.hom ≪≫ lowerStarCongr _ e.inv_hom_id ≪≫ lowerStarId _ Y :=
  rfl

/-- The counit of the equivalence `e_*` of `ℓ`-adic sheaves is that of the underlying sheaves. -/
lemma adicLowerStarEquivalence_counitIso_inv_app_hom {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : AdicSheaf l Y) :
    ((adicLowerStarEquivalence l e).counitIso.inv.app M).hom =
      (lowerStarEquivalence (WeilCoefficients.{u} l) e).counitIso.inv.app M.X :=
  (congrArg (fun i ↦ (i.inv.app M).hom) (adicLowerStarEquivalence_counitIso e)).trans
    ((adicLowerStarComp_trans_inv_app_hom e.inv e.hom e.inv_hom_id M).trans
      (congrArg (fun i ↦ i.inv.app M.X) (lowerStarEquivalence_counitIso (l := l) e)).symm)

/-- The identification `e^* ≅ (e⁻¹)_*` of `ℓ`-adic sheaves is that of the underlying sheaves. -/
lemma adicUpperStarIsoLowerStarInv_hom_app_hom {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : AdicSheaf l Y) :
    ((adicUpperStarIsoLowerStarInv l e).hom.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).hom.app M.X := by
  apply ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) e.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app (adicUpperStarLowerStarAdjunction l e.hom)
    (adicLowerStarEquivalence l e).symm.toAdjunction M
  have h₂ := Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) e.hom)
    (lowerStarEquivalence _ e).symm.toAdjunction M.X
  have h₁' : (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) e.hom).unit.app M.X ≫
      (e.hom)_*[WeilCoefficients.{u} l].map ((adicUpperStarIsoLowerStarInv l e).hom.app M).hom =
      ((adicLowerStarEquivalence l e).counitIso.inv.app M).hom := by
    refine Eq.trans ?_ (congrArg Mod.Hom.hom h₁)
    rw [Mod.comp_hom', adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom]
    rfl
  rw [h₁', adicLowerStarEquivalence_counitIso_inv_app_hom]
  exact h₂.symm

/-- The inverse of the identification `e^* ≅ (e⁻¹)_*` of `ℓ`-adic sheaves is that of the
underlying sheaves. -/
lemma adicUpperStarIsoLowerStarInv_inv_app_hom {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : AdicSheaf l Y) :
    ((adicUpperStarIsoLowerStarInv l e).inv.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).inv.app M.X := by
  rw [← cancel_epi ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).hom.app M.X),
    Iso.hom_inv_id_app, ← adicUpperStarIsoLowerStarInv_hom_app_hom, ← Mod.comp_hom',
    Iso.hom_inv_id_app]
  rfl

-- Stated for arbitrary `j`, `a`, `b` and `c`: for the geometric Frobenii the kernel times out on
-- the same proof.
private lemma exchange_hom_app_hom {X Y : Scheme.{u}} (j : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (c : a.hom ≫ j = j ≫ b.hom) (M : AdicSheaf l Y) :
    ((Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
      (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _).hom.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app
          ((j)^*ᵃ[l].obj M).X ≫
        (upperStarComp _ a.hom j).inv.app M.X ≫ (upperStarCongr _ c).hom.app M.X ≫
        (upperStarComp _ j b.hom).hom.app M.X ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom.app M.X) := by
  simp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarIsoLowerStarInv_inv_app_hom, adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom, adicUpperStarCongr_hom_app_hom]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

private lemma adicUpperStarGeometricFiberMapCompFrobeniusIso_eq :
    adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h =
      Functor.isoWhiskerLeft _
        (adicUpperStarIsoLowerStarInv l f.geometricGaloisFrobenius.asIso).symm ≪≫
      (adicUpperStarComp l _ _).symm ≪≫
      adicUpperStarCongr l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm ≪≫
      adicUpperStarComp l _ _ ≪≫
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l g.geometricGaloisFrobenius.asIso) _ :=
  rfl

/-- The exchange isomorphism `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*` of `ℓ`-adic sheaves, on the
underlying sheaves: `Fr_X^* φ̄^* ≅ (Fr_X ≫ φ̄)^* = (φ̄ ≫ Fr_Y)^* ≅ φ̄^* Fr_Y^*`, with
`Fr^* = (Fr⁻¹)_*`. -/
lemma adicUpperStarGeometricFiberMapCompFrobeniusIso_hom_app_hom
    (M : AdicSheaf l g.geometricFiber) :
    ((adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).hom.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) f.geometricGaloisFrobenius.asIso).inv.app
          ((Scheme.Hom.geometricFiberMap φ h)^*ᵃ[l].obj M).X ≫
        (upperStarComp _ f.geometricGaloisFrobenius.asIso.hom
          (Scheme.Hom.geometricFiberMap φ h)).inv.app M.X ≫
        (upperStarCongr _
          (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm).hom.app M.X ≫
        (upperStarComp _ (Scheme.Hom.geometricFiberMap φ h)
          g.geometricGaloisFrobenius.asIso.hom).hom.app M.X ≫
        (Scheme.Hom.geometricFiberMap φ h)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
            g.geometricGaloisFrobenius.asIso).hom.app M.X) :=
  (congrArg (fun i ↦ (i.hom.app M).hom)
    (adicUpperStarGeometricFiberMapCompFrobeniusIso_eq (l := l) φ h)).trans
    (exchange_hom_app_hom _ _ _ _ M)


end AlgebraicGeometry.ProEtale
