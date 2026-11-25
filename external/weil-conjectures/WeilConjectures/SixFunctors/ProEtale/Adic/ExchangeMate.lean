/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates

Let `φ : X₀ ⟶ Y₀` be a morphism of schemes over a finite field `k`, with base change
`φ̄ : X ⟶ Y` to the geometric fibers. The pullback and the pushforward along `φ̄` of sheaves of
`ℚ̄_ℓ,X`-modules commute with the Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`, through the exchange
isomorphisms `AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso` (`e^*`)
and `AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso` (`e_*`). This
file shows that `e_*` is the mate of `(e^*)⁻¹` under the adjunction `φ̄^* ⊣ φ̄_*`, so that the
adjunction lifts to sheaves with a Frobenius structure
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`).

Both are compared with the composition isomorphism of pushforwards along the two sides of
`Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`: the conjugate of `(e^*)⁻¹` under the adjunctions composed with the
Frobenius equivalences is this isomorphism, and so is the mate of `e_*` under the Frobenius
equivalences; the iterated mate of `(e^*)⁻¹` is its conjugate.

## Main results

- `AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`:
  the mate of `(e^*)⁻¹` is `e_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

section Sections

variable (A : Type u') [Category.{u + 1} A]

set_option linter.flexible false in
/-- The unit of the Frobenius equivalences, pushed forward along `J`, followed by the
composition isomorphisms of pushforwards along `Fr_X ≫ J = J ≫ Fr_Y`, agrees with the unit
followed by the pushforward of the exchange isomorphism of `J_*` with `Fr^* = (Fr⁻¹)_*`. Both are
restriction maps along canonical isomorphisms of iterated base changes. -/
lemma lowerStar_map_unit_comp_lowerStarComp {X Y : Scheme.{u}} (J : Y ⟶ X) (a : Y ≅ Y)
    (b : X ≅ X) (c : a.hom ≫ J = J ≫ b.hom) (c' : J ≫ b.inv = a.inv ≫ J)
    (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (J)_*[A].map ((lowerStarId A Y).inv.app M ≫
        (lowerStarCongr A a.inv_hom_id.symm).hom.app M ≫
        (lowerStarComp A a.inv a.hom).inv.app M) ≫
      (lowerStarComp A a.hom J).hom.app ((a.inv)_*[A].obj M) ≫
      (lowerStarCongr A c).hom.app ((a.inv)_*[A].obj M) ≫
      (lowerStarComp A J b.hom).inv.app ((a.inv)_*[A].obj M) =
    ((lowerStarId A X).inv.app ((J)_*[A].obj M) ≫
        (lowerStarCongr A b.inv_hom_id.symm).hom.app ((J)_*[A].obj M) ≫
        (lowerStarComp A b.inv b.hom).inv.app ((J)_*[A].obj M)) ≫
      (b.hom)_*[A].map ((lowerStarComp A J b.inv).hom.app M ≫
        (lowerStarCongr A c').hom.app M ≫ (lowerStarComp A a.inv J).inv.app M) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V ↦ ?_))
  -- `rw` rather than `simp only`: `simp only` would close the goal through a single kernel
  -- conversion between the composite and its sectionwise form, which is very slow.
  repeat' first
    | rw [ObjectProperty.FullSubcategory.comp_hom]
    | rw [NatTrans.comp_app]
    | rw [lowerStar_map_hom_app']
    | rw [lowerStarComp_hom_app_hom_app]
    | rw [lowerStarComp_inv_app_hom_app]
    | rw [lowerStarCongr_hom_app_hom_app]
    | rw [lowerStarId_inv_app_hom_app]
    | rw [lowerStar_obj_obj_map']
  simp only [← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [Quiver.Hom.unop_op]
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullbackId]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullbackId]
    rw [pullback.condition_assoc]
    simp

end Sections

/-- The inverse of the exchange isomorphism
`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso` of the pullbacks is
conjugate, under the adjunctions `φ̄^* ⊣ φ̄_*` composed with the Frobenius equivalences, to the
composition isomorphism `(Fr_X)_* ⋙ φ̄_* ≅ φ̄_* ⋙ (Fr_Y)_*` of pushforwards. Each of its five
constituents is conjugate to the identity, to a composition isomorphism or to a congruence
isomorphism of pushforwards. -/
lemma conjugateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv :
    conjugateEquiv
        ((adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h)).comp
          (adicLowerStarEquivalence l f.geometricGaloisFrobenius.asIso).symm.toAdjunction)
        ((adicLowerStarEquivalence l g.geometricGaloisFrobenius.asIso).symm.toAdjunction.comp
          (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h)))
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).inv =
    (adicLowerStarComp l f.geometricGaloisFrobenius.asIso.hom
      (Scheme.Hom.geometricFiberMap φ h)).hom ≫
      (adicLowerStarCongr l
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm).hom ≫
      (adicLowerStarComp l (Scheme.Hom.geometricFiberMap φ h)
        g.geometricGaloisFrobenius.asIso.hom).inv := by
  set j := Scheme.Hom.geometricFiberMap φ h
  set a := f.geometricGaloisFrobenius.asIso
  set b := g.geometricGaloisFrobenius.asIso
  set adj := adicUpperStarLowerStarAdjunction l j
  have h₁ := conjugateEquiv_whiskerRight (adicUpperStarLowerStarAdjunction l b.hom)
    (adicLowerStarEquivalence l b).symm.toAdjunction adj (adicUpperStarIsoLowerStarInv l b).inv
  have h₂ : conjugateEquiv (adicUpperStarLowerStarAdjunction l (j ≫ b.hom))
      ((adicUpperStarLowerStarAdjunction l b.hom).comp adj) (adicUpperStarComp l j b.hom).inv =
      (adicLowerStarComp l j b.hom).inv :=
    conjugateEquiv_adicUpperStarComp_inv l j b.hom
  have h₃ := conjugateEquiv_adicUpperStarCongr_inv l
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm
  have h₄ : conjugateEquiv (adj.comp (adicUpperStarLowerStarAdjunction l a.hom))
      (adicUpperStarLowerStarAdjunction l (a.hom ≫ j)) (adicUpperStarComp l a.hom j).hom =
      (adicLowerStarComp l a.hom j).hom :=
    conjugateEquiv_adicUpperStarComp_hom l a.hom j
  have h₅ := conjugateEquiv_whiskerLeft (adicLowerStarEquivalence l a).symm.toAdjunction
    (adicUpperStarLowerStarAdjunction l a.hom) adj (adicUpperStarIsoLowerStarInv l a).hom
  have hb : conjugateEquiv (adicUpperStarLowerStarAdjunction l b.hom)
      (adicLowerStarEquivalence l b).symm.toAdjunction
      (adicUpperStarIsoLowerStarInv l b).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have ha : conjugateEquiv (adicLowerStarEquivalence l a).symm.toAdjunction
      (adicUpperStarLowerStarAdjunction l a.hom) (adicUpperStarIsoLowerStarInv l a).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  rw [hb] at h₁
  rw [ha] at h₅
  simp only [adicUpperStarGeometricFiberMapCompFrobeniusIso, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ ((adicUpperStarLowerStarAdjunction l b.hom).comp adj) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (j ≫ b.hom)) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (a.hom ≫ j)) _,
    ← conjugateEquiv_comp _ (adj.comp (adicUpperStarLowerStarAdjunction l a.hom)) _]
  rw [h₁, h₂, h₃, h₄, h₅, Functor.whiskerRight_id', Functor.whiskerLeft_id']
  simp only [Category.comp_id, Category.assoc]
  rw [Category.id_comp]

lemma adicLowerStarId_inv_app_hom_hom_app (X : Scheme.{u}) (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) :
    ((adicLowerStarId l X).inv.app M).hom.hom.app V =
      M.X.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V.unop).op :=
  (congrArg (fun φ ↦ φ.hom.app V)
    (Category.id_comp ((lowerStarId (WeilCoefficients.{u} l) X).inv.app M.X))).trans
    (lowerStarId_inv_app_hom_app _ M.X V)

/-- On sections, the unit of the adjunction `(e⁻¹)_* ⊣ e_*` of `ℓ`-adic sheaves is the restriction
map along the canonical isomorphism of iterated base changes. -/
lemma adicLowerStarEquivalence_symm_unit_app_hom_hom_app {X : Scheme.{u}} (e : X ≅ X)
    (N : AdicSheaf l X) (W : X.ProEtᵒᵖ) :
    ((adicLowerStarEquivalence l e).symm.toAdjunction.unit.app N).hom.hom.app W =
      N.X.obj.map ((MorphismProperty.Over.pullbackComp e.inv e.hom).inv.app W.unop ≫
        (MorphismProperty.Over.pullbackCongr e.inv_hom_id.symm).inv.app W.unop ≫
          (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app W.unop).op := by
  rw [show (adicLowerStarEquivalence l e).symm.toAdjunction.unit.app N =
      (((adicLowerStarId l X).inv ≫ (adicLowerStarCongr l e.inv_hom_id).inv) ≫
        (adicLowerStarComp l e.inv e.hom).inv).app N from rfl,
    NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom', Mod.comp_hom',
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app, adicLowerStarId_inv_app_hom_hom_app,
    adicLowerStarCongr_inv_app_hom_hom_app, adicLowerStarComp_inv_app_hom_hom_app,
    ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]

/-- The composition isomorphism `J_* ⋙ (b⁻¹)_* ≅ (a⁻¹)_* ⋙ J_*` of pushforwards along the two
sides of `J ≫ b⁻¹ = a⁻¹ ≫ J` is the mate, under the equivalences `(a⁻¹)_* ⊣ a_*` and
`(b⁻¹)_* ⊣ b_*`, of the composition isomorphism along the two sides of `a ≫ J = J ≫ b`. -/
lemma mateEquiv_adicLowerStarComp_hom {X Y : Scheme.{u}} (J : Y ⟶ X) (a : Y ≅ Y) (b : X ≅ X)
    (c : a.hom ≫ J = J ≫ b.hom) (c' : J ≫ b.inv = a.inv ≫ J) :
    (mateEquiv (adicLowerStarEquivalence l a).symm.toAdjunction
        (adicLowerStarEquivalence l b).symm.toAdjunction
        (TwoSquare.mk _ _ _ _ (adicLowerStarComp l J b.inv ≪≫ adicLowerStarCongr l c' ≪≫
          (adicLowerStarComp l a.inv J).symm).hom)) =
    (adicLowerStarComp l a.hom J).hom ≫ (adicLowerStarCongr l c).hom ≫
      (adicLowerStarComp l J b.hom).inv := by
  -- Both sides are compared on sections, where they are restriction maps of `M.X`; see
  -- `AlgebraicGeometry.ProEtale.adicLowerStarComp_exchange`.
  refine (mateEquiv_eq_of_unit _ _ _ (TwoSquare.mk _ _ _ _ _)
    fun M ↦ Mod.hom_ext _ _ (ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V ↦ ?_))))
  have key := congrArg (fun φ ↦ φ.hom.app V)
    (lowerStar_map_unit_comp_lowerStarComp (WeilCoefficients.{u} l) J a b c c' M.X)
  have hi (X : Scheme.{u}) (e : X ≅ X) {N N' : AdicSheaf l X} (φ : N ⟶ N') (W : X.ProEtᵒᵖ) :
      ((adicLowerStarEquivalence l e).symm.inverse.map φ).hom.hom.app W =
        φ.hom.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).obj W.unop)) :=
    rfl
  have hf (X : Scheme.{u}) (e : X ≅ X) (N : AdicSheaf l X) {W W' : X.ProEtᵒᵖ} (φ : W ⟶ W') :
      ((adicLowerStarEquivalence l e).symm.functor.obj N).X.obj.map φ =
        N.X.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.inv).map φ.unop).op :=
    rfl
  -- Expose components before normalizing module, sheaf, and section compositions in order.
  -- `rewrite` retains explicit proofs without attempting reflexivity after every step.
  repeat' rewrite [Iso.trans_hom]
  repeat' rewrite [Iso.symm_hom]
  repeat' rewrite [NatTrans.comp_app]
  repeat' rewrite [Functor.map_comp]
  repeat' rewrite [Mod.comp_hom']
  repeat' rewrite [ObjectProperty.FullSubcategory.comp_hom]
  repeat' rewrite [NatTrans.comp_app]
  repeat' rewrite [adicLowerStar_map_hom_hom_app]
  repeat' rewrite [hi]
  repeat' rewrite [adicLowerStarEquivalence_symm_unit_app_hom_hom_app]
  repeat' rewrite [adicLowerStarComp_hom_app_hom_hom_app]
  repeat' rewrite [adicLowerStarComp_inv_app_hom_hom_app]
  repeat' rewrite [adicLowerStarCongr_hom_app_hom_hom_app]
  repeat' rewrite [adicLowerStar_obj_X_obj_map]
  repeat' rewrite [hf]
  repeat' rewrite [Functor.map_comp] at key
  repeat' rewrite [ObjectProperty.FullSubcategory.comp_hom] at key
  repeat' rewrite [NatTrans.comp_app] at key
  repeat' rewrite [lowerStar_map_hom_app'] at key
  repeat' rewrite [lowerStarComp_hom_app_lowerStar_obj_hom_app] at key
  repeat' rewrite [lowerStarComp_inv_app_lowerStar_obj_hom_app] at key
  repeat' rewrite [lowerStarCongr_hom_app_lowerStar_obj_hom_app] at key
  repeat' rewrite [lowerStarComp_hom_app_hom_app] at key
  repeat' rewrite [lowerStarComp_inv_app_hom_app] at key
  repeat' rewrite [lowerStarCongr_hom_app_hom_app] at key
  repeat' rewrite [lowerStarId_inv_app_hom_app] at key
  repeat' rewrite [lowerStar_obj_obj_map'] at key
  simp only [← Functor.map_comp, ← op_comp, Quiver.Hom.unop_op, Category.assoc] at key ⊢
  exact key

/-- The exchange isomorphism
`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso` of the pushforwards
is the mate, under the Frobenius equivalences, of the composition isomorphism
`(Fr_X)_* ⋙ φ̄_* ≅ φ̄_* ⋙ (Fr_Y)_*` of pushforwards. -/
lemma mateEquiv_adicLowerStarGeometricFiberMapCompFrobeniusIso_hom :
    (mateEquiv (adicLowerStarEquivalence l f.geometricGaloisFrobenius.asIso).symm.toAdjunction
        (adicLowerStarEquivalence l g.geometricGaloisFrobenius.asIso).symm.toAdjunction
        (TwoSquare.mk _ _ _ _
          (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom)) =
    (adicLowerStarComp l f.geometricGaloisFrobenius.asIso.hom
      (Scheme.Hom.geometricFiberMap φ h)).hom ≫
      (adicLowerStarCongr l
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm).hom ≫
      (adicLowerStarComp l (Scheme.Hom.geometricFiberMap φ h)
        g.geometricGaloisFrobenius.asIso.hom).inv :=
  mateEquiv_adicLowerStarComp_hom l _ _ _ _ _

/-- **The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates**: under the adjunction
`φ̄^* ⊣ φ̄_*`, the mate of the inverse of the exchange isomorphism
`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso` of the pullbacks is
the exchange isomorphism `AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso`
of the pushforwards. Both iterated mates under the Frobenius equivalences are the composition
isomorphism `(Fr_X)_* ⋙ φ̄_* ≅ φ̄_* ⋙ (Fr_Y)_*`. -/
lemma mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv :
    (mateEquiv (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
        (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
        (TwoSquare.mk _ _ _ _
          (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).inv)) =
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom := by
  have h₁ := iterated_mateEquiv_conjugateEquiv
    (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
    (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
    (adicLowerStarEquivalence l g.geometricGaloisFrobenius.asIso).symm.toAdjunction
    (adicLowerStarEquivalence l f.geometricGaloisFrobenius.asIso).symm.toAdjunction
    (TwoSquare.mk _ _ _ _ (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).inv)
  rw [conjugateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv,
    ← mateEquiv_adicLowerStarGeometricFiberMapCompFrobeniusIso_hom] at h₁
  exact ((mateEquiv _ _).injective h₁)

end AlgebraicGeometry.ProEtale
