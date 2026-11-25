/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.TraceFormula.BaseChange.Supertrace
public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.TraceFormula.WeilTrace
public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!

# The unit Weil object twisted by a scalar

Let `ℓ` be a prime, `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ`, `X` a separated scheme of
finite type over `Spec k` with an automorphism `e : X ≅ X` over `Spec k`, and `c` a unit of
`ℚ̄_ℓ`. This file constructs the canonical Weil unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
(`ProEtale.CondensedRing.weilUnit`) with its structure isomorphism multiplied by `c`
(`ProEtale.CondensedRing.weilScalarUnit`) and computes its traces: its local trace at every point
of degree `n + 1` is `c^{n+1}`, and so its global trace is `c^{n+1}` times the number of points of
degree `n + 1`.

The constants `ℚ̄_ℓ` act on the unit `ℚ̲̄_ℓ,Y` of `Mod_Y` for every scheme `Y`
(`ProEtale.CondensedRing.scalarEndRingHom`): the multiplication by a constant of the regular
condensed module `ℚ̲̄_ℓ` is pulled back along `p_Y^*`. This action is compatible with all pullbacks
(`ProEtale.CondensedRing.εIso_hom_comp_map_scalarEndRingHom_comp_εIso_inv`), and under
`End (𝟙_ Mod_{Spec Ω}) ≃+* ℚ̄_ℓ` (`ProEtale.CondensedRing.endTensorUnitRingEquiv`) it is the
identity (`ProEtale.CondensedRing.endTensorUnitRingEquiv_scalarEndRingHom`). On `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` the
action is placed in degree `0` (`ProEtale.CondensedRing.homologyUnitEndRingHom`).

The computation follows the one of the untwisted unit in `WeilConjectures.TraceFormula.WeilTrace`:
the only nonzero homology sheaf is `H⁰`, the unit Weil sheaf twisted by `c`
(`ProEtale.CondensedRing.homologyFunctorZeroWeilScalarUnitIso`); the `(n + 1)`-st iterated Weil
structure of the twisted unit Weil sheaf is the twisted unit Weil sheaf for `e^{n+1}` and `c^{n+1}`
(`ProEtale.CondensedRing.WeilSheaf.pow_scalarUnit`), since the action of `c` commutes with the unit
comparisons of the pullbacks; and the Frobenius on its stalk is, conjugated by the unit
comparison of the stalk, the multiplication by `c^{n+1}`, whose trace on the unit is itself.

## Main definitions

- `ProEtale.CondensedRing.scalarEndRingHom`: `ℚ̄_ℓ →+* End (𝟙_ Mod_Y)`.
- `ProEtale.CondensedRing.WeilSheaf.scalarUnit`: the unit Weil sheaf twisted by `c`.
- `ProEtale.CondensedRing.weilScalarUnit`: the canonical Weil unit twisted by `c`.

## Main results

- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit`:
  the local trace of the twisted Weil unit at a point of degree `n + 1` is `c^{n+1}`.
- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit`:
  for `e` of finite order, its global trace in degree `n + 1` is `c^{n+1} · #X(𝔽_{q^{n+1}})`.
- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit_point`,
  `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit_point`:
  for the base `Spec k`, the local trace at its geometric point and the global trace are `c^{n+1}`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The pullback `p_Y^*` from condensed `Λ`-modules is additive on module objects, being additive
on underlying sheaves. -/
instance additive_upperStarFromPointMod (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) : (upperStarFromPointMod Λ Y).Additive where
  map_add := by
    intros
    ext1
    exact (upperStarFromPoint Y).map_add

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The constants `ℚ̄_ℓ` act on the unit `ℚ̲̄_ℓ,Y` of `Mod_Y`: the image of the multiplication by
a constant on the regular condensed module `ℚ̲̄_ℓ` under the strong monoidal pullback `p_Y^*`. -/
noncomputable def scalarEndRingHom (Y : Scheme.{u}) :
    _root_.PadicAlgCl ℓ →+* End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))) :=
  (Functor.Monoidal.εIso
      (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).symm.conjRingEquiv.toRingHom.comp
    (((upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).mapEndRingHom _).comp
      (Profinite.PadicAlgCl.endRegularRingEquiv ℓ).toRingHom)

lemma scalarEndRingHom_apply (Y : Scheme.{u}) (c : _root_.PadicAlgCl ℓ) :
    scalarEndRingHom ℓ Y c =
      .of ((Functor.Monoidal.εIso (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).hom ≫
        (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).map
          (Profinite.PadicAlgCl.endRegularRingEquiv ℓ c).asHom ≫
        (Functor.Monoidal.εIso (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).inv) :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma scalarEndRingHom_eq_map (Y : Scheme.{u}) (c : _root_.PadicAlgCl ℓ) :
    scalarEndRingHom ℓ Y c = .of ((upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).map
      (X := Mod.regular (Profinite.padicAlgClRingObj ℓ))
      (Y := Mod.regular (Profinite.padicAlgClRingObj ℓ))
      (Profinite.PadicAlgCl.endRegularRingEquiv ℓ c).asHom) := by
  rw [scalarEndRingHom_apply]
  apply End.ext
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom']
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Under the identification `End (𝟙_ Mod_{Spec Ω}) ≃+* ℚ̄_ℓ`, the action of a constant on the
unit is the constant itself. -/
@[simp]
lemma endTensorUnitRingEquiv_scalarEndRingHom (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (c : _root_.PadicAlgCl ℓ) :
    endTensorUnitRingEquiv ℓ Ω (scalarEndRingHom ℓ (Spec (.of Ω)) c) = c := by
  conv_rhs => rw [← (endTensorUnitRingEquiv ℓ Ω).apply_symm_apply c]
  rw [scalarEndRingHom_eq_map]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

/-- Let `c : P ⋙ F ≅ Q` be an isomorphism of functors and `ε_P : b ≅ P a`, `ε_F : b' ≅ F b`,
`ε_Q : b' ≅ Q a` isomorphisms with `c_a = F ε_P⁻¹ ≫ ε_F⁻¹ ≫ ε_Q`. Then for an endomorphism `t` of
`a`, the conjugate by `ε_F` of `F` applied to the conjugate of `P t` by `ε_P` is the conjugate of
`Q t` by `ε_Q`. -/
lemma CategoryTheory.Iso.hom_comp_map_conj_comp_inv_eq {A B B' : Type*} [Category A] [Category B]
    [Category B'] {P : A ⥤ B} {F : B ⥤ B'} {Q : A ⥤ B'} (c : P ⋙ F ≅ Q) {a : A} {b : B} {b' : B'}
    (εP : b ≅ P.obj a) (εF : b' ≅ F.obj b) (εQ : b' ≅ Q.obj a)
    (h : c.hom.app a = F.map εP.inv ≫ εF.inv ≫ εQ.hom) (t : a ⟶ a) :
    εF.hom ≫ F.map (εP.hom ≫ P.map t ≫ εP.inv) ≫ εF.inv = εQ.hom ≫ Q.map t ≫ εQ.inv := by
  have h1 : F.map εP.inv ≫ εF.inv = c.hom.app a ≫ εQ.inv := by
    rw [h, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2 : εF.hom ≫ F.map εP.hom = εQ.hom ≫ c.inv.app a := by
    rw [← cancel_mono (c.hom.app a), Category.assoc, Category.assoc, Iso.inv_hom_id_app, h,
      Category.comp_id, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_assoc]
  have hn := c.hom.naturality t
  rw [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [h1, reassoc_of% h2, reassoc_of% hn,
    Iso.inv_hom_id_app_assoc]

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The action of the constants on the unit is compatible with pullbacks: for `f : X ⟶ Y`, the
pullback `f^*` of the action of `c` on `ℚ̲̄_ℓ,Y`, conjugated by the unit comparison of `f^*`, is
the action of `c` on `ℚ̲̄_ℓ,X`. -/
lemma εIso_hom_comp_map_scalarEndRingHom_comp_εIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : _root_.PadicAlgCl ℓ) :
    (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).hom ≫
      (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map (scalarEndRingHom ℓ Y c).asHom ≫
        (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv =
      (scalarEndRingHom ℓ X c).asHom :=
  Iso.hom_comp_map_conj_comp_inv_eq _ _ _ _
    (upperStarFromPointModComp_hom_app_unit (Profinite.padicAlgClRingObj ℓ) f)
    (Profinite.PadicAlgCl.endRegularRingEquiv ℓ c).asHom

/-- The automorphism of the unit `ℚ̲̄_ℓ,Y` of `Mod_Y` given by the action of a unit `c` of
`ℚ̄_ℓ`. -/
noncomputable def scalarAut (Y : Scheme.{u}) (c : (_root_.PadicAlgCl ℓ)ˣ) :
    𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) ≅ 𝟙_ _ :=
  (Aut.unitsEndEquivAut _ (Units.map (scalarEndRingHom ℓ Y).toMonoidHom c)).asIso

lemma scalarAut_hom (Y : Scheme.{u}) (c : (_root_.PadicAlgCl ℓ)ˣ) :
    (scalarAut ℓ Y c).hom = (scalarEndRingHom ℓ Y c).asHom :=
  rfl

/-- The action of a constant on the unit commutes with the unit comparison of a pullback. -/
lemma map_scalarEndRingHom_comp_εIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : _root_.PadicAlgCl ℓ) :
    (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map (scalarEndRingHom ℓ Y c).asHom ≫
        (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv =
      (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv ≫
        (scalarEndRingHom ℓ X c).asHom := by
  rw [← εIso_hom_comp_map_scalarEndRingHom_comp_εIso_inv ℓ f c, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing

/-- Let `P g` be a family of endofunctors indexed by the endomorphisms `g` of `X`, contravariant
up to the composition isomorphisms `comp`, let `ε g : a ≅ P g a` be isomorphisms compatible
with `comp`, and let `T` be an automorphism of `a` commuting with the `ε g`. Then the iterated
structure isomorphisms of `(ε e)⁻¹ ≫ T` are `(ε (e^{n+1}))⁻¹ ≫ T^{n+1}`. -/
theorem CategoryTheory.Iso.powSuccStr_symm_trans_hom_eq {C D : Type*} [Category C]
    [Category D] {X : C} (e : X ≅ X) (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D} (ε : ∀ g : X ⟶ X, a ≅ (P g).obj a)
    (h : ∀ f g : X ⟶ X, (comp f g).hom.app a ≫ (P f).map (ε g).inv ≫ (ε f).inv = (ε (f ≫ g)).inv)
    (T : a ≅ a) (t : End a) (ht : T.hom = t.asHom)
    (hT : ∀ g : X ⟶ X, (P g).map t.asHom ≫ (ε g).inv = (ε g).inv ≫ t.asHom) (n : ℕ) :
    (e.powSuccStr P comp ((ε e.hom).symm ≪≫ T) n).hom =
      (ε (e.pow (n + 1)).hom).inv ≫ (t ^ (n + 1)).asHom := by
  induction n with
  | zero =>
    have key : ∀ (g g' : X ⟶ X) (h : g = g'),
        eqToHom (congrArg (fun g ↦ (P g).obj a) h) ≫ (ε g').inv = (ε g).inv := by
      rintro g _ rfl
      simp
    rw [powSuccStr_zero, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, ht,
      ← Category.assoc, key _ _ (Category.id_comp e.hom)]
    exact congrArg (fun s : End a ↦ (ε (e.pow 1).hom).inv ≫ s.asHom) (_root_.pow_one t).symm
  | succ n ih =>
    rw [powSuccStr_succ, Iso.trans_hom, Iso.trans_hom, ih, Iso.app_hom, Functor.mapIso_hom,
      Iso.trans_hom, Functor.map_comp, Iso.symm_hom, ht, Category.assoc, reassoc_of% hT,
      reassoc_of% h]
    exact congrArg (fun s : End a ↦ (ε (e.pow (n + 2)).hom).inv ≫ s.asHom)
      (_root_.pow_succ t (n + 1)).symm

/-- If the carrier of an algebra for the identity functor is isomorphic to the unit, by an
isomorphism conjugating the structure automorphism to an endomorphism `t` of the unit, then the
structure automorphism has trace `t`. -/
lemma CategoryTheory.Endofunctor.IsoAlgebra.traceOrZero_str_hom_eq {C : Type*} [Category C]
    [MonoidalCategory C] [hC : BraidedCategory C] [Preadditive C] (A : IsoAlgebra (𝟭 C))
    (ε : 𝟙_ C ≅ A.carrier) (t : End (𝟙_ C)) (h : ε.hom ≫ A.str.hom ≫ ε.inv = t.asHom) :
    traceOrZero A.str.hom = t := by
  rw [← traceOrZero_conj ε.symm, Iso.symm_inv, Iso.symm_hom, h]
  let : HasRightDual (𝟙_ C) := ⟨𝟙_ C⟩
  rw [traceOrZero_eq_trace, trace_tensorUnit]

/-- Let `W : G ≅ E ⋙ G` and `φ : E a ≅ a`, and let `ε : d ≅ G a` conjugate the automorphism
`G a ≅ G (E a) ≅ G a` given by `W` and `G φ` to the identity. If an automorphism `s` of `a` is
sent by `G` to the conjugate of `t` by `ε`, then the automorphism given by `W` and `G (φ ≫ s)` is
conjugated by `ε` to `t`. -/
lemma CategoryTheory.Iso.hom_comp_app_trans_mapIso_trans_hom_comp_inv_eq {B D : Type*}
    [Category B] [Category D] {G : B ⥤ D} {E : B ⥤ B} (W : G ⋙ 𝟭 D ≅ E ⋙ G) {a : B} {d : D}
    (φ : E.obj a ≅ a) (s : a ≅ a) (ε : d ≅ G.obj a) (t : d ⟶ d)
    (h0 : ε.hom ≫ (W.app a ≪≫ G.mapIso φ).hom ≫ ε.inv = 𝟙 d)
    (hs : G.map s.hom ≫ ε.inv = ε.inv ≫ t) :
    ε.hom ≫ (W.app a ≪≫ G.mapIso (φ ≪≫ s)).hom ≫ ε.inv = t := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc] at h0 ⊢
  rw [hs]
  simp only [← Category.assoc] at h0 ⊢
  rw [h0, Category.id_comp]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

section ScalarSheaf

variable {X : Over (Spec (.of k))} (e : X ≅ X)

/-- The unit Weil sheaf `ℚ̲̄_ℓ,X` for `e` twisted by a unit `c` of `ℚ̄_ℓ`: the unit module object
with the structure isomorphism `e^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, the inverse of the unit comparison
of `e^*` followed by the multiplication by `c`. -/
noncomputable def WeilSheaf.scalarUnit (c : (_root_.PadicAlgCl ℓ)ˣ) : WeilSheaf ℓ e :=
  IsoAlgebra.mk (𝟙_ _)
    ((Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm ≪≫
      scalarAut ℓ X.left c)

lemma WeilSheaf.scalarUnit_str (c : (_root_.PadicAlgCl ℓ)ˣ) :
    (WeilSheaf.scalarUnit ℓ e c).str =
      (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm ≪≫
        scalarAut ℓ X.left c :=
  IsoAlgebra.mk_str _ _

/-- The iterated structure isomorphisms of the twisted unit Weil sheaf are the inverses of the
unit comparisons of the pullbacks `(e^{n+1})^*` followed by the multiplication by `c^{n+1}`. -/
lemma powSuccStr_εIso_symm_trans_scalarAut_hom (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) :
    (e.powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
      ((Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm ≪≫
        scalarAut ℓ X.left c) n).hom =
      (Functor.Monoidal.εIso ((e.pow (n + 1)).hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv ≫
        (scalarEndRingHom ℓ X.left
          ((c ^ (n + 1) : (_root_.PadicAlgCl ℓ)ˣ) : _root_.PadicAlgCl ℓ)).asHom := by
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact e.powSuccStr_symm_trans_hom_eq _ _
    (fun g ↦ Functor.Monoidal.εIso (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (fun f g ↦ upperStarComp_hom_app_unit_of_eq _ f.left g.left (Over.comp_left _ _ _ f g).symm
      _ (upperStarComp_left_eq ℓ f g)) (scalarAut ℓ X.left c) _ (scalarAut_hom ℓ X.left c)
    (fun g ↦ map_scalarEndRingHom_comp_εIso_inv ℓ g.left c) n

/-- The twisted unit Weil sheaf for `e` and `c`, as a Weil sheaf for `e^{n+1}`, is the twisted
unit Weil sheaf for `e^{n+1}` and `c^{n+1}`. -/
lemma WeilSheaf.pow_scalarUnit (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) :
    WeilSheaf.pow ℓ (WeilSheaf.scalarUnit ℓ e c) (n + 1) =
      WeilSheaf.scalarUnit ℓ (e.pow (n + 1)) (c ^ (n + 1)) := by
  rw [WeilSheaf.pow_succ, WeilSheaf.scalarUnit_str]
  unfold WeilSheaf.scalarUnit
  congr 1
  ext1
  rw [Iso.trans_hom, Iso.symm_hom, scalarAut_hom]
  exact powSuccStr_εIso_symm_trans_scalarAut_hom ℓ e c n

/-- The Frobenius on the stalk of the twisted unit Weil sheaf, conjugated by the unit comparison
`ε_x : Λ ≅ x̄^* Λ`, is the multiplication by `c`. -/
lemma WeilSheaf.stalkFunctor_obj_scalarUnit_str_hom {Ω : Type u} [Field Ω] [hΩ : IsSepClosed Ω]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ e.hom.left = σ ≫ x) (c : (_root_.PadicAlgCl ℓ)ˣ) :
    (Functor.Monoidal.εIso (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧).hom ≫
      ((WeilSheaf.stalkFunctor ℓ e σ x hx).obj (WeilSheaf.scalarUnit ℓ e c)).str.hom ≫
        (Functor.Monoidal.εIso (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv =
      (scalarEndRingHom ℓ (Spec (.of Ω)) c).asHom := by
  have h0 := WeilSheaf.stalkFunctor_obj_unit_str_hom ℓ e σ x hx
  rw [WeilSheaf.stalkFunctor_obj_str, WeilSheaf.unit_str] at h0
  rw [WeilSheaf.stalkFunctor_obj_str, WeilSheaf.scalarUnit_str]
  exact Iso.hom_comp_app_trans_mapIso_trans_hom_comp_inv_eq _ _ _ _ _ h0
    (map_scalarEndRingHom_comp_εIso_inv ℓ x c)

/-- The Frobenius on the stalk of the twisted unit Weil sheaf has trace `c`. The braiding of
`Mod_{Spec Ω}` is an argument, to be unified with the one of the trace at hand. -/
lemma WeilSheaf.traceOrZero_stalkFunctor_obj_scalarUnit_str_hom {Ω : Type u} [Field Ω]
    [hΩ : IsSepClosed Ω] [hB : BraidedCategory (GeometricPointMod ℓ Ω)]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ e.hom.left = σ ≫ x) (c : (_root_.PadicAlgCl ℓ)ˣ) :
    @Eq (End (𝟙_ (GeometricPointMod ℓ Ω)))
      (traceOrZero (C := GeometricPointMod ℓ Ω)
        (IsoAlgebra.str (C := GeometricPointMod ℓ Ω) (F := 𝟭 (GeometricPointMod ℓ Ω))
          (Functor.obj (D := IsoAlgebra (𝟭 (GeometricPointMod ℓ Ω)))
            (WeilSheaf.stalkFunctor ℓ e σ x hx) (WeilSheaf.scalarUnit ℓ e c))).hom)
      (scalarEndRingHom ℓ (Spec (.of Ω)) c) := by
  refine IsoAlgebra.traceOrZero_str_hom_eq (hC := hB) _
    (Functor.Monoidal.εIso (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧) _ ?_
  exact WeilSheaf.stalkFunctor_obj_scalarUnit_str_hom ℓ e σ x hx c

end ScalarSheaf

section ScalarSheafTrace

variable [Finite k] {X : Over (Spec (.of k))} (e : X ≅ X)

/-- The twisted unit Weil sheaf has trace `c^{n+1}` at every point of degree `n + 1`. -/
lemma weilSheafStalkTrace_scalarUnit (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    weilSheafStalkTrace ℓ (n + 1) x hx (WeilSheaf.scalarUnit ℓ e c) =
      scalarEndRingHom ℓ (Spec (.of (AlgebraicClosure k)))
        ((c : _root_.PadicAlgCl ℓ) ^ (n + 1)) := by
  rw [weilSheafStalkTrace, WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor,
    Functor.comp_obj, WeilSheaf.powFunctor_obj, WeilSheaf.pow_scalarUnit,
    ← Units.val_pow_eq_pow_val]
  exact WeilSheaf.traceOrZero_stalkFunctor_obj_scalarUnit_str_hom ℓ _ (hΩ := _) (hB := _) _ x hx _

end ScalarSheafTrace

end AlgebraicGeometry.ProEtale.CondensedRing

/-- The identification `H⁰(A[0]) ≅ A` is natural in `A`. -/
lemma DerivedCategory.homologyFunctorZeroQhSingleIso_hom_naturality {C : Type*} [Category C]
    [Abelian C] [HasDerivedCategory C] {A B : C} (f : A ⟶ B) :
    (homologyFunctor C 0).map (Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
        ((HomologicalComplex.single C (.up ℤ) 0).map f))) ≫
      (homologyFunctorZeroQhSingleIso C B).hom =
      (homologyFunctorZeroQhSingleIso C A).hom ≫ f := by
  rw [homologyFunctorZeroQhSingleIso_hom, homologyFunctorZeroQhSingleIso_hom,
    ← Functor.map_comp_assoc, quotientCompQhIso_hom_naturality, Functor.map_comp,
    Category.assoc, homologyFunctorFactors_hom_naturality_assoc]
  erw [(HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) 0).hom.naturality f]
  simp only [Category.assoc]
  rfl

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

omit [IsSeparated X.hom] in
/-- The `0`-th homology of the action of an endomorphism `t` of `Λ_X` on the unit of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`homologyUnitEndRingHom`) is `t`, under the identification `H⁰(Λ_X[0]) ≅ Λ_X`. -/
lemma homologyFunctor_map_homologyUnitEndRingHom
    (t : End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))) :
    (DerivedCategory.homologyFunctor _ 0).map
        ((boundedConstructible _).ι.map (homologyUnitEndRingHom ℓ X t).asHom) ≫
      (DerivedCategory.homologyFunctorZeroQhSingleIso _ (𝟙_ _)).hom =
      (DerivedCategory.homologyFunctorZeroQhSingleIso _ (𝟙_ _)).hom ≫ t.asHom := by
  rw [ι_map_homologyUnitEndRingHom]
  exact DerivedCategory.homologyFunctorZeroQhSingleIso_hom_naturality t.asHom

/-- The automorphism of the unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` given by the action of a unit `c` of
`ℚ̄_ℓ`, placed in degree `0`. -/
noncomputable def boundedConstructibleScalarAut (c : (_root_.PadicAlgCl ℓ)ˣ) :
    𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ≅ 𝟙_ _ :=
  (Aut.unitsEndEquivAut _
    (Units.map ((homologyUnitEndRingHom ℓ X).comp (scalarEndRingHom ℓ X.left)).toMonoidHom c)).asIso

omit [IsSeparated X.hom] in
lemma boundedConstructibleScalarAut_hom (c : (_root_.PadicAlgCl ℓ)ˣ) :
    (boundedConstructibleScalarAut ℓ (X := X) c).hom =
      (homologyUnitEndRingHom ℓ X (scalarEndRingHom ℓ X.left c)).asHom :=
  rfl

variable (e : X ≅ X)

/-- The unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with its canonical Weil structure twisted by a unit `c`
of `ℚ̄_ℓ`: the structure isomorphism is `Le^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, the one of the canonical
Weil unit `weilUnit` followed by the multiplication by `c`. Its local traces at the points of
degree `n + 1` are `c^{n+1}`
(`endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit`). -/
noncomputable def weilScalarUnit (c : (_root_.PadicAlgCl ℓ)ˣ) : WeilBoundedConstructible ℓ e.hom :=
  IsoAlgebra.mk (𝟙_ _)
    ((Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)).symm ≪≫
      boundedConstructibleScalarAut ℓ c)

lemma weilScalarUnit_str (c : (_root_.PadicAlgCl ℓ)ˣ) :
    (weilScalarUnit ℓ e c).str = (WeilBoundedConstructible.unit ℓ e.hom).str ≪≫
      boundedConstructibleScalarAut ℓ c := by
  unfold weilScalarUnit WeilBoundedConstructible.unit
  rw [IsoAlgebra.mk_str, IsoAlgebra.mk_str]

end AlgebraicGeometry.ProEtale.CondensedRing

/-- If `i ≪≫ G φ` followed by `ψ` is `r`, and `G` sends the automorphism `S` to the conjugate of
`t` by `ψ`, then `i ≪≫ G (φ ≪≫ S)` followed by `ψ` is `r ≫ t`. -/
lemma CategoryTheory.Iso.trans_mapIso_trans_hom_comp_eq {B D : Type*} [Category B] [Category D]
    {G : B ⥤ D} {a a' : B} {d d' : D} (i : d' ≅ G.obj a') (φ : a' ≅ a) (S : a ≅ a)
    (ψ : G.obj a ≅ d) (r : d' ⟶ d) (t : d ⟶ d) (h : (i ≪≫ G.mapIso φ).hom ≫ ψ.hom = r)
    (hS : G.map S.hom ≫ ψ.hom = ψ.hom ≫ t) :
    (i ≪≫ G.mapIso (φ ≪≫ S)).hom ≫ ψ.hom = r ≫ t := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at h ⊢
  rw [hS, ← reassoc_of% h]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (e : X ≅ X)

/-- The structure isomorphism `e^* H⁰ ≅ H⁰` of the `0`-th homology sheaf of the twisted Weil unit
is, under the identification `H⁰(ℚ̲̄_ℓ[0]) ≅ ℚ̲̄_ℓ`, the inverse of the unit comparison of `e^*`
followed by the multiplication by `c`. -/
lemma homologyFunctor_obj_weilScalarUnit_str_hom_comp (c : (_root_.PadicAlgCl ℓ)ˣ) :
    ((WeilBoundedConstructible.homologyFunctor ℓ e 0).obj (weilScalarUnit ℓ e c)).str.hom ≫
      (DerivedCategory.homologyFunctorZeroQhSingleIso _ (𝟙_ _)).hom =
    (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        (DerivedCategory.homologyFunctorZeroQhSingleIso _ (𝟙_ _)).hom ≫
      (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv ≫
        (scalarEndRingHom ℓ X.left c).asHom := by
  have h := WeilBoundedConstructible.homologyFunctor_obj_unit_str_hom_comp ℓ e
  rw [WeilBoundedConstructible.homologyFunctor_obj_str] at h
  rw [WeilBoundedConstructible.homologyFunctor_obj_str, weilScalarUnit_str, ← Category.assoc]
  exact Iso.trans_mapIso_trans_hom_comp_eq _ _ _ _ _ _ h
    (homologyFunctor_map_homologyUnitEndRingHom ℓ _)

/-- `H⁰` of the twisted Weil unit is the twisted unit Weil sheaf. -/
noncomputable def homologyFunctorZeroWeilScalarUnitIso (c : (_root_.PadicAlgCl ℓ)ˣ) :
    (WeilBoundedConstructible.homologyFunctor ℓ e 0).obj (weilScalarUnit ℓ e c) ≅
      WeilSheaf.scalarUnit ℓ e c :=
  IsoAlgebra.isoMk (DerivedCategory.homologyFunctorZeroQhSingleIso _ (𝟙_ _))
    (homologyFunctor_obj_weilScalarUnit_str_hom_comp ℓ e c).symm

section Trace

variable [Finite k]

/-- The local trace of the twisted Weil unit is the trace of the Frobenius on the stalk of its
homology sheaf `H⁰`, the other homology sheaves being zero. -/
lemma weilStalkTraceAlternatingSum_weilScalarUnit_eq_weilSheafStalkTrace
    (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx (weilScalarUnit ℓ e c) =
      weilSheafStalkTrace ℓ (n + 1) x hx ((WeilBoundedConstructible.homologyFunctor ℓ e 0).obj
        (weilScalarUnit ℓ e c)) := by
  rw [weilStalkTraceAlternatingSum]
  refine (finsum_eq_single _ 0 fun j hj ↦ ?_).trans ?_
  · refine smul_eq_zero_of_right _ (traceOrZero_eq_zero_of_isZero ?_ _)
    rw [Functor.id_obj, WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
      WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj, WeilSheaf.pow_carrier]
    exact Functor.map_isZero _ (isZero_homologyFunctor_unit_carrier ℓ e hj)
  · rw [Int.negOnePow_zero, Units.val_one, one_smul]

/-- **The local traces of the twisted Weil unit.** At every point of degree `n + 1`, the local
trace of the canonical Weil unit twisted by a unit `c` of `ℚ̄_ℓ` is `c^{n+1}`, as an endomorphism
of the unit of `Mod_{Spec k̄}`. -/
theorem weilStalkTraceAlternatingSum_weilScalarUnit (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx (weilScalarUnit ℓ e c) =
      scalarEndRingHom ℓ (Spec (.of (AlgebraicClosure k)))
        ((c : _root_.PadicAlgCl ℓ) ^ (n + 1)) := by
  rw [weilStalkTraceAlternatingSum_weilScalarUnit_eq_weilSheafStalkTrace,
    weilSheafStalkTrace_congr ℓ (n + 1) x hx (homologyFunctorZeroWeilScalarUnitIso ℓ e c)]
  exact weilSheafStalkTrace_scalarUnit ℓ e c n x hx

/-- **The local traces of the twisted Weil unit**, as elements of `ℚ̄_ℓ`: at every point of degree
`n + 1`, the local trace of the canonical Weil unit twisted by a unit `c` of `ℚ̄_ℓ` is `c^{n+1}`. -/
theorem endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit
    (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    endTensorUnitRingEquiv ℓ (AlgebraicClosure k)
        (weilStalkTraceAlternatingSum ℓ (n + 1) x hx (weilScalarUnit ℓ e c)) =
      (c : _root_.PadicAlgCl ℓ) ^ (n + 1) := by
  rw [weilStalkTraceAlternatingSum_weilScalarUnit]
  exact endTensorUnitRingEquiv_scalarEndRingHom ℓ _ _

attribute [local instance] fintypeFrobeniusFixedPoints

/-- **The global traces of the twisted Weil unit.** For `e` of finite order, the global trace in
degree `n + 1` of the canonical Weil unit twisted by `c` is `c^{n+1}` times the number of points
of degree `n + 1`, by the trace formula `weilTraceFormula`. -/
theorem weilStalkTraceAlternatingSum_weilCompactSupportCohomology_weilScalarUnit
    (he : ∃ m > 0, e.pow m = Iso.refl X) (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) :
    weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
        (specAlgebraicClosure_comp_pow (n + 1))
        ((weilCompactSupportCohomology ℓ e).obj (weilScalarUnit ℓ e c)) =
      Nat.card (frobeniusFixedPoints e (n + 1)) •
        scalarEndRingHom ℓ (Spec (.of (AlgebraicClosure k)))
          ((c : _root_.PadicAlgCl ℓ) ^ (n + 1)) := by
  rw [weilTraceFormula ℓ e he]
  simp only [weilStalkTraceAlternatingSum_weilScalarUnit]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

/-- **The global traces of the twisted Weil unit**, as elements of `ℚ̄_ℓ`: for `e` of finite
order, `∑ᵢ (-1)ⁱ Tr(Fr_{c,n+1} | Hⁱ_c(X_k̄, U_c)) = c^{n+1} · #X(𝔽_{q^{n+1}})`. -/
theorem endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit
    (he : ∃ m > 0, e.pow m = Iso.refl X) (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) :
    endTensorUnitRingEquiv ℓ (AlgebraicClosure k)
        (weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
          (specAlgebraicClosure_comp_pow (n + 1))
          ((weilCompactSupportCohomology ℓ e).obj (weilScalarUnit ℓ e c))) =
      (c : _root_.PadicAlgCl ℓ) ^ (n + 1) * Nat.card (frobeniusFixedPoints e (n + 1)) := by
  rw [weilStalkTraceAlternatingSum_weilCompactSupportCohomology_weilScalarUnit ℓ e he, map_nsmul,
    endTensorUnitRingEquiv_scalarEndRingHom, nsmul_eq_mul, mul_comm]

end Trace

/-! ### The base point -/

section Point

variable {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The local trace of the twisted Weil unit of the base `Spec k` at its geometric point `s` in
degree `n + 1` is `c^{n+1}`. -/
theorem endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit_point
    (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) :
    endTensorUnitRingEquiv ℓ (AlgebraicClosure k)
        (weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
          (specAlgebraicClosure_comp_pow (n + 1)) (weilScalarUnit ℓ (Iso.refl (point k)) c)) =
      (c : _root_.PadicAlgCl ℓ) ^ (n + 1) :=
  endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit ℓ _ c n _ _

/-- The global trace of the twisted Weil unit of the base `Spec k` in degree `n + 1` is
`c^{n+1}`: the base has a single point of each degree. -/
theorem endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit_point
    (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) :
    endTensorUnitRingEquiv ℓ (AlgebraicClosure k)
        (weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
          (specAlgebraicClosure_comp_pow (n + 1))
          ((weilCompactSupportCohomology ℓ (Iso.refl (point k))).obj
            (weilScalarUnit ℓ (Iso.refl (point k)) c))) =
      (c : _root_.PadicAlgCl ℓ) ^ (n + 1) := by
  rw [endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit
    ℓ _ ⟨1, Nat.one_pos, Iso.pow_refl 1⟩, Nat.card_unique, Nat.cast_one, mul_one]

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
