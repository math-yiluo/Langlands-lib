/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.TraceFormula.BaseChange.StalkTrace

/-!
# Stalks of Weil sheaves with structure through the identity

Stalks and iterated structures of Weil sheaves for an automorphism `e` with `e.hom.left = 𝟙`,
whose structure is `(𝟙)^* ≅ 𝟭` followed by an automorphism.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

noncomputable def upperStarIsoIdOfEq {Y : Scheme.{u}} {g : Y ⟶ Y} (hg : g = 𝟙 Y) :
    (g)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _ :=
  upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hg ≪≫
    upperStarId (Profinite.padicAlgClRingObj ℓ) Y

lemma upperStarIsoIdOfEq_hom_app {Y : Scheme.{u}} {g : Y ⟶ Y} (hg : g = 𝟙 Y)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :
    (upperStarIsoIdOfEq ℓ hg).hom.app M =
      (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hg).hom.app M ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M := by
  rw [upperStarIsoIdOfEq, Iso.trans_hom, NatTrans.comp_app]

/-- `upperStarComp_id_right`, evaluated. -/
@[reassoc]
lemma upperStarComp_id_right_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) f (𝟙 Y)).hom.app M ≫
        (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) =
      (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) (Category.comp_id f)).hom.app M := by
  rw [upperStarComp_id_right, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app,
    NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc, Category.assoc, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id_app,
    upperStarCongr_hom_app_eq_eqToHom, upperStarEqToIso_hom_app]
  rw [Functor.leftUnitor_inv_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

@[reassoc]
lemma upperStarEqToIso_hom_app_trans {A B : Scheme.{u}} {t t' t'' : A ⟶ B} (h : t = t')
    (h' : t' = t'')
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) B)) :
    (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) h).hom.app M ≫
        (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) h').hom.app M =
      (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) (h.trans h')).hom.app M := by
  rw [upperStarEqToIso_hom_app, upperStarEqToIso_hom_app, upperStarEqToIso_hom_app,
    eqToHom_trans]

lemma upperStarComp_hom_app_comp_map_upperStarEqToIso_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    {g g' : Y ⟶ Z} (h : g = g')
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) f g).hom.app M ≫
        (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) h).hom.app M) =
      (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) (congrArg (f ≫ ·) h)).hom.app M ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) f g').hom.app M := by
  subst h
  rw [upperStarEqToIso_hom_app, upperStarEqToIso_hom_app, eqToHom_refl, eqToHom_refl,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

@[reassoc]
lemma upperStarComp_hom_app_comp_upperStarIsoIdOfEq {Y : Scheme.{u}} {f g : Y ⟶ Y}
    (hf : f = 𝟙 Y) (hg : g = 𝟙 Y) (hfg : f ≫ g = 𝟙 Y)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) f g).hom.app M ≫
        (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map ((upperStarIsoIdOfEq ℓ hg).hom.app M) ≫
        (upperStarIsoIdOfEq ℓ hf).hom.app M =
      (upperStarIsoIdOfEq ℓ hfg).hom.app M := by
  rw [upperStarIsoIdOfEq_hom_app, upperStarIsoIdOfEq_hom_app, upperStarIsoIdOfEq_hom_app,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% upperStarComp_hom_app_comp_map_upperStarEqToIso_hom_app,
    upperStarComp_id_right_hom_app_assoc]
  rw [upperStarEqToIso_hom_app_trans_assoc, upperStarEqToIso_hom_app_trans_assoc]

theorem _root_.CategoryTheory.Iso.powSuccStr_trans_hom_eq_of_pred {C D : Type*} [Category C]
    [Category D] {X : C} (e : X ≅ X) (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D} (G : (X ⟶ X) → Prop)
    (κ : ∀ g : X ⟶ X, G g → ((P g).obj a ≅ a))
    (hκ : ∀ (f g : X ⟶ X) (hf : G f) (hg : G g) (hfg : G (f ≫ g)),
      (comp f g).hom.app a ≫ (P f).map (κ g hg).hom ≫ (κ f hf).hom = (κ (f ≫ g) hfg).hom)
    (hcongr : ∀ (g g' : X ⟶ X) (h : g = g') (hg : G g) (hg' : G g'),
      eqToHom (congrArg (fun g ↦ (P g).obj a) h) ≫ (κ g' hg').hom = (κ g hg).hom)
    (β : a ≅ a) (hβ : ∀ (g : X ⟶ X) (hg : G g),
        (P g).map β.hom ≫ (κ g hg).hom = (κ g hg).hom ≫ β.hom)
    (he : G e.hom) (hpow : ∀ n : ℕ,
        G (e.pow (n + 1)).hom) (h1 : G (𝟙 X ≫ e.hom)) (n : ℕ) :
    (e.powSuccStr P comp (κ e.hom he ≪≫ β) n).hom =
      (κ (e.pow (n + 1)).hom (hpow n)).hom ≫
          End.asHom (End.of β.hom ^ (n + 1)) := by
  induction n with
  | zero =>
    rw [Iso.powSuccStr_zero, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
      hcongr _ _ (Category.id_comp e.hom) h1 he, _root_.pow_one]
    rfl
  | succ n ih =>
    rw [Iso.powSuccStr_succ, Iso.trans_hom, Iso.trans_hom, ih, Iso.app_hom, Functor.mapIso_hom,
      Iso.trans_hom, Functor.map_comp, Category.assoc, ← Category.assoc ((P _).map β.hom),
      hβ, Category.assoc, ← Category.assoc ((P _).map (κ e.hom he).hom),
      ← Category.assoc ((comp _ _).hom.app a), hκ _ _ (hpow n) he (hpow (n + 1)),
          _root_.pow_succ,
      End.mul_asHom]
    rfl
lemma upperStarComp_hom_app_comp_upperStarIsoIdOfEq_of_eq {Y : Scheme.{u}} {f g h : Y ⟶ Y}
    (hfgh : f ≫ g = h) (hf : f = 𝟙 Y) (hg : g = 𝟙 Y) (hh : h = 𝟙 Y)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) f g).hom.app M ≫
        (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map ((upperStarIsoIdOfEq ℓ hg).app M).hom ≫
        ((upperStarIsoIdOfEq ℓ hf).app M).hom =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hfgh) ≫
        ((upperStarIsoIdOfEq ℓ hh).app M).hom := by
  subst hfgh
  rw [eqToHom_refl, Category.id_comp, Iso.app_hom, Iso.app_hom, Iso.app_hom]
  exact upperStarComp_hom_app_comp_upperStarIsoIdOfEq ℓ hf hg hh M

lemma upperStarComp_hom_app_comp_upperStarIsoIdOfEq_of_eq' {Y : Scheme.{u}} {f g t : Y ⟶ Y}
    (ht : f ≫ g = t)
    (c : (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (g)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hc : c = eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) ht.symm) ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
    (hf : f = 𝟙 Y) (hg : g = 𝟙 Y) (htt : t = 𝟙 Y)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :
    c.hom.app M ≫
        (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map ((upperStarIsoIdOfEq ℓ hg).app M).hom ≫
        ((upperStarIsoIdOfEq ℓ hf).app M).hom =
      ((upperStarIsoIdOfEq ℓ htt).app M).hom := by
  subst ht hc
  rw [eqToIso_refl, Iso.refl_trans, Iso.app_hom, Iso.app_hom, Iso.app_hom]
  exact upperStarComp_hom_app_comp_upperStarIsoIdOfEq ℓ hf hg htt M

lemma upperStarComp_left_eq' {k : Type u} [Field k] {X : Over (Spec (.of k))} (f g : X ⟶ X) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left :
      ((f ≫ g).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ _) =
    eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) (Over.comp_left _ _ _ f g))
    ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left := by
  rw [eqToIso_refl, Iso.refl_trans]

section Pow

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}

lemma pow_hom_left_eq_id {e : X ≅ X} (he : e.hom.left = 𝟙 X.left) (n : ℕ) :
    (e.pow n).hom.left = 𝟙 X.left := by
  induction n with
  | zero => rw [Iso.pow_zero, Iso.refl_hom, Over.id_left]
  | succ n ih => rw [Iso.pow_succ, Iso.trans_hom, Over.comp_left, ih, he, Category.comp_id]

lemma powSuccStr_upperStarIsoIdOfEq_trans_hom {e : X ≅ X} (he : e.hom.left = 𝟙 X.left)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) (β : M ≅ M) (n : ℕ) :
    (e.powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
      ((upperStarIsoIdOfEq ℓ he).app M ≪≫ β) n).hom =
    (upperStarIsoIdOfEq ℓ (pow_hom_left_eq_id he (n + 1))).hom.app M ≫
      End.asHom (End.of β.hom ^ (n + 1)) :=
  e.powSuccStr_trans_hom_eq_of_pred _ _ (fun g ↦ g.left = 𝟙 X.left)
    (fun g hg ↦ (upperStarIsoIdOfEq ℓ hg).app M)
    (fun f g hf hg hfg ↦ upperStarComp_hom_app_comp_upperStarIsoIdOfEq_of_eq' ℓ
      (Over.comp_left _ _ _ f g).symm _ (upperStarComp_left_eq' ℓ f g) hf hg hfg M)
    (fun g g' h hg hg' ↦ by
      subst h
      rw [eqToHom_refl, Category.id_comp])
    β (fun g hg ↦ (upperStarIsoIdOfEq ℓ hg).hom.naturality β.hom) he
    (fun n ↦ pow_hom_left_eq_id he (n + 1))
    (by rw [Over.comp_left, Over.id_left, he, Category.comp_id]) n

end Pow

section FixedPoint

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] {T : Scheme.{u}}

/-- The action of an endomorphism `σ` of `Spec Ω` on the pullbacks along a geometric point
`x̄ : Spec Ω ⟶ T` fixed by `σ`: `x̄^* ≅ x̄^* ⋙ σ^* ≅ (σ ≫ x̄)^* = x̄^*`. -/
noncomputable def upperStarFixedPointIso (σ : Spec (.of Ω) ⟶ Spec (.of Ω))
    (x : Spec (.of Ω) ⟶ T) (h : σ ≫ x = x) :
    (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ 𝟭 _ ≅ (x)^*⟦Profinite.padicAlgClRingObj
        ℓ⟧ :=
  Functor.isoWhiskerLeft _ (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).symm
      ≪≫
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).symm ≪≫
    upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) h

lemma upperStarComp_hom_app_comp_map_upperStarIsoIdOfEq_hom_app {X Y : Scheme.{u}} (x : X ⟶ Y)
    {t : Y ⟶ Y} (ht : t = 𝟙 Y)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) x t).hom.app M ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map ((upperStarIsoIdOfEq ℓ ht).hom.app M) =
      (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ)
        ((congrArg (x ≫ ·) ht).trans (Category.comp_id x))).hom.app M := by
  rw [upperStarIsoIdOfEq_hom_app, Functor.map_comp, ← Category.assoc,
    upperStarComp_hom_app_comp_map_upperStarEqToIso_hom_app, Category.assoc,
    upperStarComp_id_right_hom_app, upperStarEqToIso_hom_app_trans]

end FixedPoint

section Stalk

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

lemma WeilSheaf.pow_mk_upperStarIsoIdOfEq_str_hom {e : X ≅ X} (he : e.hom.left = 𝟙 X.left)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) (β : M ≅ M) (n : ℕ) :
    (WeilSheaf.pow ℓ (IsoAlgebra.mk M ((upperStarIsoIdOfEq ℓ he).app M ≪≫ β) :
        WeilSheaf ℓ e) (n + 1)).str.hom =
      (upperStarIsoIdOfEq ℓ (pow_hom_left_eq_id he (n + 1))).hom.app M ≫
        End.asHom (End.of β.hom ^ (n + 1)) := by
  unfold WeilSheaf.pow
  rw [IsoAlgebra.mk_str, powStr_succ_upperStar_eq_powSuccStr, IsoAlgebra.mk_str]
  erw [powSuccStr_upperStarIsoIdOfEq_trans_hom]
  -- retyping, stated for a variable natural transformation to keep the kernel away from
  -- unfolding the concrete one
  have r {P Q : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) ⥤
      CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)} (α : P ⟶ Q) :
      α.app (IsoAlgebra.mk (IsoAlgebra.mk M ((upperStarIsoIdOfEq ℓ he).app M ≪≫ β)).carrier
        (e.powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
          (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
          ((upperStarIsoIdOfEq ℓ he).app M ≪≫ β) n) : WeilSheaf ℓ (e.pow (n + 1))).carrier =
        α.app M := rfl
  rw [r]


/-- `AlgebraicGeometry.ProEtale.CondensedRing.stalkFunctor_obj_str_hom` for an endomorphism `σ`
which is not given as the morphism of an isomorphism. -/
lemma stalkFunctor_obj_str_hom_of_hom {e : X ≅ X} (σ : Spec (.of Ω) ⟶ Spec (.of Ω))
    (x : Spec (.of Ω) ⟶ X.left) (hx : x ≫ e.hom.left = σ ≫ x) (W : WeilSheaf ℓ e) :
    ((WeilSheaf.stalkFunctor ℓ e σ x hx).obj W).str.hom =
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app
          ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).inv.app W.carrier ≫
        eqToHom (congrArg (fun t : Spec (.of Ω) ⟶ X.left ↦
          (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) hx.symm) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app W.carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom := by
  have h1 : ((WeilSheaf.stalkFunctor ℓ e σ x hx).obj W).str.hom =
      (weilStalkComparison ℓ e σ x hx).hom.app W.carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom := by
    rw [WeilSheaf.stalkFunctor_obj_str]
    rfl
  have h2 := isoWhiskerLeft_symm_trans_hom_app_aux ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ)
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x)
    (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hx.symm)
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left) W.carrier
  have h3 := (congrArg (fun i ↦ i.hom.app W.carrier)
    (show weilStalkComparison ℓ e σ x hx = Functor.isoWhiskerLeft _
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).symm ≪≫
      (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).symm ≪≫
      upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hx.symm ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left from rfl)).trans h2
  refine h1.trans ((congrArg (· ≫ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom) h3).trans
    ((congrArg (fun z ↦ ((upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app
        ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).inv.app W.carrier ≫ z ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app W.carrier) ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom)
      (upperStarEqToIso_hom_app _ hx.symm W.carrier)).trans ?_))
  simp only [Category.assoc]

lemma stalkFunctor_obj_str_hom_of_upperStarIsoIdOfEq {e : X ≅ X} (he : e.hom.left = 𝟙 X.left)
    (F : WeilSheaf ℓ e) (γ : F.carrier ⟶ F.carrier)
    (hF : F.str.hom = (upperStarIsoIdOfEq ℓ he).hom.app F.carrier ≫ γ)
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ e.hom.left = σ ≫ x) :
    ((WeilSheaf.stalkFunctor ℓ e σ x hx).obj F).str.hom =
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app
          ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).inv.app F.carrier ≫
        (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) (hx.symm.trans
          ((congrArg (x ≫ ·) he).trans (Category.comp_id x)))).hom.app F.carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map γ := by
  have key := upperStarComp_hom_app_comp_map_upperStarIsoIdOfEq_hom_app ℓ x he F.carrier
  rw [stalkFunctor_obj_str_hom_of_hom, hF, Functor.map_comp,
    ← upperStarEqToIso_hom_app (Profinite.padicAlgClRingObj ℓ) hx.symm, reassoc_of% key,
    upperStarEqToIso_hom_app_trans_assoc]

lemma traceOrZero_stalkFunctor_obj_pow_mk {e : X ≅ X} (he : e.hom.left = 𝟙 X.left)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) (β : M ≅ M) (n : ℕ)
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = σ ≫ x) :
    traceOrZero ((WeilSheaf.stalkFunctor ℓ (e.pow (n + 1)) σ x hx).obj
      (WeilSheaf.pow ℓ (IsoAlgebra.mk M ((upperStarIsoIdOfEq ℓ he).app M ≪≫ β) :
        WeilSheaf ℓ e) (n + 1))).str.hom =
      traceOrZero ((upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app
          ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (WeilSheaf.pow ℓ (IsoAlgebra.mk M
            ((upperStarIsoIdOfEq ℓ he).app M ≪≫ β) : WeilSheaf ℓ e) (n + 1)).carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).inv.app
          (WeilSheaf.pow ℓ (IsoAlgebra.mk M
            ((upperStarIsoIdOfEq ℓ he).app M ≪≫ β) : WeilSheaf ℓ e) (n + 1)).carrier ≫
        (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) (hx.symm.trans
          ((congrArg (x ≫ ·) (pow_hom_left_eq_id he (n + 1))).trans
            (Category.comp_id x)))).hom.app (WeilSheaf.pow ℓ (IsoAlgebra.mk M
            ((upperStarIsoIdOfEq ℓ he).app M ≪≫ β) : WeilSheaf ℓ e) (n + 1)).carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (End.asHom (End.of β.hom ^ (n + 1)))) := by
  rw [stalkFunctor_obj_str_hom_of_upperStarIsoIdOfEq ℓ (pow_hom_left_eq_id he (n + 1)) _ _
    (WeilSheaf.pow_mk_upperStarIsoIdOfEq_str_hom ℓ he M β n) σ x hx]

end Stalk

lemma upperStarIsoIdOfEq_refl_hom_app {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    (upperStarIsoIdOfEq ℓ (by rw [Iso.refl_hom, Over.id_left] :
      (Iso.refl X).hom.left = 𝟙 X.left)).hom.app M =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app M := by
  rw [upperStarIsoIdOfEq_hom_app, upperStarEqToIso_hom_app, eqToHom_refl, Category.id_comp]


end AlgebraicGeometry.ProEtale.CondensedRing
