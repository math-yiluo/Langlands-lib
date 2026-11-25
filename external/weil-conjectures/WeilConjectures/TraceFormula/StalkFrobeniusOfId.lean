/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Sections
public import WeilConjectures.TraceFormula.BaseChange.WeilObject
public import WeilConjectures.TraceFormula.WeilIdentityStructureOfId

/-!
# The Frobenius on the stalks of a module object with the identity Weil structure

A module object `M` on a scheme `X` over `Spec k` is a Weil sheaf for the identity of `X`, with
the identity structure `(𝟙)^* M ≅ M` (`ProEtale.CondensedRing.WeilSheaf.ofId`). For the base
`X = Spec k`, at a geometric point `x̄ : Spec k̄ ⟶ Spec k`, the `(n + 1)`-st Frobenius of the
stalk `x̄^* M` acts on the global sections `𝟙_ ⟶ x̄^* M` by pullback along `σⁿ⁺¹`
(`ProEtale.CondensedRing.comp_frobeniusStalk_ofId_str_hom`): it sends `v` to
`𝟙_ ≅ (σⁿ⁺¹)^* 𝟙_ ⟶ (σⁿ⁺¹)^* x̄^* M ≅ (σⁿ⁺¹ ≫ x̄)^* M = x̄^* M`
(`ProEtale.CondensedRing.upperStarSectionMap`).

## Implementation notes

The transports along equalities of morphisms are written as `eqToHom` of objects
(`congrArg (fun s ↦ s^* M)`), and the identities `g = 𝟙` are never substituted: comparing the
components of transports of pullback functors along different equalities makes the kernel
unfold the pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

section OfId

variable {X : Over (Spec (.of k))}

/-- The structure isomorphism of `WeilSheaf.ofId M` is the identity isomorphism `(𝟙)^* M ≅ M`. -/
lemma WeilSheaf.ofId_str
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    (WeilSheaf.ofId ℓ M).str = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).app M :=
  IsoAlgebra.mk_str _ _

/-- The structure isomorphism of `WeilSheaf.ofId M` is the identity isomorphism `(𝟙)^* M ≅ M`. -/
lemma WeilSheaf.ofId_str_hom
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    (WeilSheaf.ofId ℓ M).str.hom =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app (WeilSheaf.ofId ℓ M).carrier :=
  congrArg Iso.hom (WeilSheaf.ofId_str ℓ M)

end OfId

section Identity

variable {Y : Scheme.{u}}
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))

-- the composite of the transports and composition isomorphisms takes some time to elaborate
/-- The composition isomorphism `(a ≫ b)^* ≅ b^* ⋙ a^*`, followed by the identifications
`b^* ≅ (𝟙)^* ≅ 𝟭` and `a^* ≅ (𝟙)^* ≅ 𝟭`, for `a = 𝟙` and `b = 𝟙`, is the identification
`(a ≫ b)^* ≅ (𝟙)^* ≅ 𝟭`; the composition isomorphism may be transported along `a ≫ b = t`. -/
lemma upperStarComp_hom_app_comp_map_eqToHom_comp_upperStarId_of_eq (a b : Y ⟶ Y) {t : Y ⟶ Y}
    (ht : a ≫ b = t)
    (c : (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (b)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hc : c = eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) ht.symm) ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) a b)
    (ha : a = 𝟙 Y) (hb : b = 𝟙 Y) (htt : t = 𝟙 Y) :
    c.hom.app M ≫ (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        (eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hb) ≫
          (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) ≫
        eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ha) ≫
          (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) htt) ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M := by
  subst ht hc
  have hn := upperStarComp_hom_app_map_upperStarCongr_hom_app
    (Profinite.padicAlgClRingObj ℓ) a hb M
  rw [upperStarCongr_hom_app_eq_eqToHom, upperStarCongr_hom_app_eq_eqToHom] at hn
  have e : (upperStarComp (Profinite.padicAlgClRingObj ℓ) a (𝟙 Y)).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (Category.comp_id a)) ≫
        (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).inv.app M) := by
    rw [upperStarComp_id_right, upperStarCongr_eq_upperStarEqToIso]
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
      upperStarEqToIso_hom_app]
  have hi : (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).inv.app M) ≫
      (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) = 𝟙 _ :=
    ((a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapIso
      ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).app M)).inv_hom_id
  rw [eqToIso_refl, Iso.refl_trans, Functor.map_comp, Category.assoc, reassoc_of% hn, e,
    Category.assoc, reassoc_of% hi, eqToHom_trans_assoc, eqToHom_trans_assoc]

-- the composite of the transports and composition isomorphisms takes some time to elaborate
/-- The composition isomorphism `(x ≫ g)^* ≅ g^* ⋙ x^*`, followed by the identification
`g^* ≅ (𝟙)^* ≅ 𝟭`, for `g = 𝟙`, is the transport along `x ≫ g = x`. -/
lemma upperStarComp_hom_app_comp_map_eqToHom_comp_upperStarId {S : Scheme.{u}} (x : S ⟶ Y)
    {g : Y ⟶ Y} (hg : g = 𝟙 Y) (h : x ≫ g = x) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) x g).hom.app M ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hg) ≫
            (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) h) := by
  have hn := upperStarComp_hom_app_map_upperStarCongr_hom_app
    (Profinite.padicAlgClRingObj ℓ) x hg M
  rw [upperStarCongr_hom_app_eq_eqToHom, upperStarCongr_hom_app_eq_eqToHom] at hn
  have e : (upperStarComp (Profinite.padicAlgClRingObj ℓ) x (𝟙 Y)).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (Category.comp_id x)) ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).inv.app M) := by
    rw [upperStarComp_id_right, upperStarCongr_eq_upperStarEqToIso]
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
      upperStarEqToIso_hom_app]
  have hi : (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).inv.app M) ≫
      (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) = 𝟙 _ :=
    ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapIso
      ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).app M)).inv_hom_id
  rw [Functor.map_comp, reassoc_of% hn, e, Category.assoc, hi]
  simp only [Functor.id_obj, Category.comp_id, eqToHom_trans]

end Identity

section Point

/-- Every endomorphism of the base point `Spec k` over itself is the identity. -/
lemma point_hom_left_eq_id (g : point k ⟶ point k) : g.left = 𝟙 (point k).left :=
  (Category.comp_id _).symm.trans (Over.w g)

variable {X : Over (Spec (.of k))} (hX : ∀ g : X ⟶ X, g.left = 𝟙 X.left)
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))

/-- The identification `M ≅ (𝟙)^* M ≅ g^* M` for an endomorphism `g` of `X` which is the
identity. -/
noncomputable def upperStarIdIsoOfEq (g : X ⟶ X) :
    M ≅ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M :=
  ((upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).app M).symm ≪≫
    eqToIso (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) (hX g).symm)

lemma upperStarIdIsoOfEq_inv (g : X ⟶ X) :
    (upperStarIdIsoOfEq ℓ hX M g).inv =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) (hX g)) ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app M := by
  rw [upperStarIdIsoOfEq, Iso.trans_inv, eqToIso.inv, Iso.symm_inv, Iso.app_hom]

/-- **The iterated identity structure is the identity structure**: let `X` be an object all of
whose endomorphisms are the identity, for instance the base point (`point_hom_left_eq_id`). If
`φ : (𝟙)^* a ≅ a` is the identity isomorphism, then its `(n + 1)`-st iterate is the transport
along `(𝟙ⁿ⁺¹).left = 𝟙` followed by the identity isomorphism. -/
lemma powStr_hom_of_id {a : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)}
    (φ : ((Iso.refl X).hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj a ≅ a)
    (hφ : φ.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app a) (n : ℕ) :
    ((Iso.refl X).powStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
        (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left)
        (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) φ (n + 1)).hom =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj a)
          (hX ((Iso.refl X).pow (n + 1)).hom)) ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app a := by
  have hφ' : φ = (upperStarIdIsoOfEq ℓ hX a (Iso.refl X).hom).symm := by
    ext1
    rw [Iso.symm_hom, upperStarIdIsoOfEq_inv, eqToHom_refl, Category.id_comp, hφ]
  rw [powStr_succ_upperStar_eq_powSuccStr, hφ',
    (Iso.refl X).powSuccStr_symm_hom_eq_inv _ _ (upperStarIdIsoOfEq ℓ hX a)
      (fun f g ↦ ?_) n, upperStarIdIsoOfEq_inv]
  rw [upperStarIdIsoOfEq_inv, upperStarIdIsoOfEq_inv, upperStarIdIsoOfEq_inv]
  exact upperStarComp_hom_app_comp_map_eqToHom_comp_upperStarId_of_eq ℓ a f.left g.left
    (Over.comp_left _ _ _ f g).symm _ (upperStarComp_left_eq ℓ f g) (hX f) (hX g) (hX (f ≫ g))


/-- **The iterated identity structure of the base point is the identity structure**: the
`(n + 1)`-st iterate of the identity structure isomorphism `(𝟙)^* M ≅ M` of a module object on
the base point is the transport along `(𝟙ⁿ⁺¹).left = 𝟙` followed by the identity structure
isomorphism. -/
lemma WeilSheaf.pow_ofId_str_hom
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)) (n : ℕ) :
    (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).str.hom =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (point_hom_left_eq_id ((Iso.refl (point k)).pow (n + 1)).hom)) ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) (point k).left).hom.app M := by
  have hφ : (WeilSheaf.ofId ℓ M).str =
      (upperStarIdIsoOfEq ℓ point_hom_left_eq_id M (Iso.refl (point k)).hom).symm := by
    ext1
    rw [Iso.symm_hom, upperStarIdIsoOfEq_inv, eqToHom_refl, Category.id_comp,
      WeilSheaf.ofId_str_hom]
    rfl
  have hs : (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).str =
      (Iso.refl (point k)).powStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
        (upperStarId (Profinite.padicAlgClRingObj ℓ) (point k).left)
        (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
        (WeilSheaf.ofId ℓ M).str (n + 1) :=
    IsoAlgebra.mk_str _ _
  rw [hs, powStr_succ_upperStar_eq_powSuccStr, hφ,
    (Iso.refl (point k)).powSuccStr_symm_hom_eq_inv _ _
      (upperStarIdIsoOfEq ℓ point_hom_left_eq_id M) (fun f g ↦ ?_) n, upperStarIdIsoOfEq_inv]
  rw [upperStarIdIsoOfEq_inv, upperStarIdIsoOfEq_inv, upperStarIdIsoOfEq_inv]
  exact upperStarComp_hom_app_comp_map_eqToHom_comp_upperStarId_of_eq ℓ M f.left g.left
    (Over.comp_left _ _ _ f g).symm _ (upperStarComp_left_eq ℓ f g) (point_hom_left_eq_id f)
    (point_hom_left_eq_id g) (point_hom_left_eq_id (f ≫ g))


end Point

section Stalk

variable {S Y : Scheme.{u}}
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))

-- the composite of the transports and composition isomorphisms takes some time to elaborate
/-- **The stalk Frobenius of the identity structure is the pullback of sections**: let `x̄ : S ⟶ Y`,
`g = 𝟙` an endomorphism of `Y` and `σ` an endomorphism of `S` with `x̄ ≫ g = σ ≫ x̄`, and let
`τ : σ^* ≅ 𝟭` be the inverse of the unit comparison at the unit. Then the stalk Frobenius
`x̄^* M ≅ σ^* x̄^* M ≅ (σ ≫ x̄)^* M = (x̄ ≫ g)^* M ≅ x̄^* g^* M ≅ x̄^* M` of the identity structure
sends a global section `v : 𝟙_ ⟶ x̄^* M` to its pullback along `σ`
(`ProEtale.CondensedRing.upperStarSectionMap`). -/
lemma comp_stalkFrobeniusOfId_eq_upperStarSectionMap (σ : S ⟶ S) (x : S ⟶ Y) {g : Y ⟶ Y}
    (hg : g = 𝟙 Y) (hx : x ≫ g = σ ≫ x) (h : σ ≫ x = x)
    (τ : (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)
    (hτ : τ.inv.app _ = (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).hom)
    (v : 𝟙ₘ ⟶ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) :
    v ≫ τ.inv.app ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ≫
      (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).inv.app M ≫
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hx.symm) ≫
      (upperStarComp (Profinite.padicAlgClRingObj ℓ) x g).hom.app M ≫
      (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        (eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hg) ≫
          (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) =
      upperStarSectionMap (Profinite.padicAlgClRingObj ℓ) σ h M v := by
  have hn := τ.inv.naturality v
  rw [Functor.id_map] at hn
  rw [upperStarComp_hom_app_comp_map_eqToHom_comp_upperStarId ℓ M x hg (hx.trans h),
    eqToHom_trans, reassoc_of% hn, hτ, upperStarSectionMap]

end Stalk

/-- The isomorphism `σ^* ≅ 𝟭` over a separably closed point is, at the unit, the inverse of the
unit comparison of `σ^*`, written with the unit in the form of the type of `ε`. -/
lemma upperStarIsoIdOfIsSepClosed_inv_app_tensorUnit {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) :
    (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app
        𝟙ₘ =
      (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).hom := by
  have e : (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).app
      𝟙ₘ =
        (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm :=
    Iso.ext (upperStarIsoIdOfIsSepClosed_hom_app_unit _ σ)
  exact congrArg Iso.inv e

section Stalk

variable {S Y : Scheme.{u}}
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))

-- the composite of the transports and composition isomorphisms takes some time to elaborate
/-- `ProEtale.CondensedRing.comp_stalkFrobeniusOfId_eq_upperStarSectionMap`, with the stalk
Frobenius written as the component of the stalk comparison
(`ProEtale.CondensedRing.weilStalkComparison`). -/
lemma comp_weilStalkComparison_app_eq_upperStarSectionMap (σ : S ⟶ S) (x : S ⟶ Y) {g : Y ⟶ Y}
    (hg : g = 𝟙 Y) (hx : x ≫ g = σ ≫ x) (h : σ ≫ x = x)
    (τ : (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)
    (hτ : τ.inv.app _ = (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).hom)
    (v : 𝟙ₘ ⟶ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) :
    v ≫ ((Functor.isoWhiskerLeft (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧ τ.symm ≪≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).symm ≪≫
        upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hx.symm ≪≫
        upperStarComp (Profinite.padicAlgClRingObj ℓ) x g).app M).hom ≫
      (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        (eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hg) ≫
          (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) =
      upperStarSectionMap (Profinite.padicAlgClRingObj ℓ) σ h M v := by
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, upperStarEqToIso_hom_app, Category.assoc]
  exact comp_stalkFrobeniusOfId_eq_upperStarSectionMap ℓ M σ x hg hx h τ hτ v

end Stalk

section PointStalk

/-- `ProEtale.CondensedRing.WeilSheaf.pow_ofId_str_hom`, written with the carrier of the iterate. -/
lemma WeilSheaf.pow_ofId_str_hom_carrier
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)) (n : ℕ) :
    (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).str.hom =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
          (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).carrier)
          (point_hom_left_eq_id ((Iso.refl (point k)).pow (n + 1)).hom)) ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) (point k).left).hom.app
          (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).carrier := by
  rw [WeilSheaf.pow_ofId_str_hom]
  rfl

-- the unfolding of the stalk Frobenius takes some time to elaborate
/-- **The stalk Frobenius of the identity structure on the base point**: at a geometric point
`x̄ : Spec Ω ⟶ Spec k` with `x̄ ≫ 𝟙ⁿ⁺¹ = σ ≫ x̄` and `σ ≫ x̄ = x̄`, the `(n + 1)`-st Frobenius of
the stalk `x̄^* M` of `WeilSheaf.ofId M` sends a global section `v : 𝟙_ ⟶ x̄^* M` to its pullback
along `σ` (`ProEtale.CondensedRing.upperStarSectionMap`). -/
lemma comp_stalkFunctor_obj_pow_ofId_str_hom
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)) (n : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (σ : Spec (.of Ω) ⟶ Spec (.of Ω))
    (x : Spec (.of Ω) ⟶ (point k).left)
    (hx : x ≫ ((Iso.refl (point k)).pow (n + 1)).hom.left = σ ≫ x)
    (h : σ ≫ x = x)
    (v : 𝟙ₘ ⟶ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
        (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).carrier) :
    v ≫ ((WeilSheaf.stalkFunctor ℓ ((Iso.refl (point k)).pow (n + 1)) σ x hx).obj
        (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1))).str.hom =
      upperStarSectionMap (Profinite.padicAlgClRingObj ℓ) σ h
        (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).carrier v := by
  rw [WeilSheaf.stalkFunctor_obj_str, Iso.trans_hom, Functor.mapIso_hom,
    WeilSheaf.pow_ofId_str_hom_carrier ℓ M n,
    weilStalkComparison]
  exact comp_weilStalkComparison_app_eq_upperStarSectionMap ℓ _ σ x
    (point_hom_left_eq_id ((Iso.refl (point k)).pow (n + 1)).hom) hx h _
    (upperStarIsoIdOfIsSepClosed_inv_app_tensorUnit ℓ σ) v


end PointStalk

end AlgebraicGeometry.ProEtale.CondensedRing
