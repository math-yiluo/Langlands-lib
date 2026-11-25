/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarScalar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar

/-!
# Pullbacks of `Rⁱg_* ℚ̄_ℓ,T` as abelian sheaves, along arbitrary morphisms

Let `g : T ⟶ Y` be a morphism of schemes and `Rⁱg_* ℚ̄_ℓ,T` the abelian sheaf `Rⁱg_*` of the
abelian sheaf underlying `ℚ̄_ℓ,T`. For a sheaf `F` of `ℚ̄_ℓ`-modules on `S` and `q : S ⟶ Y`, an
`AlgebraicGeometry.ProEtale.AdicAbIdentification` is an isomorphism of abelian sheaves between
the abelian sheaf underlying `F` and `q^* Rⁱg_* ℚ̄_ℓ,T`, carrying the multiplication by `c ∈ ℚ̄_ℓ`
to `q^* Rⁱg_*` of the multiplication by `c` on `ℚ̄_ℓ,T`.

- `AlgebraicGeometry.ProEtale.AdicAbIdentification.ofUpperStar`: `q^* Rⁱg_* ℚ̄_ℓ,T` has one, for
  any `q` (not only weakly étale ones, as in
  `AlgebraicGeometry.ProEtale.adicUpperStarRightDerivedLowerStarUnitAbIso`);
- `AlgebraicGeometry.ProEtale.AdicAbIdentification.upperStar`: an identification for `F` along
  `q` gives one for `f^* F` along `f ≫ q`.

The scalars are compatible with arbitrary pullbacks, the pullback being left adjoint to the
pushforward, which commutes with the scalars on the nose
(`AlgebraicGeometry.ProEtale.upperStar_map_weilSmulNatTrans_app'`).
-/

@[expose] public section

universe u

open CategoryTheory

/-- A left adjoint of a functor intertwining two natural endomorphisms of the identity functors
intertwines them as well. -/
lemma CategoryTheory.Adjunction.map_app_eq_of_right {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (β : 𝟭 C ⟶ 𝟭 C) (β' : 𝟭 D ⟶ 𝟭 D)
    (h : ∀ N, G.map (β'.app N) = β.app (G.obj N)) (M : C) :
    F.map (β.app M) = β'.app (F.obj M) := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, h]
  exact (adj.unit.naturality (β.app M)).symm.trans (β.naturality (adj.unit.app M)).symm

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The pullback along an arbitrary morphism commutes with the multiplication by a scalar. -/
lemma upperStar_map_weilSmulNatTrans_app' {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (c : ULift.{u + 1} (PadicAlgCl l))
    (M : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (f)^*[WeilCoefficients.{u} l].map ((weilSmulNatTrans l Y c).app M) =
      (weilSmulNatTrans l Z c).app ((f)^*[WeilCoefficients.{u} l].obj M) :=
  (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).map_app_eq_of_right _ _
    (fun N ↦ lowerStar_map_weilSmulNatTrans_app f c N) M

variable {T Y S : Scheme.{u}} (g : T ⟶ Y) (i : ℕ)

variable (l) in
/-- The abelian sheaf `Rⁱg_*` of the abelian sheaf underlying `ℚ̄_ℓ,T`. -/
noncomputable abbrev rightDerivedLowerStarAdicAb : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} :=
  ((g)_*[Ab.{u + 1}].rightDerived i).obj
    ((weilCoefficientsForgetAb l T).obj (adicConstantSheaf l T))

/-- `Rⁱg_*` of the multiplication by `c ∈ ℚ̄_ℓ` on the abelian sheaf underlying `ℚ̄_ℓ,T`. -/
noncomputable abbrev rightDerivedLowerStarAdicAbSmul (c : ULift.{u + 1} (PadicAlgCl l)) :
    rightDerivedLowerStarAdicAb l g i ⟶ rightDerivedLowerStarAdicAb l g i :=
  ((g)_*[Ab.{u + 1}].rightDerived i).map ((weilCoefficientsForgetAb l T).map
    ((weilSmulNatTrans l T c).app (adicConstantSheaf l T)))

/-- An identification of the abelian sheaf underlying a sheaf `F` of `ℚ̄_ℓ`-modules on `S` with
`q^* Rⁱg_* ℚ̄_ℓ,T`, carrying the multiplication by `c ∈ ℚ̄_ℓ` to `q^* Rⁱg_*` of the multiplication
by `c` on `ℚ̄_ℓ,T`. -/
structure AdicAbIdentification (F : AdicSheaf l S) (q : S ⟶ Y) where
  /-- The isomorphism of abelian sheaves. -/
  iso : (weilCoefficientsForgetAb l S).obj F.X ≅
    (q)^*[Ab.{u + 1}].obj (rightDerivedLowerStarAdicAb l g i)
  hom_smul (c : ULift.{u + 1} (PadicAlgCl l)) :
    (weilCoefficientsForgetAb l S).map ((weilSmulNatTrans l S c).app F.X) ≫ iso.hom =
      iso.hom ≫ (q)^*[Ab.{u + 1}].map (rightDerivedLowerStarAdicAbSmul g i c)

namespace AdicAbIdentification

variable {g i}

/-- The identification of the abelian sheaf underlying a pullback with the pullback of the
underlying abelian sheaf, `forget (f^* M) ≅ f^* (forget M)`, commutes with the scalars. -/
lemma sheafComposeForget₂CompUpperStarIso_inv_smul {Z X : Scheme.{u}} (f : Z ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (c : ULift.{u + 1} (PadicAlgCl l)) :
    (weilCoefficientsForgetAb l Z).map
        ((weilSmulNatTrans l Z c).app ((f)^*[WeilCoefficients.{u} l].obj M)) ≫
      (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).inv.app M =
    (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).inv.app M ≫
      (f)^*[Ab.{u + 1}].map ((weilCoefficientsForgetAb l X).map
        ((weilSmulNatTrans l X c).app M)) := by
  have h := (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).inv.naturality
    ((weilSmulNatTrans l X c).app M)
  dsimp at h
  rw [upperStar_map_weilSmulNatTrans_app'] at h
  exact h

/-- **Pullback of an identification**: an identification for `F` along `q` gives one for `f^* F`
along `f ≫ q`. -/
noncomputable def upperStar {F : AdicSheaf l S} {q : S ⟶ Y} (e : AdicAbIdentification g i F q)
    {S' : Scheme.{u}} (f : S' ⟶ S) : AdicAbIdentification g i ((f)^*ᵃ[l].obj F) (f ≫ q) where
  iso := (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).symm.app F.X ≪≫
    (f)^*[Ab.{u + 1}].mapIso e.iso ≪≫
    (ProEtale.upperStarComp Ab.{u + 1} f q).symm.app (rightDerivedLowerStarAdicAb l g i)
  hom_smul c := by
    have h1 := sheafComposeForget₂CompUpperStarIso_inv_smul f F.X c
    have h2 := congrArg (f)^*[Ab.{u + 1}].map (e.hom_smul c)
    simp only [Functor.map_comp] at h2
    have h3 := (ProEtale.upperStarComp Ab.{u + 1} f q).inv.naturality
      (rightDerivedLowerStarAdicAbSmul g i c)
    rw [Iso.trans_hom, Iso.trans_hom]
    erw [reassoc_of% h1, reassoc_of% h2]
    erw [h3]
    rfl

variable (g i) in
/-- **The identification of `q^* Rⁱg_* ℚ̄_ℓ,T`**, for an arbitrary morphism `q : S ⟶ Y`. -/
noncomputable def ofUpperStar (q : S ⟶ Y) :
    AdicAbIdentification g i ((q)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g i)) q where
  iso := (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) q).symm.app _ ≪≫
    (q)^*[Ab.{u + 1}].mapIso ((weilCoefficientsForgetAb l Y).mapIso
      (adicRightDerivedLowerStarUnitForgetIso l g i)) ≪≫
    (q)^*[Ab.{u + 1}].mapIso ((rightDerivedLowerStarWeilCoefficientsForgetAbIso l g i).app _)
  hom_smul c := by
    have h1 := sheafComposeForget₂CompUpperStarIso_inv_smul q
      (adicRightDerivedLowerStarUnit l g i).X c
    have h2 := congrArg (weilCoefficientsForgetAb l Y).map
      ((weilSmulNatTrans l Y c).naturality (adicRightDerivedLowerStarUnitForgetIso l g i).hom)
    have h4 := rightDerived_lowerStar_map_weilSmulNatTrans_app g c i (adicConstantSheaf l T)
    have h5 := (rightDerivedLowerStarWeilCoefficientsForgetAbIso l g i).hom.naturality
      ((weilSmulNatTrans l T c).app (adicConstantSheaf l T))
    dsimp at h5
    simp only [Functor.id_map, Functor.map_comp] at h2
    have key : (weilCoefficientsForgetAb l Y).map
          ((weilSmulNatTrans l Y c).app (adicRightDerivedLowerStarUnit l g i).X) ≫
        (weilCoefficientsForgetAb l Y).map (adicRightDerivedLowerStarUnitForgetIso l g i).hom ≫
          (rightDerivedLowerStarWeilCoefficientsForgetAbIso l g i).hom.app
            (adicConstantSheaf l T) =
        (weilCoefficientsForgetAb l Y).map (adicRightDerivedLowerStarUnitForgetIso l g i).hom ≫
          (rightDerivedLowerStarWeilCoefficientsForgetAbIso l g i).hom.app
            (adicConstantSheaf l T) ≫ rightDerivedLowerStarAdicAbSmul g i c := by
      erw [← reassoc_of% h2]
      rw [← h4]
      erw [h5]
    have key' := congrArg (q)^*[Ab.{u + 1}].map key
    simp only [Functor.map_comp] at key'
    rw [Iso.trans_hom, Iso.trans_hom]
    erw [reassoc_of% h1]
    exact congrArg (fun φ ↦ _ ≫ φ) key'

end AdicAbIdentification

end AlgebraicGeometry.ProEtale
