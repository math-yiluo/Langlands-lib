/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible
public import WeilConjectures.WeilSheaf.GeometricFiberPullback

/-!
# Pulled-back Weil sheaves in the condensed model

Let `k₀` be a finite field, `X₀` a `k₀`-scheme, `p : X̄ ⟶ X₀` the projection of its geometric
fibre and `Fr_X` the geometric Galois Frobenius of `X̄`. An `ℓ`-adic sheaf `H` on `X₀` gives the
pro-étale Weil sheaf `p^* H` of the old model, with its canonical Weil structure
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`), and the module object `E H` over
`ℚ̲̄_ℓ,X₀` gives the condensed Weil object `p^* (E H)`, with its canonical Weil structure
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilLowerStar`). Through the comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` of the two models they agree
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- The components of the inverse mate of a square along two adjunctions. -/
lemma mateEquiv_symm_natTrans_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (β : TwoSquare R₁ H G R₂)
    (a : A) : ((mateEquiv adj₁ adj₂).symm β).app a =
      L₂.map (G.map (adj₁.unit.app a)) ≫ L₂.map (β.app (L₁.obj a)) ≫
        adj₂.counit.app (H.obj (L₁.obj a)) := by
  simp [mateEquiv_symm_apply]

/-- A square `α` is the inverse mate of `β` as soon as `β` intertwines the units of the two
adjunctions with `α`. -/
lemma mateEquiv_eq_of_unit_comp_map (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    (β : TwoSquare R₁ H G R₂)
    (h : ∀ a, G.map (adj₁.unit.app a) ≫ β.app (L₁.obj a) =
      adj₂.unit.app (G.obj a) ≫ R₂.map (α.app a)) :
    mateEquiv adj₁ adj₂ α = β := by
  rw [← Equiv.eq_symm_apply]
  refine NatTrans.ext (funext fun a ↦ ?_)
  rw [mateEquiv_symm_natTrans_app, ← Functor.map_comp_assoc, h]
  simp

/-- Unit compatibility with the forward comparison determines the mate of its inverse. -/
private lemma mateEquiv_inv_eq_of_unit_comp_map_hom (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₁ ⋙ H ≅ G ⋙ L₂) (β : TwoSquare R₁ H G R₂)
    (h : ∀ a, G.map (adj₁.unit.app a) ≫ β.app (L₁.obj a) ≫ R₂.map (α.hom.app a) =
      adj₂.unit.app (G.obj a)) :
    mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.inv) = β := by
  apply mateEquiv_eq_of_unit_comp_map
  intro a
  rw [← h, Category.assoc, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- **An abstract coherence square for comparisons of structure isomorphisms.** Let
`c : P ⋙ E' ≅ E ⋙ P'` be a comparison of two functors `P` and `P'` along `E` and `E'`. Suppose
that the isomorphisms `P ⋙ L ≅ P ⋙ A ≅ Q ≅ P` and `P' ⋙ L' ≅ P' ⋙ A' ≅ Q' ≅ P'` (built from
`i : A ≅ L`, `m : Q ≅ P ⋙ A`, `t : Q ≅ P` and their primed analogues) are compatible with
comparisons `cQ : Q ⋙ E' ≅ E ⋙ Q'`, `cA : A ⋙ E' ≅ E' ⋙ A'` and `d : L ⋙ E' ≅ E' ⋙ L'`. Then `c`
intertwines the two isomorphisms `P ⋙ L ≅ P` and `P' ⋙ L' ≅ P'`. -/
lemma comparison_hom_app_comp_structure_hom_app {A₁ A₂ A₃ A₄ : Type*} [Category* A₁]
    [Category* A₂] [Category* A₃] [Category* A₄] {E : A₁ ⥤ A₃} {E' : A₂ ⥤ A₄}
    {P Q : A₁ ⥤ A₂} {P' Q' : A₃ ⥤ A₄} {A L : A₂ ⥤ A₂} {A' L' : A₄ ⥤ A₄}
    (c : P ⋙ E' ≅ E ⋙ P') (cQ : Q ⋙ E' ≅ E ⋙ Q') (cA : A ⋙ E' ≅ E' ⋙ A')
    (d : L ⋙ E' ≅ E' ⋙ L') (i : A ≅ L) (i' : A' ≅ L') (m : Q ≅ P ⋙ A) (m' : Q' ≅ P' ⋙ A')
    (t : Q ≅ P) (t' : Q' ≅ P')
    (hA : ∀ M, cA.inv.app M = i'.hom.app (E'.obj M) ≫ d.inv.app M ≫ E'.map (i.inv.app M))
    (hm : ∀ M, cQ.inv.app M = m'.hom.app (E.obj M) ≫ A'.map (c.inv.app M) ≫
      cA.inv.app (P.obj M) ≫ E'.map (m.inv.app M))
    (ht : ∀ M, t'.hom.app (E.obj M) ≫ c.inv.app M = cQ.inv.app M ≫ E'.map (t.hom.app M))
    (H : A₁) :
    L'.map (c.hom.app H) ≫
        (Functor.isoWhiskerLeft P' i'.symm ≪≫ m'.symm ≪≫ t').hom.app (E.obj H) =
      (d.symm.app (P.obj H) ≪≫
          E'.mapIso ((Functor.isoWhiskerLeft P i.symm ≪≫ m.symm ≪≫ t).app H)).hom ≫
        c.hom.app H := by
  refine (Iso.comp_inv_eq (c.app H)).mp ?_
  rw [Iso.app_inv]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
    Functor.map_comp]
  rw [ht, hm, hA]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc]
  exact Iso.hom_inv_id_map_assoc (c.app H) _ _

end CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

open CategoryTheory.TwoSquare

/-- **Transport of pulled-back structures along comparisons.** In the situation of
`CategoryTheory.comparison_hom_app_comp_structure_hom_app`, with the compatibilities stated as
equations of `2`-squares, the comparison `c : P ⋙ E' ≅ E ⋙ P'` is an isomorphism between the
algebras `(P x, σ_x)` transported along `E'` and the algebras `(P' (E x), σ'_{E x})`, where
`σ : P ⋙ L ≅ P ⋙ A ≅ Q ≅ P` and `σ' : P' ⋙ L' ≅ P' ⋙ A' ≅ Q' ≅ P'`. -/
noncomputable def functorOfNatIsoCompMapOfNatIsoIsoOfTwoSquare {A₁ A₂ A₃ A₄ : Type*}
    [Category* A₁] [Category* A₂] [Category* A₃] [Category* A₄] {E : A₁ ⥤ A₃} {E' : A₂ ⥤ A₄}
    {P Q : A₁ ⥤ A₂} {P' Q' : A₃ ⥤ A₄} {A L : A₂ ⥤ A₂} {A' L' : A₄ ⥤ A₄}
    (c : P ⋙ E' ≅ E ⋙ P') (cQ : Q ⋙ E' ≅ E ⋙ Q') (cA : A ⋙ E' ≅ E' ⋙ A')
    (d : L ⋙ E' ≅ E' ⋙ L') (i : A ≅ L) (i' : A' ≅ L') (m : Q ≅ P ⋙ A) (m' : Q' ≅ P' ⋙ A')
    (t : Q ≅ P) (t' : Q' ≅ P') (σ : P ⋙ L ≅ P) (σ' : P' ⋙ L' ≅ P')
    (hσ : σ = Functor.isoWhiskerLeft P i.symm ≪≫ m.symm ≪≫ t)
    (hσ' : σ' = Functor.isoWhiskerLeft P' i'.symm ≪≫ m'.symm ≪≫ t')
    (hA : TwoSquare.mk _ _ _ _ cA.inv =
      ((TwoSquare.mk _ _ _ _ d.inv).whiskerRight i'.hom).whiskerLeft i.inv)
    (hm : TwoSquare.mk _ _ _ _ cQ.inv =
      ((TwoSquare.mk _ _ _ _ c.inv ≫ᵥ TwoSquare.mk _ _ _ _ cA.inv).whiskerRight
        m'.hom).whiskerLeft m.inv)
    (ht : TwoSquare.mk _ _ _ _ c.inv =
      ((TwoSquare.mk _ _ _ _ cQ.inv).whiskerRight t'.inv).whiskerLeft t.hom) :
    functorOfNatIso P σ ⋙ mapOfNatIso d.symm ≅ E ⋙ functorOfNatIso P' σ' :=
  isoMkOfForget c fun H ↦ by
    subst hσ hσ'
    refine comparison_hom_app_comp_structure_hom_app c cQ cA d i i' m m' t t'
      (fun M ↦ ?_) (fun M ↦ ?_) (fun M ↦ ?_) H
    · simpa [TwoSquare.whiskerLeft, TwoSquare.whiskerRight] using NatTrans.congr_app hA M
    · simpa [TwoSquare.whiskerLeft, TwoSquare.whiskerRight] using NatTrans.congr_app hm M
    · have h := NatTrans.congr_app ht M
      simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
      rw [h]
      simp

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.TwoSquare

variable (l : ℕ) [Fact l.Prime] {S T : Scheme.{u}}

/-- **The pullback comparison of the two models is the mate of the pushforward comparison**:
`E ⋙ f^* ⟶ f^*ᵃ ⋙ E` (`adicUpperStarCompCondensedModIso`) is the mate, for `f^*ᵃ ⊣ f_*ᵃ` and
`f^* ⊣ f_*`, of the pushforward comparison `f_*ᵃ ⋙ E ≅ E ⋙ f_*`
(`adicLowerStarCompCondensedModIso`). -/
lemma mateEquiv_adicUpperStarCompCondensedModIso_inv (f : S ⟶ T) :
    mateEquiv (adicUpperStarLowerStarAdjunction l f)
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
        (TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l f).inv) =
      TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l f).hom := by
  apply (mateEquiv (adicSheafEquivCondensedMod l S).toAdjunction
    (adicSheafEquivCondensedMod l T).toAdjunction).injective
  have h1 := iterated_mateEquiv_conjugateEquiv (adicUpperStarLowerStarAdjunction l f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
    (adicSheafEquivCondensedMod l T).toAdjunction (adicSheafEquivCondensedMod l S).toAdjunction
    (TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l f).inv)
  have h2 : conjugateEquiv ((adicUpperStarLowerStarAdjunction l f).comp
      (adicSheafEquivCondensedMod l S).toAdjunction)
      ((adicSheafEquivCondensedMod l T).toAdjunction.comp
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f))
      (adicUpperStarCompCondensedModIso l f).inv =
        (condensedModInverseCompAdicLowerStarIso l f).hom :=
    (conjugateEquiv _ _).apply_symm_apply _
  refine NatTrans.ext (funext fun M ↦ ?_)
  have h3 := NatTrans.congr_app (h1.trans h2) M
  refine h3.trans ?_
  simp [condensedModInverseCompAdicLowerStarIso, mateEquiv_apply]

/-- The pullback comparison of the two models is compatible with the composition isomorphisms
of the pullbacks. -/
lemma adicUpperStarCompCondensedModIso_comp_inv {R : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ R) :
    TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l (f ≫ g)).inv =
      ((TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l g).inv ≫ᵥ
          TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l f).inv).whiskerRight
        (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).hom).whiskerLeft
        (adicUpperStarComp l f g).inv := by
  apply (mateEquiv (adicUpperStarLowerStarAdjunction l (f ≫ g))
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) (f ≫ g))).injective
  have hold : conjugateEquiv (adicUpperStarLowerStarAdjunction l (f ≫ g))
      ((adicUpperStarLowerStarAdjunction l g).comp (adicUpperStarLowerStarAdjunction l f))
      (adicUpperStarComp l f g).inv = (adicLowerStarComp l f g).inv :=
    (conjugateEquiv _ _).apply_symm_apply _
  have hnew : conjugateEquiv
      ((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) g).comp
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f))
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) (f ≫ g))
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).hom =
        (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g).hom :=
    (conjugateEquiv _ _).apply_symm_apply _
  rw [mateEquiv_adicUpperStarCompCondensedModIso_inv,
    conjugateEquiv_mateEquiv_vcomp _ ((adicUpperStarLowerStarAdjunction l g).comp
      (adicUpperStarLowerStarAdjunction l f)),
    mateEquiv_conjugateEquiv_vcomp _ ((CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj l) g).comp
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)),
    mateEquiv_hcomp, mateEquiv_adicUpperStarCompCondensedModIso_inv,
    mateEquiv_adicUpperStarCompCondensedModIso_inv, hold, hnew]
  refine NatTrans.ext (funext fun M ↦ ?_)
  refine Mod.Hom.ext ?_
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Mod.comp_hom',
    adicLowerStarCompCondensedModIso_hom_app_hom, CondensedRing.lowerStar_map_hom,
    CondensedRing.lowerStarComp_hom_app_hom, adicSheafEquivCondensedMod_functor_map_hom,
    adicLowerStarComp_inv_app_hom]
  erw [weilCoefficientsForgetAb_map_lowerStarComp_inv_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← lowerStarComp_hom_app_adicSheafEquivCondensedMod_obj_X l f g M, Iso.inv_hom_id_app]
  rfl

/-- The conjugate of the identification `e^* ≅ (e⁻¹)_*` of `ℓ`-adic sheaves is the identity. -/
lemma conjugateEquiv_adicUpperStarIsoLowerStarInv_inv (e : S ≅ T) :
    conjugateEquiv (adicUpperStarLowerStarAdjunction l e.hom)
      (adicLowerStarEquivalence l e).symm.toAdjunction (adicUpperStarIsoLowerStarInv l e).inv =
        𝟙 _ := by
  unfold adicUpperStarIsoLowerStarInv
  exact CategoryTheory.conjugateEquiv_leftAdjointUniq_inv _ _

/-- The conjugate of the identification `e^* ≅ (e⁻¹)_*` of module objects is the identity. -/
lemma conjugateEquiv_upperStarIsoLowerStarInv_hom (e : S ≅ T) :
    conjugateEquiv (CondensedRing.lowerStarInvAdjunction (Profinite.padicAlgClRingObj l) e)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) e.hom)
      (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l) e).hom = 𝟙 _ := by
  rw [CondensedRing.upperStarIsoLowerStarInv_eq_leftAdjointUniq]
  exact CategoryTheory.conjugateEquiv_leftAdjointUniq_hom _ _

/-- Forgetting the `ℚ̄_ℓ`-module structure commutes with the identity isomorphisms of the
pushforwards. -/
lemma weilCoefficientsForgetAb_map_lowerStarId_inv_app (G : Sheaf (Scheme.ProEt.topology T)
    (WeilCoefficients.{u} l)) :
    (weilCoefficientsForgetAb l T).map ((lowerStarId (WeilCoefficients.{u} l) T).inv.app G) =
      (lowerStarId Ab.{u + 1} T).inv.app ((weilCoefficientsForgetAb l T).obj G) :=
  rfl

/-- Forgetting the `ℚ̄_ℓ`-module structure commutes with the transports of the pushforwards. -/
lemma weilCoefficientsForgetAb_map_lowerStarCongr_inv_app {g g' : S ⟶ T} (h : g = g')
    (G : Sheaf (Scheme.ProEt.topology S) (WeilCoefficients.{u} l)) :
    (weilCoefficientsForgetAb l T).map ((lowerStarCongr (WeilCoefficients.{u} l) h).inv.app G) =
      (lowerStarCongr Ab.{u + 1} h).inv.app ((weilCoefficientsForgetAb l S).obj G) := by
  subst h
  rfl

/-- The comparison of the two models intertwines the units of the adjunctions `(e⁻¹)_* ⊣ e_*`. -/
lemma adicSheafEquivCondensedMod_map_unit_comp (e : S ≅ T) (x : AdicSheaf l T) :
    (adicSheafEquivCondensedMod l T).functor.map
        ((adicLowerStarEquivalence l e).symm.toAdjunction.unit.app x) ≫
      (adicLowerStarCompCondensedModIso l e.hom).hom.app ((e.inv)_*ᵃ[l].obj x) ≫
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) e.hom).map
          ((adicLowerStarCompCondensedModIso l e.inv).hom.app x) =
      (CondensedRing.lowerStarInvAdjunction (Profinite.padicAlgClRingObj l) e).unit.app
        ((adicSheafEquivCondensedMod l T).functor.obj x) := by
  rw [Equivalence.toAdjunction_unit, Equivalence.symm_unit,
    CondensedRing.lowerStarInvAdjunction_unit_app]
  refine Mod.Hom.ext ?_
  simp only [Mod.comp_hom', adicSheafEquivCondensedMod_functor_map_hom,
    adicLowerStarCompCondensedModIso_hom_app_hom, CondensedRing.lowerStar_map_hom,
    CondensedRing.lowerStarComp_inv_app_hom, CondensedRing.lowerStarCongr_inv_app_hom,
    CondensedRing.lowerStarId_inv_app_hom_eq]
  have hc : (adicLowerStarEquivalence l e).counitInv.app x =
      (adicLowerStarId l T).inv.app x ≫ (adicLowerStarCongr l e.inv_hom_id).inv.app x ≫
        (adicLowerStarComp l e.inv e.hom).inv.app x := by
    exact Category.assoc _ _ _
  rw [hc]
  simp only [Mod.comp_hom', CategoryTheory.Functor.map_comp, adicLowerStarId_inv_app_hom,
    adicLowerStarCongr_inv_app_hom, adicLowerStarComp_inv_app_hom]
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    weilCoefficientsForgetAb_map_lowerStarId_inv_app,
    weilCoefficientsForgetAb_map_lowerStarCongr_inv_app,
    weilCoefficientsForgetAb_map_lowerStarComp_inv_app]
  rfl

/-- The pushforward comparisons of the two models along `e` and `e⁻¹` are mates for the
adjunctions `(e⁻¹)_* ⊣ e_*` of both models. -/
lemma mateEquiv_adicLowerStarCompCondensedModIso_inv (e : S ≅ T) :
    mateEquiv (adicLowerStarEquivalence l e).symm.toAdjunction
        (CondensedRing.lowerStarInvAdjunction (Profinite.padicAlgClRingObj l) e)
        (TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l e.inv).inv) =
      TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l e.hom).hom := by
  exact mateEquiv_inv_eq_of_unit_comp_map_hom _ _
    (adicLowerStarCompCondensedModIso l e.inv) _ (adicSheafEquivCondensedMod_map_unit_comp l e)

/-- The pullback comparison of the two models along an isomorphism `e` is the pushforward
comparison along `e⁻¹`, through the identifications `e^* ≅ (e⁻¹)_*` of both models. -/
lemma adicUpperStarCompCondensedModIso_inv_of_iso (e : S ≅ T) :
    TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l e.hom).inv =
      ((TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l e.inv).inv).whiskerRight
        (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l) e).hom).whiskerLeft
        (adicUpperStarIsoLowerStarInv l e).inv := by
  apply (mateEquiv (adicUpperStarLowerStarAdjunction l e.hom)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) e.hom)).injective
  rw [mateEquiv_adicUpperStarCompCondensedModIso_inv,
    conjugateEquiv_mateEquiv_vcomp _ (adicLowerStarEquivalence l e).symm.toAdjunction,
    mateEquiv_conjugateEquiv_vcomp _
      (CondensedRing.lowerStarInvAdjunction (Profinite.padicAlgClRingObj l) e),
    conjugateEquiv_adicUpperStarIsoLowerStarInv_inv, conjugateEquiv_upperStarIsoLowerStarInv_hom]
  rw [mateEquiv_adicLowerStarCompCondensedModIso_inv]
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]

/-- The pullback comparison of the two models is compatible with the transports of the
pullbacks along an equation of morphisms. -/
lemma adicUpperStarCompCondensedModIso_inv_congr {f f' : S ⟶ T} (h : f = f') :
    TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l f').inv =
      ((TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l f).inv).whiskerRight
        (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h).inv).whiskerLeft
        (adicUpperStarCongr l h).hom := by
  subst h
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, CondensedRing.upperStarCongr,
    adicUpperStarCongr]

/-- **Weil-type structures of pullbacks in the two models**: for `p : S ⟶ T` and an
automorphism `e` of `S` with `e ≫ p = p`, the pullback comparison `E (p^*ᵃ H) ≅ p^* (E H)` is an
isomorphism between the algebras `(p^*ᵃ H, (e⁻¹)_*ᵃ p^*ᵃ H ≅ e^*ᵃ p^*ᵃ H ≅ (e ≫ p)^*ᵃ H = p^*ᵃ H)`
transported along `E` and the algebras
`(p^* (E H), (e⁻¹)_* p^* (E H) ≅ e^* p^* (E H) ≅ (e ≫ p)^* (E H) = p^* (E H))`. The structure
isomorphisms are passed as `σ` and `σ'` together with their descriptions `hσ` and `hσ'`. -/
noncomputable def adicUpperStarFunctorOfNatIsoCompCondensedModIso (p : S ⟶ T) (e : S ≅ S)
    (h : e.hom ≫ p = p) (σ : (p)^*ᵃ[l] ⋙ (e.inv)_*ᵃ[l] ≅ (p)^*ᵃ[l])
    (σ' : CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p ⋙
      CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) e.inv ≅
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p)
    (hσ : σ = Functor.isoWhiskerLeft (p)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l e).symm ≪≫
      (adicUpperStarComp l e.hom p).symm ≪≫ adicUpperStarCongr l h)
    (hσ' : σ' = Functor.isoWhiskerLeft (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p)
        (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l) e).symm ≪≫
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) e.hom p).symm ≪≫
        CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h) :
    Endofunctor.IsoAlgebra.functorOfNatIso (p)^*ᵃ[l] σ ⋙
        Endofunctor.IsoAlgebra.mapOfNatIso (adicLowerStarCompCondensedModIso l e.inv).symm ≅
      (adicSheafEquivCondensedMod l T).functor ⋙
        Endofunctor.IsoAlgebra.functorOfNatIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p) σ' :=
  Endofunctor.IsoAlgebra.functorOfNatIsoCompMapOfNatIsoIsoOfTwoSquare
    (adicUpperStarCompCondensedModIso l p) (adicUpperStarCompCondensedModIso l (e.hom ≫ p))
    (adicUpperStarCompCondensedModIso l e.hom) (adicLowerStarCompCondensedModIso l e.inv)
    (adicUpperStarIsoLowerStarInv l e)
    (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l) e)
    (adicUpperStarComp l e.hom p)
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) e.hom p)
    (adicUpperStarCongr l h) (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h)
    σ σ' hσ hσ' (adicUpperStarCompCondensedModIso_inv_of_iso l e)
    (adicUpperStarCompCondensedModIso_comp_inv l e.hom p)
    (adicUpperStarCompCondensedModIso_inv_congr l h)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The geometric fibre Weil objects are the algebras given by the pullback `p^*` and its
structure isomorphism `(Fr_X⁻¹)_* p^* ≅ p^*`. -/
lemma geometricFiberWeilLowerStar_eq :
    geometricFiberWeilLowerStar Λ f =
      Endofunctor.IsoAlgebra.functorOfNatIso (upperStar Λ f.geometricFiberProj)
        (geometricFiberProjLowerStarFrobeniusIso Λ f) :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The canonical Weil structure `Fr_X^* p^* ≅ (Fr_X ≫ p)^* = p^*` of the pulled-back sheaves,
unfolded. -/
lemma geometricFiberPullbackFrobeniusIso_eq :
    geometricFiberPullbackFrobeniusIso k₀ l X =
      Functor.isoWhiskerLeft ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l]
          (adicUpperStarIsoLowerStarInv l
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).symm ≪≫
        (adicUpperStarComp l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).symm ≪≫
        adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) :=
  rfl

/-- The pulled-back Weil sheaves transported to the condensed model, as the transport of the
algebras `(p^* H, Fr_X^* p^* H ≅ p^* H)` along the comparison of the two models. -/
lemma geometricFiberPullback_comp_toCondensed_eq :
    geometricFiberPullback k₀ l X ⋙ toCondensed k₀ l X =
      Endofunctor.IsoAlgebra.functorOfNatIso _ (geometricFiberPullbackFrobeniusIso k₀ l X) ⋙
        Endofunctor.IsoAlgebra.mapOfNatIso (adicLowerStarCompCondensedModIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).symm :=
  rfl

/-- **Pulled-back Weil sheaves in the two models**: the old-model Weil sheaf `p^* H` with its
canonical Weil structure becomes, through `toCondensed`, the condensed Weil object `p^* (E H)`
with its canonical Weil structure. -/
noncomputable def geometricFiberPullbackCompToCondensedIso :
    geometricFiberPullback k₀ l X ⋙ toCondensed k₀ l X ≅
      (adicSheafEquivCondensedMod l X).functor ⋙
        CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)) :=
  -- the transports `eqToIso` (along `rfl`-lemmas) keep the kernel from unfolding the Weil
  -- structures, whose nested proofs are abstracted differently
  eqToIso (geometricFiberPullback_comp_toCondensed_eq k₀ l X) ≪≫
    adicUpperStarFunctorOfNatIsoCompCondensedModIso l _ _
      (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)
      (geometricFiberPullbackFrobeniusIso k₀ l X)
      (CondensedRing.geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj l) _)
      (geometricFiberPullbackFrobeniusIso_eq k₀ l X)
      (CondensedRing.geometricFiberProjLowerStarFrobeniusIso_eq _ _) ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (CondensedRing.geometricFiberWeilLowerStar_eq _ _).symm)

end AlgebraicGeometry.ProEtaleWeilSheaf
