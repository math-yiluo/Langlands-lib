/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFunctor

/-!
# The Frobenius of the geometric stalks of Weil sheaves
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section GlobalSections


/-- The global sections of `(e¹)⁻¹_* N` and of `(e⁻¹)_* N` are identified compatibly with the
identification `(e¹)⁻¹_* N ≅ (e⁻¹)_* (e⁰)⁻¹_* N ≅ (e⁻¹)_* N` defining the first iterate of a
Weil structure. -/
private lemma globalSectionsLowerStarIso_inv_comp_pow_one {Y : Scheme.{u}} (e : Aut Y)
    (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) (h₀ : (e ^ 0).asIso.inv = 𝟙 Y)
    (h₁ : (e ^ 1).asIso.inv = (e ^ 0).asIso.inv ≫ e.asIso.inv) :
    (ProEtale.globalSectionsLowerStarIso _ (e ^ 1).asIso.inv).inv.app N ≫
      (Sheaf.Γ _ _).map ((ProEtale.lowerStarCongr _ h₁).hom.app N ≫
          (ProEtale.lowerStarComp _ (e ^ 0).asIso.inv e.asIso.inv).inv.app N ≫
          (e.asIso.inv)_*[_].map ((ProEtale.lowerStarCongr _ h₀).hom.app N ≫
            (ProEtale.lowerStarId _ Y).hom.app N)) =
    (ProEtale.globalSectionsLowerStarIso _ e.asIso.inv).inv.app N := by
  have e₀ := ProEtale.globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h₀ N
  rw [ProEtale.globalSectionsLowerStarIso_id] at e₀
  have e₁ := ProEtale.globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h₁ N
  have e₂ := ProEtale.globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) (e ^ 0).asIso.inv
    e.asIso.inv N
  have e₃ :=
    (ProEtale.globalSectionsLowerStarIso (WeilCoefficients.{u} l) e.asIso.inv).hom.naturality
    ((ProEtale.lowerStarCongr _ h₀).hom.app N ≫ (ProEtale.lowerStarId _ _).hom.app N)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc, Functor.id_obj] at e₃
  rw [← cancel_mono ((ProEtale.globalSectionsLowerStarIso _ e.asIso.inv).hom.app N)]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  rw [e₃, e₀, ← e₂]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [e₁, Iso.inv_hom_id_app]

variable (F : WeilSheaf k₀ l X)

/-- The first iterate `φ₁ : (Fr¹)^* F ≅ F` of the Weil structure, on the underlying sheaves. -/
lemma forget_map_frobeniusPowIso_one_hom
    (h₀ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _)
    (h₁ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv) :
    (ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso 1).hom =
      (ProEtale.lowerStarCongr _ h₁).hom.app F.obj.carrier.X ≫
        (ProEtale.lowerStarComp _
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app
            F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          ((ProEtale.lowerStarCongr _ h₀).hom.app F.obj.carrier.X ≫
            (ProEtale.lowerStarId _ _).hom.app F.obj.carrier.X) ≫
        (ProEtale.AdicSheaf.forget _).map F.obj.str.hom := by
  simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, ProEtale.adicLowerStarId, NatIso.trans_app, Category.assoc]
  rfl

/-- The Frobenius of the global sections through the first iterate `φ₁` of the Weil structure
is the Frobenius through `φ`. -/
lemma globalSectionsLowerStarIso_inv_comp_frobeniusPowIso_one :
    (ProEtale.globalSectionsLowerStarIso _
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.inv).inv.app
          F.obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso 1).hom) =
    (ProEtale.globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app F.obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map F.obj.str.hom) := by
  have h₀ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _ := by
    rw [pow_zero]; rfl
  have h₁ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv := by
    rw [pow_succ, Aut.mul_asIso, Iso.trans_inv]
  rw [forget_map_frobeniusPowIso_one_hom F h₀ h₁,
    ← globalSectionsLowerStarIso_inv_comp_pow_one _ _ h₀ h₁]
  simp only [Functor.map_comp, Category.assoc]

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

lemma globalSectionsToStalkObj_eq :
    F.globalSectionsToStalkObj s =
      (ProEtale.globalSectionsToUpperStar _ s).app F.obj.carrier.X :=
  rfl

/-- Restricting global sections to the stalk at `s` and then passing to the stalk at the
reparametrisation `σᵐ ≫ s` is restricting to the stalk at `σᵐ ≫ s`. -/
lemma globalSectionsToStalkObj_comp_stalkObjSpecFrobeniusPowIso_inv (m : ℕ) :
    F.globalSectionsToStalkObj s ≫ (F.stalkObjSpecFrobeniusPowIso m s).inv =
      F.globalSectionsToStalkObj ((specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) := by
  rw [Iso.comp_inv_eq, globalSectionsToStalkObj_eq, globalSectionsToStalkObj_eq]
  have h := ProEtale.globalSectionsToUpperStar_comp _ (specGeometricFrobenius k₀ ^ m).asIso.hom s
    F.obj.carrier.X
  simp only [stalkObjSpecFrobeniusPowIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    reassoc_of% h, ProEtale.globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso,
    Category.comp_id]

/-- Restriction of global sections to equal geometric points. -/
lemma globalSectionsToStalkObj_comp_eqToHom {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (h : t = t') :
    F.globalSectionsToStalkObj t ≫ eqToHom (congrArg F.stalkObj h) =
      F.globalSectionsToStalkObj t' := by
  subst h
  simp

/-- Restricting global sections to the stalk at `s ≫ Frᵐ` and transporting to the stalk at `s`
along the Weil structure is restricting the image of the sections under `φ_m`. -/
lemma globalSectionsToStalkObj_comp_stalkObjFrobeniusPowIso_hom (m : ℕ) :
    F.globalSectionsToStalkObj
        (s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom) ≫
      (F.stalkObjFrobeniusPowIso m s).hom =
    (ProEtale.globalSectionsLowerStarIso _
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv).inv.app
          F.obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom) ≫
      F.globalSectionsToStalkObj s := by
  rw [globalSectionsToStalkObj_eq, globalSectionsToStalkObj_eq]
  have h := ProEtale.globalSectionsToUpperStar_comp _ s
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom F.obj.carrier.X
  have h' := ProEtale.globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso
    (WeilCoefficients.{u} l) ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso
      F.obj.carrier.X
  simp only [ProEtale.globalSectionsUpperStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at h'
  rw [← Category.assoc] at h'
  replace h' := (Iso.comp_hom_eq_id ((ProEtale.globalSectionsLowerStarIso _
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv).app _)).1 h'
  simp only [stalkObjFrobeniusPowIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, reassoc_of% h]
  have nat {A B : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)} (f : A ⟶ B) :
      (ProEtale.globalSectionsToUpperStar _ s).app A ≫ (Sheaf.Γ _ _).map ((s)^*[_].map f) =
        (Sheaf.Γ _ _).map f ≫ (ProEtale.globalSectionsToUpperStar _ s).app B :=
    ((ProEtale.globalSectionsToUpperStar _ s).naturality f).symm
  rw [reassoc_of% nat, nat, reassoc_of% h']
  rfl

/-- The restriction of global sections to a stalk intertwines the Frobenius of the global
sections with the Frobenius of the stalk, as morphisms. -/
lemma globalSectionsToStalkObj_comp_stalkAt_iso
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.hom =
      (specGeometricFrobenius k₀ ^ 1).asIso.hom ≫ s) :
    F.globalSectionsToStalkObj s ≫ ((F.stalkObjSpecFrobeniusPowIso 1 s).symm ≪≫
        eqToIso (congrArg F.stalkObj hs.symm) ≪≫ F.stalkObjFrobeniusPowIso 1 s).hom =
      ((ProEtale.globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).symm.app
          F.obj.carrier.X ≪≫
        (Sheaf.Γ _ _).mapIso ((ProEtale.AdicSheaf.forget _).mapIso F.obj.str)).hom ≫
      F.globalSectionsToStalkObj s := by
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [reassoc_of% globalSectionsToStalkObj_comp_stalkObjSpecFrobeniusPowIso_inv,
    reassoc_of% (globalSectionsToStalkObj_comp_eqToHom F hs.symm),
    globalSectionsToStalkObj_comp_stalkObjFrobeniusPowIso_hom,
    reassoc_of% globalSectionsLowerStarIso_inv_comp_frobeniusPowIso_one]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private theorem toModuleCat_map_comp_apply {M N P : WeilCoefficients.{u} l} (f : M ⟶ N)
    (g : N ⟶ P) (x : (WeilCoefficients.toModuleCat l).obj M) :
    ((WeilCoefficients.toModuleCat l).map (f ≫ g)).hom x =
      ((WeilCoefficients.toModuleCat l).map g).hom
        (((WeilCoefficients.toModuleCat l).map f).hom x) := by
  rw [Functor.map_comp]
  rfl

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private theorem linearEquivOfIso_apply {M N : WeilCoefficients.{u} l} (e : M ≅ N)
    (x : (WeilCoefficients.toModuleCat l).obj M) :
    WeilCoefficients.linearEquivOfIso e x = ((WeilCoefficients.toModuleCat l).map e.hom).hom x :=
  rfl

private theorem globalSections_frobenius_eq [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    F.globalSections.frobenius = WeilCoefficients.linearEquivOfIso
      ((ProEtale.globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).symm.app
          F.obj.carrier.X ≪≫
        (Sheaf.Γ _ _).mapIso ((ProEtale.AdicSheaf.forget _).mapIso F.obj.str)) :=
  rfl

private theorem stalkAt_frobenius_eq' (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) :=
  rfl

/-- The restriction of global sections to the stalk at a geometric point `s` with
`s ≫ Fr = σ ≫ s`, for instance a point over a `k₀`-rational point, intertwines the Frobenius of
`Γ(X̄, F)` with the Frobenius of `F_s` relative to `k₀`:

```
          Fr
  Γ(X̄, F) ---> Γ(X̄, F)
     |            |
     v            v
    F_s  -----> F_s
          Fr
```
-/
theorem globalSectionsToStalkObj_frobenius [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.hom =
      (specGeometricFrobenius k₀ ^ 1).asIso.hom ≫ s)
    (a : F.globalSections.carrier) :
    ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom
        (F.globalSections.frobenius a) =
      (F.stalkAt s 1 hs).frobenius
        (((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a) := by
  -- the intermediate equations are stated with explicit arguments to keep the kernel fast
  let eΓ := (ProEtale.globalSectionsLowerStarIso _
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).symm.app
          F.obj.carrier.X ≪≫
      (Sheaf.Γ _ _).mapIso ((ProEtale.AdicSheaf.forget _).mapIso F.obj.str)
  let es := (F.stalkObjSpecFrobeniusPowIso 1 s).symm ≪≫
    eqToIso (congrArg F.stalkObj hs.symm) ≪≫ F.stalkObjFrobeniusPowIso 1 s
  have h₀ := toModuleCat_map_comp_apply eΓ.hom (F.globalSectionsToStalkObj s) a
  have h₁ := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom a)
    (globalSectionsToStalkObj_comp_stalkAt_iso F s hs)
  have h₂ := toModuleCat_map_comp_apply (F.globalSectionsToStalkObj s) es.hom a
  have e₁ := (LinearEquiv.congr_fun (globalSections_frobenius_eq F) a).trans
    (linearEquivOfIso_apply eΓ a)
  have e₂ := (LinearEquiv.congr_fun (stalkAt_frobenius_eq' F s 1 hs)
    (((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a)).trans
      (linearEquivOfIso_apply es
        (((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a))
  exact (congrArg ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom
    e₁).trans (h₀.symm.trans (h₁.symm.trans (h₂.trans e₂.symm)))

end GlobalSections


section Transport

variable (F : WeilSheaf k₀ l X)

/-- The iterated Weil structure `φ_m`, as a morphism `(Frᵐ)^* F ⟶ F` of the underlying sheaves,
through the identification `(Frᵐ)^* ≅ (Fr⁻ᵐ)_*`. -/
noncomputable def frobeniusPowStr (m : ℕ) :
    ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)^*[
      WeilCoefficients.{u} l]
      ).obj F.obj.carrier.X ⟶ F.obj.carrier.X :=
  (ProEtale.upperStarIsoLowerStarInv _ _).hom.app F.obj.carrier.X ≫
    (ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom

/-- The Weil structure `φ`, as a morphism `Fr^* F ⟶ F` of the underlying sheaves. -/
noncomputable def frobeniusStr :
    (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[WeilCoefficients.{u} l]
      ).obj F.obj.carrier.X ⟶ F.obj.carrier.X :=
  (ProEtale.upperStarIsoLowerStarInv _ _).hom.app F.obj.carrier.X ≫
    (ProEtale.AdicSheaf.forget _).map F.obj.str.hom

lemma forget_map_frobeniusPowIso_succ_hom (m : ℕ)
    (h : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv) :
    (ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso (m + 1)).hom =
      (ProEtale.lowerStarCongr _ h).hom.app F.obj.carrier.X ≫
        (ProEtale.lowerStarComp _
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app
            F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom) ≫
        (ProEtale.AdicSheaf.forget _).map F.obj.str.hom := by
  simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp]
  rfl

/-- The iterated Weil structure satisfies `φ_{m+1} = φ ∘ Fr^* φ_m`, as morphisms of the
underlying sheaves. -/
lemma upperStarFactor_hom_app_comp_frobeniusPowStr_succ (m : ℕ)
    (e : (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.hom) :
    (ProEtale.upperStarFactor _ e).hom.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
          (F.frobeniusPowStr m) ≫ F.frobeniusStr =
      F.frobeniusPowStr (m + 1) := by
  have hEi : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.inv := by
    rw [pow_succ, Aut.mul_asIso, Iso.trans_inv]
  have L := ProEtale.upperStarIsoLowerStarInv_hom_app_trans (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso e hEi F.obj.carrier.X
  have n := (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.naturality
      ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom)
  symm
  rw [frobeniusPowStr, forget_map_frobeniusPowIso_succ_hom F m hEi.symm,
    reassoc_of% ProEtale.lowerStarCongr_hom_app_comp_lowerStarComp_inv_app,
    reassoc_of% L]
  simp only [frobeniusPowStr, frobeniusStr, Functor.map_comp, Category.assoc]
  erw [reassoc_of% n]
  rfl

/-- `φ_n = φ ∘ Fr^* φ_m` for `n = m + 1`. -/
lemma upperStarFactor_hom_app_comp_frobeniusPowStr_succ' (m n : ℕ) (hmn : m + 1 = n)
    (e : (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom) :
    (ProEtale.upperStarFactor _ e).hom.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
          (F.frobeniusPowStr m) ≫ F.frobeniusStr =
      F.frobeniusPowStr n := by
  subst hmn
  exact upperStarFactor_hom_app_comp_frobeniusPowStr_succ F m e

/-- The first iterate of the Weil structure is the Weil structure. -/
lemma frobeniusPowStr_one
    (p : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.hom =
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom) :
    F.frobeniusPowStr 1 =
      (ProEtale.upperStarCongr _ p).hom.app F.obj.carrier.X ≫ F.frobeniusStr := by
  have h₀ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _ := by
    rw [pow_zero]; rfl
  have h₁ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).asIso.inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv := by
    rw [pow_succ, Aut.mul_asIso, Iso.trans_inv]
  have hp : (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1 =
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius := pow_one _
  have c := ProEtale.upperStarIsoLowerStarInv_hom_app_congr (WeilCoefficients.{u} l)
    (congrArg Aut.asIso hp) F.obj.carrier.X
  rw [frobeniusPowStr, frobeniusStr, forget_map_frobeniusPowIso_one_hom F h₀ h₁,
    reassoc_of% ProEtale.lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_comp_map_lowerStarId
      (WeilCoefficients.{u} l) h₀ h₁ (congrArg (fun e ↦ e.asIso.inv) hp), reassoc_of% c]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
lemma _root_.CategoryTheory.Aut.pow_hom_comp_pow_hom {C : Type*} [Category C] {Y : C} (g : Aut Y)
    (a b : ℕ) : (g ^ b).asIso.hom ≫ (g ^ a).asIso.hom = (g ^ (a + b)).asIso.hom := by
  rw [pow_add, Aut.mul_asIso, Iso.trans_hom]

/-- The iterated Weil structures compose: `φ_{a+b} = φ_b ∘ (Frᵇ)^* φ_a`, for `b ≥ 1`. -/
lemma upperStarFactor_hom_app_comp_frobeniusPowStr_add (a b : ℕ) (hb : 1 ≤ b)
    (e : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).asIso.hom ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (a + b)).asIso.hom) :
    (ProEtale.upperStarFactor _ e).hom.app F.obj.carrier.X ≫
        (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).asIso.hom)^*[_].map
          (F.frobeniusPowStr a) ≫ F.frobeniusPowStr b =
      F.frobeniusPowStr (a + b) := by
  induction b, hb using Nat.le_induction with
  | base =>
    have p := congrArg (fun e ↦ e.asIso.hom)
      (pow_one (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius)
    have n := (ProEtale.upperStarCongr (WeilCoefficients.{u} l) p).hom.naturality
      (F.frobeniusPowStr a)
    rw [frobeniusPowStr_one F p]
    erw [reassoc_of% n]
    rw [reassoc_of% ProEtale.upperStarFactor_hom_app_comp_upperStarCongr_hom_app _ e p
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a 1 ▸ by
        rw [pow_one])]
    exact upperStarFactor_hom_app_comp_frobeniusPowStr_succ F a _
  | succ b hb ih =>
    have f := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom b 1
    rw [pow_one] at f
    have e₁ := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom
      (a + b) 1
    rw [pow_one, Nat.add_assoc] at e₁
    have e₂ := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a b
    have n := (ProEtale.upperStarFactor (WeilCoefficients.{u} l) f).hom.naturality
      (F.frobeniusPowStr a)
    rw [Functor.comp_map] at n
    have A := ProEtale.upperStarFactor_hom_app_assoc (WeilCoefficients.{u} l) e₂ e₁ f e
      F.obj.carrier.X
    rw [← upperStarFactor_hom_app_comp_frobeniusPowStr_succ F b f]
    erw [reassoc_of% n]
    rw [← reassoc_of% A, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc]
    refine Eq.trans ?_ (upperStarFactor_hom_app_comp_frobeniusPowStr_succ' F (a + b) _
      (Nat.add_assoc a b 1) e₁)
    exact congrArg (fun x ↦ _ ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map x ≫
        F.frobeniusStr) (ih e₂)

end Transport

end AlgebraicGeometry.WeilSheaf
