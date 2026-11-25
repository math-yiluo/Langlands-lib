/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFrobenius

/-!
# Restriction of global sections to a stalk and iterates of the Frobenius

Let `F` be a Weil sheaf on a `k₀`-scheme `X` and `s` a geometric point of `X̄` with
`s ≫ Frᵐ = σᵐ ≫ s`, for instance the geometric point over a closed point of degree `m`. The
restriction `Γ(X̄, F) ⟶ F_s` intertwines the `m`-th power of the Frobenius of the global sections
with the Frobenius of `F_s` relative to `𝔽_{qᵐ}`
(`AlgebraicGeometry.WeilSheaf.globalSectionsToStalkObj_frobenius_pow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The global sections of `(eᵐ⁺¹)⁻¹_* N` and of `(e⁻¹)_* (eᵐ)⁻¹_* N` are identified compatibly
with the identification `(eᵐ⁺¹)⁻¹_* N ≅ (e⁻¹)_* (eᵐ)⁻¹_* N` defining the iterates of a Weil
structure. -/
@[reassoc]
lemma globalSectionsLowerStarIso_inv_comp_pow_succ {Y : Scheme.{u}} (e : Aut Y)
    (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) (m : ℕ)
    (h : (e ^ (m + 1)).asIso.inv = (e ^ m).asIso.inv ≫ e.asIso.inv) :
    (ProEtale.globalSectionsLowerStarIso _ (e ^ (m + 1)).asIso.inv).inv.app N ≫
      (Sheaf.Γ _ _).map ((ProEtale.lowerStarCongr _ h).hom.app N) ≫
        (Sheaf.Γ _ _).map ((ProEtale.lowerStarComp _ (e ^ m).asIso.inv e.asIso.inv).inv.app N) =
    (ProEtale.globalSectionsLowerStarIso _ (e ^ m).asIso.inv).inv.app N ≫
      (ProEtale.globalSectionsLowerStarIso _ e.asIso.inv).inv.app
        (((e ^ m).asIso.inv)_*[_].obj N) := by
  have e₁ := ProEtale.globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h N
  have e₂ := ProEtale.globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) (e ^ m).asIso.inv
    e.asIso.inv N
  rw [← cancel_mono ((ProEtale.globalSectionsLowerStarIso _ e.asIso.inv).hom.app _),
    ← cancel_mono ((ProEtale.globalSectionsLowerStarIso _ (e ^ m).asIso.inv).hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← e₂, ← Functor.map_comp_assoc _ ((ProEtale.lowerStarComp _ (e ^ m).asIso.inv
    e.asIso.inv).inv.app N),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, e₁, Iso.inv_hom_id_app]
  simp

variable (F : WeilSheaf k₀ l X)

/-- The `m`-th iterate of the Frobenius of the global sections of a Weil sheaf, through the
iterated Weil structure `φ_m : (Frᵐ)^* F ≅ F`:
`Γ(X̄, F) ≅ Γ(X̄, (Fr⁻ᵐ)_* F) --Γ(φ_m)--> Γ(X̄, F)`. -/
noncomputable def globalSectionsFrobeniusPow (m : ℕ) :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier.X ⟶
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier.X :=
  (ProEtale.globalSectionsLowerStarIso _
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv).inv.app
        F.obj.carrier.X ≫
    (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom)

/-- The `(m + 1)`-st iterate of the Frobenius of the global sections is the `m`-th iterate
followed by the Frobenius. -/
lemma globalSectionsFrobeniusPow_succ (m : ℕ) :
    F.globalSectionsFrobeniusPow (m + 1) =
      F.globalSectionsFrobeniusPow m ≫
        (ProEtale.globalSectionsLowerStarIso _
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app
            F.obj.carrier.X ≫
        (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map F.obj.str.hom) := by
  have h : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv := by
    rw [pow_succ, Aut.mul_asIso, Iso.trans_inv]
  have n := (ProEtale.globalSectionsLowerStarIso (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.naturality
      ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom)
  rw [Functor.comp_map] at n
  rw [globalSectionsFrobeniusPow, globalSectionsFrobeniusPow,
    forget_map_frobeniusPowIso_succ_hom F m h]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% globalSectionsLowerStarIso_inv_comp_pow_succ]
  erw [← reassoc_of% n]
  rfl
/-- The first iterate of the Frobenius of the global sections is the Frobenius. -/
lemma globalSectionsFrobeniusPow_one :
    F.globalSectionsFrobeniusPow 1 =
      (ProEtale.globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app F.obj.carrier.X ≫
        (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map F.obj.str.hom) :=
  F.globalSectionsLowerStarIso_inv_comp_frobeniusPowIso_one

/-- The `m`-th iterate of the Frobenius of the global sections, `m ≥ 1`, is the `m`-th power of
the Frobenius of the Frobenius module `Γ(X̄, F)`. -/
lemma toModuleCat_map_globalSectionsFrobeniusPow_apply
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (m : ℕ) (hm : 1 ≤ m)
    (a : F.globalSections.carrier) :
    ((WeilCoefficients.toModuleCat l).map (F.globalSectionsFrobeniusPow m)).hom a =
      (F.globalSections.frobeniusEnd ^ m) a := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [pow_one, globalSectionsFrobeniusPow_one]
    rfl
  | succ m hm ih =>
    rw [globalSectionsFrobeniusPow_succ, Functor.map_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, ih, pow_succ', Module.End.mul_apply]
    rfl

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The restriction of global sections to the stalk at a geometric point `s` with
`s ≫ Frᵐ = σᵐ ≫ s` intertwines the `m`-th iterate of the Frobenius of the global sections with
the Frobenius of `F_s` relative to `𝔽_{qᵐ}`, as morphisms. -/
lemma globalSectionsToStalkObj_comp_stalkAt_iso_pow (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    F.globalSectionsToStalkObj s ≫ ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫
        eqToIso (congrArg F.stalkObj hs.symm) ≪≫ F.stalkObjFrobeniusPowIso m s).hom =
      F.globalSectionsFrobeniusPow m ≫ F.globalSectionsToStalkObj s := by
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rw [reassoc_of% globalSectionsToStalkObj_comp_stalkObjSpecFrobeniusPowIso_inv,
    reassoc_of% (globalSectionsToStalkObj_comp_eqToHom F hs.symm),
    globalSectionsToStalkObj_comp_stalkObjFrobeniusPowIso_hom, globalSectionsFrobeniusPow,
    Category.assoc]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The image of an element under a composite in `WeilCoefficients`, as modules. -/
lemma toModuleCat_map_comp_apply {M N P : WeilCoefficients.{u} l} (f : M ⟶ N)
    (g : N ⟶ P) (x : (WeilCoefficients.toModuleCat l).obj M) :
    ((WeilCoefficients.toModuleCat l).map (f ≫ g)).hom x =
      ((WeilCoefficients.toModuleCat l).map g).hom
        (((WeilCoefficients.toModuleCat l).map f).hom x) := by
  rw [Functor.map_comp]
  rfl

/-- The Frobenius of the stalk `F_s` at a geometric point with `s ≫ Frᵐ = σᵐ ≫ s`. -/
lemma stalkAt_frobenius_eq (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) :=
  rfl

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The linear equivalence induced by an isomorphism in `WeilCoefficients`, applied to an
element. -/
lemma linearEquivOfIso_apply {M N : WeilCoefficients.{u} l} (e : M ≅ N)
    (x : (WeilCoefficients.toModuleCat l).obj M) :
    WeilCoefficients.linearEquivOfIso e x = ((WeilCoefficients.toModuleCat l).map e.hom).hom x :=
  rfl

/-- The Frobenius of the stalk `F_s` at a geometric point with `s ≫ Frᵐ = σᵐ ≫ s`, applied to an
element. -/
lemma stalkAt_frobeniusEnd_apply (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (y : (F.stalkAt s m hs).carrier) :
    (F.stalkAt s m hs).frobeniusEnd y =
      ((WeilCoefficients.toModuleCat l).map ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫
        eqToIso (congrArg F.stalkObj hs.symm) ≪≫ F.stalkObjFrobeniusPowIso m s).hom).hom y :=
  (LinearEquiv.congr_fun (F.stalkAt_frobenius_eq s m hs) y).trans (linearEquivOfIso_apply _ y)

/-- The restriction of global sections to the stalk at a geometric point `s` with
`s ≫ Frᵐ = σᵐ ≫ s`, `m ≥ 1`, for instance the geometric point over a closed point of degree
`m`, intertwines the `m`-th power of the Frobenius of `Γ(X̄, F)` with the Frobenius of `F_s`
relative to `𝔽_{qᵐ}`. -/
theorem globalSectionsToStalkObj_frobenius_pow [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (m : ℕ) (hm : 1 ≤ m)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (a : F.globalSections.carrier) :
    ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom
        ((F.globalSections.frobeniusEnd ^ m) a) =
      (F.stalkAt s m hs).frobeniusEnd
        (((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a) := by
  -- the intermediate equations are stated with explicit arguments to keep the kernel fast
  let es := (F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫
    eqToIso (congrArg F.stalkObj hs.symm) ≪≫ F.stalkObjFrobeniusPowIso m s
  have h₀ := toModuleCat_map_comp_apply (F.globalSectionsFrobeniusPow m)
    (F.globalSectionsToStalkObj s) a
  have h₁ := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom a)
    (globalSectionsToStalkObj_comp_stalkAt_iso_pow F s m hs)
  have h₂ := toModuleCat_map_comp_apply (F.globalSectionsToStalkObj s) es.hom a
  have e₁ := toModuleCat_map_globalSectionsFrobeniusPow_apply F m hm a
  have e₂ := stalkAt_frobeniusEnd_apply F s m hs
    (((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a)
  exact (congrArg ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom
    e₁.symm).trans (h₀.symm.trans (h₁.symm.trans (h₂.trans e₂.symm)))

/-- The restriction `Γ(X̄, F) ⟶ F_s` of global sections to the stalk at a geometric point `s`
with `s ≫ Frᵐ = σᵐ ≫ s`, as a linear map of the underlying spaces of the Frobenius modules. -/
noncomputable def globalSectionsToStalkAt [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    F.globalSections.carrier →ₗ[PadicAlgCl l] (F.stalkAt s m hs).carrier :=
  ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom

/-- The restriction of global sections to a stalk, applied to an element. -/
lemma globalSectionsToStalkAt_apply [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (a : F.globalSections.carrier) :
    F.globalSectionsToStalkAt s m hs a =
      ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a :=
  rfl

/-- The restriction of global sections to the stalk at a geometric point `s` with
`s ≫ Frᵐ = σᵐ ≫ s`, `m ≥ 1`, intertwines the `m`-th power of the Frobenius of `Γ(X̄, F)` with
the Frobenius of `F_s` relative to `𝔽_{qᵐ}`, as linear maps. -/
theorem globalSectionsToStalkAt_comp_frobeniusEnd_pow
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (m : ℕ) (hm : 1 ≤ m)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    F.globalSectionsToStalkAt s m hs ∘ₗ F.globalSections.frobeniusEnd ^ m =
      (F.stalkAt s m hs).frobeniusEnd ∘ₗ F.globalSectionsToStalkAt s m hs :=
  -- the intermediate equations are stated with explicit arguments to keep the kernel fast
  LinearMap.ext fun a ↦ (LinearMap.comp_apply _ _ a).trans
    (((F.globalSectionsToStalkAt_apply s m hs _).trans
      ((F.globalSectionsToStalkObj_frobenius_pow s m hm hs a).trans
        (congrArg (F.stalkAt s m hs).frobeniusEnd
          (F.globalSectionsToStalkAt_apply s m hs a)).symm)).trans
      (LinearMap.comp_apply _ _ a).symm)

end AlgebraicGeometry.WeilSheaf
