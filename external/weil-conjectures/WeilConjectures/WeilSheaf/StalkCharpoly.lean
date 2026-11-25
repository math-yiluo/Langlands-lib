/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.WeilSheaf.StalkFrobenius

/-!
# The characteristic polynomial of the local Frobenius
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {P P' Y Y' : Scheme.{u}}

lemma upperStarCompIso_eq {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) :
    upperStarCompIso A h =
      (upperStarComp A τ t).symm ≪≫ upperStarCongr A h ≪≫ upperStarComp A t' g :=
  rfl

lemma symm_trans_hom_app_eq {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    ((upperStarComp A τ t).symm ≪≫ upperStarCongr A h ≪≫ upperStarComp A t' g).hom.app F =
      (upperStarComp A τ t).inv.app F ≫ (upperStarCongr A h ≪≫ upperStarComp A t' g).hom.app F :=
  rfl

lemma congr_trans_hom_app_eq {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A h ≪≫ upperStarComp A t' g).hom.app F =
      (upperStarCongr A h).hom.app F ≫ (upperStarComp A t' g).hom.app F :=
  rfl

/-- The components of the isomorphism `upperStarCompIso` of a commutative square. -/
lemma upperStarCompIso_hom_app {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCompIso A h).hom.app F = (upperStarComp A τ t).inv.app F ≫
      (upperStarCongr A h).hom.app F ≫ (upperStarComp A t' g).hom.app F :=
  (congrArg (fun e ↦ e.hom.app F) (upperStarCompIso_eq A h)).trans <|
    (symm_trans_hom_app_eq A h F).trans
      (congrArg ((upperStarComp A τ t).inv.app F ≫ ·) (congr_trans_hom_app_eq A h F))

/-- The sections of the isomorphism `upperStarCongr` are an `eqToHom`. -/
lemma Γ_map_upperStarCongr_hom_app {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g')
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (Sheaf.Γ _ A).map ((upperStarCongr A h).hom.app F) = eqToHom (by rw [h]) := by
  subst h
  simp [upperStarCongr]

/-- The transport along a square `e ≫ t = t' ≫ g` whose top side is an isomorphism `e`. -/
lemma globalSectionsTransport_eq_of_iso (e : P' ≅ P) {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : e.hom ≫ t = t' ≫ g) {F : Sheaf (Scheme.ProEt.topology Y) A}
    {F' : Sheaf (Scheme.ProEt.topology Y') A} (ψ : (upperStar A g).obj F ⟶ F') :
    globalSectionsTransport A h ψ =
      (globalSectionsUpperStarIso A e).inv.app ((upperStar A t).obj F) ≫
        (Sheaf.Γ _ A).map ((upperStarCompIso A h).hom.app F ≫ (upperStar A t').map ψ) := by
  have h' :=
    globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso A e ((upperStar A t).obj F)
  replace h' : (globalSectionsToUpperStar A e.hom).app ((upperStar A t).obj F) =
      (globalSectionsUpperStarIso A e).inv.app ((upperStar A t).obj F) :=
    (Iso.comp_hom_eq_id ((globalSectionsUpperStarIso A e).app _)).1 h'
  rw [globalSectionsTransport, h']

/-- The transport along a square `e ≫ t = t' ≫ g` with `e` an isomorphism and `ψ` an
isomorphism, written as a composite of isomorphisms. -/
lemma globalSectionsTransport_eq_hom (e : P' ≅ P) {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : e.hom ≫ t = t' ≫ g) {F : Sheaf (Scheme.ProEt.topology Y) A}
    {F' : Sheaf (Scheme.ProEt.topology Y') A} (ψ : (upperStar A g).obj F ≅ F') :
    (((Sheaf.Γ _ A).mapIso ((upperStarComp A e.hom t).app F) ≪≫
        (globalSectionsUpperStarIso A e).app ((upperStar A t).obj F)).symm ≪≫
      eqToIso (congrArg (fun u ↦ (Sheaf.Γ _ A).obj ((upperStar A u).obj F)) h) ≪≫
      (Sheaf.Γ _ A).mapIso ((upperStarComp A t' g).app F ≪≫ (upperStar A t').mapIso ψ)).hom =
      globalSectionsTransport A h ψ.hom := by
  rw [globalSectionsTransport_eq_of_iso, upperStarCompIso_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, eqToIso.hom, Functor.map_comp, Category.assoc,
    Γ_map_upperStarCongr_hom_app]


section Unit

variable {X Y : Scheme.{u}}

/-- The unit of `(𝟙 X)^* ⊣ (𝟙 X)_*` followed by `(𝟙 X)_* ≅ 𝟭` is the inverse of
`(𝟙 X)^* ≅ 𝟭`. -/
lemma upperStarLowerStarAdjunction_unit_app_comp_lowerStarId_hom_app
    (G : Sheaf (Scheme.ProEt.topology X) A) :
    (upperStarLowerStarAdjunction A (𝟙 X)).unit.app G ≫
        (lowerStarId A X).hom.app ((upperStar A (𝟙 X)).obj G) =
      (upperStarId A X).inv.app G := by
  have h₁ := unit_conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction A (𝟙 X))
    (upperStarId A X).hom G
  have h₂ := congrArg (fun e ↦ e.hom.app G) (conjugateIsoEquiv_upperStarId A X)
  simp only [conjugateIsoEquiv_apply_hom] at h₂
  simp only [Functor.id_obj] at h₁
  rw [h₂] at h₁
  simp only [Adjunction.id_unit, NatTrans.id_app, Iso.symm_hom] at h₁
  have n := (lowerStarId A X).hom.naturality ((upperStarId A X).inv.app G)
  simp only [Functor.id_map] at n
  calc (upperStarLowerStarAdjunction A (𝟙 X)).unit.app G ≫
        (lowerStarId A X).hom.app ((upperStar A (𝟙 X)).obj G)
      = ((upperStarLowerStarAdjunction A (𝟙 X)).unit.app G ≫
          (lowerStar A (𝟙 X)).map ((upperStarId A X).hom.app G)) ≫
          (lowerStar A (𝟙 X)).map ((upperStarId A X).inv.app G) ≫
          (lowerStarId A X).hom.app ((upperStar A (𝟙 X)).obj G) := by
        rw [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id, Category.id_comp]
    _ = (lowerStarId A X).inv.app G ≫ (lowerStarId A X).hom.app G ≫
          (upperStarId A X).inv.app G := by
        rw [← h₁]
        rw [Category.assoc, n]
        simp only [Functor.id_obj, Category.id_comp]
    _ = (upperStarId A X).inv.app G := by simp

/-- The restriction of global sections along the identity is the inverse of `(𝟙 X)^* ≅ 𝟭`. -/
lemma globalSectionsToUpperStar_id_app (G : Sheaf (Scheme.ProEt.topology X) A) :
    (globalSectionsToUpperStar A (𝟙 X)).app G =
      (Sheaf.Γ _ A).map ((upperStarId A X).inv.app G) := by
  rw [globalSectionsToUpperStar_app, globalSectionsLowerStarIso_id, ← Functor.map_comp,
    upperStarLowerStarAdjunction_unit_app_comp_lowerStarId_hom_app]


/-- The transport along the trivial square `𝟙 ≫ t = t ≫ 𝟙` and `(𝟙)^* ≅ 𝟭` is the
identity. -/
lemma globalSectionsTransport_id {P Y : Scheme.{u}} {t : P ⟶ Y} (h : 𝟙 P ≫ t = t ≫ 𝟙 Y)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    globalSectionsTransport A h ((upperStarId A Y).hom.app F) = 𝟙 _ := by
  rw [globalSectionsTransport, globalSectionsToUpperStar_id_app, upperStarCompIso_hom_app,
    upperStarComp_id_left, upperStarComp_id_right]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc,
    Functor.comp_obj, Functor.id_obj]
  simp only [Iso.inv_hom_id_app, Functor.id_obj, CategoryTheory.Functor.map_id, Category.comp_id]
  exact CategoryTheory.Functor.map_id _ _


/-- For the identity isomorphism, `e^* ≅ (e⁻¹)_*` is the composite of `(𝟙)^* ≅ 𝟭` and
`𝟭 ≅ (𝟙)_*`. -/
lemma upperStarIsoLowerStarInv_refl_hom_app (M : Sheaf (Scheme.ProEt.topology X) A) :
    (upperStarIsoLowerStarInv A (Iso.refl X)).hom.app M ≫ (lowerStarId A X).hom.app M =
      (upperStarId A X).hom.app M := by
  apply ((upperStarLowerStarAdjunction A (𝟙 X)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h₁ := upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv A
    (Iso.refl X) M
  have h₂ : (upperStarLowerStarAdjunction A (𝟙 X)).unit.app M ≫
      (lowerStar A (𝟙 X)).map ((upperStarId A X).hom.app M) = (lowerStarId A X).inv.app M := by
    have := upperStarLowerStarAdjunction_unit_app_comp_lowerStarId_hom_app A M
    rw [← cancel_mono ((lowerStarId A X).hom.app M)]
    have n := (lowerStarId A X).hom.naturality ((upperStarId A X).hom.app M)
    simp only [Functor.id_map, Functor.id_obj] at n
    rw [Category.assoc, n, reassoc_of% this]
    simp
  erw [reassoc_of% h₁, h₂]
  rw [lowerStarUnit, ← lowerStarComp_trans_lowerStarCongr]
  erw [legacy_lowerStarComp_id_left]
  simp only [Functor.id_obj, Iso.refl_hom, Iso.refl_inv, lowerStarCongr_rfl, Iso.refl_symm,
    Iso.trans_refl, Iso.trans_assoc, Iso.trans_inv, Category.assoc, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.comp_obj, NatTrans.id_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Category.id_comp, cancelIso, Category.comp_id]
  exact Category.comp_id _


/-- For an isomorphism `e` equal to the identity, `e^* ≅ (e⁻¹)_*` is the composite of the
identifications with the identity functor. -/
lemma upperStarIsoLowerStarInv_hom_app_of_eq_refl {e : X ≅ X} (he : e = Iso.refl X)
    (h₀ : e.inv = 𝟙 X) (p : e.hom = 𝟙 X) (M : Sheaf (Scheme.ProEt.topology X) A) :
    (upperStarIsoLowerStarInv A e).hom.app M ≫ (lowerStarCongr A h₀).hom.app M ≫
        (lowerStarId A X).hom.app M =
      (upperStarCongr A p).hom.app M ≫ (upperStarId A X).hom.app M := by
  subst he
  dsimp only [Iso.refl_inv, Iso.refl_hom] at *
  simp only [lowerStarCongr, upperStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact upperStarIsoLowerStarInv_refl_hom_app A M

end Unit

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (F : WeilSheaf k₀ l X)
  (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The Frobenius of the stalk at `s` relative to `𝔽_{qᵐ}` is the transport of global sections
along the square `σᵐ ≫ s = s ≫ Frᵐ` and the iterated Weil structure. -/
lemma stalkAt_frobenius_hom_eq_globalSectionsTransport (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s).hom =
      ProEtale.globalSectionsTransport _ hs.symm (F.frobeniusPowStr m) := by
  exact ProEtale.globalSectionsTransport_eq_hom (WeilCoefficients.{u} l)
    (specGeometricFrobenius k₀ ^ m).asIso hs.symm
    ((ProEtale.upperStarIsoLowerStarInv _ _).app F.obj.carrier.X ≪≫
      (ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m))

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (F : WeilSheaf k₀ l X)
  (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)


/-- The `0`-th iterate of the Weil structure is the identification `(𝟙)^* ≅ 𝟭`. -/
lemma frobeniusPowStr_zero
    (p : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom = 𝟙 _) :
    F.frobeniusPowStr 0 = (ProEtale.upperStarCongr _ p).hom.app F.obj.carrier.X ≫
      (ProEtale.upperStarId _ _).hom.app F.obj.carrier.X := by
  have hz : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _ := by
    rw [pow_zero]; rfl
  have h₀ : (ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso 0).hom =
      (ProEtale.lowerStarCongr _ hz).hom.app F.obj.carrier.X ≫
        (ProEtale.lowerStarId _ _).hom.app F.obj.carrier.X := by
    simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Functor.map_comp,
      ProEtale.adicLowerStarId, NatIso.trans_app]
    rfl
  rw [frobeniusPowStr, h₀]
  exact ProEtale.upperStarIsoLowerStarInv_hom_app_of_eq_refl _ (by rw [pow_zero]; rfl) _ _ _


/-- The transport along the `0`-th iterate of the Weil structure is the identity. -/
lemma globalSectionsTransport_frobeniusPowStr_zero {t : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {τ : Spec (.of (AlgebraicClosure k₀)) ⟶
      Spec (.of (AlgebraicClosure k₀))} (hτ : τ = 𝟙 _)
    (h : τ ≫ t = t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom) :
    ProEtale.globalSectionsTransport _ h (F.frobeniusPowStr 0) = 𝟙 _ := by
  have p : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom = 𝟙 _ := by
    rw [pow_zero]; rfl
  rw [ProEtale.globalSectionsTransport_congr _ h p _ _ (F.frobeniusPowStr_zero p),
    ProEtale.globalSectionsTransport_congr_left _ _ hτ]
  exact ProEtale.globalSectionsTransport_id _ _ _

/-- The transports along the iterated Weil structures compose: for `b ≥ 1`, transporting along
`φ_a` and then along `φ_b` is transporting along `φ_{a+b}`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp
    {t t' t'' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {τ τ' τ'' : Spec (.of (AlgebraicClosure k₀)) ⟶
      Spec (.of (AlgebraicClosure k₀))} (a b : ℕ) (hb : 1 ≤ b)
    (ha : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom)
    (hb' : τ' ≫ t' = t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).asIso.hom)
    (hτ : τ' ≫ τ = τ'')
    (hab : τ'' ≫ t =
      t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (a + b)).asIso.hom) :
    ProEtale.globalSectionsTransport _ ha (F.frobeniusPowStr a) ≫
        ProEtale.globalSectionsTransport _ hb' (F.frobeniusPowStr b) =
      ProEtale.globalSectionsTransport _ hab (F.frobeniusPowStr (a + b)) := by
  have hg := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a b
  have h'' : (τ' ≫ τ) ≫ t = t'' ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).asIso.hom ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) := by
    rw [Category.assoc, ha, ← Category.assoc, hb', Category.assoc]
  have add := upperStarFactor_hom_app_comp_frobeniusPowStr_add F a b hb hg
  have hψ : (ProEtale.upperStarComp _ _ _).hom.app F.obj.carrier.X ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).asIso.hom)^*[_].map
        (F.frobeniusPowStr a) ≫ F.frobeniusPowStr b =
      (ProEtale.upperStarCongr _ hg).hom.app F.obj.carrier.X ≫ F.frobeniusPowStr (a + b) := by
    rw [← add]
    simp [ProEtale.upperStarFactor, ProEtale.upperStarCongr]
  rw [ProEtale.globalSectionsTransport_comp _ ha hb' h'',
    ProEtale.globalSectionsTransport_congr _ h'' hg _ _ hψ,
    ProEtale.globalSectionsTransport_congr_left _ _ hτ]

lemma globalSectionsTransport_frobeniusPowStr_congr {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {τ τ' : Spec (.of (AlgebraicClosure k₀)) ⟶
      Spec (.of (AlgebraicClosure k₀))} {n n' : ℕ} (hn : n = n') (hτ : τ = τ')
    (h : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom)
    (h' : τ' ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n').asIso.hom) :
    ProEtale.globalSectionsTransport _ h (F.frobeniusPowStr n) =
      ProEtale.globalSectionsTransport _ h' (F.frobeniusPowStr n') := by
  subst hn hτ
  rfl

instance isIso_frobeniusPowStr (m : ℕ) : IsIso (F.frobeniusPowStr m) := by
  unfold frobeniusPowStr
  exact inferInstanceAs (IsIso (((ProEtale.upperStarIsoLowerStarInv _ _).app _ ≪≫
    (ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m)).hom))

/-- The Frobenius transports at two geometric points `s` and `s'` related by a square
`g ≫ s = s' ≫ Frʲ`, with `g` commuting with `σᵐ`, are intertwined by the transport along that
square. -/
lemma globalSectionsTransport_frobeniusPowStr_comm {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {g σ : Spec (.of (AlgebraicClosure k₀)) ⟶
      Spec (.of (AlgebraicClosure k₀))} (j m : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m)
    (hg : g ≫ s = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ j).asIso.hom)
    (hs : σ ≫ s = s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (hs' : σ ≫ s' = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (hcomm : g ≫ σ = σ ≫ g) :
    ProEtale.globalSectionsTransport _ hs (F.frobeniusPowStr m) ≫
        ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j) =
      ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j) ≫
        ProEtale.globalSectionsTransport _ hs' (F.frobeniusPowStr m) := by
  have h₁ : (g ≫ σ) ≫ s = s' ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + j)).asIso.hom := by
    rw [Category.assoc, hs, ← Category.assoc, hg, Category.assoc,
      CategoryTheory.Aut.pow_hom_comp_pow_hom]
  have h₂ : (σ ≫ g) ≫ s = s' ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (j + m)).asIso.hom := by
    rw [Category.assoc, hg, ← Category.assoc, hs', Category.assoc,
      CategoryTheory.Aut.pow_hom_comp_pow_hom]
  rw [globalSectionsTransport_frobeniusPowStr_comp F m j hj hs hg rfl h₁,
    globalSectionsTransport_frobeniusPowStr_comp F j m hm hg hs' rfl h₂]
  exact globalSectionsTransport_frobeniusPowStr_congr F (Nat.add_comm m j) hcomm h₁ h₂

/-- The transport along a square `g ≫ s = s' ≫ Frʲ` with `g` an isomorphism is an
isomorphism. -/
lemma isIso_globalSectionsTransport_frobeniusPowStr {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {g : Spec (.of (AlgebraicClosure k₀)) ≅
      Spec (.of (AlgebraicClosure k₀))} (j : ℕ)
    (hg : g.hom ≫ s = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
      j).asIso.hom) :
    IsIso (ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j)) := by
  rw [ProEtale.globalSectionsTransport_eq_of_iso _ g hg]
  infer_instance

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private lemma linearEquivOfIso_toLinearMap {M N : WeilCoefficients.{u} l} (e : M ≅ N) :
    (WeilCoefficients.linearEquivOfIso e).toLinearMap =
      ((WeilCoefficients.toModuleCat l).map e.hom).hom :=
  rfl

/-- The Frobenius of the stalk at `s` relative to `𝔽_{qᵐ}`, as a linear map, is the transport of
global sections along the iterated Weil structure. -/
lemma frobeniusEnd_stalkAt (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    (F.stalkAt s m hs).frobeniusEnd = ((WeilCoefficients.toModuleCat l).map
      (ProEtale.globalSectionsTransport _ hs.symm (F.frobeniusPowStr m))).hom := by
  have e₁ : (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) := rfl
  rw [FrobeniusModule.frobeniusEnd, e₁, linearEquivOfIso_toLinearMap,
    stalkAt_frobenius_hom_eq_globalSectionsTransport F s m hs]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private lemma toModuleCat_map_comp_hom {M N P : WeilCoefficients.{u} l} (f : M ⟶ N)
    (g : N ⟶ P) :
    ((WeilCoefficients.toModuleCat l).map (f ≫ g)).hom =
      ((WeilCoefficients.toModuleCat l).map g).hom ∘ₗ
        ((WeilCoefficients.toModuleCat l).map f).hom := by
  rw [Functor.map_comp]
  rfl

/-- A geometric point fixed by `Frᵐ` up to `σᵐ` is fixed by `Frᵏᵐ` up to `σᵏᵐ`. -/
lemma comp_geometricGaloisFrobenius_pow_mul {m : ℕ}
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (k : ℕ) :
    s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (k * m)).asIso.hom =
      (specGeometricFrobenius k₀ ^ (k * m)).asIso.hom ≫ s := by
  induction k with
  | zero => simp only [zero_mul, pow_zero]; rfl
  | succ k ih =>
    rw [Nat.succ_mul, ← CategoryTheory.Aut.pow_hom_comp_pow_hom, ← Category.assoc, hs,
      Category.assoc, ih, ← Category.assoc, CategoryTheory.Aut.pow_hom_comp_pow_hom]

/-- The Frobenius relative to `𝔽_{qᵏᵐ}` is the `k`-th power of the Frobenius relative to
`𝔽_{qᵐ}`. -/
lemma frobeniusEnd_stalkAt_mul {m : ℕ} (hm : 1 ≤ m)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (k : ℕ) :
    (F.stalkAt s (k * m) (comp_geometricGaloisFrobenius_pow_mul s hs k)).frobeniusEnd =
      (F.stalkAt s m hs).frobeniusEnd ^ k := by
  induction k with
  | zero =>
    have h₀ : (specGeometricFrobenius k₀ ^ (0 * m)).asIso.hom ≫ s =
        s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom := by
      rw [zero_mul, pow_zero, pow_zero]; rfl
    rw [frobeniusEnd_stalkAt, pow_zero, globalSectionsTransport_frobeniusPowStr_congr F
      (zero_mul m) rfl _ h₀, globalSectionsTransport_frobeniusPowStr_zero F
        (by rw [zero_mul, pow_zero]; rfl)]
    rfl
  | succ k ih =>
    have h : (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ (specGeometricFrobenius k₀ ^ (k *
      m)).asIso.hom ≫
        s = s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (k * m +
          m)).asIso.hom := by
      have hk := comp_geometricGaloisFrobenius_pow_mul s hs (k + 1)
      rw [add_one_mul] at hk
      rw [← Category.assoc, CategoryTheory.Aut.pow_hom_comp_pow_hom]
      exact hk.symm
    have h' : ((specGeometricFrobenius k₀ ^ m).asIso.hom ≫ (specGeometricFrobenius k₀ ^ (k *
      m)).asIso.hom) ≫
        s = s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (k * m +
          m)).asIso.hom := by
      rw [Category.assoc]; exact h
    rw [pow_succ', ← ih, frobeniusEnd_stalkAt, frobeniusEnd_stalkAt, frobeniusEnd_stalkAt]
    have hτ : (specGeometricFrobenius k₀ ^ ((k + 1) * m)).asIso.hom =
        (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ (specGeometricFrobenius k₀ ^ (k *
          m)).asIso.hom := by
      rw [CategoryTheory.Aut.pow_hom_comp_pow_hom, add_one_mul]
    have c₁ := globalSectionsTransport_frobeniusPowStr_congr F (add_one_mul k m) hτ
      (comp_geometricGaloisFrobenius_pow_mul s hs (k + 1)).symm h'
    have c₂ := globalSectionsTransport_frobeniusPowStr_comp F (k * m) m hm
      (comp_geometricGaloisFrobenius_pow_mul s hs k).symm hs.symm rfl h'
    exact (congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom)
      (c₁.trans c₂.symm)).trans (toModuleCat_map_comp_hom _ _)

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (F : WeilSheaf k₀ l X)

/-- The Frobenius of the stalk relative to `𝔽_{q⁰}` is the identity. -/
lemma frobeniusEnd_stalkAt_zero
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom =
      (specGeometricFrobenius k₀ ^ 0).asIso.hom ≫ s) :
    (F.stalkAt s 0 hs).frobeniusEnd = LinearMap.id := by
  rw [frobeniusEnd_stalkAt, globalSectionsTransport_frobeniusPowStr_zero F
    (by rw [pow_zero]; rfl), CategoryTheory.Functor.map_id]
  rfl

/-- The transport along a square `g ≫ s = s' ≫ Frʲ` intertwines the Frobenius of the stalks
at `s` and at `s'` relative to `𝔽_{qᵐ}`. -/
lemma toModuleCat_map_globalSectionsTransport_comp_frobeniusEnd_stalkAt
    {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {g : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))} {j m : ℕ}
    (hj : 1 ≤ j) (hm : 1 ≤ m)
    (hg : g ≫ s = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ j).asIso.hom)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hs' : s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s')
    (hcomm : g ≫ (specGeometricFrobenius k₀ ^ m).asIso.hom = (specGeometricFrobenius k₀ ^
      m).asIso.hom ≫ g) :
    ((WeilCoefficients.toModuleCat l).map
        (ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j))).hom ∘ₗ
        (F.stalkAt s m hs).frobeniusEnd =
      (F.stalkAt s' m hs').frobeniusEnd ∘ₗ ((WeilCoefficients.toModuleCat l).map
        (ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j))).hom := by
  rw [frobeniusEnd_stalkAt, frobeniusEnd_stalkAt, ← toModuleCat_map_comp_hom,
    ← toModuleCat_map_comp_hom,
    globalSectionsTransport_frobeniusPowStr_comm F j m hj hm hg hs.symm hs'.symm hcomm]

/-- The stalks, with their Frobenius relative to `𝔽_{qᵐ}`, at two geometric points over the same
point with finite residue field are isomorphic: the points are related by a square
`g ≫ s = s' ≫ Frʲ`
(`AlgebraicGeometry.Scheme.Hom.exists_iso_comp_eq_comp_geometricGaloisFrobenius_pow`), and the
transport along it intertwines the two Frobenius. -/
lemma nonempty_equiv_stalkAt
    (s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hss' : (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      (s' ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)))
    (hx : (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) ∈ X.finitePoints) (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hs' : s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s') :
    Nonempty ((F.stalkAt s m hs).Equiv (F.stalkAt s' m hs')) := by
  obtain ⟨g, j, hj, hg, hcomm⟩ :=
    (X ↘ Spec (CommRingCat.of k₀)).exists_iso_comp_eq_comp_geometricGaloisFrobenius_pow s s'
      hss' hx
  have := F.isIso_globalSectionsTransport_frobeniusPowStr j hg
  let T := ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j)
  let eL := WeilCoefficients.linearEquivOfIso (asIso T)
  refine ⟨.ofComp eL ?_⟩
  rw [linearEquivOfIso_toLinearMap, asIso_hom]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [frobeniusEnd_stalkAt_zero, frobeniusEnd_stalkAt_zero]
    rfl
  · exact F.toModuleCat_map_globalSectionsTransport_comp_frobeniusEnd_stalkAt hj hm hg hs hs'
      (hcomm m)

/-- The characteristic polynomial of the Frobenius on the stalk does not depend on the
geometric point: for geometric points `s` and `s'` over the same point of `X` with finite
residue field, fixed up to reparametrisation by `Frᵐ` and by `Fr^{m'}` with `m ∣ m'`, the
Frobenius of `F_{s'}` relative to `𝔽_{q^{m'}}` has the characteristic polynomial of the
`m' / m`-th power of the Frobenius of `F_s` relative to `𝔽_{qᵐ}`. -/
theorem charpoly_frobeniusEnd_stalkAt_of_dvd
    (s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hss' : (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      (s' ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)))
    (hx : (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) ∈ X.finitePoints)
    {m m' : ℕ} (hmm' : m ∣ m')
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hs' : s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m').asIso.hom =
      (specGeometricFrobenius k₀ ^ m').asIso.hom ≫ s') :
    (F.stalkAt s' m' hs').frobeniusEnd.charpoly =
      ((F.stalkAt s m hs).frobeniusEnd ^ (m' / m)).charpoly := by
  have congr_index {t} {n n' : ℕ} (h : n = n')
      (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom =
        (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ t)
      (ht' : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n').asIso.hom =
        (specGeometricFrobenius k₀ ^ n').asIso.hom ≫ t) :
      (F.stalkAt t n ht).frobeniusEnd.charpoly = (F.stalkAt t n' ht').frobeniusEnd.charpoly := by
    subst h
    rfl
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · have h₀ : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom =
        (specGeometricFrobenius k₀ ^ 0).asIso.hom ≫ s := by
      rw [pow_zero, pow_zero]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    obtain ⟨e⟩ := F.nonempty_equiv_stalkAt s s' hss' hx 0 h₀ hs'
    rw [e.charpoly_frobeniusEnd, frobeniusEnd_stalkAt_zero, Nat.zero_div, pow_zero]
    rfl
  · have hm : 1 ≤ m := Nat.pos_of_dvd_of_pos hmm' hm'
    obtain ⟨c, rfl⟩ := hmm'
    rw [Nat.mul_div_cancel_left c hm, ← frobeniusEnd_stalkAt_mul F s hm hs c]
    have hs'' := comp_geometricGaloisFrobenius_pow_mul s hs c
    rw [congr_index (Nat.mul_comm m c) hs'
      ((Nat.mul_comm c m).symm ▸ hs' :)]
    obtain ⟨e⟩ := F.nonempty_equiv_stalkAt s s' hss' hx (c * m) hs'' _
    exact e.charpoly_frobeniusEnd

/-- The trace function at an `𝔽_{qⁿ}`-rational point `y` over a closed point `x` is the trace
of the `n / e_x`-th power of the local geometric Frobenius `Fₓ`, `e_x = [κ(x) : k₀]`: the
geometric points over `x` and over `y` lie over the same point, `e_x ∣ n`, and the
characteristic polynomial of the Frobenius does not depend on the geometric point
(`AlgebraicGeometry.WeilSheaf.charpoly_frobeniusEnd_stalkAt_of_dvd`). -/
theorem traceFunction_eq_trace_frobeniusEnd_stalk_pow (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n))
    (x : X.finitePoints) (hx : y.1.base (IsLocalRing.closedPoint _) = x.1) :
    F.traceFunction n y = LinearMap.trace (PadicAlgCl l) _
      ((F.stalk x).frobeniusEnd ^ (n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1)) := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have hx₁ :=
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base x
  have hdvd := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_dvd_of_fieldPoints n y
  rw [hx] at hdvd
  have h := F.charpoly_frobeniusEnd_stalkAt_of_dvd _ _
    (hx₁.trans ((((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint_comp_geometricFiberProj_base
      IsAlgClosed.lift y.1 y.2).trans hx).symm)) (hx₁ ▸ x.2) hdvd
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) x)
    (Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) n IsAlgClosed.lift y)
  rw [traceFunction, stalk, LinearMap.trace_eq_neg_charpoly_nextCoeff,
    LinearMap.trace_eq_neg_charpoly_nextCoeff, h]

end AlgebraicGeometry.WeilSheaf
