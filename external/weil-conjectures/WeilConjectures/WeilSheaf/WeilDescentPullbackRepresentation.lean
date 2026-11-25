/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.WeilDescentRepresentation

/-!
# The Weil fundamental representation of a sheaf pulled back from the model

Let `p : X ⟶ X₀` be the projection of the geometric fibre of a scheme over a finite field `K`,
`Fr` its geometric Galois Frobenius (`Fr ≫ p = p`), `B = (t, β)` base point data, and `M`, `M₀`
monodromies of lisse sheaves on `X` and `X₀` compatible with `p`. For a lisse sheaf `H` on `X₀`,
the Weil sheaf `p^* H` with its canonical Weil structure `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`
(`AlgebraicGeometry.WeilSheaf.geometricFiberPullback`) has Weil fundamental representation the
restriction of the monodromy representation of `π₁(X₀, t ≫ p)` on `H_{t ≫ p} = (p^* H)_t` along
`arithHom : π₁(X, t) ⋊ ℤ → π₁(X₀, t ≫ p)`
(`AlgebraicGeometry.FrobeniusBasePoint.fundamentalRep_of_iso_upperStar`): on loops this is the
compatibility of the monodromies, and on the Frobenius lift `F₀ = p_* β` it is a coherence of the
pullback pseudofunctor (`AlgebraicGeometry.ProEtale.upperStarComp_frobenius_coherence`).

To keep the kernel away from unfolding the concrete Weil sheaf `p^* H`, the statement is made
for any lisse Weil sheaf `F` with an isomorphism `e : F ≅ p^* H` of underlying sheaves carrying
its Weil structure to the canonical one.
-/

@[expose] public section

universe u

open CategoryTheory

-- The lisse monodromy (`AlgebraicGeometry.ProEtale.LisseMonodromy`) is elaborated with Mathlib's
-- `IsGrothendieckAbelian (ModuleCat _)` instance; the shortcut instance would make the kernel
-- unfold the pullback functors to compare the two.
attribute [-instance] ModuleCat.isGrothendieckAbelian_of_commRing

namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale

namespace ProEtale

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The congruence isomorphisms of pullbacks compose; the composite equality is an independent
hypothesis, so that the kernel never compares proofs of equalities of morphisms. -/
@[reassoc]
lemma upperStarCongr_hom_app_trans' {P Q : Scheme.{u}} {x y z : P ⟶ Q} (h : x = y)
    (h' : y = z) (h'' : x = z) (N : Sheaf (Scheme.ProEt.topology Q) A) :
    (upperStarCongr A h).hom.app N ≫ (upperStarCongr A h').hom.app N =
      (upperStarCongr A h'').hom.app N := by
  subst h h'
  simp [upperStarCongr]

/-- **Frobenius coherence of pullbacks.** For `φ : Z ⟶ Z` with `φ ≫ p = p` and `y : T ⟶ Z`, the
identification `((y ≫ φ) ≫ p)^* = (y ≫ p)^* ≅ y^* p^*` is the composite
`((y ≫ φ) ≫ p)^* ≅ (y ≫ φ)^* p^* ≅ y^* φ^* p^* ≅ y^* (φ ≫ p)^* = y^* p^*`. -/
lemma upperStarComp_frobenius_coherence {T Z Y : Scheme.{u}} (y : T ⟶ Z) (φ : Z ⟶ Z)
    (p : Z ⟶ Y) (hφ : φ ≫ p = p) (h : (y ≫ φ) ≫ p = y ≫ p)
    (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A h).hom.app N ≫ (upperStarComp A y p).hom.app N =
      (upperStarComp A (y ≫ φ) p).hom.app N ≫ (upperStarComp A y φ).hom.app ((p)^*[A].obj N) ≫
        (y)^*[A].map ((upperStarComp A φ p).inv.app N ≫ (upperStarCongr A hφ).hom.app N) := by
  rw [reassoc_of% upperStarComp_hom_app_comp_upperStarComp_hom_app, Functor.map_comp,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← upperStarCongr_hom_app_comp_upperStarComp_hom_app',
    upperStarCongr_hom_app_trans'_assoc _ _ _ h]

/-- The identification `G_{y ≫ f} ≅ (f^* G)_y` of stalks is `Γ` of the composition isomorphism
of pullbacks. -/
lemma upperStarStalkIso_hom_eq {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] {Z Y : Scheme.{u}}
    (f : Z ⟶ Y) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Z)
    (G : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (upperStarStalkIso l f y G).hom =
      (Sheaf.Γ _ _).map ((upperStarComp (WeilCoefficients.{u} l) y f).hom.app G) :=
  rfl

/-- **Frobenius coherence on stalks.** For `φ : Z ⟶ Z` with `φ ≫ p = p` and a geometric point
`y` of `Z`, the identification `N_{(y ≫ φ) ≫ p} = N_{y ≫ p} = (p^* N)_y` of stalks is the composite
`N_{(y ≫ φ) ≫ p} = (p^* N)_{y ≫ φ} = (φ^* p^* N)_y ≅ ((φ ≫ p)^* N)_y = (p^* N)_y`. -/
lemma stalk_frobenius_coherence {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] {Z Y : Scheme.{u}}
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Z) (φ : Z ⟶ Z) (p : Z ⟶ Y) (hφ : φ ≫ p = p)
    (h : (y ≫ φ) ≫ p = y ≫ p) (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app N) ≫
        (Sheaf.Γ _ _).map ((upperStarComp (WeilCoefficients.{u} l) y p).hom.app N) =
      (Sheaf.Γ _ _).map ((upperStarComp (WeilCoefficients.{u} l) (y ≫ φ) p).hom.app N) ≫
        (Sheaf.Γ _ _).map ((upperStarComp (WeilCoefficients.{u} l) y φ).hom.app
          ((p)^*[_].obj N)) ≫
        (Sheaf.Γ _ _).map ((y)^*[_].map
          ((upperStarComp _ φ p).inv.app N ≫ (upperStarCongr _ hφ).hom.app N)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    upperStarComp_frobenius_coherence]

/-- **Frobenius coherence on stalks, with a Weil structure.** Let `φ ≫ p = p`, `ψ : p^* N ⟶ F'`
and `s : φ^* F' ⟶ F'` such that `ψ` carries the canonical structure
`φ^* p^* N ≅ (φ ≫ p)^* N = p^* N` to `s`. Then on stalks at a geometric point `y`, the map
`N_{(y ≫ φ) ≫ p} = N_{y ≫ p} = (p^* N)_y → F'_y` is
`N_{(y ≫ φ) ≫ p} = (p^* N)_{y ≫ φ} → F'_{y ≫ φ} = (φ^* F')_y → F'_y`. -/
lemma stalk_frobenius_pullback {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] {Z Y : Scheme.{u}}
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Z) (φ : Z ⟶ Z) (p : Z ⟶ Y) (hφ : φ ≫ p = p)
    (h : (y ≫ φ) ≫ p = y ≫ p) (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
    (F' : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))
    (ψ : (p)^*[_].obj N ⟶ F') (s : (φ)^*[_].obj F' ⟶ F')
    (hs : (upperStarComp _ φ p).inv.app N ≫ (upperStarCongr _ hφ).hom.app N ≫ ψ =
      (φ)^*[_].map ψ ≫ s) :
    (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app N) ≫
        (Sheaf.Γ _ _).map ((upperStarComp (WeilCoefficients.{u} l) y p).hom.app N) ≫
        (Sheaf.Γ _ _).map ((y)^*[_].map ψ) =
      (Sheaf.Γ _ _).map ((upperStarComp (WeilCoefficients.{u} l) (y ≫ φ) p).hom.app N) ≫
        (Sheaf.Γ _ _).map (((y ≫ φ))^*[_].map ψ) ≫
        (Sheaf.Γ _ _).map ((upperStarComp (WeilCoefficients.{u} l) y φ).hom.app F') ≫
        (Sheaf.Γ _ _).map ((y)^*[_].map s) := by
  rw [← Category.assoc, stalk_frobenius_coherence y φ p hφ h N]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  rw [hs, Functor.map_comp, (upperStarComp (WeilCoefficients.{u} l) y φ).hom.naturality_assoc,
    Functor.comp_map]

/-- The stalk of a morphism of lisse sheaves is `Γ` of its pullback. -/
lemma lisseStalk_map_eq {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] {Y : Scheme.{u}}
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G G' : LisseSheaf l Y} (f : G ⟶ G') :
    (lisseStalk l y).map f = (Sheaf.Γ _ _).map ((y)^*[WeilCoefficients.{u} l].map f.hom.hom) :=
  rfl

/-- **The Frobenius of a pulled-back lisse sheaf**, for arbitrary schemes. Let `φ : Z ⟶ Z` with
`φ ≫ p = p`, monodromies `M`, `M₀` on `Z`, `Y` compatible with `p`, a path
`β : F_y ≅ F_{y ≫ φ}`, and a lisse sheaf `G` on `Z` with `s : φ^* G ⟶ G` and an isomorphism
`e : G ≅ p^* H` carrying `s` to the canonical `φ^* p^* H ≅ (φ ≫ p)^* H = p^* H`. Then under
`H_{y ≫ p} = (p^* H)_y ≅ G_y`, the transport along the push-down `p_* β` of `β` (a loop at
`y ≫ p`) is `G_y → G_{y ≫ φ} = (φ^* G)_y → G_y`. -/
theorem mono_pullbackPathIso_comp_upperStarStalkIso {l : ℕ} [Fact l.Prime] {Ω : Type u}
    [Field Ω] {Z Y : Scheme.{u}} (p : Z ⟶ Y) (φ : Z ⟶ Z) (hφ : φ ≫ p = p)
    {M : LisseMonodromy l Z Ω} {M₀ : LisseMonodromy l Y Ω}
    (hc : LisseMonodromy.IsCompatible p M₀ M) {y : Spec (.of (AlgebraicClosure Ω)) ⟶ Z}
    (β : fiber y ≅ fiber (y ≫ φ)) (h : (y ≫ φ) ≫ p = y ≫ p) (G : LisseSheaf l Z)
    (H : LisseSheaf l Y) (e : G.obj ≅ (p)^*ᵃ[l].obj H.obj) (s : G.upperStar l φ ⟶ G)
    (hs : s.hom ≫ e.hom = (φ)^*ᵃ[l].map e.hom ≫ (adicUpperStarComp l φ p).inv.app H.obj ≫
      (adicUpperStarCongr l hφ).hom.app H.obj) :
    (M₀.mono (pullbackPathIso p β ≪≫ eqToIso (congrArg fiber h))).hom.app H ≫
        (upperStarStalkIso l p y H.obj.X).hom ≫
        (lisseStalk l y).map (ObjectProperty.isoMk _ e.symm : H.upperStar l p ≅ G).hom =
      (upperStarStalkIso l p y H.obj.X).hom ≫
        (lisseStalk l y).map (ObjectProperty.isoMk _ e.symm : H.upperStar l p ≅ G).hom ≫
        (M.mono β).hom.app G ≫ (upperStarStalkIso l φ y G.obj.X).hom ≫ (lisseStalk l y).map s := by
  -- the structure `s` on underlying sheaves
  have key : (upperStarComp _ φ p).inv.app H.obj.X ≫ (upperStarCongr _ hφ).hom.app H.obj.X ≫
      e.inv.hom = (φ)^*[_].map e.inv.hom ≫ s.hom.hom := by
    have h' : (φ)^*ᵃ[l].map e.inv ≫ s.hom = (adicUpperStarComp l φ p).inv.app H.obj ≫
        (adicUpperStarCongr l hφ).hom.app H.obj ≫ e.inv := by
      rw [← cancel_mono e.hom, Category.assoc, hs, ← Functor.map_comp_assoc, e.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Category.assoc,
        e.inv_hom_id, Category.comp_id]
    have h'' := congrArg Mod.Hom.hom h'
    simp only [Mod.comp_hom', adicUpperStar_map_hom, adicUpperStarComp_inv_app_hom,
      adicUpperStarCongr_hom_app_hom] at h''
    exact h''.symm
  have h₁ : (lisseStalk l y).map (ObjectProperty.isoMk _ e.symm : H.upperStar l p ≅ G).hom ≫
      (M.mono β).hom.app G = (M.mono β).hom.app _ ≫
        (lisseStalk l (y ≫ φ)).map (ObjectProperty.isoMk _ e.symm : H.upperStar l p ≅ G).hom :=
    (M.mono β).hom.naturality _
  have h₁' {W} (g : _ ⟶ W) := (congrArg (· ≫ g) h₁)
  simp only [Category.assoc] at h₁'
  have h₂ := hc β H
  have h₂' {W} (g : _ ⟶ W) := (congrArg (· ≫ g) h₂).symm
  simp only [Category.assoc] at h₂'
  rw [h₁', h₂', M₀.mono_trans, Iso.trans_hom, NatTrans.comp_app,
    M₀.mono_eqToIso_hom_app h, Category.assoc]
  congr 1
  rw [upperStarStalkIso_hom_eq, upperStarStalkIso_hom_eq, upperStarStalkIso_hom_eq,
    lisseStalk_map_eq, lisseStalk_map_eq, lisseStalk_map_eq]
  exact stalk_frobenius_pullback y φ p hφ h H.obj.X G.obj.X e.inv.hom s.hom.hom key

end ProEtale

namespace FrobeniusBasePoint

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) (M₀ : LisseMonodromy l X K)
  (B : FrobeniusBasePoint K X)
/-- The identification `H_{t ≫ p} = (p^* H)_t ≅ F_t` of stalks induced by an isomorphism
`e : F ≅ p^* H` of `ℓ`-adic sheaves, as a morphism of stalks. -/
noncomputable def pullbackStalkHom {F : WeilSheaf K l X} (hF : F.IsLisse) {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H)
    (e : F.obj.carrier ≅ ((X ↘ Spec (.of K)).geometricFiberProj)^*ᵃ[l].obj H) :
    (lisseStalk l (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj ⟨H, hH⟩ ⟶
      (lisseStalk l B.t).obj (F.toLisse hF) :=
  (upperStarStalkIso l (X ↘ Spec (.of K)).geometricFiberProj B.t H.X).hom ≫
    (lisseStalk l B.t).map
      (ObjectProperty.isoMk _ e.symm : LisseSheaf.upperStar l
        (X ↘ Spec (.of K)).geometricFiberProj (⟨H, hH⟩ : LisseSheaf l X) ≅ F.toLisse hF).hom

/-- **The Frobenius of a pulled-back sheaf.** Under `H_{t ≫ p} ≅ F_t`, the monodromy of the
Frobenius lift `F₀ = p_* β` on `H` is the Frobenius `Φ` of the Weil fundamental representation
of `F ≅ p^* H`, whose Weil structure is the canonical one. -/
theorem mono_frobAut_comp_pullbackStalkHom
    (hc : LisseMonodromy.IsCompatible (X ↘ Spec (.of K)).geometricFiberProj M₀ M)
    {F : WeilSheaf K l X} (hF : F.IsLisse) {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H)
    (e : F.obj.carrier ≅ ((X ↘ Spec (.of K)).geometricFiberProj)^*ᵃ[l].obj H)
    (hstr : F.adicFrobStr.hom ≫ e.hom =
      ((X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map e.hom ≫
        (adicUpperStarComp l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom
          (X ↘ Spec (.of K)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (.of K)))).hom.app H) :
    (M₀.mono B.frobAut.asIso).hom.app ⟨H, hH⟩ ≫ B.pullbackStalkHom hF hH e =
      B.pullbackStalkHom hF hH e ≫ (frobStalkIso M B F hF).hom :=
  mono_pullbackPathIso_comp_upperStarStalkIso _ _ _ hc B.frobPath
    (by rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj])
    (F.toLisse hF) ⟨H, hH⟩ e (F.lisseFrobStr hF).hom hstr
/-- The identification `H_{t ≫ p} = (p^* H)_t ≅ F_t` of stalks, as a `ℚ̄_ℓ`-linear
isomorphism. -/
noncomputable def pullbackStalkEquiv {F : WeilSheaf K l X} (hF : F.IsLisse) {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H)
    (e : F.obj.carrier ≅ ((X ↘ Spec (.of K)).geometricFiberProj)^*ᵃ[l].obj H) :
    LisseMonodromy.StalkSpace (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) ⟨H, hH⟩ ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (F.toLisse hF) :=
  WeilCoefficients.linearEquivOfIso
    (upperStarStalkIso l (X ↘ Spec (.of K)).geometricFiberProj B.t H.X ≪≫
      (lisseStalk l B.t).mapIso
        (ObjectProperty.isoMk _ e.symm : LisseSheaf.upperStar l
          (X ↘ Spec (.of K)).geometricFiberProj (⟨H, hH⟩ : LisseSheaf l X) ≅ F.toLisse hF))

lemma pullbackStalkEquiv_apply {F : WeilSheaf K l X} (hF : F.IsLisse) {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H)
    (e : F.obj.carrier ≅ ((X ↘ Spec (.of K)).geometricFiberProj)^*ᵃ[l].obj H) (v) :
    B.pullbackStalkEquiv hF hH e v =
      ((WeilCoefficients.toModuleCat l).map (B.pullbackStalkHom hF hH e)).hom v :=
  rfl

/-- **The Weil fundamental representation of a sheaf pulled back from the model** (cf. Deligne,
Weil II, 1.1.7–1.1.12): if `F ≅ p^* H` with its canonical Weil structure, then under
`H_{t ≫ p} ≅ F_t` the Weil fundamental representation of `π₁(X, t) ⋊ ℤ` on `F_t` is the
monodromy representation of `π₁(X₀, t ≫ p)` on `H_{t ≫ p}` restricted along `arithHom`. -/
theorem pullbackStalkEquiv_fundamentalRep
    (hc : LisseMonodromy.IsCompatible (X ↘ Spec (.of K)).geometricFiberProj M₀ M)
    {F : WeilSheaf K l X} (hF : F.IsLisse) {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H)
    (e : F.obj.carrier ≅ ((X ↘ Spec (.of K)).geometricFiberProj)^*ᵃ[l].obj H)
    (hstr : F.adicFrobStr.hom ≫ e.hom =
      ((X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map e.hom ≫
        (adicUpperStarComp l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom
          (X ↘ Spec (.of K)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (.of K)))).hom.app H) (w : B.WeilGroup)
    (v : LisseMonodromy.StalkSpace (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) ⟨H, hH⟩) :
    B.pullbackStalkEquiv hF hH e (M₀.rep _ ⟨H, hH⟩ (B.arithHom w) v) =
      B.weilData.fundamentalRep M F hF w (B.pullbackStalkEquiv hF hH e v) := by
  refine B.weilData.intertwines_of_geometric_frobLift ((M₀.rep _ ⟨H, hH⟩).comp B.arithHom)
    (B.weilData.fundamentalRep M F hF) (B.pullbackStalkEquiv hF hH e).toLinearMap
    (fun u hu v ↦ ?_) (fun v ↦ ?_) w v
  · obtain ⟨g, rfl⟩ : u ∈ (SemidirectProduct.inl : Aut (fiber B.t) →* B.WeilGroup).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hu
    have hg : B.weilData.fundamentalRep M F hF (SemidirectProduct.inl g) =
        M.rep B.t (F.toLisse hF) g := B.weilData.fundamentalRep_geomEquiv M F hF g
    rw [MonoidHom.comp_apply, arithHom_inl, hg, geomAut_apply]
    have h₁ := (M.mono g.asIso).hom.naturality
      (ObjectProperty.isoMk _ e.symm : LisseSheaf.upperStar l
        (X ↘ Spec (.of K)).geometricFiberProj (⟨H, hH⟩ : LisseSheaf l X) ≅ F.toLisse hF).hom
    have h₂ := hc g.asIso ⟨H, hH⟩
    have key : (M₀.mono (pullbackPathIso (X ↘ Spec (.of K)).geometricFiberProj g.asIso)).hom.app
        ⟨H, hH⟩ ≫ B.pullbackStalkHom hF hH e = B.pullbackStalkHom hF hH e ≫
          (M.mono g.asIso).hom.app (F.toLisse hF) := by
      rw [pullbackStalkHom, reassoc_of% h₂]
      exact congrArg _ h₁.symm
    have := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v) key
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  · have hF₀ : B.arithHom B.weilData.frobLift = B.frobAut := by
      rw [show B.weilData.frobLift = SemidirectProduct.inr (Multiplicative.ofAdd 1) from rfl,
        arithHom_inr, toAdd_ofAdd, zpow_one]
    rw [MonoidHom.comp_apply, hF₀, WeilData.fundamentalRep_frobLift]
    have := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v)
      (B.mono_frobAut_comp_pullbackStalkHom M M₀ hc hF hH e hstr)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
/-- The underlying sheaf of the Weil sheaf `p^* H` pulled back from the model is `p^* H`. -/
noncomputable def geometricFiberPullbackCarrierIso {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    (WeilSheaf.geometricFiberPullback (k₀ := K) hH).obj.carrier ≅
      ((X ↘ Spec (.of K)).geometricFiberProj)^*ᵃ[l].obj H :=
  Iso.refl _

/-- The Weil structure of `p^* H` is the canonical one, `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`. -/
lemma adicFrobStr_geometricFiberPullback {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    (WeilSheaf.geometricFiberPullback (k₀ := K) hH).adicFrobStr.hom ≫
        (geometricFiberPullbackCarrierIso hH).hom =
      ((X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map
          (geometricFiberPullbackCarrierIso hH).hom ≫
        (adicUpperStarComp l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom
          (X ↘ Spec (.of K)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (.of K)))).hom.app H := by
  have hstr : (WeilSheaf.geometricFiberPullback (k₀ := K) hH).obj.str.hom =
      ((ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso K l X).app H).hom := by
    rw [Endofunctor.IsoAlgebra.str_hom]
    rfl
  -- stated for a variable isomorphism `α`, so that the kernel does not unfold the concrete one
  have h {P Q : AdicSheaf l (X ↘ Spec (.of K)).geometricFiber ⥤
      AdicSheaf l (X ↘ Spec (.of K)).geometricFiber} (α : P ≅ Q) :
      α.hom.app (WeilSheaf.geometricFiberPullback (k₀ := K) hH).obj.carrier =
        α.hom.app (((X ↘ Spec (.of K)).geometricFiberProj)^*ᵃ[l].obj H) := rfl
  rw [geometricFiberPullbackCarrierIso, Iso.refl_hom, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.id_comp, WeilSheaf.adicFrobStr, Iso.trans_hom,
    Iso.app_hom, hstr, h]
  simp only [ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Iso.hom_inv_id_app_assoc]

end FrobeniusBasePoint

end AlgebraicGeometry
