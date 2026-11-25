/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy
public import WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit
public import WeilConjectures.WeilSheaf.StalkConstantSheaf

/-!
# The monodromy of lisse sheaves from universal covers

Let `Y` be a connected scheme with universal profinite étale covers `p_y : Ỹ_y ⟶ Y` at the
geometric points `y : Spec Ω̄ ⟶ Y` (`AlgebraicGeometry.Scheme.UniversalCovers`), and assume that
every lisse `ℓ`-adic sheaf `G` becomes free of finite rank on every `Ỹ_y`. Then the stalk
`G_y = Γ(Spec Ω̄, y^* G)` is identified with `Γ(Ỹ_y, p_y^* G)` by restriction along the base
point `ỹ` of `Ỹ_y` (the sections of a free sheaf on the connected `Ỹ_y` are constant), and a
path `τ : F_y ≅ F_z` transports `Γ(Ỹ_y, p_y^* G) ≅ Γ(Ỹ_z, p_z^* G)` along the isomorphism
`Ỹ_y ≅ Ỹ_z` over `Y` induced by `τ`. This is the monodromy of lisse sheaves
(`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy`).

All maps involved are restrictions of sections along morphisms of schemes over `Y`
(`AlgebraicGeometry.ProEtale.resOver`), which compose
(`AlgebraicGeometry.ProEtale.resOver_comp`) and are monoidal, so the compatibilities of a
`AlgebraicGeometry.ProEtale.LisseMonodromy` follow from those of the universal covers.

## Main definitions

- `AlgebraicGeometry.ProEtale.resOver`: the restriction `Γ(T, t^* F) ⟶ Γ(S, s^* F)` along a
  morphism `h : S ⟶ T` over `Z`.
- `AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy`: the monodromy of lisse sheaves
  obtained from universal covers on which lisse sheaves are constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

section Transport

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- A composite of transports along squares, computed by a given square and morphism. -/
lemma globalSectionsTransport_comp_eq {P P' P'' Y Y' Y'' : Scheme.{u}} {τ : P' ⟶ P}
    {τ' : P'' ⟶ P'} {τ'' : P'' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {t'' : P'' ⟶ Y''} {g : Y' ⟶ Y}
    {g' : Y'' ⟶ Y'} {g'' : Y'' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) (h' : τ' ≫ t' = t'' ≫ g') (h'' : τ'' ≫ t = t'' ≫ g'')
    (hτ : τ' ≫ τ = τ'') (hg : g' ≫ g = g'')
    {F : Sheaf (Scheme.ProEt.topology Y) A} {F' : Sheaf (Scheme.ProEt.topology Y') A}
    {F'' : Sheaf (Scheme.ProEt.topology Y'') A} (ψ : (g)^*[A].obj F ⟶ F')
    (ψ' : (g')^*[A].obj F' ⟶ F'') (ψ'' : (g'')^*[A].obj F ⟶ F'')
    (hψ : (upperStarComp A g' g).hom.app F ≫ (g')^*[A].map ψ ≫ ψ' =
      (upperStarCongr A hg).hom.app F ≫ ψ'') :
    globalSectionsTransport A h ψ ≫ globalSectionsTransport A h' ψ' =
      globalSectionsTransport A h'' ψ'' := by
  subst hτ hg
  rw [globalSectionsTransport_comp A h h' h'', hψ]
  simp [upperStarCongr]

/-- The composition isomorphism `(𝟙 ≫ g)^* ≅ g^* ⋙ (𝟙)^*` followed by `(𝟙)^* ≅ 𝟭`. -/
lemma upperStarComp_id_left_hom_app {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarComp A (𝟙 Y') g).hom.app F ≫ (upperStarId A Y').hom.app ((g)^*[A].obj F) =
      (upperStarCongr A (Category.id_comp g)).hom.app F := by
  rw [upperStarComp_id_left]
  simp

/-- The composition isomorphism `(g ≫ 𝟙)^* ≅ (𝟙)^* ⋙ g^*` followed by `(𝟙)^* ≅ 𝟭`. -/
lemma upperStarComp_id_right_hom_app {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarComp A g (𝟙 Y)).hom.app F ≫ (g)^*[A].map ((upperStarId A Y).hom.app F) =
      (upperStarCongr A (Category.comp_id g)).hom.app F := by
  rw [upperStarComp_id_right]
  simp [← Functor.map_comp]

/-- The restriction of sections `Γ(T, t^* F) ⟶ Γ(S, s^* F)` along a morphism `h : S ⟶ T` of
schemes over `Z` (`h ≫ t = s`): the restriction along `h` followed by
`h^* t^* F ≅ (h ≫ t)^* F = s^* F`. -/
noncomputable irreducible_def resOver {S T Z : Scheme.{u}} {s : S ⟶ Z} {t : T ⟶ Z} (h : S ⟶ T)
    (e : h ≫ t = s) : (t)^*[A] ⋙ Sheaf.Γ _ A ⟶ (s)^*[A] ⋙ Sheaf.Γ _ A :=
  Functor.whiskerLeft (t)^*[A] (globalSectionsToUpperStar A h) ≫
    Functor.whiskerRight (upperStarFactor A e).inv (Sheaf.Γ _ A)

variable {A} in
/-- The components of the restriction over `Z`. -/
lemma resOver_app {S T Z : Scheme.{u}} {s : S ⟶ Z} {t : T ⟶ Z} (h : S ⟶ T) (e : h ≫ t = s)
    (F : Sheaf (Scheme.ProEt.topology Z) A) :
    (resOver A h e).app F = (globalSectionsToUpperStar A h).app ((t)^*[A].obj F) ≫
      (Sheaf.Γ _ A).map ((upperStarFactor A e).inv.app F) := by
  rw [resOver_def]
  rfl

/-- Composites of the isomorphisms `g^* ≅ g'^*` for equalities `g = g'`. -/
lemma upperStarCongr_hom_app_comp_hom_app {P Q : Scheme.{u}} {g g' g'' : P ⟶ Q} (p : g = g')
    (q : g' = g'') (r : g = g'') (F : Sheaf (Scheme.ProEt.topology Q) A) :
    (upperStarCongr A p).hom.app F ≫ (upperStarCongr A q).hom.app F =
      (upperStarCongr A r).hom.app F := by
  subst p q
  simp [upperStarCongr]

variable {A} in
/-- The inverse of the factorisation isomorphism `s^* ≅ t^* ⋙ h^*` of `h ≫ t = s`. -/
lemma upperStarFactor_inv_app {S T Z : Scheme.{u}} {s : S ⟶ Z} {t : T ⟶ Z} (h : S ⟶ T)
    (e : h ≫ t = s) (F : Sheaf (Scheme.ProEt.topology Z) A) :
    (upperStarFactor A e).inv.app F =
      (upperStarComp A h t).inv.app F ≫ (upperStarCongr A e).hom.app F := by
  subst e
  rw [upperStarFactor_rfl]
  simp only [upperStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

/-- The restriction over `Z` is the transport along the square `h ≫ t = s ≫ 𝟙` and
`(𝟙)^* ≅ 𝟭`. -/
lemma resOver_app_eq_transport {S T Z : Scheme.{u}} {s : S ⟶ Z} {t : T ⟶ Z} (h : S ⟶ T)
    (e : h ≫ t = s) (F : Sheaf (Scheme.ProEt.topology Z) A) :
    (resOver A h e).app F = globalSectionsTransport A (e.trans (Category.comp_id s).symm)
      ((upperStarId A Z).hom.app F) := by
  have key : (upperStarFactor A e).inv.app F = (upperStarCompIso A
      (e.trans (Category.comp_id s).symm)).hom.app F ≫
        (s)^*[A].map ((upperStarId A Z).hom.app F) := by
    have hc : (upperStarCongr A (e.trans (Category.comp_id s).symm)).hom.app F ≫
        (upperStarCongr A (Category.comp_id s)).hom.app F = (upperStarCongr A e).hom.app F :=
      upperStarCongr_hom_app_comp_hom_app A _ _ _ F
    rw [upperStarCompIso_hom_app, Category.assoc, Category.assoc, upperStarComp_id_right_hom_app,
      upperStarFactor_inv_app, hc]
  rw [resOver_app, globalSectionsTransport, key]

/-- Restrictions over `Z` compose. -/
lemma resOver_comp {S₁ S₂ T Z : Scheme.{u}} {s₁ : S₁ ⟶ Z} {s₂ : S₂ ⟶ Z} {t : T ⟶ Z}
    (h₁ : S₁ ⟶ S₂) (h₂ : S₂ ⟶ T) (e₁ : h₁ ≫ s₂ = s₁) (e₂ : h₂ ≫ t = s₂)
    (e : (h₁ ≫ h₂) ≫ t = s₁) (F : Sheaf (Scheme.ProEt.topology Z) A) :
    (resOver A h₂ e₂).app F ≫ (resOver A h₁ e₁).app F = (resOver A (h₁ ≫ h₂) e).app F := by
  rw [resOver_app_eq_transport, resOver_app_eq_transport, resOver_app_eq_transport]
  refine globalSectionsTransport_comp_eq A _ _ _ rfl (Category.comp_id _) _ _ _ ?_
  have n : (𝟙 Z)^*[A].map ((upperStarId A Z).hom.app F) ≫ (upperStarId A Z).hom.app F =
      (upperStarId A Z).hom.app ((𝟙 Z)^*[A].obj F) ≫ (upperStarId A Z).hom.app F :=
    (upperStarId A Z).hom.naturality ((upperStarId A Z).hom.app F)
  rw [n, reassoc_of% (upperStarComp_id_left_hom_app A (𝟙 Z) F)]

/-- The restriction along the identity is the identity. -/
lemma resOver_id {T Z : Scheme.{u}} (t : T ⟶ Z) (e : 𝟙 T ≫ t = t)
    (F : Sheaf (Scheme.ProEt.topology Z) A) :
    (resOver A (𝟙 T) e).app F = 𝟙 _ := by
  rw [resOver_app_eq_transport]
  exact globalSectionsTransport_id A _ F

/-- Restrictions along equal morphisms agree. -/
lemma resOver_congr {S T Z : Scheme.{u}} {s : S ⟶ Z} {t : T ⟶ Z} {h h' : S ⟶ T} (p : h = h')
    (e : h ≫ t = s) (e' : h' ≫ t = s) : resOver A h e = resOver A h' e' := by
  subst p
  rfl

/-- The restriction of global sections along `t`, followed by the restriction along `h` over `Z`,
is the restriction along `s = h ≫ t`. -/
lemma globalSectionsToUpperStar_app_comp_resOver_app {S T Z : Scheme.{u}} {s : S ⟶ Z}
    {t : T ⟶ Z} (h : S ⟶ T) (e : h ≫ t = s) (F : Sheaf (Scheme.ProEt.topology Z) A) :
    (globalSectionsToUpperStar A t).app F ≫ (resOver A h e).app F =
      (globalSectionsToUpperStar A s).app F := by
  rw [resOver_app, ← reassoc_of% (globalSectionsToUpperStar_comp A h t F), ← Functor.map_comp]
  have : (upperStarComp A h t).hom.app F ≫ (upperStarFactor A e).inv.app F =
      (upperStarCongr A e).hom.app F := by
    rw [upperStarFactor_inv_app, Iso.hom_inv_id_app_assoc]
  rw [this, globalSectionsToUpperStar_app_comp_upperStarCongr]



end Transport

section Constancy

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K]

/-- **The sections of the constant sheaf on a connected scheme are constant**: the restriction
`Γ(Z, ℚ̄_ℓ) ⟶ Γ(Spec K, s^* ℚ̄_ℓ)` to a point with values in a field is an isomorphism, both sides
being lines and the section `1` restricting to a nonzero section. -/
theorem isIso_globalSectionsToUpperStar_app_adicConstantSheaf {Z : Scheme.{u}}
    [ConnectedSpace Z] (s : Spec (.of K) ⟶ Z) :
    IsIso ((globalSectionsToUpperStar (WeilCoefficients.{u} l) s).app
      (adicConstantSheaf l Z)) := by
  let φ := ((WeilCoefficients.toModuleCat l).map
    ((globalSectionsToUpperStar (WeilCoefficients.{u} l) s).app (adicConstantSheaf l Z))).hom
  have h₁ := finrank_globalSections_adicConstantSheaf (l := l) Z
  have h₂ := finrank_globalSections_upperStar_adicConstantSheaf (l := l) s
  have : FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj (adicConstantSheaf l Z))) :=
    Module.finite_of_finrank_eq_succ h₁
  have : FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((s)^*[_].obj (adicConstantSheaf l Z)))) :=
    Module.finite_of_finrank_eq_succ h₂
  let v : (WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj (adicConstantSheaf l Z)) := oneGlobalSection Z
  have hv : v ≠ 0 := oneGlobalSection_ne_zero Z
  have hφv : φ v ≠ 0 := globalSectionsToUpperStar_oneGlobalSection_ne_zero s
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).1 h₁ m
    rw [map_smul, smul_eq_zero] at hm
    rcases hm with hc | hc
    · rw [hc, zero_smul]
    · exact absurd hc hφv
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h₁.trans h₂.symm)).1 hinj⟩
  have hbij' : Function.Bijective
      ((globalSectionsToUpperStar (WeilCoefficients.{u} l) s).app (adicConstantSheaf l Z)).hom :=
    hbij
  exact (ConcreteCategory.isIso_iff_bijective _).2 hbij'

/-- The restriction of the global sections of a free `ℓ`-adic sheaf of finite rank on a connected
scheme to a point with values in a field is an isomorphism. -/
theorem isIso_globalSectionsToUpperStar_app_of_iso_biproduct {Z : Scheme.{u}}
    [ConnectedSpace Z] (s : Spec (.of K) ⟶ Z) {M : AdicSheaf l Z} {n : ℕ}
    (E : M ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l Z) :
    IsIso ((globalSectionsToUpperStar (WeilCoefficients.{u} l) s).app M.X) := by
  let α := Functor.whiskerLeft (AdicSheaf.forget Z)
    (globalSectionsToUpperStar (WeilCoefficients.{u} l) s)
  have : ∀ j : Fin n, IsIso (α.app ((fun _ : Fin n ↦ AdicSheaf.unit l Z) j)) := fun _ ↦
    isIso_globalSectionsToUpperStar_app_adicConstantSheaf s
  have := NatTrans.isIso_app_biproduct α (fun _ : Fin n ↦ AdicSheaf.unit l Z) this
  exact (NatTrans.isIso_app_iff_of_iso α E).2 this

end Constancy

section Monoidal

variable {l : ℕ} [Fact l.Prime]

/-- The restriction of global sections along a morphism is monoidal. -/
instance isMonoidal_globalSectionsToUpperStar {Z W : Scheme.{u}} (g : Z ⟶ W) :
    NatTrans.IsMonoidal (globalSectionsToUpperStar (WeilCoefficients.{u} l) g) := by
  have e : globalSectionsToUpperStar (WeilCoefficients.{u} l) g =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit
          (Sheaf.Γ (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)) ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (g)^*[WeilCoefficients.{u} l]
          (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g).hom := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
      Category.id_comp, globalSectionsToUpperStar_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
  rw [e]
  infer_instance

/-- The factorisation isomorphisms of pullbacks are monoidal. -/
instance isMonoidal_upperStarFactor_inv {P Z W : Scheme.{u}} {a : P ⟶ W} {b : P ⟶ Z}
    {c : Z ⟶ W} (e : b ≫ c = a) :
    NatTrans.IsMonoidal (upperStarFactor (WeilCoefficients.{u} l) e).inv := by
  subst e
  rw [upperStarFactor_rfl]
  infer_instance

/-- The restriction of sections over `Z` is monoidal. -/
instance isMonoidal_resOver {S T Z : Scheme.{u}} {s : S ⟶ Z} {t : T ⟶ Z} (h : S ⟶ T)
    (e : h ≫ t = s) : NatTrans.IsMonoidal (resOver (WeilCoefficients.{u} l) h e) := by
  have e' : resOver (WeilCoefficients.{u} l) h e =
      Functor.whiskerLeft (t)^*[WeilCoefficients.{u} l]
        (globalSectionsToUpperStar (WeilCoefficients.{u} l) h) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (upperStarFactor (WeilCoefficients.{u} l) e).inv
          (Sheaf.Γ (Scheme.ProEt.topology S) (WeilCoefficients.{u} l)) := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    simp only [NatTrans.comp_app, Functor.associator_inv_app, Category.id_comp, resOver_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [e']
  infer_instance

/-- A monoidal natural transformation of lax monoidal functors to `ℚ̄_ℓ`-modules preserves the
pairings induced by the evaluation of internal homs. -/
lemma evaluationPairing_natTrans {Z : Scheme.{u}}
    {Φ Ψ : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l) ⥤ WeilCoefficients.{u} l}
    [Φ.LaxMonoidal] [Ψ.LaxMonoidal] (α : Φ ⟶ Ψ) [NatTrans.IsMonoidal α] (M N : AdicSheaf l Z)
    (f : Φ.obj ((AdicSheaf.ihom M).obj N).X) (x : Φ.obj M.X) :
    Mod.evaluationPairing Ψ M N ((α.app _).hom f) ((α.app _).hom x) =
      (α.app _).hom (Mod.evaluationPairing Φ M N f x) := by
  have h := congrArg (fun m ↦ m.hom (f ⊗ₜ x))
    (NatTrans.IsMonoidal.tensor (τ := α) ((AdicSheaf.ihom M).obj N).X M.X)
  have hn := congrArg (fun m ↦ m.hom ((μ Φ _ _).hom (f ⊗ₜ x)))
    (α.naturality (Mod.evaluation M N))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h hn
  simp only [Mod.evaluationPairing_apply]
  rw [hn, h]
  rfl

end Monoidal

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.UniversalCovers

open ProEtale FiniteEtale

variable (l : ℕ) [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  (U : Scheme.UniversalCovers Y Ω)

/-- The restriction `Γ(Ỹ_y, p_y^* F) ⟶ Γ(Spec Ω̄, y^* F)` along the base point `ỹ` of the
universal cover. -/
noncomputable def ptRes (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    (U.proj y)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _ ⟶ stalkFunctor l y :=
  resOver _ (U.pt y) (U.pt_proj y)

/-- The transport `Ỹ_y ≅ Ỹ_z` along a path is an isomorphism over `Y`. -/
lemma transport_inv_proj {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z) :
    (U.transport τ).inv ≫ U.proj y = U.proj z := by
  rw [Iso.inv_comp_eq, U.transport_proj]

/-- The transport `Γ(Ỹ_y, p_y^* F) ≅ Γ(Ỹ_z, p_z^* F)` of sections along a path
`τ : F_y ≅ F_z`: the restriction along the inverse of the isomorphism `Ỹ_y ≅ Ỹ_z` over `Y`. -/
noncomputable def transportRes {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) :
    (U.proj y)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _ ≅
      (U.proj z)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _ where
  hom := resOver _ (U.transport τ).inv (U.transport_inv_proj τ)
  inv := resOver _ (U.transport τ).hom (U.transport_proj τ)
  hom_inv_id := by
    ext F : 2
    rw [NatTrans.comp_app, resOver_comp _ _ _ _ _ (by rw [Iso.hom_inv_id, Category.id_comp]),
      resOver_congr _ (Iso.hom_inv_id _) _ (Category.id_comp _), resOver_id]
    rfl
  inv_hom_id := by
    ext F : 2
    rw [NatTrans.comp_app, resOver_comp _ _ _ _ _ (by rw [Iso.inv_hom_id, Category.id_comp]),
      resOver_congr _ (Iso.inv_hom_id _) _ (Category.id_comp _), resOver_id]
    rfl

/-- The transport of sections along a path is the restriction along the inverse of the
transport of the universal covers. -/
lemma transportRes_hom_app {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (U.transportRes l τ).hom.app F =
      (resOver _ (U.transport τ).inv (U.transport_inv_proj τ)).app F :=
  rfl

/-- Transport along the trivial path is the identity. -/
lemma transportRes_refl (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (U.transportRes l (Iso.refl (fiber y))).hom.app F = 𝟙 _ := by
  rw [transportRes_hom_app, resOver_congr _ (by rw [U.transport_refl]; rfl)
    (U.transport_inv_proj _) (Category.id_comp _), resOver_id]

/-- Transport along a composite path is the composite of the transports. -/
lemma transportRes_trans {y z w : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) (τ' : fiber z ≅ fiber w)
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (U.transportRes l (τ ≪≫ τ')).hom.app F =
      (U.transportRes l τ).hom.app F ≫ (U.transportRes l τ').hom.app F := by
  rw [transportRes_hom_app, transportRes_hom_app, transportRes_hom_app,
    resOver_comp _ _ _ _ _ (by rw [Category.assoc, U.transport_inv_proj, U.transport_inv_proj]),
    resOver_congr _ (h := (U.transport (τ ≪≫ τ')).inv)
      (h' := (U.transport τ').inv ≫ (U.transport τ).inv) (by rw [U.transport_trans]; rfl)]

variable {l U} in
/-- The restriction to the base point is an isomorphism on lisse sheaves, if lisse sheaves are
free of finite rank on the universal covers. -/
theorem isIso_ptRes_app
    (hU : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
      Nonempty ((U.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)))
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :
    IsIso ((U.ptRes l y).app G.obj.X) := by
  obtain ⟨n, ⟨E⟩⟩ := hU y G
  have := U.connectedSpace y
  have h := isIso_globalSectionsToUpperStar_app_of_iso_biproduct (U.pt y) E
  rw [adicUpperStar_obj_X] at h
  rw [ptRes, resOver_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h inferInstance

/-- The restriction to the base point is monoidal. -/
instance (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : NatTrans.IsMonoidal (U.ptRes l y) :=
  inferInstanceAs (NatTrans.IsMonoidal (resOver _ _ _))

/-- The transport of sections along a path is monoidal. -/
instance {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z) :
    NatTrans.IsMonoidal (U.transportRes l τ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (resOver _ _ _))

/-- The restriction to the base point, as a restriction over `Y`. -/
lemma ptRes_app (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (U.ptRes l y).app F = (resOver _ (U.pt y) (U.pt_proj y)).app F :=
  rfl

/-- The comparison `Γ(Ỹ_{y ≫ f}, p_{y ≫ f}^* F) ⟶ Γ(Ỹ_y, p_y^* f^* F)` along the morphism
`Ỹ_y ⟶ Ỹ_{y ≫ f}` over an endomorphism `f` of `Y`. -/
noncomputable def mapRes (f : Y ⟶ Y) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (Sheaf.Γ _ _).obj ((U.proj (y ≫ f))^*[WeilCoefficients.{u} l].obj F) ⟶
      (Sheaf.Γ _ _).obj ((U.proj y)^*[WeilCoefficients.{u} l].obj ((f)^*[_].obj F)) :=
  globalSectionsTransport _ (U.map_proj f y) (𝟙 _)

/-- The restriction to the base point over `y ≫ f`, followed by
`Γ(Spec Ω̄, (y ≫ f)^* F) ≅ Γ(Spec Ω̄, y^* f^* F)`, is the comparison along `Ỹ_y ⟶ Ỹ_{y ≫ f}`
followed by the restriction to the base point over `y`. -/
lemma ptRes_app_comp_upperStarStalkIso (f : Y ⟶ Y) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (U.ptRes l (y ≫ f)).app F ≫ (upperStarStalkIso l f y F).hom =
      U.mapRes l f y F ≫ (U.ptRes l y).app ((f)^*[_].obj F) := by
  have h₀ : U.pt (y ≫ f) ≫ U.proj (y ≫ f) = y ≫ f := U.pt_proj _
  rw [ptRes_app, ptRes_app, resOver_app_eq_transport, resOver_app_eq_transport, mapRes]
  refine Eq.trans ?_ (globalSectionsTransport_comp_eq _ _ _ h₀ (U.pt_map f y)
    (Category.id_comp f) _ _ (𝟙 _) ?_).symm
  · rw [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, globalSectionsTransport,
      globalSectionsTransport, Category.assoc, ← Functor.map_comp]
    refine congrArg (_ ≫ ·) (congrArg (Sheaf.Γ _ _).map ?_)
    rw [upperStarCompIso_hom_app, upperStarCompIso_hom_app]
    simp only [CategoryTheory.Functor.map_id, Category.assoc]
    rw [reassoc_of% upperStarComp_id_right_hom_app,
      reassoc_of% (upperStarCongr_hom_app_comp_hom_app _ _ _ h₀ F)]
    exact (Category.comp_id _).symm
  · simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    exact upperStarComp_id_left_hom_app _ f F

/-- The comparisons along `Ỹ_y ⟶ Ỹ_{y ≫ f}` intertwine the transports along a path and along
the induced path of `f`. -/
lemma transportRes_hom_app_comp_mapRes (f : Y ⟶ Y) {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (U.transportRes l (pullbackPathIso f τ)).hom.app F ≫ U.mapRes l f z F =
      U.mapRes l f y F ≫ (U.transportRes l τ).hom.app ((f)^*[_].obj F) := by
  have hτ : (U.transport τ).inv ≫ U.map f y =
      U.map f z ≫ (U.transport (pullbackPathIso f τ)).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, U.map_transport, Iso.inv_hom_id_assoc]
  have h'' : (U.map f z ≫ (U.transport (pullbackPathIso f τ)).inv) ≫ U.proj (y ≫ f) =
      U.proj z ≫ f := by
    rw [Category.assoc, U.transport_inv_proj, U.map_proj]
  rw [transportRes_hom_app, transportRes_hom_app, resOver_app_eq_transport,
    resOver_app_eq_transport, mapRes, mapRes]
  refine (globalSectionsTransport_comp_eq _ _ _ h'' rfl (Category.comp_id f) _ _ (𝟙 _) ?_).trans
    (globalSectionsTransport_comp_eq _ _ _ h'' hτ (Category.id_comp f) _ _ (𝟙 _) ?_).symm
  · simp only [Category.comp_id]
    exact upperStarComp_id_right_hom_app _ f F
  · simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    exact upperStarComp_id_left_hom_app _ f F

variable {l U}
variable (hU : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
  Nonempty ((U.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)))

include hU in
/-- The identification `Γ(Ỹ_y, p_y^* G) ≅ G_y` of the sections of a lisse sheaf over the universal
cover with its stalk, by restriction to the base point. -/
noncomputable def ptResIso (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    (ObjectProperty.ι _ ⋙ AdicSheaf.forget Y) ⋙
        ((U.proj y)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _) ≅ lisseStalk l y := by
  have : ∀ G : LisseSheaf l Y, IsIso ((Functor.whiskerLeft
      (ObjectProperty.ι _ ⋙ AdicSheaf.forget Y) (U.ptRes l y)).app G) :=
    fun G ↦ isIso_ptRes_app hU y G
  exact @asIso _ _ _ _ (Functor.whiskerLeft (ObjectProperty.ι _ ⋙ AdicSheaf.forget Y) (U.ptRes l y))
    (NatIso.isIso_of_isIso_app _)

/-- The transport of stalks of lisse sheaves along a path `τ : F_y ≅ F_z`:
`G_y ≅ Γ(Ỹ_y, p_y^* G) ≅ Γ(Ỹ_z, p_z^* G) ≅ G_z`. -/
noncomputable def monoIso {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z) :
    lisseStalk l y ≅ lisseStalk l z :=
  (ptResIso hU y).symm ≪≫ Functor.isoWhiskerLeft _ (U.transportRes l τ) ≪≫ ptResIso hU z

/-- The transport of stalks, in terms of the sections over the universal covers. -/
lemma ptRes_app_comp_monoIso_hom_app {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y) :
    (U.ptRes l y).app G.obj.X ≫ (monoIso hU τ).hom.app G =
      (U.transportRes l τ).hom.app G.obj.X ≫ (U.ptRes l z).app G.obj.X := by
  have h : (ptResIso hU y).hom.app G = (U.ptRes l y).app G.obj.X := rfl
  simp only [monoIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [← h, Iso.hom_inv_id_app_assoc]
  rfl

/-- The transport of stalks, on elements. -/
lemma monoIso_hom_app_ptRes_apply {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y)
    (s : (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      ((U.proj y)^*[WeilCoefficients.{u} l].obj G.obj.X)) :
    ((monoIso hU τ).hom.app G).hom (((U.ptRes l y).app G.obj.X).hom s) =
      ((U.ptRes l z).app G.obj.X).hom (((U.transportRes l τ).hom.app G.obj.X).hom s) :=
  congrArg (fun φ ↦ φ.hom s) (ptRes_app_comp_monoIso_hom_app hU τ G)

/-- Transport along the trivial path is the identity. -/
lemma monoIso_refl (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    monoIso hU (Iso.refl (fiber y)) = Iso.refl _ := by
  refine Iso.ext (NatTrans.ext (funext fun G ↦ ?_))
  have := isIso_ptRes_app hU y G
  rw [← cancel_epi ((U.ptRes l y).app G.obj.X), ptRes_app_comp_monoIso_hom_app, transportRes_refl]
  rfl

/-- Transport along a composite path is the composite of the transports. -/
lemma monoIso_trans {y z w : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) : monoIso hU (τ ≪≫ τ') = monoIso hU τ ≪≫ monoIso hU τ' := by
  refine Iso.ext (NatTrans.ext (funext fun G ↦ ?_))
  have := isIso_ptRes_app hU y G
  rw [← cancel_epi ((U.ptRes l y).app G.obj.X), ptRes_app_comp_monoIso_hom_app, Iso.trans_hom,
    NatTrans.comp_app, reassoc_of% ptRes_app_comp_monoIso_hom_app, ptRes_app_comp_monoIso_hom_app,
    transportRes_trans, Category.assoc]

/-- The restriction along an automorphism `a` of `Spec Ω̄` is inverse to the identification
`Γ(Spec Ω̄, (a ≫ y)^* F) ≅ Γ(Spec Ω̄, y^* F)`. -/
lemma resOver_app_eq_reparamStalkIso_inv
    (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (resOver _ a.hom (rfl : a.hom ≫ y = a.hom ≫ y)).app F = (reparamStalkIso l a y F).inv := by
  have h' := globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso
    (WeilCoefficients.{u} l) a ((y)^*[_].obj F)
  replace h' := (Iso.comp_hom_eq_id ((globalSectionsUpperStarIso _ a).app _)).1 h'
  rw [resOver_app, upperStarFactor_rfl, reparamStalkIso, h', Iso.trans_inv, Functor.mapIso_inv,
    Iso.app_inv]
  rfl

/-- The reparametrisation path acts by the canonical identification of the stalks. -/
lemma monoIso_reparam (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :
    (monoIso hU (fiberReparamIso a y)).hom.app G = (reparamStalkIso l a y G.obj.X).hom := by
  have := isIso_ptRes_app hU (a.hom ≫ y) G
  rw [← cancel_epi ((U.ptRes l (a.hom ≫ y)).app G.obj.X), ptRes_app_comp_monoIso_hom_app,
    ← Iso.comp_inv_eq, ← resOver_app_eq_reparamStalkIso_inv, Category.assoc, ptRes_app,
    resOver_comp _ _ _ _ _ (by rw [Category.assoc, U.pt_proj]), transportRes_hom_app,
    resOver_comp _ _ _ _ _ (by rw [Category.assoc, U.transport_inv_proj, Category.assoc,
      U.pt_proj]), ptRes_app]
  congr 2
  rw [← U.pt_transport_reparam, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Compatibility of the transport with pullback along an endomorphism of `Y`. -/
lemma monoIso_upperStar (f : Y ⟶ Y) {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y) :
    (monoIso hU (pullbackPathIso f τ)).hom.app G ≫ (upperStarStalkIso l f z G.obj.X).hom =
      (upperStarStalkIso l f y G.obj.X).hom ≫ (monoIso hU τ).hom.app (G.upperStar l f) := by
  have := isIso_ptRes_app hU (y ≫ f) G
  rw [← cancel_epi ((U.ptRes l (y ≫ f)).app G.obj.X), reassoc_of% ptRes_app_comp_monoIso_hom_app,
    ptRes_app_comp_upperStarStalkIso, reassoc_of% ptRes_app_comp_upperStarStalkIso,
    reassoc_of% transportRes_hom_app_comp_mapRes]
  exact congrArg (U.mapRes l f y G.obj.X ≫ ·)
    (ptRes_app_comp_monoIso_hom_app hU τ (G.upperStar l f)).symm

/-- Global sections restrict to sections of the stalks which are invariant under transport. -/
lemma monoIso_globalSections {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (G : LisseSheaf l Y) :
    (globalSectionsToUpperStar _ y).app G.obj.X ≫ (monoIso hU τ).hom.app G =
      (globalSectionsToUpperStar _ z).app G.obj.X := by
  rw [← globalSectionsToUpperStar_app_comp_resOver_app _ (U.pt y) (U.pt_proj y),
    Category.assoc, ← ptRes_app, ptRes_app_comp_monoIso_hom_app, transportRes_hom_app,
    ← Category.assoc, globalSectionsToUpperStar_app_comp_resOver_app, ptRes_app,
    globalSectionsToUpperStar_app_comp_resOver_app]

/-- The transport preserves the evaluation pairing `[G, H]_y × G_y → H_y`: all maps involved are
monoidal. -/
lemma monoIso_evaluationPairing {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) (G H : LisseSheaf l Y)
    (hGH : IsAdicLisseSheaf ((AdicSheaf.ihom G.obj).obj H.obj))
    (d : (stalkFunctor l y).obj ((AdicSheaf.ihom G.obj).obj H.obj).X)
    (v : (stalkFunctor l y).obj G.obj.X) :
    Mod.evaluationPairing (stalkFunctor l z) G.obj H.obj
        (((monoIso hU τ).hom.app ⟨_, hGH⟩).hom d) (((monoIso hU τ).hom.app G).hom v) =
      ((monoIso hU τ).hom.app H).hom
        (Mod.evaluationPairing (stalkFunctor l y) G.obj H.obj d v) := by
  have hd := isIso_ptRes_app hU y ⟨_, hGH⟩
  have hv := isIso_ptRes_app hU y G
  obtain ⟨d, rfl⟩ : ∃ d₀, ((U.ptRes l y).app _).hom d₀ = d :=
    ⟨(inv ((U.ptRes l y).app _)).hom d, by rw [← ModuleCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
  obtain ⟨v, rfl⟩ : ∃ v₀, ((U.ptRes l y).app _).hom v₀ = v :=
    ⟨(inv ((U.ptRes l y).app _)).hom v, by rw [← ModuleCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
  rw [monoIso_hom_app_ptRes_apply hU τ ⟨_, hGH⟩, monoIso_hom_app_ptRes_apply hU τ G,
    evaluationPairing_natTrans, evaluationPairing_natTrans, evaluationPairing_natTrans]
  exact (monoIso_hom_app_ptRes_apply hU τ H _).symm

/-- **The monodromy of lisse sheaves from universal covers** on which lisse sheaves are free of
finite rank: the transport `G_y ≅ Γ(Ỹ_y, p_y^* G) ≅ Γ(Ỹ_z, p_z^* G) ≅ G_z` of stalks along
paths `τ : F_y ≅ F_z` (blueprint: `situation-weil`). -/
noncomputable def lisseMonodromy : LisseMonodromy l Y Ω where
  mono τ := monoIso hU τ
  mono_refl := monoIso_refl hU
  mono_trans := monoIso_trans hU
  mono_reparam := monoIso_reparam hU
  mono_upperStar := monoIso_upperStar hU
  mono_globalSections := monoIso_globalSections hU
  mono_evaluationPairing := monoIso_evaluationPairing hU

/-- The transport of the monodromy from universal covers. -/
lemma lisseMonodromy_mono {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) : (U.lisseMonodromy hU).mono τ = monoIso hU τ :=
  rfl

end AlgebraicGeometry.Scheme.UniversalCovers
