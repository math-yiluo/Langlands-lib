/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists
public import WeilConjectures.WeilSheaf.WeilMonodromy

/-!
# Weil II 1.3.14 in arbitrary dimension

`WeilConjectures.WeilSheaf.WeilMonodromy` proves Deligne's Weil II 1.3.14 for lisse Weil sheaves
on a *curve* `C₀`, through the Weil group `AlgebraicGeometry.WeilGroup` of the curve. The curve
hypothesis `[IsCurve p]` is only a parameter of that structure: the construction of the Weil
fundamental representation uses nothing but the monodromy `M` of lisse sheaves on the geometric
fibre (which exists for any connected regular Noetherian scheme,
`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`), a geometric point `t` with a path
`β : F_t ≅ F_{t ≫ Fr}`, and the homotopy exact sequence data
`AlgebraicGeometry.WeilGroup.WeilMonodromyData`. This file removes the curve hypothesis.

* `AlgebraicGeometry.FrobeniusBasePoint`: the pair `(t, β)` for a scheme `X₀` over the finite
  field `K` of arbitrary dimension.
* `AlgebraicGeometry.FrobeniusBasePoint.frobConj`: the Frobenius transport `g ↦ β ≫ Fr_* g ≫ β⁻¹`
  is an automorphism of `π₁(X, t) = Aut F_t` (its inverse is the transport along `Fr⁻¹`,
  `AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso_inv_pullbackPathIso`).
* `AlgebraicGeometry.FrobeniusBasePoint.WeilGroup`: the Weil group `π₁(X, t) ⋊ ℤ`, constructed
  directly as a semidirect product, so that no homotopy exact sequence is needed.
* `AlgebraicGeometry.FrobeniusBasePoint.WeilData`: the abstract input (a group `W` with a
  surjective degree, `π₁(X, t) ≅ ker deg`, and a degree-one `γ` inducing the Frobenius
  transport); `AlgebraicGeometry.FrobeniusBasePoint.weilData` is the canonical instance on
  `π₁(X, t) ⋊ ℤ`, every instance is isomorphic to it
  (`AlgebraicGeometry.FrobeniusBasePoint.WeilData.weilGroupEquiv`,
  `AlgebraicGeometry.FrobeniusBasePoint.WeilData.fundamentalRep_toWeilGroupHom`), and the curve
  data give an instance (`AlgebraicGeometry.WeilGroup.WeilMonodromyData.toWeilData`) whose
  fundamental representation is the one of curves
  (`AlgebraicGeometry.WeilGroup.WeilMonodromyData.fundamentalRep_toWeilData`).
* `AlgebraicGeometry.FrobeniusBasePoint.WeilData.fundamentalRep`: the Weil fundamental
  representation, with fullness, faithfulness and essential surjectivity
  (`AlgebraicGeometry.FrobeniusBasePoint.WeilData.exists_equivalence_fundamentalRep`).
* `FrobeniusBasePoint.WeilData.isIrreducibleLisse_iff_isIrreducible_fundamentalRep`, and
  **Deligne, Weil II, 1.3.14**:
  `AlgebraicGeometry.FrobeniusBasePoint.WeilData.exists_isBoundedOn_twist_fundamentalRep`,
  `AlgebraicGeometry.FrobeniusBasePoint.WeilData.exists_isBoundedOn_fundamentalRep_twist`, with the
  finite and trivial geometric monodromy variants.
* `FrobeniusBasePoint.exists_lisseMonodromy_isBoundedOn_twist_fundamentalRep_of_smooth`:
  1.3.14 for smooth geometrically connected `X₀` of finite type over `K` of any dimension, with
  no remaining hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The first projection `P ×_X X ⟶ P`, as a morphism of finite étale `X`-schemes from the base
change of `P` along the identity. -/
noncomputable def pullbackIdHom (P : X.FiniteEtale) : (pullback (𝟙 X)).obj P ⟶ P :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (Limits.pullback.fst P.obj.hom (𝟙 X))
    (Limits.pullback.condition.trans (Category.comp_id _)))

/-- The path induced by `τ` along the identity is `τ`, up to the identifications
`y ≫ 𝟙 = y` and `z ≫ 𝟙 = z`. -/
lemma pullbackPathIso_id {y z : Spec (.of Ω) ⟶ X} (τ : fiber y ≅ fiber z) :
    pullbackPathIso (𝟙 X) τ =
      eqToIso (by rw [Category.comp_id]) ≪≫ τ ≪≫ eqToIso (by rw [Category.comp_id]) := by
  ext P x
  apply fiber_ext
  rw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, FintypeCat.comp_apply,
    FintypeCat.comp_apply, eqToIso_fiber_hom_app_left (Category.comp_id z).symm,
    pullbackPathIso_hom_app_left]
  have hw : (fiber y).map (pullbackIdHom P) ((pullbackFiberIso (𝟙 X) y).inv.app P x) =
      (eqToIso (congrArg fiber (Category.comp_id y))).hom.app P x := by
    apply fiber_ext
    rw [fiber_map_left, pullbackFiberIso_inv_app_left,
      eqToIso_fiber_hom_app_left (Category.comp_id y)]
    simp [pullbackIdHom]
  rw [← hw, ← ConcreteCategory.comp_apply, τ.hom.naturality, ConcreteCategory.comp_apply,
    fiber_map_left]
  rfl

/-- Inducing a path along an isomorphism `e` and then along its inverse gives back the path, up
to the identifications `y ≫ e ≫ e⁻¹ = y`. -/
lemma pullbackPathIso_inv_pullbackPathIso (e : X ≅ Y) {y z : Spec (.of Ω) ⟶ X}
    (τ : fiber y ≅ fiber z) :
    pullbackPathIso e.inv (pullbackPathIso e.hom τ) =
      eqToIso (by simp) ≪≫ τ ≪≫ eqToIso (by simp) := by
  have h := pullbackPathIso_comp e.hom e.inv τ
  rw [pullbackPathIso_congr e.hom_inv_id, pullbackPathIso_id] at h
  ext1
  have h' := congrArg Iso.hom h
  simp only [Iso.trans_hom, eqToIso.hom] at h' ⊢
  rw [← cancel_epi (eqToHom (by simp : fiber (y ≫ e.hom ≫ e.inv) = fiber ((y ≫ e.hom) ≫ e.inv))),
    ← cancel_mono (eqToHom (by simp : fiber ((z ≫ e.hom) ≫ e.inv) = fiber (z ≫ e.hom ≫ e.inv)))]
  simp only [Category.assoc] at h' ⊢
  rw [← h']
  simp

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale

variable (K : Type u) [Field K] [Finite K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- Base point data for the Weil fundamental representation on a scheme `X₀` over the finite
field `K` of arbitrary dimension (cf. `AlgebraicGeometry.WeilGroup.BasePointData` for curves):
a geometric point `t` of the geometric fibre `X = X₀ ×_K K̄` and a path `β : F_t ≅ F_{t ≫ Fr}`
from `t` to its image under the geometric Galois Frobenius `Fr` of `X`. -/
structure FrobeniusBasePoint where
  /-- The geometric base point of the geometric fibre. -/
  t : Spec (.of (AlgebraicClosure K)) ⟶ (X ↘ Spec (.of K)).geometricFiber
  /-- A path from `t` to `t ≫ Fr`. -/
  frobPath : fiber t ≅ fiber (t ≫ (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)

variable {K X}

namespace FrobeniusBasePoint

/-- Base point data exist as soon as the geometric fibre is connected and has a geometric
point: any two fibre functors of the Galois category of finite étale covers are isomorphic. -/
theorem nonempty [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber]
    (t : Spec (.of (AlgebraicClosure K)) ⟶ (X ↘ Spec (.of K)).geometricFiber) :
    Nonempty (FrobeniusBasePoint K X) :=
  ⟨⟨t, (PreGaloisCategory.nonempty_iso_of_fiberFunctor _ _).some⟩⟩

variable (B : FrobeniusBasePoint K X)

/-- The transport `g ↦ β ≫ Fr_* g ≫ β⁻¹` of loops at `t` along the Frobenius and the path `β`,
as an automorphism of `π₁(X, t) = Aut F_t`; its inverse is the transport along `Fr⁻¹`. -/
noncomputable def frobConj : Aut (fiber B.t) ≃* Aut (fiber B.t) where
  toFun g := .of (B.frobPath ≪≫
    pullbackPathIso (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
      B.frobPath.symm)
  invFun g := .of (eqToIso (congrArg fiber (by simp)) ≪≫
    pullbackPathIso (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv
      (B.frobPath.symm ≪≫ g.asIso ≪≫ B.frobPath) ≪≫ eqToIso (congrArg fiber (by simp)))
  left_inv g := by
    apply Aut.ext
    dsimp only
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl,
      pullbackPathIso_inv_pullbackPathIso]
    refine Iso.ext ?_
    simp
  right_inv g := by
    apply Aut.ext
    have h := pullbackPathIso_inv_pullbackPathIso
      (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.symm
      (B.frobPath.symm ≪≫ g.asIso ≪≫ B.frobPath)
    simp only [Iso.symm_hom, Iso.symm_inv] at h
    dsimp only
    rw [pullbackPathIso_trans, pullbackPathIso_trans, h, pullbackPathIso_eqToIso,
      pullbackPathIso_eqToIso]
    · refine Iso.ext ?_
      simp
    all_goals simp
  map_mul' g h := by
    apply Aut.ext
    dsimp only
    simp only [Aut.mul_asIso, pullbackPathIso_trans]
    simp

lemma frobConj_apply (g : Aut (fiber B.t)) :
    B.frobConj g = .of (B.frobPath ≪≫
      pullbackPathIso (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
        B.frobPath.symm) :=
  rfl

/-- The action of `ℤ` on `π₁(X, t)` in which `1` acts by the inverse of the Frobenius
transport `frobConj`. -/
noncomputable abbrev frobAction : Multiplicative ℤ →* MulAut (Aut (fiber B.t)) :=
  zpowersHom _ B.frobConj⁻¹

/-- **The Weil group** `W(X₀, t) = π₁(X, t) ⋊ ℤ` attached to base point data `B`: the semidirect
product of the geometric fundamental group `π₁(X, t) = Aut F_t` with `ℤ`, where the generator
`γ = (1, 1)` acts by `γ⁻¹ g γ = β ≫ Fr_* g ≫ β⁻¹`. By the homotopy exact sequence it is the Weil
group of Deligne (Weil II, 1.1.7), the preimage of `ℤ` in `π₁(X₀, t)`, but this
identification is never needed: lisse Weil sheaves are equivalent to its continuous
representations. -/
abbrev WeilGroup : Type (u + 1) := Aut (fiber B.t) ⋊[B.frobAction] Multiplicative ℤ

/-- The input for the Weil fundamental representation in arbitrary dimension: a group `W` with
a surjective degree `deg : W → ℤ`, an identification `π₁(X, t) ≅ ker deg` and an element `γ`
of degree one such that the Frobenius transport `g ↦ β ≫ Fr_* g ≫ β⁻¹` of loops is conjugation
`g ↦ γ⁻¹ g γ` (cf. `AlgebraicGeometry.WeilGroup.WeilMonodromyData` for curves, where `W` is the
Weil group of the curve and the identification comes from the homotopy exact sequence). The
canonical instance is the semidirect product `AlgebraicGeometry.FrobeniusBasePoint.WeilGroup`
(`AlgebraicGeometry.FrobeniusBasePoint.weilData`). -/
structure WeilData (W : Type*) [Group W] where
  /-- The degree. -/
  deg : W →* Multiplicative ℤ
  deg_surjective : Function.Surjective deg
  /-- The identification `π₁(X, t) ≅ ker deg`. -/
  geomEquiv : Aut (fiber B.t) ≃* deg.ker
  /-- The lift of the Frobenius. -/
  frobLift : W
  deg_frobLift : deg frobLift = Multiplicative.ofAdd 1
  geomEquiv_conj (g : Aut (fiber B.t)) :
    (geomEquiv (B.frobConj g) : W) = frobLift⁻¹ * geomEquiv g * frobLift

/-- The canonical Weil data on the semidirect product `π₁(X, t) ⋊ ℤ`. -/
noncomputable def weilData : B.WeilData B.WeilGroup where
  deg := SemidirectProduct.rightHom
  deg_surjective := SemidirectProduct.rightHom_surjective
  geomEquiv := (MonoidHom.ofInjective SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom)
  frobLift := SemidirectProduct.inr (Multiplicative.ofAdd 1)
  deg_frobLift := SemidirectProduct.rightHom_inr _
  geomEquiv_conj g := by
    have h := SemidirectProduct.inl_aut (φ := B.frobAction) (Multiplicative.ofAdd (1 : ℤ))⁻¹ g
    rw [inv_inv, map_inv SemidirectProduct.inr] at h
    simp only [MulEquiv.coe_trans, Function.comp_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
    rw [← h]
    congr 1

section FundamentalRepresentation

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) (B : FrobeniusBasePoint K X)

/-- The Frobenius `Φ : ℱ_t ≅ ℱ_t` of the Weil fundamental representation
(`situation-weil`): the transport `ℱ_t ≅ ℱ_{t ≫ Fr}` along the path `β`, the
identification `ℱ_{t ≫ Fr} = (Fr^* ℱ)_t`, and the stalk at `t` of the Weil structure
`Fr^* ℱ ≅ ℱ`. -/
noncomputable def frobStalkIso (F : WeilSheaf K l X) (hF : F.IsLisse) :
    (lisseStalk l B.t).obj (F.toLisse hF) ≅ (lisseStalk l B.t).obj (F.toLisse hF) :=
  (M.mono B.frobPath).app (F.toLisse hF) ≪≫
    upperStarStalkIso l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom B.t F.obj.carrier.X ≪≫
    (lisseStalk l B.t).mapIso (F.lisseFrobStr hF)

/-- The Frobenius `Φ` of the Weil fundamental representation, as a `ℚ̄_ℓ`-linear automorphism of
the stalk. -/
noncomputable def frobStalk (F : WeilSheaf K l X) (hF : F.IsLisse) :
    LisseMonodromy.StalkSpace B.t (F.toLisse hF) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (F.toLisse hF) :=
  WeilCoefficients.linearEquivOfIso (frobStalkIso M B F hF)

/-- Twisted equivariance of the Frobenius, as an identity of morphisms of stalks. -/
theorem mono_hom_app_comp_frobStalkIso_hom (F : WeilSheaf K l X) (hF : F.IsLisse)
    (g : Aut (fiber B.t)) :
    (M.mono (B.frobConj g).asIso).hom.app (F.toLisse hF) ≫ (frobStalkIso M B F hF).hom =
      (frobStalkIso M B F hF).hom ≫ (M.mono g.asIso).hom.app (F.toLisse hF) := by
  have h₁ : (B.frobPath ≪≫
      pullbackPathIso (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
      B.frobPath.symm) ≪≫ B.frobPath =
      B.frobPath ≪≫
        pullbackPathIso (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso := by
    simp
  have e₁ := congrArg (fun τ ↦ (M.mono τ).hom.app (F.toLisse hF)) h₁
  rw [M.mono_trans (B.frobPath ≪≫ pullbackPathIso _ g.asIso ≪≫ B.frobPath.symm) B.frobPath,
    M.mono_trans B.frobPath (pullbackPathIso _ g.asIso)] at e₁
  simp only [Iso.trans_hom, NatTrans.comp_app] at e₁
  have e₂ := M.mono_upperStar (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso
    (F.toLisse hF)
  have e₃ := (M.mono g.asIso).hom.naturality (F.lisseFrobStr hF).hom
  simp only [frobStalkIso, frobConj_apply, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂, e₃]

/-- **Twisted equivariance of the Frobenius**: `Φ ρ_geom(β ≫ Fr_* g ≫ β⁻¹) = ρ_geom(g) Φ`. -/
theorem frobStalk_rep (F : WeilSheaf K l X) (hF : F.IsLisse) (g : Aut (fiber B.t))
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    frobStalk M B F hF (M.rep B.t (F.toLisse hF) (B.frobConj g) v) =
      M.rep B.t (F.toLisse hF) g (frobStalk M B F hF v) := by
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v)
    (mono_hom_app_comp_frobStalkIso_hom M B F hF g)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The Frobenius `Φ` of the Weil fundamental representation, as a unit of the endomorphisms. -/
noncomputable def frobUnit (F : WeilSheaf K l X) (hF : F.IsLisse) :
    (Module.End (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF)))ˣ where
  val := (frobStalk M B F hF).toLinearMap
  inv := (frobStalk M B F hF).symm.toLinearMap
  val_inv := LinearMap.ext fun v ↦ (frobStalk M B F hF).apply_symm_apply v
  inv_val := LinearMap.ext fun v ↦ (frobStalk M B F hF).symm_apply_apply v

/-- The map `ℱ_t → 𝒢_t` of stalks induced by a morphism of lisse Weil sheaves. -/
noncomputable def stalkMap {F G : WeilSheaf K l X} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    LisseMonodromy.StalkSpace B.t (F.toLisse hF) →ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (G.toLisse hG) :=
  ((WeilCoefficients.toModuleCat l).map
    ((lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG))).hom

/-- The stalk map of a composite is the composite of the stalk maps. -/
lemma stalkMap_comp {F G H : WeilSheaf K l X} (φ : F ⟶ G) (ψ : G ⟶ H) (hF : F.IsLisse)
    (hG : G.IsLisse) (hH : H.IsLisse) :
    B.stalkMap (φ ≫ ψ) hF hH = B.stalkMap ψ hG hH ∘ₗ B.stalkMap φ hF hG := by
  simp only [stalkMap]
  rw [show WeilSheaf.toLisseMap (φ ≫ ψ) hF hH =
    WeilSheaf.toLisseMap φ hF hG ≫ WeilSheaf.toLisseMap ψ hG hH from rfl,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- The stalk map of the identity is the identity. -/
lemma stalkMap_id {F : WeilSheaf K l X} (hF : F.IsLisse) :
    B.stalkMap (𝟙 F) hF hF = LinearMap.id := by
  simp only [stalkMap]
  rw [show WeilSheaf.toLisseMap (𝟙 F) hF hF = 𝟙 _ from rfl, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The stalk map of the zero morphism is zero. -/
lemma stalkMap_zero {F G : WeilSheaf K l X} (hF : F.IsLisse) (hG : G.IsLisse) :
    B.stalkMap (0 : F ⟶ G) hF hG = 0 := by
  have h₁ : WeilSheaf.toLisseMap (0 : F ⟶ G) hF hG = 0 := rfl
  have : (lisseStalk l B.t).Additive := inferInstance
  have : (WeilCoefficients.toModuleCat.{u} l).Additive := inferInstance
  simp only [stalkMap, h₁, Functor.map_zero]
  rfl

/-- The Frobenius of the stalks is natural in the lisse Weil sheaf. -/
theorem frobStalkIso_naturality {F G : WeilSheaf K l X} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    (lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG) ≫ (frobStalkIso M B G hG).hom =
      (frobStalkIso M B F hF).hom ≫ (lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG) := by
  have e₁ : (lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG) ≫
      (M.mono B.frobPath).hom.app (G.toLisse hG) =
      (M.mono B.frobPath).hom.app (F.toLisse hF) ≫
        (lisseStalk l _).map (WeilSheaf.toLisseMap φ hF hG) :=
    (M.mono B.frobPath).hom.naturality (WeilSheaf.toLisseMap φ hF hG)
  have e₃ := (lisseStalk l B.t).congr_map (ObjectProperty.hom_ext _
    (WeilSheaf.adicFrobStr_naturality φ) :
      (ObjectProperty.homMk (((X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map
        ((Endofunctor.IsoAlgebra.forget _).map φ.hom)) :
          (F.toLisse hF).upperStar l _ ⟶ (G.toLisse hG).upperStar l _) ≫
        (G.lisseFrobStr hG).hom =
      (F.lisseFrobStr hF).hom ≫ WeilSheaf.toLisseMap φ hF hG)
  rw [Functor.map_comp, Functor.map_comp] at e₃
  have e₁': ∀ {Z} (h : _ ⟶ Z), (lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG) ≫
      (M.mono B.frobPath).hom.app (G.toLisse hG) ≫ h = (M.mono B.frobPath).hom.app (F.toLisse hF) ≫
        (lisseStalk l _).map (WeilSheaf.toLisseMap φ hF hG) ≫ h := fun h ↦ by
    rw [← Category.assoc, e₁, Category.assoc]
  simp only [frobStalkIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [e₁']
  congr 1
  have key := upperStarStalkIso_hom_naturality l
    (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom B.t
    ((Endofunctor.IsoAlgebra.forget _).map φ.hom).hom
  erw [reassoc_of% key]
  congr 1

/-- Stalk maps commute with the Frobenius `Φ`. -/
theorem stalkMap_frobStalk {F G : WeilSheaf K l X} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    B.stalkMap φ hF hG (frobStalk M B F hF v) = frobStalk M B G hG (B.stalkMap φ hF hG v) := by
  have h := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
    (frobStalkIso_naturality M B φ hF hG)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- Stalk maps commute with the geometric fundamental representation. -/
theorem stalkMap_rep {F G : WeilSheaf K l X} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) (g : Aut (fiber B.t)) (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    B.stalkMap φ hF hG (M.rep B.t (F.toLisse hF) g v) =
      M.rep B.t (G.toLisse hG) g (B.stalkMap φ hF hG v) := by
  have h := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
    ((M.mono g.asIso).hom.naturality (WeilSheaf.toLisseMap φ hF hG))
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- The stalk functor at `t` on lisse Weil sheaves is faithful. -/
theorem stalkMap_injective (hM : M.IsEquivalenceAt B.t) {F G : LisseWeilSheaf K l X}
    (f f' : F ⟶ G)
    (h : B.stalkMap f.hom F.property G.property = B.stalkMap f'.hom F.property G.property) :
    f = f' :=
  LisseWeilSheaf.hom_ext (hM.faithful _ _ (WeilCoefficients.hom_ext_toModuleCat h))

/-- The transport of stalks of a lisse sheaf `𝒢` from `t` to `t ≫ Fr` along `β`, followed by the
identification `𝒢_{t ≫ Fr} = (Fr^* 𝒢)_t`. -/
noncomputable def frobPathStalkIso (G : LisseSheaf l (X ↘ Spec (.of K)).geometricFiber) :
    (lisseStalk l B.t).obj G ≅
      (lisseStalk l B.t).obj
        (G.upperStar l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) :=
  (M.mono B.frobPath).app G ≪≫
    upperStarStalkIso l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom B.t G.obj.X

omit [Fact (ringChar K ≠ l)] in
/-- `frobPathStalkIso` is natural in the lisse sheaf. -/
theorem frobPathStalkIso_naturality {G H : LisseSheaf l (X ↘ Spec (.of K)).geometricFiber}
    (f : G ⟶ H) :
    (lisseStalk l B.t).map f ≫ (frobPathStalkIso M B H).hom =
      (frobPathStalkIso M B G).hom ≫ (lisseStalk l B.t).map
        (ObjectProperty.homMk (((X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map
          f.hom) : G.upperStar l _ ⟶ H.upperStar l _) := by
  have e₁ : (lisseStalk l B.t).map f ≫ (M.mono B.frobPath).hom.app H =
      (M.mono B.frobPath).hom.app G ≫ (lisseStalk l _).map f :=
    (M.mono B.frobPath).hom.naturality f
  have key := upperStarStalkIso_hom_naturality l
    (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom B.t f.hom.hom
  simp only [frobPathStalkIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, e₁, Category.assoc]
  exact congrArg ((M.mono B.frobPath).hom.app G ≫ ·) key

omit [Fact (ringChar K ≠ l)] in
/-- Conjugating the transport `β ≫ Fr_* g ≫ β⁻¹` by `frobPathStalkIso` gives the monodromy of
`g` on `Fr^* 𝒢`. -/
theorem frobPathStalkIso_conj (G : LisseSheaf l (X ↘ Spec (.of K)).geometricFiber)
    (g : Aut (fiber B.t)) :
    (M.mono (B.frobConj g).asIso).hom.app G ≫ (frobPathStalkIso M B G).hom =
      (frobPathStalkIso M B G).hom ≫ (M.mono g.asIso).hom.app
        (G.upperStar l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) := by
  have h₁ : (B.frobPath ≪≫
      pullbackPathIso (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
      B.frobPath.symm) ≪≫ B.frobPath =
      B.frobPath ≪≫
        pullbackPathIso (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso := by
    simp
  have e₁ := congrArg (fun τ ↦ (M.mono τ).hom.app G) h₁
  rw [M.mono_trans (B.frobPath ≪≫ pullbackPathIso _ g.asIso ≪≫ B.frobPath.symm) B.frobPath,
    M.mono_trans B.frobPath (pullbackPathIso _ g.asIso)] at e₁
  simp only [Iso.trans_hom, NatTrans.comp_app] at e₁
  have e₂ := M.mono_upperStar (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso G
  simp only [frobPathStalkIso, frobConj_apply, Iso.trans_hom, Iso.app_hom]
  rw [reassoc_of% e₁, e₂]
  simp only [Category.assoc]

/-- The Frobenius `Φ` is the stalk of the Weil structure after `frobPathStalkIso`. -/
lemma frobStalk_apply (F : WeilSheaf K l X) (hF : F.IsLisse)
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    frobStalk M B F hF v = ((WeilCoefficients.toModuleCat l).map
      ((lisseStalk l B.t).map (F.lisseFrobStr hF).hom)).hom
        (((WeilCoefficients.toModuleCat l).map (frobPathStalkIso M B (F.toLisse hF)).hom).hom v) :=
  rfl

/-- A morphism of lisse sheaves between lisse Weil sheaves whose stalk at `t` commutes with the
Frobenius `Φ` commutes with the Weil structures. -/
theorem upperStar_comp_lisseFrobStr_of_frobStalk (hM : M.IsEquivalenceAt B.t)
    {F G : WeilSheaf K l X} (hF : F.IsLisse) (hG : G.IsLisse) (f : F.toLisse hF ⟶ G.toLisse hG)
    (hf : ∀ v, ((WeilCoefficients.toModuleCat l).map ((lisseStalk l B.t).map f)).hom
        (frobStalk M B F hF v) =
      frobStalk M B G hG
        (((WeilCoefficients.toModuleCat l).map ((lisseStalk l B.t).map f)).hom v)) :
    (ObjectProperty.homMk
      (((X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map f.hom) :
        (F.toLisse hF).upperStar l _ ⟶ (G.toLisse hG).upperStar l _) ≫ (G.lisseFrobStr hG).hom =
      (F.lisseFrobStr hF).hom ≫ f := by
  apply hM.faithful
  apply WeilCoefficients.hom_ext_toModuleCat
  refine LinearMap.ext fun w ↦ ?_
  obtain ⟨v, rfl⟩ : ∃ v, ((WeilCoefficients.toModuleCat l).map
      (frobPathStalkIso M B (F.toLisse hF)).hom).hom v = w :=
    (WeilCoefficients.linearEquivOfIso (frobPathStalkIso M B (F.toLisse hF))).surjective w
  have n := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
    (frobPathStalkIso_naturality M B f)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at n ⊢
  rw [← n]
  exact (hf v).symm

end FundamentalRepresentation

namespace WeilData

variable {B : FrobeniusBasePoint K X} {W : Type*} [Group W] (D : B.WeilData W)

/-- The degree datum `(W, deg, γ)` of Weil data. -/
noncomputable def degreeDatum : Monodromy.DegreeDatum W :=
  ⟨D.deg, D.deg_surjective, D.frobLift, D.deg_frobLift⟩

/-- An element of the kernel of the degree is the image of a loop at `t`. -/
lemma geomEquiv_symm_conj {u : W} (hu : u ∈ D.deg.ker) :
    D.geomEquiv.symm ⟨u, hu⟩ = B.frobConj (D.geomEquiv.symm
      ⟨D.frobLift * u * D.frobLift⁻¹, D.degreeDatum.deg.normal_ker.conj_mem u hu _⟩) := by
  apply D.geomEquiv.injective
  apply Subtype.ext
  rw [MulEquiv.apply_symm_apply, D.geomEquiv_conj, MulEquiv.apply_symm_apply]
  simp only
  group

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K)

/-- The geometric fundamental representation `ρ_geom`, on `ker deg ≅ π₁(X, t)`. -/
noncomputable def geomUnits (F : WeilSheaf K l X) (hF : F.IsLisse) :
    D.deg.ker →* (Module.End (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF)))ˣ :=
  (M.rep B.t (F.toLisse hF)).asGroupHom.comp D.geomEquiv.symm.toMonoidHom

/-- The Frobenius conjugates the geometric fundamental representation as `γ` conjugates
`ker deg`: `Φ ρ_geom(u) Φ⁻¹ = ρ_geom(γ u γ⁻¹)`. -/
theorem frobUnit_conj (F : WeilSheaf K l X) (hF : F.IsLisse) (u : W)
    (hu : u ∈ D.degreeDatum.deg.ker) :
    frobUnit M B F hF * D.geomUnits M F hF ⟨u, hu⟩ * (frobUnit M B F hF)⁻¹ =
      D.geomUnits M F hF ⟨D.degreeDatum.degreeOneElement * u * D.degreeDatum.degreeOneElement⁻¹,
        D.degreeDatum.deg.normal_ker.conj_mem u hu _⟩ := by
  refine Units.ext (LinearMap.ext fun w ↦ ?_)
  obtain ⟨v, rfl⟩ := (frobStalk M B F hF).surjective w
  change frobStalk M B F hF (M.rep B.t (F.toLisse hF) (D.geomEquiv.symm ⟨u, hu⟩)
      ((frobStalk M B F hF).symm (frobStalk M B F hF v))) =
    M.rep B.t (F.toLisse hF) (D.geomEquiv.symm ⟨D.frobLift * u * D.frobLift⁻¹,
      D.degreeDatum.deg.normal_ker.conj_mem u hu _⟩) (frobStalk M B F hF v)
  rw [LinearEquiv.symm_apply_apply, D.geomEquiv_symm_conj hu, frobStalk_rep]

/-- **The Weil fundamental representation** of a lisse Weil sheaf on `X₀` of arbitrary dimension
(`situation-weil`): the representation `ρ(u γⁿ) = ρ_geom(u) Φⁿ` of `W` on
the stalk `ℱ_t`, extending the geometric fundamental representation by the Frobenius `Φ` of the
Weil structure. -/
noncomputable def fundamentalRep (F : WeilSheaf K l X) (hF : F.IsLisse) :
    Representation (PadicAlgCl l) W (LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :=
  (Units.coeHom _).comp
    (D.degreeDatum.lift (D.geomUnits M F hF) (frobUnit M B F hF) (D.frobUnit_conj M F hF))

/-- On the geometric part, the Weil fundamental representation is the geometric fundamental
representation. -/
theorem fundamentalRep_geometric (F : WeilSheaf K l X) (hF : F.IsLisse) (u : D.deg.ker) :
    D.fundamentalRep M F hF u = M.rep B.t (F.toLisse hF) (D.geomEquiv.symm u) := by
  simp only [fundamentalRep, MonoidHom.comp_apply, Units.coeHom_apply]
  rw [Monodromy.DegreeDatum.lift_apply_of_mem_ker _ _ _ _ u.2]
  rfl

/-- On a loop `g` at `t`, the Weil fundamental representation is the monodromy of `g`. -/
theorem fundamentalRep_geomEquiv (F : WeilSheaf K l X) (hF : F.IsLisse) (g : Aut (fiber B.t)) :
    D.fundamentalRep M F hF (D.geomEquiv g) = M.rep B.t (F.toLisse hF) g := by
  rw [D.fundamentalRep_geometric M F hF, MulEquiv.symm_apply_apply]

/-- The Weil fundamental representation sends the lift of the Frobenius to `Φ`. -/
theorem fundamentalRep_frobLift (F : WeilSheaf K l X) (hF : F.IsLisse) :
    D.fundamentalRep M F hF D.frobLift = (frobStalk M B F hF).toLinearMap := by
  simp only [fundamentalRep, MonoidHom.comp_apply, Units.coeHom_apply]
  exact congrArg Units.val (Monodromy.DegreeDatum.lift_degreeOneElement (D := D.degreeDatum) _ _ _)

omit [Fact (ringChar K ≠ l)] in
/-- A linear map between two representations of `W` which intertwines them on `ker deg` and at
the lift of the Frobenius intertwines them everywhere: `W` is generated by `ker deg` and the lift
of the Frobenius. -/
theorem intertwines_of_geometric_frobLift {V V' : Type*} [AddCommGroup V]
    [Module (PadicAlgCl l) V] [AddCommGroup V'] [Module (PadicAlgCl l) V']
    (ρ : Representation (PadicAlgCl l) W V) (ρ' : Representation (PadicAlgCl l) W V')
    (S : V →ₗ[PadicAlgCl l] V') (hgeom : ∀ u ∈ D.deg.ker, ∀ v, S (ρ u v) = ρ' u (S v))
    (hfrob : ∀ v, S (ρ D.frobLift v) = ρ' D.frobLift (S v)) (w : W) (v : V) :
    S (ρ w v) = ρ' w (S v) := by
  let H : Subgroup W :=
    { carrier := {w | ∀ v, S (ρ w v) = ρ' w (S v)}
      mul_mem' := fun {a b} ha hb v ↦ by
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
        rw [ha, hb]
      one_mem' := fun v ↦ by simp
      inv_mem' := fun {a} ha v ↦ by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have h := ha (ρ a⁻¹ v)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h
        rw [h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] }
  have hw : w = (w * (D.degreeDatum.degreeOneElement ^ (D.degreeDatum.deg w).toAdd)⁻¹) *
      D.degreeDatum.degreeOneElement ^ (D.degreeDatum.deg w).toAdd := by group
  have : w ∈ H := by
    rw [hw]
    refine H.mul_mem (hgeom _ (D.degreeDatum.mul_inv_zpow_mem_ker w)) (H.zpow_mem ?_ _)
    exact hfrob
  exact this v

/-- Stalk maps intertwine the Weil fundamental representations. -/
theorem stalkMap_fundamentalRep {F G : WeilSheaf K l X} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) (w : W) (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    B.stalkMap φ hF hG (D.fundamentalRep M F hF w v) =
      D.fundamentalRep M G hG w (B.stalkMap φ hF hG v) := by
  refine D.intertwines_of_geometric_frobLift _ _ _ (fun u hu v ↦ ?_) (fun v ↦ ?_) w v
  · rw [D.fundamentalRep_geometric M F hF ⟨u, hu⟩, D.fundamentalRep_geometric M G hG ⟨u, hu⟩]
    exact stalkMap_rep M B φ hF hG _ v
  · rw [fundamentalRep_frobLift, fundamentalRep_frobLift]
    exact stalkMap_frobStalk M B φ hF hG v

/-- The Weil fundamental representation is continuous on the geometric part `π₁(X, t)`, as soon
as the geometric fundamental representation is continuous. -/
theorem continuous_fundamentalRep_geomEquiv (F : WeilSheaf K l X) (hF : F.IsLisse)
    (hM : M.IsEquivalenceAt B.t) (ψ : Module.Dual (PadicAlgCl l)
      (LisseMonodromy.StalkSpace B.t (F.toLisse hF))) (v) :
    Continuous fun g : Aut (fiber B.t) ↦ ψ (D.fundamentalRep M F hF (D.geomEquiv g) v) := by
  simp_rw [fundamentalRep_geomEquiv]
  exact hM.continuous_rep _ ψ v

/-- **Fullness of the Weil fundamental representation**: a linear map of stalks intertwining the
Weil fundamental representations is the stalk of a morphism of lisse Weil sheaves. -/
theorem exists_stalkMap_eq (hM : M.IsEquivalenceAt B.t) {F G : LisseWeilSheaf K l X}
    (φ : LisseMonodromy.StalkSpace B.t (F.obj.toLisse F.property) →ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (G.obj.toLisse G.property))
    (hφ : ∀ w v, φ (D.fundamentalRep M F.obj F.property w v) =
      D.fundamentalRep M G.obj G.property w (φ v)) :
    ∃ f : F ⟶ G, B.stalkMap f.hom F.property G.property = φ := by
  obtain ⟨f₀, hf₀⟩ := hM.full φ fun g v ↦ by
    have h := hφ (D.geomEquiv g) v
    rwa [fundamentalRep_geomEquiv, fundamentalRep_geomEquiv] at h
  have key := upperStar_comp_lisseFrobStr_of_frobStalk M B hM F.property G.property f₀ fun v ↦ by
    rw [hf₀]
    have h := hφ D.frobLift v
    rwa [fundamentalRep_frobLift, fundamentalRep_frobLift] at h
  have key' := congrArg (fun ψ ↦ ψ.hom) key
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    WeilSheaf.lisseFrobStr, Functor.FullyFaithful.preimageIso_hom, ObjectProperty.ι_obj,
    WeilSheaf.adicFrobStr, Iso.trans_hom, Iso.app_hom, Category.assoc] at key'
  have hstr : (WeilSheaf.frobeniusPullback K l X).map f₀.hom ≫ G.obj.obj.obj.str =
      F.obj.obj.obj.str ≫ f₀.hom := by
    rw [← cancel_epi ((adicUpperStarIsoLowerStarInv l
      (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).hom.app F.obj.obj.carrier),
      ← (adicUpperStarIsoLowerStarInv l _).hom.naturality_assoc]
    exact key'
  exact ⟨ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk ⟨f₀.hom, hstr⟩)), hf₀⟩

/-- **Essential surjectivity of the Weil fundamental representation**: every finite-dimensional
representation of `W` which is continuous on the geometric part `π₁(X, t)` is the Weil
fundamental representation of a lisse Weil sheaf (`definition-weil-representation--1`,
Frobenius descent). -/
theorem exists_fundamentalRep_linearEquiv (hM : M.IsEquivalenceAt B.t) (V : Type (u + 1))
    [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    (ρ : Representation (PadicAlgCl l) W V)
    (hρ : ∀ (φ : Module.Dual (PadicAlgCl l) V) (v : V),
      Continuous fun g : Aut (fiber B.t) ↦ φ (ρ (D.geomEquiv g) v)) :
    ∃ (F : LisseWeilSheaf K l X)
      (e : LisseMonodromy.StalkSpace B.t (F.obj.toLisse F.property) ≃ₗ[PadicAlgCl l] V),
      ∀ w v, e (D.fundamentalRep M F.obj F.property w v) = ρ w (e v) := by
  let ρg : Representation (PadicAlgCl l) (Aut (fiber B.t)) V :=
    ρ.comp (D.deg.ker.subtype.comp D.geomEquiv.toMonoidHom)
  obtain ⟨G₀, e, he⟩ := hM.essSurj V ρg hρ
  have he' (g : Aut (fiber B.t)) (x : V) : e.symm (ρg g x) = M.rep B.t G₀ g (e.symm x) := by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  let P := WeilCoefficients.linearEquivOfIso (frobPathStalkIso M B G₀)
  have hP (g : Aut (fiber B.t)) (v : LisseMonodromy.StalkSpace B.t G₀) :
      P (M.rep B.t G₀ (B.frobConj g) v) = M.rep B.t _ g (P v) := by
    have h := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
      (frobPathStalkIso_conj M B G₀ g)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  let Rγ := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom D.frobLift)
  have hRγ (x : V) : Rγ x = ρ D.frobLift x := rfl
  let φ : LisseMonodromy.StalkSpace B.t
      (G₀.upperStar l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t G₀ :=
    P.symm ≪≫ₗ e ≪≫ₗ Rγ ≪≫ₗ e.symm
  have hφP (w : LisseMonodromy.StalkSpace B.t G₀) : φ (P w) = e.symm (ρ D.frobLift (e w)) := by
    simp only [φ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hRγ]
  have hφ (g : Aut (fiber B.t)) (v) : φ (M.rep B.t _ g v) = M.rep B.t G₀ g (φ v) := by
    obtain ⟨w, rfl⟩ := P.surjective v
    have hc := D.geomEquiv_conj g
    rw [← hP, hφP, hφP, he, ← he']
    congr 1
    change ρ D.frobLift (ρ (D.geomEquiv (B.frobConj g) : W) (e w)) =
      ρ (D.geomEquiv g : W) (ρ D.frobLift (e w))
    rw [hc, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  obtain ⟨ψ, hψ⟩ := hM.full φ.toLinearMap hφ
  have : IsIso ψ := hM.isIso_of_bijective ψ (by rw [hψ]; exact φ.bijective)
  let str : (WeilSheaf.frobeniusPullback K l X).obj G₀.obj ≅ G₀.obj :=
    ((adicUpperStarIsoLowerStarInv l (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).app
      G₀.obj).symm ≪≫ (ObjectProperty.ι _).mapIso (asIso ψ)
  let F : WeilSheaf K l X :=
    ⟨Endofunctor.IsoAlgebra.mk G₀.obj str, G₀.property.isAdicConstructibleSheaf⟩
  have hF : F.IsLisse := G₀.property
  have hfrob (v : LisseMonodromy.StalkSpace B.t G₀) :
      frobStalk M B F hF v = e.symm (ρ D.frobLift (e v)) := by
    have hψF : (F.lisseFrobStr hF).hom = ψ := by
      apply ObjectProperty.hom_ext
      simp [F, str, WeilSheaf.lisseFrobStr, WeilSheaf.adicFrobStr, Endofunctor.IsoAlgebra.str,
        Endofunctor.IsoAlgebra.mk]
    rw [frobStalk_apply, ← hφP, hψF]
    exact LinearMap.congr_fun hψ (P v)
  refine ⟨⟨F, hF⟩, e, fun w v ↦ ?_⟩
  refine D.intertwines_of_geometric_frobLift _ _ e.toLinearMap (fun u hu v ↦ ?_) (fun v ↦ ?_) w v
  · change e (D.fundamentalRep M F hF u v) = ρ u (e v)
    rw [D.fundamentalRep_geometric M F hF ⟨u, hu⟩]
    refine (he _ v).trans ?_
    simp only [ρg, MonoidHom.comp_apply, Subgroup.subtype_apply]
    erw [MulEquiv.apply_symm_apply]
  · change e (D.fundamentalRep M F hF D.frobLift v) = ρ D.frobLift (e v)
    rw [fundamentalRep_frobLift]
    change e (frobStalk M B F hF v) = _
    rw [hfrob, LinearEquiv.apply_symm_apply]

end WeilData

section Irreducible

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) (B : FrobeniusBasePoint K X)

/-- The stalk at the base point of a zero lisse Weil sheaf is zero. -/
lemma subsingleton_stalk_of_isZero {F : WeilSheaf K l X} (hF : F.IsLisse) (h : IsZero F) :
    Subsingleton (LisseMonodromy.StalkSpace B.t (F.toLisse hF)) := by
  refine subsingleton_of_forall_eq 0 fun v ↦ ?_
  have h' := LinearMap.congr_fun (B.stalkMap_id hF) v
  rw [h.eq_of_src (𝟙 F) 0, stalkMap_zero] at h'
  exact h'.symm

/-- A lisse Weil sheaf whose stalk at the base point is zero is zero, if the monodromy at the
base point is an equivalence. -/
lemma isZero_of_subsingleton_stalk (hM : M.IsEquivalenceAt B.t) {F : WeilSheaf K l X}
    (hF : F.IsLisse) [Subsingleton (LisseMonodromy.StalkSpace B.t (F.toLisse hF))] :
    IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  have h := stalkMap_injective M B hM (F := ⟨F, hF⟩) (G := ⟨F, hF⟩) (𝟙 _)
    (ObjectProperty.homMk 0) (LinearMap.ext fun v ↦ by
      rw [Subsingleton.elim v 0, map_zero, map_zero])
  exact congrArg (fun f ↦ f.hom) h

/-- A morphism of lisse Weil sheaves whose stalk at the base point is injective is a
monomorphism of Weil sheaves, if the monodromy at the base point is an equivalence. -/
theorem mono_of_injective_stalkMap [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (hM : M.IsEquivalenceAt B.t) {F G : WeilSheaf K l X}
    (hF : F.IsLisse) (hG : G.IsLisse) (φ : F ⟶ G)
    (hφ : Function.Injective (B.stalkMap φ hF hG)) : Mono φ := by
  have hK := (WeilSheaf.IsLisse.kernel_cokernel hF hG φ).1
  refine Preadditive.mono_of_kernel_zero ?_
  have h := stalkMap_injective M B hM (F := ⟨kernel φ, hK⟩) (G := ⟨F, hF⟩)
    (ObjectProperty.homMk (kernel.ι φ)) (ObjectProperty.homMk 0) (LinearMap.ext fun v ↦ by
      apply hφ
      have h₁ := LinearMap.congr_fun (B.stalkMap_comp (kernel.ι φ) φ hK hF hG) v
      rw [kernel.condition, stalkMap_zero] at h₁
      simp only [ObjectProperty.homMk_hom, stalkMap_zero, LinearMap.zero_apply, map_zero]
      exact h₁.symm)
  exact congrArg (fun f ↦ f.hom) h

namespace WeilData

variable {B} {W : Type*} [Group W] (D : B.WeilData W)

/-- The embedding `π₁(X, t) ≅ ker deg ⊆ W` of the geometric fundamental group. -/
noncomputable def geomHom : Aut (fiber B.t) →* W :=
  D.deg.ker.subtype.comp D.geomEquiv.toMonoidHom

lemma geomHom_apply (g : Aut (fiber B.t)) : D.geomHom g = D.geomEquiv g :=
  rfl

/-- The Weil fundamental representation is continuous along `π₁(X, t) → W`. -/
theorem fundamentalRep_isContinuousOn (F : WeilSheaf K l X) (hF : F.IsLisse)
    (hM : M.IsEquivalenceAt B.t) : (D.fundamentalRep M F hF).IsContinuousOn D.geomHom :=
  D.continuous_fundamentalRep_geomEquiv M F hF hM

/-- **The Weil fundamental representation of an irreducible lisse Weil sheaf is irreducible**
(cf. Deligne, Weil II, 1.3.14), on a scheme `X₀` of arbitrary dimension. -/
theorem isIrreducible_fundamentalRep [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (hM : M.IsEquivalenceAt B.t) {F : WeilSheaf K l X}
    (hF : F.IsIrreducibleLisse) : (D.fundamentalRep M F hF.1).IsIrreducible := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  refine Representation.isIrreducible_iff.2 ⟨?_, fun U hU ↦ ?_⟩
  · rw [← not_subsingleton_iff_nontrivial]
    intro h
    exact hF.2.1 (isZero_of_subsingleton_stalk M B hM hF.1)
  let U' : Subrepresentation (D.fundamentalRep M F hF.1) := ⟨U, fun g v hv ↦ hU g v hv⟩
  obtain ⟨Y, e, he⟩ := D.exists_fundamentalRep_linearEquiv M hM U U'.toRepresentation
    ((D.fundamentalRep_isContinuousOn M F hF.1 hM).subrepresentation U')
  obtain ⟨f, hf⟩ := D.exists_stalkMap_eq M hM (G := ⟨F, hF.1⟩) (U.subtype ∘ₗ e.toLinearMap)
    fun w v ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he]
      rfl
  have hinj : Function.Injective (B.stalkMap f.hom Y.property hF.1) := by
    rw [hf]
    exact U.injective_subtype.comp e.injective
  have := mono_of_injective_stalkMap M B hM Y.property hF.1 f.hom hinj
  rcases hF.2.2 Y.obj f.hom this Y.property with h | h
  · left
    have := subsingleton_stalk_of_isZero B Y.property h
    rw [eq_bot_iff]
    intro v hv
    have h₀ : (⟨v, hv⟩ : U) = 0 := by
      rw [← e.apply_symm_apply ⟨v, hv⟩, Subsingleton.elim (e.symm ⟨v, hv⟩) 0, map_zero]
    simpa using congrArg Subtype.val h₀
  · right
    rw [eq_top_iff]
    intro v _
    have h₁ := LinearMap.congr_fun (B.stalkMap_comp (inv f.hom) f.hom hF.1 Y.property hF.1) v
    rw [IsIso.inv_hom_id, stalkMap_id, hf, LinearMap.id_apply] at h₁
    rw [h₁]
    exact Submodule.coe_mem _

/-- Conversely, a lisse Weil sheaf whose Weil fundamental representation is irreducible is
irreducible lisse. -/
theorem isIrreducibleLisse_of_isIrreducible_fundamentalRep
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l X} (hF : F.IsLisse) (h : (D.fundamentalRep M F hF).IsIrreducible) :
    F.IsIrreducibleLisse := by
  obtain ⟨hnt, hirr⟩ := Representation.isIrreducible_iff.1 h
  refine ⟨hF, fun hz ↦ ?_, fun G i hi hG ↦ ?_⟩
  · have := subsingleton_stalk_of_isZero B hF hz
    exact not_subsingleton _ this
  rcases hirr (LinearMap.range (B.stalkMap i hG hF)) (fun g v hv ↦ by
      obtain ⟨u, rfl⟩ := hv
      exact ⟨_, D.stalkMap_fundamentalRep M i hG hF g u⟩) with h₀ | h₀
  · left
    obtain rfl : i = 0 := congrArg (fun f ↦ f.hom) (stalkMap_injective M B hM (F := ⟨G, hG⟩)
      (G := ⟨F, hF⟩) (ObjectProperty.homMk i) (ObjectProperty.homMk 0)
      ((LinearMap.range_eq_bot.1 h₀).trans (B.stalkMap_zero hG hF).symm))
    exact IsZero.of_mono_zero G F
  · right
    have hQ := (WeilSheaf.IsLisse.kernel_cokernel hG hF i).2
    have hπ : cokernel.π i = 0 := congrArg (fun f ↦ f.hom) (stalkMap_injective M B hM
      (F := ⟨F, hF⟩) (G := ⟨cokernel i, hQ⟩) (ObjectProperty.homMk (cokernel.π i))
      (ObjectProperty.homMk 0) (LinearMap.ext fun v ↦ by
        obtain ⟨u, rfl⟩ := LinearMap.range_eq_top.1 h₀ v
        have h₁ := LinearMap.congr_fun (B.stalkMap_comp i (cokernel.π i) hG hF hQ) u
        rw [cokernel.condition, stalkMap_zero] at h₁
        simp only [ObjectProperty.homMk_hom, stalkMap_zero, LinearMap.zero_apply]
        exact h₁.symm))
    have : Epi i := Preadditive.epi_of_cokernel_zero hπ
    exact isIso_of_mono_of_epi i

/-- A lisse Weil sheaf on `X₀` is irreducible lisse if and only if its Weil fundamental
representation is irreducible. -/
theorem isIrreducibleLisse_iff_isIrreducible_fundamentalRep
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l X} (hF : F.IsLisse) :
    F.IsIrreducibleLisse ↔ (D.fundamentalRep M F hF).IsIrreducible :=
  ⟨fun h ↦ D.isIrreducible_fundamentalRep M hM h,
    D.isIrreducibleLisse_of_isIrreducible_fundamentalRep M hM hF⟩

end WeilData

end Irreducible

section Twist

namespace WeilData

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)] [LocallyOfFiniteType (X ↘ Spec (.of K))]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) {B : FrobeniusBasePoint K X}
  {W : Type*} [Group W] (D : B.WeilData W)

open Representation

omit [LocallyOfFiniteType (X ↘ Spec (.of K))] in
/-- The Weil fundamental representation is bounded on the geometric part `ker deg ≅ π₁(X, t)`:
the geometric fundamental group is compact and acts continuously. -/
theorem isBoundedOn_fundamentalRep_geometric (hM : M.IsEquivalenceAt B.t) (F : WeilSheaf K l X)
    (hF : F.IsLisse) : (D.fundamentalRep M F hF).IsBoundedOn D.deg.ker := by
  intro v φ
  obtain ⟨C, hC⟩ := (isCompact_range (hM.continuous_rep (F.toLisse hF) φ v)
    ).exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨C, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hC _ ⟨D.geomEquiv.symm ⟨w, hw⟩,
    congrArg (fun T ↦ φ (T v)) (D.fundamentalRep_geometric M F hF ⟨w, hw⟩).symm⟩

/-- **Deligne, Weil II, 1.3.14**, for the Weil fundamental representation on a scheme `X₀` of
arbitrary dimension: if `ℱ` is an irreducible lisse Weil sheaf, there is `b ∈ ℚ̄_ℓˣ` such that
the twist `ρ_ℱ ⊗ b^{-deg}` of its Weil fundamental representation is bounded on the whole Weil
group. -/
theorem exists_isBoundedOn_twist_fundamentalRep (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l X} (hF : F.IsIrreducibleLisse) :
    ∃ b : (PadicAlgCl l)ˣ,
      ((D.fundamentalRep M F hF.1).twist (degreeCharacter D.deg b⁻¹)).IsBoundedOn Set.univ := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  have := D.isIrreducible_fundamentalRep M hM hF
  exact exists_isBoundedOn_twist _ D.deg_surjective
    (D.isBoundedOn_fundamentalRep_geometric M hM F hF.1)

/-- **Finite geometric monodromy** (cf. Deligne, Weil II, 1.3.14) in arbitrary dimension: if the
geometric monodromy group of an irreducible lisse Weil sheaf `ℱ` is finite, then a twist
`ρ_ℱ ⊗ b^{-deg}` of its Weil fundamental representation has finite image. -/
theorem exists_finite_range_twist_fundamentalRep (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l X} (hF : F.IsIrreducibleLisse)
    (hfin : (D.fundamentalRep M F hF.1 '' D.deg.ker).Finite) :
    ∃ b : (PadicAlgCl l)ˣ,
      (Set.range ((D.fundamentalRep M F hF.1).twist (degreeCharacter D.deg b⁻¹))).Finite := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  have := D.isIrreducible_fundamentalRep M hM hF
  exact exists_finite_range_twist _ D.deg_surjective hfin

/-- **Trivial geometric monodromy** in arbitrary dimension: if the geometric fundamental group
acts trivially on the stalk of an irreducible lisse Weil sheaf `ℱ`, then `ℱ` has rank one and its
Weil fundamental representation is a character `b ^ deg`. -/
theorem finrank_eq_one_and_exists_twist_eq_one_fundamentalRep (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l X} (hF : F.IsIrreducibleLisse)
    (htriv : ∀ g, M.rep B.t (F.toLisse hF.1) g = 1) :
    Module.finrank (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) = 1 ∧
      ∃ b : (PadicAlgCl l)ˣ,
        ∀ w, (D.fundamentalRep M F hF.1).twist (degreeCharacter D.deg b⁻¹) w = 1 := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  have := D.isIrreducible_fundamentalRep M hM hF
  refine finrank_eq_one_and_exists_twist_eq_one _ D.deg_surjective fun i hi ↦ ?_
  rw [D.fundamentalRep_geometric M F hF.1 ⟨i, hi⟩]
  exact htriv _

/-- **Deligne, Weil II, 1.3.14**, sheaf-theoretic form in arbitrary dimension: an irreducible
lisse Weil sheaf `ℱ` on `X₀` is the twist of an irreducible lisse Weil sheaf `ℱ'` with bounded
monodromy. Precisely, there are `b ∈ ℚ̄_ℓˣ`, a lisse Weil sheaf `ℱ'` whose Weil fundamental
representation is bounded on the whole Weil group, and an identification `ℱ'_t ≅ ℱ_t` of stalks
carrying the Weil fundamental representation of `ℱ'` to the twist `ρ_ℱ ⊗ b^{-deg}`; moreover
`ℱ'` is again irreducible lisse. -/
theorem exists_isBoundedOn_fundamentalRep_twist (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l X} (hF : F.IsIrreducibleLisse) :
    ∃ (b : (PadicAlgCl l)ˣ) (Y : LisseWeilSheaf K l X)
      (e : LisseMonodromy.StalkSpace B.t (Y.obj.toLisse Y.property) ≃ₗ[PadicAlgCl l]
        LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)),
      (∀ w v, e (D.fundamentalRep M Y.obj Y.property w v) =
        (D.fundamentalRep M F hF.1).twist (degreeCharacter D.deg b⁻¹) w (e v)) ∧
      Y.obj.IsIrreducibleLisse ∧ (D.fundamentalRep M Y.obj Y.property).IsBoundedOn Set.univ := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  obtain ⟨b, hb⟩ := D.exists_isBoundedOn_twist_fundamentalRep M hM hF
  set σ := (D.fundamentalRep M F hF.1).twist (degreeCharacter D.deg b⁻¹)
  have hσ : σ.IsContinuousOn D.geomHom := by
    intro φ v
    have h (g : Aut (fiber B.t)) : φ (σ (D.geomHom g) v) =
        φ (D.fundamentalRep M F hF.1 (D.geomHom g) v) := by
      simp [σ, geomHom_apply, MonoidHom.mem_ker.1 (D.geomEquiv g).2]
    simp_rw [h]
    exact D.fundamentalRep_isContinuousOn M F hF.1 hM φ v
  obtain ⟨Y, e, he⟩ := D.exists_fundamentalRep_linearEquiv M hM _ σ hσ
  have := D.isIrreducible_fundamentalRep M hM hF
  have : σ.IsIrreducible := IsIrreducible.twist _
  refine ⟨b, Y, e, he, D.isIrreducibleLisse_of_isIrreducible_fundamentalRep M hM Y.property
    (IsIrreducible.of_linearEquiv e he), fun v φ ↦ ?_⟩
  obtain ⟨c, hc⟩ := hb (e v) (φ ∘ₗ e.symm.toLinearMap)
  refine ⟨c, ?_⟩
  rintro _ ⟨w, -, rfl⟩
  have h := hc _ ⟨w, Set.mem_univ _, rfl⟩
  beta_reduce at h
  rwa [LinearMap.comp_apply, ← he, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h

end WeilData

end Twist

section Equivalence

namespace WeilData

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) {B : FrobeniusBasePoint K X}
  {W : Type u} [Group W] (D : B.WeilData W)

/-- The finite-dimensional representations of `W` which are continuous on the geometric part
`π₁(X, t) → W`. -/
def isContinuousRep : ObjectProperty (Rep.{u} (PadicAlgCl l) W) :=
  fun V ↦ FiniteDimensional (PadicAlgCl l) V.V ∧ V.ρ.IsContinuousOn D.geomHom

/-- **The lisse sheaf–representation equivalence** on a scheme `X₀` of arbitrary dimension
(`definition-weil-representation--1`): if the monodromy at `t` is an equivalence,
the Weil fundamental representation is an equivalence between lisse Weil sheaves on `X₀` and
finite-dimensional representations of `W` continuous on `π₁(X, t)`, under which every lisse Weil
sheaf goes to a representation isomorphic to its Weil fundamental representation. -/
theorem exists_equivalence_fundamentalRep (hM : M.IsEquivalenceAt B.t) :
    ∃ e : LisseWeilSheaf K l X ≌ (D.isContinuousRep (l := l)).FullSubcategory,
      ∀ F : LisseWeilSheaf K l X, ∃ f : (e.functor.obj F).obj.V ≃ₗ[PadicAlgCl l]
          LisseMonodromy.StalkSpace B.t (F.obj.toLisse F.property),
        ∀ g v, f ((e.functor.obj F).obj.ρ g v) =
          D.fundamentalRep M F.obj F.property g (f v) := by
  have (F : LisseWeilSheaf K l X) : FiniteDimensional (PadicAlgCl l)
      (LisseMonodromy.StalkSpace B.t (F.obj.toLisse F.property)) :=
    F.obj.finiteDimensional_stalkObj B.t
  refine Representation.exists_equivalence_of_realization D.geomHom
    (fun F : LisseWeilSheaf K l X ↦ LisseMonodromy.StalkSpace B.t (F.obj.toLisse F.property))
    (fun F ↦ D.fundamentalRep M F.obj F.property)
    (fun F ↦ D.fundamentalRep_isContinuousOn M F.obj F.property hM)
    (fun {F G : LisseWeilSheaf K l X} (f : F ⟶ G) ↦ B.stalkMap f.hom F.property G.property)
    (fun F ↦ B.stalkMap_id F.property) (fun f g ↦ B.stalkMap_comp f.hom g.hom _ _ _)
    (fun {F G : LisseWeilSheaf K l X} (f : F ⟶ G) w v ↦ D.stalkMap_fundamentalRep M f.hom _ _ w v)
    (fun f f' h ↦ stalkMap_injective M B hM f f' h)
    (fun φ hφ ↦ D.exists_stalkMap_eq M hM φ hφ)
    (fun V _ _ _ ρ hρ ↦ D.exists_fundamentalRep_linearEquiv M hM V ρ hρ) _ fun _ ↦ Iff.rfl

end WeilData

end Equivalence

section Comparison

namespace WeilData

variable {B : FrobeniusBasePoint K X} {W : Type*} [Group W] (D : B.WeilData W)

/-- The Frobenius transport of loops is conjugation by the inverse of the lift of the
Frobenius. -/
lemma geomHom_frobConj (x : Aut (fiber B.t)) :
    D.geomHom (B.frobConj x) = D.frobLift⁻¹ * D.geomHom x * D.frobLift :=
  D.geomEquiv_conj x

/-- The inverse of the Frobenius transport of loops is conjugation by the lift of the
Frobenius. -/
lemma geomHom_frobConj_symm (x : Aut (fiber B.t)) :
    D.geomHom (B.frobConj.symm x) = D.frobLift * D.geomHom x * D.frobLift⁻¹ := by
  have h := D.geomHom_frobConj (B.frobConj.symm x)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

/-- The action of `n ∈ ℤ` on `π₁(X, t)` defining `π₁(X, t) ⋊ ℤ` is conjugation by `γⁿ`. -/
lemma geomHom_frobAction (n : ℤ) (x : Aut (fiber B.t)) :
    D.geomHom (B.frobAction (Multiplicative.ofAdd n) x) =
      D.frobLift ^ n * D.geomHom x * (D.frobLift ^ n)⁻¹ := by
  simp only [frobAction, zpowersHom_apply, toAdd_ofAdd]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, MulAut.mul_apply, ih, MulAut.inv_apply, geomHom_frobConj_symm]
    group
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply, ih, inv_inv, geomHom_frobConj]
    group

/-- The comparison homomorphism `π₁(X, t) ⋊ ℤ → W`, `(g, n) ↦ θ(g) γⁿ`. -/
noncomputable def toWeilGroupHom : B.WeilGroup →* W :=
  SemidirectProduct.lift D.geomHom (zpowersHom W D.frobLift) fun g ↦ by
    ext x
    have h := D.geomHom_frobAction (Multiplicative.toAdd g) x
    rw [ofAdd_toAdd] at h
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      zpowersHom_apply]
    exact h

@[simp]
lemma toWeilGroupHom_inl (g : Aut (fiber B.t)) :
    D.toWeilGroupHom (SemidirectProduct.inl g) = D.geomHom g :=
  SemidirectProduct.lift_inl _ _ _ g

@[simp]
lemma toWeilGroupHom_inr (n : Multiplicative ℤ) :
    D.toWeilGroupHom (SemidirectProduct.inr n) = D.frobLift ^ n.toAdd :=
  SemidirectProduct.lift_inr _ _ _ n

/-- The comparison homomorphism preserves degrees. -/
lemma deg_comp_toWeilGroupHom : D.deg.comp D.toWeilGroupHom = B.weilData.deg := by
  refine SemidirectProduct.hom_ext (MonoidHom.ext fun g ↦ ?_) (MonoidHom.ext fun n ↦ ?_)
  · simp only [MonoidHom.comp_apply, toWeilGroupHom_inl, geomHom_apply]
    exact (D.geomEquiv g).2.trans (SemidirectProduct.rightHom_inl g).symm
  · simp only [MonoidHom.comp_apply, toWeilGroupHom_inr, map_zpow, D.deg_frobLift]
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
    exact (SemidirectProduct.rightHom_inr n).symm

/-- **Uniqueness of the Weil group**: any Weil data `(W, deg, θ, γ)` is canonically isomorphic
to the semidirect product `π₁(X, t) ⋊ ℤ`, by `(g, n) ↦ θ(g) γⁿ`. -/
lemma bijective_toWeilGroupHom : Function.Bijective D.toWeilGroupHom := by
  refine ⟨(injective_iff_map_eq_one _).2 fun x hx ↦ ?_, fun w ↦ ?_⟩
  · have hdeg := congrArg D.deg hx
    rw [← MonoidHom.comp_apply, deg_comp_toWeilGroupHom, map_one] at hdeg
    rw [← SemidirectProduct.inl_left_mul_inr_right x] at hx ⊢
    replace hdeg : x.right = 1 := hdeg
    rw [hdeg, map_one, mul_one] at hx ⊢
    rw [toWeilGroupHom_inl, geomHom_apply, OneMemClass.coe_eq_one,
      MulEquiv.map_eq_one_iff] at hx
    rw [hx, map_one]
  · refine ⟨SemidirectProduct.inl (D.geomEquiv.symm
      ⟨_, D.degreeDatum.mul_inv_zpow_mem_ker w⟩) * SemidirectProduct.inr (D.deg w), ?_⟩
    rw [map_mul, toWeilGroupHom_inl, toWeilGroupHom_inr, geomHom_apply,
      MulEquiv.apply_symm_apply]
    simp [degreeDatum]

/-- The isomorphism `π₁(X, t) ⋊ ℤ ≅ W` attached to Weil data on `W`. -/
noncomputable def weilGroupEquiv : B.WeilGroup ≃* W :=
  MulEquiv.ofBijective D.toWeilGroupHom D.bijective_toWeilGroupHom

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K)

/-- The Weil fundamental representation of `W` restricts, along `π₁(X, t) ⋊ ℤ ≅ W`, to the Weil
fundamental representation of the canonical Weil group: all Weil data give the same theory. -/
theorem fundamentalRep_toWeilGroupHom (F : WeilSheaf K l X) (hF : F.IsLisse)
    (w : B.WeilGroup) :
    D.fundamentalRep M F hF (D.toWeilGroupHom w) = B.weilData.fundamentalRep M F hF w := by
  refine LinearMap.ext fun v ↦ (B.weilData.intertwines_of_geometric_frobLift
    (B.weilData.fundamentalRep M F hF) ((D.fundamentalRep M F hF).comp D.toWeilGroupHom)
    LinearMap.id (fun u hu v ↦ ?_) (fun v ↦ ?_) w v).symm
  · obtain ⟨g, hg⟩ := B.weilData.geomEquiv.surjective ⟨u, hu⟩
    obtain rfl : u = SemidirectProduct.inl g := (congrArg Subtype.val hg).symm
    rw [LinearMap.id_apply, LinearMap.id_apply, MonoidHom.comp_apply, toWeilGroupHom_inl,
      geomHom_apply, fundamentalRep_geomEquiv]
    exact congrArg (fun T ↦ T v) (B.weilData.fundamentalRep_geomEquiv M F hF g)
  · rw [LinearMap.id_apply, LinearMap.id_apply, MonoidHom.comp_apply, fundamentalRep_frobLift]
    have : D.toWeilGroupHom B.weilData.frobLift = D.frobLift :=
      (D.toWeilGroupHom_inr _).trans (by simp)
    rw [this, fundamentalRep_frobLift]

end WeilData

end Comparison

section Canonical

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

open Representation

/-- **Deligne, Weil II, 1.3.14** for the canonical Weil group `π₁(X, t) ⋊ ℤ` of a scheme `X₀`
of finite type over `K` of arbitrary dimension: for an irreducible lisse Weil sheaf `ℱ` some
twist `ρ_ℱ ⊗ b^{-deg}` of its Weil fundamental representation is bounded on the whole Weil
group. -/
theorem exists_isBoundedOn_twist_fundamentalRep [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) (B : FrobeniusBasePoint K X)
    (hM : M.IsEquivalenceAt B.t) {F : WeilSheaf K l X} (hF : F.IsIrreducibleLisse) :
    ∃ b : (PadicAlgCl l)ˣ, ((B.weilData.fundamentalRep M F hF.1).twist
      (degreeCharacter B.weilData.deg b⁻¹)).IsBoundedOn Set.univ :=
  B.weilData.exists_isBoundedOn_twist_fundamentalRep M hM hF

/-- **Deligne, Weil II, 1.3.14** in arbitrary dimension, without monodromy hypotheses: let `X₀`
be of finite type over `K` with connected, regular geometric fibre `X` (Noetherian and
quasi-compact), and `t` a geometric point of `X`. Then there are a monodromy `M` of lisse sheaves
on `X` which is an equivalence at `t` and base point data `B` at `t` such that for every
irreducible lisse Weil sheaf `ℱ` on `X₀` some twist `ρ_ℱ ⊗ b^{-deg}` of its Weil fundamental
representation of `π₁(X, t) ⋊ ℤ` is bounded. -/
theorem exists_lisseMonodromy_isBoundedOn_twist_fundamentalRep
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [IsLocallyNoetherian (X ↘ Spec (.of K)).geometricFiber]
    [CompactSpace (X ↘ Spec (.of K)).geometricFiber] [IsRegular (X ↘ Spec (.of K)).geometricFiber]
    [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber]
    (t : Spec (.of (AlgebraicClosure K)) ⟶ (X ↘ Spec (.of K)).geometricFiber) :
    ∃ (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) (B : FrobeniusBasePoint K X),
      B.t = t ∧ M.IsEquivalenceAt B.t ∧ ∀ (F : WeilSheaf K l X) (hF : F.IsIrreducibleLisse),
        ∃ b : (PadicAlgCl l)ˣ, ((B.weilData.fundamentalRep M F hF.1).twist
          (degreeCharacter B.weilData.deg b⁻¹)).IsBoundedOn Set.univ := by
  obtain ⟨M, hM⟩ := ProEtale.exists_lisseMonodromy (l := l)
    (Y := (X ↘ Spec (.of K)).geometricFiber) (Ω := K)
  let B : FrobeniusBasePoint K X := ⟨t, (PreGaloisCategory.nonempty_iso_of_fiberFunctor _ _).some⟩
  exact ⟨M, B, rfl, hM B.t, fun F hF ↦ exists_isBoundedOn_twist_fundamentalRep M B (hM B.t) hF⟩

/-- **Deligne, Weil II, 1.3.14** for smooth geometrically connected `X₀` of finite type over
`K` of arbitrary dimension: the geometric fibre is then connected, regular, Noetherian and
quasi-compact, so `exists_lisseMonodromy_isBoundedOn_twist_fundamentalRep` applies. -/
theorem exists_lisseMonodromy_isBoundedOn_twist_fundamentalRep_of_smooth
    [Smooth (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [GeometricallyConnected (X ↘ Spec (.of K))]
    (t : Spec (.of (AlgebraicClosure K)) ⟶ (X ↘ Spec (.of K)).geometricFiber) :
    ∃ (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) (B : FrobeniusBasePoint K X),
      B.t = t ∧ M.IsEquivalenceAt B.t ∧ ∀ (F : WeilSheaf K l X) (hF : F.IsIrreducibleLisse),
        ∃ b : (PadicAlgCl l)ˣ, ((B.weilData.fundamentalRep M F hF.1).twist
          (degreeCharacter B.weilData.deg b⁻¹)).IsBoundedOn Set.univ := by
  have : ConnectedSpace (X ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := X ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (X ↘ Spec (.of K)).geometricFiberProj
      (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  exact exists_lisseMonodromy_isBoundedOn_twist_fundamentalRep t

end Canonical

end FrobeniusBasePoint

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}

/-- The base point data of a curve, as base point data in the sense of arbitrary dimension. -/
def BasePointData.toFrobeniusBasePoint (B : BasePointData W) : FrobeniusBasePoint K C :=
  ⟨B.t, B.frobPath⟩

/-- The homotopy exact sequence data of a curve, as Weil data in the sense of arbitrary
dimension for the Weil group of the curve. -/
def WeilMonodromyData.toWeilData {B : BasePointData W} (D : WeilMonodromyData B) :
    B.toFrobeniusBasePoint.WeilData W.carrier where
  deg := W.deg
  deg_surjective := W.deg_surjective
  geomEquiv := D.geomEquiv.toMulEquiv
  frobLift := D.frobLift
  deg_frobLift := D.deg_frobLift
  geomEquiv_conj g := D.geomEquiv_conj g

/-- For curves, the Weil fundamental representation in the sense of arbitrary dimension is the
Weil fundamental representation of `AlgebraicGeometry.WeilGroup.fundamentalRep`. -/
theorem WeilMonodromyData.fundamentalRep_toWeilData {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
    (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K) {B : BasePointData W}
    (D : WeilMonodromyData B) (F : WeilSheaf K l C) (hF : F.IsLisse) :
    D.toWeilData.fundamentalRep M F hF = fundamentalRep M D F hF :=
  rfl

end WeilGroup

end AlgebraicGeometry
