/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.RepresentationTheory.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.SixFunctors.ProEtale.Adic.StalkEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# The monodromy of lisse `ℓ`-adic sheaves

Let `Y` be a connected scheme, `Ω` a field with algebraic closure `Ω̄` and
`ℚ̄_ℓ = PadicAlgCl ℓ`. For a geometric point `y : Spec Ω̄ ⟶ Y` write `F_y` both for the
fibre functor on finite étale `Y`-schemes and for the stalk functor `G ↦ Γ(Spec Ω̄, y^* G)`
on lisse `ℓ`-adic sheaves on `Y_proét`. By `proposition-lattices-representations-normal-scheme` (for
`Λ = ℚ̄_ℓ`), the stalk functor at a geometric point `t` identifies lisse `ℚ̄_ℓ`-sheaves with the
continuous finite-dimensional `ℚ̄_ℓ`-representations of `π₁(Y, t) = Aut F_t`, as an exact tensor
equivalence compatible with base change; and `situation-weil` transports
stalks along paths, i.e. isomorphisms of fibre functors `F_y ≅ F_z`.

This file packages these facts as a *monodromy* of lisse sheaves
(`AlgebraicGeometry.ProEtale.LisseMonodromy`): for every path `τ : F_y ≅ F_z` a natural
isomorphism `mono τ` from the stalk functor at `y` to the stalk functor at `z`, such that

* `mono` is functorial in the path (`mono_refl`, `mono_trans`);
* reparametrising a geometric point by an automorphism `a` of `Spec Ω̄` is transported by the
  canonical identification `Γ(Spec Ω̄, (a ≫ y)^* G) ≅ Γ(Spec Ω̄, a^* y^* G) ≅ Γ(Spec Ω̄, y^* G)`
  (`mono_reparam`);
* it is compatible with pullback along an endomorphism `f` of `Y`: the path `F_{y ≫ f} ≅ F_{z ≫ f}`
  induced by `τ` acts on `Γ(Spec Ω̄, (y ≫ f)^* G) = Γ(Spec Ω̄, y^* f^* G)` as `τ` acts on the
  stalks of `f^* G` (`mono_upperStar`, the compatibility of
  `proposition-lattices-representations-normal-scheme` with base change);
* global sections restrict to flat sections (`mono_globalSections`);
* it preserves the evaluation pairing `[G, H]_y × G_y → H_y` of internal homs of lisse sheaves
  (`mono_evaluationPairing`, the tensor compatibility of
  `proposition-lattices-representations-normal-scheme` applied to `[G, H] ⊗ G → H`; for `H = ℚ̄_ℓ`
  this is the pairing of the dual).

At a base point `t`, the automorphisms of `F_t` act on the stalk `G_t`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.rep`), and
`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt` records that this is a fully
faithful and essentially surjective functor to continuous finite-dimensional representations.

The existence of a monodromy which is an equivalence at every base point, for a connected
regular Noetherian `Y`, is `AlgebraicGeometry.ProEtale.exists_lisseMonodromy`
(`WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme.FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (Ω : Type u) [Field Ω]

/-- The category of lisse `ℓ`-adic sheaves on `Y_proét`. -/
abbrev LisseSheaf : Type (u + 2) :=
  (adicLisseSheaf l Y).FullSubcategory

variable {Y Ω}

/-- The stalk functor `G ↦ Γ(Spec Ω̄, y^* G)` at a geometric point `y`, on lisse sheaves. -/
noncomputable abbrev lisseStalk (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    LisseSheaf l Y ⥤ WeilCoefficients.{u} l :=
  ObjectProperty.ι _ ⋙ AdicSheaf.forget Y ⋙ stalkFunctor l y

/-- The identification `Γ(Spec Ω̄, (a ≫ y)^* G) ≅ Γ(Spec Ω̄, a^* y^* G) ≅ Γ(Spec Ω̄, y^* G)` of the
stalks at a geometric point `y` and at its reparametrisation by an automorphism `a` of
`Spec Ω̄`. -/
noncomputable def reparamStalkIso
    (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (G : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (stalkFunctor l (a.hom ≫ y)).obj G ≅ (stalkFunctor l y).obj G :=
  (Sheaf.Γ _ _).mapIso ((upperStarComp _ a.hom y).app G) ≪≫
    (globalSectionsUpperStarIso _ a).app _

/-- The identification `Γ(Spec Ω̄, (y ≫ f)^* G) ≅ Γ(Spec Ω̄, y^* f^* G)` of the stalk of `G` at
`y ≫ f` with the stalk of `f^* G` at `y`. -/
noncomputable def upperStarStalkIso {X : Scheme.{u}} (f : X ⟶ Y)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ X)
    (G : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (stalkFunctor l (y ≫ f)).obj G ≅ (stalkFunctor l y).obj ((f)^*[_].obj G) :=
  (Sheaf.Γ _ _).mapIso ((upperStarComp _ y f).app G)

/-- The identification `Γ(Spec Ω̄, (y ≫ f)^* G) ≅ Γ(Spec Ω̄, y^* f^* G)` is natural in `G`. -/
lemma upperStarStalkIso_hom_naturality {X : Scheme.{u}} (f : X ⟶ Y)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ X)
    {G H : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)} (φ : G ⟶ H) :
    (stalkFunctor l (y ≫ f)).map φ ≫ (upperStarStalkIso l f y H).hom =
      (upperStarStalkIso l f y G).hom ≫ (stalkFunctor l y).map ((f)^*[_].map φ) := by
  simp only [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map,
    ← Functor.map_comp, (upperStarComp _ y f).hom.naturality]

/-- The pullback of a lisse sheaf, as a lisse sheaf. -/
noncomputable abbrev LisseSheaf.upperStar {X : Scheme.{u}} (f : X ⟶ Y) (G : LisseSheaf l Y) :
    LisseSheaf l X :=
  ⟨(f)^*ᵃ[l].obj G.obj, G.property.upperStar f⟩

/-- The constant sheaf `ℚ̄_ℓ`, as a lisse sheaf. -/
noncomputable abbrev LisseSheaf.unit : LisseSheaf l Y :=
  ⟨AdicSheaf.unit l Y, isAdicLisseSheaf_adicConstantSheaf Y⟩

variable (Y Ω)

/-- **The monodromy of lisse sheaves** on `Y`: the transport of stalks of lisse `ℓ`-adic sheaves
along paths between geometric points with values in `Ω̄`, in the sense of
`situation-weil` ("the usual transport of the stalk"), with the
compatibilities of `proposition-lattices-representations-normal-scheme` (functoriality, base change,
tensor products), see the module docstring. -/
structure LisseMonodromy where
  /-- The transport `F_y ≅ F_z` of stalks of lisse sheaves along a path `τ : F_y ≅ F_z`. -/
  mono {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z) :
    lisseStalk l y ≅ lisseStalk l z
  /-- Transport along the trivial path is the identity. -/
  mono_refl (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : mono (Iso.refl (fiber y)) = Iso.refl _
  /-- Transport along a composite path is the composite of the transports. -/
  mono_trans {y z w : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) :
    mono (τ ≪≫ τ') = mono τ ≪≫ mono τ'
  /-- The reparametrisation path acts by the canonical identification of the stalks. -/
  mono_reparam (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :
    (mono (fiberReparamIso a y)).hom.app G = (reparamStalkIso l a y G.obj.X).hom
  /-- Compatibility with pullback along an endomorphism `f` of `Y`. -/
  mono_upperStar (f : Y ⟶ Y) {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (G : LisseSheaf l Y) :
    (mono (pullbackPathIso f τ)).hom.app G ≫ (upperStarStalkIso l f z G.obj.X).hom =
      (upperStarStalkIso l f y G.obj.X).hom ≫ (mono τ).hom.app (G.upperStar l f)
  /-- Global sections restrict to sections of the stalks which are invariant under transport. -/
  mono_globalSections {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (G : LisseSheaf l Y) :
    (globalSectionsToUpperStar _ y).app G.obj.X ≫ (mono τ).hom.app G =
      (globalSectionsToUpperStar _ z).app G.obj.X
  /-- Transport preserves the evaluation pairing `[G, H]_y × G_y → H_y` of an internal hom of
  lisse sheaves; for `H = ℚ̄_ℓ` this is the pairing `(G^∨)_y × G_y → ℚ̄_ℓ` of the dual. -/
  mono_evaluationPairing {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (G H : LisseSheaf l Y) (hGH : IsAdicLisseSheaf ((AdicSheaf.ihom G.obj).obj H.obj))
    (d : (stalkFunctor l y).obj ((AdicSheaf.ihom G.obj).obj H.obj).X)
    (v : (stalkFunctor l y).obj G.obj.X) :
    Mod.evaluationPairing (stalkFunctor l z) G.obj H.obj
        (((mono τ).hom.app ⟨_, hGH⟩).hom d) (((mono τ).hom.app G).hom v) =
      ((mono τ).hom.app H).hom (Mod.evaluationPairing (stalkFunctor l y) G.obj H.obj d v)

namespace LisseMonodromy

variable {l Y Ω} (M : LisseMonodromy l Y Ω)

/-- The stalk `G_t` of a lisse sheaf at a geometric point, as a `ℚ̄_ℓ`-vector space. -/
noncomputable abbrev StalkSpace (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :
    ModuleCat.{u + 1} (PadicAlgCl l) :=
  (WeilCoefficients.toModuleCat l).obj ((lisseStalk l t).obj G)

/-- The `ℚ̄_ℓ`-linear transport `G_y → G_z` along a path. -/
noncomputable def monoLinear {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (G : LisseSheaf l Y) : StalkSpace y G →ₗ[PadicAlgCl l] StalkSpace z G :=
  ((WeilCoefficients.toModuleCat l).map ((M.mono τ).hom.app G)).hom

/-- Transport along the trivial path is the identity. -/
lemma monoLinear_refl (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (G : LisseSheaf l Y) (v : StalkSpace y G) :
    M.monoLinear (Iso.refl (fiber y)) G v = v := by
  simp [monoLinear, M.mono_refl]

/-- Transport along a composite path is the composite of the transports. -/
lemma monoLinear_trans {y z w : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) (G : LisseSheaf l Y) (v : StalkSpace y G) :
    M.monoLinear (τ ≪≫ τ') G v = M.monoLinear τ' G (M.monoLinear τ G v) := by
  simp [monoLinear, M.mono_trans]
  rfl

/-- The monodromy representation of `π₁(Y, t) = Aut F_t` on the stalk `G_t` of a lisse sheaf:
an automorphism `g` of the fibre functor acts by transport along the path `g`. -/
noncomputable def rep (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :
    Representation (PadicAlgCl l) (Aut (fiber t)) (StalkSpace t G) where
  toFun g := M.monoLinear g.asIso G
  map_one' := LinearMap.ext fun v ↦ M.monoLinear_refl t G v
  map_mul' g h := LinearMap.ext fun v ↦ by
    rw [Aut.mul_asIso, M.monoLinear_trans]
    rfl

/-- The monodromy representation acts by transport. -/
lemma rep_apply (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) (g : Aut (fiber t))
    (v : StalkSpace t G) : M.rep t G g v = M.monoLinear g.asIso G v :=
  rfl

/-- The monodromy at the base point `t` is an equivalence onto continuous finite-dimensional
representations (`proposition-lattices-representations-normal-scheme` for `Λ = ℚ̄_ℓ`): the
representations `AlgebraicGeometry.ProEtale.LisseMonodromy.rep` are continuous, the stalk functor at
`t` is faithful and full onto `π₁(Y, t)`-equivariant maps, and every continuous finite-dimensional
representation of `π₁(Y, t)` is the monodromy representation of a lisse sheaf. -/
structure IsEquivalenceAt (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : Prop where
  /-- The monodromy representations are continuous. -/
  continuous_rep (G : LisseSheaf l Y) (φ : Module.Dual (PadicAlgCl l) (StalkSpace t G))
    (v : StalkSpace t G) : Continuous fun g : Aut (fiber t) ↦ φ (M.rep t G g v)
  /-- The stalk functor at `t` is faithful. -/
  faithful {G H : LisseSheaf l Y} (f g : G ⟶ H)
    (h : (lisseStalk l t).map f = (lisseStalk l t).map g) : f = g
  /-- Every equivariant linear map of stalks is the stalk of a morphism. -/
  full {G H : LisseSheaf l Y} (φ : StalkSpace t G →ₗ[PadicAlgCl l] StalkSpace t H)
    (hφ : ∀ g v, φ (M.rep t G g v) = M.rep t H g (φ v)) :
    ∃ f : G ⟶ H, ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom = φ
  /-- Every continuous finite-dimensional representation is a monodromy representation. -/
  essSurj (V : Type (u + 1)) [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) (Aut (fiber t)) V)
    (hρ : ∀ (φ : Module.Dual (PadicAlgCl l) V) (v : V), Continuous fun g ↦ φ (ρ g v)) :
    ∃ (G : LisseSheaf l Y) (e : StalkSpace t G ≃ₗ[PadicAlgCl l] V),
      ∀ g v, e (M.rep t G g v) = ρ g (e v)

/-- The stalk map of a morphism of lisse sheaves intertwines the monodromy representations. -/
lemma rep_naturality (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    {G H : LisseSheaf l Y} (f : G ⟶ H)
    (g : Aut (fiber t)) (v : StalkSpace t G) :
    ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom (M.rep t G g v) =
      M.rep t H g (((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom v) := by
  have h := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
    ((M.mono g.asIso).hom.naturality f)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

variable {M} in
/-- A morphism of lisse sheaves whose stalk at a base point is bijective is an isomorphism, if
the monodromy at that base point is an equivalence. -/
lemma IsEquivalenceAt.isIso_of_bijective {t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (hM : M.IsEquivalenceAt t)
    {G H : LisseSheaf l Y} (f : G ⟶ H)
    (hf : Function.Bijective ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom) :
    IsIso f := by
  let e := LinearEquiv.ofBijective _ hf
  obtain ⟨f', hf'⟩ := hM.full e.symm.toLinearMap fun g v ↦ by
    apply e.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    change _ = ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom _
    rw [M.rep_naturality]
    exact congrArg _ (e.apply_symm_apply v).symm
  have hcomp : ∀ (a : G ⟶ H) (b : H ⟶ G) (x : StalkSpace t G),
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (a ≫ b))).hom x =
        ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map b)).hom
          (((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map a)).hom x) := fun a b x ↦ by
    rw [Functor.map_comp, Functor.map_comp]
    rfl
  refine ⟨f', hM.faithful _ _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)),
    hM.faithful _ _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))⟩
  · change ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (f ≫ f'))).hom x =
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (𝟙 G))).hom x
    rw [hcomp, hf', CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact e.symm_apply_apply x
  · change ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (f' ≫ f))).hom x =
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (𝟙 H))).hom x
    rw [CategoryTheory.Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      hf', CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact e.apply_symm_apply x

/-- The identification of stalks along an equality of geometric points. -/
lemma mono_eqToIso_hom_app {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (h : y = z)
    (G : LisseSheaf l Y) :
    (M.mono (eqToIso (congrArg fiber h))).hom.app G =
      (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app G.obj.X) := by
  subst h
  simp [M.mono_refl, upperStarCongr]
  rfl

/-- Transport along the inverse path is the inverse transport. -/
lemma mono_symm {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z) :
    M.mono τ.symm = (M.mono τ).symm := by
  have h := M.mono_trans τ τ.symm
  rw [Iso.self_symm_id, M.mono_refl] at h
  ext1
  exact (Iso.inv_ext (congrArg Iso.hom h).symm).symm

/-- **Transport of a Frobenius-type operator along a path.** Let `s` be a geometric point with
`s ≫ f = a ≫ s` for an endomorphism `f` of `Y` and an automorphism `a` of `Spec Ω̄`, and
`ψ : f^* G ⟶ G`. The operator `G_s ≅ G_{a ≫ s} = G_{s ≫ f} = (f^* G)_s ⟶ G_s` is carried by the
transport along a path `π : F_s ≅ F_t` to the transport along the loop
`F_t ≅ F_s ≅ F_{a ≫ s} = F_{s ≫ f} ≅ F_{t ≫ f}` followed by `G_{t ≫ f} = (f^* G)_t ⟶ G_t`. -/
theorem reparam_comp_upperStar_comp_mono (f : Y ⟶ Y)
    (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    {s t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (hs : s ≫ f = a.hom ≫ s) (π : fiber s ≅ fiber t)
    (G : LisseSheaf l Y) (ψ : G.upperStar l f ⟶ G) :
    (M.mono (fiberReparamIso a s)).inv.app G ≫
        (M.mono (eqToIso (congrArg fiber hs.symm))).hom.app G ≫
        (upperStarStalkIso l f s G.obj.X).hom ≫ (lisseStalk l s).map ψ ≫ (M.mono π).hom.app G =
      (M.mono π).hom.app G ≫
        (M.mono (π.symm ≪≫ (fiberReparamIso a s).symm ≪≫ eqToIso (congrArg fiber hs.symm) ≪≫
          pullbackPathIso f π)).hom.app G ≫
        (upperStarStalkIso l f t G.obj.X).hom ≫ (lisseStalk l t).map ψ := by
  have e₁ := M.mono_upperStar f π G
  have e₂ : (M.mono π).hom.app _ ≫ (lisseStalk l t).map ψ =
      (lisseStalk l s).map ψ ≫ (M.mono π).hom.app _ :=
    ((M.mono π).hom.naturality _).symm
  rw [M.mono_trans, M.mono_trans, M.mono_trans, M.mono_symm, M.mono_symm]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% e₁, e₂]

/-- The transport along the reparametrisation path and along an equality of geometric points,
followed by `G_{s ≫ f} = (f^* G)_s ⟶ G_s`, computed on the underlying sheaves. -/
theorem reparam_upperStar_apply (f : Y ⟶ Y)
    (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    {s : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (hs : s ≫ f = a.hom ≫ s) (G : LisseSheaf l Y)
    (ψ : G.upperStar l f ⟶ G) (v : StalkSpace s G) :
    ((WeilCoefficients.toModuleCat l).map ((lisseStalk l s).map ψ)).hom
      (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l f s G.obj.X).hom).hom
        (((WeilCoefficients.toModuleCat l).map
          ((M.mono (eqToIso (congrArg fiber hs.symm))).hom.app G)).hom
          (((WeilCoefficients.toModuleCat l).map
            ((M.mono (fiberReparamIso a s)).inv.app G)).hom v))) =
    ((WeilCoefficients.toModuleCat l).map ((stalkFunctor l s).map ψ.hom.hom)).hom
      (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l f s G.obj.X).hom).hom
        (((WeilCoefficients.toModuleCat l).map
          ((Sheaf.Γ _ _).map ((upperStarCongr _ hs.symm).hom.app G.obj.X))).hom
          (((WeilCoefficients.toModuleCat l).map (reparamStalkIso l a s G.obj.X).inv).hom v))) := by
  have e₃ : (M.mono (fiberReparamIso a s)).app G = reparamStalkIso l a s G.obj.X :=
    Iso.ext (M.mono_reparam a s G)
  have h₁ : ((WeilCoefficients.toModuleCat l).map
      ((M.mono (fiberReparamIso a s)).inv.app G)).hom v =
      ((WeilCoefficients.toModuleCat l).map (reparamStalkIso l a s G.obj.X).inv).hom v := by
    rw [← Iso.app_inv, e₃]
    rfl
  have h₂ : ∀ w, ((WeilCoefficients.toModuleCat l).map
      ((M.mono (eqToIso (congrArg fiber hs.symm))).hom.app G)).hom w =
      ((WeilCoefficients.toModuleCat l).map
        ((Sheaf.Γ _ _).map ((upperStarCongr _ hs.symm).hom.app G.obj.X))).hom w := fun w ↦ by
    rw [M.mono_eqToIso_hom_app]
    rfl
  rw [h₁, h₂]
  rfl

/-- `reparam_comp_upperStar_comp_mono` on elements. -/
theorem reparam_comp_upperStar_comp_mono_apply (f : Y ⟶ Y)
    (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    {s t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (hs : s ≫ f = a.hom ≫ s) (π : fiber s ≅ fiber t)
    (G : LisseSheaf l Y)
    (ψ : G.upperStar l f ⟶ G) (v : StalkSpace s G) :
    M.monoLinear π G (((WeilCoefficients.toModuleCat l).map ((lisseStalk l s).map ψ)).hom
      (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l f s G.obj.X).hom).hom
        (((WeilCoefficients.toModuleCat l).map
          ((M.mono (eqToIso (congrArg fiber hs.symm))).hom.app G)).hom
          (((WeilCoefficients.toModuleCat l).map
            ((M.mono (fiberReparamIso a s)).inv.app G)).hom v)))) =
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map ψ)).hom
        (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l f t G.obj.X).hom).hom
          (M.monoLinear (π.symm ≪≫ (fiberReparamIso a s).symm ≪≫ eqToIso (congrArg fiber hs.symm) ≪≫
            pullbackPathIso f π) G (M.monoLinear π G v))) := by
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v)
    (M.reparam_comp_upperStar_comp_mono f a hs π G ψ)
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The transport along a path followed by `G_{t ≫ f} = (f^* G)_t ⟶ G_t`, on elements. -/
theorem mono_comp_upperStar_comp_apply (f : Y ⟶ Y) {y t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (δ : fiber y ≅ fiber (t ≫ f)) (G : LisseSheaf l Y) (ψ : G.upperStar l f ⟶ G)
    (w : StalkSpace y G) :
    ((WeilCoefficients.toModuleCat l).map ((M.mono δ).hom.app G ≫
        (upperStarStalkIso l f t G.obj.X).hom ≫ (lisseStalk l t).map ψ)).hom w =
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map ψ)).hom
        (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l f t G.obj.X).hom).hom
          (M.monoLinear δ G w)) := by
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

end LisseMonodromy

end AlgebraicGeometry.ProEtale
