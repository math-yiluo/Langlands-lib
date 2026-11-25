/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayer
public import WeilConjectures.CategoryTheory.Adjunction.ConjugateCounit

/-!

# The Galois action on the nearby cycles of a finite Galois layer

Let `N_{L'}` be the finite Galois layer of a model `N` along `h : N.generic ⟶ Spec L` and a
finite Galois extension `L'/L` (`NearbyCyclesModel.galoisLayer`), with generic fibre
`G = N.generic ×_{Spec L} Spec L'`, projection `g : G ⟶ N.generic` and automorphisms `ρ_σ` of
`G` over `N.generic`. This file computes the action of `σ ∈ Gal(L'/L)` on the nearby cycles of
`N_{L'}` (`NearbyCyclesModel.Hom.autAction` of `NearbyCyclesModel.galoisLayerAut σ`).

For `s : G ⟶ G'`, `p`, `q` out of `G'` and factorizations `s ≫ p = p₁`, `s ≫ q = q₁`, the
*unit transport* `Rp_* Lq^* A ⟶ Rp₁_* Lq₁^* A` is the unit of `Ls^* ⊣ Rs_*` followed by the
composition isomorphisms (`ProEtale.CondensedRing.derivedUnitTransport`); for `p = q = g` and
`s = ρ_σ` it is the action of `ρ_σ` on `Rg_* Lg^*`.

## Main results

- `NearbyCyclesModel.Hom.pullbackExchange_app_eq_derivedUnitTransport`,
  `NearbyCyclesModel.Hom.autAction_eq_derivedUnitTransport`: the pullback exchange and the action
  on nearby cycles of an endomorphism of a model with identity total component `𝟙` and generic
  component `s` are `Li^*` of the unit transport along `s` (a mate computation, cf.
  `NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`).
- `ProEtale.CondensedRing.derivedUnitTransport_comp`: the unit transport of a composite
  `g ≫ j`, `g ≫ ε` is `Rj_*` of the unit transport of `g` at `Lε^*`, up to the composition
  isomorphisms; it rests on the associativity of the composition isomorphisms of derived
  pushforwards (`ProEtale.CondensedRing.rightDerivedLowerStarComp_inv_app_assoc`).
- `NearbyCyclesModel.galoisLayerAut_autAction`: the action of `σ` on the nearby cycles of `N_{L'}`
  is `κ⁻¹ ≫ Li^* Rj_* (u_σ) ≫ κ`, for the unit transport `u_σ` along `ρ_σ` of `Rg_* Lg^*` at
  `Lε^* C` and `κ = NearbyCyclesModel.galoisLayerExchangeIso`.
- `NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom'`: the splitting of the
  pullback exchange of `N_{L'} ⟶ N` with idempotent `|Γ|⁻¹ ∑ σ, σ_*`, the average of the actions
  of `galoisLayerAut σ` on the nearby cycles, provided the unit transports `u_σ` are the derived
  Galois actions `ProEtale.CondensedRing.derivedGaloisAction` up to a bijection of `Γ`.

## Implementation notes

The diagram chases are carried out in abstract categories (`CategoryTheory.unitTransport_comp_aux`,
`CategoryTheory.pullbackExchange_endo_aux`) and then instantiated. The identification of the
unit transports `u_σ` with the derived Galois actions (defined through the restriction to the
base changes `V ×_X Y`) is not proved here and enters the last theorem as a hypothesis.

-/

@[expose] public section


universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- The coherence behind `ProEtale.CondensedRing.derivedUnitTransport_comp`, in abstract
categories: the unit transport `R_{gj}(η_s) ≫ c ≫ R(c⁻¹)` along `s` of a composite `g ≫ j`,
`g ≫ ε` is `R_j` of the unit transport along `s` of `g`, up to the composition isomorphisms,
provided the composition isomorphisms are associative. -/
lemma unitTransport_comp_aux {CX CN CT CG' CG : Type*} [Category CX] [Category CN]
    [Category CT] [Category CG'] [Category CG]
    {Lε : CX ⥤ CN} {Rj : CN ⥤ CT} {Lg : CN ⥤ CG'} {Rg : CG' ⥤ CN} {Ls : CG' ⥤ CG}
    {Rs : CG ⥤ CG'} {Lgε : CX ⥤ CG'} {Rgj : CG' ⥤ CT} {Lsg : CN ⥤ CG} {Rsg : CG ⥤ CN}
    {Ls_gε Lsg_ε : CX ⥤ CG} {Rs_gj Rsg_j : CG ⥤ CT} (η : 𝟭 CG' ⟶ Ls ⋙ Rs)
    (cLgε : Lgε ≅ Lε ⋙ Lg) (cLsg : Lsg ≅ Lg ⋙ Ls) (cLs_gε : Ls_gε ≅ Lgε ⋙ Ls)
    (cLsg_ε : Lsg_ε ≅ Lε ⋙ Lsg) (cRgj : Rg ⋙ Rj ≅ Rgj) (cRsg : Rs ⋙ Rg ≅ Rsg)
    (cRs_gj : Rs ⋙ Rgj ≅ Rs_gj) (cRsg_j : Rsg ⋙ Rj ≅ Rsg_j) (hL : Ls_gε = Lsg_ε)
    (hR : Rs_gj = Rsg_j)
    (hLassoc : ∀ A, cLsg_ε.hom.app A ≫ cLsg.hom.app (Lε.obj A) =
      eqToHom (by rw [hL]) ≫ cLs_gε.hom.app A ≫ Ls.map (cLgε.hom.app A))
    (hRassoc : ∀ Z, cRs_gj.inv.app Z ≫ cRgj.inv.app (Rs.obj Z) =
      eqToHom (by rw [hR]) ≫ cRsg_j.inv.app Z ≫ Rj.map (cRsg.inv.app Z))
    (A : CX) :
    (Rgj.map (η.app (Lgε.obj A)) ≫ cRs_gj.hom.app (Ls.obj (Lgε.obj A)) ≫
        Rs_gj.map (cLs_gε.inv.app A)) ≫ eqToHom (by rw [hR, hL]) =
      Rgj.map (cLgε.hom.app A) ≫ cRgj.inv.app (Lg.obj (Lε.obj A)) ≫
        Rj.map (Rg.map (η.app (Lg.obj (Lε.obj A))) ≫
          cRsg.hom.app (Ls.obj (Lg.obj (Lε.obj A))) ≫ Rsg.map (cLsg.inv.app (Lε.obj A))) ≫
        cRsg_j.hom.app (Lsg.obj (Lε.obj A)) ≫ Rsg_j.map (cLsg_ε.inv.app A) := by
  subst hL hR
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hLassoc hRassoc ⊢
  have hR' : Rj.map (cRsg.hom.app (Ls.obj (Lg.obj (Lε.obj A)))) ≫
      cRsg_j.hom.app (Ls.obj (Lg.obj (Lε.obj A))) =
      cRgj.hom.app (Rs.obj (Ls.obj (Lg.obj (Lε.obj A)))) ≫
        cRs_gj.hom.app (Ls.obj (Lg.obj (Lε.obj A))) := by
    have h := hRassoc (Ls.obj (Lg.obj (Lε.obj A)))
    calc _ = Rj.map (cRsg.hom.app _) ≫ cRsg_j.hom.app _ ≫
          (cRs_gj.inv.app _ ≫ cRgj.inv.app (Rs.obj (Ls.obj (Lg.obj (Lε.obj A))))) ≫
          cRgj.hom.app _ ≫ cRs_gj.hom.app _ := by simp
      _ = _ := by
        rw [h]
        simp [← Functor.map_comp_assoc]
  have hL' : cLsg.inv.app (Lε.obj A) ≫ cLsg_ε.inv.app A =
      Ls.map (cLgε.inv.app A) ≫ cLs_gε.inv.app A := by
    calc _ = (Ls.map (cLgε.inv.app A) ≫ cLs_gε.inv.app A) ≫ (cLs_gε.hom.app A ≫
          Ls.map (cLgε.hom.app A)) ≫ cLsg.inv.app (Lε.obj A) ≫ cLsg_ε.inv.app A := by
          simp [← Functor.map_comp_assoc]
      _ = _ := by
        rw [← hLassoc]
        simp
  have hη := η.naturality (cLgε.inv.app A)
  have hc := cRs_gj.hom.naturality (Ls.map (cLgε.inv.app A))
  have hd := cRgj.inv.naturality (η.app (Lg.obj (Lε.obj A)))
  have he := cRsg_j.hom.naturality (cLsg.inv.app (Lε.obj A))
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hη hc hd he
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% he, reassoc_of% hR', ← Functor.map_comp, hL', Functor.map_comp,
    ← reassoc_of% hc, ← reassoc_of% hd, Iso.inv_hom_id_app_assoc, ← Rgj.map_comp_assoc,
    ← Rgj.map_comp_assoc, Category.assoc, ← hη, Iso.hom_inv_id_app_assoc]

/-- The conjugation glue behind `NearbyCyclesModel.galoisLayerAut_autAction`: if `x` is
conjugate to `F (r v ≫ w ≫ y ≫ w' ≫ r v')` by `F (r u)`, then it is conjugate to `F y` by
`κ = F (w' ≫ r (v' ≫ u'))` with inverse `F (r (u ≫ v) ≫ w)`, if `u ≫ u' = 𝟙`. -/
lemma eq_inv_comp_map_comp_hom_of_comp_map_eq {C C' D : Type*} [Category C] [Category C']
    [Category D] (F : C ⥤ D) (r : C' ⥤ C) {l₀ l₁ l₂ : C'} {T : C} (u : l₀ ⟶ l₁)
    (u' : l₁ ⟶ l₀) (hu : u ≫ u' = 𝟙 _) (v : l₁ ⟶ l₂) (v' : l₂ ⟶ l₁) (w : r.obj l₂ ⟶ T)
    (w' : T ⟶ r.obj l₂)
    (y : T ⟶ T) (x : F.obj (r.obj l₀) ⟶ F.obj (r.obj l₀))
    (hx : x ≫ F.map (r.map u) =
      F.map (r.map u) ≫ F.map (r.map v ≫ w ≫ y ≫ w' ≫ r.map v'))
    (κ : F.obj T ≅ F.obj (r.obj l₀)) (hκ : κ.hom = F.map (w' ≫ r.map (v' ≫ u')))
    (hκ' : κ.inv = F.map (r.map (u ≫ v) ≫ w)) :
    x = κ.inv ≫ F.map y ≫ κ.hom := by
  have hx' := congrArg (· ≫ F.map (r.map u')) hx
  simp only [Category.assoc, ← F.map_comp, ← r.map_comp, hu, r.map_id, F.map_id,
    Category.comp_id] at hx'
  rw [hx', hκ, hκ']
  simp only [← F.map_comp, Category.assoc, r.map_comp]

/-- The glue behind `NearbyCyclesModel.Hom.autAction_eq_derivedUnitTransport`: if
`α = I₁(Ψ b) ≫ u ≫ Ψ(I⁻¹(b))` for isomorphisms `I : L₀ ≅ 𝟭`, `I₁ : L₁ ≅ 𝟭`, then
`I₁⁻¹(Ψ b) ≫ α ≫ Ψ(I(b)) = u`. -/
lemma inv_app_comp_comp_map_hom_app_eq_of_eq {C E : Type*} [Category C] [Category E]
    (Ψ : C ⥤ E) {L₀ : C ⥤ C} (I : L₀ ≅ 𝟭 C) {L₁ : E ⥤ E} (I₁ : L₁ ≅ 𝟭 E) (b : C)
    (α : L₁.obj (Ψ.obj b) ⟶ Ψ.obj (L₀.obj b)) (u : Ψ.obj b ⟶ Ψ.obj b)
    (hα : α = I₁.hom.app (Ψ.obj b) ≫ u ≫ Ψ.map (I.inv.app b)) :
    I₁.inv.app (Ψ.obj b) ≫ α ≫ Ψ.map (I.hom.app b) = u := by
  subst hα
  simp [← Ψ.map_comp]

/-- The pullback exchange of an endomorphism of a model with identity total component, in
abstract categories: `Lε`, `Lj ⊣ Rj`, `Li` are the functors of the model, `Ls ⊣ Rs` the adjunction
of the generic component, `I₀`, `It`, `I'` the identity isomorphisms of the pullbacks along
identities, `cI`, `θ`, `cE` the pullback comparisons of the three squares, and `c`, `d` the
composition isomorphisms `Lj ≅ Lj ⋙ Ls`, `Lε ≅ Lε ⋙ Ls`. -/
lemma pullbackExchange_endo_aux {DX DG DT DS : Type*} [Category DX] [Category DG] [Category DT]
    [Category DS] {Lε : DX ⥤ DG} {Lj : DT ⥤ DG} {Rj : DG ⥤ DT} {Li : DT ⥤ DS} {Ls Rs : DG ⥤ DG}
    {L₀ : DX ⥤ DX} {Lt : DT ⥤ DT} {L' : DS ⥤ DS} (aj : Lj ⊣ Rj) (as : Ls ⊣ Rs)
    (I₀ : L₀ ≅ 𝟭 DX) (It : Lt ≅ 𝟭 DT) (I' : L' ≅ 𝟭 DS) (cI : Li ⋙ L' ≅ Lt ⋙ Li)
    (θ : Lt ⋙ Lj ⟶ Lj ⋙ Ls) (cE : Lε ⋙ Ls ⟶ L₀ ⋙ Lε) (c : Lj ≅ Lj ⋙ Ls) (d : Lε ≅ Lε ⋙ Ls)
    (hI : ∀ Y, cI.hom.app Y = I'.hom.app (Li.obj Y) ≫ Li.map (It.inv.app Y))
    (hθ : ∀ B, θ.app B = Lj.map (It.hom.app B) ≫ c.hom.app B)
    (hE : ∀ A, cE.app A = d.inv.app A ≫ Lε.map (I₀.inv.app A))
    (α : (Lε ⋙ Rj ⋙ Li) ⋙ L' ⟶ L₀ ⋙ Lε ⋙ Rj ⋙ Li)
    (hα : α = Functor.whiskerLeft (Lε ⋙ Rj) cI.hom ≫ Functor.whiskerRight
      (Functor.whiskerLeft Lε (mateEquiv aj aj θ) ≫ Functor.whiskerRight cE Rj) Li)
    (A : DX) :
    α.app A = I'.hom.app (Li.obj (Rj.obj (Lε.obj A))) ≫
      Li.map (Rj.map (as.unit.app (Lε.obj A)) ≫
        (conjugateIsoEquiv (aj.comp as) aj c).hom.app (Ls.obj (Lε.obj A)) ≫
        Rj.map (d.inv.app A)) ≫ Li.map (Rj.map (Lε.map (I₀.inv.app A))) := by
  subst hα
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, mateEquiv_app_of_isoId_comp aj aj as It c θ hθ, hI, hE]
  simp [← Functor.map_comp]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

-- the conjugates of the composition isomorphisms of derived pullbacks are large terms
/-- **Associativity of the composition isomorphisms of derived pushforwards**: the two ways of
identifying `R(a ≫ b ≫ c)_*` with `Ra_* ⋙ Rb_* ⋙ Rc_*` agree. It is the conjugate of the
associativity `leftDerivedUpperStarComp_assoc_app` of the derived pullbacks. -/
lemma rightDerivedLowerStarComp_inv_app_assoc {A₀ A₁ A₂ A₃ : Scheme.{u}} (a : A₀ ⟶ A₁)
    (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃)
    (Z : DerivedCategory (Mod (Sheaf (ProEt.topology A₀) Ab.{u + 1}) (condensedRingObj Λ A₀))) :
    (rightDerivedLowerStarComp Λ a (b ≫ c)).inv.app Z ≫
        (rightDerivedLowerStarComp Λ b c).inv.app (R((a)_*⟦Λ⟧).obj Z) =
      eqToHom (by rw [Category.assoc]) ≫ (rightDerivedLowerStarComp Λ (a ≫ b) c).inv.app Z ≫
        R((c)_*⟦Λ⟧).map ((rightDerivedLowerStarComp Λ a b).inv.app Z) := by
  let L' : (A₀ ⟶ A₃) → _ := fun m ↦ L((m)^*⟦Λ⟧)
  let R' : (A₀ ⟶ A₃) → _ := fun m ↦ R((m)_*⟦Λ⟧)
  let adj' : ∀ m, L' m ⊣ R' m := fun m ↦ derivedUpperStarLowerStarAdjunction Λ m
  refine conjugateIsoEquiv_assoc_aux L' R' adj'
    (Category.assoc a b c).symm (derivedUpperStarLowerStarAdjunction Λ c)
    (derivedUpperStarLowerStarAdjunction Λ b) (derivedUpperStarLowerStarAdjunction Λ a)
    (derivedUpperStarLowerStarAdjunction Λ (b ≫ c))
    (derivedUpperStarLowerStarAdjunction Λ (a ≫ b)) (leftDerivedUpperStarComp Λ b c)
    (leftDerivedUpperStarComp Λ a b) (leftDerivedUpperStarComp Λ a (b ≫ c))
    (leftDerivedUpperStarComp Λ (a ≫ b) c) (fun K ↦ ?_) Z
  have h := leftDerivedUpperStarComp_assoc_app Λ a b c K
  rw [← cancel_epi (eqToHom (congrArg (fun m ↦ (L' m).obj K) (Category.assoc a b c))),
    ← h, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The **unit transport** along `s : G ⟶ G'` of `R(p)_* L(q)^*`, for `s ≫ p = p₁` and
`s ≫ q = q₁`: the unit of `Ls^* ⊣ Rs_*` followed by the composition isomorphisms,
`Rp_* Lq^* A ⟶ Rp_* Rs_* Ls^* Lq^* A ≅ R(s ≫ p)_* L(s ≫ q)^* A = R(p₁)_* L(q₁)^* A`. For an
automorphism `s` of a Galois covering `g = p = q` (with `s ≫ g = g`) this is the action of `s` on
`Rg_* Lg^* A`. -/
noncomputable def derivedUnitTransport {G G' T S : Scheme.{u}} (s : G ⟶ G') {p : G' ⟶ T}
    {q : G' ⟶ S} {p₁ : G ⟶ T} {q₁ : G ⟶ S} (hp : s ≫ p = p₁) (hq : s ≫ q = q₁)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :
    R((p)_*⟦Λ⟧).obj (L((q)^*⟦Λ⟧).obj A) ⟶ R((p₁)_*⟦Λ⟧).obj (L((q₁)^*⟦Λ⟧).obj A) :=
  (R((p)_*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ s).unit.app (L((q)^*⟦Λ⟧).obj A)) ≫
    (rightDerivedLowerStarComp Λ s p).hom.app (L((s)^*⟦Λ⟧).obj (L((q)^*⟦Λ⟧).obj A)) ≫
    R((s ≫ p)_*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ s q).inv.app A)) ≫
    eqToHom (by rw [hp, hq])

/-- The unit transport along `s` of `R(p)_* L(q)^*` to `R(s ≫ p)_* L(s ≫ q)^*`, without
transport along equalities. -/
lemma derivedUnitTransport_rfl {G G' T S : Scheme.{u}} (s : G ⟶ G') (p : G' ⟶ T) (q : G' ⟶ S)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :
    derivedUnitTransport Λ s (p₁ := s ≫ p) (q₁ := s ≫ q) rfl rfl A =
      R((p)_*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ s).unit.app
          (L((q)^*⟦Λ⟧).obj A)) ≫
        (rightDerivedLowerStarComp Λ s p).hom.app (L((s)^*⟦Λ⟧).obj (L((q)^*⟦Λ⟧).obj A)) ≫
        R((s ≫ p)_*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ s q).inv.app A) :=
  Category.comp_id _

/-- The unit transport in terms of the composition isomorphisms `L(p₁)^* ≅ Lp^* ⋙ Ls^*` along
the factorizations `s ≫ p = p₁`, `s ≫ q = q₁` and the conjugate of the first. -/
lemma derivedUnitTransport_eq_conjugate {G G' T S : Scheme.{u}} (s : G ⟶ G') {p : G' ⟶ T}
    {q : G' ⟶ S} {p₁ : G ⟶ T} {q₁ : G ⟶ S} (hp : s ≫ p = p₁) (hq : s ≫ q = q₁)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :
    derivedUnitTransport Λ s hp hq A =
      R((p)_*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ s).unit.app
          (L((q)^*⟦Λ⟧).obj A)) ≫
        (conjugateIsoEquiv ((derivedUpperStarLowerStarAdjunction Λ p).comp
          (derivedUpperStarLowerStarAdjunction Λ s)) (derivedUpperStarLowerStarAdjunction Λ p₁)
          (leftDerivedUpperStarCompOfEq Λ hp)).hom.app (L((s)^*⟦Λ⟧).obj (L((q)^*⟦Λ⟧).obj A)) ≫
        R((p₁)_*⟦Λ⟧).map ((leftDerivedUpperStarCompOfEq Λ hq).inv.app A) := by
  subst hp hq
  exact Category.comp_id _

-- the derived functors and their composition isomorphisms are large terms
/-- **The unit transport of a composite**: the unit transport along `s` of `R(g' ≫ j)_*
L(g' ≫ ε)^*` is `Rj_*` of the unit transport along `s` of `Rg'_* Lg'^*` at `Lε^* A`, up to the
composition isomorphisms. -/
lemma derivedUnitTransport_comp {G G' N T S : Scheme.{u}} (s : G ⟶ G') (g' : G' ⟶ N)
    (g : G ⟶ N) (hs : s ≫ g' = g) (j : N ⟶ T) (ε : N ⟶ S)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :
    derivedUnitTransport Λ s (p := g' ≫ j) (q := g' ≫ ε) (p₁ := g ≫ j) (q₁ := g ≫ ε)
        (by rw [← hs, Category.assoc]) (by rw [← hs, Category.assoc]) A =
      R((g' ≫ j)_*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ g' ε).hom.app A) ≫
        (rightDerivedLowerStarComp Λ g' j).inv.app (L((g')^*⟦Λ⟧).obj (L((ε)^*⟦Λ⟧).obj A)) ≫
        R((j)_*⟦Λ⟧).map (derivedUnitTransport Λ s hs hs (L((ε)^*⟦Λ⟧).obj A)) ≫
        (rightDerivedLowerStarComp Λ g j).hom.app (L((g)^*⟦Λ⟧).obj (L((ε)^*⟦Λ⟧).obj A)) ≫
        R((g ≫ j)_*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ g ε).inv.app A) := by
  subst hs
  rw [derivedUnitTransport_rfl Λ s g' g']
  exact unitTransport_comp_aux (derivedUpperStarLowerStarAdjunction Λ s).unit
    (leftDerivedUpperStarComp Λ g' ε) (leftDerivedUpperStarComp Λ s g')
    (leftDerivedUpperStarComp Λ s (g' ≫ ε)) (leftDerivedUpperStarComp Λ (s ≫ g') ε)
    (rightDerivedLowerStarComp Λ g' j) (rightDerivedLowerStarComp Λ s g')
    (rightDerivedLowerStarComp Λ s (g' ≫ j)) (rightDerivedLowerStarComp Λ (s ≫ g') j)
    (by rw [Category.assoc]) (by rw [Category.assoc])
    (leftDerivedUpperStarComp_assoc_app Λ s g' ε)
    (rightDerivedLowerStarComp_inv_app_assoc Λ s g' j) A

section Squares

variable {X Y Z : Scheme.{u}}

/-- `pullbackSquareComparison_hom_app_comp_id_bottom` for a square `g' ≫ p = p' ≫ 𝟙` with an
arbitrary factorization `g' ≫ p = p'`. -/
lemma pullbackSquareComparison_hom_app_of_eq_id_bottom (g' : X ⟶ Y) (p : Y ⟶ Z) {p' : X ⟶ Z}
    (h : g' ≫ p = p') (sq : CommSq g' p' p (𝟙 Z))
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (pullbackSquareComparison Λ sq).hom.app B =
      L((p')^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Z).hom.app B) ≫
        (leftDerivedUpperStarCompOfEq Λ h).hom.app B := by
  subst h
  exact pullbackSquareComparison_hom_app_comp_id_bottom Λ g' p sq B

/-- `pullbackSquareComparison_hom_app_comp_id_right` for a square `g'' ≫ 𝟙 = p' ≫ g` with an
arbitrary factorization `p' ≫ g = g''`. -/
lemma pullbackSquareComparison_hom_app_of_eq_id_right (p' : X ⟶ Y) (g : Y ⟶ Z) {g'' : X ⟶ Z}
    (h : p' ≫ g = g'') (sq : CommSq g'' p' (𝟙 Z) g)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (pullbackSquareComparison Λ sq).hom.app A =
      (leftDerivedUpperStarCompOfEq Λ h).inv.app A ≫
        L((g'')^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Z).inv.app A) := by
  subst h
  exact pullbackSquareComparison_hom_app_comp_id_right Λ p' g sq A

-- the derived pullbacks are large terms
/-- The identity isomorphism `L(t)^* ≅ 𝟭` for an endomorphism `t = 𝟙 Z`: the transport of
`leftDerivedUpperStarId` along the equality. -/
noncomputable def leftDerivedUpperStarIdOfEq {t : Z ⟶ Z} (ht : t = 𝟙 Z) : L((t)^*⟦Λ⟧) ≅ 𝟭 _ :=
  Eq.rec (motive := fun t' _ ↦ L((t')^*⟦Λ⟧) ≅ 𝟭 _) (leftDerivedUpperStarId Λ Z) ht.symm

/-- `pullbackSquareComparison_hom_app_id_right` for a square whose right edge `t` is equal to
the identity. -/
lemma pullbackSquareComparison_hom_app_id_right_of_eq (p : X ⟶ Y) {t : Y ⟶ Y} (ht : t = 𝟙 Y)
    (sq : CommSq p (𝟙 X) t p)
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app B =
      (leftDerivedUpperStarId Λ X).hom.app (L((p)^*⟦Λ⟧).obj B) ≫
        L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarIdOfEq Λ ht).inv.app B) := by
  subst ht
  exact pullbackSquareComparison_hom_app_id_right Λ p sq B

/-- `pullbackSquareComparison_hom_app_of_eq_id_bottom` for a square whose bottom edge `t` is
equal to the identity. -/
lemma pullbackSquareComparison_hom_app_of_eq_of_eq (g' : X ⟶ Y) (p : Y ⟶ Z) {p' : X ⟶ Z}
    {t : Z ⟶ Z} (h : g' ≫ p = p') (ht : t = 𝟙 Z) (sq : CommSq g' p' p t)
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (pullbackSquareComparison Λ sq).hom.app B =
      L((p')^*⟦Λ⟧).map ((leftDerivedUpperStarIdOfEq Λ ht).hom.app B) ≫
        (leftDerivedUpperStarCompOfEq Λ h).hom.app B := by
  subst ht
  exact pullbackSquareComparison_hom_app_of_eq_id_bottom Λ g' p h sq B

end Squares

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}}

-- the derived functors and their composition isomorphisms are large terms
/-- **The pullback exchange of an endomorphism of a model with identity total component** is the
unit transport along its generic component `s`: `α_φ(A) = I(Ψ A) ≫ Li^*(u_s(A)) ≫ Ψ(I⁻¹(A))`
for the identity isomorphisms `I : L(𝟙)^* ≅ 𝟭` and the unit transport `u_s` of
`ProEtale.CondensedRing.derivedUnitTransport`. -/
lemma Hom.pullbackExchange_app_eq_derivedUnitTransport (M : NearbyCyclesModel X X')
    (s : M.generic ⟶ M.generic) (hp : s ≫ M.j = M.j) (hq : s ≫ M.ε = M.ε)
    (φ : M.Hom M (𝟙 X) (𝟙 X')) (ht : φ.total = 𝟙 _) (hg : φ.generic = s)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (φ.pullbackExchange Λ).app A =
      (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj A) ≫
        L((M.i)^*⟦Λ⟧).map (derivedUnitTransport Λ s hp hq A) ≫
        (M.nearbyCycles Λ).map ((leftDerivedUpperStarId Λ X).inv.app A) := by
  rw [derivedUnitTransport_eq_conjugate]
  subst hg
  refine pullbackExchange_endo_aux (derivedUpperStarLowerStarAdjunction Λ M.j)
    (derivedUpperStarLowerStarAdjunction Λ φ.generic) (leftDerivedUpperStarId Λ X)
    (leftDerivedUpperStarIdOfEq Λ ht) (leftDerivedUpperStarId Λ X')
    (pullbackSquareComparison Λ φ.commSq_i) (pullbackSquareComparison Λ φ.commSq_j).hom
    (pullbackSquareComparison Λ φ.commSq_ε).hom
    (leftDerivedUpperStarCompOfEq Λ hp) (leftDerivedUpperStarCompOfEq Λ hq)
    ?_ ?_ ?_ _ ?_ A
  · exact fun Y ↦ pullbackSquareComparison_hom_app_id_right_of_eq Λ M.i ht φ.commSq_i Y
  · exact fun B ↦ pullbackSquareComparison_hom_app_of_eq_of_eq Λ φ.generic M.j hp ht φ.commSq_j B
  · exact fun A ↦ pullbackSquareComparison_hom_app_of_eq_id_right Λ φ.generic M.ε hq φ.commSq_ε A
  · rfl

-- the derived functors and their composition isomorphisms are large terms
/-- **The action of an endomorphism of a model with identity total component** on the nearby
cycles is `Li^*` of the unit transport along its generic component. -/
lemma Hom.autAction_eq_derivedUnitTransport (M : NearbyCyclesModel X X')
    (s : M.generic ⟶ M.generic) (hp : s ≫ M.j = M.j) (hq : s ≫ M.ε = M.ε)
    (φ : M.Hom M (𝟙 X) (𝟙 X')) (ht : φ.total = 𝟙 _) (hg : φ.generic = s)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    φ.autAction Λ A = L((M.i)^*⟦Λ⟧).map (derivedUnitTransport Λ s hp hq A) :=
  inv_app_comp_comp_map_hom_app_eq_of_eq (M.nearbyCycles Λ) (leftDerivedUpperStarId Λ X)
    (leftDerivedUpperStarId Λ X') A _ _
    (Hom.pullbackExchange_app_eq_derivedUnitTransport Λ M s hp hq φ ht hg A)

variable (N : NearbyCyclesModel X X') {L : Type u} [Field L] (h : N.generic ⟶ Spec (.of L))
  (L' : Type u) [Field L'] [Algebra L L']

-- the derived functors and their composition isomorphisms are large terms
/-- **The Galois action on the nearby cycles of a finite Galois layer** is, through the
canonical isomorphism `κ` (`NearbyCyclesModel.galoisLayerExchangeIso`), `Li^* Rj_*` of the unit
transport along the automorphism `ρ_σ` of the generic fibre `G` over `N.generic`, at `Lε^* C`. -/
lemma galoisLayerAut_autAction (σ : L' ≃ₐ[L] L')
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (N.galoisLayerAut h L' σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) =
      (N.galoisLayerExchangeIso h L' Λ C).inv ≫
        L((N.i)^*⟦Λ⟧).map (R((N.j)_*⟦Λ⟧).map (derivedUnitTransport Λ
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) (L((N.ε)^*⟦Λ⟧).obj C))) ≫
        (N.galoisLayerExchangeIso h L' Λ C).hom := by
  let p' := Spec.map (CommRingCat.ofHom (algebraMap L L'))
  let p := pullback.fst h p'
  let s := pullbackAction h p' specGaloisAction_comp σ
  have hs := pullbackAction_fst h p' specGaloisAction_comp σ
  let F := L((N.i)^*⟦Λ⟧)
  let Rj := R((p ≫ N.j)_*⟦Λ⟧)
  let Lε := L((p ≫ N.ε)^*⟦Λ⟧)
  have hp : s ≫ (N.galoisLayer h L').j =
      (N.galoisLayer h L').j := (N.galoisLayerAut h L' σ).comm_j.trans (Category.comp_id _)
  have hq : s ≫ (N.galoisLayer h L').ε =
      (N.galoisLayer h L').ε := (N.galoisLayerAut h L' σ).comm_ε.trans (Category.comp_id _)
  have h1 := Hom.autAction_eq_derivedUnitTransport Λ (N.galoisLayer h L') _ hp hq
    (N.galoisLayerAut h L' σ) rfl rfl C
  have h2 : derivedUnitTransport Λ s hp hq C =
      Rj.map ((leftDerivedUpperStarComp Λ _ N.ε).hom.app C) ≫
        (rightDerivedLowerStarComp Λ _ N.j).inv.app _ ≫
        R((N.j)_*⟦Λ⟧).map (derivedUnitTransport Λ s hs hs (L((N.ε)^*⟦Λ⟧).obj C)) ≫
        (rightDerivedLowerStarComp Λ _ N.j).hom.app _ ≫
        Rj.map ((leftDerivedUpperStarComp Λ _ N.ε).inv.app C) :=
    derivedUnitTransport_comp Λ s p p hs N.j N.ε C
  have hn := Hom.autAction_naturality Λ (N.galoisLayerAut h L' σ) (A' := C)
    ((leftDerivedUpperStarId Λ X).hom.app C)
  rw [h1, h2] at hn
  exact eq_inv_comp_map_comp_hom_of_comp_map_eq F Rj
    (Lε.map ((leftDerivedUpperStarId Λ X).hom.app C))
    (Lε.map ((leftDerivedUpperStarId Λ X).inv.app C))
    (by rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id])
    ((leftDerivedUpperStarComp Λ p N.ε).hom.app C) ((leftDerivedUpperStarComp Λ p N.ε).inv.app C)
    ((rightDerivedLowerStarComp Λ _ N.j).inv.app _) ((rightDerivedLowerStarComp Λ _ N.j).hom.app _)
    _ _ hn _ rfl rfl

variable [FiniteDimensional L L'] [IsGalois L L']

-- the derived functors and their composition isomorphisms are large terms
/-- **The pullback exchange of a finite Galois layer is split by the averaged action on nearby
cycles**: if multiplication by `|Γ|` is invertible on `Lε^* C` and the unit transports along
the `ρ_σ` are the derived Galois actions up to a bijection `e` of `Γ`, the pullback exchange
`α` of `N_{L'} ⟶ N` has a retraction `r` with `|Γ| • (r ≫ α) = ∑ σ, σ_*`, where `σ_*` is the
action of `galoisLayerAut σ` on the nearby cycles. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom'
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso (Fintype.card (L' ≃ₐ[L] L') • 𝟙 (L((N.ε)^*⟦Λ⟧).obj C))]
    (e : (L' ≃ₐ[L] L') ≃ (L' ≃ₐ[L] L'))
    (hact : ∀ σ, derivedUnitTransport Λ (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) (L((N.ε)^*⟦Λ⟧).obj C) =
        (derivedGaloisAction Λ (pullback.fst _ _) (pullbackAction_fst h _ specGaloisAction_comp)
          (e σ)).app (L((N.ε)^*⟦Λ⟧).obj C)) :
    ∃ r, ((N.galoisLayerHom h L').pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      Fintype.card (L' ≃ₐ[L] L') • (r ≫ ((N.galoisLayerHom h L').pullbackExchange Λ).app C) =
        ∑ σ, (N.galoisLayerAut h L' σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) := by
  have key (σ : L' ≃ₐ[L] L') :=
    (congrArg (fun z ↦ (N.galoisLayerExchangeIso h L' Λ C).inv ≫
      L((N.i)^*⟦Λ⟧).map (R((N.j)_*⟦Λ⟧).map z) ≫ (N.galoisLayerExchangeIso h L' Λ C).hom)
        (hact σ)).symm.trans (galoisLayerAut_autAction Λ N h L' σ C).symm
  have base := exists_retraction_pullbackExchange_galoisLayerHom N h L' Λ C
  obtain ⟨r, hr₁, hr₂⟩ := base
  exact ⟨r, hr₁, hr₂.trans ((Equiv.sum_comp e _).symm.trans
    (Finset.sum_congr rfl fun σ _ ↦ key σ))⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
