/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverDescent
public import WeilConjectures.WeilSheaf.Dual

/-!
# Continuity of the monodromy from universal covers

Let `Y` be a connected scheme with universal covers on which lisse sheaves are free, and let
`M` be the monodromy of lisse sheaves obtained from them. The matrix coefficients
`g ↦ φ(ρ(g) v)` of the monodromy representation on a stalk `G_t` are continuous on
`π₁(Y, t)` (`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy_continuous_rep`).

Indeed, write `φ` as the evaluation pairing with an element `d` of the stalk of the dual
`G^∨`, and extend `d` and `v` to sections `d̃` of `G^∨` and `ṽ` of `G` over the universal cover
`Ỹ_t`. The pairing of the pullbacks of `d̃` and `ṽ` along the two projections of
`Ỹ_t ×_Y Ỹ_t` is a section of `ℚ̄_ℓ`, that is a locally finite continuous function `c` on
`Ỹ_t ×_Y Ỹ_t`, and `φ(ρ(g) v)` is the value of `c` at the point `(t̃, g⁻¹ t̃)`, which depends
continuously on `g` (`AlgebraicGeometry.Scheme.UniversalCovers.continuous_graph`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] {Z : Scheme.{u}}

/-- The value of an element of the stalk `Γ(Spec K, t^* ℚ̄_ℓ)` of the constant sheaf at a point
with values in a field: its function `Spec K → ℚ̄_ℓ`, evaluated at the closed point. -/
noncomputable def stalkUnitVal (t : Spec (.of K) ⟶ Z)
    (x : (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((t)^*[_].obj (adicConstantSheaf l Z))) :
    PadicAlgCl l :=
  (((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId _)).hom.app
    (adicConstantSheaf l (Spec (.of K)))).hom
      (((Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l t)).hom x)).down.1
    (IsLocalRing.closedPoint K)

/-- The value of stalk elements of the constant sheaf is `ℚ̄_ℓ`-linear. -/
lemma stalkUnitVal_smul (t : Spec (.of K) ⟶ Z) (c : PadicAlgCl l)
    (x : (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((t)^*[_].obj (adicConstantSheaf l Z))) :
    stalkUnitVal t ((ULift.up c : ULift.{u + 1} (PadicAlgCl l)) • x) = c * stalkUnitVal t x := by
  simp only [stalkUnitVal, map_smul]
  rfl

/-- The value of a section of `ℚ̄_ℓ` given by a function `c`, restricted to a point. -/
lemma stalkUnitVal_resOver {T Y : Scheme.{u}} {z : Spec (.of K) ⟶ T} {q : T ⟶ Y}
    {t : Spec (.of K) ⟶ Y} (e : z ≫ q = t)
    (a : (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((q)^*[_].obj (adicConstantSheaf l Y)))
    (c : PadicAlgCl.locallyFiniteFunctions l T)
    (hc : ((Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l q)).hom a =
      adicConstantGlobalSection c) :
    stalkUnitVal t (((resOver _ z e).app (adicConstantSheaf l Y)).hom a) =
      c.1 (z.base (IsLocalRing.closedPoint K)) := by
  subst e
  have h₁ := upperStarAdicConstantSheafHom_comp l z q
  have h₂ : (upperStarFactor (WeilCoefficients.{u} l) (rfl : z ≫ q = z ≫ q)).inv.app
      (adicConstantSheaf l Y) ≫ upperStarAdicConstantSheafHom l (z ≫ q) =
      (z)^*[_].map (upperStarAdicConstantSheafHom l q) ≫ upperStarAdicConstantSheafHom l z := by
    rw [upperStarFactor_rfl, ← h₁, Iso.inv_hom_id_app_assoc]
  have n := congrArg (fun φ ↦ φ.hom a) ((globalSectionsToUpperStar (WeilCoefficients.{u} l)
    z).naturality (upperStarAdicConstantSheafHom l q))
  simp only [Functor.comp_map, ModuleCat.hom_comp, LinearMap.comp_apply] at n
  have key : ((Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l (z ≫ q))).hom
      (((resOver _ z rfl).app (adicConstantSheaf l Y)).hom a) =
      adicConstantGlobalSection (PadicAlgCl.locallyFiniteFunctionsComp l z.base.hom c) := by
    have h₃ := congrArg (fun φ ↦ φ.hom a)
      (show (globalSectionsToUpperStar (WeilCoefficients.{u} l) z).app _ ≫
        (Sheaf.Γ _ _).map ((upperStarFactor (WeilCoefficients.{u} l)
          (rfl : z ≫ q = z ≫ q)).inv.app (adicConstantSheaf l Y)) ≫
        (Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l (z ≫ q)) =
        (globalSectionsToUpperStar (WeilCoefficients.{u} l) z).app _ ≫
        (Sheaf.Γ _ _).map ((z)^*[_].map (upperStarAdicConstantSheafHom l q)) ≫
        (Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l z) by
        rw [← Functor.map_comp, h₂, Functor.map_comp])
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₃
    rw [resOver_app]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    refine h₃.trans ?_
    rw [hc] at n
    erw [← n]
    exact globalSectionsToUpperStar_adicConstantGlobalSection z c
  rw [stalkUnitVal, key, adicConstantGlobalSection, ← ModuleCat.comp_apply, Iso.inv_hom_id_app]
  rfl

/-- The unit section of the stalk of `ℚ̄_ℓ` has value `1`. -/
lemma stalkUnitVal_oneGlobalSection (t : Spec (.of K) ⟶ Z) :
    stalkUnitVal t (((globalSectionsToUpperStar _ t).app (adicConstantSheaf l Z)).hom
      (oneGlobalSection Z)) = 1 := by
  rw [stalkUnitVal, show ((Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l t)).hom
    (((globalSectionsToUpperStar _ t).app (adicConstantSheaf l Z)).hom (oneGlobalSection Z)) =
      oneGlobalSection (Spec (.of K)) from
    Γ_map_adicUpperStarUnitIso_globalSectionsToUpperStar_oneGlobalSection t,
    oneGlobalSection_eq, adicConstantGlobalSection, ← ModuleCat.comp_apply, Iso.inv_hom_id_app]
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.UniversalCovers

open ProEtale FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  {U : Scheme.UniversalCovers Y Ω}

/-- The transport along the inverse loop is the inverse of the transport. -/
lemma transport_inv_hom (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (g : Aut (fiber t)) :
    (U.transport (g⁻¹ : Aut (fiber t)).asIso).hom = (U.transport g.asIso).inv := by
  have h := U.transport_trans g.asIso (g⁻¹ : Aut (fiber t)).asIso
  rw [Aut.inv_asIso, Iso.self_symm_id, U.transport_refl] at h
  exact (Iso.hom_comp_eq_id (U.transport g.asIso)).1 (congrArg Iso.hom h).symm

variable (hU : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
  Nonempty ((U.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)))

include hU in
/-- **The monodromy representations are continuous** (blueprint:
`proposition-lattices-representations-normal-scheme`): `φ(ρ(g) v)` is the value of a continuous
function on `Ỹ_t ×_Y Ỹ_t` at the point `(t̃, g⁻¹ t̃)`. -/
theorem lisseMonodromy_continuous_rep (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (G : LisseSheaf l Y)
    (φ : Module.Dual (PadicAlgCl l) (LisseMonodromy.StalkSpace t G))
    (v : LisseMonodromy.StalkSpace t G) :
    Continuous fun g : Aut (fiber t) ↦ φ ((U.lisseMonodromy hU).rep t G g v) := by
  have hD : IsAdicLisseSheaf ((AdicSheaf.ihom G.obj).obj (AdicSheaf.unit l Y)) :=
    (show IsAdicLisseSheaf G.obj from G.property).ihom (isAdicLisseSheaf_adicConstantSheaf Y)
  let D : LisseSheaf l Y := ⟨_, hD⟩
  let u₀ := ((globalSectionsToUpperStar _ t).app (adicConstantSheaf l Y)).hom (oneGlobalSection Y)
  let ψ : (stalkFunctor l t).obj G.obj.X →ₗ[ULift.{u + 1} (PadicAlgCl l)]
      (stalkFunctor l t).obj (AdicSheaf.unit l Y).X :=
    { toFun w := (ULift.up (φ w) : ULift.{u + 1} (PadicAlgCl l)) • u₀
      map_add' w w' := by
        change (ULift.up (φ (w + w')) : ULift.{u + 1} (PadicAlgCl l)) • u₀ = _
        rw [map_add, ← add_smul]
        rfl
      map_smul' c w := by
        change (ULift.up (φ (c • w)) : ULift.{u + 1} (PadicAlgCl l)) • u₀ =
          c • ((ULift.up (φ w) : ULift.{u + 1} (PadicAlgCl l)) • u₀)
        rw [show φ (c • w) = c.down * φ w from φ.map_smul c.down w, smul_smul]
        rfl }
  obtain ⟨d, hd⟩ := (G.property.bijective_evaluationPairing t).2 ψ
  have hpd := isIso_ptRes_app hU t D
  have hpv := isIso_ptRes_app hU t G
  let d' := (inv ((U.ptRes l t).app D.obj.X)).hom d
  have hd' : ((U.ptRes l t).app D.obj.X).hom d' = d := by
    rw [← ModuleCat.comp_apply, IsIso.inv_hom_id]; rfl
  let s := (inv ((U.ptRes l t).app G.obj.X)).hom v
  have hs : ((U.ptRes l t).app G.obj.X).hom s = v := by
    rw [← ModuleCat.comp_apply, IsIso.inv_hom_id]; rfl
  let a := Mod.evaluationPairing
    ((pullback.fst (U.proj t) (U.proj t) ≫ U.proj t)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _)
    G.obj (AdicSheaf.unit l Y)
    (((resOver _ (pullback.fst (U.proj t) (U.proj t)) rfl).app D.obj.X).hom d')
    (((resOver _ (pullback.snd (U.proj t) (U.proj t)) pullback.condition.symm).app
      G.obj.X).hom s)
  let c : PadicAlgCl.locallyFiniteFunctions l (pullback (U.proj t) (U.proj t) : Scheme.{u}) :=
    (((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId _)).hom.app
      (adicConstantSheaf l _)).hom (((Sheaf.Γ _ _).map
        (upperStarAdicConstantSheafHom l (pullback.fst (U.proj t) (U.proj t) ≫ U.proj t))).hom
          a)).down
  have hc : ((Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l
      (pullback.fst (U.proj t) (U.proj t) ≫ U.proj t))).hom a = adicConstantGlobalSection c := by
    rw [adicConstantGlobalSection, ULift.up_down, ← ModuleCat.comp_apply, Iso.hom_inv_id_app]
    rfl
  let z : Aut (fiber t) → (Spec (.of (AlgebraicClosure Ω)) ⟶ pullback (U.proj t) (U.proj t)) :=
    fun g ↦ pullback.lift (U.pt t) (U.pt t ≫ (U.transport g.asIso).inv)
      (by rw [Category.assoc, U.transport_inv_proj])
  have key (g : Aut (fiber t)) :
      φ ((U.lisseMonodromy hU).rep t G g v) =
        c.1 ((z g).base (IsLocalRing.closedPoint (AlgebraicClosure Ω))) := by
    have hz₁ : z g ≫ pullback.fst (U.proj t) (U.proj t) = U.pt t := pullback.lift_fst _ _ _
    have hz₂ : z g ≫ pullback.snd (U.proj t) (U.proj t) = U.pt t ≫ (U.transport g.asIso).inv :=
      pullback.lift_snd _ _ _
    have hzq : z g ≫ pullback.fst (U.proj t) (U.proj t) ≫ U.proj t = t := by
      rw [← Category.assoc, hz₁, U.pt_proj]
    have e₁ : ((monoIso hU g.asIso).hom.app G).hom v =
        ((resOver _ (z g) hzq).app G.obj.X).hom
          (((resOver _ (pullback.snd (U.proj t) (U.proj t)) pullback.condition.symm).app
            G.obj.X).hom s) := by
      rw [← hs, monoIso_hom_app_ptRes_apply, transportRes_hom_app, ptRes_app]
      have r₁ := congrArg (fun φ ↦ φ.hom s) (resOver_comp _ (U.pt t) (U.transport g.asIso).inv
        (U.pt_proj t) (U.transport_inv_proj g.asIso)
        (by rw [Category.assoc, U.transport_inv_proj, U.pt_proj]) G.obj.X)
      have r₂ := congrArg (fun φ ↦ φ.hom s) (resOver_comp _ (z g)
        (pullback.snd (U.proj t) (U.proj t)) hzq pullback.condition.symm
        (by rw [hz₂, Category.assoc, U.transport_inv_proj, U.pt_proj]) G.obj.X)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at r₁ r₂
      rw [r₁, r₂, resOver_congr _ hz₂.symm]
    have e₂ : d = ((resOver _ (z g) hzq).app D.obj.X).hom
        (((resOver _ (pullback.fst (U.proj t) (U.proj t)) rfl).app D.obj.X).hom d') := by
      rw [← hd', ptRes_app]
      have r := congrArg (fun φ ↦ φ.hom d') (resOver_comp _ (z g)
        (pullback.fst (U.proj t) (U.proj t)) hzq rfl (by rw [hz₁, U.pt_proj]) D.obj.X)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at r
      rw [r, resOver_congr _ hz₁]
    have e₃ : Mod.evaluationPairing (stalkFunctor l t) G.obj (AdicSheaf.unit l Y) d
        (((monoIso hU g.asIso).hom.app G).hom v) =
          ((resOver _ (z g) hzq).app (adicConstantSheaf l Y)).hom a := by
      rw [e₁, e₂]
      exact evaluationPairing_natTrans (resOver _ (z g) hzq) G.obj (AdicSheaf.unit l Y) _ _
    have hψ := LinearMap.congr_fun hd (((monoIso hU g.asIso).hom.app G).hom v)
    calc φ ((U.lisseMonodromy hU).rep t G g v)
        = φ ((U.lisseMonodromy hU).rep t G g v) * stalkUnitVal t u₀ := by
          rw [stalkUnitVal_oneGlobalSection, mul_one]
      _ = stalkUnitVal t (ψ (((monoIso hU g.asIso).hom.app G).hom v)) :=
          (stalkUnitVal_smul t _ u₀).symm
      _ = stalkUnitVal t (((resOver _ (z g) hzq).app (adicConstantSheaf l Y)).hom a) := by
          rw [← hψ, e₃]
      _ = c.1 ((z g).base (IsLocalRing.closedPoint (AlgebraicClosure Ω))) :=
          stalkUnitVal_resOver hzq a c hc
  have hz : (fun g ↦ (z g).base (IsLocalRing.closedPoint (AlgebraicClosure Ω))) =
      (fun g' : Aut (fiber t) ↦ (pullback.lift (f := U.proj t) (g := U.proj t) (U.pt t)
        (U.pt t ≫ (U.transport g'.asIso).hom) (by rw [Category.assoc, U.transport_proj]) :
          Spec (.of (AlgebraicClosure Ω)) ⟶ pullback (U.proj t) (U.proj t)).base
          (IsLocalRing.closedPoint (AlgebraicClosure Ω))) ∘ fun g ↦ g⁻¹ := by
    funext g
    simp only [Function.comp_apply, z, transport_inv_hom]
  simp_rw [key]
  rw [show (fun g ↦ c.1 ((z g).base (IsLocalRing.closedPoint (AlgebraicClosure Ω)))) =
    c.1 ∘ fun g ↦ (z g).base (IsLocalRing.closedPoint (AlgebraicClosure Ω)) from rfl, hz]
  exact c.1.continuous.comp ((U.continuous_graph t _).comp continuous_inv)

end AlgebraicGeometry.Scheme.UniversalCovers
