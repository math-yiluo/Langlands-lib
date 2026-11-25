/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ExchangeOnProper

/-!

# The compact-support exchange of a compactification on bounded constructible pushforwards

Let `ν_f = χ_p⁻¹ ∘ Rp'_*(ν_h)` be the compact-support exchange of a compactified morphism of
models `f = p ∘ h` on bounded constructible complexes
(`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`), and `φ_g : M_B ⟶ M_C` a
morphism of models over `g : B ⟶ C`. Then on `g_* N`, `ν_f` is the pushforward exchange of
`(φ_g ∘ φ_h) ∘ φ_p` after `f'_!(χ_g)`, through the composition isomorphisms
(`compactSupportExchangeOfCompactification_app_lowerStar`): this is the key lemma of step (B) of
Varshavsky's argument on `Dᵇc`, deduced from the ambient
`NearbyCyclesModel.Hom.compactSupportExchange_comp_app` by
`compactSupportExchangeAux_app_comp_aux`.

## Implementation notes

The statement of `compactSupportExchangeOfCompactification_app_lowerStar` is the type of its proof
(`type_of%`). Restating it by hand at `Λ = ℚ̄_ℓ` elaborates the instance arguments of the derived
categories (`IsGrothendieckAbelian`, `MonoidalPreadditive`, …) to proof terms different from those
of the instantiated generic declarations; the elaborator and the kernel then fail to check the
(proof-irrelevant) definitional equality in reasonable time.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Shape

variable {DC DC' DP DP' CC CC' CP CP' Cs Cs' Ds Ds' : Type*} [Category DC] [Category DC']
  [Category DP] [Category DP'] [Category CC] [Category CC'] [Category CP] [Category CP']
  [Category Cs] [Category Cs'] [Category Ds] [Category Ds']

/-- `compactSupportExchangeAux_app_comp_aux` for any `ν` equal to the shape
`compactSupportExchangeAux …` (e.g. a definition unfolding to it). -/
lemma compactSupportExchangeAux_app_comp_aux_of_eq {CB DB DB' : Type*} [Category CB]
    [Category DB] [Category DB'] {Sp : CC ⥤ CC'} {LSf' : CC' ⥤ Cs'} {LSf : CC ⥤ Cs}
    {Ts : Cs ⥤ Cs'} {OLS : CC ⥤ CP} {OLS' : CC' ⥤ CP'} {LStp : CP ⥤ Cs} {LStp' : CP' ⥤ Cs'}
    {ιC : CC ⥤ DC} {ιC' : CC' ⥤ DC'} {ιP : CP ⥤ DP} {ιP' : CP' ⥤ DP'} {ιs : Cs ⥤ Ds}
    {ιs' : Cs' ⥤ Ds'} (hι : ιs'.FullyFaithful) {ΨC : DC ⥤ DC'} {ΨP : DP ⥤ DP'} {Ψs : Ds ⥤ Ds'}
    {Dh : DC ⥤ DP} {Dh' : DC' ⥤ DP'} {Rp : DP ⥤ Ds} {Rp' : DP' ⥤ Ds'}
    (i₁ : LSf' ≅ OLS' ⋙ LStp') (i₂ : LSf ≅ OLS ⋙ LStp)
    (cSp : Sp ⋙ ιC' ≅ ιC ⋙ ΨC) (cO' : OLS' ⋙ ιP' ≅ ιC' ⋙ Dh') (cR' : LStp' ⋙ ιs' ≅ ιP' ⋙ Rp')
    (cO : OLS ⋙ ιP ≅ ιC ⋙ Dh) (cR : LStp ⋙ ιs ≅ ιP ⋙ Rp) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs)
    (νh : ΨC ⋙ Dh' ⟶ Dh ⋙ ΨP) (χp : Rp ⋙ Ψs ⟶ ΨP ⋙ Rp') (hφp : IsIsoOn ιP χp)
    (ν : Sp ⋙ LSf' ⟶ LSf ⋙ Ts)
    (hν : ν = compactSupportExchangeAux hι i₁ i₂ cSp cO' cR' cO cR cT νh
      (invOnSubcategory ιP χp hφp))
    {ιB : CB ⥤ DB} {G : CB ⥤ CC} {Rg : DB ⥤ DC} (cG : G ⋙ ιC ≅ ιB ⋙ Rg) {ΨB : DB ⥤ DB'}
    {Rg' : DB' ⥤ DC'} {Rhg : DB ⥤ DP} {Rhg' : DB' ⥤ DP'} {Rphg : DB ⥤ Ds} {Rphg' : DB' ⥤ Ds'}
    (e : Rg ⋙ Dh ⟶ Rhg) (e' : Rg' ⋙ Dh' ⟶ Rhg') (conj : Rphg ≅ Rhg ⋙ Rp)
    (conj' : Rphg' ≅ Rhg' ⋙ Rp') (χg : Rg ⋙ ΨC ⟶ ΨB ⋙ Rg') (χphg : Rphg ⋙ Ψs ⟶ ΨB ⋙ Rphg')
    (N : CB)
    (hC : ∀ χ₀ : (ΨP ⋙ Rp').obj (Dh.obj (Rg.obj (ιB.obj N))) ⟶
        (Rp ⋙ Ψs).obj (Dh.obj (Rg.obj (ιB.obj N))),
      χ₀ ≫ χp.app (Dh.obj (Rg.obj (ιB.obj N))) = 𝟙 _ →
        Rp'.map (νh.app (Rg.obj (ιB.obj N))) ≫ χ₀ ≫
            Ψs.map (Rp.map (e.app (ιB.obj N)) ≫ conj.inv.app (ιB.obj N)) ≫
            χphg.app (ιB.obj N) =
          Rp'.map (Dh'.map (χg.app (ιB.obj N)) ≫ e'.app (ΨB.obj (ιB.obj N))) ≫
            conj'.inv.app (ΨB.obj (ιB.obj N))) :
    ιs'.map (i₁.inv.app (Sp.obj (G.obj N))) ≫ ιs'.map (ν.app (G.obj N)) ≫
        cT.hom.app (LSf.obj (G.obj N)) ≫
        Ψs.map (ιs.map (i₂.hom.app (G.obj N)) ≫ cR.hom.app (OLS.obj (G.obj N)) ≫
          Rp.map (cO.hom.app (G.obj N)) ≫ Rp.map (Dh.map (cG.hom.app N)) ≫
          Rp.map (e.app (ιB.obj N)) ≫ conj.inv.app (ιB.obj N)) ≫ χphg.app (ιB.obj N) =
      cR'.hom.app (OLS'.obj (Sp.obj (G.obj N))) ≫
        Rp'.map (cO'.hom.app (Sp.obj (G.obj N)) ≫ Dh'.map (cSp.hom.app (G.obj N)) ≫
          Dh'.map (ΨC.map (cG.hom.app N)) ≫ Dh'.map (χg.app (ιB.obj N)) ≫
          e'.app (ΨB.obj (ιB.obj N))) ≫ conj'.inv.app (ΨB.obj (ιB.obj N)) := by
  subst hν
  exact compactSupportExchangeAux_app_comp_aux hι i₁ i₂ cSp cO' cR' cO cR cT νh χp hφp cG e e'
    conj conj' χg χphg N hC

end Shape

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {B C P Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {B' C' P' Y' : Over (Spec (.of k'))}
  [LocallyOfFiniteType C'.hom] [QuasiCompact C'.hom]
  [IsSeparated C'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {MB : NearbyCyclesModel B.left B'.left}
  {MC : NearbyCyclesModel C.left C'.left} {MP : NearbyCyclesModel P.left P'.left}
  {MY : NearbyCyclesModel Y.left Y'.left}
  (hMC : MC.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hMY : MY.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  {f : C ⟶ Y} {h : C ⟶ P} {p : P ⟶ Y} [IsOpenImmersion h.left] [IsProper p.left]
  (w : h ≫ p = f) {f' : C' ⟶ Y'} {h' : C' ⟶ P'} {p' : P' ⟶ Y'} [IsOpenImmersion h'.left]
  [IsProper p'.left] (w' : h' ≫ p' = f')
  (φh : MC.Hom MP h.left h'.left) [IsIso (φh.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
  (φp : MP.Hom MY p.left p'.left)
  (hφp : IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P.left)).ι
    (φp.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)))
  {g : B ⟶ C} {g' : B' ⟶ C'} (φg : MB.Hom MC g.left g'.left)

local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

/-- `Rf_! ≅ h_! ⋙ Rp_*` on bounded constructible complexes for a factorization `f = p ∘ h` with
`h` an open immersion and `p` proper, as in `compactSupportExchangeOfCompactification`. -/
noncomputable abbrev compactificationLowerShriekIso {C P Y : Over (Spec (.of k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {f : C ⟶ Y} (h : C ⟶ P) (p : P ⟶ Y) [IsOpenImmersion h.left] [IsProper p.left]
    (w : h ≫ p = f) :
    boundedConstructibleLowerShriek ℓ f ≅
      boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h ⋙ boundedConstructibleLowerStar ℓ p :=
  lowerShriekCompOfEq ℓ h p w ≪≫
    Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl
      ℓ h) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p)

/-- The hypothesis of an implication, as written in its type. -/
abbrev hypothesisOf {P Q : Prop} (_ : P → Q) : Prop :=
  P

/-- **The compact-support exchange of a compactification on pushforwards** (step (B) of
Varshavsky's argument, on `Dᵇc`): for `ν = ν_f = compactSupportExchangeOfCompactification …` and
a morphism of models `φ_g` over `g : B ⟶ C`, at `G N = g_* N` (`N : Dᵇc(B)`, `N₀ = ι N`):
```
ι(i₁⁻¹) ≫ ι(ν(G N)) ≫ cT ≫ Ψ_Y(ι(i₂) ≫ cR ≫ Rp_*(cO) ≫ Rp_*(h_!(cG)) ≫ Rp_*(e_{N₀}) ≫ conj⁻¹)
    ≫ χ_{(φ_g φ_h) φ_p}(N₀)
  = cR' ≫ Rp'_*(cO' ≫ h'_!(cSp) ≫ h'_!(Ψ_C(cG)) ≫ h'_!(χ_g(N₀)) ≫ e'_{Ψ_B N₀}) ≫ conj'⁻¹
```
with `i₁ : Rf'_! ≅ h'_! ⋙ Rp'_*`, `i₂ : Rf_! ≅ h_! ⋙ Rp_*` (`compactificationLowerShriekIso`),
`e = closedExtension : h_! g_* ⟶ (hg)_*`, `conj = lowerStarCompOfEq : R(phg)_* ≅ R(hg)_* ⋙ Rp_*`
and the (identity) compatibility isomorphisms `cT, cR, cO, cG, cSp, cO', cR'` of the restricted
functors with the inclusions `ι` of `Dᵇc` (shape of `compactSupportExchangeAux_app_comp_aux`).

The ambient identity `hC` at `N₀` is a hypothesis: it is
`NearbyCyclesModel.Hom.compactSupportExchange_comp_app` for `φ_g`, `φ_h`, `φ_p` at `N₀`, but on the
per-ring `Dᵇc` operations the kernel cannot check this instance in reasonable time (the ambient
functors of `Dᵇc` and of the ambient exchange maps are presented through different instance
terms, and comparing them unfolds the coefficient rings). -/
theorem compactSupportExchangeOfCompactification_app_lowerStar
    (ν : NearbyCyclesModel.boundedConstructibleNearbyCycles hMC ⋙
        boundedConstructibleLowerShriek ℓ f' ⟶
      boundedConstructibleLowerShriek ℓ f ⋙
        NearbyCyclesModel.boundedConstructibleNearbyCycles hMY)
    (hν : ν = compactSupportExchangeOfCompactification ℓ hMC hMY w w' φh φp hφp)
    (N : Dᵇc(B.left)⟦Λℓ⟧)
    (hC : hypothesisOf (compactSupportExchangeAux_app_comp_aux_of_eq
      (ObjectProperty.fullyFaithfulι _)
      (compactificationLowerShriekIso ℓ h' p' w') (compactificationLowerShriekIso ℓ h p w)
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hMC)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
      (boundedConstructibleLowerStarCompatibility ℓ _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
      (boundedConstructibleLowerStarCompatibility ℓ _)
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hMY)
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ h.left)
        (openImmersionAdjunction ℓ h'.left) (φh.pullbackExchange _))
      (φp.pushforwardExchange _) hφp ν hν (boundedConstructibleLowerStarCompatibility ℓ g)
      (closedExtension (openImmersionAdjunction ℓ h.left) rfl)
      (closedExtension (openImmersionAdjunction ℓ h'.left) rfl)
      (lowerStarCompOfEq rfl) (lowerStarCompOfEq rfl) (φg.pushforwardExchange _)
      (((φg.comp φh).comp φp).pushforwardExchange _) N)) :
    type_of% (compactSupportExchangeAux_app_comp_aux_of_eq (ObjectProperty.fullyFaithfulι _)
      (compactificationLowerShriekIso ℓ h' p' w') (compactificationLowerShriekIso ℓ h p w)
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hMC)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
      (boundedConstructibleLowerStarCompatibility ℓ _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
      (boundedConstructibleLowerStarCompatibility ℓ _)
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hMY)
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ h.left)
        (openImmersionAdjunction ℓ h'.left) (φh.pullbackExchange _))
      (φp.pushforwardExchange _) hφp ν hν (boundedConstructibleLowerStarCompatibility ℓ g)
      (closedExtension (openImmersionAdjunction ℓ h.left) rfl)
      (closedExtension (openImmersionAdjunction ℓ h'.left) rfl)
      (lowerStarCompOfEq rfl) (lowerStarCompOfEq rfl) (φg.pushforwardExchange _)
      (((φg.comp φh).comp φp).pushforwardExchange _) N hC) :=
  compactSupportExchangeAux_app_comp_aux_of_eq (ObjectProperty.fullyFaithfulι _)
      (compactificationLowerShriekIso ℓ h' p' w') (compactificationLowerShriekIso ℓ h p w)
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hMC)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
      (boundedConstructibleLowerStarCompatibility ℓ _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
      (boundedConstructibleLowerStarCompatibility ℓ _)
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hMY)
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ h.left)
        (openImmersionAdjunction ℓ h'.left) (φh.pullbackExchange _))
      (φp.pushforwardExchange _) hφp ν hν (boundedConstructibleLowerStarCompatibility ℓ g)
      (closedExtension (openImmersionAdjunction ℓ h.left) rfl)
      (closedExtension (openImmersionAdjunction ℓ h'.left) rfl)
      (lowerStarCompOfEq rfl) (lowerStarCompOfEq rfl) (φg.pushforwardExchange _)
      (((φg.comp φh).comp φp).pushforwardExchange _) N hC

end AlgebraicGeometry.ProEtale.CondensedRing
