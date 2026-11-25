/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.TwoSquare
public import WeilConjectures.SmoothPurity.UpperShriekBaseChangeReduction
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerShriekBaseChangeProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperStarReading
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLowerStarExchange

/-!
# The reduction modulo `ℓ` is compatible with proper base change

For a cartesian square `g' ≫ f = f' ≫ g` of separated `k`-schemes of finite type with `f` and
`f'` proper, the canonical comparisons `Rf_! ⋙ red ≅ red ⋙ Rf_!` of the reduction modulo `ℓⁿ`
read on the étale site (`ProEtale.CondensedRing.etaleReductionLowerShriekIso`) are compatible
with compact-support base change
(`ProEtale.CondensedRing.etaleReductionLowerShriekBaseChangeCompatible_of_isProper`), hence
`ProEtale.CondensedRing.etaleReductionProperBaseChangeCompatibleAll`.

The diagram chase is carried out for abstract categories and functors
(`CategoryTheory.comp_hom_app_comp_map_eq_of_isProper`): `Ex_!` is `Ex_*` through `Rf_! ≅ Rf_*`
on both sides, and the reduction is the condensed reduction followed by the étale reading, each
compatible with the pullbacks, the pushforwards and the base change morphisms.

## Implementation notes

The hypotheses of the abstract lemma are instantiated with the concrete lemmas, with the data
written explicitly. The comparison of the condensed reduction with the pushforwards is written
as the `mateEquiv` it is defined as, the compatibility of the condensed reduction with base change
is transported along the `Precoherent Profinite` proofs (`normalize_precoherent`), and the
compatibility of `Ex_!` with `Ex_*` on étale sheaves is used as an identity of natural
transformations: its components carry other instances of the categories of étale sheaves (the
ring structure of `ModuleCat` through `CommRing`, …), which the kernel compares only very slowly.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

variable {AY AX AY' AX' BY BX BY' BX' CY CX CY' CX' : Type*} [Category* AY] [Category* AX]
  [Category* AY'] [Category* AX'] [Category* BY] [Category* BX] [Category* BY'] [Category* BX']
  [Category* CY] [Category* CX] [Category* CY'] [Category* CX']
  {Sh P : AX ⥤ AY} {Sh' P' : AX' ⥤ AY'} {Q : BX ⥤ BY} {Q' : BX' ⥤ BY'}
  {Fs Fp : CX ⥤ CY} {Fs' Fp' : CX' ⥤ CY'}
  {GA : AY ⥤ AY'} {HA : AX ⥤ AX'} {GB : BY ⥤ BY'} {HB : BX ⥤ BX'} {GC : CY ⥤ CY'}
  {HC : CX ⥤ CX'}
  {RY : AY ⥤ BY} {RX : AX ⥤ BX} {RY' : AY' ⥤ BY'} {RX' : AX' ⥤ BX'}
  {ρY : BY ⥤ CY} {ρX : BX ⥤ CX} {ρY' : BY' ⥤ CY'} {ρX' : BX' ⥤ CX'}

/-- The components of a composite comparison `Sh ⋙ RY ⋙ ρY ≅ (RX ⋙ ρX) ⋙ Fs` whose inverse is
the horizontal composite of the squares `inv Pr ≫ (κ⁻¹ ▷ RY)` and `(Pρ ≪≫ ρX ◁ κe⁻¹)⁻¹`. -/
lemma hom_app_of_inv_eq_hComp (κ : Sh ≅ P) (κe : Fs ≅ Fp) (Pr : P ⋙ RY ⟶ RX ⋙ Q) [IsIso Pr]
    (Pρ : Q ⋙ ρY ≅ ρX ⋙ Fp) (γ : Sh ⋙ RY ⋙ ρY ≅ (RX ⋙ ρX) ⋙ Fs)
    (hγ : γ.inv = ((TwoSquare.mk _ _ _ _ (inv Pr ≫ Functor.whiskerRight κ.inv RY)).hComp
      (TwoSquare.mk _ _ _ _ (Pρ ≪≫ Functor.isoWhiskerLeft ρX κe.symm).inv))) (M : AX) :
    γ.hom.app M = ρY.map (RY.map (κ.hom.app M) ≫ Pr.app M) ≫ Pρ.hom.app (RX.obj M) ≫
      κe.inv.app (ρX.obj (RX.obj M)) := by
  rw [← cancel_epi (γ.inv.app M), Iso.inv_hom_id_app, hγ]
  simp only [TwoSquare.hComp, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.assoc, Functor.comp_obj]
  rw [← Functor.map_comp_assoc, Category.assoc, ← Functor.map_comp_assoc RY,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, NatIso.isIso_inv_app,
    IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp [TwoSquare.mk]

/-- **Compatibility of a reduction with compact-support base change, for proper vertical maps**,
abstractly. Consider, for a square with vertical maps `p`, `p'` and horizontal maps `g`, `g'`,
three layers of categories (`A`: integral coefficients, `B`: finite coefficients, `C`: étale
sheaves), the reductions `R : A ⥤ B` and readings `ρ : B ⥤ C`, and:
* in `A`, compact-support pushforwards `Sh ≅ P` (`κ`) with compact-support base change `Ex`
  and base change `BC` related by `κ` (`hEx`);
* in `C`, compact-support pushforwards `Fs ≅ Fp` (`κe`) with compact-support base change `Exe`
  and base change `BCe` related by `κe` (`hEt`);
* the comparisons `Pr` of `R` and `Pρ` of `ρ` with the pushforwards, and the comparisons
  `Riso`, `cρ` and `c` of `R`, `ρ` and `R ⋙ ρ` with the pullbacks (`hc`);
* the compatibilities `hR` of `R` and `hρ` of `ρ` with the base change morphisms (cubes of
  mates).

Then the comparisons `γ : Sh ⋙ R ⋙ ρ ≅ (R ⋙ ρ) ⋙ Fs` whose inverses are the pastes of
`Pr⁻¹ ≫ κ⁻¹` and `(Pρ ≪≫ κe⁻¹)⁻¹` (`hγ`) are compatible with the compact-support base changes. -/
theorem comp_hom_app_comp_map_eq_of_isProper (κ : Sh ≅ P) (κ' : Sh' ≅ P') (κe : Fs ≅ Fp)
    (κe' : Fs' ≅ Fp') (Pr : P ⋙ RY ⟶ RX ⋙ Q) [IsIso Pr] (Pr' : P' ⋙ RY' ⟶ RX' ⋙ Q')
    [IsIso Pr'] (Pρ : Q ⋙ ρY ≅ ρX ⋙ Fp) (Pρ' : Q' ⋙ ρY' ≅ ρX' ⋙ Fp')
    (γ : Sh ⋙ RY ⋙ ρY ≅ (RX ⋙ ρX) ⋙ Fs) (γ' : Sh' ⋙ RY' ⋙ ρY' ≅ (RX' ⋙ ρX') ⋙ Fs')
    (hγ : γ.inv = ((TwoSquare.mk _ _ _ _ (inv Pr ≫ Functor.whiskerRight κ.inv RY)).hComp
      (TwoSquare.mk _ _ _ _ (Pρ ≪≫ Functor.isoWhiskerLeft ρX κe.symm).inv)))
    (hγ' : γ'.inv = ((TwoSquare.mk _ _ _ _ (inv Pr' ≫ Functor.whiskerRight κ'.inv RY')).hComp
      (TwoSquare.mk _ _ _ _ (Pρ' ≪≫ Functor.isoWhiskerLeft ρX' κe'.symm).inv)))
    (Riso : GA ⋙ RY' ≅ RY ⋙ GB) (Riso' : HA ⋙ RX' ≅ RX ⋙ HB) (cρ : GB ⋙ ρY' ≅ ρY ⋙ GC)
    (cρ' : HB ⋙ ρX' ≅ ρX ⋙ HC) (c : GA ⋙ RY' ⋙ ρY' ≅ (RY ⋙ ρY) ⋙ GC)
    (c' : HA ⋙ RX' ⋙ ρX' ≅ (RX ⋙ ρX) ⋙ HC)
    (hc : ∀ M, c.hom.app M = ρY'.map (Riso.hom.app M) ≫ cρ.hom.app (RY.obj M))
    (hc' : ∀ M, c'.hom.app M = ρX'.map (Riso'.hom.app M) ≫ cρ'.hom.app (RX.obj M))
    (Ex : Sh ⋙ GA ⟶ HA ⋙ Sh') (BC : P ⋙ GA ⟶ HA ⋙ P')
    (hEx : Functor.whiskerRight κ.hom GA ≫ BC = Ex ≫ Functor.whiskerLeft HA κ'.hom)
    (BCf : Q ⋙ GB ⟶ HB ⋙ Q')
    (hR : ∀ K, Riso.inv.app (P.obj K) ≫ RY'.map (BC.app K) ≫ Pr'.app (HA.obj K) =
      GB.map (Pr.app K) ≫ BCf.app (RX.obj K) ≫ Q'.map (Riso'.inv.app K))
    (BCe : Fp ⋙ GC ⟶ HC ⋙ Fp')
    (hρ : ∀ K, cρ.inv.app (Q.obj K) ≫ ρY'.map (BCf.app K) ≫ Pρ'.hom.app (HB.obj K) =
      GC.map (Pρ.hom.app K) ≫ BCe.app (ρX.obj K) ≫ Fp'.map (cρ'.inv.app K))
    (Exe : Fs ⋙ GC ⟶ HC ⋙ Fs')
    (hEt : Exe ≫ Functor.whiskerLeft HC κe'.hom = Functor.whiskerRight κe.hom GC ≫ BCe)
    (M : AX) :
    (RY' ⋙ ρY').map (Ex.app M) ≫ γ'.hom.app (HA.obj M) ≫ Fs'.map (c'.hom.app M) =
      c.hom.app (Sh.obj M) ≫ GC.map (γ.hom.app M) ≫ Exe.app ((RX ⋙ ρX).obj M) := by
  have hEt' (K : CX) : GC.map (κe.inv.app K) ≫ Exe.app K = BCe.app K ≫ κe'.inv.app (HC.obj K) := by
    have h := NatTrans.congr_app hEt K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
    rw [← cancel_mono (κe'.hom.app (HC.obj K)), Category.assoc, h, ← GC.map_comp_assoc,
      Iso.inv_hom_id_app, GC.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  have hEx' := NatTrans.congr_app hEx M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hEx'
  have hR' : RY'.map (BC.app M) ≫ Pr'.app (HA.obj M) = Riso.hom.app (P.obj M) ≫
      GB.map (Pr.app M) ≫ BCf.app (RX.obj M) ≫ Q'.map (Riso'.inv.app M) := by
    rw [← hR, Iso.hom_inv_id_app_assoc]
  have hρ' : ρY'.map (BCf.app (RX.obj M)) ≫ Pρ'.hom.app (HB.obj (RX.obj M)) =
      cρ.hom.app (Q.obj (RX.obj M)) ≫ GC.map (Pρ.hom.app (RX.obj M)) ≫
        BCe.app (ρX.obj (RX.obj M)) ≫ Fp'.map (cρ'.inv.app (RX.obj M)) := by
    rw [← hρ, Iso.hom_inv_id_app_assoc]
  rw [hom_app_of_inv_eq_hComp κ' κe' Pr' Pρ' γ' hγ' (HA.obj M),
    hom_app_of_inv_eq_hComp κ κe Pr Pρ γ hγ M, hc, hc']
  have e₁ : ρY'.map (RY'.map (Ex.app M)) ≫
      ρY'.map (RY'.map (κ'.hom.app (HA.obj M)) ≫ Pr'.app (HA.obj M)) =
      ρY'.map (RY'.map (GA.map (κ.hom.app M))) ≫
        ρY'.map (RY'.map (BC.app M) ≫ Pr'.app (HA.obj M)) := by
    rw [← ρY'.map_comp, ← ρY'.map_comp, ← Category.assoc, ← Category.assoc, ← RY'.map_comp,
      ← RY'.map_comp, hEx']
  have e₂ : Fp'.map (ρX'.map (Riso'.inv.app M)) ≫ Fp'.map (ρX'.map (Riso'.hom.app M)) = 𝟙 _ := by
    rw [← Fp'.map_comp, ← ρX'.map_comp, Iso.inv_hom_id_app, ρX'.map_id, Fp'.map_id]
  have e₃ : Fp'.map (cρ'.inv.app (RX.obj M)) ≫ Fp'.map (cρ'.hom.app (RX.obj M)) = 𝟙 _ := by
    rw [← Fp'.map_comp, Iso.inv_hom_id_app, Fp'.map_id]
  have n₁ := κe'.inv.naturality (ρX'.map (Riso'.hom.app M) ≫ cρ'.hom.app (RX.obj M))
  have n₂ := Pρ'.hom.naturality (Riso'.inv.app M)
  have n₃ := Riso.hom.naturality (κ.hom.app M)
  have n₄ := cρ.hom.naturality (RY.map (κ.hom.app M) ≫ Pr.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at n₁ n₂ n₃ n₄
  calc _ = ρY'.map (RY'.map (GA.map (κ.hom.app M))) ≫
        ρY'.map (RY'.map (BC.app M) ≫ Pr'.app (HA.obj M)) ≫ Pρ'.hom.app _ ≫
        Fp'.map (ρX'.map (Riso'.hom.app M) ≫ cρ'.hom.app (RX.obj M)) ≫ κe'.inv.app _ := by
        simp only [Functor.comp_map, Category.assoc]
        rw [← n₁, reassoc_of% e₁]
        rfl
    _ = ρY'.map (RY'.map (GA.map (κ.hom.app M))) ≫ ρY'.map (Riso.hom.app (P.obj M)) ≫
        ρY'.map (GB.map (Pr.app M)) ≫ ρY'.map (BCf.app (RX.obj M)) ≫
        Pρ'.hom.app (HB.obj (RX.obj M)) ≫ Fp'.map (cρ'.hom.app (RX.obj M)) ≫
        κe'.inv.app _ := by
        rw [hR']
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% n₂, reassoc_of% e₂]
    _ = ρY'.map (Riso.hom.app (Sh.obj M)) ≫ cρ.hom.app (RY.obj (Sh.obj M)) ≫
        GC.map (ρY.map (RY.map (κ.hom.app M) ≫ Pr.app M)) ≫ GC.map (Pρ.hom.app (RX.obj M)) ≫
        BCe.app (ρX.obj (RX.obj M)) ≫ κe'.inv.app _ := by
        rw [reassoc_of% hρ', reassoc_of% e₃, ← ρY'.map_comp_assoc, n₃,
          ρY'.map_comp_assoc, ← ρY'.map_comp_assoc (GB.map _), ← GB.map_comp, reassoc_of% n₄]
        rfl
    _ = _ := by
        simp only [Functor.comp_obj, Functor.map_comp, Category.assoc, hEt']

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

set_option maxRecDepth 20000 in
-- the final `exact` unfolds `etaleReduction` to the condensed reduction followed by the étale
-- reading
/-- **The canonical reduction comparisons for proper morphisms are compatible with
compact-support base change** (blueprint `sk-thm-sf-compatibility`, (7), for the coefficient
map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` read on the étale site): for a cartesian square `g' ≫ f = f' ≫ g` with `f`
and `f'` proper, the comparisons `etaleReductionLowerShriekIso` satisfy
`EtaleReductionLowerShriekBaseChangeCompatible`. This is
`CategoryTheory.comp_hom_app_comp_map_eq_of_isProper` for `Ex_!` and `Ex_*` with `𝒪_E`-coefficients
(`boundedConstructibleLowerShriekBaseChange_padicIntegers_of_isProper_mateEquiv`), the
compatibility of the condensed reduction with base change
(`boundedConstructibleIntegersModPowReduction_baseChange`), the compatibility of the étale reading
with base change (`finiteEtaleReading_map_baseChange`) and `Ex_!` and `Ex_*` on étale sheaves
(`Etale.rightDerivedLowerShriekBaseChangeMap_comp_lowerStarIso`). -/
theorem etaleReductionLowerShriekBaseChangeCompatible_of_isProper (sq : IsPullback g' f' f g)
    [IsProper f.left] [IsProper f'.left] :
    haveI := HasCompactification.of_over f
    haveI := HasCompactification.of_over f'
    EtaleReductionLowerShriekBaseChangeCompatible ℓ E n sq (etaleReductionLowerShriekIso ℓ E n f)
      (etaleReductionLowerShriekIso ℓ E n f') := by
  have := HasCompactification.of_over f
  have := HasCompactification.of_over f'
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E n f
    (integersModPowPullUnitCompatible ℓ E n f.left) (integersModPowPullδCompatible ℓ E n f.left)
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E n f'
    (integersModPowPullUnitCompatible ℓ E n f'.left)
    (integersModPowPullδCompatible ℓ E n f'.left)
  intro M
  have : IsIso (mateEquiv
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f)
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).inv) :=
    inferInstanceAs (IsIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n f))
  have : IsIso (mateEquiv
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f')
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f').inv) :=
    inferInstanceAs (IsIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n f'))
  have h := CategoryTheory.comp_hom_app_comp_map_eq_of_isProper
    (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E f')
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f'.left)
    (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f)
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).inv)
    (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f')
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f').inv)
    (finiteEtaleReadingLowerStarIso ℓ E n f) (finiteEtaleReadingLowerStarIso ℓ E n f')
    (etaleReductionLowerShriekIso ℓ E n f) (etaleReductionLowerShriekIso ℓ E n f')
    (by rw [etaleReductionLowerShriekIso, Iso.symm_inv, asIso_hom]; rfl)
    (by rw [etaleReductionLowerShriekIso, Iso.symm_inv, asIso_hom]; rfl)
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g)
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g')
    (finiteEtaleReadingUpperStarIso ℓ E n g) (finiteEtaleReadingUpperStarIso ℓ E n g')
    (etaleReductionUpperStarIso ℓ E n g) (etaleReductionUpperStarIso ℓ E n g')
    (etaleReductionUpperStarIso_hom_app ℓ E n g) (etaleReductionUpperStarIso_hom_app ℓ E n g')
    (boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq)
    (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
      (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
        sq.toCommSq).hom)
    (boundedConstructibleLowerShriekBaseChange_padicIntegers_of_isProper_mateEquiv ℓ E sq)
    (mateEquiv (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f)
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f')
      (boundedConstructiblePullbackSquareComparison (Profinite.integersModPowRingObj ℓ E n) ℓ
        sq.toCommSq).hom)
    (fun K ↦ by
      -- the `Precoherent Profinite` proofs of the two statements differ
      have hR := boundedConstructibleIntegersModPowReduction_baseChange ℓ E n sq.toCommSq K
      revert hR
      normalize_precoherent
      exact id)
    (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
      sq.overLeft.toCommSq)
    (fun K ↦ finiteEtaleReading_map_baseChange ℓ E n sq.toCommSq K)
    (Etale.rightDerivedLowerShriekBaseChangeMap (integersModPowCoeff.{u} ℓ E n) sq.overLeft)
    (Etale.rightDerivedLowerShriekBaseChangeMap_comp_lowerStarIso sq.overLeft) M
  exact h


variable (k) in
/-- **The canonical reduction comparisons for proper morphisms are compatible with
compact-support base change** (`EtaleReductionProperBaseChangeCompatibleAll`):
`etaleReductionLowerShriekBaseChangeCompatible_of_isProper` for the fibre product squares. -/
theorem etaleReductionProperBaseChangeCompatibleAll :
    EtaleReductionProperBaseChangeCompatibleAll ℓ k := by
  intro E S S' Z _ _ _ _ _ _ _ _ _ p _ g
  have : IsProper (Limits.pullback.snd p g).left :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p g).overLeft inferInstance
  exact etaleReductionLowerShriekBaseChangeCompatible_of_isProper ℓ E.1 1
    (IsPullback.of_hasPullback p g)

end AlgebraicGeometry.ProEtale.CondensedRing
