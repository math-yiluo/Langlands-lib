/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# The exceptional base change map at the unit and composition (A1', step 3)

For stacked squares `f : X ⟶ Y`, `g : Y ⟶ Z` over `k₁` with base changes `f'`, `g'` over `k₂`
and compact-support base change isomorphisms `bcf`, `bcg`, `bcfg` compatible with the composition
isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`, the exceptional base change map at the unit of the
composite (`ProEtale.CondensedRing.smoothUnitBaseChange`) is the pasting of the mate of `bcf` at
`Rg^! ℚ̄_ℓ` and of `Rf'^!` applied to the exceptional base change map of `g`, through the
composition isomorphisms `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` (`smoothUnitBaseChange_comp`). Hence
invertibility passes from the factors to the composite (`isIso_smoothUnitBaseChange_comp`):
this is the pasting step of the local proof of `IsIso smoothUnitBaseChange` for a smooth
non-proper `f` (Zariski-locally `f = g ∘ j ∘ p` with `g` étale, `j` an open immersion and `p`
the projection of a projective space).

The generic statement is `CategoryTheory.Adjunction.unitBaseChange_comp`, a reformulation of
`CategoryTheory.Adjunction.mateEquiv_inv_comp` in terms of `unitBaseChange`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

section Generic

variable {Cx Cy Cz Cx' Cy' Cz' : Type*} [Category* Cx] [Category* Cy] [Category* Cz]
  [Category* Cx'] [Category* Cy'] [Category* Cz']
  {Lf : Cx ⥤ Cy} {Rf : Cy ⥤ Cx} (adjf : Lf ⊣ Rf) {Lg : Cy ⥤ Cz} {Rg : Cz ⥤ Cy} (adjg : Lg ⊣ Rg)
  {Lh : Cx ⥤ Cz} {Rh : Cz ⥤ Cx} (adjh : Lh ⊣ Rh)
  {Lf' : Cx' ⥤ Cy'} {Rf' : Cy' ⥤ Cx'} (adjf' : Lf' ⊣ Rf')
  {Lg' : Cy' ⥤ Cz'} {Rg' : Cz' ⥤ Cy'} (adjg' : Lg' ⊣ Rg')
  {Lh' : Cx' ⥤ Cz'} {Rh' : Cz' ⥤ Cx'} (adjh' : Lh' ⊣ Rh')
  {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'} {Gc : Cz ⥤ Cz'}
  (Exf : Lf ⋙ Gb ⟶ Ga ⋙ Lf') [IsIso Exf] (Exg : Lg ⋙ Gc ⟶ Gb ⋙ Lg') [IsIso Exg]
  (Exh : Lh ⋙ Gc ⟶ Ga ⋙ Lh') [IsIso Exh] (e : Lh ≅ Lf ⋙ Lg) (e' : Lh' ≅ Lf' ⋙ Lg')
  (hEx : ExchangeCompCompatible Exf Exg Exh e e')
  (ρ : Rh ≅ Rg ⋙ Rf)
  (hρ : ∀ K : Cz, Lg.map (Lf.map (ρ.hom.app K)) ≫ Lg.map (adjf.counit.app _) ≫
    adjg.counit.app K = e.inv.app _ ≫ adjh.counit.app K)
  (ρ' : Rh' ≅ Rg' ⋙ Rf')
  (hρ' : ∀ K : Cz', Lg'.map (Lf'.map (ρ'.hom.app K)) ≫ Lg'.map (adjf'.counit.app _) ≫
    adjg'.counit.app K = e'.inv.app _ ≫ adjh'.counit.app K)
  {U : Cz} {U' : Cz'} (ε : Gc.obj U ⟶ U')

include hEx hρ hρ' in
/-- **Pasting of exceptional base change maps at the unit**: for compatible exchange maps of
stacked squares, `unitBaseChange` of the composite is, through the composition isomorphisms
`ρ : Rh ≅ Rg ⋙ Rf` and `ρ'` of the right adjoints, the mate of `Exf` at `Rg U` followed by
`Rf'` of `unitBaseChange` of the second square. -/
theorem unitBaseChange_comp :
    unitBaseChange adjh adjh' Exh ε =
      Ga.map (ρ.hom.app U) ≫ (mateEquiv adjf adjf' (inv Exf)).app (Rg.obj U) ≫
        Rf'.map (unitBaseChange adjg adjg' Exg ε) ≫ ρ'.inv.app U' := by
  have hξ : ∀ M : Cx, (inv Exh).app M ≫ Gc.map (e.hom.app M) =
      e'.hom.app (Ga.obj M) ≫ Lg'.map ((inv Exf).app M) ≫ (inv Exg).app (Lf.obj M) :=
    fun M ↦ by
      have h := hEx.comp M
      rw [← cancel_epi (Exh.app M)]
      simp only [NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc, Functor.map_inv]
      rw [← cancel_mono (Exg.app _), ← cancel_mono (Lg'.map (Exf.app M))]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact h
  have key := mateEquiv_inv_comp adjf adjg adjh adjf' adjg' adjh' (inv Exf) (inv Exg) (inv Exh)
    e e' hξ ρ.hom hρ ρ'.hom hρ' U
  calc unitBaseChange adjh adjh' Exh ε
      = (mateEquiv adjh adjh' (inv Exh)).app U ≫ Rh'.map ε := rfl
    _ = (mateEquiv adjh adjh' (inv Exh)).app U ≫ ρ'.hom.app (Gc.obj U) ≫
          (Rg' ⋙ Rf').map ε ≫ ρ'.inv.app U' := by
        rw [NatIso.naturality_2]
    _ = Ga.map (ρ.hom.app U) ≫ (mateEquiv adjf adjf' (inv Exf)).app (Rg.obj U) ≫
          Rf'.map ((mateEquiv adjg adjg' (inv Exg)).app U) ≫
          (Rg' ⋙ Rf').map ε ≫ ρ'.inv.app U' := by
        rw [← reassoc_of% key]
    _ = _ := by
        simp only [unitBaseChange, Functor.comp_map, Functor.map_comp, Category.assoc]

include hEx hρ hρ' in
/-- Invertibility of the pasted exceptional base change map at the unit, in terms of the factors:
`unitBaseChange` of the composite is invertible if and only if the mate of `Exf` at `Rg U`
followed by `Rf'(unitBaseChange_g)` is. -/
theorem isIso_unitBaseChange_comp_iff :
    IsIso (unitBaseChange adjh adjh' Exh ε) ↔
      IsIso ((mateEquiv adjf adjf' (inv Exf)).app (Rg.obj U) ≫
        Rf'.map (unitBaseChange adjg adjg' Exg ε)) := by
  rw [unitBaseChange_comp adjf adjg adjh adjf' adjg' adjh' Exf Exg Exh e e' hEx ρ hρ ρ' hρ' ε,
    isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff]

include hEx hρ hρ' in
/-- If the mate of `Exf` is invertible at `Rg U` and `unitBaseChange` of the second square is
invertible, so is `unitBaseChange` of the composite. -/
theorem isIso_unitBaseChange_comp
    [IsIso ((mateEquiv adjf adjf' (inv Exf)).app (Rg.obj U))]
    [IsIso (unitBaseChange adjg adjg' Exg ε)] :
    IsIso (unitBaseChange adjh adjh' Exh ε) :=
  (isIso_unitBaseChange_comp_iff adjf adjg adjh adjf' adjg' adjh' Exf Exg Exh e e' hEx ρ hρ ρ'
    hρ' ε).2 inferInstance

end Generic

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The counit compatibility of the composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` -/

section CompCounit

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl`) is compatible with the
counits of `Rf_! ⊣ Rf^!`, `Rg_! ⊣ Rg^!` and `R(f ≫ g)_! ⊣ R(f ≫ g)^!` through
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`. -/
lemma lowerShriek_map_upperShriekComp_padicAlgCl_hom_app_comp_counit
    (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ g).map ((boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g).hom.app K)) ≫
      (boundedConstructibleLowerShriek ℓ g).map
        ((boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ g).counit.app K =
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv.app _ ≫
      (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g)).counit.app K := by
  have h := conjugateEquiv_counit (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction ℓ g))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).symm.hom K
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj, Iso.symm_hom] at h
  exact h

end CompCounit

/-! ### Pasting of exceptional base change maps at the unit -/

section Paste

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y Z : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {X' Y' Z' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left} {πZ : Z'.left ⟶ Z.left}
  (bcf : boundedConstructibleLowerShriek l f ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f')
  (bcg : boundedConstructibleLowerShriek l g ⋙ boundedConstructibleUpperStarOfMap l πZ ≅
    boundedConstructibleUpperStarOfMap l πY ⋙ boundedConstructibleLowerShriek l g')
  (bcfg : boundedConstructibleLowerShriek l (f ≫ g) ⋙ boundedConstructibleUpperStarOfMap l πZ ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l (f' ≫ g'))
  (hbc : Adjunction.ExchangeCompCompatible bcf.hom bcg.hom bcfg.hom
    (boundedConstructibleLowerShriekComp_padicAlgCl l f g)
    (boundedConstructibleLowerShriekComp_padicAlgCl l f' g'))
  (e : (boundedConstructibleUpperStarOfMap l πZ).obj (𝟙_ _) ⟶ 𝟙_ _)

/-- The mate `πY^* Rf^! ⟶ Rf'^! πX^*` of a compact-support base change isomorphism `bcf`. -/
abbrev upperShriekMateOfMap :
    boundedConstructibleUpperShriek l f ⋙ boundedConstructibleUpperStarOfMap l πX ⟶
      boundedConstructibleUpperStarOfMap l πY ⋙ boundedConstructibleUpperShriek l f' :=
  (mateEquiv (boundedConstructibleUpperShriekAdjunction l f)
    (boundedConstructibleUpperShriekAdjunction l f') (inv bcf.hom))

include hbc in
/-- **Pasting of exceptional base change maps at the unit (step 3)**: for stacked squares with
compatible compact-support base change isomorphisms, `smoothUnitBaseChange` of the composite is,
through the composition isomorphisms `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`, the mate of `bcf` at
`Rg^! ℚ̄_ℓ` followed by `Rf'^!` of `smoothUnitBaseChange` of `g`. -/
theorem smoothUnitBaseChange_comp :
    smoothUnitBaseChange l (f ≫ g) (f' ≫ g') bcfg e =
      (boundedConstructibleUpperStarOfMap l πX).map
          ((boundedConstructibleUpperShriekComp_padicAlgCl l f g).hom.app (𝟙_ _)) ≫
        (upperShriekMateOfMap l f f' bcf).app ((boundedConstructibleUpperShriek l g).obj (𝟙_ _)) ≫
        (boundedConstructibleUpperShriek l f').map (smoothUnitBaseChange l g g' bcg e) ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl l f' g').inv.app (𝟙_ _) :=
  Adjunction.unitBaseChange_comp (boundedConstructibleUpperShriekAdjunction l f)
    (boundedConstructibleUpperShriekAdjunction l g)
    (boundedConstructibleUpperShriekAdjunction l (f ≫ g))
    (boundedConstructibleUpperShriekAdjunction l f')
    (boundedConstructibleUpperShriekAdjunction l g')
    (boundedConstructibleUpperShriekAdjunction l (f' ≫ g'))
    bcf.hom bcg.hom bcfg.hom _ _ hbc
    (boundedConstructibleUpperShriekComp_padicAlgCl l f g)
    (lowerShriek_map_upperShriekComp_padicAlgCl_hom_app_comp_counit l f g)
    (boundedConstructibleUpperShriekComp_padicAlgCl l f' g')
    (lowerShriek_map_upperShriekComp_padicAlgCl_hom_app_comp_counit l f' g') e

include hbc in
/-- Invertibility of the exceptional base change map at the unit of a composite, in terms of the
factors. -/
theorem isIso_smoothUnitBaseChange_comp_iff :
    IsIso (smoothUnitBaseChange l (f ≫ g) (f' ≫ g') bcfg e) ↔
      IsIso ((upperShriekMateOfMap l f f' bcf).app
          ((boundedConstructibleUpperShriek l g).obj (𝟙_ _)) ≫
        (boundedConstructibleUpperShriek l f').map (smoothUnitBaseChange l g g' bcg e)) :=
  Adjunction.isIso_unitBaseChange_comp_iff (boundedConstructibleUpperShriekAdjunction l f)
    (boundedConstructibleUpperShriekAdjunction l g)
    (boundedConstructibleUpperShriekAdjunction l (f ≫ g))
    (boundedConstructibleUpperShriekAdjunction l f')
    (boundedConstructibleUpperShriekAdjunction l g')
    (boundedConstructibleUpperShriekAdjunction l (f' ≫ g'))
    bcf.hom bcg.hom bcfg.hom _ _ hbc
    (boundedConstructibleUpperShriekComp_padicAlgCl l f g)
    (lowerShriek_map_upperShriekComp_padicAlgCl_hom_app_comp_counit l f g)
    (boundedConstructibleUpperShriekComp_padicAlgCl l f' g')
    (lowerShriek_map_upperShriekComp_padicAlgCl_hom_app_comp_counit l f' g') e

include hbc in
/-- **Step 3 of the local proof of `IsIso smoothUnitBaseChange`**: if the mate of `bcf` is
invertible at `Rg^! ℚ̄_ℓ` (for instance `f` étale or an open immersion, step 2) and the
exceptional base change map at the unit of `g` is invertible (for instance `g` smooth proper
along a weakly étale base change), then so is the one of `f ≫ g`. -/
theorem isIso_smoothUnitBaseChange_comp
    [IsIso ((upperShriekMateOfMap l f f' bcf).app
      ((boundedConstructibleUpperShriek l g).obj (𝟙_ _)))]
    [IsIso (smoothUnitBaseChange l g g' bcg e)] :
    IsIso (smoothUnitBaseChange l (f ≫ g) (f' ≫ g') bcfg e) :=
  (isIso_smoothUnitBaseChange_comp_iff l f g f' g' bcf bcg bcfg hbc e).2 inferInstance

/-- The pasted compact-support base change isomorphism of a composite, from those of the
factors: `R(f ≫ g)_! ⋙ πZ^* ≅ Rf_! ⋙ Rg_! ⋙ πZ^* ≅ Rf_! ⋙ πY^* ⋙ Rg'_! ≅ πX^* ⋙ Rf'_! ⋙ Rg'_!
≅ πX^* ⋙ R(f' ≫ g')_!`. -/
def pasteLowerShriekBaseChange :
    boundedConstructibleLowerShriek l (f ≫ g) ⋙ boundedConstructibleUpperStarOfMap l πZ ≅
      boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l (f' ≫ g') :=
  Functor.isoWhiskerRight (boundedConstructibleLowerShriekComp_padicAlgCl l f g) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ bcg ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight bcf _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekComp_padicAlgCl l f' g').symm

/-- The pasted base change isomorphism is compatible with the composition isomorphisms. -/
lemma exchangeCompCompatible_pasteLowerShriekBaseChange :
    Adjunction.ExchangeCompCompatible bcf.hom bcg.hom
      (pasteLowerShriekBaseChange l f g f' g' bcf bcg).hom
      (boundedConstructibleLowerShriekComp_padicAlgCl l f g)
      (boundedConstructibleLowerShriekComp_padicAlgCl l f' g') := ⟨fun M ↦ by
  simp [pasteLowerShriekBaseChange]⟩

/-- Step 3 for the pasted compact-support base change isomorphism. -/
theorem isIso_smoothUnitBaseChange_paste
    [IsIso ((upperShriekMateOfMap l f f' bcf).app
      ((boundedConstructibleUpperShriek l g).obj (𝟙_ _)))]
    [IsIso (smoothUnitBaseChange l g g' bcg e)] :
    IsIso (smoothUnitBaseChange l (f ≫ g) (f' ≫ g')
      (pasteLowerShriekBaseChange l f g f' g' bcf bcg) e) :=
  isIso_smoothUnitBaseChange_comp l f g f' g' bcf bcg _
    (exchangeCompCompatible_pasteLowerShriekBaseChange l f g f' g' bcf bcg) e

end Paste

end AlgebraicGeometry.ProEtale.CondensedRing
