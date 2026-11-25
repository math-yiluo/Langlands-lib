/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Integral

/-!

# The compact-support exchange of the fixed locus

For the specialization data determined by the support
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofSupportExchange`), with
`Ψ_F = Lι'^* Ψ_C Rι_*` and `β_c` the mate of a compact-support exchange `ν_c`, the
compact-support exchange `ν_d : Rd'_! Ψ_F ⟶ Ψ_X Rd_!` whose mate is `β_d`
(`fixedLocusCompactSupportExchange`) is computed explicitly: it is
```
Rd'_! Lι'^* Ψ_C Rι_* ≅ LΔ'^* Rc'_! Ψ_C Rι_* --ν_c--> LΔ'^* Ψ_{X×X} Rc_! Rι_*
  --α_Δ--> Ψ_X LΔ^* Rc_! Rι_* ≅ Ψ_X Rd_! Lι^* Rι_* --ε--> Ψ_X Rd_!
```
with `α_Δ` the mate of `χ_Δ` and the base change isomorphisms of the fixed squares. This is the
`ν`-form of blueprint `sec-Base-change-for-nearby-cycles` (6), proved first for arbitrary
adjunctions (`CategoryTheory.mateEquiv_symm_eq_fixedSquareCompactSupportExchange`).

## Main statements

In namespace `ProEtale.CondensedRing.Correspondence.TraceSpecialization`:
- `fixedLocusCompactSupportExchange_eq`: the explicit form of `ν_d`;
- `fixedLocusToPointCompactSupportExchange_app`: the same for the composite `ν_F` of `ν_d`
  with `ν_X`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {DC DF DX DP DC' DF' DX' DP' : Type*} [Category DC] [Category DF] [Category DX]
  [Category DP] [Category DC'] [Category DF'] [Category DX'] [Category DP']
  {cL : DC ⥤ DP} {cR : DP ⥤ DC} {dL : DF ⥤ DX} {dR : DX ⥤ DF}
  {ιU : DC ⥤ DF} {ιS : DF ⥤ DC} {ΔU : DP ⥤ DX} {ΔS : DX ⥤ DP}
  {cL' : DC' ⥤ DP'} {cR' : DP' ⥤ DC'} {dL' : DF' ⥤ DX'} {dR' : DX' ⥤ DF'}
  {ιU' : DC' ⥤ DF'} {ιS' : DF' ⥤ DC'} {ΔU' : DP' ⥤ DX'} {ΔS' : DX' ⥤ DP'}
  (adjc : cL ⊣ cR) (adjd : dL ⊣ dR) (adjι : ιU ⊣ ιS) (adjΔ : ΔU ⊣ ΔS)
  (adjc' : cL' ⊣ cR') (adjd' : dL' ⊣ dR') (adjι' : ιU' ⊣ ιS') (adjΔ' : ΔU' ⊣ ΔS')
  (BC : cL ⋙ ΔU ≅ ιU ⋙ dL) (BC' : cL' ⋙ ΔU' ≅ ιU' ⋙ dL')
  {ΨC : DC ⥤ DC'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
  (νc : ΨC ⋙ cL' ⟶ cL ⋙ ΨP) (αΔ : ΨP ⋙ ΔU' ⟶ ΔU ⋙ ΨX)

/-- The compact-support exchange `d'_! ι'^* Ψ_C ι_* ⟶ Ψ_X d_!` of the fixed square:
`d'_! ι'^* ≅ Δ'^* c'_!`, then `ν_c`, `α_Δ`, `Δ^* c_! ≅ d_! ι^*` and the counit of `ι^* ⊣ ι_*`. -/
@[simps]
def fixedSquareCompactSupportExchange : (ιS ⋙ ΨC ⋙ ιU') ⋙ dL' ⟶ dL ⋙ ΨX where
  app N := BC'.inv.app (ΨC.obj (ιS.obj N)) ≫ ΔU'.map (νc.app (ιS.obj N)) ≫
    αΔ.app (cL.obj (ιS.obj N)) ≫ ΨX.map (BC.hom.app (ιS.obj N)) ≫
    ΨX.map (dL.map (adjι.counit.app N))
  naturality N N' g := by
    have h₁ := BC'.inv.naturality (ΨC.map (ιS.map g))
    have h₂ := νc.naturality (ιS.map g)
    have h₃ := αΔ.naturality (cL.map (ιS.map g))
    have h₄ := BC.hom.naturality (ιS.map g)
    have h₅ := adjι.counit.naturality g
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at h₁ h₂ h₃ h₄ h₅ ⊢
    rw [reassoc_of% h₁, ← ΔU'.map_comp_assoc, h₂, ΔU'.map_comp_assoc, reassoc_of% h₃]
    simp only [Category.assoc, ← ΨX.map_comp]
    rw [reassoc_of% h₄, ← dL.map_comp, h₅, dL.map_comp]


/-- **The compact-support exchange of the fixed locus** (the `ν`-form of blueprint
`sec-Base-change-for-nearby-cycles` (6)): if `β_d` is `ι'^*` of
`B' ∘ c'^!(χ_Δ) ∘ β_c(Δ_*) ∘ Ψ_C(B⁻¹)` followed by the counit of `ι'^* ⊣ ι'_*`, where `β_c`,
`χ_Δ` are the mates of `ν_c`, `α_Δ` and `B`, `B'` the conjugates of `BC⁻¹`, `BC'⁻¹`, then the
mate `ν_d` of `β_d` is `fixedSquareCompactSupportExchange`, that is,
`ν_d(N) = Ψ_X d_!(ε_ι) ∘ Ψ_X(BC) ∘ α_Δ(c_! ι_* N) ∘ Δ'^* ν_c(ι_* N) ∘ BC'⁻¹`. -/
theorem mateEquiv_symm_eq_fixedSquareCompactSupportExchange
    (βd : dR ⋙ (ιS ⋙ ΨC ⋙ ιU') ⟶ ΨX ⋙ dR')
    (hβd : ∀ M, βd.app M = ιU'.map (ΨC.map
      ((conjugateIsoEquiv (adjc.comp adjΔ) (adjι.comp adjd) BC.symm).inv.app M) ≫
        (mateEquiv adjc adjc' νc).app (ΔS.obj M) ≫ cR'.map ((mateEquiv adjΔ adjΔ' αΔ).app M) ≫
        (conjugateIsoEquiv (adjc'.comp adjΔ') (adjι'.comp adjd') BC'.symm).hom.app
          (ΨX.obj M)) ≫ adjι'.counit.app _) :
    (mateEquiv adjd adjd').symm βd = fixedSquareCompactSupportExchange adjι BC BC' νc αΔ := by
  rw [Equiv.symm_apply_eq]
  ext M
  apply (adjd'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit, hβd]
  have hB := conjugateEquiv_counit (adjι.comp adjd) (adjc.comp adjΔ) BC.hom M
  have hB' := conjugateEquiv_counit (adjc'.comp adjΔ') (adjι'.comp adjd') BC'.inv (ΨX.obj M)
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_counit_app] at hB hB'
  simp only [conjugateIsoEquiv_apply_inv, conjugateIsoEquiv_apply_hom, Iso.symm_inv,
    Iso.symm_hom, Functor.map_comp, Category.assoc, fixedSquareCompactSupportExchange_app,
    Functor.comp_obj]
  have hn {A B : DC'} (g : A ⟶ B) : dL'.map (ιU'.map g) ≫ BC'.inv.app B =
      BC'.inv.app A ≫ ΔU'.map (cL'.map g) := BC'.inv.naturality g
  have h₃ : ΔU'.map (cL'.map (cR'.map ((mateEquiv adjΔ adjΔ' αΔ).app M))) ≫
      ΔU'.map (adjc'.counit.app (ΔS'.obj (ΨX.obj M))) =
      ΔU'.map (adjc'.counit.app _) ≫ ΔU'.map ((mateEquiv adjΔ adjΔ' αΔ).app M) := by
    rw [← ΔU'.map_comp, ← ΔU'.map_comp]
    exact congrArg ΔU'.map (adjc'.counit.naturality _)
  have h₄ : ΔU'.map (cL'.map ((mateEquiv adjc adjc' νc).app (ΔS.obj M))) ≫
      ΔU'.map (adjc'.counit.app _) =
      ΔU'.map (νc.app _) ≫ ΔU'.map (ΨP.map (adjc.counit.app (ΔS.obj M))) := by
    rw [← ΔU'.map_comp, ← ΔU'.map_comp, mateEquiv_counit]
  have h₅ := mateEquiv_counit adjΔ adjΔ' αΔ M
  have h₆ {A B : DC} (g : A ⟶ B) : ΔU'.map (cL'.map (ΨC.map g)) ≫ ΔU'.map (νc.app B) =
      ΔU'.map (νc.app A) ≫ ΔU'.map (ΨP.map (cL.map g)) := by
    rw [← ΔU'.map_comp, ← ΔU'.map_comp]
    exact congrArg ΔU'.map (νc.naturality g)
  have h₇ {A B : DP} (g : A ⟶ B) : ΔU'.map (ΨP.map g) ≫ αΔ.app B =
      αΔ.app A ≫ ΨX.map (ΔU.map g) := αΔ.naturality g
  simp only [Functor.comp_obj] at h₅
  rw [hB', reassoc_of% hn, reassoc_of% hn, reassoc_of% hn, reassoc_of% h₃, reassoc_of% h₄, h₅,
    reassoc_of% h₆, reassoc_of% h₇, reassoc_of% h₇]
  simp only [← ΨX.map_comp]
  rw [hB]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.Correspondence.TraceSpecialization

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}
  (ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (χΔ : boundedConstructibleLowerStar ℓ (diag X) ⋙ ΨXX ⟶
    ΨX ⋙ boundedConstructibleLowerStar ℓ (diag X'))
  (νc : ΨC ⋙ boundedConstructibleLowerShriek ℓ c'.support ⟶
    boundedConstructibleLowerShriek ℓ c.support ⋙ ΨXX)

/-- **The compact-support exchange `ν_d` of the fixed locus** determined by the support, for
`β_c` the mate of `ν_c`: `ν_d(N)` is
`Rd'_! Lι'^* Ψ_C Rι_* N ≅ LΔ'^* Rc'_! Ψ_C Rι_* N ⟶ LΔ'^* Ψ_{X×X} Rc_! Rι_* N`
`⟶ Ψ_X LΔ^* Rc_! Rι_* N ≅ Ψ_X Rd_! Lι^* Rι_* N ⟶ Ψ_X Rd_! N`
(`ν_c`, then the mate `α_Δ` of `χ_Δ`, the base change of the fixed square and the counit). -/
theorem fixedLocusCompactSupportExchange_eq :
    fixedLocusCompactSupportExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ
        (exceptionalExchange ℓ c.support c'.support νc) =
      fixedSquareCompactSupportExchange (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
        F.lowerShriekBaseChangeIso F'.lowerShriekBaseChangeIso νc
        ((CategoryTheory.mateEquiv
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X'))).symm χΔ) :=
  mateEquiv_symm_eq_fixedSquareCompactSupportExchange
    (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction ℓ F.d) _
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
    (boundedConstructibleUpperShriekAdjunction ℓ c'.support)
    (boundedConstructibleUpperShriekAdjunction ℓ F'.d)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X')) _ _ _ _ _ fun M => by
      simp only [fixedLocusExceptionalExchange, fixedSquareExchange, fourExchange_app,
        Equiv.apply_symm_apply]
      rfl

/-- `fixedLocusCompactSupportExchange_eq` read through the composition with `ν_X`: the
compact-support exchange `ν_F` of the structure maps of the fixed loci, for `β_c` the mate of
`ν_c`, in terms of `ν_c`, `α_Δ` and `ν_X`. -/
theorem fixedLocusToPointCompactSupportExchange_app
    {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)
    (N : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (fixedLocusToPointCompactSupportExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ
        (exceptionalExchange ℓ c.support c'.support νc) νX).app N =
      (lowerShriekCompOfEq ℓ F'.d (toPoint X') (comp_toPoint F'.d)).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          ((fixedSquareCompactSupportExchange
            (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
            F.lowerShriekBaseChangeIso F'.lowerShriekBaseChangeIso νc
            ((CategoryTheory.mateEquiv
              (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
              (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X'))).symm χΔ)).app
            N) ≫
          νX.app _ ≫
            Ψpt.map ((lowerShriekCompOfEq ℓ F.d (toPoint X) (comp_toPoint F.d)).inv.app N) := by
  rw [fixedLocusToPointCompactSupportExchange, fixedLocusCompactSupportExchange_eq,
    compExchange_app]

end AlgebraicGeometry.ProEtale.CondensedRing.Correspondence.TraceSpecialization
