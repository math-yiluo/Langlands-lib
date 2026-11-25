/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCompose
public import WeilConjectures.CategoryTheory.Adjunction.MateFixedSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.Specialization.Basic

/-!

# Trace specialization from compact-support exchanges

Let `c` be an endocorrespondence over `k` (the generic fibre) and `c'` one over `k'` (the special
fibre), with fixed loci `F` and `F'`, and let `Ψ` be specialization functors between the bounded
constructible derived categories of the corresponding schemes. In the nearby-cycles formalism
(blueprint `prose-E-15`) the exceptional exchanges `β_f : Ψ Rf^! ⟶ Rf'^! Ψ` and
the dualizing maps `θ_X : Ψ ω_X ⟶ ω_{X'}` are built from the *compact-support exchanges*

```
ν_f : Rf'_! Ψ ⟶ Ψ Rf_!
```

as their mates for `Rf_! ⊣ Rf^!` (`ProEtale.CondensedRing.exceptionalExchange`), and
`θ_X = β_{a_X}(ℚ̄_ℓ)` read through the specialization unit `σ : ℚ̄_ℓ ≅ Ψ ℚ̄_ℓ` of the point
(`ProEtale.CondensedRing.dualizingExchange`). The proper exchanges `χ_f` are the mates of the
pullback exchanges `α_f : f'^* Ψ ⟶ Ψ f^*` for `f^* ⊣ Rf_*`.

The two coherences of the trace class (blueprint `sec-Base-change-for-nearby-cycles` (4) and (6))
follow formally from two properties of `ν`, which in the nearby-cycles formalism hold because `ν`
is compatible with composition and is the inverse of `χ` for proper maps:

* if `ν_{a_F}` is the composite of `ν_d` and `ν_{a_X}` (for `a_F = a_X ∘ d`), then
  `θ_F = d'^! θ_X ∘ β_d(ω_X)` (`ProEtale.CondensedRing.dualizingExchange_eq_comp`, (4));
* if `ν_ι`, `ν_Δ` are inverse to `χ_ι`, `χ_Δ` and the composites of `ν` along `cι = Δd` agree,
  then the fixed-square identity `Rι'_* β_d ∘ χ_ι ∘ Ψ_C(B) = B' ∘ c'^!(χ_Δ) ∘ β_c(RΔ_*)` holds
  (`CategoryTheory.fixedSquare_of_compactSupportExchange`, (6)).

Together with the unit identity, this builds the specialization data `TraceSpecialization` of
blueprint `proposition-specialization-trace-class` out of pullback and compact-support exchanges
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofCompactSupportExchange`).

## Main definitions

- `ProEtale.CondensedRing.exceptionalExchange`: the exceptional exchange `β_f`, the mate of a
  compact-support exchange `ν_f`.
- `ProEtale.CondensedRing.dualizingExchange`: the dualizing map `θ_X = β_{a_X}(ℚ̄_ℓ)`.
- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofCompactSupportExchange`: the
  specialization data built from pullback and compact-support exchanges.

## Main statements

- `ProEtale.CondensedRing.dualizingExchange_eq_comp`: the composition law
  `θ_F = d'^! θ_X ∘ β_d(ω_X)` (blueprint `lemma-compatibilities-base-change-maps` (3)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

section Exchange

variable (ℓ) {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The *exceptional exchange* `β_f : Ψ_X Rf^! ⟶ Rf'^! Ψ_Y` of a compact-support exchange
`ν_f : Rf'_! Ψ_X ⟶ Ψ_Y Rf_!` (blueprint `prose-E-15` (4)): its mate for the
adjunctions `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, that is, the `Rf'_! ⊣ Rf'^!` adjoint of
`Rf'_! Ψ_X Rf^! ⟶ Ψ_Y Rf_! Rf^! ⟶ Ψ_Y`. -/
noncomputable def exceptionalExchange (f : X ⟶ Y) (f' : X' ⟶ Y')
    {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ΨY : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ν : ΨX ⋙ boundedConstructibleLowerShriek ℓ f' ⟶
      boundedConstructibleLowerShriek ℓ f ⋙ ΨY) :
    boundedConstructibleUpperShriek ℓ f ⋙ ΨX ⟶
      ΨY ⋙ boundedConstructibleUpperShriek ℓ f' :=
  mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f') ν

/-- The *dualizing map* `θ_X : Ψ_X ω_X ⟶ ω_{X'}` of a compact-support exchange
`ν : Ra_{X'!} Ψ_X ⟶ Ψ_s Ra_{X!}` for the structure maps (blueprint `prose-E-15`
(5)): the exceptional exchange `β_{a_X}(ℚ̄_ℓ) : Ψ_X Ra_X^! ℚ̄_ℓ ⟶ Ra_{X'}^! Ψ_s ℚ̄_ℓ`, followed
by the inverse of the specialization unit `σ_s : ℚ̄_ℓ ≅ Ψ_s ℚ̄_ℓ` of the point. -/
noncomputable def dualizingExchange
    {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]
    (ν : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt) :
    ΨX.obj (dualizingComplex' ℓ X) ⟶ dualizingComplex' ℓ X' :=
  (exceptionalExchange ℓ (toPoint X) (toPoint X') ν).app (𝟙_ _) ≫
    (boundedConstructibleUpperShriek ℓ (toPoint X')).map
      (inv σpt)

end Exchange

section Composition

variable (ℓ) {F X P : Over (Spec (.of k))} [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {F' X' P' : Over (Spec (.of k'))} [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom]
  [IsSeparated F'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {ΨF : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(F'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- **Composition law for exceptional exchanges** (blueprint
`lemma-compatibilities-base-change-maps` (3), `β_{ad} = d'^! β_a ∘ β_d(a^!)`): if the
compact-support exchange `ν` of `d ≫ a` is the composite of those of `d` and `a` under the
composition isomorphisms of the lower shrieks, then the exceptional exchange of `d ≫ a` is the
composite of those of `d` and `a` under the composition isomorphisms of the exceptional inverse
images. -/
theorem exceptionalExchange_comp_app (d : F ⟶ X) (a : X ⟶ P) (d' : F' ⟶ X') (a' : X' ⟶ P')
    {ΨP : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(P'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (νd : ΨF ⋙ boundedConstructibleLowerShriek ℓ d' ⟶
      boundedConstructibleLowerShriek ℓ d ⋙ ΨX)
    (νa : ΨX ⋙ boundedConstructibleLowerShriek ℓ a' ⟶
      boundedConstructibleLowerShriek ℓ a ⋙ ΨP)
    (ν : ΨF ⋙ boundedConstructibleLowerShriek ℓ (d' ≫ a') ⟶
      boundedConstructibleLowerShriek ℓ (d ≫ a) ⋙ ΨP)
    (h : ∀ M, ν.app M ≫ ΨP.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ d a).hom.app M) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ d' a').hom.app (ΨF.obj M) ≫
        (boundedConstructibleLowerShriek ℓ a').map (νd.app M) ≫
          νa.app ((boundedConstructibleLowerShriek ℓ d).obj M))
    (N : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (exceptionalExchange ℓ (d ≫ a) (d' ≫ a') ν).app N ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ d' a').hom.app (ΨP.obj N) =
      ΨF.map ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ d a).hom.app N) ≫
        (exceptionalExchange ℓ d d' νd).app
          ((boundedConstructibleUpperShriek ℓ a).obj N) ≫
          (boundedConstructibleUpperShriek ℓ d').map
            ((exceptionalExchange ℓ a a' νa).app N) :=
  mateEquiv_app_comp_conjugateIsoEquiv_hom_app _ _ _ _ _ _ _ _ νd νa ν h N

/-- The composition isomorphism `R(a)_! ≅ Rd_! ⋙ R(b)_!` for a morphism `a` equal to `d ≫ b`: the
composition isomorphism of `d ≫ b`, transported along `d ≫ b = a`. -/
noncomputable def lowerShriekCompOfEq {aF : F ⟶ P} (d : F ⟶ X) (b : X ⟶ P) (w : d ≫ b = aF) :
    boundedConstructibleLowerShriek ℓ aF ≅
      boundedConstructibleLowerShriek ℓ d ⋙
        boundedConstructibleLowerShriek ℓ b :=
  eqToIso (by rw [← w]) ≪≫ boundedConstructibleLowerShriekComp_padicAlgCl ℓ d b

@[simp]
lemma lowerShriekCompOfEq_rfl (d : F ⟶ X) (b : X ⟶ P) :
    lowerShriekCompOfEq ℓ d b rfl = boundedConstructibleLowerShriekComp_padicAlgCl ℓ d b := by
  simp [lowerShriekCompOfEq]

/-- The composition isomorphism `Rd^! Rb^! ℚ̄_ℓ ≅ R(a)^! ℚ̄_ℓ` for a morphism `a` equal to
`d ≫ b`: the composition isomorphism of `d ≫ b` at the unit, transported along `d ≫ b = a`. -/
noncomputable def upperShriekUnitCompOfEq {aF : F ⟶ P} (d : F ⟶ X) (b : X ⟶ P)
    (w : d ≫ b = aF) :
    (boundedConstructibleUpperShriek ℓ d).obj
        ((boundedConstructibleUpperShriek ℓ b).obj (𝟙_ _)) ≅
      (boundedConstructibleUpperShriek ℓ aF).obj (𝟙_ _) :=
  ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ d b).app (𝟙_ _)).symm ≪≫
    eqToIso (by rw [w])

@[simp]
lemma upperShriekUnitCompOfEq_rfl (d : F ⟶ X) (b : X ⟶ P) :
    upperShriekUnitCompOfEq ℓ d b rfl =
      ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ d b).app (𝟙_ _)).symm := by
  simp [upperShriekUnitCompOfEq]

/-- The composition isomorphism of the dualizing complexes is `upperShriekUnitCompOfEq`. -/
lemma dualizingComplexComp_eq_upperShriekUnitCompOfEq (d : F ⟶ X) :
    dualizingComplexComp ℓ d = upperShriekUnitCompOfEq ℓ d (toPoint X) (comp_toPoint d) :=
  rfl

variable {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

/-- `dualizingExchange_eq_comp` for an arbitrary morphism `a_F` equal to `d ≫ a_X`. -/
private lemma dualizingExchange_eq_comp_aux (d : F ⟶ X) (d' : F' ⟶ X') {aF : F ⟶ point k}
    {aF' : F' ⟶ point k'} (w : d ≫ toPoint X = aF) (w' : d' ≫ toPoint X' = aF')
    (νd : ΨF ⋙ boundedConstructibleLowerShriek ℓ d' ⟶
      boundedConstructibleLowerShriek ℓ d ⋙ ΨX)
    (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)
    (νF : ΨF ⋙ boundedConstructibleLowerShriek ℓ aF' ⟶
      boundedConstructibleLowerShriek ℓ aF ⋙ Ψpt)
    (h : ∀ M, νF.app M ≫ Ψpt.map ((lowerShriekCompOfEq ℓ d (toPoint X) w).hom.app M) =
      (lowerShriekCompOfEq ℓ d' (toPoint X') w').hom.app (ΨF.obj M) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          (νd.app M) ≫
          νX.app ((boundedConstructibleLowerShriek ℓ d).obj M)) :
    (exceptionalExchange ℓ aF aF' νF).app (𝟙_ _) ≫
        (boundedConstructibleUpperShriek ℓ aF').map (inv σpt) =
      ΨF.map (upperShriekUnitCompOfEq ℓ d (toPoint X) w).inv ≫
        (exceptionalExchange ℓ d d' νd).app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleUpperShriek ℓ d').map
          (dualizingExchange ℓ σpt νX) ≫ (upperShriekUnitCompOfEq ℓ d' (toPoint X') w').hom := by
  subst w w'
  simp only [lowerShriekCompOfEq_rfl] at h
  simp only [upperShriekUnitCompOfEq_rfl, Iso.symm_inv, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
  have hc := exceptionalExchange_comp_app ℓ d (toPoint X) d' (toPoint X') νd νX νF h (𝟙_ _)
  have hn := (boundedConstructibleUpperShriekComp_padicAlgCl ℓ d' (toPoint X')).hom.naturality
    (inv σpt)
  rw [dualizingExchange, Functor.map_comp]
  rw [← cancel_mono ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ d' (toPoint X')).hom.app
    (𝟙_ _))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hn, reassoc_of% hc]
  simp only [Functor.comp_map, Functor.comp_obj, Category.comp_id]

/-- **The composition law for the dualizing maps** (blueprint
`lemma-compatibilities-base-change-maps` (3), `θ_F = d'^! θ_X ∘ β_d(ω_X)`;
`sec-Base-change-for-nearby-cycles` (4)): if the compact-support exchange of `a_F` is the composite
of those of `d : F ⟶ X` and of `a_X`, then the dualizing map of `F` is
`Ψ_F ω_F ≅ Ψ_F Rd^! ω_X ⟶ Rd'^! Ψ_X ω_X ⟶ Rd'^! ω_{X'} ≅ ω_{F'}`. -/
theorem dualizingExchange_eq_comp (d : F ⟶ X) (d' : F' ⟶ X')
    (νd : ΨF ⋙ boundedConstructibleLowerShriek ℓ d' ⟶
      boundedConstructibleLowerShriek ℓ d ⋙ ΨX)
    (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)
    (νF : ΨF ⋙ boundedConstructibleLowerShriek ℓ (toPoint F') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F) ⋙ Ψpt)
    (h : ∀ M, νF.app M ≫
        Ψpt.map ((lowerShriekCompOfEq ℓ d (toPoint X) (comp_toPoint d)).hom.app M) =
      (lowerShriekCompOfEq ℓ d' (toPoint X') (comp_toPoint d')).hom.app (ΨF.obj M) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          (νd.app M) ≫
          νX.app ((boundedConstructibleLowerShriek ℓ d).obj M)) :
    dualizingExchange ℓ σpt νF = ΨF.map (dualizingComplexComp ℓ d).inv ≫
      (exceptionalExchange ℓ d d' νd).app (dualizingComplex' ℓ X) ≫
      (boundedConstructibleUpperShriek ℓ d').map
        (dualizingExchange ℓ σpt νX) ≫ (dualizingComplexComp ℓ d').hom := by
  rw [dualizingComplexComp_eq_upperShriekUnitCompOfEq,
    dualizingComplexComp_eq_upperShriekUnitCompOfEq]
  exact dualizingExchange_eq_comp_aux ℓ σpt d d' (comp_toPoint d) (comp_toPoint d') νd νX νF h

end Composition
namespace Correspondence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}

section FixedSquare

variable
    {ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ΨF : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (αι : ΨC ⋙ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι ⋙ ΨF)
    (αΔ : ΨXX ⋙ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X') ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X) ⋙ ΨX)
    (νc : ΨC ⋙ boundedConstructibleLowerShriek ℓ c'.support ⟶
      boundedConstructibleLowerShriek ℓ c.support ⋙ ΨXX)
    (νd : ΨF ⋙ boundedConstructibleLowerShriek ℓ F'.d ⟶
      boundedConstructibleLowerShriek ℓ F.d ⋙ ΨX)
    (νι : ΨF ⋙ boundedConstructibleLowerShriek ℓ F'.ι ⟶
      boundedConstructibleLowerShriek ℓ F.ι ⋙ ΨC)
    (νΔ : ΨX ⋙ boundedConstructibleLowerShriek ℓ (diag X') ⟶
      boundedConstructibleLowerShriek ℓ (diag X) ⋙ ΨXX)

/-- **The fixed-square identity from compact-support exchanges** (blueprint
`sec-Base-change-for-nearby-cycles` (6)): if `ν_ι`, `ν_Δ` are inverse to the proper exchanges
`χ_ι`, `χ_Δ` (the mates of `α_ι`, `α_Δ`) and the compact-support exchanges are compatible with
the composition `cι = Δd`, then
`Rι'_* β_d ∘ χ_ι ∘ Ψ_C(B) = B' ∘ c'^!(χ_Δ) ∘ β_c(RΔ_*)`. That is, for `M ∈ Dᵇc(X)` the square
```
Ψ_C c^! RΔ_* M --Ψ_C(B)--> Ψ_C Rι_* d^! M --χ_ι--> Rι'_* Ψ_F d^! M
      |                                                   |
   β_c(RΔ_* M)                                       Rι'_* β_d
      v                                                   v
c'^! Ψ_{X×X} RΔ_* M --c'^!(χ_Δ)--> c'^! RΔ'_* Ψ_X M --B'--> Rι'_* d'^! Ψ_X M
```
commutes. -/
theorem fixedSquare_of_compactSupportExchange_app
    (hι : ∀ Q, ΨC.map ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι).hom.app Q) ≫
      (CategoryTheory.mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι) αι).app Q ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F'.ι).inv.app (ΨF.obj Q) ≫
      νι.app Q =
        𝟙 (ΨC.obj ((boundedConstructibleLowerShriek ℓ F.ι).obj Q)))
    (hΔ : ∀ Q, νΔ.app Q ≫
      ΨXX.map ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X)).hom.app Q) ≫
      (CategoryTheory.mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X')) αΔ).app Q ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X')).inv.app (ΨX.obj Q) =
        𝟙 ((boundedConstructibleLowerShriek ℓ (diag X')).obj
          (ΨX.obj Q)))
    (hcomp : Functor.whiskerRight νι
        (boundedConstructibleLowerShriek ℓ c'.support) ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ νc ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ
          F.isPullback.w).hom ΨXX =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ΨF
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F'.isPullback.w).hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight νd
          (boundedConstructibleLowerShriek ℓ (diag X')) ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ νΔ ≫ (Functor.associator _ _ _).inv)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ΨC.map (F.upperShriekLowerStarIso.app M).hom ≫
        (CategoryTheory.mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι) αι).app _ ≫
        (boundedConstructibleLowerStar ℓ F'.ι).map
          ((exceptionalExchange ℓ F.d F'.d νd).app M) =
      (exceptionalExchange ℓ c.support c'.support νc).app _ ≫
        (boundedConstructibleUpperShriek ℓ c'.support).map
          ((CategoryTheory.mateEquiv
            (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
            (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X')) αΔ).app M) ≫
        (F'.upperShriekLowerStarIso.app (ΨX.obj M)).hom := by
  have hBC := boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ F.isPullback
  have hBC' := boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ F'.isPullback
  refine fixedSquare_of_compactSupportExchange _ _ _ _ _ _ _ _
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F'.ι)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X'))
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.isPullback.w)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F'.isPullback.w)
    F.lowerShriekBaseChangeIso F'.lowerShriekBaseChangeIso αι αΔ νc νd νι νΔ ?_ ?_
    ?_ ?_ ?_ M
  · exact hBC
  · exact hBC'
  · exact hι
  · exact hΔ
  · exact hcomp

end FixedSquare

/-- The *specialization data built from exchange maps* (blueprint
`proposition-specialization-trace-class`, `prose-E-15`): given specialization functors
`Ψ_C, Ψ_F, Ψ_X, Ψ_{X×X}` and `Ψ_s` of the point, specialization units `σ_C`, `σ_F` and an
invertible unit `σ_s`, pullback exchanges `α_ι`, `α_Δ` and compact-support exchanges
`ν_c, ν_d, ν_ι, ν_Δ` and `ν_X, ν_F` (for the structure maps), the specialization data has
* the proper exchanges `χ_ι`, `χ_Δ`, the mates of `α_ι`, `α_Δ`;
* the exceptional exchanges `β_c`, `β_d`, the mates of `ν_c`, `ν_d`
  (`ProEtale.CondensedRing.exceptionalExchange`);
* the dualizing maps `θ_X`, `θ_F` of `ν_X`, `ν_F` (`ProEtale.CondensedRing.dualizingExchange`).

Its coherences follow from the unit identity `hunit`, from the compatibility `hθ` of the
compact-support exchanges with the composition `a_F = a_X ∘ d`
(`ProEtale.CondensedRing.dualizingExchange_eq_comp`), and from the facts that `ν_ι`, `ν_Δ` are
inverse to `χ_ι`, `χ_Δ` (`hι`, `hΔ`) and that the compact-support exchanges are compatible with
the composition `cι = Δd` (`hcomp`; `CategoryTheory.fixedSquare_of_compactSupportExchange`). -/
noncomputable def TraceSpecialization.ofCompactSupportExchange
    (ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ΨF : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (σC : 𝟙_ _ ⟶ ΨC.obj (𝟙_ _)) (σF : 𝟙_ _ ⟶ ΨF.obj (𝟙_ _))
    (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]
    (αι : ΨC ⋙ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι ⋙ ΨF)
    (αΔ : ΨXX ⋙ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X') ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X) ⋙ ΨX)
    (hunit : σC ≫ ΨC.map ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).unit.app
        (𝟙_ _)) ≫
        (CategoryTheory.mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι) αι).app _ =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ F'.ι).map
          ((Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι)).inv ≫ σF ≫
            ΨF.map (Functor.Monoidal.εIso
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)).hom))
    (νc : ΨC ⋙ boundedConstructibleLowerShriek ℓ c'.support ⟶
      boundedConstructibleLowerShriek ℓ c.support ⋙ ΨXX)
    (νd : ΨF ⋙ boundedConstructibleLowerShriek ℓ F'.d ⟶
      boundedConstructibleLowerShriek ℓ F.d ⋙ ΨX)
    (νι : ΨF ⋙ boundedConstructibleLowerShriek ℓ F'.ι ⟶
      boundedConstructibleLowerShriek ℓ F.ι ⋙ ΨC)
    (νΔ : ΨX ⋙ boundedConstructibleLowerShriek ℓ (diag X') ⟶
      boundedConstructibleLowerShriek ℓ (diag X) ⋙ ΨXX)
    (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)
    (νF : ΨF ⋙ boundedConstructibleLowerShriek ℓ
        (toPoint F'.F) ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F.F) ⋙ Ψpt)
    (hι : ∀ Q, ΨC.map ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι).hom.app Q) ≫
      (CategoryTheory.mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι) αι).app Q ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F'.ι).inv.app (ΨF.obj Q) ≫
      νι.app Q =
        𝟙 (ΨC.obj ((boundedConstructibleLowerShriek ℓ F.ι).obj Q)))
    (hΔ : ∀ Q, νΔ.app Q ≫
      ΨXX.map ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X)).hom.app Q) ≫
      (CategoryTheory.mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X')) αΔ).app Q ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X')).inv.app (ΨX.obj Q) =
        𝟙 ((boundedConstructibleLowerShriek ℓ (diag X')).obj
          (ΨX.obj Q)))
    (hcomp : Functor.whiskerRight νι
        (boundedConstructibleLowerShriek ℓ c'.support) ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ νc ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ
          F.isPullback.w).hom ΨXX =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ΨF
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F'.isPullback.w).hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight νd
          (boundedConstructibleLowerShriek ℓ (diag X')) ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ νΔ ≫ (Functor.associator _ _ _).inv)
    (hθ : ∀ M, νF.app M ≫
        Ψpt.map ((lowerShriekCompOfEq ℓ F.d (toPoint X) (comp_toPoint F.d)).hom.app M) =
      (lowerShriekCompOfEq ℓ F'.d (toPoint X') (comp_toPoint F'.d)).hom.app (ΨF.obj M) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          (νd.app M) ≫
          νX.app ((boundedConstructibleLowerShriek ℓ F.d).obj M)) :
    c.TraceSpecialization F c' F' where
  ΨC := ΨC
  ΨF := ΨF
  ΨX := ΨX
  ΨXX := ΨXX
  σC := σC
  σF := σF
  θX := dualizingExchange ℓ σpt νX
  θF := dualizingExchange ℓ σpt νF
  χι := CategoryTheory.mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι) αι
  χΔ := CategoryTheory.mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X')) αΔ
  βc := exceptionalExchange ℓ c.support c'.support νc
  βd := exceptionalExchange ℓ F.d F'.d νd
  unit_comp := hunit
  θF_eq := dualizingExchange_eq_comp ℓ σpt F.d F'.d νd νX νF hθ
  fixedSquare := fixedSquare_of_compactSupportExchange_app αι αΔ νc νd νι νΔ hι hΔ hcomp

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
