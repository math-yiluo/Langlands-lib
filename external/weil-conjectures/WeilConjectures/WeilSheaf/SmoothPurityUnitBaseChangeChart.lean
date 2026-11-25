/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeLocal
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeProper

/-!
# The exceptional base change map at the unit on a chart of the étale normal form (A1')

Formal consequences of the pasting law (`smoothUnitBaseChange_comp`) used in the local proof of
`IsIso smoothUnitBaseChange` for a smooth non-proper `f`:

* `isIso_smoothUnitBaseChange_iff_isIso_mate_app`: for `e` invertible, the exceptional base
  change map at the unit is invertible iff the mate of `bc` is invertible at the unit;
* `isIso_smoothUnitBaseChange_comp_openImmersion_right_iff` (**locality on the base**): for an
  open immersion `jV : V ⟶ Y` whose exceptional base change map at the unit is invertible, the
  one of `fV ≫ jV` is invertible iff the one of `fV : XV ⟶ V` is;
* `isIso_smoothUnitBaseChange_chart`: on a chart `U --g--> A --jA--> P --p--> V --jV--> Y`
  (`g` étale, `jA` an open immersion, `p` the projection of a projective space, `jV` an open
  immersion), the exceptional base change map at the unit of the composite is invertible as soon
  as the mates of `bcg` and `bcjA` are invertible (step 2), the one of `jV` is invertible (open
  unit case of step 2) and the one of `p` is (the proper piece,
  `isIso_smoothUnitBaseChange_of_projectiveSpace_of_weaklyEtale`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Unit

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (bc : boundedConstructibleLowerShriek l f ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f')
  (e : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)

/-- `smoothUnitBaseChange` is the mate of `bc` at the unit followed by `Rf'^!(e)`. -/
lemma smoothUnitBaseChange_eq_mate_app :
    smoothUnitBaseChange l f f' bc e =
      (upperShriekMateOfMap l f f' bc).app (𝟙_ _) ≫
        (boundedConstructibleUpperShriek l f').map e :=
  rfl

/-- For `e` invertible, the exceptional base change map at the unit is invertible iff the mate of
`bc` is invertible at the unit. -/
theorem isIso_smoothUnitBaseChange_iff_isIso_mate_app [IsIso e] :
    IsIso (smoothUnitBaseChange l f f' bc e) ↔
      IsIso ((upperShriekMateOfMap l f f' bc).app (𝟙_ _)) := by
  rw [smoothUnitBaseChange_eq_mate_app, isIso_comp_right_iff]

/-- The mate of `bc` is invertible at `N` iff it is at any `N' ≅ N`. -/
theorem isIso_mate_app_iff_of_iso {N N' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧}
    (i : N ≅ N') :
    IsIso ((upperShriekMateOfMap l f f' bc).app N) ↔
      IsIso ((upperShriekMateOfMap l f f' bc).app N') :=
  NatTrans.isIso_app_iff_of_iso _ i

end Unit

section Base

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {XV V Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType XV.hom] [QuasiCompact XV.hom] [IsSeparated XV.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {XV' V' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType XV'.hom] [QuasiCompact XV'.hom] [IsSeparated XV'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (fV : XV ⟶ V) (jV : V ⟶ Y) [IsOpenImmersion jV.left] (fV' : XV' ⟶ V') (jV' : V' ⟶ Y')
  [IsOpenImmersion jV'.left]
  {πXV : XV'.left ⟶ XV.left} {πV : V'.left ⟶ V.left} {πY : Y'.left ⟶ Y.left}
  (bcf : boundedConstructibleLowerShriek l fV ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πXV ⋙ boundedConstructibleLowerShriek l fV')
  (bcj : boundedConstructibleLowerShriek l jV ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πV ⋙ boundedConstructibleLowerShriek l jV')
  (eY : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)
  (eV : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _)

omit [IsOpenImmersion jV'.left] in
/-- **Locality on the base**: for an open immersion `jV : V ⟶ Y` whose exceptional base change
map at the unit is invertible (the open-immersion unit case of step 2) and `eV` invertible, the
exceptional base change map at the unit of `fV ≫ jV` (pasted base change) is invertible iff the
one of `fV` is. -/
theorem isIso_smoothUnitBaseChange_comp_openImmersion_right_iff
    [IsIso (smoothUnitBaseChange l jV jV' bcj eY)] [IsIso eV] :
    IsIso (smoothUnitBaseChange l (fV ≫ jV) (fV' ≫ jV')
        (pasteLowerShriekBaseChange l fV jV fV' jV' bcf bcj) eY) ↔
      IsIso (smoothUnitBaseChange l fV fV' bcf eV) := by
  rw [isIso_smoothUnitBaseChange_comp_iff l fV jV fV' jV' bcf bcj _
    (exchangeCompCompatible_pasteLowerShriekBaseChange l fV jV fV' jV' bcf bcj) eY,
    isIso_comp_right_iff, isIso_smoothUnitBaseChange_iff_isIso_mate_app]
  exact isIso_mate_app_iff_of_iso l fV fV' bcf
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl l jV)

end Base

section Chart

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U A P V Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {U' A' P' V' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType A'.hom] [QuasiCompact A'.hom] [IsSeparated A'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (g : U ⟶ A) (jA : A ⟶ P) (p : P ⟶ V) (jV : V ⟶ Y)
  (g' : U' ⟶ A') (jA' : A' ⟶ P') (p' : P' ⟶ V') (jV' : V' ⟶ Y')
  {πU : U'.left ⟶ U.left} {πA : A'.left ⟶ A.left} {πP : P'.left ⟶ P.left}
  {πV : V'.left ⟶ V.left} {πY : Y'.left ⟶ Y.left}
  (bcg : boundedConstructibleLowerShriek l g ⋙ boundedConstructibleUpperStarOfMap l πA ≅
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l g')
  (bcjA : boundedConstructibleLowerShriek l jA ⋙ boundedConstructibleUpperStarOfMap l πP ≅
    boundedConstructibleUpperStarOfMap l πA ⋙ boundedConstructibleLowerShriek l jA')
  (bcp : boundedConstructibleLowerShriek l p ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πP ⋙ boundedConstructibleLowerShriek l p')
  (bcjV : boundedConstructibleLowerShriek l jV ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πV ⋙ boundedConstructibleLowerShriek l jV')
  (eY : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)

/-- The pasted compact-support base change isomorphism of the chart `g ≫ jA ≫ p ≫ jV`. -/
abbrev chartLowerShriekBaseChange :
    boundedConstructibleLowerShriek l (g ≫ jA ≫ p ≫ jV) ⋙
        boundedConstructibleUpperStarOfMap l πY ≅
      boundedConstructibleUpperStarOfMap l πU ⋙
        boundedConstructibleLowerShriek l (g' ≫ jA' ≫ p' ≫ jV') :=
  pasteLowerShriekBaseChange l g (jA ≫ p ≫ jV) g' (jA' ≫ p' ≫ jV') bcg
    (pasteLowerShriekBaseChange l jA (p ≫ jV) jA' (p' ≫ jV') bcjA
      (pasteLowerShriekBaseChange l p jV p' jV' bcp bcjV))

/-- **The exceptional base change map at the unit on a chart of the étale normal form**: if the
mates of `bcg` and `bcjA` are invertible at the relevant objects (step 2: `g` étale, `jA` an
open immersion) and the exceptional base change map at the unit of `p ≫ jV` is invertible, then
the one of the chart `g ≫ jA ≫ p ≫ jV` is. -/
theorem isIso_smoothUnitBaseChange_chart
    [IsIso ((upperShriekMateOfMap l g g' bcg).app
      ((boundedConstructibleUpperShriek l (jA ≫ p ≫ jV)).obj (𝟙_ _)))]
    [IsIso ((upperShriekMateOfMap l jA jA' bcjA).app
      ((boundedConstructibleUpperShriek l (p ≫ jV)).obj (𝟙_ _)))]
    [IsIso (smoothUnitBaseChange l (p ≫ jV) (p' ≫ jV')
      (pasteLowerShriekBaseChange l p jV p' jV' bcp bcjV) eY)] :
    IsIso (smoothUnitBaseChange l (g ≫ jA ≫ p ≫ jV) (g' ≫ jA' ≫ p' ≫ jV')
      (chartLowerShriekBaseChange l g jA p jV g' jA' p' jV' bcg bcjA bcp bcjV) eY) :=
  have : IsIso (smoothUnitBaseChange l (jA ≫ p ≫ jV) (jA' ≫ p' ≫ jV')
      (pasteLowerShriekBaseChange l jA (p ≫ jV) jA' (p' ≫ jV') bcjA
        (pasteLowerShriekBaseChange l p jV p' jV' bcp bcjV)) eY) :=
    isIso_smoothUnitBaseChange_paste l jA (p ≫ jV) jA' (p' ≫ jV') bcjA _ eY
  isIso_smoothUnitBaseChange_paste l g (jA ≫ p ≫ jV) g' (jA' ≫ p' ≫ jV') bcg _ eY

variable [IsProper p.left] [IsProper p'.left] (sqp : IsPullback πP p'.left p.left πV)
  [IsOpenImmersion jV.left] [IsOpenImmersion jV'.left]
  (eV : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _)

omit [IsOpenImmersion jV'.left] in
/-- **The chart theorem with the proper piece from the library**: for `p` the projection of a
projective space `ℙⁿ_V ⟶ V`, `πV` weakly étale, `bcp` proper base change, `jV` an open immersion
with invertible exceptional base change map at the unit, and the mates of `bcg`, `bcjA`
invertible, the exceptional base change map at the unit of the chart is invertible. -/
theorem isIso_smoothUnitBaseChange_chart_of_projectiveSpace (n : ℕ)
    (eP : P.left ≅ ℙ(ULift.{u} (Fin (n + 1)); V.left))
    (he : eP.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); V.left) ↘ V.left = p.left) [WeaklyEtale πV]
    [IsIso eV] [IsIso (smoothUnitBaseChange l jV jV' bcjV eY)]
    [IsIso ((upperShriekMateOfMap l g g' bcg).app
      ((boundedConstructibleUpperShriek l (jA ≫ p ≫ jV)).obj (𝟙_ _)))]
    [IsIso ((upperShriekMateOfMap l jA jA' bcjA).app
      ((boundedConstructibleUpperShriek l (p ≫ jV)).obj (𝟙_ _)))] :
    IsIso (smoothUnitBaseChange l (g ≫ jA ≫ p ≫ jV) (g' ≫ jA' ≫ p' ≫ jV')
      (chartLowerShriekBaseChange l g jA p jV g' jA' p' jV' bcg bcjA
        (properLowerShriekBaseChangeOfMap l p p' sqp) bcjV) eY) :=
  have hp : IsIso (smoothUnitBaseChange l p p' (properLowerShriekBaseChangeOfMap l p p' sqp) eV) :=
    isIso_smoothUnitBaseChange_of_projectiveSpace_of_weaklyEtale l p p' sqp eV n eP he
  have : IsIso (smoothUnitBaseChange l (p ≫ jV) (p' ≫ jV')
      (pasteLowerShriekBaseChange l p jV p' jV' (properLowerShriekBaseChangeOfMap l p p' sqp)
        bcjV) eY) :=
    (isIso_smoothUnitBaseChange_comp_openImmersion_right_iff l p jV p' jV'
      (properLowerShriekBaseChangeOfMap l p p' sqp) bcjV eY eV).2 hp
  isIso_smoothUnitBaseChange_chart l g jA p jV g' jA' p' jV' bcg bcjA
    (properLowerShriekBaseChangeOfMap l p p' sqp) bcjV eY

end Chart

section Congr

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) {f₁' f₂' : X' ⟶ Y'} (h' : f₁' = f₂')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (bc : boundedConstructibleLowerShriek l f₁ ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f₁')
  (e : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)

/-- A compact-support base change isomorphism transported along equalities of morphisms
`f₁ = f₂`, `f₁' = f₂'` (in practice `jᵢ ≫ f = gᵢ ≫ jA ≫ p ≫ jV` on a chart). -/
def transportLowerShriekBaseChange :
    boundedConstructibleLowerShriek l f₂ ⋙ boundedConstructibleUpperStarOfMap l πY ≅
      boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f₂' :=
  Functor.isoWhiskerRight (eqToIso (by rw [h])) _ ≪≫ bc ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (by rw [h']))

/-- The exceptional base change map at the unit is compatible with the transport along
equalities of morphisms. -/
theorem smoothUnitBaseChange_transport :
    smoothUnitBaseChange l f₂ f₂' (transportLowerShriekBaseChange l h h' bc) e =
      eqToHom (by rw [h]) ≫ smoothUnitBaseChange l f₁ f₁' bc e ≫ eqToHom (by rw [h']) := by
  subst h h'
  have hbc : transportLowerShriekBaseChange l rfl rfl bc = bc := by
    ext K
    simp [transportLowerShriekBaseChange]
  rw [hbc]
  simp

/-- Invertibility of the exceptional base change map at the unit is invariant under the
transport along equalities of morphisms. -/
theorem isIso_smoothUnitBaseChange_transport_iff :
    IsIso (smoothUnitBaseChange l f₂ f₂' (transportLowerShriekBaseChange l h h' bc) e) ↔
      IsIso (smoothUnitBaseChange l f₁ f₁' bc e) := by
  rw [smoothUnitBaseChange_transport, isIso_comp_left_iff, isIso_comp_right_iff]

end Congr

end AlgebraicGeometry.ProEtale.CondensedRing
