/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeGeometricFiber
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeOpenImmersion
public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-!
# The exceptional base change map at the unit over a point, through Nagata (A1')

Let `k` be a finite field with algebraic closure `k̄`, and `f : X ⟶ Spec k` a separated `k`-scheme
of finite type, with geometric fibre `f̄ : X̄ ⟶ Spec k̄` (`geometricFiberOverMap f`). Factor `f`
through the compactification `X --j--> X^c --p--> Spec k` defining `Rf_!`
(`compactificationOverField f`): `j` is an open immersion and `p` is proper. For any
compact-support base change isomorphism `bcj` of `j` along `X̄^c ⟶ X^c`, the pasting of `bcj`
with proper base change for `p` (`nagataLowerShriekBaseChange`) is a compact-support base change
isomorphism for `f`, and its exceptional base change map at the unit
`πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` is invertible
(`ProEtale.CondensedRing.isIso_smoothUnitBaseChange_nagataLowerShriekBaseChange`).

## Proof

By the pasting law (`isIso_smoothUnitBaseChange_paste`) it is enough that

* the exceptional base change map at the unit of `p` is invertible: this is
  `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_unit_point` for the proper
  `k`-scheme `X^c` (no smoothness is needed);
* the mate `πX^* Rj^! N ⟶ Rj̄^! πX^c^* N` of `bcj` is invertible at `N = Rp^! ℚ̄_ℓ`: for an open
  immersion this holds for **every** `N` and **every** base change isomorphism
  (`isIso_upperShriekMateOfMap_app_of_isOpenImmersion'`), since the units of `Rj_! ⊣ Rj^!` and
  `Rj̄_! ⊣ Rj̄^!` are invertible (`CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_unit`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a') {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
  {G : C ⥤ C'} {H : D ⥤ D'} (bc : a ⋙ H ⟶ G ⋙ b) [IsIso bc]

/-- For adjunctions `a ⊣ a'` and `b ⊣ b'` with invertible units and a natural isomorphism
`a' ⋙ G ≅ H ⋙ b'`, the mate `G a' ⟶ b' H` of the inverse of any invertible base change morphism
`bc : a H ⟶ G b` is invertible. -/
lemma isIso_mateEquiv_app_of_isIso_unit [IsIso adj.unit] [IsIso adj'.unit]
    (τ : a' ⋙ G ≅ H ⋙ b') (U : D) : IsIso ((mateEquiv adj adj' (inv bc)).app U) := by
  have := isIso_unitBaseChange_of_isIso_unit adj adj' bc (𝟙 (H.obj U)) τ
  simpa [unitBaseChange] using this

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section OpenImmersion

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U V : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  {U' V' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (j : U ⟶ V) (j' : U' ⟶ V') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {πU : U'.left ⟶ U.left} {πV : V'.left ⟶ V.left}
  (bc : boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j')

/-- **The exceptional base change map of an open immersion is invertible.** For open immersions
`j`, `j'` in a commutative square `πU ≫ j = j' ≫ πV` and **any** compact-support base change
isomorphism `bc`, the mate `πU^* Rj^! N ⟶ Rj'^! πV^* N` of `bc` is invertible for every `N`. -/
theorem isIso_upperShriekMateOfMap_app_of_isOpenImmersion' (h : πU ≫ j.left = j'.left ≫ πV)
    (N : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj l⟧) :
    IsIso ((upperShriekMateOfMap l j j' bc).app N) :=
  Adjunction.isIso_mateEquiv_app_of_isIso_unit _ _ _
    (Functor.isoWhiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl l j) _ ≪≫
      boundedConstructibleUpperStarCompUpperStarOfMapIso l j j' h ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl l j').symm)
    N

end OpenImmersion

section OpenImmersionBaseChange

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U V : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  {U' V' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  {j : U ⟶ V} {j' : U' ⟶ V'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {πU : U'.left ⟶ U.left} {πV : V'.left ⟶ V.left}

/-- **Extension by zero commutes with pullback across fields** on bounded constructible
complexes: for a cartesian square `πU ≫ j = j' ≫ πV` with `j`, `j'` open immersions,
`j_! ⋙ πV^* ≅ πU^* ⋙ j'_!`, the restriction of the ambient
`ProEtale.CondensedRing.openImmersionLowerShriekMapDerivedCategoryBaseChangeIso`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarOfMapIso
    (sq : IsPullback πU j'.left j.left πV) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj l) l j ⋙
        boundedConstructibleUpperStarOfMap l πV ≅
      boundedConstructibleUpperStarOfMap l πU ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj l) l j' :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleOpenImmersionLowerShriekCompatibility _ l j) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerLeft _
            (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πV) ≪≫
          openImmersionLowerShriekMapDerivedCategoryBaseChangeIso _ sq.flip ≪≫
          Functor.isoWhiskerRight
            (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πU).symm
            _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleOpenImmersionLowerShriekCompatibility _ l j').symm ≪≫
      (Functor.associator _ _ _).symm)

/-- **The compact-support base change isomorphism of an open immersion across fields**:
`Rj_! ⋙ πV^* ≅ πU^* ⋙ Rj'_!` for a cartesian square `πU ≫ j = j' ≫ πV` of open immersions, from
`Rj_! ≅ j_!` (`boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`) and the
base change of the extension by zero
(`boundedConstructibleOpenImmersionLowerShriekUpperStarOfMapIso`). -/
noncomputable def openImmersionLowerShriekBaseChangeOfMap (sq : IsPullback πU j'.left j.left πV) :
    boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πV ≅
      boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j' :=
  Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl l j) _ ≪≫
    boundedConstructibleOpenImmersionLowerShriekUpperStarOfMapIso l sq ≪≫
    Functor.isoWhiskerLeft _
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl l j').symm

end OpenImmersionBaseChange

section Point

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (f : X ⟶ point k)

/-- The open immersion `j : X ⟶ X^c` of the compactification of `f` defining `Rf_!`. -/
abbrev nagataOpenImmersion : X ⟶ (compactificationOverField f).overObj :=
  (compactificationOverField f).overI

/-- The proper morphism `p : X^c ⟶ Spec k` of the compactification of `f` defining `Rf_!`. -/
abbrev nagataProper : (compactificationOverField f).overObj ⟶ point k :=
  (compactificationOverField f).overG

omit [Finite k] [Fact (ringChar k).Prime] in
lemma nagataOpenImmersion_comp_nagataProper :
    nagataOpenImmersion f ≫ nagataProper f = f :=
  (compactificationOverField f).overI_overG

omit [Finite k] [Fact (ringChar k).Prime] in
lemma geometricFiberOverMap_nagataOpenImmersion_comp_nagataProper :
    geometricFiberOverMap (nagataOpenImmersion f) ≫ geometricFiberOverMap (nagataProper f) =
      geometricFiberOverMap f := by
  rw [← geometricFiberOverMap_comp, nagataOpenImmersion_comp_nagataProper]

/-- The compact-support base change isomorphism `Rf_! ⋙ πS^* ≅ πX^* ⋙ Rf̄_!` along `k ⟶ k̄`
attached to the compactification `X --j--> X^c --p--> Spec k` defining `Rf_!`: the pasting of a
compact-support base change isomorphism `bcj` of `j` with proper base change for `p`
(`properLowerShriekBaseChangeOfMap`), transported along `j ≫ p = f`. -/
def nagataLowerShriekBaseChange
    (bcj : boundedConstructibleLowerShriek l (nagataOpenImmersion f) ⋙
        boundedConstructibleUpperStarOfMap l (X := (compactificationOverField f).overObj)
          (Y := geometricFiberOver (compactificationOverField f).overObj)
          (compactificationOverField f).overObj.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap (nagataOpenImmersion f))) :
    boundedConstructibleLowerShriek l f ⋙
        boundedConstructibleUpperStarOfMap l (X := point k)
          (Y := geometricFiberOver (point k)) (point k).hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap f) :=
  transportLowerShriekBaseChange l (nagataOpenImmersion_comp_nagataProper f)
    (geometricFiberOverMap_nagataOpenImmersion_comp_nagataProper f)
    (pasteLowerShriekBaseChange l (nagataOpenImmersion f) (nagataProper f)
      (geometricFiberOverMap (nagataOpenImmersion f)) (geometricFiberOverMap (nagataProper f)) bcj
      (properLowerShriekBaseChangeOfMap l (nagataProper f) (geometricFiberOverMap (nagataProper f))
        (isPullback_geometricFiberOverMap (nagataProper f))))

instance : IsIso (geometricFiberOver (point k)).hom :=
  inferInstanceAs (IsIso (pullback.snd (𝟙 (Spec (.of k))) _))

omit [Finite k] [Fact (ringChar k).Prime] in
/-- The geometric fibre of the point is the base change of the point along `k ⟶ k̄`. -/
lemma isPullback_geometricFiberProj_point :
    IsPullback (point k).hom.geometricFiberProj (geometricFiberOver (point k)).hom
      (point k).hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :=
  IsPullback.of_hasPullback _ _

omit [Finite k] in
/-- **A1' over a point.** For a separated `k`-scheme of finite type `f : X ⟶ Spec k` (`k` finite)
and the compact-support base change isomorphism along `k ⟶ k̄` attached to the compactification
defining `Rf_!` (`nagataLowerShriekBaseChange`, for any base change isomorphism `bcj` of the open
immersion), the exceptional base change map at the unit `πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` is
invertible, for any isomorphism `e : πS^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`. -/
theorem isIso_smoothUnitBaseChange_nagataLowerShriekBaseChange
    (bcj : boundedConstructibleLowerShriek l (nagataOpenImmersion f) ⋙
        boundedConstructibleUpperStarOfMap l (X := (compactificationOverField f).overObj)
          (Y := geometricFiberOver (compactificationOverField f).overObj)
          (compactificationOverField f).overObj.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap (nagataOpenImmersion f)))
    (e : (boundedConstructibleUpperStarOfMap l (X := point k) (Y := geometricFiberOver (point k))
      (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l f (geometricFiberOverMap f)
      (nagataLowerShriekBaseChange l f bcj) e) := by
  -- the proper piece
  have := isIso_upperShriekBaseChangeOfMap_app_unit_point l (L := AlgebraicClosure k)
    (Z := (compactificationOverField f).overObj) (Z' := geometricFiberOver _)
    (P' := geometricFiberOver (point k)) (f := nagataProper f)
    (f' := geometricFiberOverMap (nagataProper f)) isPullback_geometricFiberProj_point
    (isPullback_geometricFiberOverMap (nagataProper f))
  have : IsIso (smoothUnitBaseChange l (nagataProper f) (geometricFiberOverMap (nagataProper f))
      (properLowerShriekBaseChangeOfMap l (nagataProper f) (geometricFiberOverMap (nagataProper f))
        (isPullback_geometricFiberOverMap (nagataProper f))) e) :=
    isIso_smoothUnitBaseChange_of_isIso_upperShriekBaseChangeOfMap l (nagataProper f)
      (geometricFiberOverMap (nagataProper f)) (isPullback_geometricFiberOverMap (nagataProper f)) e
  -- the open-immersion piece
  have := isIso_upperShriekMateOfMap_app_of_isOpenImmersion' l (nagataOpenImmersion f)
    (geometricFiberOverMap (nagataOpenImmersion f)) bcj
    (isPullback_geometricFiberOverMap (nagataOpenImmersion f)).w
    ((boundedConstructibleUpperShriek l (nagataProper f)).obj (𝟙_ _))
  rw [nagataLowerShriekBaseChange, isIso_smoothUnitBaseChange_transport_iff]
  exact isIso_smoothUnitBaseChange_paste l _ _ _ _ _ _ e

/-- **The compact-support base change isomorphism of `f : X ⟶ Spec k` along `k ⟶ k̄`**, through
the compactification `X --j--> X^c --p--> Spec k` defining `Rf_!`: the pasting of the base change
of the extension by zero along `j` (`openImmersionLowerShriekBaseChangeOfMap`) with proper base
change along `p`. -/
noncomputable def geometricFiberLowerShriekBaseChangePoint :
    boundedConstructibleLowerShriek l f ⋙
        boundedConstructibleUpperStarOfMap l (X := point k)
          (Y := geometricFiberOver (point k)) (point k).hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap f) :=
  nagataLowerShriekBaseChange l f
    (openImmersionLowerShriekBaseChangeOfMap l
      (isPullback_geometricFiberOverMap (nagataOpenImmersion f)))

omit [Finite k] in
/-- **A1' over a point**: for a separated `k`-scheme of finite type `f : X ⟶ Spec k` over a
finite field `k`, the exceptional base change map at the unit `πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` along
`k ⟶ k̄` attached to the compact-support base change isomorphism
`geometricFiberLowerShriekBaseChangePoint` is invertible, for any isomorphism
`e : πS^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`. -/
theorem isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangePoint
    (e : (boundedConstructibleUpperStarOfMap l (X := point k) (Y := geometricFiberOver (point k))
      (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l f (geometricFiberOverMap f)
      (geometricFiberLowerShriekBaseChangePoint l f) e) :=
  isIso_smoothUnitBaseChange_nagataLowerShriekBaseChange l f _ e

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
