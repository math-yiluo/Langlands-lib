/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint
public import WeilConjectures.SmoothPurity.EtaleUpperShriek

/-!
# The exceptional base change at the unit for étale morphisms

Let `h : U ⟶ V` be a morphism of separated `k₁`-schemes of finite type, `h' : U' ⟶ V'` one of
`k₂`-schemes, with `πU : U' ⟶ U`, `πV : V' ⟶ V` and `πU ≫ h = h' ≫ πV`, and let
`bc : Rh_! ⋙ πV^* ≅ πU^* ⋙ Rh'_!` be a compact-support base change isomorphism. This file treats
the exceptional base change map `smoothUnitBaseChange : πU^* Rh^! ℚ̄_ℓ ⟶ Rh'^! ℚ̄_ℓ` (the mate of
`bc` under `Rh_! ⊣ Rh^!`, `Rh'_! ⊣ Rh'^!`, followed by `Rh'^!(e)`) when `Rh_!` and `Rh'_!` are
also left adjoint to the pullbacks, as for étale morphisms.

The mate of a square does not depend on the chosen right adjoints, up to the canonical
isomorphisms between them (`CategoryTheory.Adjunction.mateEquiv_app_eq_conjugateEquiv`). Through
`Rh^! ≅ h^*`, the exceptional base change map is therefore the mate of `bc` under `Rh_! ⊣ h^*`
and `Rh'_! ⊣ h'^*`. If `bc` carries the counit of `Rh_! ⊣ h^*` to that of `Rh'_! ⊣ h'^*` through
the composition isomorphism `πU^* h^* ≅ h'^* πV^*` of the pullbacks, then this mate *is* that
composition isomorphism (`CategoryTheory.Adjunction.mateEquiv_eq_of_counit`), and so it is
invertible.

## Main statements

* `ProEtale.CondensedRing.isIso_mateEquiv_boundedConstructibleUpperShriekAdjunction_of_counit`:
  the exceptional base change `πU^* Rh^! ⟶ Rh'^! πV^*` is an isomorphism of functors, for
  adjunctions `Rh_! ⊣ h^*`, `Rh'_! ⊣ h'^*` compatible with `bc`.
* `ProEtale.CondensedRing.isIso_smoothUnitBaseChange_of_counit`: the same at the unit, for
  `smoothUnitBaseChange` with `e` invertible.
* `ProEtale.CondensedRing.isIso_smoothUnitBaseChange_of_isOpenImmersion_of_counit`: the case of an
open
  immersion, where `Rj_! ≅ j_!` and `j_! ⊣ j^*` are in the library. The compatibility asked of
  `bc` is that of the extension by zero.
* `ProEtale.CondensedRing.isIso_smoothUnitBaseChange_of_etale`: the case of an étale morphism,
  for the adjunction `Rh_! ⊣ h^*` of
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale`.
* `ProEtale.CondensedRing.isIso_smoothUnitBaseChange_etaleLowerShriekBaseChange`: for a
  cartesian square with `h` étale and the canonical compact-support base change
  `ProEtale.CondensedRing.etaleLowerShriekBaseChange` (the inverse of the mate of
  `πU^* h^* ≅ h'^* πV^*`), `smoothUnitBaseChange` is invertible, with no hypothesis on `bc`.

## Remaining input (left as `sorry`)

The adjunction `Rh_! ⊣ h^*` of an étale `h`
(`ProEtale.CondensedRing.nonempty_boundedConstructibleLowerShriekUpperStarAdjunction_of_etale`) is
purity in relative dimension zero, `Rh^! ≅ h^*`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarIsoUpperShriekOfEtale`). What remains is

* `ProEtale.CondensedRing.isIso_etaleLowerShriekExchange`: étale base change for `Rh_!`, the
  exchange `πU^* ⋙ Rh'_! ⟶ Rh_! ⋙ πV^*` of a cartesian square with `h` étale is invertible.

The invertibility of `e : πV^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is needed: once the mate is invertible,
`smoothUnitBaseChange` is invertible if and only if `Rh'^!(e)` is.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

/-! ### Mates and changes of right adjoints -/

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {a : C ⥤ D} {a' S : D ⥤ C} (adj : a ⊣ a') (adjS : a ⊣ S)
  {b : C' ⥤ D'} {b' S' : D' ⥤ C'} (adj' : b ⊣ b') (adjS' : b ⊣ S')
  {G : C ⥤ C'} {H : D ⥤ D'}

/-- The mate of a square under `a ⊣ S` and `b ⊣ S'` is its mate under `a ⊣ a'` and `b ⊣ b'`,
conjugated by the canonical isomorphisms `S ≅ a'` and `b' ≅ S'`. -/
lemma mateEquiv_app_eq_conjugateEquiv (α : TwoSquare G a b H) (U : D) :
    (mateEquiv adjS adjS' α).app U =
      G.map ((conjugateEquiv adjS adj (𝟙 a)).app U) ≫ (mateEquiv adj adj' α).app U ≫
        (conjugateEquiv adj' adjS' (𝟙 b)).app (H.obj U) := by
  have h₁ := congr_app (mateEquiv_conjugateEquiv_vcomp adj adj' adjS' α (𝟙 b)) U
  have h₂ := congr_app (conjugateEquiv_mateEquiv_vcomp adjS adj adjS' (𝟙 a)
    (α.whiskerRight (𝟙 b))) U
  have h₃ : (α.whiskerRight (𝟙 b)).whiskerLeft (𝟙 a) = α := by
    ext X
    simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  rw [h₃] at h₂
  rw [h₂]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₁ ⊢
  rw [h₁]

/-- Whether a component of the mate of a square is invertible does not depend on the chosen
right adjoints. -/
lemma isIso_mateEquiv_app_iff (α : TwoSquare G a b H) (U : D) :
    IsIso ((mateEquiv adjS adjS' α).app U) ↔ IsIso ((mateEquiv adj adj' α).app U) := by
  rw [mateEquiv_app_eq_conjugateEquiv adj adjS adj' adjS']
  constructor
  · intro h
    have := IsIso.of_isIso_comp_left (G.map ((conjugateEquiv adjS adj (𝟙 a)).app U))
      ((mateEquiv adj adj' α).app U ≫ (conjugateEquiv adj' adjS' (𝟙 b)).app (H.obj U))
    exact IsIso.of_isIso_comp_right _ ((conjugateEquiv adj' adjS' (𝟙 b)).app (H.obj U))
  · intro h
    infer_instance

/-- Whether the mate of a square is invertible does not depend on the chosen right adjoints. -/
lemma isIso_mateEquiv_iff (α : TwoSquare G a b H) :
    IsIso (mateEquiv adjS adjS' α) ↔ IsIso (mateEquiv adj adj' α) := by
  rw [NatTrans.isIso_iff_isIso_app, NatTrans.isIso_iff_isIso_app]
  exact forall_congr' fun U ↦ isIso_mateEquiv_app_iff adj adjS adj' adjS' α U

/-- The mate of `α` is `c` as soon as `α` carries the counit of `a ⊣ S` to that of `b ⊣ S'`
through `c`. -/
lemma mateEquiv_eq_of_counit (α : TwoSquare G a b H) (c : TwoSquare S H G S')
    (h : ∀ M, α.app (S.obj M) ≫ H.map (adjS.counit.app M) =
      b.map (c.app M) ≫ adjS'.counit.app (H.obj M)) :
    mateEquiv adjS adjS' α = c := by
  ext M
  apply (adjS'.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, mateEquiv_counit, h]

/-- The mate of `α` under `a ⊣ a'` and `b ⊣ b'` is invertible as soon as `α` carries the counit
of some other adjunction `a ⊣ S` to that of some `b ⊣ S'` through an isomorphism `c`. -/
lemma isIso_mateEquiv_of_counit (α : TwoSquare G a b H) (c : TwoSquare S H G S')
    [IsIso c]
    (h : ∀ M, α.app (S.obj M) ≫ H.map (adjS.counit.app M) =
      b.map (c.app M) ≫ adjS'.counit.app (H.obj M)) :
    IsIso (mateEquiv adj adj' α) := by
  rw [← isIso_mateEquiv_iff adj adjS adj' adjS', mateEquiv_eq_of_counit adjS adjS' α c h]
  infer_instance

/-- If the inverse mate `β` of an isomorphism `c` is invertible, then `β⁻¹` carries the counit of
`a ⊣ S` to that of `b ⊣ S'` through `c`. -/
lemma map_counit_eq_inv_mateEquiv_symm (c : TwoSquare S H G S')
    [IsIso ((mateEquiv adjS adjS').symm c)] (M : D) :
    H.map (adjS.counit.app M) =
      (inv ((mateEquiv adjS adjS').symm c)).app (S.obj M) ≫ b.map (c.app M) ≫
        adjS'.counit.app (H.obj M) := by
  rw [mateEquiv_counit_symm, ← Category.assoc, ← NatTrans.comp_app, IsIso.inv_hom_id,
    NatTrans.id_app, Category.id_comp]

variable {bc : a ⋙ H ⟶ G ⋙ b} [IsIso bc] {U : D} {U' : D'} (e : H.obj U ⟶ U')

/-- For an invertible `e`, `CategoryTheory.Adjunction.unitBaseChange` is invertible if and only if
the mate of `bc⁻¹` under any other adjunctions `a ⊣ S`, `b ⊣ S'` is invertible at `U`. -/
lemma isIso_unitBaseChange_iff [IsIso e] :
    IsIso (unitBaseChange adj adj' bc e) ↔ IsIso ((mateEquiv adjS adjS' (inv bc)).app U) := by
  rw [isIso_mateEquiv_app_iff adj adjS adj' adjS', unitBaseChange]
  constructor
  · intro h
    exact IsIso.of_isIso_comp_right _ (b'.map e)
  · intro h
    infer_instance

/-- `CategoryTheory.Adjunction.unitBaseChange` is invertible when `e` and the mate of `bc⁻¹`
are. -/
lemma isIso_unitBaseChange [IsIso e] [IsIso (mateEquiv adj adj' (inv bc))] :
    IsIso (unitBaseChange adj adj' bc e) := by
  rw [unitBaseChange]
  infer_instance

end CategoryTheory.Adjunction

/-! ### The exceptional base change when `Rh_!` is left adjoint to the pullback -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U V : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  {U' V' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  {πU : U'.left ⟶ U.left} {πV : V'.left ⟶ V.left}

/-- The composition isomorphism `h^* ⋙ πU^* ≅ πV^* ⋙ h'^*` of the pullbacks of bounded
constructible complexes along a commutative square `πU ≫ h = h' ≫ πV`. -/
def boundedConstructibleUpperStarOfMapSquareIso (h : U ⟶ V) (h' : U' ⟶ V')
    (w : πU ≫ h.left = h'.left ≫ πV) :
    boundedConstructibleUpperStarOfMap l (X := V) (Y := U) h.left ⋙
        boundedConstructibleUpperStarOfMap l (X := U) (Y := U') πU ≅
      boundedConstructibleUpperStarOfMap l (X := V) (Y := V') πV ⋙
        boundedConstructibleUpperStarOfMap l (X := V') (Y := U') h'.left :=
  (boundedConstructibleUpperStarOfMapComp l h.left πU).symm ≪≫
    eqToIso (by rw [w]) ≪≫ boundedConstructibleUpperStarOfMapComp l πV h'.left

section General

variable {h : U ⟶ V} {h' : U' ⟶ V'}
  (bc : boundedConstructibleLowerShriek l h ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l h')
  (e : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _)
  (adj : boundedConstructibleLowerShriek l h ⊣ boundedConstructibleUpperStarOfMap l h.left)
  (adj' : boundedConstructibleLowerShriek l h' ⊣ boundedConstructibleUpperStarOfMap l h'.left)
  (w : πU ≫ h.left = h'.left ≫ πV)

/-- **The exceptional base change of a morphism whose lower shriek is left adjoint to the
pullback.** If `Rh_! ⊣ h^*` and `Rh'_! ⊣ h'^*`, and the compact-support base change `bc` carries
the counit of the first to that of the second through `πU^* h^* ≅ h'^* πV^*`, then the
exceptional base change `πU^* Rh^! ⟶ Rh'^! πV^*` (the mate of `bc⁻¹`) is an isomorphism. -/
theorem isIso_mateEquiv_boundedConstructibleUpperShriekAdjunction_of_counit
    (hbc : ∀ M, (boundedConstructibleUpperStarOfMap l πV).map (adj.counit.app M) =
      bc.hom.app ((boundedConstructibleUpperStarOfMap l h.left).obj M) ≫
        (boundedConstructibleLowerShriek l h').map
          ((boundedConstructibleUpperStarOfMapSquareIso l h h' w).hom.app M) ≫
        adj'.counit.app ((boundedConstructibleUpperStarOfMap l πV).obj M)) :
    IsIso (mateEquiv (boundedConstructibleUpperShriekAdjunction l h)
      (boundedConstructibleUpperShriekAdjunction l h') bc.inv) := by
  refine Adjunction.isIso_mateEquiv_of_counit _ adj _ adj' _
    (.mk _ _ _ _ (boundedConstructibleUpperStarOfMapSquareIso l h h' w).hom) fun M ↦ ?_
  rw [hbc M, ← Category.assoc]
  erw [bc.inv_hom_id_app]
  rw [Category.id_comp]

/-- **The exceptional base change at the unit of a morphism whose lower shriek is left adjoint
to the pullback**: `smoothUnitBaseChange` is invertible under the hypotheses of
`isIso_mateEquiv_boundedConstructibleUpperShriekAdjunction_of_counit`, for an invertible `e`. -/
theorem isIso_smoothUnitBaseChange_of_counit [IsIso e]
    (hbc : ∀ M, (boundedConstructibleUpperStarOfMap l πV).map (adj.counit.app M) =
      bc.hom.app ((boundedConstructibleUpperStarOfMap l h.left).obj M) ≫
        (boundedConstructibleLowerShriek l h').map
          ((boundedConstructibleUpperStarOfMapSquareIso l h h' w).hom.app M) ≫
        adj'.counit.app ((boundedConstructibleUpperStarOfMap l πV).obj M)) :
    IsIso (smoothUnitBaseChange l h h' bc e) := by
  have : IsIso (mateEquiv (boundedConstructibleUpperShriekAdjunction l h)
      (boundedConstructibleUpperShriekAdjunction l h') (inv bc.hom)) := by
    refine Adjunction.isIso_mateEquiv_of_counit _ adj _ adj' _
      (.mk _ _ _ _ (boundedConstructibleUpperStarOfMapSquareIso l h h' w).hom) fun M ↦ ?_
    rw [hbc M, IsIso.Iso.inv_hom, ← Category.assoc]
    erw [bc.inv_hom_id_app]
    rw [Category.id_comp]
  exact Adjunction.isIso_unitBaseChange _ _ e

end General

/-! ### Open immersions -/

/-- For an open immersion `j`, the lower shriek `Rj_!` on bounded constructible `ℚ̄_ℓ`-complexes
is left adjoint to the pullback: the adjunction `j_! ⊣ j^*` transported along `Rj_! ≅ j_!`. -/
def boundedConstructibleLowerShriekUpperStarAdjunctionOfIsOpenImmersion (j : U ⟶ V)
    [IsOpenImmersion j.left] :
    boundedConstructibleLowerShriek l j ⊣ boundedConstructibleUpperStarOfMap l j.left :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj l) l j).ofNatIsoLeft
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl l j).symm

/-- **The exceptional base change at the unit of an open immersion**: `smoothUnitBaseChange` is
invertible for an invertible `e`, provided `bc` carries, through `Rj_! ≅ j_!` and
`πU^* j^* ≅ j'^* πV^*`, the counit of `j_! ⊣ j^*` to that of `j'_! ⊣ j'^*`. -/
theorem isIso_smoothUnitBaseChange_of_isOpenImmersion_of_counit
    {j : U ⟶ V} {j' : U' ⟶ V'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (bc : boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πV ≅
      boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j')
    (e : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]
    (w : πU ≫ j.left = j'.left ≫ πV)
    (hbc : ∀ M, (boundedConstructibleUpperStarOfMap l πV).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl l j).hom.app
            ((boundedConstructibleUpperStarOfMap l j.left).obj M) ≫
          (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj l) l j).counit.app M) =
      bc.hom.app ((boundedConstructibleUpperStarOfMap l j.left).obj M) ≫
        (boundedConstructibleLowerShriek l j').map
          ((boundedConstructibleUpperStarOfMapSquareIso l j j' w).hom.app M) ≫
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl l j').hom.app
            ((boundedConstructibleUpperStarOfMap l j'.left).obj
              ((boundedConstructibleUpperStarOfMap l πV).obj M)) ≫
          (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj l) l j').counit.app
              ((boundedConstructibleUpperStarOfMap l πV).obj M)) :
    IsIso (smoothUnitBaseChange l j j' bc e) :=
  isIso_smoothUnitBaseChange_of_counit l bc e
    (boundedConstructibleLowerShriekUpperStarAdjunctionOfIsOpenImmersion l j)
    (boundedConstructibleLowerShriekUpperStarAdjunctionOfIsOpenImmersion l j') w
    (by simpa [boundedConstructibleLowerShriekUpperStarAdjunctionOfIsOpenImmersion] using hbc)

/-! ### Étale morphisms -/

/-- **`Rh_! ⊣ h^*` for étale `h`** on bounded constructible `ℚ̄_ℓ`-complexes: the lower shriek,
defined through a Nagata compactification, is left adjoint to the pullback, that is
`Rh^! ≅ h^*` (`boundedConstructibleEtaleLowerShriekUpperStarAdjunction`, by purity in relative
dimension zero); for open immersions it is
`boundedConstructibleLowerShriekUpperStarAdjunctionOfIsOpenImmersion`. -/
theorem nonempty_boundedConstructibleLowerShriekUpperStarAdjunction_of_etale
    (h : U ⟶ V) [Etale h.left] :
    Nonempty (boundedConstructibleLowerShriek l h ⊣
      boundedConstructibleUpperStarOfMap l h.left) :=
  ⟨boundedConstructibleEtaleLowerShriekUpperStarAdjunction l h⟩

/-- The adjunction `Rh_! ⊣ h^*` of an étale morphism `h`, chosen by
`nonempty_boundedConstructibleLowerShriekUpperStarAdjunction_of_etale`. -/
def boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale (h : U ⟶ V) [Etale h.left] :
    boundedConstructibleLowerShriek l h ⊣ boundedConstructibleUpperStarOfMap l h.left :=
  (nonempty_boundedConstructibleLowerShriekUpperStarAdjunction_of_etale l h).some

/-- **The exceptional base change at the unit of an étale morphism**: `smoothUnitBaseChange` is
invertible for an invertible `e`, provided `bc` carries, through `πU^* h^* ≅ h'^* πV^*`, the
counit of `Rh_! ⊣ h^*` to that of `Rh'_! ⊣ h'^*`. -/
theorem isIso_smoothUnitBaseChange_of_etale
    {h : U ⟶ V} {h' : U' ⟶ V'} [Etale h.left] [Etale h'.left]
    (bc : boundedConstructibleLowerShriek l h ⋙ boundedConstructibleUpperStarOfMap l πV ≅
      boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l h')
    (e : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]
    (w : πU ≫ h.left = h'.left ≫ πV)
    (hbc : ∀ M, (boundedConstructibleUpperStarOfMap l πV).map
        ((boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale l h).counit.app M) =
      bc.hom.app ((boundedConstructibleUpperStarOfMap l h.left).obj M) ≫
        (boundedConstructibleLowerShriek l h').map
          ((boundedConstructibleUpperStarOfMapSquareIso l h h' w).hom.app M) ≫
        (boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale l h').counit.app
          ((boundedConstructibleUpperStarOfMap l πV).obj M)) :
    IsIso (smoothUnitBaseChange l h h' bc e) :=
  isIso_smoothUnitBaseChange_of_counit l bc e _ _ w hbc

/-! ### The canonical compact-support base change of an étale morphism -/

section Canonical

variable {h : U ⟶ V} {h' : U' ⟶ V'} [Etale h.left] [Etale h'.left]
  (hsq : IsPullback πU h'.left h.left πV)

/-- The exchange morphism `πU^* ⋙ Rh'_! ⟶ Rh_! ⋙ πV^*` of an étale morphism: the mate, under
`Rh_! ⊣ h^*` and `Rh'_! ⊣ h'^*`, of the composition isomorphism `πU^* h^* ≅ h'^* πV^*`. -/
def etaleLowerShriekExchange :
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l h' ⟶
      boundedConstructibleLowerShriek l h ⋙ boundedConstructibleUpperStarOfMap l πV :=
  ((mateEquiv (boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale l h)
    (boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale l h')).symm
      (.mk _ _ _ _ (boundedConstructibleUpperStarOfMapSquareIso l h h' hsq.w).hom))

/-- **Étale base change for the lower shriek** on bounded constructible `ℚ̄_ℓ`-complexes: for a
cartesian square with `h` étale, the exchange morphism `πU^* ⋙ Rh'_! ⟶ Rh_! ⋙ πV^*` is an
isomorphism. -/
theorem isIso_etaleLowerShriekExchange : IsIso (etaleLowerShriekExchange l hsq) :=
  sorry

/-- The **compact-support base change isomorphism of an étale morphism**,
`Rh_! ⋙ πV^* ≅ πU^* ⋙ Rh'_!`: the inverse of `etaleLowerShriekExchange`. -/
def etaleLowerShriekBaseChange :
    boundedConstructibleLowerShriek l h ⋙ boundedConstructibleUpperStarOfMap l πV ≅
      boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l h' :=
  have := isIso_etaleLowerShriekExchange l hsq
  (asIso (etaleLowerShriekExchange l hsq)).symm

/-- The compact-support base change of an Ã©tale morphism is the inverse of the exchange
morphism. -/
lemma etaleLowerShriekBaseChange_hom :
    (etaleLowerShriekBaseChange l hsq).hom =
      @inv _ _ _ _ (etaleLowerShriekExchange l hsq) (isIso_etaleLowerShriekExchange l hsq) :=
  rfl

/-- **The exceptional base change at the unit of an étale morphism**, for the canonical
compact-support base change `etaleLowerShriekBaseChange`: `smoothUnitBaseChange` is invertible
for every invertible `e`. -/
theorem isIso_smoothUnitBaseChange_etaleLowerShriekBaseChange
    (e : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l h h' (etaleLowerShriekBaseChange l hsq) e) := by
  have := isIso_etaleLowerShriekExchange l hsq
  refine isIso_smoothUnitBaseChange_of_etale l _ e hsq.w fun M ↦ ?_
  rw [etaleLowerShriekBaseChange_hom]
  have : IsIso ((mateEquiv (boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale l h)
      (boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale l h')).symm
      (.mk _ _ _ _ (boundedConstructibleUpperStarOfMapSquareIso l h h' hsq.w).hom)) :=
    isIso_etaleLowerShriekExchange l hsq
  exact Adjunction.map_counit_eq_inv_mateEquiv_symm
    (boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale l h)
    (boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale l h')
    (.mk _ _ _ _ (boundedConstructibleUpperStarOfMapSquareIso l h h' hsq.w).hom) M

end Canonical

end AlgebraicGeometry.ProEtale.CondensedRing
