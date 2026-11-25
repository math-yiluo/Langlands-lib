/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.TraceFormula.CompactPullback
public import WeilConjectures.TraceFormula.FibreCoherence
public import WeilConjectures.TraceFormula.PointDualizable
public import WeilConjectures.TraceFormula.Stalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported

/-!

# The lower shriek of Weil objects and the global Frobenius

Let `f : X ⟶ Y` be a morphism of schemes over `Spec k` and `Φ_X : X ⟶ X`, `Φ_Y : Y ⟶ Y`
endomorphisms with `Φ_X ≫ f = f ≫ Φ_Y`. Unlike the case of automorphisms
(`ProEtale.CondensedRing.weilLowerShriek`), the Frobenius square need not be cartesian: put
```
X' = X ×_{f, Y, Φ_Y} Y,   p : X' ⟶ X,   f' : X' ⟶ Y,   r = (Φ_X, f) : X ⟶ X',
```
so that `r ≫ p = Φ_X` and `r ≫ f' = f`; `r` is the *relative Frobenius* of `f` (blueprint
`lemma-comparison-via-relative-frobenius--text-1`). For the model Frobenii of a morphism of models
over a finite field `r` is a finite universal homeomorphism. The Frobenius comparison of `Rf_!`
(blueprint `lemma-comparison-via-relative-frobenius--2`) is then the composite
```
θ_f : Φ_Y^* Rf_! ≅ Rf'_! p^*                    (compact-support base change)
          ≅ Rf'_! Rr_* r^* p^*                   (topological invariance: the unit of r^* ⊣ Rr_*)
          ≅ Rf'_! Rr_! r^* p^*                   (Rr_! ≅ Rr_*, r being proper)
          ≅ R(r ≫ f')_! L(r ≫ p)^* = Rf_! Φ_X^*  (composition)
```
(`ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison`), and the *lower shriek of Weil
objects* `ProEtale.CondensedRing.weilLowerShriekOfFrobenius` sends `(K, φ)` to `Rf_! K` with
the Weil structure `Φ_Y^* Rf_! K ≅ Rf_! Φ_X^* K --Rf_! φ--> Rf_! K`.

## Compactly supported cohomology

For the structure morphism `a_X : X ⟶ s` and the identity of the base point, the square is
trivially cartesian (`X' = X`, `p = 𝟙`, `r = Φ_X`), and the lower shriek of Weil objects is the
*compactly supported cohomology* of Weil objects
```
RΓ_c(X, -) = ProEtale.CondensedRing.weilCompactCohomology :
  WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ (𝟙 s),
```
for every finite universal homeomorphism `Φ`. The *global operator* `F_{c,m}` of a Weil object
`(K, φ)` is the Frobenius of the Weil object `RΓ_c(X, (K, φ_m))` for the identity of `s`, an
automorphism of `RΓ_c(X, K) = Ra_{X!} K`
(`ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator`, blueprint
`definition-frobenius-correspondences-their-operators` and
`lemma-scheme-frobenius-geometric-frobenius--3`).

The comparison uses topological invariance
(`ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`): the unit
`𝟭 ⟶ Lr^* ⋙ Rr_*` is an isomorphism for a finite universal homeomorphism `r`.

## Main definitions

- `ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison`: the Frobenius comparison `θ_f`.
- `ProEtale.CondensedRing.weilLowerShriekOfFrobenius`: the lower shriek of Weil objects along a
  morphism compatible with Frobenius endomorphisms.
- `ProEtale.CondensedRing.weilCompactCohomology`: the compactly supported cohomology of Weil
  objects.
- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobenius`: the Frobenius of
  `RΓ_c(X, K)`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator`: the global Frobenius
  operator `F_{c,m}` on `RΓ_c(X, K)`.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology`:
  `RΓ_c(X, K)` is perfect (blueprint `lemma-perfect-complexes-geometric-point`).
- `ProEtale.CondensedRing.nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso`: the
  compactly supported cohomology of `Rf_! K` is that of `K`, as Weil objects (blueprint
  `lemma-comparison-via-relative-frobenius--4`).
- `ProEtale.CondensedRing.nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`: the stalk of
  `Rf_! K` at a fixed point `y` is the compactly supported cohomology of the fibre `X_y`, as Weil
  objects (proper base change, blueprint `lemma-comparison-via-relative-frobenius--4`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The lower shriek of Weil objects -/

section LowerShriek

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (f : X ⟶ Y) {p : X' ⟶ X} {f' : X' ⟶ Y}
  (sq : IsPullback p f' f ΦY) (r : X ⟶ X') (hrp : r ≫ p = ΦX) (hrf : r ≫ f' = f)
  [IsFinite r.left] [IsUniversalHomeomorphism r.left]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] [IsFinite r.left]
  [IsUniversalHomeomorphism r.left] in
include sq hrp hrf in
/-- The Frobenius endomorphisms are compatible with `f`: `Φ_X ≫ f = f ≫ Φ_Y`. -/
lemma frobenius_comp_eq_comp_frobenius : ΦX ≫ f = f ≫ ΦY :=
  calc ΦX ≫ f = r ≫ p ≫ f := by rw [← hrp, Category.assoc]
    _ = r ≫ f' ≫ ΦY := by rw [sq.w]
    _ = f ≫ ΦY := by rw [← Category.assoc, hrf]

noncomputable def weilLowerShriekFrobeniusComparisonImpl :
    boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦY ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX ⋙
        boundedConstructibleLowerShriek ℓ f :=
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have := isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction
    ℓ r
  asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq) ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (asIso (boundedConstructibleUpperStarLowerStarAdjunction
        ℓ r).unit) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).symm _)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).symm _ ≪≫
    eqToIso (by rw [hrp, hrf])

omit ℓ k in
/-- The Frobenius comparison `θ_f : Rf_! ⋙ LΦ_Y^* ≅ LΦ_X^* ⋙ Rf_!` of the lower shriek, for the
cartesian square `sq : p ≫ f = f' ≫ Φ_Y` and the relative Frobenius `r` with `r ≫ p = Φ_X` and
`r ≫ f' = f`, a finite universal homeomorphism: compact-support base change for `sq`, the unit
of `Lr^* ⊣ Rr_*`, the identification `Rr_! ≅ Rr_*` and the composition isomorphisms of the
lower shriek and of the pullback (blueprint `lemma-comparison-via-relative-frobenius--2`). -/
noncomputable irreducible_def weilLowerShriekFrobeniusComparison :=
  @weilLowerShriekFrobeniusComparisonImpl

/-- The *lower shriek of Weil objects* along a morphism `f` compatible with Frobenius
endomorphisms: a Weil object `(K, φ)` for `Φ_X` is sent to `Rf_! K` with the Weil structure
`Φ_Y^* Rf_! K ≅ Rf_! Φ_X^* K --Rf_! φ--> Rf_! K` given by
`weilLowerShriekFrobeniusComparison` (blueprint `lemma-comparison-via-relative-frobenius`). -/
noncomputable def weilLowerShriekOfFrobenius :
    WeilBoundedConstructible ℓ ΦX ⥤ WeilBoundedConstructible ℓ ΦY :=
  IsoAlgebra.mapOfNatIso (weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf)

@[simp]
lemma weilLowerShriekOfFrobenius_obj_carrier (K : WeilBoundedConstructible ℓ ΦX) :
    ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K).carrier =
      (boundedConstructibleLowerShriek ℓ f).obj K.carrier :=
  rfl

/-- The lower shriek of Weil objects lifts the lower shriek on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along the forgetful
functors. -/
lemma weilLowerShriekOfFrobenius_comp_forget :
    weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf ⋙ WeilBoundedConstructible.forget ℓ ΦY =
      WeilBoundedConstructible.forget ℓ ΦX ⋙
        boundedConstructibleLowerShriek ℓ f :=
  rfl

lemma weilLowerShriekOfFrobenius_obj_str (K : WeilBoundedConstructible ℓ ΦX) :
    ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K).str =
      (weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf).app K.carrier ≪≫
        (boundedConstructibleLowerShriek ℓ f).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

end LowerShriek

/-! ### Compactly supported cohomology -/

section CompactCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

omit [Fact (ringChar k).Prime] in
/-- The trivial cartesian square `𝟙 X ≫ a_X = a_X ≫ 𝟙 s` of the structure morphism. -/
lemma isPullback_toPoint (X : Over (Spec (.of k))) :
    IsPullback (𝟙 X) (toPoint X) (toPoint X) (𝟙 (point k)) :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

variable (Φ : X ⟶ X) [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]

/-- The *compactly supported cohomology* `RΓ_c(X, -) = Ra_{X!}` of Weil objects for a finite
universal homeomorphism `Φ`: the lower shriek of Weil objects along the structure morphism
`a_X : X ⟶ s`, with the identity of the base point and the trivial cartesian square, the relative
Frobenius being `Φ` itself. -/
noncomputable def weilCompactCohomology :
    WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ (𝟙 (point k)) :=
  weilLowerShriekOfFrobenius ℓ Φ (𝟙 (point k)) (toPoint X) (isPullback_toPoint X) Φ
    (Category.comp_id Φ) (comp_toPoint Φ)

@[simp]
lemma weilCompactCohomology_obj_carrier (K : WeilBoundedConstructible ℓ Φ) :
    ((weilCompactCohomology ℓ Φ).obj K).carrier =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        K.carrier :=
  rfl

lemma weilCompactCohomology_obj_str (K : WeilBoundedConstructible ℓ Φ) :
    ((weilCompactCohomology ℓ Φ).obj K).str =
      (weilLowerShriekFrobeniusComparison ℓ Φ (𝟙 (point k)) (toPoint X) (isPullback_toPoint X) Φ
        (Category.comp_id Φ) (comp_toPoint Φ)).app K.carrier ≪≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).mapIso
          K.str :=
  weilLowerShriekOfFrobenius_obj_str ℓ _ _ _ _ _ _ _ K

-- the rewrites unfold the restricted `ℚ̲̄_ℓ`-functors, which is expensive
/-- **The Frobenius comparison of `RΓ_c` is the pullback along `Φ`** (blueprint
`lemma-scheme-frobenius-geometric-frobenius--3`): for the trivial square of the structure
morphism, the Frobenius comparison `θ : L(𝟙 s)^* Ra_{X!} ≅ Ra_{X!} LΦ^*` composed with the
identity isomorphism `𝟭 ≅ L(𝟙 s)^*` is the pullback `Φ^♯ : RΓ_c(X, M) ⟶ RΓ_c(X, LΦ^* M)` of
`ProEtale.CondensedRing.compactPullback`. -/
lemma boundedConstructibleUpperStarId_inv_app_comp_weilLowerShriekFrobeniusComparison_hom_app
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarId _ ℓ (point k)).inv.app
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj M) ≫
      (weilLowerShriekFrobeniusComparison ℓ Φ (𝟙 (point k)) (toPoint X) (isPullback_toPoint X) Φ
        (Category.comp_id Φ) (comp_toPoint Φ)).hom.app M =
      (compactPullback ℓ Φ).app M := by
  have h₁ := congrArg
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      Φ).unit_naturality ((boundedConstructibleUpperStarId _ ℓ X).inv.app M))
  have h₂ := congrArg
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Φ).inv.naturality
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarId _ ℓ X).inv.app M)))
  have h₃ := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ Φ (toPoint X)).inv.naturality
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
      ((boundedConstructibleUpperStarId _ ℓ X).inv.app M))
  have h₄ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarId _ ℓ X).inv.app M) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Φ (𝟙 X)).inv.app M =
      eqToHom (by rw [Category.comp_id]; rfl) := by
    rw [← cancel_mono
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Φ (𝟙 X)).hom.app M),
      Category.assoc, Iso.inv_hom_id_app]
    simp only [Functor.comp_obj, Category.comp_id]
    rw [← cancel_mono
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarId _ ℓ X).hom.app M)), ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id_app, Category.assoc, boundedConstructibleUpperStarComp_id_right_app,
      eqToHom_trans]
    simp
  have h₄' := congrArg
    (boundedConstructibleLowerShriek ℓ (Φ ≫ toPoint X)).map h₄
  simp only [CategoryTheory.Functor.map_comp, Functor.comp_map, eqToHom_map, Functor.comp_obj,
    Functor.id_obj] at h₁ h₂ h₃ h₄'
  simp only [weilLowerShriekFrobeniusComparison_def, weilLowerShriekFrobeniusComparisonImpl,
    Iso.trans_hom, NatTrans.comp_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom, eqToHom_app,
    Category.id_comp, Functor.comp_obj, Functor.id_obj]
  rw [reassoc_of% (boundedConstructibleUpperStarId_inv_app_comp_baseChange_app ℓ
      (isPullback_toPoint X) M), ← reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃,
    reassoc_of% h₄', eqToHom_trans, compactPullback_app,
    boundedConstructibleLowerShriekCompToPoint_hom_app]

end CompactCohomology

/-! ### The global operator -/

namespace WeilBoundedConstructible

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Φ : X ⟶ X}

/-- The *compactly supported Frobenius* of a Weil object `(K, φ)` for a finite universal
homeomorphism `Φ`: the Frobenius of the Weil object `RΓ_c(X, (K, φ))` for the identity of the base
point, an automorphism of `RΓ_c(X, K) = Ra_{X!} K`. Explicitly it is
```
RΓ_c(X, K) ≅ L(𝟙 s)^* Ra_{X!} K --θ_{a_X}--> Ra_{X!} LΦ^* K --Ra_{X!} φ--> Ra_{X!} K.
```
-/
noncomputable def compactFrobenius (K : WeilBoundedConstructible ℓ Φ) [IsFinite Φ.left]
    [IsUniversalHomeomorphism Φ.left] :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        K.carrier :=
  ((weilCompactCohomology ℓ Φ).obj K).frobenius.hom

/- The carriers `(K.iterate m).carrier` and `K.carrier` are defeq, but the kernel check of this
defeq times out (see `ProEtale.CondensedRing.WeilBoundedConstructible.iterate_str`), so the
definition casts along `iterate_carrier`. -/
/-- The *global operator* `F_{c,m}` of a Weil object `(K, φ)` on its compactly supported
cohomology `RΓ_c(X, K) = Ra_{X!} K`: the compactly supported Frobenius of the iterate
`(K, φ_m)`, that is the Frobenius of the Weil object `RΓ_c(X, (K, φ_m))` for the identity of the
base point. Explicitly it is
```
RΓ_c(X, K) ≅ L(𝟙 s)^* Ra_{X!} K --θ_{a_X}--> Ra_{X!} LΦ_m^* K --Ra_{X!} φ_m--> Ra_{X!} K
```
(blueprint `definition-frobenius-correspondences-their-operators` and
`lemma-scheme-frobenius-geometric-frobenius--3`). It agrees with the global operator
`T_{c_m}(φ_m)` of the graph correspondence `c_m = (𝟙, Φ_m)`
(`ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator_eq_correspondenceGlobalOperator`,
blueprint `lemma-scheme-frobenius-geometric-frobenius--3`). -/
noncomputable def globalOperator (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        K.carrier :=
  eqToHom (by rw [iterate_carrier]) ≫ (K.iterate m).compactFrobenius ≫
    eqToHom (by rw [iterate_carrier])

/-- The global operator is invertible. -/
instance isIso_globalOperator (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    IsIso (K.globalOperator m) := by
  have : IsIso (K.iterate m).compactFrobenius :=
    Iso.isIso_hom ((weilCompactCohomology ℓ (frobeniusIterate Φ m)).obj (K.iterate m)).frobenius
  dsimp only [globalOperator]
  infer_instance


/-- An isomorphism of the carriers of Weil objects for the identity intertwining their
Frobenii is compatible with the structure isomorphisms. -/
lemma isoMk_condition_of_frobenius {A B : WeilBoundedConstructible ℓ (𝟙 X)}
    (e : A.carrier ≅ B.carrier) (h : A.frobenius.hom ≫ e.hom = e.hom ≫ B.frobenius.hom) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).map e.hom ≫
      B.obj.str = A.obj.str ≫ e.hom := by
  have hA := frobenius_hom A
  have hB := frobenius_hom B
  rw [IsoAlgebra.str_hom] at hA hB
  rw [← cancel_epi ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).inv.app
    A.carrier),
    ← (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).inv.naturality_assoc,
    Functor.id_map, ← hB, ← reassoc_of% hA]
  exact h.symm
/-- The compactly supported Frobenius of a Weil object `(K, φ)` is
`RΓ_c(X, φ) ∘ Φ^♯ : RΓ_c(X, K) ⟶ RΓ_c(X, LΦ^* K) ⟶ RΓ_c(X, K)` (blueprint
`lemma-scheme-frobenius-geometric-frobenius--3`). -/
lemma compactFrobenius_eq (K : WeilBoundedConstructible ℓ Φ) [IsFinite Φ.left]
    [IsUniversalHomeomorphism Φ.left] :
    K.compactFrobenius =
      (compactPullback ℓ Φ).app K.carrier ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          K.str.hom := by
  rw [compactFrobenius, frobenius_hom, weilCompactCohomology_obj_str, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, ← Category.assoc]
  exact congrArg (· ≫ (boundedConstructibleLowerShriek ℓ
    (toPoint X)).map K.str.hom)
    (boundedConstructibleUpperStarId_inv_app_comp_weilLowerShriekFrobeniusComparison_hom_app ℓ Φ
      K.carrier)

/-- **The global operator as an explicit composite** (blueprint
`lemma-scheme-frobenius-geometric-frobenius--3`): `F_{c,m} = RΓ_c(X, φ_m) ∘ Φ_m^♯`, the
pullback `Φ_m^♯ : RΓ_c(X, K) ⟶ RΓ_c(X, LΦ_m^* K)` of
`ProEtale.CondensedRing.compactPullback` followed by the iterated Weil structure `φ_m`. -/
theorem globalOperator_eq (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    K.globalOperator m =
      (compactPullback ℓ (frobeniusIterate Φ m)).app K.carrier ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          (K.iterateStr m).hom := by
  have key (a : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (h : a = K.carrier) :
      eqToHom (by rw [h]) ≫ (compactPullback ℓ (frobeniusIterate Φ m)).app a ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (frobeniusIterate Φ m)).map (eqToHom h) ≫ (K.iterateStr m).hom ≫ eqToHom h.symm) ≫
        eqToHom (by rw [h]) =
      (compactPullback ℓ (frobeniusIterate Φ m)).app K.carrier ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          (K.iterateStr m).hom := by
    subst h
    simp
  rw [globalOperator, compactFrobenius_eq, iterate_str]
  simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Category.assoc]
  exact key _ (K.iterate_carrier m)

/-- The global operator `F_{c,m}` of a Weil object is the global operator `F_{c,m}(φ)` of its
structure isomorphism `φ` as a Frobenius coefficient morphism (blueprint
`definition-frobenius-correspondences-their-operators`). -/
lemma globalOperator_eq_frobeniusCompactOperator (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsProper Φ.left] [IsFinite (frobeniusIterate Φ m).left]
    [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    K.globalOperator m = frobeniusCompactOperator ℓ K.str.hom m := by
  rw [globalOperator_eq, iterateStr_hom_eq_frobeniusCoefficientIterate, frobeniusCompactOperator]

/-- The global operator of degree `m` is the `m`-th power of the global operator of degree
one, `F_{c,m} = F_{c,1}^m` (blueprint `lemma-comparison-via-relative-frobenius--2`). -/
lemma globalOperator_eq_pow (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left]
    [IsFinite (frobeniusIterate Φ 1).left] [IsUniversalHomeomorphism (frobeniusIterate Φ 1).left] :
    K.globalOperator m =
      (End.of (K.globalOperator 1) ^ m).asHom := by
  have : IsFinite Φ.left := by
    rw [← frobeniusIterate_one Φ]
    infer_instance
  rw [globalOperator_eq_frobeniusCompactOperator, globalOperator_eq_frobeniusCompactOperator]
  exact frobeniusCompactOperator_eq_pow ℓ K.str.hom m

/-- **Perfectness of compactly supported cohomology** (blueprint
`lemma-perfect-complexes-geometric-point`): for `k` separably closed, `RΓ_c(X, K)` is a perfect
complex, that is a dualizable object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
theorem nonempty_hasRightDual_compactCohomology [IsSepClosed k]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)) :=
  nonempty_hasRightDual_point ℓ k _

/-- **Perfectness of the geometric stalks** (blueprint `lemma-perfect-complexes-geometric-point`,
clause on derived geometric stalks; section `chap-Smooth-purity`): for `k` separably closed,
the stalk `K_x̄ = Lx^* K` of a bounded constructible complex at a rational point is a perfect
complex, that is a dualizable object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
theorem nonempty_hasRightDual_stalk [IsSepClosed k]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (x : RationalPoint X) :
    Nonempty (HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :=
  nonempty_hasRightDual_point ℓ k _

end WeilBoundedConstructible

/-! ### The Frobenius comparison at a fibre -/

section Fibre

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- **The Frobenius comparison at a fibre** (blueprint `lemma-comparison-via-relative-frobenius--4`,
proof of (2)): for the fibre `Z` of `f = r ≫ f'` over a point `y` fixed by `Φ_Y`, the base change
`β : Ly^* Rf_! ≅ RΓ_c(Z, -)` intertwines `Ly^*(θ_f)` with the pullback `Φ_Z^♯`. -/
@[reassoc]
lemma baseChange_comp_weilLowerShriekFrobeniusComparison_stalk {ΦY : Y ⟶ Y} {p : X' ⟶ X}
    {f' : X' ⟶ Y} {r : X ⟶ X'} {ΦZ : Z ⟶ Z} {j : Z ⟶ X'} {y : RationalPoint Y}
    [IsFinite r.left] [IsUniversalHomeomorphism r.left] [IsProper ΦZ.left]
    (sq : IsPullback p f' (r ≫ f') ΦY) (hy : y ≫ ΦY = y)
    (hZ : IsPullback (j ≫ p) (toPoint Z) (r ≫ f') y) (hL : IsPullback j (toPoint Z) f' y)
    (hT : IsPullback (j ≫ p) ΦZ r j) (hi : ΦZ ≫ j ≫ p = (j ≫ p) ≫ r ≫ p)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ g).obj ((boundedConstructibleLowerShriek ℓ
          (r ≫ f')).obj K)) hy.symm) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y ΦY).hom.app
        ((boundedConstructibleLowerShriek ℓ (r ≫ f')).obj K) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((weilLowerShriekFrobeniusComparison ℓ (r ≫ p) ΦY (r ≫ f') sq r rfl rfl).hom.app K) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ p)).obj K) =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K ≫
      (compactPullback ℓ ΦZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ p)).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ (r ≫ p) (j ≫ p) hi).hom.app K) := by
  have hH := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ hL sq K
  have cH := boundedConstructibleLowerShriekBaseChange_padicAlgCl_congr_app_bottom ℓ hZ
    (hL.paste_horiz sq) hy.symm K
  have hk := baseChange_comp_relativeFrobenius_stalk ℓ hZ hL hT hi K
  simp only [weilLowerShriekFrobeniusComparison_def, weilLowerShriekFrobeniusComparisonImpl,
    Iso.trans_hom, NatTrans.comp_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom, eqToHom_app,
    Category.id_comp, Functor.comp_obj, Functor.id_obj]
  simp only [Functor.map_comp, Category.assoc]
  simp only [cH, hH]
  simp only [eqToHom_refl ((boundedConstructibleLowerShriek ℓ
      (r ≫ f')).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (r ≫ p)).obj K))]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp
      (X := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).obj
        ((boundedConstructibleLowerShriek ℓ (r ≫ f')).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ p)).obj K)))
      ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app _)]
  simp only [Category.assoc]
  simp only [hk]

end Fibre

/-! ### Compatibilities with the lower shriek -/

section Compatibilities

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} {f : X ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y}
  (sq : IsPullback p f' f ΦY) {r : X ⟶ X'} (hrp : r ≫ p = ΦX) (hrf : r ≫ f' = f)
  [IsFinite r.left] [IsUniversalHomeomorphism r.left]
  [IsFinite ΦX.left] [IsUniversalHomeomorphism ΦX.left]
  [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left]

omit [IsFinite ΦX.left]
  [IsUniversalHomeomorphism ΦX.left] [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left]
  [IsFinite r.left] [IsUniversalHomeomorphism r.left] in
/-- The relative Frobenius part of `θ_f` is the pullback along `r` on compactly supported
cohomology: `Rf'_!(η_r)` followed by `Rf'_! Rr_* ≅ Rf'_! Rr_! ≅ R(r ≫ f')_!` is `r^♯` under the
composition isomorphisms. -/
lemma compToPoint_inv_app_comp_relativeFrobenius (r : X ⟶ X') (f' : X' ⟶ Y) [IsProper r.left]
    (M : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.app M ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriek ℓ f').map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            r).unit.app M)) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriek ℓ f').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M))) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)) =
    (compactPullback ℓ r).app M ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ (r ≫ f')).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M) := by
  have h₁ := (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      r).unit.app M)
  have h₂ := (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M))
  have h₃ := boundedConstructibleLowerShriekCompToPoint_assoc ℓ r f'
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)
  simp only [Functor.comp_map] at h₁ h₂
  have h₃' : (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.app
        ((boundedConstructibleLowerShriek ℓ r).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)) =
      (boundedConstructibleLowerShriekCompToPoint ℓ r).hom.app _ ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ (r ≫ f')).inv.app _ := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekCompToPoint ℓ r).inv.app _),
      ← reassoc_of% h₃, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂, h₃', compactPullback_app]
  simp only [Category.assoc]

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] [IsFinite ΦX.left]
  [IsUniversalHomeomorphism ΦX.left] [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left] in
/-- The casts at the end of `θ_f`. -/
lemma compToPoint_inv_app_comp_eqToHom {a : X ⟶ X} {b : X ⟶ Y} (ha : a = ΦX) (hb : b = f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : (boundedConstructibleLowerShriek ℓ b).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a).obj K) =
      (boundedConstructibleLowerShriek ℓ f).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K)) :
    (boundedConstructibleLowerShriekCompToPoint ℓ b).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        (eqToHom e) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K) =
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      (eqToHom (by rw [ha])) := by
  subst ha hb
  simp

omit [IsUniversalHomeomorphism ΦX.left] [IsUniversalHomeomorphism ΦY.left] in
include sq hrp hrf in
/-- **The Frobenius comparison of `Rf_!` on compactly supported cohomology** (blueprint
`lemma-comparison-via-relative-frobenius--4`, proof of (1)): under the composition isomorphism
`c_f : RΓ_c(Y, Rf_! K) ≅ RΓ_c(X, K)`, `RΓ_c(Y, θ_f) ∘ Φ_Y^♯` is `Φ_X^♯`. -/
@[reassoc]
lemma compactPullback_comp_weilLowerShriekFrobeniusComparison
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ ΦY).app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf).hom.app K) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K) =
    (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K ≫ (compactPullback ℓ ΦX).app K := by
  have : IsFinite p.left := MorphismProperty.of_isPullback sq.overLeft.flip inferInstance
  have : IsProper (r ≫ p).left := by
    rw [Over.comp_left]
    infer_instance
  have hB : (compactPullback ℓ ΦY).app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K) =
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K ≫ (compactPullback ℓ p).app K ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.app _ := by
    rw [← reassoc_of% (compactPullback_app_comp_baseChange ℓ sq K), Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, Category.comp_id]
  have hn := (boundedConstructibleLowerShriekCompToPoint ℓ (r ≫ f')).inv.naturality
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).inv.app K)
  simp only [Functor.comp_map] at hn
  simp only [weilLowerShriekFrobeniusComparison_def, weilLowerShriekFrobeniusComparisonImpl,
    Iso.trans_hom, NatTrans.comp_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom, eqToHom_app,
    Category.id_comp, Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hB, reassoc_of% (compToPoint_inv_app_comp_relativeFrobenius ℓ r f' _),
    ← reassoc_of% hn, compToPoint_inv_app_comp_eqToHom ℓ hrp hrf,
    ← compactPullback_app_congr ℓ hrp, compactPullback_comp_app]
  simp only [Category.assoc]

-- the defeq of the carriers of the lower shriek of Weil objects with `Rf_! K` is slow
/-- **The Leray isomorphism for Weil objects** (blueprint
`lemma-comparison-via-relative-frobenius--4`, the global operators): the compactly supported
cohomology of `Rf_! K` is that of `K`, `RΓ_c(Y, Rf_! K) ≅ RΓ_c(X, K)`, as Weil objects for the
identity of the base point. In particular the global operators of `K` and of `Rf_! K` have the same
trace. -/
theorem nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso
    (K : WeilBoundedConstructible ℓ ΦX) :
    Nonempty ((weilCompactCohomology ℓ ΦY).obj
        ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K) ≅
      (weilCompactCohomology ℓ ΦX).obj K) := by
  refine ⟨IsoAlgebra.isoMk ((boundedConstructibleLowerShriekCompToPoint ℓ f).app K.carrier)
    (WeilBoundedConstructible.isoMk_condition_of_frobenius _ ?_)⟩
  have hn := (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.naturality K.str.hom
  simp only [Functor.comp_map] at hn
  rw [← WeilBoundedConstructible.compactFrobenius, ← WeilBoundedConstructible.compactFrobenius,
    WeilBoundedConstructible.compactFrobenius_eq, WeilBoundedConstructible.compactFrobenius_eq,
    weilLowerShriekOfFrobenius_obj_str]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hn]
  exact compactPullback_comp_weilLowerShriekFrobeniusComparison_assoc ℓ sq hrp hrf K.carrier _

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] {ΦZ : Z ⟶ Z} [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]
  {i : Z ⟶ X} (hi : ΦZ ≫ i = i ≫ ΦX) {y : RationalPoint Y} (hy : y ≫ ΦY = y)
  (hZ : IsPullback i (toPoint Z) f y)

-- the defeq of the carriers of the lower shriek of Weil objects with `Rf_! K` is slow
omit [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left] in
include hZ in
/-- **Proper base change for Weil objects** (blueprint `lemma-comparison-via-relative-frobenius--4`,
the stalks): for a rational point `y` of `Y` fixed by `Φ_Y` with fibre `Z = X ×_Y y` carrying a
Frobenius `Φ_Z` compatible with `Φ_X`, the stalk at `y` of `Rf_! K` is the compactly supported
cohomology of the restriction of `K` to the fibre, `(Rf_! K)_ȳ ≅ RΓ_c(Z, K|_Z)`, as Weil objects
for the identity of the base point. In particular the local Frobenius of `Rf_! K` at `y` and the
global operator of `K|_Z` have the same trace. -/
theorem nonempty_weilStalk_weilLowerShriekOfFrobenius_iso (K : WeilBoundedConstructible ℓ ΦX) :
    Nonempty ((weilStalk ℓ ΦY y hy).obj
        ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K) ≅
      (weilCompactCohomology ℓ ΦZ).obj ((weilUpperStar ℓ ΦZ ΦX i hi).obj K)) := by
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j : Z ⟶ X', j ≫ p = i ∧ j ≫ f' = toPoint Z ≫ y :=
    ⟨sq.lift i (toPoint Z ≫ y) (by rw [hZ.w, Category.assoc, hy]), sq.lift_fst _ _ _,
      sq.lift_snd _ _ _⟩
  subst hj₁ hrp hrf
  have hL : IsPullback j (toPoint Z) f' y := IsPullback.of_right (by rw [hy]; exact hZ) hj₂ sq
  have hTw : (j ≫ p) ≫ r = ΦZ ≫ j := sq.hom_ext
    (by simp only [Category.assoc] at hi ⊢; exact hi.symm)
    (by rw [Category.assoc, hZ.w, Category.assoc, hj₂, ← Category.assoc, comp_toPoint])
  have hT : IsPullback (j ≫ p) ΦZ r j := IsPullback.of_bot (by rw [comp_toPoint]; exact hZ) hTw hL
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ
  refine ⟨IsoAlgebra.isoMk (asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    hZ).app K.carrier)) (WeilBoundedConstructible.isoMk_condition_of_frobenius _ ?_)⟩
  rw [asIso_hom, WeilBoundedConstructible.weilStalk_obj_frobenius_hom_eq,
    ← WeilBoundedConstructible.compactFrobenius,
    WeilBoundedConstructible.compactFrobenius_eq, weilLowerShriekOfFrobenius_obj_str,
    weilUpperStar_obj_str]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hn := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).naturality K.str.hom
  simp only [Functor.comp_map] at hn
  rw [hn]
  exact baseChange_comp_weilLowerShriekFrobeniusComparison_stalk_assoc ℓ sq hy hZ hL hT hi
    K.carrier _

end Compatibilities

end AlgebraicGeometry.ProEtale.CondensedRing
