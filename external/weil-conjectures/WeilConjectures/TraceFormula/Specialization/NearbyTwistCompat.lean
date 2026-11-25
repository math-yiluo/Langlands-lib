/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceOpen
public import WeilConjectures.TraceFormula.Specialization.NearbyExceptionalExchangeSlice
import WeilConjectures.Tactic.TransportExact

/-!

# The exceptional exchanges and the twists by invertible objects

The inputs `m`, `n`, `hm`, `hκP` of `NearbyCyclesModel.exists_twist_of_composition_law` for the
twist `T = ℚ̄_ℓ(0)[n]` (blueprint `lemma-nearby-duality-slice--1`, the twist (1)).

For a morphism of models `φ : N ⟶ M` over proper `i₁`, `i₂`, the exceptional exchange
`β = exceptionalExchange ν` of a compact-support exchange `ν` inverse to the proper exchange
`χ_φ` is the mate of `χ_φ⁻¹` under `Ri_* ⊣ Ri^!`, and `χ_φ` is the mate of the pullback exchange
`α_φ` under `Li^* ⊣ Ri_*`. Twist isomorphisms `F(- ⊗ T) ≅ F(-) ⊗ T` are carried along mates:

* `Li^*(A ⊗ T) ≅ Li^* A ⊗ T` from the monoidal structure of `Li^*`
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarZeroTwistIso`);
* its mate `Ri_* K ⊗ T ⟶ Ri_*(K ⊗ T)`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarZeroTwistMap`)
  and the mate `Ri^! Z ⊗ T ⟶ Ri^!(Z ⊗ T)` of its inverse
  (`ProEtale.CondensedRing.upperShriekZeroTwistMap`), invertible since `T` is invertible
  (`CategoryTheory.isIso_mateEquiv_of_isEquivalence`); the inverse of the latter is
  `m = ProEtale.CondensedRing.upperShriekZeroTwistIso`, natural by
  `ProEtale.CondensedRing.upperShriekZeroTwistIso_hom_naturality`.

The compatibility of `α_φ` with the twist isomorphisms `κ` of nearby cycles
(`NearbyCyclesModel.Hom.liftExchange_zeroTwistIso`) passes to `χ_φ` and then to `β` by two cubes of
mates (`CategoryTheory.mate_twist_compat`, `CategoryTheory.mate_inv_twist_compat`), giving
`NearbyCyclesModel.exceptionalExchange_zeroTwistIso`, the hypothesis `hκP`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Tensoring on the right with an invertible object is an equivalence. -/
lemma isEquivalence_tensorRight_of_isInvertible {C : Type*} [Category C] [MonoidalCategory C]
    {T : C} (hT : IsInvertible T) : (tensorRight T).IsEquivalence := by
  obtain ⟨T', ⟨e⟩, ⟨e'⟩⟩ := hT
  exact (tensorRightEquivalenceOfTensorIso e e').isEquivalence_functor

/-- Inverting the invertible morphisms of a commutative square of composites. -/
lemma comp_inv_eq_inv_comp_of_comp {C : Type*} [Category C] {a b c d e f : C} (x : a ⟶ b)
    (y : b ⟶ c) (z : c ⟶ d) (u : a ⟶ e) (v : e ⟶ f) (w : f ⟶ d) [IsIso y] [IsIso z] [IsIso u]
    [IsIso v] (h : x ≫ y ≫ z = u ≫ v ≫ w) :
    w ≫ inv z ≫ inv y = inv v ≫ inv u ≫ x := by
  rw [← cancel_epi (u ≫ v), Category.assoc, ← reassoc_of% h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The twist isomorphism `F(A ⊗ T) ≅ F A ⊗ T'` of a monoidal functor `F`, for `F T ≅ T'`. -/
noncomputable def Functor.tensorRightCommIso {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (T : C) {T' : D}
    (t : F.obj T ≅ T') : tensorRight T ⋙ F ≅ F ⋙ tensorRight T' :=
  NatIso.ofComponents (fun A ↦ (Functor.Monoidal.μIso F A T).symm ≪≫ whiskerLeftIso _ t)
    (fun f ↦ by
      change F.map (f ▷ T) ≫ ((Functor.Monoidal.μIso F _ T).symm ≪≫ whiskerLeftIso _ t).hom =
        ((Functor.Monoidal.μIso F _ T).symm ≪≫ whiskerLeftIso _ t).hom ≫ F.map f ▷ T'
      rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
        Functor.Monoidal.μIso_inv, whiskerLeftIso_hom, whiskerLeftIso_hom, Category.assoc,
        whisker_exchange]
      exact (Functor.OplaxMonoidal.δ_natural_left_assoc F f T _).symm)

section Abstract

variable {DX DY EX EY : Type*} [Category DX] [Category DY] [Category EX] [Category EY]
  [MonoidalCategory DX] [MonoidalCategory DY] [MonoidalCategory EX] [MonoidalCategory EY]
  {L : DX ⥤ DY} {R : DY ⥤ DX} {L' : EX ⥤ EY} {R' : EY ⥤ EX} {U : DX ⥤ DY} {U' : EX ⥤ EY}
  {ΨM : DX ⥤ EX} {ΨN : DY ⥤ EY} {TX : DX} {TY : DY} {TX' : EX} {TY' : EY}

/-- **The pushforward exchange and the twists**: if the exchange `α : Ψ_M ⋙ L' ⟶ L ⋙ Ψ_N` of
left adjoints is compatible with twist isomorphisms `e`, `e'`, `κ_M`, `κ_N` of `L`, `L'`, `Ψ_M`,
`Ψ_N` with the tensor products by `T`, then its mate `χ : R ⋙ Ψ_M ⟶ Ψ_N ⋙ R'` is compatible with
the mates `βr`, `βs` of `e`, `e'` and the inverses of `κ_M`, `κ_N`. -/
lemma mate_twist_compat (adj : L ⊣ R) (adj' : L' ⊣ R')
    (e : tensorRight TX ⋙ L ≅ L ⋙ tensorRight TY)
    (e' : tensorRight TX' ⋙ L' ≅ L' ⋙ tensorRight TY')
    (κM : tensorRight TX ⋙ ΨM ≅ ΨM ⋙ tensorRight TX')
    (κN : tensorRight TY ⋙ ΨN ≅ ΨN ⋙ tensorRight TY')
    (α : ΨM ⋙ L' ⟶ L ⋙ ΨN)
    (hα : ∀ A, L'.map (κM.hom.app A) ≫ e'.hom.app (ΨM.obj A) ≫ α.app A ▷ TY' =
      α.app (A ⊗ TX) ≫ ΨN.map (e.hom.app A) ≫ κN.hom.app (L.obj A))
    (χ : R ⋙ ΨM ⟶ ΨN ⋙ R') (hχ : χ = (mateEquiv adj adj' α))
    (βr : R ⋙ tensorRight TX ⟶ tensorRight TY ⋙ R)
    (hβr : βr = (mateEquiv adj adj e.hom))
    (βs : R' ⋙ tensorRight TX' ⟶ tensorRight TY' ⋙ R')
    (hβs : βs = (mateEquiv adj' adj' e'.hom)) (K : DY) :
    κM.inv.app (R.obj K) ≫ ΨM.map (βr.app K) ≫ χ.app (K ⊗ TY) =
      χ.app K ▷ TX' ≫ βs.app (ΨN.obj K) ≫ R'.map (κN.inv.app K) := by
  subst hχ hβr hβs
  refine mateEquiv_app_cube adj adj adj' adj' e.hom e'.hom α α κM.inv κN.inv (fun A ↦ ?_) K
  rw [← cancel_mono (κN.hom.app (L.obj A))]
  simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  erw [← hα A]
  rw [← L'.map_comp_assoc, Iso.inv_hom_id_app]
  erw [L'.map_id, Category.id_comp]
  rfl

/-- **The exceptional exchange and the twists**: in the situation of
`CategoryTheory.mate_twist_compat`, with `χ`, `βr`, `βs` invertible (e.g. by proper base change,
`T` invertible), the mate `β : U ⋙ Ψ_N ⟶ Ψ_M ⋙ U'` of `χ⁻¹` for adjunctions `R ⊣ U`,
`R' ⊣ U'` is compatible with the mates `γr`, `γs` of `βr⁻¹`, `βs⁻¹` and the inverses of `κ_M`,
`κ_N`. -/
lemma mate_inv_twist_compat (adj : L ⊣ R) (adj' : L' ⊣ R') (adjU : R ⊣ U) (adjU' : R' ⊣ U')
    (e : tensorRight TX ⋙ L ≅ L ⋙ tensorRight TY)
    (e' : tensorRight TX' ⋙ L' ≅ L' ⋙ tensorRight TY')
    (κM : tensorRight TX ⋙ ΨM ≅ ΨM ⋙ tensorRight TX')
    (κN : tensorRight TY ⋙ ΨN ≅ ΨN ⋙ tensorRight TY')
    (α : ΨM ⋙ L' ⟶ L ⋙ ΨN)
    (hα : ∀ A, L'.map (κM.hom.app A) ≫ e'.hom.app (ΨM.obj A) ≫ α.app A ▷ TY' =
      α.app (A ⊗ TX) ≫ ΨN.map (e.hom.app A) ≫ κN.hom.app (L.obj A))
    (χ : R ⋙ ΨM ⟶ ΨN ⋙ R') (hχ : χ = (mateEquiv adj adj' α)) [IsIso χ]
    (βr : R ⋙ tensorRight TX ⟶ tensorRight TY ⋙ R)
    (hβr : βr = (mateEquiv adj adj e.hom)) [IsIso βr]
    (βs : R' ⋙ tensorRight TX' ⟶ tensorRight TY' ⋙ R')
    (hβs : βs = (mateEquiv adj' adj' e'.hom)) [IsIso βs]
    (β : U ⋙ ΨN ⟶ ΨM ⋙ U') (hβ : β = (mateEquiv adjU adjU' (inv χ)))
    (γr : U ⋙ tensorRight TY ⟶ tensorRight TX ⋙ U)
    (hγr : γr = (mateEquiv adjU adjU (inv βr)))
    (γs : U' ⋙ tensorRight TY' ⟶ tensorRight TX' ⋙ U')
    (hγs : γs = (mateEquiv adjU' adjU' (inv βs))) (Z : DX) :
    κN.inv.app (U.obj Z) ≫ ΨN.map (γr.app Z) ≫ β.app (Z ⊗ TX) =
      β.app Z ▷ TY' ≫ γs.app (ΨM.obj Z) ≫ U'.map (κM.inv.app Z) := by
  subst hβ hγr hγs
  refine mateEquiv_app_cube adjU adjU adjU' adjU' (inv βr) (inv βs) (inv χ) (inv χ)
    κN.inv κM.inv (fun K ↦ ?_) Z
  have h := mate_twist_compat adj adj' e e' κM κN α hα χ hχ βr hβr βs hβs K
  have := comp_inv_eq_inv_comp_of_comp _ _ _ _ _ _ h
  simp only [Functor.comp_obj, NatIso.isIso_inv_app, Functor.map_inv]
  exact this




/-- **The exceptional exchange and the twists**, in the form of the hypothesis `hκP` of
`NearbyCyclesModel.exists_twist_of_composition_law`: with `m = γs⁻¹` and `n = γr⁻¹`,
`β(ω ⊗ T) ≫ U'(κ_M) ≫ m = Ψ_N(n) ≫ κ_N ≫ β(ω) ▷ T`. -/
lemma mate_inv_twist_compat' (adj : L ⊣ R) (adj' : L' ⊣ R') (adjU : R ⊣ U) (adjU' : R' ⊣ U')
    (e : tensorRight TX ⋙ L ≅ L ⋙ tensorRight TY)
    (e' : tensorRight TX' ⋙ L' ≅ L' ⋙ tensorRight TY')
    (κM : tensorRight TX ⋙ ΨM ≅ ΨM ⋙ tensorRight TX')
    (κN : tensorRight TY ⋙ ΨN ≅ ΨN ⋙ tensorRight TY')
    (α : ΨM ⋙ L' ⟶ L ⋙ ΨN)
    (hα : ∀ A, L'.map (κM.hom.app A) ≫ e'.hom.app (ΨM.obj A) ≫ α.app A ▷ TY' =
      α.app (A ⊗ TX) ≫ ΨN.map (e.hom.app A) ≫ κN.hom.app (L.obj A))
    (χ : R ⋙ ΨM ⟶ ΨN ⋙ R') (hχ : χ = (mateEquiv adj adj' α)) [IsIso χ]
    (βr : R ⋙ tensorRight TX ⟶ tensorRight TY ⋙ R)
    (hβr : βr = (mateEquiv adj adj e.hom)) [IsIso βr]
    (βs : R' ⋙ tensorRight TX' ⟶ tensorRight TY' ⋙ R')
    (hβs : βs = (mateEquiv adj' adj' e'.hom)) [IsIso βs]
    (β : U ⋙ ΨN ⟶ ΨM ⋙ U') (hβ : β = (mateEquiv adjU adjU' (inv χ)))
    (γr : U ⋙ tensorRight TY ⟶ tensorRight TX ⋙ U)
    (hγr : γr = (mateEquiv adjU adjU (inv βr))) [IsIso γr]
    (γs : U' ⋙ tensorRight TY' ⟶ tensorRight TX' ⋙ U')
    (hγs : γs = (mateEquiv adjU' adjU' (inv βs))) [IsIso γs] (ω : DX) :
    β.app (ω ⊗ TX) ≫ U'.map (κM.hom.app ω) ≫ inv (γs.app (ΨM.obj ω)) =
      ΨN.map (inv (γr.app ω)) ≫ κN.hom.app (U.obj ω) ≫ β.app ω ▷ TY' := by
  have h := mate_inv_twist_compat adj adj' adjU adjU' e e' κM κN α hα χ hχ βr hβr βs hβs β hβ γr
    hγr γs hγs ω
  rw [← cancel_epi (κN.inv.app (U.obj ω) ≫ ΨN.map (γr.app ω)), Category.assoc, reassoc_of% h]
  simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [U'.map_id, Category.id_comp]
  rw [IsIso.hom_inv_id, IsIso.hom_inv_id, ΨN.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact Category.comp_id _

end Abstract

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory`, as in
-- `NearbyCyclesModel.zeroTwistIso`.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

section Twist

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] (i : Y ⟶ X) (n : ℤ)

/-- The twist isomorphism `Li^*(A ⊗ ℚ̄_ℓ(0)[n]) ≅ Li^* A ⊗ ℚ̄_ℓ(0)[n]` of the derived pullback on
bounded constructible complexes: the monoidal structure of `Li^*` and
`Li^* ℚ̄_ℓ(0)[n] ≅ ℚ̄_ℓ(0)[n]`. -/
noncomputable def boundedConstructibleUpperStarZeroTwistIso :
    tensorRight (boundedConstructibleTateTwist ℓ X 0 n) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i ⋙
        tensorRight (boundedConstructibleTateTwist ℓ Y 0 n) :=
  Functor.tensorRightCommIso _ _
    (NearbyCyclesModel.boundedConstructibleTateTwistZeroUpperStarIso ℓ (X := X) (Y := Y) i.left n)

lemma boundedConstructibleUpperStarZeroTwistIso_hom_app
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarZeroTwistIso ℓ i n).hom.app A =
      ((Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) i.left)
        A (boundedConstructibleTateTwist ℓ X 0 n)).symm ≪≫
      whiskerLeftIso _ (NearbyCyclesModel.boundedConstructibleTateTwistZeroUpperStarIso ℓ
        (X := X) (Y := Y) i.left n)).hom :=
  rfl

/-- The twist map `Ri_* K ⊗ ℚ̄_ℓ(0)[n] ⟶ Ri_*(K ⊗ ℚ̄_ℓ(0)[n])` (the projection morphism): the mate
of `ProEtale.CondensedRing.boundedConstructibleUpperStarZeroTwistIso` under `Li^* ⊣ Ri_*`. -/
noncomputable def boundedConstructibleLowerStarZeroTwistMap :
    boundedConstructibleLowerStar ℓ i ⋙ tensorRight (boundedConstructibleTateTwist ℓ X 0 n) ⟶
      tensorRight (boundedConstructibleTateTwist ℓ Y 0 n) ⋙ boundedConstructibleLowerStar ℓ i :=
  (mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ i)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i)
    (boundedConstructibleUpperStarZeroTwistIso ℓ i n).hom)

instance isIso_boundedConstructibleLowerStarZeroTwistMap :
    IsIso (boundedConstructibleLowerStarZeroTwistMap ℓ i n) := by
  have := isEquivalence_tensorRight_of_isInvertible
    (isInvertible_boundedConstructibleTateTwist_zero ℓ X n)
  have := isEquivalence_tensorRight_of_isInvertible
    (isInvertible_boundedConstructibleTateTwist_zero ℓ Y n)
  exact isIso_mateEquiv_of_isEquivalence _ _ _

variable [IsProper i.left]

/-- The twist map `Ri^! Z ⊗ ℚ̄_ℓ(0)[n] ⟶ Ri^!(Z ⊗ ℚ̄_ℓ(0)[n])` of the exceptional inverse image
along a proper `i`: the mate of the inverse of
`ProEtale.CondensedRing.boundedConstructibleLowerStarZeroTwistMap` under `Ri_* ⊣ Ri^!`. -/
noncomputable def upperShriekZeroTwistMap :
    boundedConstructibleUpperShriek ℓ i ⋙ tensorRight (boundedConstructibleTateTwist ℓ Y 0 n) ⟶
      tensorRight (boundedConstructibleTateTwist ℓ X 0 n) ⋙ boundedConstructibleUpperShriek ℓ i :=
  (mateEquiv (lowerStarUpperShriekAdjunction ℓ i) (lowerStarUpperShriekAdjunction ℓ i)
    (inv (boundedConstructibleLowerStarZeroTwistMap ℓ i n)))

instance isIso_upperShriekZeroTwistMap : IsIso (upperShriekZeroTwistMap ℓ i n) := by
  have := isEquivalence_tensorRight_of_isInvertible
    (isInvertible_boundedConstructibleTateTwist_zero ℓ X n)
  have := isEquivalence_tensorRight_of_isInvertible
    (isInvertible_boundedConstructibleTateTwist_zero ℓ Y n)
  exact isIso_mateEquiv_of_isEquivalence _ _ _

/-- **The exceptional inverse image commutes with the twist by `ℚ̄_ℓ(0)[n]`**:
`Ri^!(Z ⊗ ℚ̄_ℓ(0)[n]) ≅ Ri^! Z ⊗ ℚ̄_ℓ(0)[n]` for proper `i`, the inverse of
`ProEtale.CondensedRing.upperShriekZeroTwistMap`. -/
noncomputable def upperShriekZeroTwistIso (Z : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriek ℓ i).obj (Z ⊗ boundedConstructibleTateTwist ℓ X 0 n) ≅
      (boundedConstructibleUpperShriek ℓ i).obj Z ⊗ boundedConstructibleTateTwist ℓ Y 0 n :=
  (asIso ((upperShriekZeroTwistMap ℓ i n).app Z)).symm

lemma upperShriekZeroTwistIso_hom (Z : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (upperShriekZeroTwistIso ℓ i n Z).hom = inv ((upperShriekZeroTwistMap ℓ i n).app Z) :=
  rfl

/-- **Naturality of `Ri^!(Z ⊗ T) ≅ Ri^! Z ⊗ T`**. -/
lemma upperShriekZeroTwistIso_hom_naturality
    {Z Z' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : Z ⟶ Z') :
    (boundedConstructibleUpperShriek ℓ i).map (f ▷ boundedConstructibleTateTwist ℓ X 0 n) ≫
        (upperShriekZeroTwistIso ℓ i n Z').hom =
      (upperShriekZeroTwistIso ℓ i n Z).hom ≫
        (boundedConstructibleUpperShriek ℓ i).map f ▷ boundedConstructibleTateTwist ℓ Y 0 n := by
  rw [upperShriekZeroTwistIso_hom, upperShriekZeroTwistIso_hom, IsIso.eq_inv_comp,
    ← Category.assoc, IsIso.comp_inv_eq]
  exact ((upperShriekZeroTwistMap ℓ i n).naturality f).symm

end Twist

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k] [Field k'] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X₁ Y₁ : Over (Spec (.of k))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
  [IsSeparated X₁.hom] [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X₁.left X'.left} {N : NearbyCyclesModel Y₁.left Y'.left}
  {i₁ : Y₁ ⟶ X₁} {i₂ : Y' ⟶ X'} [IsProper i₁.left] [IsProper i₂.left]

section

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {X'' : Over (Spec (.of k'))} [LocallyOfFiniteType X''.hom]
  [QuasiCompact X''.hom] [IsSeparated X''.hom] (M₀ : NearbyCyclesModel X.left X''.left)

/-- The twist isomorphisms `κ_A : Ψ(A ⊗ ℚ̄_ℓ(0)[n]) ≅ Ψ A ⊗ ℚ̄_ℓ(0)[n]`
(`NearbyCyclesModel.zeroTwistIso`) as a natural isomorphism. -/
noncomputable def zeroTwistNatIso
    (hP : M₀.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (q : M₀.total ⟶ trait k') (n : ℤ) :
    tensorRight (boundedConstructibleTateTwist ℓ X 0 n) ⋙ boundedConstructibleNearbyCycles hP ≅
      boundedConstructibleNearbyCycles hP ⋙
        tensorRight (boundedConstructibleTateTwist ℓ X'' 0 n) :=
  NatIso.ofComponents (M₀.zeroTwistIso hP q n) (zeroTwistIso_hom_naturality hP q n)

end

omit [IsProper i₁.left] [IsProper i₂.left] in
/-- The compatibility of the pullback exchange of a morphism of models with the twist
isomorphisms (`NearbyCyclesModel.Hom.liftExchange_zeroTwistIso`), in the shape of the hypothesis
of `CategoryTheory.mate_twist_compat`. -/
lemma pullbackExchange_zeroTwistIso (φ : N.Hom M i₁.left i₂.left)
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (qM : M.total ⟶ trait k') (qN : N.total ⟶ trait k') (n : ℤ)
    (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i₂).map
        ((M.zeroTwistNatIso hM qM n).hom.app A) ≫
      (boundedConstructibleUpperStarZeroTwistIso ℓ i₂ n).hom.app
        ((boundedConstructibleNearbyCycles hM).obj A) ≫
      (φ.boundedConstructiblePullbackExchange ℓ hN hM).app A ▷
        boundedConstructibleTateTwist ℓ Y' 0 n =
    (φ.boundedConstructiblePullbackExchange ℓ hN hM).app
        (A ⊗ boundedConstructibleTateTwist ℓ X₁ 0 n) ≫
      (boundedConstructibleNearbyCycles hN).map
        ((boundedConstructibleUpperStarZeroTwistIso ℓ i₁ n).hom.app A) ≫
      (N.zeroTwistNatIso hN qN n).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i₁).obj A) := by
  have h := φ.liftExchange_zeroTwistIso hM hN qM qN _
    (Hom.boundedConstructiblePullbackExchange_eq_liftExchange ℓ φ hN hM) n A
  rw [boundedConstructibleUpperStarZeroTwistIso_hom_app,
    boundedConstructibleUpperStarZeroTwistIso_hom_app]
  exact h

/-- **The exceptional exchange and the twists by `ℚ̄_ℓ(0)[n]`** (the hypothesis `hκP` of
`NearbyCyclesModel.exists_twist_of_composition_law`): for a morphism of models `φ : N ⟶ M` over
proper `i₁`, `i₂` with invertible proper exchange `χ_φ` and a compact-support exchange `ν` inverse
to it, the exceptional exchange `β = exceptionalExchange ν` satisfies
`β(ω ⊗ T) ≫ Ri₂^!(κ_M) ≫ m = Ψ_N(n) ≫ κ_N ≫ β(ω) ▷ T`, where `κ` are the twist isomorphisms of
nearby cycles (`NearbyCyclesModel.zeroTwistIso`) and `m`, `n` those of the exceptional inverse
images (`ProEtale.CondensedRing.upperShriekZeroTwistIso`). -/
theorem exceptionalExchange_zeroTwistIso (φ : N.Hom M i₁.left i₂.left)
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (qM : M.total ⟶ trait k') (qN : N.total ⟶ trait k')
    [IsIso (φ.boundedConstructiblePushforwardExchange ℓ hN hM)]
    (ν : boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleLowerShriek ℓ i₂ ⟶
      boundedConstructibleLowerShriek ℓ i₁ ⋙ boundedConstructibleNearbyCycles hM)
    (hν : ∀ K, (φ.boundedConstructiblePushforwardExchange ℓ hN hM).app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
        ((boundedConstructibleNearbyCycles hN).obj K) ≫ ν.app K =
        (boundedConstructibleNearbyCycles hM).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app K))
    (n : ℤ) (ω : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (exceptionalExchange ℓ i₁ i₂ ν).app (ω ⊗ boundedConstructibleTateTwist ℓ X₁ 0 n) ≫
        (boundedConstructibleUpperShriek ℓ i₂).map (M.zeroTwistIso hM qM n ω).hom ≫
        (upperShriekZeroTwistIso ℓ i₂ n ((boundedConstructibleNearbyCycles hM).obj ω)).hom =
      (boundedConstructibleNearbyCycles hN).map (upperShriekZeroTwistIso ℓ i₁ n ω).hom ≫
        (N.zeroTwistIso hN qN n ((boundedConstructibleUpperShriek ℓ i₁).obj ω)).hom ≫
        (exceptionalExchange ℓ i₁ i₂ ν).app ω ▷ boundedConstructibleTateTwist ℓ Y' 0 n := by
  have := mate_inv_twist_compat' (ΨM := boundedConstructibleNearbyCycles hM)
    (ΨN := boundedConstructibleNearbyCycles hN)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i₁)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i₂)
    (lowerStarUpperShriekAdjunction ℓ i₁) (lowerStarUpperShriekAdjunction ℓ i₂)
    (boundedConstructibleUpperStarZeroTwistIso ℓ i₁ n)
    (boundedConstructibleUpperStarZeroTwistIso ℓ i₂ n)
    (M.zeroTwistNatIso hM qM n) (N.zeroTwistNatIso hN qN n)
    (φ.boundedConstructiblePullbackExchange ℓ hN hM)
    ?hα
    (φ.boundedConstructiblePushforwardExchange ℓ hN hM)
    (Hom.boundedConstructiblePushforwardExchange_eq_mateEquiv ℓ φ hN hM)
    (boundedConstructibleLowerStarZeroTwistMap ℓ i₁ n) rfl
    (boundedConstructibleLowerStarZeroTwistMap ℓ i₂ n) rfl
    (exceptionalExchange ℓ i₁ i₂ ν)
    (NatTrans.ext (funext (exceptionalExchange_app_eq_mateEquiv_inv ℓ hM hN φ ν hν)))
    (upperShriekZeroTwistMap ℓ i₁ n) rfl (upperShriekZeroTwistMap ℓ i₂ n) rfl ω
  · exact this
  · intro A
    transport_exact pullbackExchange_zeroTwistIso φ hM hN qM qN n A

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
