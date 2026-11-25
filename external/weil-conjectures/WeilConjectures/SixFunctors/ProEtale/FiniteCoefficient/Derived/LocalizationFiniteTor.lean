/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# The closed-support triangle on pro-étale complexes of finite Tor amplitude

Let `k` be a field, `X` a scheme of finite type over `k`, `i : Z ⟶ X` a closed immersion and
`j : U ⟶ X` the complementary quasi-compact open immersion, and let `Λ` be a finite ring
killed by an integer invertible in `k`: the finite coefficient stage `A_{E,n}` of blueprint
`lemma-local-cohomology-right-adjoint--2`. This file proves clauses (1')–(4') of that proposition at
the finite stage, on the bounded constructible pro-étale complexes of finite Tor amplitude
`Dᵇc_ctf(-, Λ)` (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`), with
explicit Tor amplitude intervals, for `dim U ≤ d`:

1'. `Rj_*` sends Tor amplitude `[a, b]` to `[a, b + 2d]`
   (`AlgebraicGeometry.ProEtale.torAmplitudeIn_rightDerivedFunctor_lowerStar_of_isOpenImmersion`);
2'. `Ri^!` sends Tor amplitude `[a, b]` to `[a, b + 2d + 1]`
   (`AlgebraicGeometry.ProEtale.torAmplitudeIn_closedUpperShriek_rightDerivedFunctor_obj`);
3'. `i^*`, `j^*` and `Ri_*` preserve Tor amplitude intervals
   (`AlgebraicGeometry.ProEtale.torAmplitudeIn_mapDerivedCategory_upperStar`,
   `AlgebraicGeometry.ProEtale.torAmplitudeIn_rightDerivedFunctor_lowerStar_of_isClosedImmersion`),
   so the three vertices of the closed-support triangle of an object of `Dᵇc_ctf` lie in
   `Dᵇc_ctf` (`AlgebraicGeometry.ProEtale.constructibleFiniteTor_closedSupportTriangle_obj`);
4'. on `Dᵇc_ctf` the direct image `i_*` has the right adjoint `Ri^!`
   (`AlgebraicGeometry.ProEtale.finiteTorClosedUpperShriekAdjunction`), whose unit is an
   isomorphism, and `Ri^! Rj_* = 0`.

## Method

The Tor amplitude of `Ri_* P` is detected after the pullbacks `i^*` and `j^*`
(`AlgebraicGeometry.ProEtale.torAmplitudeIn_of_mapDerivedCategory_upperStar`): the pullbacks are
exact, jointly conservative on sheaves, and commute with the derived tensor product
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso`); and `i^* Ri_* P ≅ P`,
`j^* Ri_* P = 0`. For `Ri^! K`, tensoring the closed-support triangle
`Ri_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` with a sheaf `M` gives a distinguished triangle whose long exact
homology sequence bounds the homology of `Ri_* Ri^! K ⊗ᴸ M`; then `Ri^! K ≅ i^* Ri_* Ri^! K`.
This replaces the blueprint's residue test (`lemma-bounds-finite-reductions--2`) by a test on all
sheaves `M`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- For a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁[1]` in `D(C)` with `T₂` concentrated in
`[a, b]` and `T₃` concentrated in `[a, e]`, where `b ≤ e + 1`, the first vertex `T₁` is
concentrated in `[a, e + 1]`: it sits in the distinguished triangle `T₃[-1] ⟶ T₁ ⟶ T₂ ⟶`. -/
lemma homologyConcentratedIn_obj₁_of_distTriang (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) {a b e : ℤ} (hbe : b ≤ e + 1)
    (h₂ : homologyConcentratedIn a b T.obj₂) (h₃ : homologyConcentratedIn a e T.obj₃) :
    homologyConcentratedIn a (e + 1) T.obj₁ := by
  have hT' := inv_rot_of_distTriang T hT
  obtain ⟨g₂, l₂⟩ := h₂
  obtain ⟨g₃, l₃⟩ := h₃
  have : TStructure.t.IsGE T.invRotate.obj₁ (a + 1) := TStructure.t.isGE_shift T.obj₃ a (-1) (a + 1)
  have : TStructure.t.IsLE T.invRotate.obj₁ (e + 1) := TStructure.t.isLE_shift T.obj₃ e (-1) (e + 1)
  have : TStructure.t.IsLE T.invRotate.obj₃ b := l₂
  have : TStructure.t.IsGE T.invRotate.obj₃ a := g₂
  exact ⟨TStructure.t.isGE₂ _ hT' a (TStructure.t.isGE_of_ge _ a (a + 1)) ‹_›,
    TStructure.t.isLE₂ _ hT' (e + 1) ‹_› (TStructure.t.isLE_of_le _ b (e + 1))⟩

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Generic

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {A} in
/-- A zero object of `D(X_proét)` has Tor amplitude in every interval. -/
lemma torAmplitudeIn_of_isZero {X : Scheme.{u}} {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) A)} (hK : IsZero K) :
    DerivedCategory.torAmplitudeIn A X a b K := fun M ↦
  have hZ := isZero_derivedTensor_obj_obj_of_isZero_left hK
    ((_root_.DerivedCategory.singleFunctor _ 0).obj M)
  ⟨_root_.DerivedCategory.TStructure.t.isGE_of_isZero hZ a,
    _root_.DerivedCategory.TStructure.t.isLE_of_isZero hZ b⟩

variable {A} in
/-- For a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶` in `D(X_proét)` with `T₂` of Tor amplitude in
`[a, b]` and `T₃` of Tor amplitude in `[a, e]`, where `b ≤ e + 1`, the first vertex `T₁` has Tor
amplitude in `[a, e + 1]`: tensoring with a sheaf is a triangulated functor. -/
lemma torAmplitudeIn_obj₁_of_distTriang {X : Scheme.{u}}
    (T : Triangle (_root_.DerivedCategory (Sheaf (ProEt.topology X) A)))
    (hT : T ∈ distTriang _) {a b e : ℤ} (hbe : b ≤ e + 1)
    (h₂ : DerivedCategory.torAmplitudeIn A X a b T.obj₂)
    (h₃ : DerivedCategory.torAmplitudeIn A X a e T.obj₃) :
    DerivedCategory.torAmplitudeIn A X a (e + 1) T.obj₁ := fun F ↦ by
  let G := (curriedTensor (_root_.DerivedCategory (Sheaf (ProEt.topology X) A))).flip.obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  let := _root_.DerivedCategory.commShiftTensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) A) 0).obj F)
  have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) A) 0).obj F)
  exact _root_.DerivedCategory.homologyConcentratedIn_obj₁_of_distTriang _
    (G.map_distinguished _ hT) hbe (h₂ F) (h₃ F)

variable [ProEtale.UpperStarPreservesFlat A]

/-- The pullback `D(g^*)` commutes with tensoring by a sheaf placed in degree `0`:
`D(g^*)(K ⊗ᴸ M) ≅ D(g^*) K ⊗ᴸ g^* M`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso`). -/
noncomputable def mapDerivedCategoryUpperStarTensorSingleIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology X) A)) (M : Sheaf (ProEt.topology X) A) :
    D((g)^*[A]).obj (K ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj M) ≅
      D((g)^*[A]).obj K ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj ((g)^*[A].obj M) :=
  ((leftDerivedUpperStarIsoMapDerivedCategory A g).app _).symm ≪≫
    leftDerivedUpperStarTensorIso A g _ _ ≪≫
    tensorIso ((leftDerivedUpperStarIsoMapDerivedCategory A g).app K)
      ((leftDerivedUpperStarIsoMapDerivedCategory A g).app _ ≪≫
        ((g)^*[A].mapDerivedCategorySingleFunctor 0).app M)

variable {A} in
/-- The pullback `D(g^*)` preserves Tor amplitude intervals, `g^*` being exact and preserving
flat sheaves (`DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj`). -/
theorem torAmplitudeIn_mapDerivedCategory_upperStar {X Y : Scheme.{u}} (g : Y ⟶ X) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) A)}
    (hK : DerivedCategory.torAmplitudeIn A X a b K) :
    DerivedCategory.torAmplitudeIn A Y a b (D((g)^*[A]).obj K) :=
  _root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj _ hK

end Generic

variable {Λ : Type (u + 1)} [CommRing Λ] {Z U X : Scheme.{u}}

section Module

/-- An object `E` of `D(X_proét)` whose pullbacks `D(i^*) E` and `D(j^*) E` have homology
concentrated in `[a, b]` has homology concentrated in `[a, b]`, for a closed immersion `i` whose
range is the complement of the range of the quasi-compact open immersion `j`: the pullbacks are
exact and jointly conservative on sheaves
(`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl`). -/
theorem homologyConcentratedIn_of_mapDerivedCategory_upperStar (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) {a b : ℤ}
    {E : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hi : _root_.DerivedCategory.homologyConcentratedIn a b
      (D((i)^*[ModuleCat.{u + 1} Λ]).obj E))
    (hj : _root_.DerivedCategory.homologyConcentratedIn a b
      (D((j)^*[ModuleCat.{u + 1} Λ]).obj E)) :
    _root_.DerivedCategory.homologyConcentratedIn a b E := by
  have key (q : ℤ)
      (hiq : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (D((i)^*[ModuleCat.{u + 1} Λ]).obj E)))
      (hjq : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (D((j)^*[ModuleCat.{u + 1} Λ]).obj E))) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj E) :=
    isZero_of_isZero_upperStar_of_isCompl i j hij _
      (hiq.of_iso (((i)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso q).app E))
      (hjq.of_iso (((j)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso q).app E))
  exact ⟨(_root_.DerivedCategory.isGE_iff E a).2 fun q hq ↦
      key q ((_root_.DerivedCategory.isGE_iff _ a).1 hi.1 q hq)
        ((_root_.DerivedCategory.isGE_iff _ a).1 hj.1 q hq),
    (_root_.DerivedCategory.isLE_iff E b).2 fun q hq ↦
      key q ((_root_.DerivedCategory.isLE_iff _ b).1 hi.2 q hq)
        ((_root_.DerivedCategory.isLE_iff _ b).1 hj.2 q hq)⟩

variable [IsNoetherianRing Λ]

/-- **Tor amplitude is detected on the closed and the open part.** Let `i` be a closed immersion
whose range is the complement of the range of the quasi-compact open immersion `j`. If
`D(i^*) K` and `D(j^*) K` have Tor amplitude in `[a, b]`, so has `K`: for a sheaf `M`, the
pullbacks of `K ⊗ᴸ M` are `D(i^*) K ⊗ᴸ i^* M` and `D(j^*) K ⊗ᴸ j^* M`
(`AlgebraicGeometry.ProEtale.mapDerivedCategoryUpperStarTensorSingleIso`), with homology in
`[a, b]`, so `K ⊗ᴸ M` has homology in `[a, b]`
(`AlgebraicGeometry.ProEtale.homologyConcentratedIn_of_mapDerivedCategory_upperStar`). -/
theorem torAmplitudeIn_of_mapDerivedCategory_upperStar (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hi : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b
      (D((i)^*[ModuleCat.{u + 1} Λ]).obj K))
    (hj : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b
      (D((j)^*[ModuleCat.{u + 1} Λ]).obj K)) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K := fun M ↦
  homologyConcentratedIn_of_mapDerivedCategory_upperStar i j hij
    ((_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (mapDerivedCategoryUpperStarTensorSingleIso _ i K M).symm (hi _))
    ((_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (mapDerivedCategoryUpperStarTensorSingleIso _ j K M).symm (hj _))

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3') at the finite stage `A_{E,n}`:
the direct image `Ri_*` along a closed immersion `i` (whose range is the complement of the range of
a quasi-compact open immersion `j`) preserves Tor amplitude intervals: `D(i^*) Ri_* P ≅ P` and
`D(j^*) Ri_* P = 0`, and Tor amplitude is detected after `i^*` and `j^*`
(`AlgebraicGeometry.ProEtale.torAmplitudeIn_of_mapDerivedCategory_upperStar`). No
constructibility is needed. -/
theorem torAmplitudeIn_rightDerivedFunctor_lowerStar_of_isClosedImmersion (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) {a b : ℤ}
    {P : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hP : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b P) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (R((i)_*[ModuleCat.{u + 1} Λ]).obj P) :=
  torAmplitudeIn_of_mapDerivedCategory_upperStar i j hij
    ((DerivedCategory.torAmplitudeIn _ Z a b).prop_of_iso
      (closedUpperShriekIsoMapDerivedCategoryUpperStar i j hij P) hP)
    (torAmplitudeIn_of_isZero
      (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedFunctor_lowerStar i j hij P))

end Module

section Finite

variable [Finite Λ] {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0) (hΛ : (N : Λ) = 0)
  (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

include hN hΛ s

omit [IsClosedImmersion i] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (1') at the finite stage `A_{E,n}`:
if `G ∈ Dᵇc_proét(U, Λ)` has Tor amplitude in `[a, b]` and `dim U ≤ d`, then `Rj_* G` has Tor
amplitude in `[a, b + 2d]`. This is the case of an open immersion of
`AlgebraicGeometry.ProEtale.torAmplitudeIn_rightDerivedLowerStar`; it is sharper than the
blueprint's interval `[a, b + 2d + c]`, `c ≥ 0` being the torsion cohomological dimension of
`k`. -/
theorem torAmplitudeIn_rightDerivedFunctor_lowerStar_of_isOpenImmersion (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞)) {a b : ℤ}
    {G : _root_.DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hG : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U G)
    (hGt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b G) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a (b + 2 * (d : ℤ))
      (R((j)_*[ModuleCat.{u + 1} Λ]).obj G) :=
  torAmplitudeIn_rightDerivedLowerStar Λ N hN (nsmul_id_eq_zero N hΛ) s j d hd a b hG hGt

omit [IsClosedImmersion i] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (1') at the finite stage `A_{E,n}`:
`Rj_*` carries `Dᵇc_ctf(U, Λ)` into `Dᵇc_ctf(X, Λ)`, for `dim U ≤ d`. -/
theorem constructibleFiniteTor_rightDerivedFunctor_lowerStar_of_isOpenImmersion (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞))
    {G : _root_.DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hG : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U G) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (R((j)_*[ModuleCat.{u + 1} Λ]).obj G) :=
  have ⟨hbc, a, _, hGt⟩ := hG
  ⟨boundedConstructible_rightDerivedFunctor_lowerStar_of_isOpenImmersion j N hN hΛ s hbc, a, _,
    torAmplitudeIn_rightDerivedFunctor_lowerStar_of_isOpenImmersion N hN hΛ s j d hd hbc hGt⟩

omit [QuasiCompact j] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3') at the finite stage `A_{E,n}`:
the direct image `Ri_*` along a closed immersion preserves bounded constructibility together with
the Tor amplitude interval `[a, b]`
(`AlgebraicGeometry.ProEtale.torAmplitudeIn_rightDerivedFunctor_lowerStar_of_isClosedImmersion`). -/
theorem boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_of_isClosedImmersion
    [QuasiCompact j] (hij : IsCompl (Set.range i.base) (Set.range j.base)) {a b : ℤ}
    {P : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hP : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z P)
    (hPt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b P) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        (R((i)_*[ModuleCat.{u + 1} Λ]).obj P) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        (R((i)_*[ModuleCat.{u + 1} Λ]).obj P) :=
  ⟨boundedConstructible_rightDerivedFunctor_lowerStar_of_isClosedImmersion i N hN hΛ s hP,
    torAmplitudeIn_rightDerivedFunctor_lowerStar_of_isClosedImmersion i j hij hPt⟩

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3') at the finite stage `A_{E,n}`:
`Ri_*` carries `Dᵇc_ctf(Z, Λ)` into `Dᵇc_ctf(X, Λ)`
(`boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_of_isClosedImmersion`). -/
theorem constructibleFiniteTor_rightDerivedFunctor_lowerStar_of_isClosedImmersion
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {P : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hP : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z P) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (R((i)_*[ModuleCat.{u + 1} Λ]).obj P) :=
  have ⟨hbc, a, b, hPt⟩ := hP
  have h := boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_of_isClosedImmersion
    N hN hΛ s i j hij hbc hPt
  ⟨h.1, a, b, h.2⟩

omit hN hΛ s [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3') at the finite stage `A_{E,n}`:
the pullback `Lg^*` along any morphism (in particular `i^*` and `j^*`) preserves bounded
constructibility together with the Tor amplitude interval `[a, b]`
(`AlgebraicGeometry.ProEtale.torAmplitudeIn_leftDerivedUpperStar`). -/
theorem boundedConstructible_and_torAmplitudeIn_leftDerivedFunctor_upperStar_obj
    {Y : Scheme.{u}} (g : Y ⟶ X) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
        (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  ⟨boundedConstructible_leftDerivedFunctor_upperStar_obj g hK,
    torAmplitudeIn_leftDerivedUpperStar _ g a b hKt⟩

omit hN hΛ s [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j] in
/-- The pullback `Lg^*` carries `Dᵇc_ctf(X, Λ)` into `Dᵇc_ctf(Y, Λ)`. -/
theorem constructibleFiniteTor_leftDerivedFunctor_upperStar_obj {Y : Scheme.{u}} (g : Y ⟶ X)
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  have ⟨hbc, a, b, hKt⟩ := hK
  have h := boundedConstructible_and_torAmplitudeIn_leftDerivedFunctor_upperStar_obj g hbc hKt
  ⟨h.1, a, b, h.2⟩

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2') at the finite stage `A_{E,n}`
(the first vertex of the closed-support triangle): if `K ∈ Dᵇc_proét(X, Λ)` has Tor amplitude in
`[a, b]` and `dim U ≤ d`, then `Ri_* Ri^! K` has Tor amplitude in `[a, b + 2d + 1]`. In the
closed-support triangle `Ri_* Ri^! K ⟶ K ⟶ Rj_* Lj^* K ⟶` the object `Rj_* Lj^* K` has Tor
amplitude in `[a, b + 2d]` (clauses (3') and (1')), and
`AlgebraicGeometry.ProEtale.torAmplitudeIn_obj₁_of_distTriang` applies. -/
theorem torAmplitudeIn_rightDerivedFunctor_lowerStar_obj_closedUpperShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞)) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a (b + 2 * (d : ℤ) + 1)
      (R((i)_*[ModuleCat.{u + 1} Λ]).obj
        ((closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K)) := by
  obtain ⟨w, hw⟩ := exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit i j hij K
  have h := boundedConstructible_and_torAmplitudeIn_leftDerivedFunctor_upperStar_obj j hK hKt
  exact torAmplitudeIn_obj₁_of_distTriang _ hw (by lia) hKt
    (torAmplitudeIn_rightDerivedFunctor_lowerStar_of_isOpenImmersion N hN hΛ s j d hd h.1 h.2)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2') at the finite stage `A_{E,n}`:
if `K ∈ Dᵇc_proét(X, Λ)` has Tor amplitude in `[a, b]` and `dim U ≤ d`, then `Ri^! K` (the right
adjoint of `Ri_*`, `AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`) has
Tor amplitude in `[a, b + 2d + 1]`: `Ri^! K ≅ D(i^*) Ri_* Ri^! K`, and `D(i^*)` preserves Tor
amplitude. This is sharper than the blueprint's interval `[a, b + 2d + c + 1]`, `c ≥ 0` being the
torsion cohomological dimension of `k`. -/
theorem torAmplitudeIn_closedUpperShriek_rightDerivedFunctor_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞)) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + 2 * (d : ℤ) + 1)
      ((closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K) :=
  (DerivedCategory.torAmplitudeIn _ Z _ _).prop_of_iso
    (closedUpperShriekIsoMapDerivedCategoryUpperStar i j hij _).symm
    (torAmplitudeIn_mapDerivedCategory_upperStar i
      (torAmplitudeIn_rightDerivedFunctor_lowerStar_obj_closedUpperShriek N hN hΛ s i j hij d hd
        hK hKt))

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2') at the finite stage `A_{E,n}`:
`Ri^!` carries `Dᵇc_ctf(X, Λ)` into `Dᵇc_ctf(Z, Λ)`, for `dim U ≤ d`. -/
theorem constructibleFiniteTor_closedUpperShriek_rightDerivedFunctor_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞))
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z
      ((closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K) :=
  have ⟨hbc, a, _, hKt⟩ := hK
  ⟨boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj i j N hN hΛ s hij hbc, a, _,
    torAmplitudeIn_closedUpperShriek_rightDerivedFunctor_obj N hN hΛ s i j hij d hd hbc hKt⟩

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3') at the finite stage `A_{E,n}`:
for `K ∈ Dᵇc_ctf(X, Λ)` and `dim U ≤ d`, all three vertices of the closed-support triangle
`Ri_* Ri^! K ⟶ K ⟶ Rj_* Lj^* K ⟶` (`AlgebraicGeometry.ProEtale.closedSupportTriangle`) lie in
`Dᵇc_ctf(X, Λ)`; if `K` has Tor amplitude in `[a, b]`, the outer vertices have Tor amplitude in
`[a, b + 2d + 1]` and `[a, b + 2d]`. -/
theorem constructibleFiniteTor_closedSupportTriangle_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞))
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) (w) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (closedSupportTriangle i j hij K w).obj₁ ∧
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (closedSupportTriangle i j hij K w).obj₂ ∧
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (closedSupportTriangle i j hij K w).obj₃ :=
  ⟨constructibleFiniteTor_rightDerivedFunctor_lowerStar_of_isClosedImmersion N hN hΛ s i j hij
      (constructibleFiniteTor_closedUpperShriek_rightDerivedFunctor_obj N hN hΛ s i j hij d hd hK),
    hK, constructibleFiniteTor_rightDerivedFunctor_lowerStar_of_isOpenImmersion N hN hΛ s j d hd
      (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj j hK)⟩

/-- The direct image `i_* : Dᵇc_ctf(Z, Λ) ⥤ Dᵇc_ctf(X, Λ)` along a closed immersion. -/
noncomputable def finiteTorRightDerivedLowerStar
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).FullSubcategory ⥤
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory :=
  (DerivedCategory.constructibleFiniteTor _ X).lift
    ((DerivedCategory.constructibleFiniteTor _ Z).ι ⋙ R((i)_*[ModuleCat.{u + 1} Λ]))
    (fun P ↦ constructibleFiniteTor_rightDerivedFunctor_lowerStar_of_isClosedImmersion N hN hΛ s
      i j hij P.2)

/-- The exceptional inverse image `Ri^! : Dᵇc_ctf(X, Λ) ⥤ Dᵇc_ctf(Z, Λ)` along a closed
immersion, for `dim U ≤ d`: the restriction of the right adjoint of `Ri_*` on the ambient
categories
(`AlgebraicGeometry.ProEtale.constructibleFiniteTor_closedUpperShriek_rightDerivedFunctor_obj`). -/
noncomputable def finiteTorClosedUpperShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞)) :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory ⥤
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).FullSubcategory :=
  (DerivedCategory.constructibleFiniteTor _ Z).lift
    ((DerivedCategory.constructibleFiniteTor _ X).ι ⋙
      (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor)
    (fun K ↦ constructibleFiniteTor_closedUpperShriek_rightDerivedFunctor_obj N hN hΛ s i j hij d
      hd K.2)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (4') at the finite stage `A_{E,n}`:
the direct image `i_* : Dᵇc_ctf(Z, Λ) ⥤ Dᵇc_ctf(X, Λ)` has the right adjoint `Ri^!`, the
restriction of the ambient adjunction
`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`. -/
noncomputable def finiteTorClosedUpperShriekAdjunction
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞)) :
    finiteTorRightDerivedLowerStar N hN hΛ s i j hij ⊣
      finiteTorClosedUpperShriek N hN hΛ s i j hij d hd :=
  (derivedLowerStarClosedUpperShriekAdjunction i j hij).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _)
    (Iso.refl _)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (4') at the finite stage `A_{E,n}`:
the unit `Q ⟶ Ri^! i_* Q` of the adjunction on `Dᵇc_ctf`
(`AlgebraicGeometry.ProEtale.finiteTorClosedUpperShriekAdjunction`) is an isomorphism, `Ri_*`
being fully faithful (`CategoryTheory.ObjectProperty.isIso_unit_app_of_lift`). -/
theorem isIso_finiteTorClosedUpperShriekAdjunction_unit_app
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞))
    (Q : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).FullSubcategory) :
    IsIso ((finiteTorClosedUpperShriekAdjunction N hN hΛ s i j hij d hd).unit.app Q) :=
  ObjectProperty.isIso_unit_app_of_lift _ _ Q

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (4') at the finite stage `A_{E,n}`:
`Ri^! Rj_* G = 0` in `Dᵇc_ctf(Z, Λ)` for `G ∈ Dᵇc_ctf(U, Λ)`; this holds for every
`G ∈ D(U_proét, Λ)`
(`ProEtale.isZero_closedUpperShriek_rightDerivedFunctor_obj_rightDerivedFunctor_lowerStar`). -/
theorem isZero_finiteTorClosedUpperShriek_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞))
    {G : _root_.DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hG : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U G) :
    IsZero ((finiteTorClosedUpperShriek N hN hΛ s i j hij d hd).obj
      ⟨_, constructibleFiniteTor_rightDerivedFunctor_lowerStar_of_isOpenImmersion N hN hΛ s j d hd
        hG⟩) :=
  IsZero.of_full_of_faithful_of_isZero (DerivedCategory.constructibleFiniteTor _ Z).ι _
    (isZero_closedUpperShriek_rightDerivedFunctor_obj_rightDerivedFunctor_lowerStar i j hij G)

end Finite

end ProEtale

end AlgebraicGeometry
