/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.TraceFormula.Specialization.PointsSupport

/-!

# Complexes supported at finitely many closed points

Let `V` be a separated scheme of finite type over a separably closed field `k` and `S` a finite
set of closed points of `V`. A bounded constructible `ℚ̄_ℓ`-complex `C` on `V` whose restriction to
`V ∖ S` vanishes, and whose global sections `RΓ(V, C)` vanish, is zero
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`, blueprint
`lemma-finite-support-global-sections--1`).

The closed points need not be rational: `k` need not be perfect. This generalises
`WeilConjectures.TraceFormula.Specialization.PointsSupport` (rational points). The residue field
`κ(z)` of a closed point is finite, hence purely inseparable, over `k`, so it is separably closed
(`ProEtale.CondensedRing.isSepClosed_of_locallyOfFiniteType`). Every bounded constructible complex
on `Spec κ(z)` is then a finite direct sum of shifts of the unit, and `RΓ(Spec κ(z), -)` detects
vanishing (`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_toPoint_of_isSepClosed`): a summand
`𝟙⟦d⟧ = La^* 𝟙⟦d⟧ ⟶ E` is adjoint to a morphism into `Ra_* E = 0`. The open–closed triangle at a
closed point then splits as for rational points, and one concludes by induction on `S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Residue fields of closed points -/

section ResidueField

variable {k : Type u} [Field k] (K : Type u) [Field K]

/-- A field of finite type over a separably closed field `k` (through a morphism
`Spec K ⟶ Spec k` locally of finite type) is separably closed: it is finite, hence purely
inseparable, over `k`. -/
lemma isSepClosed_of_locallyOfFiniteType [IsSepClosed k] (g : Spec (.of K) ⟶ Spec (.of k))
    [LocallyOfFiniteType g] : IsSepClosed K := by
  let f : CommRingCat.of k ⟶ CommRingCat.of K := Spec.preimage g
  have hf : f.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map f) := by
      rw [Spec.map_preimage]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  let := f.hom.toAlgebra
  have : Algebra.FiniteType k K := hf
  have := finite_of_finite_type_of_isJacobsonRing k K
  exact Algebra.IsAlgebraic.isSepClosed (F := k) (E := K)

/-- A field receiving a morphism from `k` has the characteristic of `k`. -/
lemma ringChar_eq_of_spec (g : Spec (.of K) ⟶ Spec (.of k)) : ringChar K = ringChar k := by
  let := (Spec.preimage g).hom.toAlgebra
  exact (Algebra.ringChar_eq k K).symm

end ResidueField

/-! ### Closed points as schemes over `k` -/

section ClosedPoint

variable {k : Type u} [Field k] {V : Over (Spec (.of k))}

/-- The closed point `Spec κ(z)` of `V`, as a scheme over `k`. -/
noncomputable abbrev closedPointOver (z : V.left) : Over (Spec (.of k)) :=
  Over.mk (V.left.fromSpecResidueField z ≫ V.hom)

/-- The inclusion `Spec κ(z) ⟶ V` of a point. -/
noncomputable abbrev closedPointι (z : V.left) : closedPointOver z ⟶ V :=
  Over.homMk (V.left.fromSpecResidueField z)

lemma range_closedPointι (z : V.left) : Set.range (closedPointι z).left.base = {z} :=
  Scheme.range_fromSpecResidueField z

lemma isClosedImmersion_closedPointι {z : V.left} (hz : IsClosed {z}) :
    IsClosedImmersion (closedPointι z).left :=
  isClosed_singleton_iff_isClosedImmersion.1 hz

lemma locallyOfFiniteType_closedPointOver [LocallyOfFiniteType V.hom] {z : V.left}
    (hz : IsClosed {z}) : LocallyOfFiniteType (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (LocallyOfFiniteType (V.left.fromSpecResidueField z ≫ V.hom))

lemma quasiCompact_closedPointOver [QuasiCompact V.hom] {z : V.left}
    (hz : IsClosed {z}) : QuasiCompact (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (QuasiCompact (V.left.fromSpecResidueField z ≫ V.hom))

lemma isSeparated_closedPointOver [IsSeparated V.hom] {z : V.left}
    (hz : IsClosed {z}) : IsSeparated (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (IsSeparated (V.left.fromSpecResidueField z ≫ V.hom))

end ClosedPoint

/-! ### Global sections on a separably closed point -/

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Global sections detect vanishing on a separably closed point**: let `P` be a `k`-scheme
of finite type whose underlying scheme is `Spec K` for a separably closed field `K`. A bounded
constructible complex `E` on `P` with `RΓ(P, E) = 0` vanishes. Indeed `E` is a finite direct sum of
shifts `𝟙⟦d⟧` of the unit, and every morphism `𝟙⟦d⟧ = La^* 𝟙⟦d⟧ ⟶ E` is adjoint to a morphism
`𝟙⟦d⟧ ⟶ Ra_* E = 0`. -/
theorem isZero_of_isZero_lowerStar_toPoint_of_isSepClosed {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (K : Type u) [Field K] [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
    (hP : P.left = Spec (.of K)) (E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hE : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint P)).obj E)) : IsZero E := by
  obtain ⟨P, f, rfl⟩ : ∃ (P' : Scheme.{u}) (f : P' ⟶ Spec (.of k)), P = Over.mk f :=
    ⟨P.left, P.hom, rfl⟩
  dsimp only [Over.mk_left] at hP
  subst hP
  let Dc := (nonempty_shiftDecomposition_point ℓ K E).some
  set adj := boundedConstructibleUpperStarLowerStarAdjunction ℓ
    (toPoint (Over.mk f))
  have hincl : ∀ j, Dc.incl j = 0 := fun j ↦ by
    let e : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint (Over.mk f))).obj ((shiftFunctor _ (Dc.deg j)).obj (𝟙_ _)) ≅
        (shiftFunctor _ (Dc.deg j)).obj (𝟙_ _) :=
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint (Over.mk f))).commShiftIso (Dc.deg j)).app _ ≪≫
        (shiftFunctor _ (Dc.deg j)).mapIso (Functor.Monoidal.εIso _).symm
    have h0 : adj.homEquiv _ _ (e.hom ≫ Dc.incl j) = 0 := hE.eq_of_tgt _ _
    have h1 : e.hom ≫ Dc.incl j = 0 := by
      rw [← (adj.homEquiv _ _).symm_apply_apply (e.hom ≫ Dc.incl j), h0,
        Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
    simpa using h1
  refine (IsZero.iff_id_eq_zero E).2 ?_
  rw [← Dc.total]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [hincl j, comp_zero]

end Point

/-! ### Open–closed vanishing at a closed point -/

section Vanishing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Open–closed detection of vanishing**: if `x : P ⟶ V` is a closed immersion and
`g : Y ⟶ V` a quasi-compact morphism with complementary range, then a complex `E` with
`Lx^* E = 0` and `Lg^* E = 0` vanishes. -/
theorem isZero_of_isCompl_range_of_isClosedImmersion {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    {P : Over (Spec (.of k))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [IsSeparated P.hom] (x : P ⟶ V) [IsClosedImmersion x.left]
    {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (g : Y ⟶ V) [QuasiCompact g.left]
    (hcompl : IsCompl (Set.range x.left.base) (Set.range g.left.base))
    (E : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hxE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj E))
    (hgE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj E)) :
    IsZero E := by
  have hiso := isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl _ ℓ x g hcompl
    (0 : E ⟶ E) ⟨⟨hgE.to_ _, hgE.eq_of_src _ _, hgE.eq_of_src _ _⟩⟩
    ⟨⟨hxE.to_ _, hxE.eq_of_src _ _, hxE.eq_of_src _ _⟩⟩
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← IsIso.hom_inv_id (0 : E ⟶ E), zero_comp]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- The factorization through an open `W` of a closed immersion with range in `W` is a closed
immersion. -/
lemma isClosedImmersion_opensOverLift (W : X.left.Opens) {P : Over (Spec (.of k))}
    (x : P ⟶ X) [IsClosedImmersion x.left] (hx : Set.range x.left.base ⊆ W) :
    IsClosedImmersion (opensOverLift W x hx).left := by
  have h : (opensOverLift W x hx).left ≫ W.ι = x.left :=
    congrArg CommaMorphism.left (opensOverLift_ι W x hx)
  have : IsPreimmersion ((opensOverLift W x hx).left ≫ W.ι) := by
    rw [h]
    infer_instance
  have : IsPreimmersion (opensOverLift W x hx).left := IsPreimmersion.of_comp _ W.ι
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  have hr : Set.range (opensOverLift W x hx).left.base =
      W.ι.base ⁻¹' Set.range x.left.base := by
    rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (W.ι.isOpenEmbedding.injective.preimage_image _).symm
  rw [hr]
  exact x.left.isClosedEmbedding.isClosed_range.preimage W.ι.base.hom.continuous

/-- **Open–closed detection of vanishing on an open neighbourhood of a closed point**: let
`x : P ⟶ X` be a closed immersion with range in the open `W'` and `g : Y ⟶ X` a morphism whose
range is the complement of the range of `x` in `W'`. If `Lx^* E = 0` and `Lg^* E = 0`, then `E`
vanishes on `W'`. -/
theorem isZero_upperStar_opensOverι_of_isCompl_of_isClosedImmersion (W' : X.left.Opens)
    {P : Over (Spec (.of k))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [IsSeparated P.hom] (x : P ⟶ X) [IsClosedImmersion x.left]
    (hx : Set.range x.left.base ⊆ W') {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Y ⟶ X) (hg : Set.range g.left.base ⊆ W')
    (hxg : Disjoint (Set.range x.left.base) (Set.range g.left.base))
    (hW' : (W' : Set X.left) ⊆ Set.range x.left.base ∪ Set.range g.left.base)
    (E : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hxE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj E))
    (hgE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj E)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W')).obj E) := by
  have := isClosedImmersion_opensOverLift W' x hx
  set xV := opensOverLift W' x hx
  obtain ⟨gV, rfl⟩ : ∃ gV : Y ⟶ opensOver W', gV ≫ opensOverι W' = g :=
    ⟨_, opensOverLift_ι W' g hg⟩
  have : QuasiCompact (gV.left ≫ (opensOver W').hom) := by
    rw [Over.w gV]
    infer_instance
  have : QuasiCompact gV.left := QuasiCompact.of_comp gV.left (opensOver W').hom
  have hxV : xV ≫ opensOverι W' = x := opensOverLift_ι W' x hx
  refine isZero_of_isCompl_range_of_isClosedImmersion ℓ xV gV ?_ _
    (isZero_upperStar_obj_upperStar_obj _ ℓ _ _ E (hxV ▸ hxE))
    (isZero_upperStar_obj_upperStar_obj _ ℓ _ _ E hgE)
  refine Set.isCompl_range_of_injective W'.ι.isOpenEmbedding.injective
    (range_comp_left_base xV (opensOverι W')) (range_comp_left_base gV (opensOverι W'))
    (by rwa [hxV]) ?_
  rw [Scheme.Opens.range_ι, hxV]
  exact hW'

/-- **Hom vanishing at a closed immersion**: if `D` vanishes on an open neighbourhood `V` of the
range of a proper `x = xV ≫ jV`, then every morphism `Rx_* E ⟶ D` vanishes. -/
lemma eq_zero_of_lowerStar_of_isProper {V P : Over (Spec (.of k))} [LocallyOfFiniteType V.hom]
    [QuasiCompact V.hom] [IsSeparated V.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [IsSeparated P.hom] (xV : P ⟶ V) (jV : V ⟶ X) [IsOpenImmersion jV.left] {x : P ⟶ X}
    [IsProper x.left] (hx : xV ≫ jV = x) (E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (D : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hD : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jV).obj D))
    (φ : (boundedConstructibleLowerStar ℓ x).obj E ⟶ D) :
    φ = 0 := by
  subst hx
  have hZ : IsZero ((boundedConstructibleUpperShriek ℓ
      (xV ≫ jV)).obj D) :=
    ((boundedConstructibleUpperShriek ℓ xV).map_isZero
      (hD.of_iso ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ jV).app D))).of_iso
      ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ xV jV).app D)
  set adj := boundedConstructibleUpperShriekAdjunction ℓ
    (xV ≫ jV)
  set e := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (xV ≫ jV)).app E
  have h : e.hom ≫ φ = 0 := by
    rw [← (adj.homEquiv _ _).symm_apply_apply (e.hom ≫ φ), hZ.eq_of_tgt (adj.homEquiv _ _ _) 0,
      Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  exact (cancel_epi e.hom).1 (h.trans comp_zero.symm)

/-- If `Rx_* Lx^* C` is a retract of `C` through the unit, `RΓ(X, C) = 0`, and global sections on
`P` detect vanishing, then `Lx^* C = 0`: `RΓ(P, Lx^* C) = RΓ(X, Rx_* Lx^* C)` is a retract of
`RΓ(X, C) = 0`. -/
lemma isZero_upperStar_of_retract_of_conservative {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] (x : P ⟶ X)
    (hcons : ∀ E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsZero ((boundedConstructibleLowerStar ℓ
        (toPoint P)).obj E) → IsZero E)
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hΓ : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint X)).obj C))
    (s : (boundedConstructibleLowerStar ℓ x).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C) ⟶ C)
    (hs : s ≫ (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      x).unit.app C = 𝟙 _) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C) := by
  have hP : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint X)).obj ((boundedConstructibleLowerStar ℓ x).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C))) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← CategoryTheory.Functor.map_id, ← hs, Functor.map_comp,
      hΓ.eq_of_tgt ((boundedConstructibleLowerStar ℓ (toPoint X)).map s) 0, zero_comp]
  have hxa : x ≫ toPoint X = toPoint P := by
    ext1
    simp
  exact hcons _ (hP.of_iso (eqToIso (by rw [hxa]) ≪≫
    ((boundedConstructibleLowerStarComp ℓ x (toPoint X)).app _).symm))

/-- **A complex vanishes along a closed immersion `x` if its global sections vanish**, provided
global sections on the source of `x` detect vanishing and the extension by zero `j_! Lj^* C` from
the complement `j` of `x` vanishes on an open neighbourhood `W'` of `x`: the open–closed triangle
`j_! Lj^* C ⟶ C ⟶ Rx_* Lx^* C ⟶` then splits. -/
theorem isZero_upperStar_of_isZero_lowerStar_of_isClosedImmersion {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] (x : P ⟶ X)
    [IsClosedImmersion x.left]
    (hcons : ∀ E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsZero ((boundedConstructibleLowerStar ℓ
        (toPoint P)).obj E) → IsZero E)
    (U : X.left.Opens) (hU : IsCompl (Set.range (opensOverι U).left.base) (Set.range x.left.base))
    (W' : X.left.Opens) (hx : Set.range x.left.base ⊆ W')
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hW : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W')).obj ((boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι U)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (opensOverι U)).obj C))))
    (hΓ : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint X)).obj C)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_openImmersionLowerShriek_openClosed (opensOverι U) x hU C
  obtain ⟨δ₀, hδ₀⟩ := WeilBoundedConstructible.exists_eq_map_comp_commShiftIso
    (ObjectProperty.fullyFaithfulι _) δ
  have hW₁ : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W')).obj ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (1 : ℤ)).obj
        ((boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι U)).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              (opensOverι U)).obj C)))) :=
    ((shiftFunctor _ (1 : ℤ)).map_isZero hW).of_iso
      (((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι W')).commShiftIso (1 : ℤ)).app _)
  have hδ₀' : δ₀ = 0 :=
    eq_zero_of_lowerStar_of_isProper ℓ (opensOverLift W' x hx) (opensOverι W')
      (opensOverLift_ι _ _ _) _ _ hW₁ δ₀
  have hδ : δ = 0 := by
    rw [hδ₀, hδ₀', Functor.map_zero, zero_comp]
  obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₃ _ hT (𝟙 _) (by
    rw [Triangle.mk_mor₃, hδ]
    exact comp_zero)
  exact isZero_upperStar_of_retract_of_conservative ℓ x hcons C hΓ
    ((ObjectProperty.fullyFaithfulι _).preimage s)
    ((boundedConstructible _).ι.map_injective (by
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_id]
      exact hs.symm))

/-- **The induction step**: let `x` be a closed immersion with complement `U`, and `W₀ ⊆ W'` opens
with `W' = x ∪ W₀`, `W₀` disjoint from `x`. If `C` vanishes on `W₀` and `RΓ(X, C) = 0`, and global
sections on the source of `x` detect vanishing, then `C` vanishes on `W'`. -/
theorem isZero_upperStar_opensOverι_of_isClosedImmersion {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] (x : P ⟶ X)
    [IsClosedImmersion x.left]
    (hcons : ∀ E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsZero ((boundedConstructibleLowerStar ℓ
        (toPoint P)).obj E) → IsZero E)
    (U W₀ W' : X.left.Opens)
    (hU : IsCompl (Set.range (opensOverι U).left.base) (Set.range x.left.base))
    (hx : Set.range x.left.base ⊆ W') (hW₀U : (W₀ : Set X.left) ⊆ U)
    (hW₀W' : (W₀ : Set X.left) ⊆ W') (hdisj : Disjoint (Set.range x.left.base) W₀)
    (hcov : (W' : Set X.left) ⊆ Set.range x.left.base ∪ W₀)
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hC : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W₀)).obj C))
    (hΓ : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint X)).obj C)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W')).obj C) := by
  have hW₀ : Set.range (opensOverι W₀).left.base ⊆ U := by
    rw [range_opensOverι]
    exact hW₀U
  have hrange : Set.range (opensOverLift U (opensOverι W₀) hW₀ ≫ opensOverι U).left.base =
      W₀ := by
    rw [opensOverLift_ι, range_opensOverι]
  have hε : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι U)).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι U)).counit.app C)) :=
    IsIso.of_isIso_fac_left (hh := IsIso.id _)
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        (opensOverι U)).right_triangle_components C)
  have hD := isZero_upperStar_opensOverι_of_isCompl_of_isClosedImmersion ℓ W' x hx
    (opensOverLift U (opensOverι W₀) hW₀ ≫ opensOverι U) (by rwa [hrange])
    (by rwa [hrange]) (by rwa [hrange]) _
    (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ
      (opensOverι U) x hU.disjoint _)
    ((isZero_upperStar_of_range_subset ℓ W₀ _ (by rw [hrange]) C hC).of_iso
      ((boundedConstructibleUpperStarComp _ ℓ _ _).app _ ≪≫
        (boundedConstructibleUpperStar _ ℓ _).mapIso (@asIso _ _ _ _ _ hε) ≪≫
        ((boundedConstructibleUpperStarComp _ ℓ _ _).app C).symm))
  exact isZero_upperStar_opensOverι_of_isCompl_of_isClosedImmersion ℓ W' x hx (opensOverι W₀)
    (by rwa [range_opensOverι]) (by rwa [range_opensOverι]) (by rwa [range_opensOverι]) C
    (isZero_upperStar_of_isZero_lowerStar_of_isClosedImmersion ℓ x hcons U hU W' hx C hD hΓ)
    hC

end Vanishing

/-! ### Finitely many closed points -/

section Points

/-- The open complement of a finite set of closed points of a scheme. -/
def finsetComplOpens {X : Scheme.{u}} (S : Finset X) (hS : ∀ x ∈ S, IsClosed {x}) : X.Opens :=
  ⟨(↑S)ᶜ, by
    rw [isOpen_compl_iff, ← Set.biUnion_of_singleton (↑S : Set X)]
    exact S.finite_toSet.isClosed_biUnion fun x hx ↦ hS x hx⟩

@[simp]
lemma coe_finsetComplOpens {X : Scheme.{u}} (S : Finset X) (hS : ∀ x ∈ S, IsClosed {x}) :
    (finsetComplOpens S hS : Set X) = (↑S)ᶜ :=
  rfl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Global sections on a closed point of `X` detect vanishing: its residue field is separably
closed. -/
lemma isZero_of_isZero_lowerStar_closedPoint {z : X.left} (hz : IsClosed {z}) :
    haveI := locallyOfFiniteType_closedPointOver hz
    haveI := quasiCompact_closedPointOver hz
    haveI := isSeparated_closedPointOver hz
    ∀ E : Dᵇc((closedPointOver z).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsZero ((boundedConstructibleLowerStar ℓ
        (toPoint (closedPointOver z))).obj E) → IsZero E := by
  have := locallyOfFiniteType_closedPointOver hz
  have := quasiCompact_closedPointOver hz
  have := isSeparated_closedPointOver hz
  have : IsSepClosed (X.left.residueField z) :=
    isSepClosed_of_locallyOfFiniteType (X.left.residueField z) (closedPointOver z).hom
  have hchar := ringChar_eq_of_spec (X.left.residueField z) (closedPointOver z).hom
  have : Fact (ringChar (X.left.residueField z)).Prime := ⟨by rw [hchar]; exact Fact.out⟩
  have : Fact (ringChar (X.left.residueField z) ≠ ℓ) := ⟨by rw [hchar]; exact Fact.out⟩
  exact fun E hE ↦ isZero_of_isZero_lowerStar_toPoint_of_isSepClosed ℓ
    (X.left.residueField z) rfl E hE

/-- **Global sections detect complexes supported at finitely many closed points**, on bounded
constructible complexes. -/
theorem isZero_of_isZero_upperStar_finsetComplOpens_of_isZero_lowerStar (S : Finset X.left)
    (hS : ∀ x ∈ S, IsClosed {x}) (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι (finsetComplOpens S hS))).obj C))
    (hΓ : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint X)).obj C)) : IsZero C := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact (isZero_upperStar_of_range_subset ℓ _ (𝟙 X)
      (fun y _ ↦ by simp) C hU).of_iso ((boundedConstructibleUpperStarId _ ℓ X).app C).symm
  | insert z S hzS ih =>
    have hz : IsClosed {z} := hS z (Finset.mem_insert_self _ _)
    have hS' : ∀ x ∈ S, IsClosed {x} := fun x hx ↦ hS x (Finset.mem_insert_of_mem hx)
    have hz' : ∀ x ∈ ({z} : Finset X.left), IsClosed {x} := by simpa using hz
    have := locallyOfFiniteType_closedPointOver hz
    have := quasiCompact_closedPointOver hz
    have := isSeparated_closedPointOver hz
    have := isClosedImmersion_closedPointι hz
    refine ih hS' (isZero_upperStar_opensOverι_of_isClosedImmersion ℓ (closedPointι z)
      (isZero_of_isZero_lowerStar_closedPoint ℓ hz) (finsetComplOpens {z} hz')
      (finsetComplOpens (insert z S) hS) (finsetComplOpens S hS') ?_ ?_ ?_ ?_ ?_ ?_ C hU hΓ)
    · rw [range_opensOverι, range_closedPointι, coe_finsetComplOpens, Finset.coe_singleton]
      exact isCompl_compl.symm
    · rw [range_closedPointι, Set.singleton_subset_iff, SetLike.mem_coe, ← SetLike.mem_coe,
        coe_finsetComplOpens, Set.mem_compl_iff, Finset.mem_coe]
      exact hzS
    · intro y hy
      simp only [coe_finsetComplOpens, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
        not_or, Finset.mem_singleton] at hy ⊢
      exact hy.1
    · intro y hy
      simp only [coe_finsetComplOpens, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
        not_or] at hy ⊢
      exact hy.2
    · rw [range_closedPointι, Set.disjoint_singleton_left, coe_finsetComplOpens]
      simp
    · intro y hy
      rw [range_closedPointι]
      by_cases h : y = z
      · exact Or.inl h
      · right
        simp only [coe_finsetComplOpens, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
          not_or] at hy ⊢
        exact ⟨h, hy⟩

/-- **Global sections detect complexes supported at finitely many closed points** (blueprint
`lemma-finite-support-global-sections--1`): let `X` be a separated scheme of finite type over a
separably closed field `k` and `S` a finite set of closed points of `X`. A bounded constructible
complex `C` on `X` whose restriction to `X ∖ S` vanishes and whose global sections `RΓ(X, C)`
vanish is zero. The points of `S` need not be rational. -/
theorem isZero_of_isZero_upperStar_finsetComplOpens (S : Finset X.left)
    (hS : ∀ x ∈ S, IsClosed {x})
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) C)
    (hU : IsZero (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (hΓ : IsZero (R((X.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) : IsZero C := by
  rw [← toPoint_left X] at hΓ
  have h := isZero_of_isZero_upperStar_finsetComplOpens_of_isZero_lowerStar ℓ S hS ⟨C, hC⟩
    (IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _ hU)
    (IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _ hΓ)
  exact (boundedConstructible _).ι.map_isZero h

end Points

end AlgebraicGeometry.ProEtale.CondensedRing
