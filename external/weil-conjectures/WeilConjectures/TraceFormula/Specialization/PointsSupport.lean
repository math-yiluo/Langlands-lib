/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointSupport
public import WeilConjectures.TraceFormula.Additivity

/-!

# Complexes supported at finitely many rational points

Let `X` be a separated `k`-scheme of finite type and `S` a finite set of rational points of `X`.
A bounded constructible `ℚ̄_ℓ`-complex `C` on `X` whose restriction to the open complement
`X ∖ S` (`ProEtale.CondensedRing.pointsCompl`) vanishes is detected by its global sections: if
`RΓ(X, C) = 0`, then `C = 0`
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_pointsComplι_of_isZero_lowerStar`, blueprint
`lemma-finite-support-global-sections--1`).

The proof is by induction on `S`. For `S = S' ∪ {x}`, the open–closed triangle
`j_! Lj^* C ⟶ C ⟶ Rx_* Lx^* C ⟶` of the complement `j` of `x` splits: its connecting morphism
vanishes since `j_! Lj^* C` vanishes on the open neighbourhood `X ∖ S'` of `x`
(`ProEtale.CondensedRing.eq_zero_of_lowerStar_rationalPoint`). Hence `RΓ(X, Rx_* Lx^* C) = Lx^* C`
is a retract of `RΓ(X, C) = 0`, so `C` vanishes at `x`, hence on `X ∖ S'`, and we conclude by
induction.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

/-- Two maps `a`, `b` into `β` whose images under an injective map `j` are disjoint and cover the
image of `j` have complementary ranges. -/
lemma Set.isCompl_range_of_injective {α β γ δ : Type*} {j : β → α} (hj : Function.Injective j)
    {a : γ → β} {b : δ → β} {A B : Set α} (ha : Set.range (j ∘ a) = A)
    (hb : Set.range (j ∘ b) = B) (hAB : Disjoint A B) (hj' : Set.range j ⊆ A ∪ B) :
    IsCompl (Set.range a) (Set.range b) := by
  have ka : Set.range a = j ⁻¹' Set.range (j ∘ a) := by
    rw [Set.range_comp, hj.preimage_image]
  have kb : Set.range b = j ⁻¹' Set.range (j ∘ b) := by
    rw [Set.range_comp, hj.preimage_image]
  rw [ka, kb, ha, hb]
  exact ⟨hAB.preimage j, codisjoint_iff_le_sup.2 fun y _ ↦ hj' ⟨y, rfl⟩⟩

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### Open subschemes as schemes over `s` -/

section Opens

/-- An open subscheme `W` of `X`, as a scheme over `s`. -/
noncomputable abbrev opensOver (W : X.left.Opens) : Over (Spec (.of k)) :=
  Over.mk (W.ι ≫ X.hom)

/-- The open immersion `W ⟶ X` of an open subscheme. -/
noncomputable abbrev opensOverι (W : X.left.Opens) : opensOver W ⟶ X :=
  Over.homMk W.ι

instance (W : X.left.Opens) : IsOpenImmersion (opensOverι W).left :=
  inferInstanceAs (IsOpenImmersion W.ι)

instance (W : X.left.Opens) : LocallyOfFiniteType (opensOver W).hom :=
  inferInstanceAs (LocallyOfFiniteType (W.ι ≫ X.hom))

instance (W : X.left.Opens) : IsSeparated (opensOver W).hom :=
  inferInstanceAs (IsSeparated (W.ι ≫ X.hom))

instance (W : X.left.Opens) : QuasiCompact (opensOverι W).left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  exact inferInstanceAs (QuasiCompact W.ι)

instance (W : X.left.Opens) : QuasiCompact (opensOver W).hom :=
  inferInstanceAs (QuasiCompact ((opensOverι W).left ≫ X.hom))

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma range_opensOverι (W : X.left.Opens) :
    Set.range (opensOverι W).left.base = W :=
  Scheme.Opens.range_ι _

/-- A morphism to `X` with range in the open `W` factors through `W`. -/
noncomputable def opensOverLift (W : X.left.Opens) {Y : Over (Spec (.of k))} (g : Y ⟶ X)
    (h : Set.range g.left.base ⊆ W) : Y ⟶ opensOver W :=
  Over.homMk (IsOpenImmersion.lift W.ι g.left (h.trans_eq (Scheme.Opens.range_ι W).symm))
    (by simp)

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
@[reassoc (attr := simp)]
lemma opensOverLift_ι (W : X.left.Opens) {Y : Over (Spec (.of k))} (g : Y ⟶ X)
    (h : Set.range g.left.base ⊆ W) : opensOverLift W g h ≫ opensOverι W = g := by
  ext1
  exact IsOpenImmersion.lift_fac _ _ _

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma range_comp_left_base {Y Z : Over (Spec (.of k))} (f : Y ⟶ Z) (g : Z ⟶ X) :
    Set.range (g.left.base ∘ f.left.base) = Set.range (f ≫ g).left.base :=
  rfl

end Opens

/-! ### The open complement of finitely many rational points -/

section PointsCompl

/-- The open complement `X ∖ S` of a finite set `S` of rational points, an open subset of `X`. -/
noncomputable def pointsComplOpens (S : Finset (RationalPoint X)) : X.left.Opens :=
  ⟨(⋃ x ∈ S, Set.range x.left.base)ᶜ,
    (isClosed_biUnion_finset fun x _ ↦ x.left.isClosedEmbedding.isClosed_range).isOpen_compl⟩

/-- The open complement `X ∖ S` of a finite set `S` of rational points, as a scheme over `s`. -/
noncomputable abbrev pointsCompl (S : Finset (RationalPoint X)) : Over (Spec (.of k)) :=
  opensOver (pointsComplOpens S)

/-- The open immersion `X ∖ S ⟶ X` of the complement of a finite set of rational points. -/
noncomputable abbrev pointsComplι (S : Finset (RationalPoint X)) : pointsCompl S ⟶ X :=
  opensOverι (pointsComplOpens S)

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma mem_pointsComplOpens {S : Finset (RationalPoint X)} {y : X.left} :
    y ∈ pointsComplOpens S ↔ ∀ z ∈ S, y ∉ Set.range z.left.base := by
  simp [pointsComplOpens]

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- If the rational point `x` lies outside `X ∖ S`, then `X ∖ S = X ∖ (S ∪ {x})`. -/
lemma pointsComplOpens_subset_insert [DecidableEq (RationalPoint X)] (x : RationalPoint X)
    (S : Finset (RationalPoint X)) (hx : ¬ Set.range x.left.base ⊆ pointsComplOpens S) :
    (pointsComplOpens S : Set X.left) ⊆ pointsComplOpens (insert x S) := by
  intro y hy
  refine mem_pointsComplOpens.2 fun z hz ↦ ?_
  rcases Finset.mem_insert.1 hz with rfl | hz
  · rintro ⟨p, rfl⟩
    refine hx ?_
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim (α := Spec (.of k)) q p]
  · exact mem_pointsComplOpens.1 hy z hz

end PointsCompl

/-! ### Vanishing on opens -/

section Vanishing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- If `C` vanishes on the open `W`, then `Lg^* C = 0` for every `g` with range in `W`. -/
lemma isZero_upperStar_of_range_subset (W : X.left.Opens) {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (g : Y ⟶ X)
    (h : Set.range g.left.base ⊆ W) (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hW : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι
        W)).obj C)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj C) :=
  ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverLift W g
      h)).map_isZero hW).of_iso
    (eqToIso (by rw [opensOverLift_ι]) ≪≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverLift W g h)
          (opensOverι W)).app C)

/-- **Open–closed detection of vanishing at a rational point**: if `x` is a rational point of
`V` and `g : Y ⟶ V` a quasi-compact morphism with range the complement of `x`, then a complex `E`
with `Lx^* E = 0` and `Lg^* E = 0` vanishes. -/
theorem isZero_of_isCompl_range_rationalPoint {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] (x : RationalPoint V)
    {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (g : Y ⟶ V) [QuasiCompact g.left]
    (hcompl : IsCompl (Set.range x.left.base) (Set.range g.left.base)) (E : Dᵇc(V.left)⟦Λ⟧)
    (hxE : IsZero ((boundedConstructibleUpperStar Λ ℓ x).obj E))
    (hgE : IsZero ((boundedConstructibleUpperStar Λ ℓ g).obj E)) : IsZero E := by
  have hiso := isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl Λ ℓ x g hcompl
    (0 : E ⟶ E) ⟨⟨hgE.to_ _, hgE.eq_of_src _ _, hgE.eq_of_src _ _⟩⟩
    ⟨⟨hxE.to_ _, hxE.eq_of_src _ _, hxE.eq_of_src _ _⟩⟩
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← IsIso.hom_inv_id (0 : E ⟶ E), zero_comp]

/-- `L(f ≫ g)^* E = 0` implies `Lf^* Lg^* E = 0`. -/
lemma isZero_upperStar_obj_upperStar_obj {Y Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : Y ⟶ Z) (g : Z ⟶ X) (E : Dᵇc(X.left)⟦Λ⟧)
    (h : IsZero ((boundedConstructibleUpperStar Λ ℓ (f ≫ g)).obj E)) :
    IsZero ((boundedConstructibleUpperStar Λ ℓ f).obj
      ((boundedConstructibleUpperStar Λ ℓ g).obj E)) :=
  h.of_iso ((boundedConstructibleUpperStarComp Λ ℓ f g).app E).symm

/-- **Open–closed detection of vanishing on an open neighbourhood of a rational point**: let `x`
be a rational point in the open `W'` and `g : Y ⟶ X` a morphism whose range is the complement of
`x` in `W'`. If `Lx^* E = 0` and `Lg^* E = 0`, then `E` vanishes on `W'`. -/
theorem isZero_upperStar_opensOverι_of_isCompl (W' : X.left.Opens) (x : RationalPoint X)
    (hx : Set.range x.left.base ⊆ W') {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Y ⟶ X) (hg : Set.range g.left.base ⊆ W')
    (hxg : Disjoint (Set.range x.left.base) (Set.range g.left.base))
    (hW' : (W' : Set X.left) ⊆ Set.range x.left.base ∪ Set.range g.left.base)
    (E : Dᵇc(X.left)⟦Λ⟧) (hxE : IsZero ((boundedConstructibleUpperStar Λ ℓ x).obj E))
    (hgE : IsZero ((boundedConstructibleUpperStar Λ ℓ g).obj E)) :
    IsZero ((boundedConstructibleUpperStar Λ ℓ (opensOverι W')).obj E) := by
  obtain ⟨xV, rfl⟩ : ∃ xV : RationalPoint (opensOver W'), xV ≫ opensOverι W' = x :=
    ⟨_, opensOverLift_ι W' x hx⟩
  obtain ⟨gV, rfl⟩ : ∃ gV : Y ⟶ opensOver W', gV ≫ opensOverι W' = g :=
    ⟨_, opensOverLift_ι W' g hg⟩
  have : QuasiCompact (gV.left ≫ (opensOver W').hom) := by
    rw [Over.w gV]
    infer_instance
  have : QuasiCompact gV.left := QuasiCompact.of_comp gV.left (opensOver W').hom
  refine isZero_of_isCompl_range_rationalPoint Λ ℓ xV gV ?_ _
    (isZero_upperStar_obj_upperStar_obj Λ ℓ _ _ E hxE)
    (isZero_upperStar_obj_upperStar_obj Λ ℓ _ _ E hgE)
  refine Set.isCompl_range_of_injective W'.ι.isOpenEmbedding.injective
    (range_comp_left_base xV (opensOverι W')) (range_comp_left_base gV (opensOverι W')) hxg ?_
  rw [Scheme.Opens.range_ι]
  exact hW'

end Vanishing

/-! ### The splitting at a rational point -/

section Splitting

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- **Hom vanishing at a rational point**: if `D` vanishes on an open neighbourhood `V` of a
rational point `x`, then every morphism `Rx_* E ⟶ D` vanishes. Indeed `Rx_* ≅ Rx_!` since `x` is
proper, and `Rx^! D ≅ Rx_V^! Rj_V^! D ≅ Rx_V^! Lj_V^* D = 0`. -/
lemma eq_zero_of_lowerStar_rationalPoint {V : Over (Spec (.of k))} [LocallyOfFiniteType V.hom]
    [QuasiCompact V.hom] [IsSeparated V.hom] (xV : RationalPoint V) (jV : V ⟶ X)
    [IsOpenImmersion jV.left] {x : RationalPoint X} (hx : xV ≫ jV = x)
    (E : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
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

/-- If `Rx_* Lx^* C` is a retract of `C` through the unit, and `RΓ(X, C) = 0`, then
`Lx^* C = 0`: indeed `RΓ(X, Rx_* Lx^* C) = Lx^* C` is then a retract of `RΓ(X, C) = 0`. -/
lemma isZero_upperStar_of_retract (x : RationalPoint X)
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
  have hxa : x ≫ toPoint X = 𝟙 (point k) := by
    ext1
    simp
  exact isZero_of_isZero_boundedConstructibleLowerStar_id ℓ (hP.of_iso
    (eqToIso (by rw [hxa]) ≪≫
      ((boundedConstructibleLowerStarComp ℓ x (toPoint X)).app _).symm))

variable {ℓ}

/-- **A complex vanishes at a rational point `x` if its global sections vanish**, provided its
extension by zero `j_! Lj^* C` from the complement `j` of `x` vanishes on an open neighbourhood
`W'` of `x`: the open–closed triangle `j_! Lj^* C ⟶ C ⟶ Rx_* Lx^* C ⟶` then splits, so
`RΓ(X, Rx_* Lx^* C) = Lx^* C` is a retract of `RΓ(X, C) = 0`. -/
theorem isZero_upperStar_rationalPoint_of_isZero_lowerStar (x : RationalPoint X)
    (W' : X.left.Opens) (hx : Set.range x.left.base ⊆ W')
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hW : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W')).obj ((boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι (pointComplOpens x))).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (opensOverι (pointComplOpens x))).obj C))))
    (hΓ : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint X)).obj C)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_openImmersionLowerShriek_openClosed
    (opensOverι (pointComplOpens x)) x (isCompl_range_pointComplι x) C
  obtain ⟨δ₀, hδ₀⟩ := WeilBoundedConstructible.exists_eq_map_comp_commShiftIso
    (ObjectProperty.fullyFaithfulι _) δ
  have hW₁ : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W')).obj ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (1 : ℤ)).obj
        ((boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι (pointComplOpens x))).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              (opensOverι (pointComplOpens x))).obj C)))) :=
    ((shiftFunctor _ (1 : ℤ)).map_isZero hW).of_iso
      (((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι W')).commShiftIso (1 : ℤ)).app _)
  have hδ₀' : δ₀ = 0 :=
    eq_zero_of_lowerStar_rationalPoint ℓ (opensOverLift W' x hx) (opensOverι W')
      (opensOverLift_ι _ _ _) _ _ hW₁ δ₀
  have hδ : δ = 0 := by
    rw [hδ₀, hδ₀', Functor.map_zero, zero_comp]
  obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₃ _ hT (𝟙 _) (by
    rw [Triangle.mk_mor₃, hδ]
    exact comp_zero)
  exact isZero_upperStar_of_retract ℓ x C hΓ ((ObjectProperty.fullyFaithfulι _).preimage s)
    ((boundedConstructible _).ι.map_injective (by
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_id]
      exact hs.symm))

end Splitting

/-! ### Finitely many rational points -/

section Points

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- **The induction step**: if `C` vanishes on `X ∖ (S ∪ {x})` for a rational point `x` in
`X ∖ S`, and `RΓ(X, C) = 0`, then `C` vanishes on `X ∖ S`. -/
theorem isZero_upperStar_pointsComplι_of_insert [DecidableEq (RationalPoint X)]
    (x : RationalPoint X) (S : Finset (RationalPoint X))
    (hx : Set.range x.left.base ⊆ pointsComplOpens S)
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointsComplι (insert x S))).obj C))
    (hΓ : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint X)).obj C)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointsComplι S)).obj C) := by
  have hWx : Set.range (pointsComplι (insert x S)).left.base ⊆ pointComplOpens x := by
    rw [range_opensOverι]
    exact fun y hy ↦ mem_pointsComplOpens.1 hy x (Finset.mem_insert_self _ _)
  have hWS : Set.range (pointsComplι (insert x S)).left.base ⊆ pointsComplOpens S := by
    rw [range_opensOverι]
    exact fun y hy ↦ mem_pointsComplOpens.2 fun z hz ↦
      mem_pointsComplOpens.1 hy z (Finset.mem_insert_of_mem hz)
  have hdisj : Disjoint (Set.range x.left.base)
      (Set.range (pointsComplι (insert x S)).left.base) := by
    rw [range_opensOverι]
    exact Set.disjoint_left.2 fun y hy hy' ↦
      mem_pointsComplOpens.1 hy' x (Finset.mem_insert_self _ _) hy
  have hcov : (pointsComplOpens S : Set X.left) ⊆
      Set.range x.left.base ∪ Set.range (pointsComplι (insert x S)).left.base := by
    rw [range_opensOverι]
    intro y hy
    by_cases h : y ∈ Set.range x.left.base
    · exact Or.inl h
    · refine Or.inr (mem_pointsComplOpens.2 fun z hz ↦ ?_)
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact h
      · exact mem_pointsComplOpens.1 hy z hz
  have hε : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι (pointComplOpens x))).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι (pointComplOpens x))).counit.app C)) :=
    IsIso.of_isIso_fac_left (hh := IsIso.id _)
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        (opensOverι (pointComplOpens x))).right_triangle_components C)
  have hD := isZero_upperStar_opensOverι_of_isCompl _ ℓ (pointsComplOpens S) x hx
    (opensOverLift (pointComplOpens x) (pointsComplι (insert x S)) hWx ≫
      opensOverι (pointComplOpens x)) (by rwa [opensOverLift_ι]) (by rwa [opensOverLift_ι])
    (by rwa [opensOverLift_ι]) _
    (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ
      (opensOverι (pointComplOpens x)) x (isCompl_range_pointComplι x).disjoint _)
    ((isZero_upperStar_of_range_subset ℓ (pointsComplOpens (insert x S)) _
      (by rw [opensOverLift_ι, range_opensOverι]) C hU).of_iso
      ((boundedConstructibleUpperStarComp _ ℓ _ _).app _ ≪≫
        (boundedConstructibleUpperStar _ ℓ _).mapIso (@asIso _ _ _ _ _ hε) ≪≫
        ((boundedConstructibleUpperStarComp _ ℓ _ _).app C).symm))
  exact isZero_upperStar_opensOverι_of_isCompl _ ℓ _ x hx (pointsComplι (insert x S)) hWS hdisj
    hcov C (isZero_upperStar_rationalPoint_of_isZero_lowerStar x _ hx C hD hΓ) hU

variable (ℓ) in
/-- **Global sections detect complexes supported at finitely many rational points** (blueprint
`lemma-finite-support-global-sections--1`, the finite-support step of Gabber's Künneth formula for
nearby cycles, Illusie, *Around the Thom–Sebastiani theorem*, 4.7): let `S` be a finite set of
rational points of a separated `k`-scheme of finite type `X`. If the restriction of
`C ∈ Dᵇc(X, ℚ̄_ℓ)` to the open complement `X ∖ S` vanishes, and `RΓ(X, C) = 0`, then `C = 0`.

This is the case of rational points; when `k` is algebraically closed, every closed point is
rational. The proof is by induction on `S`: the open–closed triangle at a point `x ∈ S` splits
(`isZero_upperStar_rationalPoint_of_isZero_lowerStar`), so `C` vanishes at `x`, hence on the
complement of `S ∖ {x}` (`isZero_upperStar_pointsComplι_of_insert`). -/
theorem isZero_of_isZero_upperStar_pointsComplι_of_isZero_lowerStar
    (S : Finset (RationalPoint X)) (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointsComplι S)).obj C))
    (hΓ : IsZero ((boundedConstructibleLowerStar ℓ
      (toPoint X)).obj C)) : IsZero C := by
  classical
  induction S using Finset.induction_on generalizing C with
  | empty =>
    exact (isZero_upperStar_of_range_subset ℓ _ (𝟙 X)
      (fun y _ ↦ mem_pointsComplOpens.2 fun z hz ↦ absurd hz (Finset.notMem_empty z)) C
        hU).of_iso ((boundedConstructibleUpperStarId _ ℓ X).app C).symm
  | insert x S _ ih =>
    by_cases hx : Set.range x.left.base ⊆ pointsComplOpens S
    · exact ih C (isZero_upperStar_pointsComplι_of_insert x S hx C hU hΓ) hΓ
    · exact ih C (isZero_upperStar_of_range_subset ℓ _ (pointsComplι S)
        ((range_opensOverι _).trans_subset (pointsComplOpens_subset_insert x S hx)) C hU) hΓ

end Points

end AlgebraicGeometry.ProEtale.CondensedRing
