/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedDescent
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GenericallyConnected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Pro-étale locally constant sheaves of sets on normal schemes

Let `f : V ⟶ Y` be a single-morphism pro-étale cover and `c` a descent cocycle on a constant
sheaf, defining a pro-étale locally constant sheaf of sets `F_c` on `Y`
(`AlgebraicGeometry.IsDescentCocycle`).

If the fibre of `F_c` is finite, then `F_c` is represented by a finite étale `Y`-scheme
(`AlgebraicGeometry.exists_isTwistedSection_finiteEtale_of_fin`): over every affine open of
`Y` the sheaf of twisted sections is represented by fpqc descent of the finite étale scheme
`V × Fin N` along an affine weakly étale cover
(`AlgebraicGeometry.TwistedDescent.exists_isUniversalSection`), and the representing schemes
glue (`AlgebraicGeometry.Scheme.exists_isUniversalSection_of_forall_exists_opens`).

On a connected normal Noetherian scheme every pro-étale locally constant sheaf of sets
becomes constant on the universal profinite étale cover `Ỹ_y`, i.e. it has a section over `Ỹ_y`
through every point
(`AlgebraicGeometry.exists_isTwistedSection_universalCover_of_isIntegrallyClosed_stalk`; the
regular case is `AlgebraicGeometry.exists_isTwistedSection_universalCover`). The input
from the theory of the pro-étale fundamental group is Bhatt–Scholze, *The pro-étale topology
for schemes*, Lemma 7.4.10: on a geometrically unibranch scheme every locally constant sheaf of
sets on `Y_proét` is a disjoint union of finite étale `Y`-schemes
(`AlgebraicGeometry.exists_isTwistedSection_finiteEtale_of_isIntegrallyClosed_stalk`). It is
reduced to the finiteness of its components
(`AlgebraicGeometry.exists_finite_invariant_subset_of_isIntegrallyClosed_stalk`), proved from the
local irreducibility of normal schemes étale over `Y` (`AlgebraicGeometry.IsGenericallyConnected`),
and the finite case. It is combined with the splitting of finite étale `Y`-schemes over `Ỹ_y` at all
geometric points (`AlgebraicGeometry.Scheme.UniversalCovers.exists_comp_eq_of_finiteEtale`),
deduced from `AlgebraicGeometry.Scheme.UniversalCovers.bijective_fiber` in the Galois category
of finite étale `Ỹ_y`-schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.FiniteEtale

variable {Y V : Scheme.{u}}

/-- A weakly étale surjective quasi-compact `f : V ⟶ Y` admits, over an affine `S ⟶ Y`, an
affine weakly étale surjective `S`-scheme `W` with a `Y`-morphism `W ⟶ V`: a finite disjoint
union of affine opens of `V ×_Y S`. -/
lemma exists_affine_weaklyEtale_cover (f : V ⟶ Y) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {S : Scheme.{u}} (s : S ⟶ Y) [IsAffine S] :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (j : W ⟶ V) (p : W ⟶ S) (_ : WeaklyEtale p)
      (_ : Surjective p), j ≫ f = p ≫ s := by
  let 𝒰 := (pullback f s).affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    rw [Scheme.OpenCover.finiteSubcover_X]
    exact Scheme.isAffine_affineCover _ _
  let g : ∐ 𝒰.X ⟶ pullback f s := Sigma.desc 𝒰.f
  have : WeaklyEtale g := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : Surjective g := Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range
  exact ⟨∐ 𝒰.X, inferInstance, g ≫ pullback.fst f s, g ≫ pullback.snd f s, inferInstance,
    inferInstance, by rw [Category.assoc, Category.assoc, pullback.condition]⟩

/-- **Finite locally constant sheaves of sets are finite étale** (fpqc descent of finite étale
morphisms), in cocycle form. Let `f : V ⟶ Y` be weakly étale, surjective and quasi-compact, hence
an fpqc cover, `Y` quasi-separated, and `c` a descent cocycle on the constant sheaf with *finite*
fibre `Fin N`. The descent datum `c` on the finite étale `V`-scheme `V × Fin N = ∐_{Fin N} V`
is effective: there is a finite étale `p : P ⟶ Y` with `P ×_Y V ≅ V × Fin N` compatibly with
`c` (descent of affine morphisms along fpqc covers, Stacks Project, Tag 0245, and finite étale
morphisms being fpqc local on the base, Tags 02L4 and 02VN). The projection `P ×_Y V ⟶ Fin N`
is a section of the sheaf of sets defined by `c` over `P` (its tautological section), and it
takes every value at some point over every geometric point of `V`. -/
theorem exists_isTwistedSection_finiteEtale_of_fin (f : V ⟶ Y) [WeaklyEtale f]
    [Surjective f] [QuasiCompact f] [QuasiSeparatedSpace Y] {N : ℕ}
    {c : ↥(pullback f f) → Fin N → Fin N} (hc : IsDescentCocycle f c) {K : Type u} [Field K]
    [IsAlgClosed K] (v : Spec (.of K) ⟶ V) (a : Fin N) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Y) (_ : IsFinite p) (_ : Etale p) (σ : ↥(pullback f p) → Fin N)
      (p' : Spec (.of K) ⟶ P) (h : v ≫ f = p' ≫ p),
      IsTwistedSection f c p σ ∧
        σ ((pullback.lift v p' h).base (IsLocalRing.closedPoint K)) = a := by
  classical
  -- local representability over affine opens, with the values at geometric points
  have hloc (O : Y.Opens) (hO : IsAffineOpen O) : ∃ (W : Scheme.{u}) (j : W ⟶ V) (p : W ⟶ O)
      (_ : Surjective p) (_ : WeaklyEtale (j ≫ f)) (_ : j ≫ f = p ≫ O.ι ≫ 𝟙 Y)
      (Nsch : Scheme.{u}) (n : Nsch ⟶ O) (_ : Etale n) (_ : IsFinite n)
      (ξ : (twistedSectionsPresheaf f c).obj (op (Scheme.Etale.mk (n ≫ O.ι ≫ 𝟙 Y)))),
      Scheme.IsUniversalSection (twistedSectionsPresheaf f c) (O.ι ≫ 𝟙 Y)
        (Scheme.Etale.mk (n ≫ O.ι ≫ 𝟙 Y)) n ξ ∧
      ∀ (wk : Spec (.of K) ⟶ W) (b : Fin N),
        ∃ (nk : Spec (.of K) ⟶ Nsch) (h : (wk ≫ j) ≫ f = nk ≫ n ≫ O.ι ≫ 𝟙 Y),
          ξ.1 ((pullback.lift (wk ≫ j) nk h).base (IsLocalRing.closedPoint K)) = b := by
    have : IsAffine O := hO
    obtain ⟨W, _, j, p, _, _, hjp⟩ := exists_affine_weaklyEtale_cover f (O.ι ≫ 𝟙 Y)
    have : WeaklyEtale (j ≫ f) := hjp ▸ inferInstance
    obtain ⟨Nsch, n, hn, hnf, ξ, hξ, hval⟩ :=
      TwistedDescent.exists_isUniversalSection hc (O.ι ≫ 𝟙 Y) j p hjp
    exact ⟨W, j, p, inferInstance, inferInstance, hjp, Nsch, n, hn, hnf, ξ, hξ,
      fun wk b ↦ hval wk b⟩
  have H (y : Y) : ∃ O : Y.Opens, y ∈ O ∧
      Scheme.IsRepresentableOver (twistedSectionsPresheaf f c) (𝟙 Y) O := by
    obtain ⟨O, hO, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
    obtain ⟨-, -, -, -, -, -, Nsch, n, hn, hnf, ξ, hξ, -⟩ := hloc O hO
    exact ⟨O, hy, Nsch, n, hn, hnf, ξ, hξ⟩
  obtain ⟨P, π, _, _, ξ, hξ⟩ := Scheme.exists_isUniversalSection_of_forall_exists_opens
    (isSheaf_twistedSectionsPresheaf f c) (𝟙 Y) H
  -- the value at `v`: an affine open around the image of `v`
  set y := (v ≫ f).base (IsLocalRing.closedPoint K)
  obtain ⟨O, hO, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  obtain ⟨W, j, p, _, _, hjp, Nsch, n, _, _, ξO, -, hval⟩ := hloc O hO
  -- a geometric point of `W` over `v ≫ f`
  obtain ⟨wk, hwk⟩ : ∃ wk : Spec (.of K) ⟶ W, wk ≫ j ≫ f = v ≫ f := by
    obtain ⟨o, ho⟩ : y ∈ Set.range O.ι.base := by rwa [Scheme.Opens.range_ι]
    obtain ⟨w, hw⟩ := p.surjective o
    have hw' : (j ≫ f).base w = (v ≫ f).base (IsLocalRing.closedPoint K) := by
      rw [hjp, Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, ho]
      rfl
    obtain ⟨x, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j ≫ f) (g := v ≫ f) w
      (IsLocalRing.closedPoint K) hw'
    obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (pullback.snd (j ≫ f) (v ≫ f)) x
    exact ⟨σ ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc,
      hσ, Category.id_comp]⟩
  -- the value at `wk ≫ j` transported to `v`
  let g : Spec (.of K) ⟶ pullback f f := pullback.lift v (wk ≫ j) (by rw [Category.assoc, hwk])
  obtain ⟨b, hb⟩ := (hc.bijective (g.base (IsLocalRing.closedPoint K))).2 a
  obtain ⟨nk, hnk, hξb⟩ := hval wk b
  -- the comparison map from `Nsch` to `P`
  obtain ⟨⟨α, hα⟩, hαξ⟩ := (hξ (Scheme.Etale.mk (n ≫ O.ι ≫ 𝟙 Y)) (n ≫ O.ι)
    (Category.assoc _ _ _)).2 ξO
  have hp' : (wk ≫ j) ≫ f = (nk ≫ α.left) ≫ π ≫ 𝟙 Y := by
    rw [hnk, Category.assoc, reassoc_of% hα]
  have h : v ≫ f = (nk ≫ α.left) ≫ π ≫ 𝟙 Y := by rw [← hp', Category.assoc, hwk]
  refine ⟨P, π ≫ 𝟙 Y, inferInstance, inferInstance, ξ.1, nk ≫ α.left, h, ξ.2, ?_⟩
  -- the two points of `V ×_Y P` over `nk ≫ α`
  set q := pullback.snd f (π ≫ 𝟙 Y)
  let w₂ : Spec (.of K) ⟶ pullback q q :=
    pullback.lift (pullback.lift v (nk ≫ α.left) h) (pullback.lift (wk ≫ j) (nk ≫ α.left) hp')
      (by simp [q])
  have hw₂ : ξ.1 ((pullback.fst q q).base (w₂.base (IsLocalRing.closedPoint K))) =
      c ((twistedPairMap f (π ≫ 𝟙 Y)).base (w₂.base (IsLocalRing.closedPoint K)))
        (ξ.1 ((pullback.snd q q).base (w₂.base (IsLocalRing.closedPoint K)))) :=
    ξ.2.2 _
  have e₁ : w₂ ≫ pullback.fst q q = pullback.lift v (nk ≫ α.left) h := pullback.lift_fst _ _ _
  have e₂ : w₂ ≫ pullback.snd q q = pullback.lift (wk ≫ j) (nk ≫ α.left) hp' :=
    pullback.lift_snd _ _ _
  have e₃ : w₂ ≫ twistedPairMap f (π ≫ 𝟙 Y) = g :=
    pullback.hom_ext (by simp [w₂, g, q]) (by simp [w₂, g, q])
  have e₄ : pullback.lift (f := f) (g := (Scheme.Etale.mk (n ≫ O.ι ≫ 𝟙 Y)).hom) (wk ≫ j) nk hnk ≫
      pullbackMapRight f α.left (MorphismProperty.Over.w α) =
        pullback.lift (wk ≫ j) (nk ≫ α.left) hp' :=
    pullback.hom_ext
      (by rw [Category.assoc, pullbackMapRight_fst, pullback.lift_fst]
          exact (pullback.lift_fst _ _ _).symm)
      (by rw [Category.assoc, pullbackMapRight_snd, pullback.lift_snd_assoc]
          exact (pullback.lift_snd _ _ _).symm)
  simp only [← Scheme.Hom.comp_apply, e₁, e₂] at hw₂
  rw [hw₂, ← e₄, Scheme.Hom.comp_apply,
    ← Function.comp_apply (f := ξ.1)]
  have hαξ' : (twistedSectionsPresheaf f c).map α.op ξ = ξO := hαξ
  change c _ (((twistedSectionsPresheaf f c).map α.op ξ).1 _) = a
  rw [hαξ']
  refine (congrArg (c _) hξb).trans ?_
  rw [← Scheme.Hom.comp_apply, e₃, hb]

/-- **The components of a locally constant sheaf of sets on a geometrically unibranch scheme are
finite** (Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 7.4.10), in cocycle form.
Let `Y` be a connected normal (hence geometrically unibranch) Noetherian scheme, that is, with
local rings integrally closed domains, `f : V ⟶ Y` a single-morphism pro-étale cover and `c` a
descent cocycle on the constant sheaf `S_V`, defining a pro-étale locally constant sheaf of sets
`F_c` on `Y`. Then every point `s` of the fibre `S` at a point `v` of `V` lies in a finite
subsheaf of `F_c`: a locally constant function `T` from `V` to finite subsets of `S`, compatible
with `c`, with `s ∈ T v`.

The subsheaf `T` is the orbit of `s` at a generization lying over the generic point `η` of
`Y` (`AlgebraicGeometry.exists_finite_invariant_subset_of_isGenericallyConnected`), after
replacing `V` by a cover which is ind-étale over affine opens of `Y`
(`AlgebraicGeometry.exists_isGenericallyConnected_cover_of_isIntegrallyClosed_stalk`, via Stacks
097Z) and on which nearby generic points are connected close to the diagonal, by local
irreducibility of the normal schemes étale over `Y`. Normality is necessary: on a nodal curve, a
cocycle with values in the shifts of `ℤ` along the loop has infinite orbits. -/
theorem exists_finite_invariant_subset_of_isIntegrallyClosed_stalk [IsLocallyNoetherian Y]
    [CompactSpace Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : V ⟶ Y) [WeaklyEtale f] [Surjective f] [QuasiCompact f] {S : Type*}
    {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c) (v : V) (s : S) :
    ∃ T : V → Set S, (∀ v, (T v).Finite) ∧ IsLocallyConstant T ∧
      (∀ z, T ((pullback.fst f f).base z) = c z '' T ((pullback.snd f f).base z)) ∧
        s ∈ T v := by
  have := isIntegral_of_isDomain_stalk Y fun y ↦ (hY y).1
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace f
  have hη : ∀ y : Y, genericPoint Y ⤳ y := genericPoint_specializes
  obtain ⟨W, j, _, _, hj, hsub, hQ⟩ :=
    exists_isGenericallyConnected_cover_of_isIntegrallyClosed_stalk hY f hη
  exact exists_finite_invariant_subset_of_comp f j hj hsub hc (fun w s' ↦
    exists_finite_invariant_subset_of_isGenericallyConnected (j ≫ f) hη hQ hc.restrict w s') v s

/-- **The components of a locally constant sheaf of sets on a regular scheme are finite**: the
case of a connected regular Noetherian scheme `Y` of
`AlgebraicGeometry.exists_finite_invariant_subset_of_isIntegrallyClosed_stalk`, regular schemes
being normal (`AlgebraicGeometry.IsRegular.isIntegrallyClosed_stalk`). -/
theorem exists_finite_invariant_subset [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsRegular Y] [ConnectedSpace Y] (f : V ⟶ Y) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {S : Type*} {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    (v : V) (s : S) :
    ∃ T : V → Set S, (∀ v, (T v).Finite) ∧ IsLocallyConstant T ∧
      (∀ z, T ((pullback.fst f f).base z) = c z '' T ((pullback.snd f f).base z)) ∧
        s ∈ T v :=
  exists_finite_invariant_subset_of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk y⟩) f hc v s

/-- **Locally constant sheaves of sets on a geometrically unibranch scheme are unions of finite
étale ones** (Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 7.4.10, with Lemma
7.3.9), in cocycle form. Let `Y` be a connected normal (hence geometrically unibranch)
Noetherian scheme, `f : V ⟶ Y` a single-morphism pro-étale cover and `c` a descent
cocycle on the constant sheaf `S_V`, defining a pro-étale locally constant sheaf of sets `F_c` on
`Y`. Then through every point `s` of the stalk of `F_c` at a geometric point `v̄ ≫ f`
(identified with `S` through `v̄ : Spec K ⟶ V`) passes a section of `F_c` over a finite étale
`p : P ⟶ Y`, at a geometric point `p̄` of `P` over `v̄ ≫ f`.

The point `s` lies in a finite subsheaf `T` of `F_c`
(`AlgebraicGeometry.exists_finite_invariant_subset_of_isIntegrallyClosed_stalk`), whose fibres
have constant cardinality `N` over the connected `Y`; enumerating them locally constantly turns
`c` into a descent cocycle on `Fin N`, which is effective
(`AlgebraicGeometry.exists_isTwistedSection_finiteEtale_of_fin`). -/
theorem exists_isTwistedSection_finiteEtale_of_isIntegrallyClosed_stalk [IsLocallyNoetherian Y]
    [CompactSpace Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : V ⟶ Y) [WeaklyEtale f] [Surjective f] [QuasiCompact f] {S : Type*}
    {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    {K : Type u} [Field K] [IsAlgClosed K] (v : Spec (.of K) ⟶ V) (s : S) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Y) (_ : IsFinite p) (_ : Etale p) (σ : ↥(pullback f p) → S)
      (p' : Spec (.of K) ⟶ P) (h : v ≫ f = p' ≫ p),
      IsTwistedSection f c p σ ∧
        σ ((pullback.lift v p' h).base (IsLocalRing.closedPoint K)) = s := by
  classical
  set v₀ := v.base (IsLocalRing.closedPoint K)
  obtain ⟨T, hTfin, hTlc, hTinv, hs⟩ :=
    exists_finite_invariant_subset_of_isIntegrallyClosed_stalk hY f hc v₀ s
  set p₁ := (pullback.fst f f).base
  set p₂ := (pullback.snd f f).base
  -- the cardinality of `T` is constant
  set N := (T v₀).ncard
  have hcard (z : ↥(pullback f f)) : (T (p₁ z)).ncard = (T (p₂ z)).ncard := by
    rw [hTinv z, Set.ncard_image_of_injective _ (hc.bijective z).1]
  have hN (w : V) : (T w).ncard = N := by
    have := IsTwistedSection.apply_eq_of_preconnectedSpace (f := f) (𝟙 Y)
      (fun x ↦ (T ((pullback.fst f (𝟙 Y)).base x)).ncard)
      (by exact (hTlc.comp Set.ncard).comp_continuous (pullback.fst f (𝟙 Y)).base.hom.continuous)
      (fun w ↦ by
        have h := hcard ((twistedPairMap f (𝟙 Y)).base w)
        simp only [p₁, p₂, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_snd] at h
        simpa only [Scheme.Hom.comp_apply] using h)
    have hsurj : Function.Surjective (pullback.fst f (𝟙 Y)).base :=
      (pullback.fst f (𝟙 Y)).surjective
    obtain ⟨x, hx⟩ := hsurj w
    obtain ⟨x₀, hx₀⟩ := hsurj v₀
    have := this x x₀
    simp only [hx, hx₀] at this
    exact this
  -- enumerations of the values of `T`
  let en (A : Set S) : Fin N → S :=
    if h : Nonempty (Fin N ≃ A) then fun i ↦ (h.some i : S) else fun _ ↦ s
  have hen (w : V) : Nonempty (Fin N ≃ T w) := by
    have := (hTfin w).fintype
    exact ⟨(Fintype.equivFinOfCardEq (by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hN w])).symm⟩
  let E (w : V) : Fin N → S := en (T w)
  have hE (w : V) (i : Fin N) : E w i = ((hen w).some i : S) := by
    simp only [E, en, dite_eq_left (hen w)]
  have hEinj (w : V) : Function.Injective (E w) := fun i j h ↦ by
    rw [hE, hE] at h
    exact (hen w).some.injective (Subtype.ext h)
  have hErange (w : V) : Set.range (E w) = T w := by
    ext t
    simp only [Set.mem_range, hE]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ ((hen w).some i).2,
      fun ht ↦ ⟨(hen w).some.symm ⟨t, ht⟩, by simp⟩⟩
  have hElc : IsLocallyConstant E := hTlc.comp en
  -- the cocycle on `Fin N`
  have hex (z : ↥(pullback f f)) (i : Fin N) : ∃ j, E (p₁ z) j = c z (E (p₂ z) i) := by
    rw [← Set.mem_range, hErange, hTinv z, ← hErange]
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  let c' (z : ↥(pullback f f)) (i : Fin N) : Fin N := (hex z i).choose
  have hc' (z : ↥(pullback f f)) (i : Fin N) : E (p₁ z) (c' z i) = c z (E (p₂ z) i) :=
    (hex z i).choose_spec
  have hc'eq {z z' : ↥(pullback f f)} {i : Fin N} (h₁ : E (p₁ z) = E (p₁ z'))
      (h₂ : c z (E (p₂ z) i) = c z' (E (p₂ z') i)) : c' z i = c' z' i :=
    hEinj (p₁ z) (by rw [hc', h₁, hc', h₂])
  have hp₁ : Continuous p₁ := (pullback.fst f f).base.hom.continuous
  have hp₂ : Continuous p₂ := (pullback.snd f f).base.hom.continuous
  have hcoc : IsDescentCocycle f c' := by
    refine ⟨fun i ↦ ?_, fun z ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro z₀
      have h₁ := (IsLocallyConstant.iff_eventually_eq _).1 (hElc.comp_continuous hp₁) z₀
      have h₂ := (IsLocallyConstant.iff_eventually_eq _).1 (hElc.comp_continuous hp₂) z₀
      have h₃ := (IsLocallyConstant.iff_eventually_eq _).1
        (hc.isLocallyConstant (E (p₂ z₀) i)) z₀
      filter_upwards [h₁, h₂, h₃] with z hz₁ hz₂ hz₃
      refine hc'eq hz₁ ?_
      simp only [Function.comp_apply] at hz₂
      rw [hz₂, hz₃]
    · rw [← Finite.injective_iff_bijective]
      intro i j hij
      have := congrArg (E (p₁ z)) hij
      rw [hc', hc'] at this
      exact hEinj _ ((hc.bijective z).1 this)
    · funext i
      have hd₁ : p₁ ((pullback.diagonal f).base w) = w := by
        simp only [p₁]; rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]; rfl
      have hd₂ : p₂ ((pullback.diagonal f).base w) = w := by
        simp only [p₂]; rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]; rfl
      have := hc' ((pullback.diagonal f).base w) i
      rw [hc.diagonal w, hd₁, hd₂] at this
      exact hEinj w this
    · funext i
      set q₁₂ := pullback.fst (pullback.snd f f) (pullback.fst f f)
      set q₂₃ := pullback.snd (pullback.snd f f) (pullback.fst f f)
      have e₁ : p₁ ((tripleProj₁₃ f).base w) = p₁ (q₁₂.base w) := by
        simp only [p₁, q₁₂, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      have e₂ : p₂ ((tripleProj₁₃ f).base w) = p₂ (q₂₃.base w) := by
        simp only [p₂, q₂₃, ← Scheme.Hom.comp_apply, pullback.lift_snd]
      have e₃ : p₂ (q₁₂.base w) = p₁ (q₂₃.base w) := by
        simp only [p₁, p₂, q₁₂, q₂₃, ← Scheme.Hom.comp_apply, pullback.condition]
      refine hEinj (p₁ ((tripleProj₁₃ f).base w)) ?_
      simp only [Function.comp_apply]
      rw [hc', hc.cocycle w, e₂, Function.comp_apply, ← hc', ← e₃, ← hc', e₁]
  -- the value at `v`
  obtain ⟨a, ha⟩ : ∃ a, E v₀ a = s := by
    rw [← Set.mem_range, hErange]
    exact hs
  obtain ⟨P, p, hp, hpe, σ', p', h, hσ', hσ'a⟩ :=
    exists_isTwistedSection_finiteEtale_of_fin f hcoc v a
  refine ⟨P, p, hp, hpe, fun x ↦ E ((pullback.fst f p).base x) (σ' x), p', h, ⟨?_, fun w ↦ ?_⟩, ?_⟩
  · exact hElc.comp_continuous (pullback.fst f p).base.hom.continuous |>.comp₂ hσ'.1 fun g i ↦ g i
  · have hm₁ : p₁ ((twistedPairMap f p).base w) = (pullback.fst f p).base
        ((pullback.fst (pullback.snd f p) (pullback.snd f p)).base w) := by
      simp only [p₁, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    have hm₂ : p₂ ((twistedPairMap f p).base w) = (pullback.fst f p).base
        ((pullback.snd (pullback.snd f p) (pullback.snd f p)).base w) := by
      simp only [p₂, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    simp only
    rw [hσ'.2 w, ← hm₁, hc', hm₂]
  · simp only
    rw [hσ'a, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact ha

/-- **Locally constant sheaves of sets on a regular scheme are unions of finite étale ones**:
the case of a connected regular Noetherian scheme `Y` of
`AlgebraicGeometry.exists_isTwistedSection_finiteEtale_of_isIntegrallyClosed_stalk`, regular
schemes being normal (`AlgebraicGeometry.IsRegular.isIntegrallyClosed_stalk`). -/
theorem exists_isTwistedSection_finiteEtale [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsRegular Y] [ConnectedSpace Y] (f : V ⟶ Y) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {S : Type*} {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    {K : Type u} [Field K] [IsAlgClosed K] (v : Spec (.of K) ⟶ V) (s : S) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Y) (_ : IsFinite p) (_ : Etale p) (σ : ↥(pullback f p) → S)
      (p' : Spec (.of K) ⟶ P) (h : v ≫ f = p' ≫ p),
      IsTwistedSection f c p σ ∧
        σ ((pullback.lift v p' h).base (IsLocalRing.closedPoint K)) = s :=
  exists_isTwistedSection_finiteEtale_of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk y⟩) f hc v s

/-- The points of the fibre of a finite coproduct of finite étale schemes come from the
summands. -/
lemma Scheme.FiniteEtale.exists_fiber_map_sigmaι {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) {N : ℕ} (Z : Fin N → X.FiniteEtale)
    (d : (fiber s).obj (∐ Z)) :
    ∃ i, ∃ x : (fiber s).obj (Z i), (fiber s).map (Sigma.ι Z i) x = d := by
  obtain ⟨⟨i⟩, x, hx⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (fiber s ⋙ FintypeCat.incl) (colimit.isColimit (Discrete.functor Z))) d
  exact ⟨i, x, hx⟩

/-- **Finite étale schemes split over the universal cover at every geometric point.** For a
finite étale `p : P ⟶ Y`, every geometric point of `P` over a geometric point `t` of the
universal cover `Ỹ_y` is the image of `t` under a `Y`-morphism `Ỹ_y ⟶ P`. Indeed the
`Y`-morphisms `a : Ỹ_y ⟶ P` give sections of the finite étale `P ×_Y Ỹ_y ⟶ Ỹ_y`, hence a
morphism `∐_a Ỹ_y ⟶ P ×_Y Ỹ_y` of finite étale `Ỹ_y`-schemes. It is bijective on the geometric
fibres at the base point (`AlgebraicGeometry.Scheme.UniversalCovers.bijective_fiber`), hence an
isomorphism, `Ỹ_y` being connected
(`AlgebraicGeometry.Scheme.FiniteEtale.isIso_of_isIso_fiber_map`), hence bijective on the geometric
fibres at `t`. -/
theorem Scheme.UniversalCovers.exists_comp_eq_of_finiteEtale {Ω : Type u} [Field Ω]
    (U : Scheme.UniversalCovers Y Ω) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    {P : Scheme.{u}} (p : P ⟶ Y) [IsFinite p] [Etale p] {K : Type u} [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ U.cover y) (p' : Spec (.of K) ⟶ P) (h : t ≫ U.proj y = p' ≫ p) :
    ∃ a : U.cover y ⟶ P, a ≫ p = U.proj y ∧ t ≫ a = p' := by
  have := U.connectedSpace y
  set π := U.proj y
  let PF : Y.FiniteEtale := ⟨Scheme.Etale.mk p, inferInstanceAs (IsFinite p)⟩
  let Q : (U.cover y).FiniteEtale :=
    ⟨Scheme.Etale.mk (pullback.snd p π), inferInstanceAs (IsFinite (pullback.snd p π))⟩
  let top : (U.cover y).FiniteEtale :=
    ⟨Scheme.Etale.mk (𝟙 (U.cover y)), inferInstanceAs (IsFinite (𝟙 (U.cover y)))⟩
  let A := {g : U.cover y ⟶ P // g ≫ p = π}
  have hbij := U.bijective_fiber y PF
  have : Finite A := Finite.of_injective _ hbij.1
  let e := Finite.equivFin A
  let N := Nat.card A
  -- the sections of `Q` given by the `Y`-morphisms `Ỹ_y ⟶ P`
  let σ (a : A) : top ⟶ Q := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.lift a.1 (𝟙 _) (by simp [a.2])) (by simp [Q, top]; rfl) trivial)
  let φ : ∐ (fun _ : Fin N ↦ top) ⟶ Q := Sigma.desc fun i ↦ σ (e.symm i)
  have hσleft (a : A) : (σ a).hom.left = pullback.lift a.1 (𝟙 _) (by simp [a.2]) := rfl
  -- the unique point of the fibre of `top`
  let star {L : Type u} [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ U.cover y) :
      (fiber s).obj top := fiberMk s top s (Category.comp_id s)
  have hstar {L : Type u} [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ U.cover y)
      (x : (fiber s).obj top) : x = star s :=
    fiber_ext s ((Category.comp_id _).symm.trans (fiber_left_comp s x))
  have hφσ {L : Type u} [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ U.cover y) (i : Fin N) :
      ((fiber s).map φ ((fiber s).map (Sigma.ι _ i) (star s))).left =
        pullback.lift (s ≫ (e.symm i).1) s (by simp [(e.symm i).2, π]) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Sigma.ι_comp_desc, fiber_map_left]
    apply pullback.hom_ext
    · simp [hσleft, star]
    · simp only [Category.assoc, pullback.lift_snd, fiberMk_left, star, hσleft]
      exact Category.comp_id _
  -- the comparison map is an isomorphism, as it is bijective on the fibre at the base point
  have hiso : IsIso φ := by
    have hs : U.pt y ≫ π = y := U.pt_proj y
    have : IsIso ((fiber (U.pt y)).map φ) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      refine ⟨fun d₁ d₂ hd ↦ ?_, fun q ↦ ?_⟩
      · obtain ⟨i, x, rfl⟩ := exists_fiber_map_sigmaι (U.pt y) _ d₁
        obtain ⟨j, x', rfl⟩ := exists_fiber_map_sigmaι (U.pt y) _ d₂
        rw [hstar _ x, hstar _ x'] at hd ⊢
        have h₁ := congrArg (fun z ↦ z.left ≫ pullback.fst p π) hd
        simp only [hφσ, pullback.lift_fst] at h₁
        have hij : e.symm i = e.symm j := hbij.1 (fiber_ext y h₁)
        rw [e.symm.injective hij]
      · have hq : q.left ≫ pullback.snd p π = U.pt y := fiber_left_comp (U.pt y) q
        let x := fiberMk y PF (q.left ≫ pullback.fst p π) (by
          rw [Category.assoc, show pullback.fst p π ≫ PF.obj.hom = pullback.snd p π ≫ π from
            pullback.condition, ← Category.assoc, hq]
          exact hs)
        obtain ⟨a, ha⟩ := hbij.2 x
        refine ⟨(fiber (U.pt y)).map (Sigma.ι _ (e a)) (star _), fiber_ext _ ?_⟩
        rw [hφσ]
        apply pullback.hom_ext
        · simpa [x] using congrArg (fun z ↦ z.left) ha
        · simpa using hq.symm
    exact isIso_of_isIso_fiber_map (U.pt y) φ
  -- hence also bijective on the fibre at `t`
  have hbt : Function.Bijective ((fiber t).map φ) := ConcreteCategory.bijective_of_isIso _
  obtain ⟨d, hd⟩ := hbt.2 (fiberMk t Q (pullback.lift p' t h.symm) (pullback.lift_snd _ _ _))
  obtain ⟨i, x, rfl⟩ := exists_fiber_map_sigmaι t _ d
  rw [hstar _ x] at hd
  have h₁ := congrArg (fun z ↦ z.left ≫ pullback.fst p π) hd
  simp only [hφσ, pullback.lift_fst, fiberMk_left] at h₁
  exact ⟨(e.symm i).1, (e.symm i).2, h₁⟩


/-- **Pro-étale locally constant sheaves of sets are constant on the universal cover.** Let `Y`
be a connected normal Noetherian scheme, `Ỹ_y = U.cover y` its universal profinite étale cover
at a geometric point `y`, `f : V ⟶ Y` a single-morphism pro-étale cover and `c` a descent
cocycle on the constant sheaf `S_V`. Then the sheaf of sets defined by `c` has a section over
`Ỹ_y` through every point of `V ×_Y Ỹ_y` and every value in `S`: the sheaf is a union of finite
étale ones (`AlgebraicGeometry.exists_isTwistedSection_finiteEtale_of_isIntegrallyClosed_stalk`),
which split over `Ỹ_y` (`AlgebraicGeometry.Scheme.UniversalCovers.exists_comp_eq_of_finiteEtale`).
-/
theorem exists_isTwistedSection_universalCover_of_isIntegrallyClosed_stalk {Ω : Type u} [Field Ω]
    [IsLocallyNoetherian Y] [CompactSpace Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Scheme.UniversalCovers Y Ω) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (f : V ⟶ Y)
    [WeaklyEtale f] [Surjective f] [QuasiCompact f] {S : Type*} {c : ↥(pullback f f) → S → S}
    (hc : IsDescentCocycle f c) (x : ↥(pullback f (U.proj y))) (s : S) :
    ∃ σ, IsTwistedSection f c (U.proj y) σ ∧ σ x = s := by
  -- a geometric point over `x`
  set x' := (pullback f (U.proj y)).fromSpecAlgebraicClosureResidueField x
  have hx' : x'.base (IsLocalRing.closedPoint _) = x := by
    simp only [x', Scheme.fromSpecAlgebraicClosureResidueField, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply (X := pullback f (U.proj y)) x _
  obtain ⟨P, p, _, _, σ, p', h, hσ, hσs⟩ :=
    exists_isTwistedSection_finiteEtale_of_isIntegrallyClosed_stalk hY f hc
      (x' ≫ pullback.fst _ _) s
  obtain ⟨a, ha, hap⟩ := U.exists_comp_eq_of_finiteEtale y p (x' ≫ pullback.snd _ _) p' (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, h])
  have hm : x' ≫ pullback.map f (U.proj y) f p (𝟙 V) a (𝟙 Y) (by simp) (by simp [ha]) =
      pullback.lift (x' ≫ pullback.fst _ _) p' h :=
    pullback.hom_ext (by simp) (by simpa using hap)
  refine ⟨_, hσ.comp a ha, ?_⟩
  simp only [Function.comp_apply]
  rw [← hx', ← Scheme.Hom.comp_apply, hm]
  exact hσs

/-- **Pro-étale locally constant sheaves of sets on a regular scheme are constant on the
universal cover**: the case of a connected regular Noetherian scheme `Y` of
`AlgebraicGeometry.exists_isTwistedSection_universalCover_of_isIntegrallyClosed_stalk`, regular
schemes being normal (`AlgebraicGeometry.IsRegular.isIntegrallyClosed_stalk`). -/
theorem exists_isTwistedSection_universalCover {Ω : Type u} [Field Ω] [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] (U : Scheme.UniversalCovers Y Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (f : V ⟶ Y) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {S : Type*} {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    (x : ↥(pullback f (U.proj y))) (s : S) :
    ∃ σ, IsTwistedSection f c (U.proj y) σ ∧ σ x = s :=
  exists_isTwistedSection_universalCover_of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk y⟩) U y f hc x s

end AlgebraicGeometry
